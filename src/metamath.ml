type command =
  (* $c *)
  | CmdC of string list
  (* $v *)
  | CmdV of string list
  (* $f *)
  | CmdF of string * string * string
  (* $a *)
  | CmdA of string * string list
  (* $e *)
  | CmdE of string * string list
  (* $d *)
  | CmdD of string list
  (* $p *)
  | CmdP of string * string list * string list
  (* ${ ... $} *)
  | Block of command list

type prog = { name : string; content : command list }

let (let*) = Option.bind

module SymSet = Set.Make(String)

let keywords = SymSet.of_list [
  "$c";
  "$f";
  "$e";
  "$a";
  "$v";
  "$d";
  "$p";
  "$=";
  "$.";
  "${";
  "$}";
  "$(";
  "$)";
]

let is_keyword s = SymSet.mem s keywords

let rec spaces inp =
  match Stream.peek inp with
  | Some (' ' | '\t' | '\n') ->
    Stream.junk inp;
    spaces inp
  | _ -> ()

let token inp =
  let rec next_tok acc =
    match Stream.peek inp with
    | None | Some (' ' | '\n' | '\t') -> acc
    | Some c ->
      Stream.junk inp;
      next_tok (acc ^ String.make 1 c)
  in
  let elem _ =
    match Stream.peek inp with
    | None -> None
    | Some _ -> spaces inp; Some (next_tok "")
  in
  Stream.from elem


let parse inp =
  let rec parse_stmt () =
    match Stream.peek inp with
    | Some "$(" ->
      Stream.junk inp;
      let* _ = parse_comment () in
      parse_stmt ()
    | Some "${" ->
      Stream.junk inp;
      let* l = parse_block () in
      let* _ = expect "$}" in
      Some (Block l)
    | Some "$c" ->
      Stream.junk inp;
      let* l = parse_list () in
      let* _ = expect "$." in
      Some (CmdC l)
    | Some "$v" ->
      Stream.junk inp;
      let* l = parse_list () in
      let* _ = expect "$." in
      Some (CmdV l)
    | Some "$d" ->
      Stream.junk inp;
      let* l = parse_list () in
      let* _ = expect "$." in
      Some (CmdD l)
    | Some lbl when not (is_keyword lbl) ->
      Stream.junk inp;
      begin match Stream.peek inp with
      | Some "$f" ->
        Stream.junk inp;
        let* l = parse_list () in
        let* _ = expect "$." in
        begin match l with
        | [ty; x] -> Some (CmdF (lbl, ty, x))
        | _ -> None
        end
      | Some "$e" ->
        Stream.junk inp;
        let* l = parse_list () in
        let* _ = expect "$." in
        Some (CmdE (lbl, l))
      | Some "$a" ->
        Stream.junk inp;
        let* l = parse_list () in
        let* _ = expect "$." in
        Some (CmdA (lbl, l))
      | Some "$p" ->
        Stream.junk inp;
        let* l = parse_list () in
        let* _ = expect "$=" in
        let* p = parse_list () in
        let* _ = expect "$." in
        Some (CmdP (lbl, l, p)) 
      | _ -> None
      end
    | _ -> None
  and parse_list () =
    match Stream.peek inp with
    | None -> Some []
    | Some x when is_keyword x -> Some []
    | Some x ->
      Stream.junk inp;
      let* xs = parse_list () in
      Some (x::xs)
  and parse_comment () =
    match Stream.peek inp with
    | None -> None
    | Some "$)" -> Stream.junk inp; Some ()
    | Some _ ->
      Stream.junk inp; parse_comment ()
  and parse_block () =
    match parse_stmt () with
    | None -> Some []
    | Some x ->
      let* xs = parse_block () in
      Some (x::xs)
  and expect t =
    match Stream.peek inp with
    | Some tok when tok = t ->
      Stream.junk inp; Some ()
    | _ -> None
  in
  parse_block ()

let parse_string s =
  parse (Stream.of_string s |> token)

let parse_file f =
  let inx = open_in f in
  Stream.of_channel inx
  |> token
  |> parse
  |> Option.map (fun l -> { name = f; content = l })

module Subst : sig
  type t
  val apply_var : t -> string -> string list
  val apply : t -> string list -> string list
  val extend : string -> string list -> t -> t
  val empty : t
end = struct

  type t = (string * string list) list

  let empty = []

  let apply_var s x =
    match List.assoc_opt x s with
    | None -> [x]
    | Some l -> l

  let apply s =
    List.concat_map (apply_var s)

  let extend x vx s =
    (x, vx)::s
end

module Assertion : sig
  type t
  val make : string list -> t
  val statement : t -> string list
  val instanciate : t -> Subst.t -> t
  val has_type : t -> string -> bool
  val body : t -> string list
end = struct
  type t = { typecode : string; body : string list }
  
  let make = function
    | [] -> Printf.eprintf "ill formed assertion"; exit 1
    | typecode::body -> { typecode; body }

  let statement { typecode; body } = typecode::body
  
  let body { body; _ } = body

  let has_type a ty = a.typecode = ty
  
  let instanciate a s =
    { a with body = Subst.apply s a.body }
end

module Hypothesis : sig
  type t
  val make_var_type : string -> string -> t
  val make_logic    : Assertion.t -> t
  val statement : t -> string list
  val assertion : t -> Assertion.t
  val match_arg : t -> Assertion.t -> Subst.t -> Subst.t
end = struct
  type t =
    | VType of string * string
    | Logic of Assertion.t
  let make_var_type v tv = VType (v, tv)
  let make_logic a = Logic a
  let statement = function
    | VType (v, tv) -> [v; tv]
    | Logic a -> Assertion.statement a
  let assertion = function
    | VType (v, tv) -> Assertion.make [tv; v]
    | Logic a -> a
  let match_arg (hyp : t) (arg : Assertion.t) (s : Subst.t) =
    match hyp with
    | VType (v, tv) ->
      if Assertion.has_type arg tv then
        Subst.extend v (Assertion.body arg) s
      else begin
        Printf.eprintf "Type %s missmatched\n" tv; exit 1
      end
    | Logic hyp ->
      if hyp = arg then s
      else begin
        Printf.eprintf "Argument missmatch\n"; exit 1
      end
end

module Frame = struct

  type t = {
    hypothesis : (string * Hypothesis.t) list;
    distincts  : string list list
  }
  
  let empty = { hypothesis = []; distincts = [] }
  
  let get_hypothesis frame hyp =
    List.assoc_opt hyp frame.hypothesis

  let suppose_distincts (f : t) (vs : string list) =
    { f with distincts = vs::f.distincts }

  let suppose (f : t) (id : string) h =
    { f with hypothesis = (id, h)::f.hypothesis }
end

module Item : sig
  type t
  val instanciate : t -> Subst.t -> Assertion.t
  val make_axm : Frame.t -> string list -> t
  val make_thm : Frame.t -> string list -> string list -> t
  val get_hypothesis : t -> Hypothesis.t list
  val get_thm : t -> (Assertion.t * Frame.t * string list) option
end = struct
  type t =
    | Axm of Assertion.t * Frame.t
    | Thm of Assertion.t * Frame.t * string list

  let get_thm = function
    | Thm (a, f, p) -> Some (a, f, p)
    | _ -> None

  let instanciate (a : t) (s : Subst.t) =
    match a with
    | Axm (stmt, _) | Thm (stmt, _, _) ->
      Assertion.instanciate stmt s

  let make_axm frame body =
    Axm (Assertion.make body, frame)

  let make_thm frame body proof =
    Thm (Assertion.make body, frame, proof)

  let get_hypothesis = function
    | Axm (_, frame) | Thm (_, frame, _) ->
      List.map snd frame.hypothesis
end

module Db = struct

  type t = {
    statements : (string, Item.t) Hashtbl.t;
    mutable constants : SymSet.t;
    mutable variables : SymSet.t;
  }

  let empty = {
    statements = Hashtbl.create 10;
    constants = SymSet.empty;
    variables = SymSet.empty;
  }

  let is_var db v = SymSet.mem v db.variables
  
  let is_cst db c = SymSet.mem c db.constants

  let get_vars db body =
    List.filter (fun x -> SymSet.mem x db.variables) body
    |> SymSet.of_list

  let get_avars db (a : Assertion.t) =
    Assertion.statement a |> get_vars db

  let get_hvars db (h : Hypothesis.t) =
    Hypothesis.statement h |> get_vars db

  let common_vars s1 s2=
    SymSet.(not (is_empty (inter s1 s2)))
  
  let get_item db sym =
    Hashtbl.find_opt db.statements sym

  let get_hypothesis db (frame : Frame.t) body =
    let vars = get_vars db body in
    List.filter (fun (_, hyp) ->
      common_vars vars (get_hvars db hyp)
    ) frame.hypothesis

  let get_distincts db (frame : Frame.t) body =
    let vars = get_vars db body in
    List.filter (fun distincts ->
      common_vars vars (get_vars db distincts)
    ) frame.distincts
end

module Loader : sig
  type t
  val of_prog : prog -> t
  val of_file : string -> t
  val load : t -> Db.t
end = struct

  type t = {
    prog : prog;
    mutable frames : Frame.t list;
    db : Db.t;
  }

  let of_prog prog = { prog; frames = [Frame.empty]; db = Db.empty }
  
  let of_file file =
    match parse_file file with
    | None -> Printf.eprintf "Unable to load file %s\n" file; exit 1
    | Some prog -> of_prog prog

  let check_lbl loader lbl =
    if Hashtbl.mem loader.db.statements lbl then begin
      Printf.eprintf "Label %s already defined\n" lbl;
      exit 1
    end

  let make_frame loader body =
    match loader.frames with
    | [] -> assert false
    | frame::_ ->
      let hypothesis = Db.get_hypothesis loader.db frame body in
      let distincts  = Db.get_distincts loader.db frame body in
      { Frame.hypothesis; Frame.distincts }

  let new_axm loader lbl body =
    check_lbl loader lbl;
    let frame = make_frame loader body in
    Hashtbl.add loader.db.statements lbl (Item.make_axm frame body)

  let new_thm loader lbl _typecode body proof =
    check_lbl loader lbl;
    let frame = make_frame loader body in
    Hashtbl.add loader.db.statements lbl (Item.make_thm frame body proof)

  let suppose_type loader lbl typecode var =
    check_lbl loader lbl;
    match loader.frames with
    | f::fs ->
      let ty = Hypothesis.make_var_type var typecode in
      if Db.is_cst loader.db typecode then
        if Db.is_var loader.db var then loader.frames <- (Frame.suppose f lbl ty)::fs
        else (Printf.eprintf "Undeclared variable %s\n" var ; exit 1)
      else (Printf.eprintf "Undefined typecode %s\n" typecode; exit 1)
    | _ -> assert false

  let suppose loader lbl body =
    check_lbl loader lbl;
    match loader.frames with
    | f::fs ->
      let ty = Hypothesis.make_logic (Assertion.make body) in
      List.iter (fun x ->
        if Db.is_cst loader.db x || Db.is_var loader.db x then ()
        else (Printf.eprintf "Undefined symbol %s\n" x; exit 1)
      ) body;
      loader.frames <- (Frame.suppose f lbl ty)::fs
    | _ -> assert false

  let suppose_distincts loader distincts =
    match loader.frames with
    | f::fs ->
      List.iter (fun x ->
        if Db.is_var loader.db x then ()
        else (Printf.eprintf "Undefined variable %s\n" x; exit 1)
      ) distincts;
      loader.frames <- (Frame.suppose_distincts f distincts)::fs
    | _ -> assert false
    

  let new_csts loader csts =
    loader.db.constants <- SymSet.union (loader.db.constants) (SymSet.of_list csts) 

  let new_vars loader vars =
    loader.db.variables <- SymSet.union (loader.db.variables) (SymSet.of_list vars) 

  
  let new_frame loader =
    loader.frames <- (List.hd loader.frames)::loader.frames

  let drop_frame loader =
    loader.frames <- List.tl loader.frames

  let load loader =
    let rec load_block block =
      List.iter (function
        | CmdA (lbl, body) ->
          new_axm loader lbl body
        | CmdP (lbl, body, proof) ->
          new_thm loader lbl "" body proof
        | CmdC csts ->
          new_csts loader csts
        | CmdV vars ->
          new_vars loader vars
        | CmdF (lbl, ty, x) ->
          suppose_type loader lbl ty x
        | CmdE (lbl, body) ->
          suppose loader lbl body
        | CmdD distincts ->
          suppose_distincts loader distincts
        | Block block ->
          new_frame loader;
          load_block block;
          drop_frame loader
      ) block
    in
    load_block loader.prog.content;
    loader.db
end

module Checker = struct
  let check_proof db name typecode body frame proof =
    let classify sym =
      match Frame.get_hypothesis frame sym with
      | Some v -> `HYP v | None ->
      match Db.get_item db sym with
      | Some v -> `THM v | None -> failwith ("unbound label " ^ sym)
    in
    let match_hyp (hyp : Hypothesis.t) (arg : Assertion.t) s =
      let arg' = Assertion.instanciate arg s in
      Hypothesis.match_arg hyp arg' s
    in
    let match_hyps stack hyps =
      List.fold_left (fun (stack, subst) hyp ->
        match stack with
        | arg::stack ->
          stack, match_hyp hyp arg subst
        | [] -> failwith "empty stack"
      ) (stack, Subst.empty) hyps
    in 
    let apply_thm (thm : Item.t) stack =
      let hyps = Item.get_hypothesis thm in
      let stack, subst = match_hyps stack hyps in
      (Item.instanciate thm subst)::stack
    in
    let rec step stack proof =
      match proof with
      | [] -> stack
      | sym::proof ->
        match classify sym with
        | `HYP hyp -> step (Hypothesis.assertion hyp::stack) proof
        | `THM thm -> step (apply_thm thm stack) proof
    in
    match step [] proof with
    | [conclusion] ->
      if Assertion.statement conclusion = typecode::body then
        Printf.printf "Theorem %s sucessfully checked!\n" name
      else begin
        failwith "conclusion of the proof doesnt match the goal"
      end
    | [] -> failwith "empty stack after proof"
    | _ -> failwith "too many arguments in the proof"
end

let check_sym db sym =
  match Db.get_item db sym with
  | Some item ->
    begin match Item.get_thm item with
    | Some (a, frame, proof) ->
      let stmt = Assertion.statement a in
      let typecode = List.hd stmt in 
      let body = List.tl stmt in 
      Checker.check_proof db sym typecode body frame proof
    | _ -> failwith "nothing to prove"
    end
  | _ -> failwith "nothing to prove"

let loader = Loader.of_file "test.mm"

let () = check_sym (Loader.load loader) "wnew"