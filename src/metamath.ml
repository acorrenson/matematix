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


module Assertion = struct
  type t =
    | Type of { typecode : string; var  : string }
    | Fact of { typecode : string; body : string list }

  let body = function
    | Type { var; _ } -> [var]
    | Fact { body; _ } -> body

  let typecode = function
    | Type { typecode; _ } | Fact { typecode; _ } -> typecode

  let make_fact = function
    | [] -> Printf.eprintf "Unable to make an empty assertion\n"; exit 1
    | typecode::body -> Fact { typecode; body }

  let make_type = function
    | [] -> Printf.eprintf "Unable to make an empty type assertion\n"; exit 1
    | [typecode; var] -> Type { typecode; var }
    | body -> Printf.eprintf "ill-formed type assertion %s\n" (String.concat " " body); exit 1
end

module Frame = struct

  type t = {
    hypothesis : (string * Assertion.t) list;
    distincts  : string list list
  }
  
  let empty = { hypothesis = []; distincts = [] }

  let suppose_distincts (f : t) (vs : string list) =
    { f with distincts = vs::f.distincts }

  let suppose (f : t) (id : string) (a : Assertion.t) =
    { f with hypothesis = (id, a)::f.hypothesis }
end

module Item = struct
  type t =
    | Axm of { statement : Assertion.t; frame : Frame.t; }
    | Thm of { statement : Assertion.t; proof : string list; frame : Frame.t; }

  let make_axm frame body =
    match body with
    | [] -> Printf.eprintf "Unsable to make empty axiom\n"; exit 1
    | typecode::body -> Axm { statement = Assertion.Fact { typecode; body }; frame }

  let make_thm frame body proof =
    match body with
    | [] -> Printf.eprintf "Unsable to make empty theorem\n"; exit 1
    | typecode::body -> Thm { statement = Assertion.Fact { typecode; body }; frame; proof }
  
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
    Assertion.body a |> get_vars db

  
  let common_var db body1 body2 =
    let vars1 = get_vars db body1 in
    let vars2 = get_vars db body2 in
    SymSet.(not (is_empty (inter vars1 vars2)))

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

  let check_typecode loader typecode =
    if Db.is_cst loader.db typecode then begin
      Printf.eprintf "Undefined typecode %s\n" typecode;
      exit 1
    end
  
  let check_assertion loader typecode body =
    if not (Db.is_cst loader.db typecode) then begin
      Printf.eprintf "An assertion must start with a typecode!\n";
      exit 1
    end else begin
      let vars = Db.get_vars loader.db body in
      let diff = SymSet.diff vars loader.db.variables in
      if not (SymSet.is_empty diff) then begin
        Printf.eprintf "Undefined variable %s\n" (SymSet.choose diff);
        exit 1
      end
    end

  let make_frame loader body =
    match loader.frames with
    | [] -> assert false
    | { hypothesis; distincts }::_ ->
      let hypothesis =
        List.filter (fun (_, hyp) ->
          Db.common_var loader.db body (Assertion.body hyp)
        ) hypothesis
      in
      let distincts =
        List.filter (fun disj ->
          Db.common_var loader.db body disj
        ) distincts
      in
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
      let ty = Assertion.Type { typecode; var } in
      loader.frames <- (Frame.suppose f lbl ty)::fs
    | _ -> assert false

  let suppose loader lbl body =
    check_lbl loader lbl;
    match loader.frames with
    | f::fs ->
      let ty = Assertion.make_fact body in
      loader.frames <- (Frame.suppose f lbl ty)::fs
    | _ -> assert false

  let suppose_distincts loader distincts =
    match loader.frames with
    | f::fs ->
      if List.for_all (Db.is_var loader.db) distincts then
        loader.frames <- (Frame.suppose_distincts f distincts)::fs
      else begin
        Printf.eprintf "I-ll formed distinct asssumption\n"; exit 1
      end
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

module Subst : sig
  type t
  val apply_var : t -> string -> string list
  val apply : t -> string list -> string list
  val apply' : t -> Assertion.t -> Assertion.t
  val extend : string -> string list -> t -> t
end = struct

  type t = (string * string list) list

  let apply_var s x =
    match List.assoc_opt x s with
    | None -> [x]
    | Some l -> l

  let apply s =
    List.concat_map (apply_var s)

  let apply' s = function
    | Assertion.Type { typecode; var } ->
      Assertion.Fact { typecode; body = apply_var s var }
    | Assertion.Fact { typecode; body } ->
      Assertion.Fact { typecode; body = apply s body }

  let extend x vx s =
    (x, vx)::s
end

module Checker = struct
  let check_proof db _name typecode body frame proof =
    let classify sym =
      match List.assoc_opt sym frame.Frame.hypothesis with
      | Some v -> `HYP v | None ->
      match Hashtbl.find_opt db.Db.statements sym with
      | Some v -> `THM v | None -> failwith ("unbound label " ^ sym)
    in
    let match_hyp hyp arg subst =
      match hyp, (Subst.apply' subst arg) with
      | Assertion.Type ty, Assertion.Fact ty' ->
        if ty = ty' then compose x vx subst
        else failwith (Printf.sprintf "types %s and %s don't match" ty ty')
      | Assertion.Fact ty, Assertion.Fact ty' ->
        if ty = ty' then
          if p = p' then subst
          else failwith "body missmatch"
        else failwith (Printf.sprintf "types %s and %s don't match" ty ty')
      | _ -> failwith "hypothesis missmatch"
    in
    let match_hyps stack hyps =
      List.fold_left (fun (stack, subst) hyp ->
        match stack with
        | arg::stack ->
          stack, match_hyp hyp arg subst
        | [] -> failwith "empty stack"
      ) (stack, []) (List.map snd hyps)
    in
    let apply_thm thm stack =
      match thm with
      | Axm { typecode; body; frame; _ }
      | Thm { typecode; body; frame; _ } ->
        let stack, subst = match_hyps stack frame.hypothesis in
        let arg = Prop (typecode, apply subst body) in
        arg::stack
    in
    let rec step stack proof =
      match proof with
      | [] -> stack
      | sym::proof ->
        match classify sym with
        | `HYP hyp -> step (hyp::stack) proof
        | `THM thm -> step (apply_thm thm stack) proof
    in
    match step [] proof with
    | [conclusion] ->
      if conclusion = Prop (typecode, body) then ()
      else begin
        print_hyp conclusion;
        failwith "conclusion of the proof doesnt match the goal"
      end
    | [] -> failwith "empty stack after proof"
    | _ -> failwith "too many arguments in the proof"
end

let check_sym db sym =
  match Hashtbl.find_opt db.statements sym with
  | Some (Thm { typecode; body; frame; proof }) ->
    check_proof db sym typecode body frame proof
  | _ -> failwith "nothing to prove"

let () = check_sym (load_file "test.mm") "wnew"

let db = load_file "test.mm" *)