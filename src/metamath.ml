type stmt =
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
  | Block of stmt list

type prog = { name : string; content : stmt list }

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


type hypothesis =
  | Type of string * string
  | Prop of string * string list

type frame = {
  hypothesis : (string * hypothesis) list;
  distincts  : string list list
}

let empty_frame = { hypothesis = []; distincts = [] }

let add_disj frames disj =
  match !frames with
  | f::fs -> frames := { f with distincts = disj::f.distincts }::fs
  | _ -> assert false

let add_hyp frames hyp =
  match !frames with
  | f::fs -> frames := { f with hypothesis = hyp::f.hypothesis }::fs
  | _ -> assert false

type statement =
  | Axm of {
    typecode : string;
    body : string list;
    frame : frame;
  }
  | Thm of {
    typecode : string;
    body : string list;
    proof : string list;
    frame : frame;
  }

type db = {
  statements : (string, statement) Hashtbl.t;
  mutable constants : SymSet.t;
  mutable variables : SymSet.t;
}

let is_var db s = SymSet.mem s db.variables

let is_cst db s = SymSet.mem s db.constants

let print_hyp = function
  | Type (ty, x) ->
    Printf.printf "Type %s %s\n" ty x
  | Prop (ty, body) ->
    Printf.printf "Prop %s %s\n" ty (String.concat " " body)

let print_db { statements; constants; variables } =
  Printf.printf "Variables : %s\n"
    (SymSet.fold (fun x acc -> acc ^ " " ^ x) variables "");
  Printf.printf "Constants : %s\n"
    (SymSet.fold (fun x acc -> acc ^ " " ^ x) constants "");
  Printf.printf "Statements :\n";
  Hashtbl.iter (fun name -> function
    | Thm { typecode; body; frame; _ } ->
      Printf.printf "Theorem \"%s\": %s\n" name (String.concat " " (typecode::body));
      Printf.printf "Under conditions:\n";
      List.iter (fun (name, cond) ->
        match cond with
        | Type (ty, x) ->
          Printf.printf "\t%s: %s %s\n" name ty x
        | Prop (ty, body) ->
          Printf.printf "\t%s: %s %s\n" name ty (String.concat " " body)
      ) frame.hypothesis
    | Axm { typecode; body; frame; _ } ->
      Printf.printf "Axiom \"%s\": %s\n" name (String.concat " " (typecode::body));
      Printf.printf "Under conditions:\n";
      List.iter (fun (name, cond) ->
        match cond with
        | Type (ty, x) ->
          Printf.printf "\t%s: %s %s\n" name ty x
        | Prop (ty, body) ->
          Printf.printf "\t%s: %s %s\n" name ty (String.concat " " body)
      ) frame.hypothesis
  ) statements

let get_vars vars body =
  List.filter (fun x -> SymSet.mem x vars) body
  |> SymSet.of_list

let get_csts vars body =
  List.filter (fun x -> SymSet.mem x vars) body
  |> SymSet.of_list

let common_var s1 s2 =
  SymSet.(not (is_empty (inter s1 s2)))

let hyp_vars variables = function
  | Type (_, x) ->
    if SymSet.mem x variables then
      SymSet.singleton x
    else
      SymSet.empty
  | Prop (_, body) ->
    get_vars variables body

let make_frame { variables; _ } frames body =
  match frames with
  | [] -> assert false
  | { hypothesis; distincts }::_ ->
    let body_vars = get_vars variables body in
    let hypothesis =
      List.filter (fun (_, hyp) ->
        common_var body_vars (hyp_vars variables hyp)
      ) hypothesis
    in
    let distincts =
      List.filter (fun disj ->
        common_var body_vars (get_vars variables disj)
      ) distincts
    in
    { hypothesis; distincts }


let check_lbl { statements; _ } lbl =
  if Hashtbl.mem statements lbl then
    Printf.eprintf "label %s already defined!\n" lbl;
    exit 1

let check_body db typecode body =
  if not (is_cst db typecode) then begin
    Printf.eprintf "A statement must start with a typecode!\n";
    exit 1
  end else begin
    let vars = get_vars db.variables body in
    let diff = SymSet.diff vars db.variables in
    if not (SymSet.is_empty diff) then begin
      Printf.eprintf "Undefined variable %s\n" (SymSet.choose diff);
      exit 1
    end
  end

type subst = (string * string list) list

let apply_var (s : subst) (x : string) =
  match List.assoc_opt x s with
  | None -> [x]
  | Some l -> l

let apply (s : subst) =
  List.concat_map (apply_var s)

let apply' (s : subst) = function
  | Type (ty, x) -> Prop (ty, apply_var s x)
  | Prop (ty, body) -> Prop (ty, apply s body)

let compose (x : string) (vx : string list) (s : subst) =
  (x, vx)::s

let check_proof db _name typecode body frame proof =
  let classify sym =
    match List.assoc_opt sym frame.hypothesis with
    | Some v -> `HYP v | None ->
    match Hashtbl.find_opt db.statements sym with
    | Some v -> `THM v | None -> failwith ("unbound label " ^ sym)
  in
  let match_hyp hyp arg subst =
    match hyp, (apply' subst arg) with
    | Type (ty, x), Type (ty', x') ->
      if ty = ty' then compose x [x'] subst
      else failwith (Printf.sprintf "types %s and %s don't match" ty ty')
    | Type (ty, x), Prop (ty', vx) ->
      if ty = ty' then compose x vx subst
      else failwith (Printf.sprintf "types %s and %s don't match" ty ty')
    | Prop (ty, p), Prop (ty', p') ->
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


let make_axm db frames body =
  match body with
  | typecode::body ->
    check_body db typecode body;
    Axm { typecode; body; frame = make_frame db frames body }
  | [] -> failwith "Unable to make empty axiom"

let make_thm db frames body proof =
  match body with
  | typecode::body ->
    check_body db typecode body;
    Thm { typecode; body; frame = make_frame db frames body; proof }
  | [] -> failwith "Unable to make empty theorem"

let make_type_hyp db frames lbl ty v =
  if not (is_cst db ty) then begin
    Printf.eprintf "in %s : Undefined typecode %s\n" lbl ty;
    exit 1
  end else if not (is_var db v) then begin
    Printf.eprintf "in %S : Undefined variable %s\n" lbl v;
    exit 1
  end else add_hyp frames (lbl, Type (ty, v))

let make_hyp db frames lbl body =
  match body with
  | ty::body ->
    if not (is_cst db ty) then begin
      Printf.eprintf "in %s : Undefined typecode %s\n" lbl ty;
      exit 1
    end else begin
      add_hyp frames (lbl, Prop (ty, body))
    end
  | _ ->
    Printf.eprintf "in %s : ill-formed hypothesis\n" lbl;
    exit 1

let make_disj db frames disj =
  if List.for_all (is_var db) disj then
    add_disj frames disj
  else
    Printf.eprintf "ill-formed disjoint-variable restriction"

let load { content; _ } : db =
  let db = { statements = Hashtbl.create 10; variables = SymSet.empty; constants = SymSet.empty } in
  let frames = ref [empty_frame] in
  let new_frame () = frames := (List.hd !frames)::!frames in
  let drop_frame () = frames := List.tl !frames in
  let rec load_block block =
    List.iter (function
      | CmdA (lbl, body) ->
        Hashtbl.add db.statements lbl (make_axm db !frames body)
      | CmdP (lbl, body, proof) ->
        Hashtbl.add db.statements lbl (make_thm db !frames body proof)
      | CmdC csts ->
        db.constants <- SymSet.union db.constants (SymSet.of_list csts)
      | CmdV vars ->
        db.variables <- SymSet.union db.variables (SymSet.of_list vars)
      | CmdF (lbl, ty, x) ->
        make_type_hyp db frames lbl ty x
      | CmdE (lbl, body) ->
        make_hyp db frames lbl body
      | CmdD disj ->
        make_disj db frames disj
      | Block block ->
        new_frame ();
        load_block block;
        drop_frame ()
    ) block
  in
  load_block content;
  db

let load_file f =
  match parse_file f with
  | None -> Printf.eprintf "unable to parse file %s\n" f; exit 1
  | Some prog -> let db = load prog in print_db db; db

let check_sym db sym =
  match Hashtbl.find_opt db.statements sym with
  | Some (Thm { typecode; body; frame; proof }) ->
    check_proof db sym typecode body frame proof
  | _ -> failwith "nothing to prove"

let () = check_sym (load_file "test.mm") "wnew"

(* let db = load_file "test.mm" *)