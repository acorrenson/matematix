type stmt =
  (* $c *)
  | CmdC of string list
  (* $v *)
  | CmdV of string list
  (* $f *)
  | CmdF of string list
  (* $a *)
  | CmdA of string * string * string list
  (* $e *)
  | CmdE of string * string * string list
  (* $d *)
  | CmdD of string * string
  (* $p *)
  | CmdP of string * string
  (* ${ ... $} *)
  | Block of stmt list

type prog = { name : string; content : stmt list }

type thm = {
  name : string;
  typecode : string;
  body : string list;
  proof : string list
}

type hyp = {
  name: string;
  typecode : string;
  body : string list
}

type concl =
  | Axiom of hyp
  | Theorem of thm

type typ_env = (string * string) list
type dis_env = (string * string) list
type hyp_env = (string * hyp) list

type frame = {
  types       : typ_env;
  hypothesis  : hyp_env;
  disjoints   : dis_env;
  conclusion  : concl;
}

type db = {
  statements : (string * frame) list;
}

let check_thm types hypothesis { name; typecode; body; proof } =
  true

let check_axm types hypothesis { name; typecode; body } =
  true

let check_frame { types; hypothesis; conclusion } =
  match conclusion with
  | Axiom axm -> check_axm types hypothesis axm
  | Theorem thm -> check_thm types hypothesis thm
