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