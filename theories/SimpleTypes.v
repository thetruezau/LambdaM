(* Simple Types *)
(* ------------ *)

Inductive type: Type := Base | Arr : type -> type -> type.
