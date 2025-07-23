(* Simple Types *)
(* ------------ *)

Inductive type: Type :=
| Base
| Arr (A B: type) : type.
