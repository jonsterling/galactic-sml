structure Ops =
struct
  datatype t =
    PI
  | SET
  | LAM
  | APP
  | ASC

  fun eq (x : t) y = x = y
  fun arity PI = #[0,1]
    | arity LAM = #[0,1,1]
    | arity APP = #[0,1,0,0]
    | arity SET = #[]
    | arity ASC = #[0,0]

  fun to_string PI = "Π"
    | to_string LAM = "λ"
    | to_string SET = "Set"
    | to_string APP = "App"
    | to_string ASC = "Ascribe"
end
