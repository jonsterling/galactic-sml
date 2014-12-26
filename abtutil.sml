functor AbtUtil (A : ABT) : ABTUTIL =
struct

  open A

  infix 5 $
  infix 5 $$
  infix 5 \
  infix 5 \\

  fun `` v = into (` v)
  fun ?? v = into (? v)
  fun v \\ e = into (v \ e)
  fun p $$ es = into (p $ es)

  fun subst e v e' =
    case out e' of
      ` v' => if Variable.eq v v' then e else e'
    | v' \ e'' => v' \\ subst e v e''
    | p $ es => p $$ Vector.map (subst e v) es
    | ? _ => e'

  fun to_string e =
    case out e of
      ` v => Variable.to_string v
    | v \ e => Variable.to_string v ^ "." ^ (to_string e)
    | p $ es =>
        Operator.to_string p ^
          (if Vector.length es = 0 then ""
             else VectorUtil.to_string to_string es)
    | ? v => "{?" ^ Variable.to_string v ^ "}"

  exception ExpectedBinding of t

  fun unbind e =
    case out e of
      v \ e => (v,e)
    | ? v => (Variable.newvar(), into (? v))
    | _ => raise ExpectedBinding e

  fun subst1 xe b =
    case unbind xe of
      (x,e) => subst b x e

end
