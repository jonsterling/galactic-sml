functor Abt (Operator : OPERATOR) :> ABT
  where
    type Operator.t = Operator.t
    and Variable = Variable
  =
struct
  structure Operator : OPERATOR = Operator
  structure Variable : VARIABLE = Variable

  infix 5 \
  infix 5 $

  datatype t =
    FREE of Variable.t
  | BOUND of int
  | ABS of t
  | APP of Operator.t * t vector
  | META of Variable.t

  datatype 'a view =
    ` of Variable.t
  | \ of Variable.t * 'a
  | $ of Operator.t * 'a vector
  | ? of Variable.t

  fun map f (` v) = ` v
    | map f (v \ e') = v \ f e'
    | map f (p $ es) = p $ Vector.map f es
    | map f (? v) = ? v

  fun shiftvar v n (FREE v') = if Variable.eq v v' then BOUND n else (FREE v')
    | shiftvar v n (BOUND m) = BOUND m
    | shiftvar v n (ABS e') = ABS (shiftvar v (n + 1) e')
    | shiftvar v n (APP (p, es)) = APP (p, Vector.map (shiftvar v n) es)
    | shiftvar v n (META mv) = META mv

  fun match_arity (0, ABS _) = false
    | match_arity (0, _) = true
    | match_arity (n, ABS e') = match_arity (n - 1, e')
    | match_arity (n, _) = false

  exception Malformed of string

  fun doapp (oper, es) =
    if VectorUtil.pair_all_eq match_arity (Operator.arity oper) es
    then APP (oper, es)
    else raise Malformed "Bad arity"

  fun into (` v) = FREE v
    | into (v \ e') = ABS (shiftvar v 0 e')
    | into (p $ es) = doapp (p, es)
    | into (? v) = META v

  fun addvar v n (FREE v') = FREE v'
    | addvar v n (BOUND m) = if m = n then FREE v else BOUND m
    | addvar v n (ABS e) = ABS (addvar v (n + 1) e)
    | addvar v n (APP (p, es)) = APP (p, Vector.map (addvar v n) es)
    | addvar v n (META mv) = META mv

  fun out e =
    case e of
      FREE v => ` v
    | BOUND n => raise Fail "bound variable occured in out"
    | ABS e' =>
      let
        val v = Variable.newvar ()
      in
        v \ addvar v 0 e'
      end
    | APP (p, es) => p $ es
    | META v => ? v

  fun aequiv (FREE v1, FREE v2) = Variable.eq v1 v2
    | aequiv (BOUND m, BOUND n) = m = n
    | aequiv (ABS e1, ABS e2) = aequiv (e1, e2)
    | aequiv (APP (p1, es1), APP (p2, es2)) = Operator.eq p1 p2 andalso VectorUtil.pair_all_eq aequiv es1 es2
    | aequiv (META mv1, META mv2) = Variable.eq mv1 mv2
    | aequiv (_, _) = false

end
