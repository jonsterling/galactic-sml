structure Judgements : JUDGEMENTS =
struct
  structure Ctx = Context
  type tm = Tm.t
  type ty = Tm.t
  type eq_hint = ty * tm * tm
  type ctx = ty Ctx.context
  type eq = {ty:ty, tm1:tm, tm2:tm}
  type hints =
    { general : eq Ctx.context
    , beta : eq Ctx.context
    }

  val empty_hints =
    { general = Ctx.empty
    , beta = Ctx.empty
    }

  exception Hole
  exception NHole of string

  type ('i, 'o) judgement = ctx * hints -> 'i -> 'o

  infix 5 $
  infix 5 $$
  infix 5 \
  infix 5 \\

  open Tm
  open Ops

  exception InvalidTerm of tm

  fun is_neutral tm =
    case out tm of
      ` v => true
    | ? v => true
    | APP $ #[M,_] => is_neutral M
    | ASC $ #[M,_] => is_neutral M
    | _ => false

  fun is_canon tm =
    case out tm of
      PI $ _ => true
    | LAM $ _ => true
    | SET $ _ => true
    | ASC $ #[M,_] => is_canon M
    | _ => false

  fun is_normal tm =
    is_neutral tm orelse is_canon tm

  exception StructurallyInequal of eq

  fun whnf (G,E:hints) {tm, ty} =
    if is_canon tm then tm
    else
      case Ctx.search (#beta E) (fn {tm1,...} => Tm.aequiv (tm, tm1)) of
        SOME (_, {tm2,...}) => tm2
      | NONE =>
        (case (out ty, out tm) of
           (BN, APP $ #[A,xB,M,N]) =>
             (case out (whnf (G,E) {tm = M, ty = PI $$ #[A,xB]}) of
                LAM $ #[_,_,xE] => whnf (G,E) {tm = subst1 xE N, ty = subst1 xB N}
              | M' => whnf (G,E) { tm = APP $$ #[A,xB,into M',N], ty = subst1 xB N})
         | (PI $ #[A,xB], M) =>
             let
               val x = Variable.newvar()
             in
               LAM $$ #[A,xB, x \\ (APP $$ #[A,xB,into M, ``x])]
             end
         | _ => tm)

  fun eq_str (G,E:hints) (e as {ty,tm1,tm2}) =
    case Tm.aequiv (tm1, tm2) of
      true => ()
    | false =>
      (case (out ty, out tm1, out tm2) of
         (T,APP $ #[A,xB,M,N], APP $ #[A',xB',M',N']) =>
           ( eq (G,E) {ty=SET $$ #[], tm1=A, tm2=A'}
           ; let
               val (x,B) = unbind xB
               val Gx = Ctx.insert G x A
             in
               ( eq (Gx,E) {ty=SET $$ #[], tm1=B, tm2=subst1 xB' (``x)}
               ; eq (G,E) {ty=PI $$ #[A,xB], tm1=M, tm2=M'}
               ; eq (G,E) {ty=A, tm1=N, tm2=N'})
             end)
       | _ => raise StructurallyInequal e)

  and eq_ext (G,E:hints) {ty,tm1,tm2} =
    case Tm.aequiv (tm1, tm2) of
      true => ()
    | false =>
      (case (out ty, out tm1, out tm2) of
         (PI $ #[A,xB], LAM $ #[A',xB',xM], LAM $ #[A'',xB'',xN]) =>
           ( eq (G,E) {ty=SET $$ #[], tm1=A, tm2=A'}
           ; eq (G,E) {ty=SET $$ #[], tm1=A', tm2=A''}
           ; let
               val (x,B) = unbind xB
               val Gx = Ctx.insert G x A
               val B' = subst1 xB' (``x)
               val B'' = subst1 xB'' (``x)
             in
               ( eq (Gx,E) {ty=SET $$ #[], tm1=B, tm2=B'}
               ; eq (Gx,E) {ty=SET $$ #[], tm1=B', tm2=B''}
               ; eq (Gx,E) {ty=B, tm1=subst1 xM (``x), tm2=subst1 xN (``x)})
             end)
       | _ => raise Hole)

  and eq (G,E:hints) (e as {ty,tm1,tm2}) =
    let
      fun find_hint {ty=ty',tm1=tm1',tm2=tm2'} =
        aequiv (ty,ty') andalso
          ((aequiv (tm1,tm1') andalso aequiv (tm2,tm2')) orelse
           (aequiv (tm1,tm2') andalso aequiv (tm2,tm1')))
    in
      if (Tm.aequiv (tm1,tm2)) then ()
      else
        (case Ctx.search (#general E) find_hint of
          SOME (_,_) => ()
        | NONE =>
          eq_str (G,E) e
          handle _ => eq_ext (G,E) e
          handle ex =>
            if is_canon tm1 andalso is_canon tm2 andalso is_canon ty then
              raise ex
            else
              let
                val nty = whnf (G,E) {ty=SET $$ #[], tm=ty}
                val ntm1 = whnf (G,E) {ty=nty, tm=tm1}
                val ntm2 = whnf (G,E) {ty=nty, tm=tm2}
              in
                if Tm.aequiv (ty,nty) andalso Tm.aequiv (tm1,ntm1) andalso Tm.aequiv (tm2,ntm2) then
                  raise ex
                else
                  eq (G,E) {ty=nty, tm1=whnf (G,E) {ty=nty, tm=tm1}, tm2=whnf (G,E) {ty=nty, tm=tm2}}
              end)
    end


  fun chk (g,h) {ty,tm} = raise Hole
  and syn (g,h) i = raise Hole

  val set_alias = Variable.newvar()
  val my_hints : hints =
    {beta=Ctx.insert Ctx.empty (Variable.newvar()) {ty=SET $$ #[], tm1=(``set_alias), tm2=SET $$ #[]}
    ,general=Ctx.empty
    }

  fun extm () =
    let
      open Variable
      val x = newvar()
      val set = SET $$ #[]
    in
      {ty=PI $$ #[set, x \\ set]
      ,tm1=LAM $$ #[set, x \\ set, x \\ ``set_alias]
      ,tm2=LAM $$ #[set, x \\ set, x \\ set]
      }
    end

  val test =
    eq (Ctx.empty, my_hints) (extm())
    handle NHole msg => print msg

end
