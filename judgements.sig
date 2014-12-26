signature JUDGEMENTS =
sig
  structure Ctx : CONTEXT where type Key.ord_key = Variable.t

  type tm
  type ty

  type eq = {ty:ty, tm1:tm, tm2:tm}

  type ctx = ty Ctx.context
  type hints =
    { beta : eq Ctx.context
    , general : eq Ctx.context
    }

  type ('i, 'o) judgement = ctx * hints -> 'i -> 'o

  val whnf : ({ty:ty,tm:tm}, tm) judgement

  (* equality on neutral terms *)
  val eq_str : (eq, unit) judgement

  (* equality on canonical terms *)
  val eq_ext : (eq, unit) judgement

  val chk : ({ty:ty,tm:tm}, tm) judgement
  val syn : (tm, {ty:ty,tm:tm}) judgement

end
