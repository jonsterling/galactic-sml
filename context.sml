structure Context :> CONTEXT where type Key.ord_key = Variable.t =
struct
  structure M =
  struct
    structure M' = BinaryMapFn
      (struct type ord_key = Variable.t val compare = Variable.compare end)
    open M'

    exception Hole
    fun list_search xs p =
      case xs of
        nil => NONE
      | ((i,x) :: ys) => if p x then SOME (i,x) else list_search ys p

    fun search ma p = list_search (M'.listItemsi ma) p
  end

  type 'a context = 'a M.map
  structure K = M.Key
  structure Key = K

  val empty = M.empty

  fun insert ctx k v = M.insert (ctx, k, v)
  fun remove ctx k = M.remove (ctx, k)

  fun lookup ctx k = M.find (ctx, k)

  (* Needs to be made more lazy *)
  fun search ctx p = M.search ctx p

  val map = M.map
  val mapi = M.mapi
end
