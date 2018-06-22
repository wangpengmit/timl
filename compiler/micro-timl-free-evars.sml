structure MicroTiMLFreeEVars = struct

open MicroTiMLVisitor
open MicroTiMLUtil
open MicroTiMLUtilTiML

infixr 0 $

infix 6 @%--
fun a @%-- b = ISet.difference (a, ISetU.fromList b)
         
fun set_is_rec_expr_visitor_vtable cast pass_through_EAbsIT =
  let
    val vtable = 
        default_expr_visitor_vtable
          cast
          extend_noop
          extend_noop
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    fun set_flag bind =
      if pass_through_EAbsIT then
        let
          val (name_anno, e) = unBindAnno bind
          val (binds, e) = collect_EAbsIT e
          val (st, (anno, (name, body)), i_spec) = assert_EAbs e
          val e = EAbs (st, EBindAnno ((name, anno), EAnnoBodyOfRecur body), i_spec)
        in
          BindAnno (name_anno, EAbsITs (binds, e))
        end
      else
        let
          val (name1, e) = unBindAnno bind
          val e = case e of
                      EAbs (st, bind, spec) =>
                      let
                        val (name, body) = unBindAnno bind
                      in
                        EAbs (st, BindAnno (name, EAnnoBodyOfRecur body), spec)
                      end
                    | EAbsI bind =>
                      let
                        val (name, body) = unBindAnno bind
                      in
                        EAbsI $ BindAnno (name, EAnnoBodyOfRecur body)
                      end
                    | EAbsT bind =>
                      let
                        val (name, body) = unBindAnno bind
                      in
                        EAbsT $ BindAnno (name, EAnnoBodyOfRecur body)
                      end
                    | _ => raise Impossible "set_is_rec: other than EAbs/EAbsI/EAbsT"
        in
          BindAnno (name1, e)
        end
    fun visit_ERec this env bind =
      let
        val bind = set_flag bind
      in
        #visit_ERec vtable this env bind (* call super*)
      end
  in
    override_visit_ERec vtable visit_ERec
  end
fun new_set_is_rec_expr_visitor params = new_expr_visitor set_is_rec_expr_visitor_vtable params
fun set_is_rec pass_through_EAbsIT b =
  let
    val visitor as (ExprVisitor vtable) = new_set_is_rec_expr_visitor pass_through_EAbsIT
  in
    #visit_expr vtable visitor () b
  end

fun free_evars_expr_visitor_vtable cast output =
  let
    fun extend_e this env name = (env + 1, name)
    fun visit_var this env data =
      ((case data of
            ID (n, _) => if n >= env then output $ n - env
                         else ()
          | QID _ => raise Impossible "free_evars/QID"
       );
       data)
  in
    default_expr_visitor_vtable
      cast
      extend_noop
      extend_noop
      extend_noop
      extend_e
      visit_var
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
  end
fun new_free_evars_expr_visitor params = new_expr_visitor free_evars_expr_visitor_vtable params
fun free_evars b =
  let
    val r = ref []
    fun output n = push_ref r n
    val visitor as (ExprVisitor vtable) = new_free_evars_expr_visitor output
    val _ = #visit_expr vtable visitor 0 b
    val fvars = !r
  in
    ISetU.to_set fvars
  end
              
fun set_free_evars_expr_visitor_vtable cast () =
  let
    val vtable = 
        default_expr_visitor_vtable
          cast
          extend_noop
          extend_noop
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    fun visit_expr this env e =
      case e of
          EAbs (pre_st, bind, spec) =>
          let
            val (name, e) = unBindAnno bind
            val (is_rec, e) = is_rec_body e
            val excluded = [0] @ (if is_rec then [1] else []) (* argument and (optionally) self-reference are not free evars *)
            val n_fvars = ISet.numItems (free_evars e @%-- excluded)
            val e = #visit_expr (cast this) this env e
            val e = EAnnoFreeEVars (e, n_fvars)
          in
            EAbs (pre_st, BindAnno (name, e), spec)
          end
        | EAbsT data =>
          let
            val (name, e) = unBindAnno data
            val (is_rec, e) = is_rec_body e
            val excluded = if is_rec then [0] else []
            val n_fvars = ISet.numItems (free_evars e @%-- excluded)
            val e = #visit_expr (cast this) this env e
            val e = EAnnoFreeEVars (e, n_fvars)
          in
            EAbsT $ BindAnno (name, e)
          end
        | EAbsI data =>
          let
            val (name, e) = unBindAnno data
            val (is_rec, e) = is_rec_body e
            val excluded = if is_rec then [0] else []
            val n_fvars = ISet.numItems (free_evars e @%-- excluded)
            val e = #visit_expr (cast this) this env e
            val e = EAnnoFreeEVars (e, n_fvars)
          in
            EAbsI $ BindAnno (name, e)
          end
        | _ => #visit_expr vtable this env e (* call super *)
    val vtable = override_visit_expr vtable visit_expr
  in
    vtable
  end
fun new_set_free_evars_expr_visitor params = new_expr_visitor set_free_evars_expr_visitor_vtable params
fun set_free_evars b =
  let
    val visitor as (ExprVisitor vtable) = new_set_free_evars_expr_visitor ()
  in
    #visit_expr vtable visitor 0 b
  end
              
end
