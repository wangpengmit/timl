signature SIG_DERIV_TRANSFOMRERS =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    structure DerivAssembler :
              sig
                  val as_KdEqKArrow : MicroTiMLDef.kdeq -> MicroTiMLDef.kdeq -> MicroTiMLDef.kdeq_judgement
                  val as_KdEqKSubset : MicroTiMLDef.kdeq -> MicroTiMLDef.proping -> MicroTiMLDef.kdeq_judgement
                  val as_WfPropQuan : MicroTiMLDef.quan -> MicroTiMLDef.sort -> MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop_judgement
                  val as_WfPropBinPred : MicroTiMLDef.prop_bin_pred -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.wfprop_judgement
                  val as_WfPropNot : MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop_judgement
                  val as_WfPropBinConn : MicroTiMLDef.prop_bin_conn -> MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop_judgement
                  val as_WfKdSubset : MicroTiMLDef.wfkind -> MicroTiMLDef.wfprop -> MicroTiMLDef.wfkind_judgement
                  val as_WfKdArrow : MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind_judgement
                  val as_KdEq : MicroTiMLDef.kinding -> MicroTiMLDef.kdeq -> MicroTiMLDef.kinding_judgement
                  val as_KdRef : MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdRec : MicroTiMLDef.wfkind -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdQuan : MicroTiMLDef.quan -> MicroTiMLDef.wfkind -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdTimeApp : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdTimeAbs : MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdApp : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdAbs : MicroTiMLDef.wfkind -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdArrow : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdIte : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdBinOp : MicroTiMLDef.cstr_bin_op -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdUnOp : MicroTiMLDef.cstr_un_op -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_TyEqRef : MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqRec : MicroTiMLDef.kdeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqBetaRev : MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqBeta : MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqNat : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.proping -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqTimeApp : int -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqQuan : MicroTiMLDef.quan -> MicroTiMLDef.kdeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqApp : MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqArrow : MicroTiMLDef.tyeq -> MicroTiMLDef.proping -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqIte : MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqUnOp : MicroTiMLDef.cstr_un_op -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqBinOp : MicroTiMLDef.cstr_bin_op -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyApp : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyAppK : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyAbs : MicroTiMLDef.kinding -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TySubTy : MicroTiMLDef.typing -> MicroTiMLDef.tyeq -> MicroTiMLDef.typing_judgement
                  val as_TySubTi : MicroTiMLDef.typing -> MicroTiMLDef.proping -> MicroTiMLDef.typing_judgement
                  val as_TyWrite : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyRead : MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyNew : MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyCase : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyInj : MicroTiMLDef.injector -> MicroTiMLDef.typing -> MicroTiMLDef.kinding -> MicroTiMLDef.typing_judgement
                  val as_TyProj : MicroTiMLDef.projector -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyPair : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyUnpack : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyPack : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyUnfold : MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyFold : MicroTiMLDef.kinding -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyHalt : MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyRec : MicroTiMLDef.kinding -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyFix : MicroTiMLDef.ctx -> MicroTiMLDef.kinding -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyAbsC : MicroTiMLDef.wfkind -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyAppC : MicroTiMLDef.typing -> MicroTiMLDef.kinding -> MicroTiMLDef.typing_judgement
                  val as_TyLet : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
              end

    structure ShiftCtx :
              sig
                  val shift_ctx_ty : ((MicroTiMLDef.kctx * int) * (MicroTiMLDef.tctx * int)) -> MicroTiMLDef.typing -> MicroTiMLDef.typing
                  val shift_ctx_kd : (MicroTiMLDef.kctx * int) -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
                  val shift_ctx_te : (MicroTiMLDef.kctx * int) -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq
                  val shift_ctx_pr : (MicroTiMLDef.kctx * int) -> MicroTiMLDef.proping -> MicroTiMLDef.proping
                  val shift_ctx_wk : (MicroTiMLDef.kctx * int) -> MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind

                  val shift0_ctx_ty : (MicroTiMLDef.kctx * MicroTiMLDef.tctx) -> MicroTiMLDef.typing -> MicroTiMLDef.typing
                  val shift0_ctx_kd : MicroTiMLDef.kctx -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
                  val shift0_ctx_te : MicroTiMLDef.kctx -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq
                  val shift0_ctx_pr : MicroTiMLDef.kctx -> MicroTiMLDef.proping -> MicroTiMLDef.proping
                  val shift0_ctx_wk : MicroTiMLDef.kctx -> MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind
              end

    structure DerivSubstTyping :
              sig
                  val subst_ty_ty : MicroTiMLDef.typing -> int -> MicroTiMLDef.typing -> MicroTiMLDef.typing
                  val subst0_ty_ty : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing
              end

    (*structure DerivSubstKinding :
              sig
                  val subst_kd_kd : MicroTiMLDef.kinding -> int -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
                  val subst0_kd_kd : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
              end*)

    structure CPS :
              sig
                  val cps_deriv : MicroTiMLDef.typing -> MicroTiMLDef.typing
              end

    structure WrapLambda :
              sig
                  val wrap_lambda_deriv : MicroTiMLDef.typing -> MicroTiMLDef.typing
              end

    structure CloConv :
              sig
                  val clo_conv_deriv : MicroTiMLDef.typing -> MicroTiMLDef.typing
              end
end
