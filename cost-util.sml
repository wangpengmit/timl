structure CostUtil = struct

open EVMCosts
open MicroTiMLCosts
open Expr

infixr 0 $
       
infix 9 %@
infix 8 %^
infix 7 %*
infix 6 %+ 
infix 4 %<
infix 4 %>
infix 4 %<=
infix 4 %>=
infix 4 %=
infix 4 <?
infix 4 >?
infix 4 <=?
infix 4 >=?
infix 4 =?
infix 4 <>?
infixr 3 /\
infixr 3 /\?
infixr 2 \/
infixr 2 \/?
infixr 1 -->
infix 1 <->

fun N n = INat (n, dummy)
               
fun IFloor' i = IFloor (i, dummy)
fun IToReal' i = IToReal (i, dummy)
fun to_real n = IToReal' $ N n
fun ILog256 i = ILog ("256", i, dummy)
fun IIte' (i1, i2, i3) = IIte (i1, i2, i3, dummy)
                       
fun nat_exp_cost i2 = IIte'(i2 =? N 0, IToReal' $ N C_exp, IToReal' $ N C_exp %+ N C_expbyte %* (N 1 %+ IFloor' (ILog256 $ IToReal' i2)))
fun E_nat_exp_cost i2 = nat_exp_cost i2 %+ to_real (C_SWAP + 2 * C_Var + C_Let)

fun set_cost old new = IIte' (old =? N 0 /\? new <>? N 0, N C_sset, N C_sreset)
                                     
end
