// Lean compiler output
// Module: Definitions.Def_ZetaNine_CoefficientMapFiniteSum
// Imports: public import Init public meta import Init public import Definitions.Def_ZetaNine_CoefficientMapPartialFractions public import Definitions.Def_ZetaNine_HarmonicStability public import Mathlib.Algebra.BigOperators.Intervals
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lp_mathlib_Nat_cast___at___00Mathlib_Meta_Positivity_evalLogNatLit_spec__0(lean_object*);
lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_weightedR(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_Icc___at___00Nat_divisorsAntidiagonal_spec__0(lean_object*, lean_object*);
lean_object* lp_zeta9TelescoperOfflineAuthor_Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMapFiniteSum_finiteL___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMapFiniteSum_finiteL(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMapFiniteSum_finiteL___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMapFiniteSum_finiteL___lam__0(lean_object* v_n_1_, lean_object* v_W_2_, lean_object* v_t_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_Positivity_evalLogNatLit_spec__0(v_t_3_);
v___x_5_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_weightedR(v_n_1_, v_W_2_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMapFiniteSum_finiteL(lean_object* v_n_6_, lean_object* v_T_7_, lean_object* v_W_8_){
_start:
{
lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___f_9_ = lean_alloc_closure((void*)(lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMapFiniteSum_finiteL___lam__0), 3, 2);
lean_closure_set(v___f_9_, 0, v_n_6_);
lean_closure_set(v___f_9_, 1, v_W_8_);
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lp_mathlib_Finset_Icc___at___00Nat_divisorsAntidiagonal_spec__0(v___x_10_, v_T_7_);
v___x_12_ = lp_zeta9TelescoperOfflineAuthor_Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0___redArg(v___x_11_, v___f_9_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMapFiniteSum_finiteL___boxed(lean_object* v_n_13_, lean_object* v_T_14_, lean_object* v_W_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMapFiniteSum_finiteL(v_n_13_, v_T_14_, v_W_15_);
lean_dec(v_T_14_);
return v_res_16_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_zeta9TelescoperOfflineAuthor_Definitions_Def__ZetaNine__CoefficientMapPartialFractions(uint8_t builtin);
lean_object* initialize_zeta9TelescoperOfflineAuthor_Definitions_Def__ZetaNine__HarmonicStability(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_Intervals(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_zeta9TelescoperOfflineAuthor_Definitions_Def__ZetaNine__CoefficientMapFiniteSum(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_zeta9TelescoperOfflineAuthor_Definitions_Def__ZetaNine__CoefficientMapPartialFractions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_zeta9TelescoperOfflineAuthor_Definitions_Def__ZetaNine__HarmonicStability(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_Intervals(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
