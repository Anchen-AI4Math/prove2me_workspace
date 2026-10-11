// Lean compiler output
// Module: missions.zeta9.formalization.CoefficientMapSummation
// Imports: public import Init public meta import Init public import missions.zeta9.formalization.CoefficientMapReflection public import missions.zeta9.formalization.CoefficientMapFiniteSum public import Mathlib.NumberTheory.LSeries.RiemannZeta public import Mathlib.Analysis.PSeries public import Mathlib.Analysis.Normed.Group.InfiniteSum public import Mathlib.Analysis.Normed.Module.FiniteDimension
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(lean_object*);
lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMap_weightedR(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Rat_cast___at___00Rat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapSummation_actualSeries(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapSummation_actualSeries___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapSummation_actualSeries(lean_object* v_n_1_, lean_object* v_W_2_, lean_object* v_t_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___f_8_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_add(v_t_3_, v___x_4_);
v___x_6_ = lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(v___x_5_);
v___x_7_ = lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMap_weightedR(v_n_1_, v_W_2_, v___x_6_);
v___f_8_ = lean_alloc_closure((void*)(lp_mathlib_Rat_cast___at___00Rat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_8_, 0, v___x_7_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapSummation_actualSeries___boxed(lean_object* v_n_9_, lean_object* v_W_10_, lean_object* v_t_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapSummation_actualSeries(v_n_9_, v_W_10_, v_t_11_);
lean_dec(v_t_11_);
return v_res_12_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMapReflection(uint8_t builtin);
lean_object* initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMapFiniteSum(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_NumberTheory_LSeries_RiemannZeta(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_PSeries(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Group_InfiniteSum(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Module_FiniteDimension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMapSummation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMapReflection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMapFiniteSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_NumberTheory_LSeries_RiemannZeta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_PSeries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Normed_Group_InfiniteSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Normed_Module_FiniteDimension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
