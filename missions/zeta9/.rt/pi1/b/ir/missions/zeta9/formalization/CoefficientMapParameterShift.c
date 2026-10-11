// Lean compiler output
// Module: missions.zeta9.formalization.CoefficientMapParameterShift
// Imports: public import Init public meta import Init public import missions.zeta9.formalization.CoefficientMapKernelBridge public import missions.zeta9.formalization.CoefficientMapConnection
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
lean_object* lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_pow(lean_object*, lean_object*);
static lean_once_cell_t lp_zeta9ParameterShiftIndependent_ZetaNine_CoefficientMapParameterShift_parameterScale___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_zeta9ParameterShiftIndependent_ZetaNine_CoefficientMapParameterShift_parameterScale___closed__0;
static lean_once_cell_t lp_zeta9ParameterShiftIndependent_ZetaNine_CoefficientMapParameterShift_parameterScale___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_zeta9ParameterShiftIndependent_ZetaNine_CoefficientMapParameterShift_parameterScale___closed__1;
LEAN_EXPORT lean_object* lp_zeta9ParameterShiftIndependent_ZetaNine_CoefficientMapParameterShift_parameterScale(lean_object*);
static lean_object* _init_lp_zeta9ParameterShiftIndependent_ZetaNine_CoefficientMapParameterShift_parameterScale___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_zeta9ParameterShiftIndependent_ZetaNine_CoefficientMapParameterShift_parameterScale___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(2u);
v___x_4_ = lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_zeta9ParameterShiftIndependent_ZetaNine_CoefficientMapParameterShift_parameterScale(lean_object* v_n_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_6_ = lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(v_n_5_);
v___x_7_ = lean_obj_once(&lp_zeta9ParameterShiftIndependent_ZetaNine_CoefficientMapParameterShift_parameterScale___closed__0, &lp_zeta9ParameterShiftIndependent_ZetaNine_CoefficientMapParameterShift_parameterScale___closed__0_once, _init_lp_zeta9ParameterShiftIndependent_ZetaNine_CoefficientMapParameterShift_parameterScale___closed__0);
lean_inc_ref(v___x_6_);
v___x_8_ = l_Rat_add(v___x_6_, v___x_7_);
v___x_9_ = lean_obj_once(&lp_zeta9ParameterShiftIndependent_ZetaNine_CoefficientMapParameterShift_parameterScale___closed__1, &lp_zeta9ParameterShiftIndependent_ZetaNine_CoefficientMapParameterShift_parameterScale___closed__1_once, _init_lp_zeta9ParameterShiftIndependent_ZetaNine_CoefficientMapParameterShift_parameterScale___closed__1);
v___x_10_ = l_Rat_add(v___x_6_, v___x_9_);
v___x_11_ = l_Rat_mul(v___x_8_, v___x_10_);
lean_dec_ref(v___x_8_);
v___x_12_ = lean_unsigned_to_nat(7u);
v___x_13_ = l_Rat_pow(v___x_11_, v___x_12_);
return v___x_13_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_zeta9ParameterShiftIndependent_missions_zeta9_formalization_CoefficientMapKernelBridge(uint8_t builtin);
lean_object* initialize_zeta9ParameterShiftIndependent_missions_zeta9_formalization_CoefficientMapConnection(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_zeta9ParameterShiftIndependent_missions_zeta9_formalization_CoefficientMapParameterShift(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_zeta9ParameterShiftIndependent_missions_zeta9_formalization_CoefficientMapKernelBridge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_zeta9ParameterShiftIndependent_missions_zeta9_formalization_CoefficientMapConnection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
