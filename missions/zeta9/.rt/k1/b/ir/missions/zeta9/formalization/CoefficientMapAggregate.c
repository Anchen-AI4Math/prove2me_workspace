// Lean compiler output
// Module: missions.zeta9.formalization.CoefficientMapAggregate
// Imports: public import Init public meta import Init public import missions.zeta9.formalization.CoefficientMapSummation public import Mathlib.Algebra.Polynomial.Eval.SMul public import Mathlib.Algebra.Polynomial.BigOperators
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_Polynomial_coeff___at___00ZetaNine_CoefficientMapAggregate_polynomialCoordinates_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapAggregate_polynomialCoordinates(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor___private_missions_zeta9_formalization_CoefficientMapAggregate_0__ZetaNine_CoefficientMapAggregate_aggregate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor___private_missions_zeta9_formalization_CoefficientMapAggregate_0__ZetaNine_CoefficientMapAggregate_aggregate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_Polynomial_coeff___at___00ZetaNine_CoefficientMapAggregate_polynomialCoordinates_spec__0(lean_object* v_x_1_, lean_object* v_a_2_){
_start:
{
lean_object* v_toFun_3_; lean_object* v___x_4_; 
v_toFun_3_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_toFun_3_);
lean_dec_ref(v_x_1_);
v___x_4_ = lean_apply_1(v_toFun_3_, v_a_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapAggregate_polynomialCoordinates(lean_object* v_W_5_, lean_object* v_i_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lp_zeta9KernelBridgeOfflineAuthor_Polynomial_coeff___at___00ZetaNine_CoefficientMapAggregate_polynomialCoordinates_spec__0(v_W_5_, v_i_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor___private_missions_zeta9_formalization_CoefficientMapAggregate_0__ZetaNine_CoefficientMapAggregate_aggregate_match__1_splitter___redArg(lean_object* v_x_8_, lean_object* v_h__1_9_, lean_object* v_h__2_10_, lean_object* v_h__3_11_, lean_object* v_h__4_12_, lean_object* v_h__5_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_nat_dec_eq(v_x_8_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; uint8_t v___x_17_; 
lean_dec(v_h__1_9_);
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_nat_dec_eq(v_x_8_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; uint8_t v___x_19_; 
lean_dec(v_h__2_10_);
v___x_18_ = lean_unsigned_to_nat(2u);
v___x_19_ = lean_nat_dec_eq(v_x_8_, v___x_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; uint8_t v___x_21_; 
lean_dec(v_h__3_11_);
v___x_20_ = lean_unsigned_to_nat(3u);
v___x_21_ = lean_nat_dec_eq(v_x_8_, v___x_20_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; 
lean_dec(v_h__4_12_);
v___x_22_ = lean_apply_5(v_h__5_13_, v_x_8_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_22_;
}
else
{
lean_object* v___x_23_; lean_object* v___x_24_; 
lean_dec(v_h__5_13_);
lean_dec(v_x_8_);
v___x_23_ = lean_box(0);
v___x_24_ = lean_apply_1(v_h__4_12_, v___x_23_);
return v___x_24_;
}
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; 
lean_dec(v_h__5_13_);
lean_dec(v_h__4_12_);
lean_dec(v_x_8_);
v___x_25_ = lean_box(0);
v___x_26_ = lean_apply_1(v_h__3_11_, v___x_25_);
return v___x_26_;
}
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; 
lean_dec(v_h__5_13_);
lean_dec(v_h__4_12_);
lean_dec(v_h__3_11_);
lean_dec(v_x_8_);
v___x_27_ = lean_box(0);
v___x_28_ = lean_apply_1(v_h__2_10_, v___x_27_);
return v___x_28_;
}
}
else
{
lean_object* v___x_29_; lean_object* v___x_30_; 
lean_dec(v_h__5_13_);
lean_dec(v_h__4_12_);
lean_dec(v_h__3_11_);
lean_dec(v_h__2_10_);
lean_dec(v_x_8_);
v___x_29_ = lean_box(0);
v___x_30_ = lean_apply_1(v_h__1_9_, v___x_29_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor___private_missions_zeta9_formalization_CoefficientMapAggregate_0__ZetaNine_CoefficientMapAggregate_aggregate_match__1_splitter(lean_object* v_motive_31_, lean_object* v_x_32_, lean_object* v_h__1_33_, lean_object* v_h__2_34_, lean_object* v_h__3_35_, lean_object* v_h__4_36_, lean_object* v_h__5_37_){
_start:
{
lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_38_ = lean_unsigned_to_nat(0u);
v___x_39_ = lean_nat_dec_eq(v_x_32_, v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; uint8_t v___x_41_; 
lean_dec(v_h__1_33_);
v___x_40_ = lean_unsigned_to_nat(1u);
v___x_41_ = lean_nat_dec_eq(v_x_32_, v___x_40_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; uint8_t v___x_43_; 
lean_dec(v_h__2_34_);
v___x_42_ = lean_unsigned_to_nat(2u);
v___x_43_ = lean_nat_dec_eq(v_x_32_, v___x_42_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; uint8_t v___x_45_; 
lean_dec(v_h__3_35_);
v___x_44_ = lean_unsigned_to_nat(3u);
v___x_45_ = lean_nat_dec_eq(v_x_32_, v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; 
lean_dec(v_h__4_36_);
v___x_46_ = lean_apply_5(v_h__5_37_, v_x_32_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_46_;
}
else
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_h__5_37_);
lean_dec(v_x_32_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_apply_1(v_h__4_36_, v___x_47_);
return v___x_48_;
}
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_h__5_37_);
lean_dec(v_h__4_36_);
lean_dec(v_x_32_);
v___x_49_ = lean_box(0);
v___x_50_ = lean_apply_1(v_h__3_35_, v___x_49_);
return v___x_50_;
}
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec(v_h__5_37_);
lean_dec(v_h__4_36_);
lean_dec(v_h__3_35_);
lean_dec(v_x_32_);
v___x_51_ = lean_box(0);
v___x_52_ = lean_apply_1(v_h__2_34_, v___x_51_);
return v___x_52_;
}
}
else
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec(v_h__5_37_);
lean_dec(v_h__4_36_);
lean_dec(v_h__3_35_);
lean_dec(v_h__2_34_);
lean_dec(v_x_32_);
v___x_53_ = lean_box(0);
v___x_54_ = lean_apply_1(v_h__1_33_, v___x_53_);
return v___x_54_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMapSummation(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_Eval_SMul(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_BigOperators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMapAggregate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMapSummation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Polynomial_Eval_SMul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Polynomial_BigOperators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
