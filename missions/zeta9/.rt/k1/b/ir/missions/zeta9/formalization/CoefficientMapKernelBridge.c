// Lean compiler output
// Module: missions.zeta9.formalization.CoefficientMapKernelBridge
// Imports: public import Init public meta import Init public import missions.zeta9.formalization.CoefficientMapTelescoper public import missions.zeta9.formalization.CoefficientMapShiftDegree public import Mathlib.Order.Interval.Set.Infinite
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
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* l_Rat_pow(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_zeta9KernelBridgeOfflineAuthor_Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0___redArg(lean_object*, lean_object*);
static lean_once_cell_t lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_negativeProduct___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_negativeProduct(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_aValue(lean_object*, lean_object*);
static lean_once_cell_t lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_bValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_bValue___closed__0;
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_bValue(lean_object*, lean_object*);
static lean_object* _init_lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0(lean_object* v_t_3_, lean_object* v_k_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(v_k_4_);
v___x_6_ = lean_obj_once(&lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0, &lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0_once, _init_lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0);
v___x_7_ = l_Rat_add(v___x_5_, v___x_6_);
v___x_8_ = l_Rat_sub(v_t_3_, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct(lean_object* v_n_9_, lean_object* v_t_10_){
_start:
{
lean_object* v___f_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___f_11_ = lean_alloc_closure((void*)(lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0), 2, 1);
lean_closure_set(v___f_11_, 0, v_t_10_);
v___x_12_ = l_List_range(v_n_9_);
v___x_13_ = lp_zeta9KernelBridgeOfflineAuthor_Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0___redArg(v___x_12_, v___f_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_negativeProduct___lam__0(lean_object* v_n_14_, lean_object* v_t_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_17_ = lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(v_n_14_);
v___x_18_ = l_Rat_add(v_t_15_, v___x_17_);
v___x_19_ = lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(v_k_16_);
v___x_20_ = lean_obj_once(&lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0, &lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0_once, _init_lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0);
v___x_21_ = l_Rat_add(v___x_19_, v___x_20_);
v___x_22_ = l_Rat_add(v___x_18_, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_negativeProduct(lean_object* v_n_23_, lean_object* v_t_24_){
_start:
{
lean_object* v___f_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
lean_inc(v_n_23_);
v___f_25_ = lean_alloc_closure((void*)(lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_negativeProduct___lam__0), 3, 2);
lean_closure_set(v___f_25_, 0, v_n_23_);
lean_closure_set(v___f_25_, 1, v_t_24_);
v___x_26_ = l_List_range(v_n_23_);
v___x_27_ = lp_zeta9KernelBridgeOfflineAuthor_Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0___redArg(v___x_26_, v___f_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_aValue(lean_object* v_n_28_, lean_object* v_t_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_30_ = lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(v_n_28_);
lean_inc_ref(v___x_30_);
lean_inc_ref(v_t_29_);
v___x_31_ = l_Rat_sub(v_t_29_, v___x_30_);
v___x_32_ = lean_obj_once(&lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0, &lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0_once, _init_lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0);
v___x_33_ = l_Rat_sub(v___x_31_, v___x_32_);
v___x_34_ = l_Rat_add(v_t_29_, v___x_30_);
v___x_35_ = lean_unsigned_to_nat(10u);
v___x_36_ = l_Rat_pow(v___x_34_, v___x_35_);
v___x_37_ = l_Rat_mul(v___x_33_, v___x_36_);
lean_dec_ref(v___x_33_);
return v___x_37_;
}
}
static lean_object* _init_lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_bValue___closed__0(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_unsigned_to_nat(2u);
v___x_39_ = lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_bValue(lean_object* v_n_40_, lean_object* v_t_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_42_ = lean_unsigned_to_nat(10u);
lean_inc_ref(v_t_41_);
v___x_43_ = l_Rat_pow(v_t_41_, v___x_42_);
v___x_44_ = lean_obj_once(&lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_bValue___closed__0, &lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_bValue___closed__0_once, _init_lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_bValue___closed__0);
v___x_45_ = lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(v_n_40_);
v___x_46_ = l_Rat_mul(v___x_44_, v___x_45_);
v___x_47_ = l_Rat_add(v_t_41_, v___x_46_);
v___x_48_ = lean_obj_once(&lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0, &lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0_once, _init_lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0);
v___x_49_ = l_Rat_add(v___x_47_, v___x_48_);
v___x_50_ = l_Rat_mul(v___x_43_, v___x_49_);
lean_dec_ref(v___x_43_);
return v___x_50_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMapTelescoper(uint8_t builtin);
lean_object* initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMapShiftDegree(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Order_Interval_Set_Infinite(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMapKernelBridge(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMapTelescoper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMapShiftDegree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Order_Interval_Set_Infinite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
