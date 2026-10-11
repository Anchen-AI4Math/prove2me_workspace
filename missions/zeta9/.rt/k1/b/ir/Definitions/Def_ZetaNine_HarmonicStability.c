// Lean compiler output
// Module: Definitions.Def_ZetaNine_HarmonicStability
// Imports: public import Init public meta import Init public import Mathlib.Analysis.SpecialFunctions.Log.Basic public import Mathlib.Algebra.BigOperators.Group.Finset.Basic public import Mathlib.Order.Interval.Finset.Nat
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
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Mathlib_Meta_Positivity_evalLogNatLit_spec__0(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_pow(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_Icc___at___00Nat_divisorsAntidiagonal_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_HarmonicStability_harmonicPower___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_HarmonicStability_harmonicPower___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_zeta9KernelBridgeOfflineAuthor_Multiset_sum___at___00Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_add, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_zeta9KernelBridgeOfflineAuthor_Multiset_sum___at___00Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0_spec__0___closed__0 = (const lean_object*)&lp_zeta9KernelBridgeOfflineAuthor_Multiset_sum___at___00Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0_spec__0___closed__0_value;
static lean_once_cell_t lp_zeta9KernelBridgeOfflineAuthor_Multiset_sum___at___00Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_zeta9KernelBridgeOfflineAuthor_Multiset_sum___at___00Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_Multiset_sum___at___00Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_HarmonicStability_harmonicPower(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_HarmonicStability_harmonicPower___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_HarmonicStability_harmonicPower___lam__0(lean_object* v___x_1_, lean_object* v_s_2_, lean_object* v_j_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_Positivity_evalLogNatLit_spec__0(v___x_1_);
v___x_5_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_Positivity_evalLogNatLit_spec__0(v_j_3_);
v___x_6_ = l_Rat_pow(v___x_5_, v_s_2_);
v___x_7_ = l_Rat_div(v___x_4_, v___x_6_);
lean_dec_ref(v___x_4_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_HarmonicStability_harmonicPower___lam__0___boxed(lean_object* v___x_8_, lean_object* v_s_9_, lean_object* v_j_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_HarmonicStability_harmonicPower___lam__0(v___x_8_, v_s_9_, v_j_10_);
lean_dec(v_s_9_);
return v_res_11_;
}
}
static lean_object* _init_lp_zeta9KernelBridgeOfflineAuthor_Multiset_sum___at___00Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_Positivity_evalLogNatLit_spec__0(v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_Multiset_sum___at___00Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0_spec__0(lean_object* v_s_15_){
_start:
{
lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___f_16_ = ((lean_object*)(lp_zeta9KernelBridgeOfflineAuthor_Multiset_sum___at___00Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0_spec__0___closed__0));
v___x_17_ = lean_obj_once(&lp_zeta9KernelBridgeOfflineAuthor_Multiset_sum___at___00Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0_spec__0___closed__1, &lp_zeta9KernelBridgeOfflineAuthor_Multiset_sum___at___00Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0_spec__0___closed__1_once, _init_lp_zeta9KernelBridgeOfflineAuthor_Multiset_sum___at___00Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0_spec__0___closed__1);
v___x_18_ = l_List_foldrTR___redArg(v___f_16_, v___x_17_, v_s_15_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0___redArg(lean_object* v_s_19_, lean_object* v_f_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lp_mathlib_Multiset_map___redArg(v_f_20_, v_s_19_);
v___x_22_ = lp_zeta9KernelBridgeOfflineAuthor_Multiset_sum___at___00Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0_spec__0(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_HarmonicStability_harmonicPower(lean_object* v_s_23_, lean_object* v_N_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_25_ = lean_unsigned_to_nat(1u);
v___f_26_ = lean_alloc_closure((void*)(lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_HarmonicStability_harmonicPower___lam__0___boxed), 3, 2);
lean_closure_set(v___f_26_, 0, v___x_25_);
lean_closure_set(v___f_26_, 1, v_s_23_);
v___x_27_ = lp_mathlib_Finset_Icc___at___00Nat_divisorsAntidiagonal_spec__0(v___x_25_, v_N_24_);
v___x_28_ = lp_zeta9KernelBridgeOfflineAuthor_Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0___redArg(v___x_27_, v___f_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_HarmonicStability_harmonicPower___boxed(lean_object* v_s_29_, lean_object* v_N_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_HarmonicStability_harmonicPower(v_s_29_, v_N_30_);
lean_dec(v_N_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0(lean_object* v_00_u03b9_32_, lean_object* v_s_33_, lean_object* v_f_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lp_zeta9KernelBridgeOfflineAuthor_Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0___redArg(v_s_33_, v_f_34_);
return v___x_35_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_Group_Finset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Order_Interval_Finset_Nat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_zeta9KernelBridgeOfflineAuthor_Definitions_Def__ZetaNine__HarmonicStability(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_Group_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Order_Interval_Finset_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
