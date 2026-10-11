// Lean compiler output
// Module: missions.zeta9.formalization.CoefficientMapTelescoper
// Imports: public import Init public meta import Init public import missions.zeta9.formalization.CoefficientMapAggregate
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
lean_object* l_Rat_neg(lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_zeta9MatrixIndependent_Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_prefixSum___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_prefixSum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_prefixSum___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_rootNode___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_rootNode___closed__0;
LEAN_EXPORT lean_object* lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_rootNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9MatrixIndependent___private_missions_zeta9_formalization_CoefficientMapTelescoper_0__ZetaNine_CoefficientMapTelescoper_rootNode_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9MatrixIndependent___private_missions_zeta9_formalization_CoefficientMapTelescoper_0__ZetaNine_CoefficientMapTelescoper_rootNode_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9MatrixIndependent___private_missions_zeta9_formalization_CoefficientMapTelescoper_0__ZetaNine_CoefficientMapTelescoper_rootNode_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_prefixSum___lam__0(lean_object* v_c_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_c_1_, v_i_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_prefixSum(lean_object* v_c_4_, lean_object* v_j_5_){
_start:
{
lean_object* v___f_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___f_6_ = lean_alloc_closure((void*)(lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_prefixSum___lam__0), 2, 1);
lean_closure_set(v___f_6_, 0, v_c_4_);
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_add(v_j_5_, v___x_7_);
v___x_9_ = l_List_range(v___x_8_);
v___x_10_ = lp_zeta9MatrixIndependent_Finset_sum___at___00ZetaNine_HarmonicStability_harmonicPower_spec__0___redArg(v___x_9_, v___f_6_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_prefixSum___boxed(lean_object* v_c_11_, lean_object* v_j_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_prefixSum(v_c_11_, v_j_12_);
lean_dec(v_j_12_);
return v_res_13_;
}
}
static lean_object* _init_lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_rootNode___closed__0(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_rootNode(lean_object* v_n_16_, lean_object* v_i_17_){
_start:
{
if (lean_obj_tag(v_i_17_) == 0)
{
lean_object* v_val_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
lean_dec(v_n_16_);
v_val_18_ = lean_ctor_get(v_i_17_, 0);
lean_inc(v_val_18_);
lean_dec_ref_known(v_i_17_, 1);
v___x_19_ = lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(v_val_18_);
v___x_20_ = lean_obj_once(&lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_rootNode___closed__0, &lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_rootNode___closed__0_once, _init_lp_zeta9MatrixIndependent_ZetaNine_CoefficientMapTelescoper_rootNode___closed__0);
v___x_21_ = l_Rat_add(v___x_19_, v___x_20_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_val_22_ = lean_ctor_get(v_i_17_, 0);
lean_inc(v_val_22_);
lean_dec_ref_known(v_i_17_, 1);
v___x_23_ = lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(v_n_16_);
v___x_24_ = l_Rat_neg(v___x_23_);
v___x_25_ = lp_mathlib_Nat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__2(v_val_22_);
v___x_26_ = l_Rat_sub(v___x_24_, v___x_25_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* lp_zeta9MatrixIndependent___private_missions_zeta9_formalization_CoefficientMapTelescoper_0__ZetaNine_CoefficientMapTelescoper_rootNode_match__1_splitter___redArg(lean_object* v_i_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
if (lean_obj_tag(v_i_27_) == 0)
{
lean_object* v_val_30_; lean_object* v___x_31_; 
lean_dec(v_h__2_29_);
v_val_30_ = lean_ctor_get(v_i_27_, 0);
lean_inc(v_val_30_);
lean_dec_ref_known(v_i_27_, 1);
v___x_31_ = lean_apply_1(v_h__1_28_, v_val_30_);
return v___x_31_;
}
else
{
lean_object* v_val_32_; lean_object* v___x_33_; 
lean_dec(v_h__1_28_);
v_val_32_ = lean_ctor_get(v_i_27_, 0);
lean_inc(v_val_32_);
lean_dec_ref_known(v_i_27_, 1);
v___x_33_ = lean_apply_1(v_h__2_29_, v_val_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* lp_zeta9MatrixIndependent___private_missions_zeta9_formalization_CoefficientMapTelescoper_0__ZetaNine_CoefficientMapTelescoper_rootNode_match__1_splitter(lean_object* v_n_34_, lean_object* v_motive_35_, lean_object* v_i_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
if (lean_obj_tag(v_i_36_) == 0)
{
lean_object* v_val_39_; lean_object* v___x_40_; 
lean_dec(v_h__2_38_);
v_val_39_ = lean_ctor_get(v_i_36_, 0);
lean_inc(v_val_39_);
lean_dec_ref_known(v_i_36_, 1);
v___x_40_ = lean_apply_1(v_h__1_37_, v_val_39_);
return v___x_40_;
}
else
{
lean_object* v_val_41_; lean_object* v___x_42_; 
lean_dec(v_h__1_37_);
v_val_41_ = lean_ctor_get(v_i_36_, 0);
lean_inc(v_val_41_);
lean_dec_ref_known(v_i_36_, 1);
v___x_42_ = lean_apply_1(v_h__2_38_, v_val_41_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* lp_zeta9MatrixIndependent___private_missions_zeta9_formalization_CoefficientMapTelescoper_0__ZetaNine_CoefficientMapTelescoper_rootNode_match__1_splitter___boxed(lean_object* v_n_43_, lean_object* v_motive_44_, lean_object* v_i_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_zeta9MatrixIndependent___private_missions_zeta9_formalization_CoefficientMapTelescoper_0__ZetaNine_CoefficientMapTelescoper_rootNode_match__1_splitter(v_n_43_, v_motive_44_, v_i_45_, v_h__1_46_, v_h__2_47_);
lean_dec(v_n_43_);
return v_res_48_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_zeta9MatrixIndependent_missions_zeta9_formalization_CoefficientMapAggregate(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_zeta9MatrixIndependent_missions_zeta9_formalization_CoefficientMapTelescoper(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_zeta9MatrixIndependent_missions_zeta9_formalization_CoefficientMapAggregate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
