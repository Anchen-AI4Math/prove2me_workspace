// Lean compiler output
// Module: missions.zeta9.formalization.CoefficientMap
// Imports: public import Init public meta import Init public import Mathlib.Algebra.Polynomial.Eval.Defs public import Mathlib.Algebra.BigOperators.Ring.Finset public import Mathlib.Data.Nat.Choose.Cast public import Mathlib.Data.Nat.Factorial.BigOperators public import Mathlib.Tactic
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
lean_object* lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Multiset_erase___at___00Nat_Partition_partitionWithPartEquiv_spec__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* l_Rat_mul___boxed(lean_object*, lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Rat_commSemiring;
lean_object* lp_mathlib_Polynomial_definition_00___x40_Mathlib_Algebra_Polynomial_Eval_Defs_2849575019____hygCtx___hyg_2____at___00Polynomial_wrapped___elam__0_00___x40_Mathlib_Algebra_Polynomial_Eval_Defs_2849575019____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_factorialBinarySplitting(lean_object*);
lean_object* l_Rat_pow(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* l_Rat_neg(lean_object*);
static lean_once_cell_t lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__1(lean_object*, lean_object*);
static const lean_closure_object lp_zeta9TelescoperOfflineAuthor_Multiset_prod___at___00Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_zeta9TelescoperOfflineAuthor_Multiset_prod___at___00Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0_spec__0___closed__0 = (const lean_object*)&lp_zeta9TelescoperOfflineAuthor_Multiset_prod___at___00Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Multiset_prod___at___00Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_poleProduct___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_poleProduct(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_poleProduct___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_actualR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedPoleProduct(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedPoleProduct___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedR___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_leadingPoleCoefficient(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Polynomial_eval_u2082___at___00Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_zeta9TelescoperOfflineAuthor_Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_zeta9TelescoperOfflineAuthor_Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0___closed__0 = (const lean_object*)&lp_zeta9TelescoperOfflineAuthor_Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_weightedR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedWeightedR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedWeightedR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_weightedLeadingPoleCoefficient(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0(lean_object* v_n_3_, lean_object* v_t_4_, lean_object* v_i_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_6_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v_n_3_);
v___x_7_ = l_Rat_add(v_t_4_, v___x_6_);
v___x_8_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v_i_5_);
v___x_9_ = lean_obj_once(&lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0___closed__0, &lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0___closed__0_once, _init_lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0___closed__0);
v___x_10_ = l_Rat_add(v___x_8_, v___x_9_);
v___x_11_ = l_Rat_add(v___x_7_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__1(lean_object* v_t_12_, lean_object* v_i_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_14_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v_i_13_);
v___x_15_ = lean_obj_once(&lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0___closed__0, &lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0___closed__0_once, _init_lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0___closed__0);
v___x_16_ = l_Rat_add(v___x_14_, v___x_15_);
v___x_17_ = l_Rat_sub(v_t_12_, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Multiset_prod___at___00Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0_spec__0(lean_object* v_s_19_){
_start:
{
lean_object* v___f_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___f_20_ = ((lean_object*)(lp_zeta9TelescoperOfflineAuthor_Multiset_prod___at___00Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0_spec__0___closed__0));
v___x_21_ = lean_obj_once(&lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0___closed__0, &lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0___closed__0_once, _init_lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0___closed__0);
v___x_22_ = l_List_foldrTR___redArg(v___f_20_, v___x_21_, v_s_19_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0___redArg(lean_object* v_s_23_, lean_object* v_f_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lp_mathlib_Multiset_map___redArg(v_f_24_, v_s_23_);
v___x_26_ = lp_zeta9TelescoperOfflineAuthor_Multiset_prod___at___00Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0_spec__0(v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator(lean_object* v_n_27_, lean_object* v_t_28_){
_start:
{
lean_object* v___f_29_; lean_object* v___f_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
lean_inc_ref(v_t_28_);
lean_inc(v_n_27_);
v___f_29_ = lean_alloc_closure((void*)(lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0), 3, 2);
lean_closure_set(v___f_29_, 0, v_n_27_);
lean_closure_set(v___f_29_, 1, v_t_28_);
v___f_30_ = lean_alloc_closure((void*)(lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__1), 2, 1);
lean_closure_set(v___f_30_, 0, v_t_28_);
v___x_31_ = lp_mathlib_Nat_factorialBinarySplitting(v_n_27_);
v___x_32_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v___x_31_);
v___x_33_ = lean_unsigned_to_nat(7u);
v___x_34_ = l_Rat_pow(v___x_32_, v___x_33_);
v___x_35_ = l_List_range(v_n_27_);
lean_inc(v___x_35_);
v___x_36_ = lp_zeta9TelescoperOfflineAuthor_Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0___redArg(v___x_35_, v___f_30_);
v___x_37_ = l_Rat_mul(v___x_34_, v___x_36_);
lean_dec_ref(v___x_34_);
v___x_38_ = lp_zeta9TelescoperOfflineAuthor_Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0___redArg(v___x_35_, v___f_29_);
v___x_39_ = l_Rat_mul(v___x_37_, v___x_38_);
lean_dec_ref(v___x_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0(lean_object* v_00_u03b9_40_, lean_object* v_s_41_, lean_object* v_f_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_zeta9TelescoperOfflineAuthor_Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0___redArg(v_s_41_, v_f_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_poleProduct___lam__0(lean_object* v_t_44_, lean_object* v_k_45_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v_k_45_);
v___x_47_ = l_Rat_add(v_t_44_, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_poleProduct(lean_object* v_n_48_, lean_object* v_t_49_){
_start:
{
lean_object* v___f_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___f_50_ = lean_alloc_closure((void*)(lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_poleProduct___lam__0), 2, 1);
lean_closure_set(v___f_50_, 0, v_t_49_);
v___x_51_ = lean_unsigned_to_nat(1u);
v___x_52_ = lean_nat_add(v_n_48_, v___x_51_);
v___x_53_ = l_List_range(v___x_52_);
v___x_54_ = lp_zeta9TelescoperOfflineAuthor_Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0___redArg(v___x_53_, v___f_50_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_poleProduct___boxed(lean_object* v_n_55_, lean_object* v_t_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_poleProduct(v_n_55_, v_t_56_);
lean_dec(v_n_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_actualR(lean_object* v_n_58_, lean_object* v_t_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
lean_inc_ref(v_t_59_);
lean_inc(v_n_58_);
v___x_60_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator(v_n_58_, v_t_59_);
v___x_61_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_poleProduct(v_n_58_, v_t_59_);
lean_dec(v_n_58_);
v___x_62_ = lean_unsigned_to_nat(9u);
v___x_63_ = l_Rat_pow(v___x_61_, v___x_62_);
v___x_64_ = l_Rat_div(v___x_60_, v___x_63_);
lean_dec_ref(v___x_60_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0(lean_object* v_s_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lp_mathlib_Multiset_erase___at___00Nat_Partition_partitionWithPartEquiv_spec__0(v_s_65_, v_a_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0___boxed(lean_object* v_s_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = lp_zeta9TelescoperOfflineAuthor_Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0(v_s_68_, v_a_69_);
lean_dec(v_a_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedPoleProduct(lean_object* v_n_71_, lean_object* v_j_72_, lean_object* v_t_73_){
_start:
{
lean_object* v___f_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___f_74_ = lean_alloc_closure((void*)(lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_poleProduct___lam__0), 2, 1);
lean_closure_set(v___f_74_, 0, v_t_73_);
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_add(v_n_71_, v___x_75_);
v___x_77_ = l_List_range(v___x_76_);
v___x_78_ = lp_mathlib_Multiset_erase___at___00Nat_Partition_partitionWithPartEquiv_spec__0(v___x_77_, v_j_72_);
v___x_79_ = lp_zeta9TelescoperOfflineAuthor_Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0___redArg(v___x_78_, v___f_74_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedPoleProduct___boxed(lean_object* v_n_80_, lean_object* v_j_81_, lean_object* v_t_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedPoleProduct(v_n_80_, v_j_81_, v_t_82_);
lean_dec(v_j_81_);
lean_dec(v_n_80_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedR(lean_object* v_n_84_, lean_object* v_j_85_, lean_object* v_t_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
lean_inc_ref(v_t_86_);
lean_inc(v_n_84_);
v___x_87_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator(v_n_84_, v_t_86_);
v___x_88_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedPoleProduct(v_n_84_, v_j_85_, v_t_86_);
lean_dec(v_n_84_);
v___x_89_ = lean_unsigned_to_nat(9u);
v___x_90_ = l_Rat_pow(v___x_88_, v___x_89_);
v___x_91_ = l_Rat_div(v___x_87_, v___x_90_);
lean_dec_ref(v___x_87_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedR___boxed(lean_object* v_n_92_, lean_object* v_j_93_, lean_object* v_t_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedR(v_n_92_, v_j_93_, v_t_94_);
lean_dec(v_j_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_leadingPoleCoefficient(lean_object* v_n_96_, lean_object* v_j_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
lean_inc(v_j_97_);
v___x_98_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v_j_97_);
v___x_99_ = l_Rat_neg(v___x_98_);
v___x_100_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedR(v_n_96_, v_j_97_, v___x_99_);
lean_dec(v_j_97_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Polynomial_eval_u2082___at___00Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0_spec__0(lean_object* v_f_101_, lean_object* v_x_102_, lean_object* v_p_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lp_mathlib_Rat_commSemiring;
v___x_105_ = lp_mathlib_Polynomial_definition_00___x40_Mathlib_Algebra_Polynomial_Eval_Defs_2849575019____hygCtx___hyg_2____at___00Polynomial_wrapped___elam__0_00___x40_Mathlib_Algebra_Polynomial_Eval_Defs_2849575019____hygCtx___hyg_2__spec__0___redArg(v___x_104_, v___x_104_, v_f_101_, v_x_102_, v_p_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0(lean_object* v_x_107_, lean_object* v_p_108_){
_start:
{
lean_object* v___f_109_; lean_object* v___x_110_; 
v___f_109_ = ((lean_object*)(lp_zeta9TelescoperOfflineAuthor_Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0___closed__0));
v___x_110_ = lp_zeta9TelescoperOfflineAuthor_Polynomial_eval_u2082___at___00Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0_spec__0(v___f_109_, v_x_107_, v_p_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_weightedR(lean_object* v_n_111_, lean_object* v_W_112_, lean_object* v_t_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
lean_inc_ref_n(v_t_113_, 2);
lean_inc(v_n_111_);
v___x_114_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_actualR(v_n_111_, v_t_113_);
v___x_115_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v_n_111_);
v___x_116_ = l_Rat_add(v_t_113_, v___x_115_);
v___x_117_ = l_Rat_mul(v_t_113_, v___x_116_);
lean_dec_ref(v_t_113_);
v___x_118_ = lp_zeta9TelescoperOfflineAuthor_Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0(v___x_117_, v_W_112_);
v___x_119_ = l_Rat_mul(v___x_114_, v___x_118_);
lean_dec_ref(v___x_114_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedWeightedR(lean_object* v_n_120_, lean_object* v_j_121_, lean_object* v_W_122_, lean_object* v_t_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
lean_inc_ref_n(v_t_123_, 2);
lean_inc(v_n_120_);
v___x_124_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedR(v_n_120_, v_j_121_, v_t_123_);
v___x_125_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v_n_120_);
v___x_126_ = l_Rat_add(v_t_123_, v___x_125_);
v___x_127_ = l_Rat_mul(v_t_123_, v___x_126_);
lean_dec_ref(v_t_123_);
v___x_128_ = lp_zeta9TelescoperOfflineAuthor_Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0(v___x_127_, v_W_122_);
v___x_129_ = l_Rat_mul(v___x_124_, v___x_128_);
lean_dec_ref(v___x_124_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedWeightedR___boxed(lean_object* v_n_130_, lean_object* v_j_131_, lean_object* v_W_132_, lean_object* v_t_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedWeightedR(v_n_130_, v_j_131_, v_W_132_, v_t_133_);
lean_dec(v_j_131_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_weightedLeadingPoleCoefficient(lean_object* v_n_135_, lean_object* v_j_136_, lean_object* v_W_137_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
lean_inc(v_j_136_);
v___x_138_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v_j_136_);
v___x_139_ = l_Rat_neg(v___x_138_);
v___x_140_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedWeightedR(v_n_135_, v_j_136_, v_W_137_, v___x_139_);
lean_dec(v_j_136_);
return v___x_140_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_Eval_Defs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_Ring_Finset(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Nat_Choose_Cast(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Nat_Factorial_BigOperators(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_zeta9TelescoperOfflineAuthor_missions_zeta9_formalization_CoefficientMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Polynomial_Eval_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_Ring_Finset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Nat_Choose_Cast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Nat_Factorial_BigOperators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
