// Lean compiler output
// Module: Definitions.Def_ZetaNine_CoefficientMap
// Imports: public import Init public meta import Init public import Mathlib.Algebra.Polynomial.Eval.Defs public import Mathlib.Algebra.BigOperators.Ring.Finset public import Mathlib.Data.Nat.Choose.Cast public import Mathlib.Data.Nat.Factorial.BigOperators
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
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
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object lp_zeta9TelescoperOfflineAuthor_Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_zeta9TelescoperOfflineAuthor_Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0___closed__0 = (const lean_object*)&lp_zeta9TelescoperOfflineAuthor_Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0___boxed(lean_object*, lean_object*);
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
v___x_2_ = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator___lam__0(lean_object* v_n_3_, lean_object* v_t_4_, lean_object* v_i_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_6_ = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(v_n_3_);
v___x_7_ = l_Rat_add(v_t_4_, v___x_6_);
v___x_8_ = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(v_i_5_);
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
v___x_14_ = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(v_i_13_);
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
v___x_32_ = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(v___x_31_);
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
v___x_46_ = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(v_k_45_);
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
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_65_, size_t v_i_66_, size_t v_stop_67_, lean_object* v_b_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = lean_usize_dec_eq(v_i_66_, v_stop_67_);
if (v___x_69_ == 0)
{
size_t v___x_70_; size_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = ((size_t)1ULL);
v___x_71_ = lean_usize_sub(v_i_66_, v___x_70_);
v___x_72_ = lean_array_uget_borrowed(v_as_65_, v___x_71_);
lean_inc(v___x_72_);
v___x_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v_b_68_);
v_i_66_ = v___x_71_;
v_b_68_ = v___x_73_;
goto _start;
}
else
{
return v_b_68_;
}
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_75_, lean_object* v_i_76_, lean_object* v_stop_77_, lean_object* v_b_78_){
_start:
{
size_t v_i_boxed_79_; size_t v_stop_boxed_80_; lean_object* v_res_81_; 
v_i_boxed_79_ = lean_unbox_usize(v_i_76_);
lean_dec(v_i_76_);
v_stop_boxed_80_ = lean_unbox_usize(v_stop_77_);
lean_dec(v_stop_77_);
v_res_81_ = lp_zeta9TelescoperOfflineAuthor___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0_spec__1_spec__2(v_as_75_, v_i_boxed_79_, v_stop_boxed_80_, v_b_78_);
lean_dec_ref(v_as_75_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0_spec__1(lean_object* v_l_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
if (lean_obj_tag(v_a_84_) == 0)
{
lean_dec_ref(v_a_85_);
lean_inc(v_l_82_);
return v_l_82_;
}
else
{
lean_object* v_head_86_; lean_object* v_tail_87_; uint8_t v___x_88_; 
v_head_86_ = lean_ctor_get(v_a_84_, 0);
lean_inc(v_head_86_);
v_tail_87_ = lean_ctor_get(v_a_84_, 1);
lean_inc(v_tail_87_);
lean_dec_ref_known(v_a_84_, 2);
v___x_88_ = lean_nat_dec_eq(v_head_86_, v_a_83_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; 
v___x_89_ = lean_array_push(v_a_85_, v_head_86_);
v_a_84_ = v_tail_87_;
v_a_85_ = v___x_89_;
goto _start;
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
lean_dec(v_head_86_);
v___x_91_ = lean_array_get_size(v_a_85_);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_nat_dec_lt(v___x_92_, v___x_91_);
if (v___x_93_ == 0)
{
lean_dec_ref(v_a_85_);
return v_tail_87_;
}
else
{
size_t v___x_94_; size_t v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_usize_of_nat(v___x_91_);
v___x_95_ = ((size_t)0ULL);
v___x_96_ = lp_zeta9TelescoperOfflineAuthor___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0_spec__1_spec__2(v_a_85_, v___x_94_, v___x_95_, v_tail_87_);
lean_dec_ref(v_a_85_);
return v___x_96_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0_spec__1___boxed(lean_object* v_l_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = lp_zeta9TelescoperOfflineAuthor___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0_spec__1(v_l_97_, v_a_98_, v_a_99_, v_a_100_);
lean_dec(v_a_98_);
lean_dec(v_l_97_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0(lean_object* v_s_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = ((lean_object*)(lp_zeta9TelescoperOfflineAuthor_Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0___closed__0));
lean_inc(v_s_104_);
v___x_107_ = lp_zeta9TelescoperOfflineAuthor___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0_spec__1(v_s_104_, v_a_105_, v_s_104_, v___x_106_);
lean_dec(v_s_104_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0___boxed(lean_object* v_s_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = lp_zeta9TelescoperOfflineAuthor_Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0(v_s_108_, v_a_109_);
lean_dec(v_a_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0(lean_object* v_s_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lp_zeta9TelescoperOfflineAuthor_Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0(v_s_111_, v_a_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0___boxed(lean_object* v_s_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = lp_zeta9TelescoperOfflineAuthor_Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0(v_s_114_, v_a_115_);
lean_dec(v_a_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedPoleProduct(lean_object* v_n_117_, lean_object* v_j_118_, lean_object* v_t_119_){
_start:
{
lean_object* v___f_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___f_120_ = lean_alloc_closure((void*)(lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_poleProduct___lam__0), 2, 1);
lean_closure_set(v___f_120_, 0, v_t_119_);
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_nat_add(v_n_117_, v___x_121_);
v___x_123_ = l_List_range(v___x_122_);
v___x_124_ = lp_zeta9TelescoperOfflineAuthor_Multiset_erase___at___00Finset_erase___at___00ZetaNine_CoefficientMap_clearedPoleProduct_spec__0_spec__0(v___x_123_, v_j_118_);
v___x_125_ = lp_zeta9TelescoperOfflineAuthor_Finset_prod___at___00ZetaNine_CoefficientMap_numerator_spec__0___redArg(v___x_124_, v___f_120_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedPoleProduct___boxed(lean_object* v_n_126_, lean_object* v_j_127_, lean_object* v_t_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedPoleProduct(v_n_126_, v_j_127_, v_t_128_);
lean_dec(v_j_127_);
lean_dec(v_n_126_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedR(lean_object* v_n_130_, lean_object* v_j_131_, lean_object* v_t_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
lean_inc_ref(v_t_132_);
lean_inc(v_n_130_);
v___x_133_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_numerator(v_n_130_, v_t_132_);
v___x_134_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedPoleProduct(v_n_130_, v_j_131_, v_t_132_);
lean_dec(v_n_130_);
v___x_135_ = lean_unsigned_to_nat(9u);
v___x_136_ = l_Rat_pow(v___x_134_, v___x_135_);
v___x_137_ = l_Rat_div(v___x_133_, v___x_136_);
lean_dec_ref(v___x_133_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedR___boxed(lean_object* v_n_138_, lean_object* v_j_139_, lean_object* v_t_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedR(v_n_138_, v_j_139_, v_t_140_);
lean_dec(v_j_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_leadingPoleCoefficient(lean_object* v_n_142_, lean_object* v_j_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
lean_inc(v_j_143_);
v___x_144_ = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(v_j_143_);
v___x_145_ = l_Rat_neg(v___x_144_);
v___x_146_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedR(v_n_142_, v_j_143_, v___x_145_);
lean_dec(v_j_143_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Polynomial_eval_u2082___at___00Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0_spec__0(lean_object* v_f_147_, lean_object* v_x_148_, lean_object* v_p_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lp_mathlib_Rat_commSemiring;
v___x_151_ = lp_mathlib_Polynomial_definition_00___x40_Mathlib_Algebra_Polynomial_Eval_Defs_2849575019____hygCtx___hyg_2____at___00Polynomial_wrapped___elam__0_00___x40_Mathlib_Algebra_Polynomial_Eval_Defs_2849575019____hygCtx___hyg_2__spec__0___redArg(v___x_150_, v___x_150_, v_f_147_, v_x_148_, v_p_149_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0(lean_object* v_x_153_, lean_object* v_p_154_){
_start:
{
lean_object* v___f_155_; lean_object* v___x_156_; 
v___f_155_ = ((lean_object*)(lp_zeta9TelescoperOfflineAuthor_Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0___closed__0));
v___x_156_ = lp_zeta9TelescoperOfflineAuthor_Polynomial_eval_u2082___at___00Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0_spec__0(v___f_155_, v_x_153_, v_p_154_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_weightedR(lean_object* v_n_157_, lean_object* v_W_158_, lean_object* v_t_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
lean_inc_ref_n(v_t_159_, 2);
lean_inc(v_n_157_);
v___x_160_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_actualR(v_n_157_, v_t_159_);
v___x_161_ = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(v_n_157_);
v___x_162_ = l_Rat_add(v_t_159_, v___x_161_);
v___x_163_ = l_Rat_mul(v_t_159_, v___x_162_);
lean_dec_ref(v_t_159_);
v___x_164_ = lp_zeta9TelescoperOfflineAuthor_Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0(v___x_163_, v_W_158_);
v___x_165_ = l_Rat_mul(v___x_160_, v___x_164_);
lean_dec_ref(v___x_160_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedWeightedR(lean_object* v_n_166_, lean_object* v_j_167_, lean_object* v_W_168_, lean_object* v_t_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
lean_inc_ref_n(v_t_169_, 2);
lean_inc(v_n_166_);
v___x_170_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedR(v_n_166_, v_j_167_, v_t_169_);
v___x_171_ = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(v_n_166_);
v___x_172_ = l_Rat_add(v_t_169_, v___x_171_);
v___x_173_ = l_Rat_mul(v_t_169_, v___x_172_);
lean_dec_ref(v_t_169_);
v___x_174_ = lp_zeta9TelescoperOfflineAuthor_Polynomial_eval___at___00ZetaNine_CoefficientMap_weightedR_spec__0(v___x_173_, v_W_168_);
v___x_175_ = l_Rat_mul(v___x_170_, v___x_174_);
lean_dec_ref(v___x_170_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedWeightedR___boxed(lean_object* v_n_176_, lean_object* v_j_177_, lean_object* v_W_178_, lean_object* v_t_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedWeightedR(v_n_176_, v_j_177_, v_W_178_, v_t_179_);
lean_dec(v_j_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_weightedLeadingPoleCoefficient(lean_object* v_n_181_, lean_object* v_j_182_, lean_object* v_W_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
lean_inc(v_j_182_);
v___x_184_ = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(v_j_182_);
v___x_185_ = l_Rat_neg(v___x_184_);
v___x_186_ = lp_zeta9TelescoperOfflineAuthor_ZetaNine_CoefficientMap_clearedWeightedR(v_n_181_, v_j_182_, v_W_183_, v___x_185_);
lean_dec(v_j_182_);
return v___x_186_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_Eval_Defs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_Ring_Finset(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Nat_Choose_Cast(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Nat_Factorial_BigOperators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_zeta9TelescoperOfflineAuthor_Definitions_Def__ZetaNine__CoefficientMap(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
