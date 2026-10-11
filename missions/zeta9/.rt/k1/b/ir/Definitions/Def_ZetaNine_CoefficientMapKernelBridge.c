// Lean compiler output
// Module: Definitions.Def_ZetaNine_CoefficientMapKernelBridge
// Imports: public import Init public meta import Init public import Definitions.Def_ZetaNine_CoefficientMapTelescoper public import Definitions.Def_ZetaNine_CoefficientMapShiftDegree public import Mathlib.Algebra.Polynomial.Eval.Defs public import Mathlib.Algebra.BigOperators.Ring.Finset public import Mathlib.Data.Nat.Choose.Cast public import Mathlib.Data.Nat.Factorial.BigOperators public import Mathlib.Tactic public import Mathlib.RingTheory.PowerSeries.Inverse public import Mathlib.Algebra.Polynomial.Eval.Coeff public import Mathlib.Algebra.BigOperators.NatAntidiagonal public import Mathlib.Algebra.Polynomial.BigOperators public import Mathlib.Algebra.Polynomial.RingDivision public import Mathlib.Algebra.Polynomial.Degree.Lemmas public import Mathlib.RingTheory.Coprime.Lemmas public import Mathlib.RingTheory.PowerSeries.Trunc public import Mathlib.Algebra.BigOperators.Intervals public import Mathlib.NumberTheory.LSeries.RiemannZeta public import Mathlib.Analysis.PSeries public import Mathlib.Analysis.Normed.Group.InfiniteSum public import Mathlib.Analysis.Normed.Module.FiniteDimension public import Mathlib.Algebra.Polynomial.Eval.SMul public import Mathlib.Algebra.Polynomial.Taylor public import Mathlib.Algebra.Polynomial.Reverse public import Mathlib.Order.Interval.Set.Infinite
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
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* l_Rat_pow(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor___private_Definitions_Def__ZetaNine__CoefficientMapKernelBridge_0__ZetaNine_CoefficientMapAggregate_aggregate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor___private_Definitions_Def__ZetaNine__CoefficientMapKernelBridge_0__ZetaNine_CoefficientMapAggregate_aggregate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor___private_Definitions_Def__ZetaNine__CoefficientMapKernelBridge_0__ZetaNine_CoefficientMapTelescoper_rootNode_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor___private_Definitions_Def__ZetaNine__CoefficientMapKernelBridge_0__ZetaNine_CoefficientMapTelescoper_rootNode_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor___private_Definitions_Def__ZetaNine__CoefficientMapKernelBridge_0__ZetaNine_CoefficientMapTelescoper_rootNode_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0(lean_object* v_t_3_, lean_object* v_k_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v_k_4_);
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
v___x_17_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v_n_14_);
v___x_18_ = l_Rat_add(v_t_15_, v___x_17_);
v___x_19_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v_k_16_);
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
v___x_30_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v_n_28_);
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
v___x_39_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v___x_38_);
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
v___x_45_ = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalRealSqrt_spec__3(v_n_40_);
v___x_46_ = l_Rat_mul(v___x_44_, v___x_45_);
v___x_47_ = l_Rat_add(v_t_41_, v___x_46_);
v___x_48_ = lean_obj_once(&lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0, &lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0_once, _init_lp_zeta9KernelBridgeOfflineAuthor_ZetaNine_CoefficientMapKernelBridge_positiveProduct___lam__0___closed__0);
v___x_49_ = l_Rat_add(v___x_47_, v___x_48_);
v___x_50_ = l_Rat_mul(v___x_43_, v___x_49_);
lean_dec_ref(v___x_43_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor___private_Definitions_Def__ZetaNine__CoefficientMapKernelBridge_0__ZetaNine_CoefficientMapAggregate_aggregate_match__1_splitter___redArg(lean_object* v_x_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_, lean_object* v_h__3_54_, lean_object* v_h__4_55_, lean_object* v_h__5_56_){
_start:
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = lean_nat_dec_eq(v_x_51_, v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; uint8_t v___x_60_; 
lean_dec(v_h__1_52_);
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = lean_nat_dec_eq(v_x_51_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; uint8_t v___x_62_; 
lean_dec(v_h__2_53_);
v___x_61_ = lean_unsigned_to_nat(2u);
v___x_62_ = lean_nat_dec_eq(v_x_51_, v___x_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; uint8_t v___x_64_; 
lean_dec(v_h__3_54_);
v___x_63_ = lean_unsigned_to_nat(3u);
v___x_64_ = lean_nat_dec_eq(v_x_51_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; 
lean_dec(v_h__4_55_);
v___x_65_ = lean_apply_5(v_h__5_56_, v_x_51_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_65_;
}
else
{
lean_object* v___x_66_; lean_object* v___x_67_; 
lean_dec(v_h__5_56_);
lean_dec(v_x_51_);
v___x_66_ = lean_box(0);
v___x_67_ = lean_apply_1(v_h__4_55_, v___x_66_);
return v___x_67_;
}
}
else
{
lean_object* v___x_68_; lean_object* v___x_69_; 
lean_dec(v_h__5_56_);
lean_dec(v_h__4_55_);
lean_dec(v_x_51_);
v___x_68_ = lean_box(0);
v___x_69_ = lean_apply_1(v_h__3_54_, v___x_68_);
return v___x_69_;
}
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v_h__5_56_);
lean_dec(v_h__4_55_);
lean_dec(v_h__3_54_);
lean_dec(v_x_51_);
v___x_70_ = lean_box(0);
v___x_71_ = lean_apply_1(v_h__2_53_, v___x_70_);
return v___x_71_;
}
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_h__5_56_);
lean_dec(v_h__4_55_);
lean_dec(v_h__3_54_);
lean_dec(v_h__2_53_);
lean_dec(v_x_51_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_apply_1(v_h__1_52_, v___x_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor___private_Definitions_Def__ZetaNine__CoefficientMapKernelBridge_0__ZetaNine_CoefficientMapAggregate_aggregate_match__1_splitter(lean_object* v_motive_74_, lean_object* v_x_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_, lean_object* v_h__3_78_, lean_object* v_h__4_79_, lean_object* v_h__5_80_){
_start:
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = lean_nat_dec_eq(v_x_75_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; uint8_t v___x_84_; 
lean_dec(v_h__1_76_);
v___x_83_ = lean_unsigned_to_nat(1u);
v___x_84_ = lean_nat_dec_eq(v_x_75_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; uint8_t v___x_86_; 
lean_dec(v_h__2_77_);
v___x_85_ = lean_unsigned_to_nat(2u);
v___x_86_ = lean_nat_dec_eq(v_x_75_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; uint8_t v___x_88_; 
lean_dec(v_h__3_78_);
v___x_87_ = lean_unsigned_to_nat(3u);
v___x_88_ = lean_nat_dec_eq(v_x_75_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; 
lean_dec(v_h__4_79_);
v___x_89_ = lean_apply_5(v_h__5_80_, v_x_75_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_89_;
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec(v_h__5_80_);
lean_dec(v_x_75_);
v___x_90_ = lean_box(0);
v___x_91_ = lean_apply_1(v_h__4_79_, v___x_90_);
return v___x_91_;
}
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v_h__5_80_);
lean_dec(v_h__4_79_);
lean_dec(v_x_75_);
v___x_92_ = lean_box(0);
v___x_93_ = lean_apply_1(v_h__3_78_, v___x_92_);
return v___x_93_;
}
}
else
{
lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v_h__5_80_);
lean_dec(v_h__4_79_);
lean_dec(v_h__3_78_);
lean_dec(v_x_75_);
v___x_94_ = lean_box(0);
v___x_95_ = lean_apply_1(v_h__2_77_, v___x_94_);
return v___x_95_;
}
}
else
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec(v_h__5_80_);
lean_dec(v_h__4_79_);
lean_dec(v_h__3_78_);
lean_dec(v_h__2_77_);
lean_dec(v_x_75_);
v___x_96_ = lean_box(0);
v___x_97_ = lean_apply_1(v_h__1_76_, v___x_96_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor___private_Definitions_Def__ZetaNine__CoefficientMapKernelBridge_0__ZetaNine_CoefficientMapTelescoper_rootNode_match__1_splitter___redArg(lean_object* v_i_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_){
_start:
{
if (lean_obj_tag(v_i_98_) == 0)
{
lean_object* v_val_101_; lean_object* v___x_102_; 
lean_dec(v_h__2_100_);
v_val_101_ = lean_ctor_get(v_i_98_, 0);
lean_inc(v_val_101_);
lean_dec_ref_known(v_i_98_, 1);
v___x_102_ = lean_apply_1(v_h__1_99_, v_val_101_);
return v___x_102_;
}
else
{
lean_object* v_val_103_; lean_object* v___x_104_; 
lean_dec(v_h__1_99_);
v_val_103_ = lean_ctor_get(v_i_98_, 0);
lean_inc(v_val_103_);
lean_dec_ref_known(v_i_98_, 1);
v___x_104_ = lean_apply_1(v_h__2_100_, v_val_103_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor___private_Definitions_Def__ZetaNine__CoefficientMapKernelBridge_0__ZetaNine_CoefficientMapTelescoper_rootNode_match__1_splitter(lean_object* v_n_105_, lean_object* v_motive_106_, lean_object* v_i_107_, lean_object* v_h__1_108_, lean_object* v_h__2_109_){
_start:
{
if (lean_obj_tag(v_i_107_) == 0)
{
lean_object* v_val_110_; lean_object* v___x_111_; 
lean_dec(v_h__2_109_);
v_val_110_ = lean_ctor_get(v_i_107_, 0);
lean_inc(v_val_110_);
lean_dec_ref_known(v_i_107_, 1);
v___x_111_ = lean_apply_1(v_h__1_108_, v_val_110_);
return v___x_111_;
}
else
{
lean_object* v_val_112_; lean_object* v___x_113_; 
lean_dec(v_h__1_108_);
v_val_112_ = lean_ctor_get(v_i_107_, 0);
lean_inc(v_val_112_);
lean_dec_ref_known(v_i_107_, 1);
v___x_113_ = lean_apply_1(v_h__2_109_, v_val_112_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* lp_zeta9KernelBridgeOfflineAuthor___private_Definitions_Def__ZetaNine__CoefficientMapKernelBridge_0__ZetaNine_CoefficientMapTelescoper_rootNode_match__1_splitter___boxed(lean_object* v_n_114_, lean_object* v_motive_115_, lean_object* v_i_116_, lean_object* v_h__1_117_, lean_object* v_h__2_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = lp_zeta9KernelBridgeOfflineAuthor___private_Definitions_Def__ZetaNine__CoefficientMapKernelBridge_0__ZetaNine_CoefficientMapTelescoper_rootNode_match__1_splitter(v_n_114_, v_motive_115_, v_i_116_, v_h__1_117_, v_h__2_118_);
lean_dec(v_n_114_);
return v_res_119_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_zeta9KernelBridgeOfflineAuthor_Definitions_Def__ZetaNine__CoefficientMapTelescoper(uint8_t builtin);
lean_object* initialize_zeta9KernelBridgeOfflineAuthor_Definitions_Def__ZetaNine__CoefficientMapShiftDegree(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_Eval_Defs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_Ring_Finset(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Nat_Choose_Cast(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Nat_Factorial_BigOperators(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_PowerSeries_Inverse(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_Eval_Coeff(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_NatAntidiagonal(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_BigOperators(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_RingDivision(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_Degree_Lemmas(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_Coprime_Lemmas(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_PowerSeries_Trunc(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_Intervals(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_NumberTheory_LSeries_RiemannZeta(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_PSeries(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Group_InfiniteSum(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Module_FiniteDimension(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_Eval_SMul(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_Taylor(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_Reverse(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Order_Interval_Set_Infinite(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_zeta9KernelBridgeOfflineAuthor_Definitions_Def__ZetaNine__CoefficientMapKernelBridge(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_zeta9KernelBridgeOfflineAuthor_Definitions_Def__ZetaNine__CoefficientMapTelescoper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_zeta9KernelBridgeOfflineAuthor_Definitions_Def__ZetaNine__CoefficientMapShiftDegree(builtin);
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
res = initialize_mathlib_Mathlib_RingTheory_PowerSeries_Inverse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Polynomial_Eval_Coeff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_NatAntidiagonal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Polynomial_BigOperators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Polynomial_RingDivision(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Polynomial_Degree_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_Coprime_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_PowerSeries_Trunc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_Intervals(builtin);
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
res = initialize_mathlib_Mathlib_Algebra_Polynomial_Eval_SMul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Polynomial_Taylor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Polynomial_Reverse(builtin);
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
