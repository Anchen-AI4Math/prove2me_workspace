// Lean compiler output
// Module: Solutions.Sol_ZetaNine_CoefficientMapShiftDegree_actual_shift_difference_degree_lower_bound
// Imports: public import Init public meta import Init public import Definitions.Def_ZetaNine_CoefficientMapShiftDegree public import Mathlib.Algebra.Polynomial.Taylor public import Mathlib.Algebra.Polynomial.Reverse public import Mathlib.Tactic
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_zeta9ShiftDegreeIndependentReview_Definitions_Def__ZetaNine__CoefficientMapShiftDegree(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_Taylor(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_Reverse(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_zeta9ShiftDegreeIndependentReview_Solutions_Sol__ZetaNine__CoefficientMapShiftDegree__actual__shift__difference__degree__lower__bound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_zeta9ShiftDegreeIndependentReview_Definitions_Def__ZetaNine__CoefficientMapShiftDegree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Polynomial_Taylor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Polynomial_Reverse(builtin);
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
