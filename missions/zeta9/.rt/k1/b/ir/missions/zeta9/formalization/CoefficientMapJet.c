// Lean compiler output
// Module: missions.zeta9.formalization.CoefficientMapJet
// Imports: public import Init public meta import Init public import missions.zeta9.formalization.CoefficientMap public import Mathlib.RingTheory.PowerSeries.Inverse public import Mathlib.Algebra.Polynomial.Eval.Coeff public import Mathlib.Algebra.BigOperators.NatAntidiagonal
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
lean_object* initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMap(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_PowerSeries_Inverse(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_Eval_Coeff(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_NatAntidiagonal(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMapJet(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_zeta9KernelBridgeOfflineAuthor_missions_zeta9_formalization_CoefficientMap(builtin);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
