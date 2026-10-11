import missions.zeta9.formalization.CoefficientMapTelescoper

set_option autoImplicit false
namespace KernelIndependentRootNodeValueComparison

def rootNode (n : ℕ) (i : Fin (n + 1) ⊕ Fin (n + 1)) : ℚ :=
  match i with
  | .inl k => (k.val : ℚ) + 1
  | .inr k => -(n : ℚ) - (k.val : ℚ)

end KernelIndependentRootNodeValueComparison

theorem independent_rootNode_whole_value_eq : KernelIndependentRootNodeValueComparison.rootNode = ZetaNine.CoefficientMapTelescoper.rootNode := rfl
