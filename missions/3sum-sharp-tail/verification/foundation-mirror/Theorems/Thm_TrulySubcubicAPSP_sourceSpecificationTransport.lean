import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Definitions.Def_TrulySubcubicAPSP_Problems

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem TrulySubcubicAPSP.sourceSpecificationTransport :
    (∀ r : Rat, EndStatement.ExactTriangle.SolvedInTime r →
      TrulySubcubicAPSP.ExactTriangle.SolvedInTime r) ∧
    (∀ r : Rat, EndStatement.MinPlusProduct.SolvedInTime r →
      TrulySubcubicAPSP.MinPlusProduct.SolvedInTime r) ∧
    (∀ r : Rat, EndStatement.APSP.SolvedInTime r →
      TrulySubcubicAPSP.APSP.SolvedInTime r) := by sorry
