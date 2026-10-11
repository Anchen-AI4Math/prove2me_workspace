import Definitions.Def_ZetaNine_CoefficientMapKernelBridge

set_option autoImplicit false
open scoped BigOperators Topology
open Finset Polynomial Filter
open ZetaNine ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapAggregate

theorem ZetaNine.CoefficientMapKernelBridge.original_five_dimensional_map_bijective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    Function.Bijective (quarticAggregateLinearMap n):= by sorry
