import Solutions.Sol_ThreeSum1960614_model_platform_bound

/- The existing platform root uses the literal rational endpoint. The original
   source uses lowerTarget. This check preserves the frozen public contract
   and proves their definitional equality without importing the target stub. -/
example (e b S th terminal ratio R : ℝ)
    (hmodel : ThreeSum1960614.ModelFeasible 232 e b S th terminal ratio R) :
    (196061349120 / 100000000000 : ℝ) < R :=
  solution e b S th terminal ratio R hmodel
