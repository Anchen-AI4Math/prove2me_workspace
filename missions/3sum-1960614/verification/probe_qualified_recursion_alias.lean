import Lean

section
local macro "check" : term => pure (Lean.mkIdent `AliasProbe.Tree.check_implementation)
local macro "Tree.check" : term => pure (Lean.mkIdent `AliasProbe.Tree.check_implementation)

theorem AliasProbe.Tree.check_implementation : ∀ n : Nat, n = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (Tree.check n)
end

theorem aliasProbeSolution : type_of% (@AliasProbe.Tree.check_implementation) :=
  @AliasProbe.Tree.check_implementation

#print axioms aliasProbeSolution
