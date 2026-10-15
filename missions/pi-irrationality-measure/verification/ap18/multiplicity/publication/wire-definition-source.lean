import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace OAI.PiExponent.Collision

open scoped BigOperators

def multiplicity {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (group : ι → κ) (a : κ) : ℕ :=
  (rows.filter fun i => group i = a).card

end OAI.PiExponent.Collision
