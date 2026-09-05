import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- Every bounded witness carries a simple path as part of its certificate. -/
theorem boundedWitness_simplePath
    {n : Nat} {r : Transition n} {start target : State n} {xs : List (State n)}
    (hw : BoundedWitness r start target xs) :
    SimplePath xs := by
  rcases hw with ⟨_, _, _, hsimple, _, _⟩
  exact hsimple

end FiniteBridge
