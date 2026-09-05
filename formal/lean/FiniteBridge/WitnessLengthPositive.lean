import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- Every bounded witness is nonempty, hence has positive list length. -/
theorem boundedWitness_length_pos
    {n : Nat} {r : Transition n} {start target : State n} {xs : List (State n)}
    (hw : BoundedWitness r start target xs) :
    0 < xs.length := by
  rcases hw with ⟨hne, _, _, _, _, _⟩
  exact List.length_pos_of_ne_nil hne

end FiniteBridge
