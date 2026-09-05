import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- A bounded witness has at most one entry per available finite state. -/
theorem boundedWitness_length_le_state_count
    {n : Nat} {r : Transition n} {start target : State n} {xs : List (State n)}
    (hw : BoundedWitness r start target xs) :
    xs.length ≤ n := by
  rcases hw with ⟨hne, hhead, hlast, hsimple, hvalid, hbound⟩
  exact simplePath_length_le_state_count hsimple

end FiniteBridge
