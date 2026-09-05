import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- Every bounded witness contains at most as many states as the finite state space. -/
theorem boundedWitness_length_le_state_count
    {n : Nat} {r : Transition n} {start target : State n} {xs : List (State n)}
    (hw : BoundedWitness r start target xs) :
    xs.length ≤ n := by
  rcases hw with ⟨hne, hhead, hlast, hsimple, hvalid, hbound⟩
  omega

end FiniteBridge
