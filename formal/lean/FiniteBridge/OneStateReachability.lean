import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- A one-state finite space cannot contain distinct reachable endpoints. -/
theorem one_state_reachability_endpoint_equal
    {r : Transition 1} {start target : State 1}
    (_hreach : Relation.ReflTransGen r start target) :
    start = target := by
  exact Subsingleton.elim _ _

end FiniteBridge
