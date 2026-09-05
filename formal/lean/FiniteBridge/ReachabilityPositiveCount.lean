import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- Any finite-state reachability judgment implies that the state space is nonempty. -/
theorem reflTransGen_implies_positive_state_count
    {n : Nat} {r : Transition n} {start target : State n}
    (_hreach : Relation.ReflTransGen r start target) :
    0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  exact Fin.elim0 start

end FiniteBridge
