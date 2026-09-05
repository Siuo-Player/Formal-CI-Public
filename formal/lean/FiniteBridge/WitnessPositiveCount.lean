import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- A bounded witness can only exist over a nonempty finite state space. -/
theorem boundedWitness_implies_positive_state_count
    {n : Nat} {r : Transition n} {start target : State n} {xs : List (State n)}
    (_hw : BoundedWitness r start target xs) :
    0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  exact Fin.elim0 start

end FiniteBridge
