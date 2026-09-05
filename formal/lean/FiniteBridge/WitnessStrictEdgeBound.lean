import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- A bounded witness uses strictly fewer edges than there are states. -/
theorem boundedWitness_edge_count_lt_state_count
    {n : Nat} {r : Transition n} {start target : State n} {xs : List (State n)}
    (hw : BoundedWitness r start target xs) :
    xs.length - 1 < n := by
  rcases hw with ⟨hne, _, _, hsimple, _, hbound⟩
  by_cases hn : n = 0
  · subst n
    exact False.elim (Fin.elim0 start)
  · have hlt : n - 1 < n := Nat.sub_lt (Nat.zero_lt_of_ne_zero hn) (by decide)
    exact lt_of_le_of_lt hbound hlt

end FiniteBridge
