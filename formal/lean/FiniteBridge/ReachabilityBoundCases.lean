import Mathlib
import FiniteBridge.Foundations
import FiniteBridge.BoundedReachability

namespace FiniteBridge

theorem reachable_edge_count_lt_state_count
    {n : Nat} {r : Transition n} {start target : State n}
    (hreach : Relation.ReflTransGen r start target) :
    ∃ xs : List (State n),
      BoundedWitness r start target xs ∧
      xs.length - 1 < n := by
  rcases boundedWitness_of_reflTransGen hreach with ⟨xs, hw⟩
  rcases hw with ⟨hne, hhead, hlast, hsimple, hvalid, hbound⟩
  by_cases hn : n = 0
  · subst n
    exact False.elim (Fin.elim0 start)
  · have hlt : n - 1 < n := Nat.sub_lt (Nat.zero_lt_of_ne_zero hn) (Nat.zero_lt_of_ne_zero hn)
    exact ⟨xs, ⟨hne, hhead, hlast, hsimple, hvalid, hbound⟩, lt_of_le_of_lt hbound hlt⟩

end FiniteBridge
