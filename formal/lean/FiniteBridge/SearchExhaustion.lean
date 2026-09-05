import Mathlib
import FiniteBridge.Foundations
import FiniteBridge.FiniteSearchState

namespace FiniteBridge
namespace SearchState

section

variable {n : Nat} {r : Transition n} {start : State n}

/-- A nonempty frontier after a search step must have come from a nonempty
frontier before that step. -/
theorem old_frontier_nonempty_of_step_frontier_nonempty
    {state : SearchState n r}
    (hfront : (step (r := r) state).frontier.Nonempty) :
    state.frontier.Nonempty := by
  rcases hfront with ⟨x, hx⟩
  change x ∈ nextFrontier (r := r) state at hx
  unfold nextFrontier at hx
  have hbi : x ∈ state.frontier.biUnion (fun s => successors (r := r) s) :=
    (Finset.mem_sdiff.mp hx).1
  rcases Finset.mem_biUnion.mp hbi with ⟨s, hs, _⟩
  exact ⟨s, hs⟩

/-- Whenever a search step produces a nonempty new frontier, its visited set
strictly grows. -/
theorem step_visited_card_strict_of_step_frontier_nonempty
    {state : SearchState n r}
    (hfront : (step (r := r) state).frontier.Nonempty) :
    state.visited.card < (step (r := r) state).visited.card := by
  have hdisj : Disjoint state.visited (step (r := r) state).frontier :=
    (step_frontier_disjoint_old_visited (r := r) state).symm
  have hcard :
      (step (r := r) state).visited.card =
        state.visited.card + (step (r := r) state).frontier.card := by
    simpa [step] using Finset.card_union_of_disjoint hdisj
  have hpos : 0 < (step (r := r) state).frontier.card :=
    Finset.card_pos.mpr hfront
  omega

/-- If the frontier is nonempty after `fuel` rounds, at least `fuel + 1`
distinct states have been visited. -/
theorem run_visited_card_ge_succ_of_frontier_nonempty :
    ∀ fuel, (run (r := r) fuel (initial start)).frontier.Nonempty →
      fuel + 1 ≤ (run (r := r) fuel (initial start)).visited.card := by
  intro fuel
  induction fuel with
  | zero =>
      intro _
      simp [initial]
  | succ fuel ih =>
      intro hfront
      have hprevfront :
          (run (r := r) fuel (initial start)).frontier.Nonempty :=
        old_frontier_nonempty_of_step_frontier_nonempty
          (r := r) (run (r := r) fuel (initial start)) hfront
      have hlower := ih hprevfront
      have hstrict := step_visited_card_strict_of_step_frontier_nonempty
        (r := r) (run (r := r) fuel (initial start)) hfront
      omega

/-- After `n` rounds, the finite search frontier is empty. The `n - 1`
round bound is a discovery bound; one additional round is required to expose
frontier exhaustion for this runner semantics. -/
theorem run_n_frontier_empty :
    (run (r := r) n (initial start)).frontier = ∅ := by
  by_contra hne
  have hfront : (run (r := r) n (initial start)).frontier.Nonempty := by
    exact Finset.nonempty_iff_ne_empty.mpr hne
  have hlower := run_visited_card_ge_succ_of_frontier_nonempty
    (r := r) (start := start) n hfront
  have hupper :
      (run (r := r) n (initial start)).visited.card ≤ n := by
    have hsubset :
        (run (r := r) n (initial start)).visited ⊆
          (Finset.univ : Finset (State n)) := Finset.subset_univ _
    simpa using Finset.card_le_card hsubset
  omega

end
end SearchState
end FiniteBridge
