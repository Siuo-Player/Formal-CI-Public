import Mathlib
import FiniteBridge.Foundations
import FiniteBridge.FiniteSearchState

namespace FiniteBridge
namespace SearchState

section

variable {n : Nat} {r : Transition n} {start target current : State n}

/-- Every state marked as visited by the finite search is genuinely reachable
from the search start. -/
theorem run_visited_implies_reachable
    : ∀ fuel, ∀ {target : State n},
      target ∈ (run (r := r) fuel (initial start)).visited →
      Relation.ReflTransGen r start target := by
  intro fuel
  induction fuel with
  | zero =>
      intro target htarget
      have htarget' : target = start := by
        simpa [initial] using htarget
      subst target
      exact Relation.ReflTransGen.refl
  | succ fuel ih =>
      intro target htarget
      change target ∈ (step (r := r) (run (r := r) fuel (initial start))).visited at htarget
      change target ∈
        (run (r := r) fuel (initial start)).visited ∪
          nextFrontier (r := r) (run (r := r) fuel (initial start)) at htarget
      rcases Finset.mem_union.mp htarget with h_old | h_new
      · exact ih h_old
      · have hnew := Finset.mem_sdiff.mp h_new
        have hbi : target ∈
            (run (r := r) fuel (initial start)).frontier.biUnion
              (fun s => successors (r := r) s) := hnew.1
        rcases Finset.mem_biUnion.mp hbi with ⟨s, hsfront, hsucc⟩
        have hsvisited : s ∈
            (run (r := r) fuel (initial start)).visited :=
          (run (r := r) fuel (initial start)).frontier_subset_visited hsfront
        have hsreach := ih hsvisited
        have hrel : r s target := by
          simpa [successors] using hsucc
        exact Relation.ReflTransGen.tail hsreach hrel

/-- The visited set of a finite search run is contained in semantic
reflexive-transitive reachability. -/
theorem run_visited_subset_reachable
    (fuel : Nat) :
    (run (r := r) fuel (initial start)).visited ⊆
      {target | Relation.ReflTransGen r start target} := by
  intro target htarget
  exact run_visited_implies_reachable (r := r) (start := start) fuel htarget

end
end SearchState
end FiniteBridge
