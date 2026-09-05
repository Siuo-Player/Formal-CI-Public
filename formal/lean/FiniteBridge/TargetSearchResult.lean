import Mathlib
import FiniteBridge.ResultSemantics
import FiniteBridge.SearchReachability

namespace FiniteBridge
namespace SearchState

section

variable {n : Nat} {r : Transition n} {start target : State n}

/-- Validity predicate for a target-specific search result: the reported
state must be the requested target and the target must be reachable from the
start state. -/
def targetWitnessValid (start target : State n) (w : State n) : Prop :=
  w = target ∧ Relation.ReflTransGen r start w

/-- Semantic target classifier induced by the complete `n - 1`-round search.
This is intentionally noncomputable: `successors` is a semantic filter over a
propositional relation, not an executable search interface. -/
noncomputable def targetSearchResult : SearchResult (State n) := by
  classical
  by_cases htarget : target ∈ (run (r := r) (n - 1) (initial start)).visited
  · exact SearchResult.found target
  · exact SearchResult.provedEmpty

/-- The semantic target classifier is sound: a found result has a reachable
target, and a proved-empty result rules out a reachable target. -/
theorem targetSearchResult_sound :
    SearchResultSound (targetWitnessValid (r := r) start target)
      (targetSearchResult (r := r) start target) := by
  classical
  unfold targetSearchResult
  by_cases htarget : target ∈
      (run (r := r) (n - 1) (initial start)).visited
  · simp only [SearchResultSound, targetWitnessValid, htarget,
      ↓reduceIte]
    constructor
    · rfl
    · exact mem_run_n_sub_one_iff_reachable.mp htarget
  · simp only [SearchResultSound, htarget, ↓reduceIte]
    intro hex
    rcases hex with ⟨w, hwt, hwreach⟩
    subst w
    exact htarget (mem_run_n_sub_one_iff_reachable.mpr hwreach)

end
end SearchState
end FiniteBridge
