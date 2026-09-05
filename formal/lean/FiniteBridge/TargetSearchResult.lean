import Mathlib
import FiniteBridge.ResultSemantics
import FiniteBridge.SearchResultCertificates
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
noncomputable def targetSearchResult (start target : State n) : SearchResult (State n) := by
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
  by_cases htarget : target ∈
      (run (r := r) (n - 1) (initial start)).visited
  · have hresult : targetSearchResult (r := r) start target = SearchResult.found target := by
      simp [targetSearchResult, htarget]
    rw [hresult]
    apply found_searchResultSound
    exact ⟨rfl, mem_run_n_sub_one_iff_reachable.mp htarget⟩
  · have hresult : targetSearchResult (r := r) start target = SearchResult.provedEmpty := by
      simp [targetSearchResult, htarget]
    rw [hresult]
    apply provedEmpty_searchResultSound
    · intro w hw
      rcases hw with ⟨hwt, hwreach⟩
      subst w
      apply mem_run_n_sub_one_iff_reachable.mpr
      exact hwreach
    · intro w hwmem hwvalid
      rcases hwvalid with ⟨hwt, hreach⟩
      subst w
      exact htarget (mem_run_n_sub_one_iff_reachable.mpr hreach)

end
end SearchState
end FiniteBridge
