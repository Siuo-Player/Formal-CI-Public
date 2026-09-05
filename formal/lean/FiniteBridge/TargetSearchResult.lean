import Mathlib
import FiniteBridge.ResultSemantics
import FiniteBridge.SearchReachability

namespace FiniteBridge
namespace SearchState

section

variable {n : Nat} {r : Transition n} {start target : State n}

def targetWitnessValid (start target w : State n) : Prop :=
  w = target ∧ Relation.ReflTransGen r start w

noncomputable def targetSearchResult : SearchResult (State n) := by
  classical
  by_cases htarget : target ∈ (run (r := r) (n - 1) (initial start)).visited
  · exact SearchResult.found target
  · exact SearchResult.provedEmpty

theorem targetSearchResult_sound :
    SearchResultSound (targetWitnessValid (r := r) start target)
      (targetSearchResult (r := r) start target) := by
  classical
  unfold targetSearchResult
  by_cases htarget : target ∈
      (run (r := r) (n - 1) (initial start)).visited
  · simp only [SearchResultSound, targetWitnessValid, htarget, ↓reduceIte]
    exact ⟨rfl, mem_run_n_sub_one_iff_reachable.mp htarget⟩
  · simp only [SearchResultSound, htarget, ↓reduceIte]
    intro hex
    rcases hex with ⟨w, hwt, hwreach⟩
    subst w
    exact htarget (mem_run_n_sub_one_iff_reachable.mpr hwreach)

end
end SearchState
end FiniteBridge
