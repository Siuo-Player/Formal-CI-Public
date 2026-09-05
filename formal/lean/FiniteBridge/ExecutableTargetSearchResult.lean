import Mathlib
import FiniteBridge.ExecutableSearchBridge
import FiniteBridge.TargetSearchResult

namespace FiniteBridge
namespace SearchState

section

variable {n : Nat} {r : Transition n} [DecidableRel r]
  {start target : State n}

/-- Executable target classifier based on the computable `n - 1`-round runner.
The result is `found target` exactly when the target is visited; otherwise it
is `provedEmpty`. -/
def executableTargetSearchResult (start target : State n) : SearchResult (State n) :=
  if target ∈ (executableRun (r := r) (n - 1) (initial start)).visited then
    SearchResult.found target
  else
    SearchResult.provedEmpty

/-- The executable classifier is definitionally characterized by target
membership in the executable runner's visited set. -/
theorem executableTargetSearchResult_found_iff :
    executableTargetSearchResult (r := r) start target = SearchResult.found target ↔
      target ∈ (executableRun (r := r) (n - 1) (initial start)).visited := by
  simp [executableTargetSearchResult]

/-- The executable classifier agrees exactly with the previously defined
semantic target classifier. -/
theorem executableTargetSearchResult_eq_semantic :
    executableTargetSearchResult (r := r) start target =
      targetSearchResult (r := r) start target := by
  simp [executableTargetSearchResult, targetSearchResult,
    executableRun_eq_semantic (r := r) (n - 1) (initial start)]

/-- The executable target classifier is sound for the target reachability
predicate. -/
theorem executableTargetSearchResult_sound :
    SearchResultSound (targetWitnessValid (r := r) start target)
      (executableTargetSearchResult (r := r) start target) := by
  rw [executableTargetSearchResult_eq_semantic (r := r) (start := start) (target := target)]
  exact targetSearchResult_sound (r := r) (start := start) (target := target)

end
end SearchState
end FiniteBridge
