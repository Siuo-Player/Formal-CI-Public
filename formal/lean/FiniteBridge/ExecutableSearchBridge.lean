import Mathlib
import FiniteBridge.FiniteSearchState

namespace FiniteBridge
namespace SearchState

section

variable {n : Nat} {r : Transition n} [DecidableRel r]

/-- Executable successor enumeration for a decidable finite-state relation. -/
def executableSuccessors (s : State n) : Finset (State n) :=
  Finset.univ.filter (fun t => r s t)

/-- The executable successor enumeration contains exactly the relational successors. -/
theorem mem_executableSuccessors_iff (s t : State n) :
    t ∈ executableSuccessors (r := r) s ↔ r s t := by
  simp [executableSuccessors]

/-- The semantic successor set uses the same extensional membership condition. -/
theorem mem_semanticSuccessors_iff (s t : State n) :
    t ∈ successors (r := r) s ↔ r s t := by
  simp [successors]

/-- The executable and semantic successor enumerations are extensionally equal. -/
theorem executableSuccessors_eq_semantic (s : State n) :
    executableSuccessors (r := r) s = successors (r := r) s := by
  ext t
  rw [mem_executableSuccessors_iff, mem_semanticSuccessors_iff]

/-- Executable frontier expansion, using the decidable successor enumeration. -/
def executableNextFrontier (state : SearchState n r) : Finset (State n) :=
  state.frontier.biUnion (fun s => executableSuccessors (r := r) s) \ state.visited

/-- Executable frontier expansion agrees exactly with the semantic expansion. -/
theorem executableNextFrontier_eq_semantic (state : SearchState n r) :
    executableNextFrontier (r := r) state = nextFrontier (r := r) state := by
  unfold executableNextFrontier nextFrontier
  rw [show
      (fun s => executableSuccessors (r := r) s) =
        (fun s => successors (r := r) s) by
      funext s
      exact executableSuccessors_eq_semantic (r := r) s]

/-- Executable one-step search, reusing the common `SearchState` representation. -/
def executableStep (state : SearchState n r) : SearchState n r := by
  let frontier' := executableNextFrontier (r := r) state
  let visited' := state.visited ∪ frontier'
  have hsubset : frontier' ⊆ visited' := by
    intro x hx
    exact Finset.mem_union_right _ hx
  exact ⟨frontier', visited', hsubset⟩

/-- The executable step has the same frontier as the semantic step. -/
theorem executableStep_frontier_eq_semantic (state : SearchState n r) :
    (executableStep (r := r) state).frontier =
      (step (r := r) state).frontier := by
  simp [executableStep, executableNextFrontier_eq_semantic]

/-- The executable step has the same visited set as the semantic step. -/
theorem executableStep_visited_eq_semantic (state : SearchState n r) :
    (executableStep (r := r) state).visited =
      (step (r := r) state).visited := by
  simp [executableStep, executableNextFrontier_eq_semantic]

/-- The executable step is extensionally identical to the semantic step. -/
theorem executableStep_eq_semantic (state : SearchState n r) :
    executableStep (r := r) state = step (r := r) state := by
  cases state with
  | mk frontier visited hsubset =>
      simp [executableStep, executableNextFrontier_eq_semantic, step]

/-- Executable bounded search runner based on the decidable successor enumeration. -/
def executableRun : Nat → SearchState n r → SearchState n r
  | 0, state => state
  | fuel + 1, state => executableStep (r := r) (executableRun fuel state)

/-- Every executable run is extensionally the corresponding semantic run. -/
theorem executableRun_eq_semantic :
    ∀ fuel (state : SearchState n r),
      executableRun (r := r) fuel state = run (r := r) fuel state := by
  intro fuel
  induction fuel with
  | zero =>
      intro state
      rfl
  | succ fuel ih =>
      intro state
      simp [executableRun, run, executableStep_eq_semantic, ih]

end
end SearchState
end FiniteBridge
