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

end
end SearchState
end FiniteBridge
