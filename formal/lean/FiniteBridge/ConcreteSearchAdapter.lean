import Mathlib
import FiniteBridge.ExecutableSearchBridge

namespace FiniteBridge

/-- Contract required to connect a concrete finite search state space to the
abstract `Fin n` transition relation used by the completeness results.

The equivalence makes the abstraction total and one-to-one.  The successor
condition is the semantic boundary: it requires the concrete enumerator to
contain exactly the transitions represented by `r`.  No engine is claimed to
satisfy this contract merely by instantiating the structure. -/
structure ConcreteSearchAdapter
    (ConcreteState : Type*)
    (n : Nat)
    (r : Transition n)
    [DecidableRel r]
    [Fintype ConcreteState]
    [DecidableEq ConcreteState] where
  encode : ConcreteState ≃ State n
  successors : ConcreteState → Finset ConcreteState
  mem_successors_iff : ∀ s t,
    t ∈ successors s ↔ r (encode s) (encode t)

namespace ConcreteSearchAdapter

variable {ConcreteState : Type*} {n : Nat} {r : Transition n}
  [DecidableRel r] [Fintype ConcreteState] [DecidableEq ConcreteState]
  (adapter : ConcreteSearchAdapter ConcreteState n r)

/-- Push a concrete successor set through the state-space equivalence. -/
def encodedSuccessors (s : State n) : Finset (State n) :=
  (adapter.successors (adapter.encode.symm s)).image adapter.encode

/-- The encoded concrete successors are exactly the abstract successors. -/
theorem mem_encodedSuccessors_iff (s t : State n) :
    t ∈ adapter.encodedSuccessors s ↔ r s t := by
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨u, hu, hencode⟩
    rw [adapter.mem_successors_iff] at hu
    simpa [hencode] using hu
  · intro hrt
    have hmem : adapter.encode.symm t ∈
        adapter.successors (adapter.encode.symm s) := by
      rw [adapter.mem_successors_iff]
      simpa using hrt
    exact Finset.mem_image.mpr ⟨adapter.encode.symm t, hmem, by simp⟩

/-- Concrete successor enumeration agrees extensionally with the executable
abstract successor enumeration after encoding. -/
theorem encodedSuccessors_eq_executableSuccessors (s : State n) :
    adapter.encodedSuccessors s =
      SearchState.executableSuccessors (r := r) s := by
  ext t
  rw [mem_encodedSuccessors_iff]
  exact (SearchState.mem_executableSuccessors_iff (r := r) s t).symm

/-- If the concrete expansion is applied to an abstract state, its encoded
frontier is the same frontier that the formal runner computes. -/
def encodedNextFrontier
    (state : SearchState n r) : Finset (State n) :=
  state.frontier.biUnion adapter.encodedSuccessors \ state.visited

theorem encodedNextFrontier_eq_executable (state : SearchState n r) :
    adapter.encodedNextFrontier state =
      SearchState.executableNextFrontier (r := r) state := by
  unfold encodedNextFrontier SearchState.executableNextFrontier
  rw [show adapter.encodedSuccessors =
      SearchState.executableSuccessors (r := r) by
    funext s
    exact adapter.encodedSuccessors_eq_executableSuccessors s]

/-- The adapter's boundary is strong enough to reuse the existing executable
runner: no additional search-completeness theorem is needed once the concrete
implementation proves this contract. -/
theorem adapter_mem_successors_characterization (s : State n) :
    ∀ t, t ∈ adapter.encodedSuccessors s ↔ r s t := by
  intro t
  exact adapter.mem_encodedSuccessors_iff s t

end ConcreteSearchAdapter

end FiniteBridge
