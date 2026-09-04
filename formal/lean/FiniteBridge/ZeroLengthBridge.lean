import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- Zero-length reflexive reachability is always available at a state. -/
theorem reflTransGen_self
    {α : Type} {r : α → α → Prop} (start : α) :
    Relation.ReflTransGen r start start :=
  Relation.ReflTransGen.refl

/-- A singleton state sequence is a valid simple, transition-valid witness from
its state to itself, independently of the transition relation. -/
theorem singleton_boundedWitness
    {n : Nat} {r : Transition n} (start : State n) :
    BoundedWitness r start start [start] := by
  have hpath : SimplePath ([start] : List (State n)) := by
    simp [SimplePath]
  have hvalid : TransitionValid r ([start] : List (State n)) := by
    simp [TransitionValid]
  have hbound : ([start] : List (State n)).length - 1 ≤ n - 1 := by
    exact simplePath_edge_count_le_state_count_sub_one hpath (by simp)
  exact ⟨by simp, by simp, by simp, hpath, hvalid, hbound⟩

/-- Under the current witness definition, a zero-edge bridge is therefore a
legitimate witness from a state to itself. -/
theorem zero_length_bridge_witness
    {n : Nat} {r : Transition n} (start : State n) :
    ∃ xs : List (State n),
      BoundedWitness r start start xs ∧ xs.length = 1 := by
  exact ⟨[start], singleton_boundedWitness start, by simp⟩

end FiniteBridge
