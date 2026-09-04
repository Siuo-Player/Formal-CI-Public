import Mathlib
import FiniteBridge.BoundedResult

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
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp [SimplePath]
  · simp [TransitionValid]
  · decide

/-- Under the current witness definition, a zero-edge bridge is therefore a
legitimate witness exactly when both endpoints are the same state. -/
theorem zero_length_bridge_witness
    {n : Nat} {r : Transition n} (start : State n) :
    ∃ xs : List (State n),
      BoundedWitness r start start xs ∧ xs.length = 1 := by
  exact ⟨[start], singleton_boundedWitness start, by simp⟩

end FiniteBridge
