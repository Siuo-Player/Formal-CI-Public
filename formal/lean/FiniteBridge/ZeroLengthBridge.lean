import Mathlib
import FiniteBridge.Foundations
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
  exact boundedWitness_of_simplePath
    (r := r)
    (start := start)
    (target := start)
    (xs := [start])
    (by simp)
    (by simp)
    (by simp)
    (by simp [SimplePath])
    (by simp [TransitionValid])

/-- Under the current witness definition, a zero-edge bridge is therefore a
legitimate witness from a state to itself. -/
theorem zero_length_bridge_witness
    {n : Nat} {r : Transition n} (start : State n) :
    ∃ xs : List (State n),
      BoundedWitness r start start xs ∧ xs.length = 1 := by
  exact ⟨[start], singleton_boundedWitness start, by simp⟩

end FiniteBridge
