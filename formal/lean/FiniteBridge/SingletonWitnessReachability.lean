import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- A singleton bounded witness certifies the reflexive endpoint relation. -/
theorem singleton_boundedWitness_implies_reflTransGen
    {n : Nat} {r : Transition n} (start : State n)
    (hw : BoundedWitness r start start [start]) :
    Relation.ReflTransGen r start start := by
  exact Relation.ReflTransGen.refl

end FiniteBridge
