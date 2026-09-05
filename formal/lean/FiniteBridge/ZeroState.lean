import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- There are no finite states when the state count is zero. -/
theorem no_state_of_zero_count {x : State 0} : False := by
  exact Fin.elim0 x

/-- Consequently, no reflexive reachability judgment can be formed over `Fin 0`. -/
theorem no_reflTransGen_of_zero_count
    {r : Transition 0} {start : State 0} :
    Relation.ReflTransGen r start start → False := by
  intro _
  exact no_state_of_zero_count (x := start)

end FiniteBridge
