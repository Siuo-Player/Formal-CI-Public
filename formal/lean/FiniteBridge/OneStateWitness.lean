import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- Over a one-state space, every bounded witness is necessarily a singleton. -/
theorem one_state_boundedWitness_length_eq_one
    {r : Transition 1} {start target : State 1} {xs : List (State 1)}
    (hw : BoundedWitness r start target xs) :
    xs.length = 1 := by
  rcases hw with ⟨hne, hhead, hlast, hsimple, hvalid, hbound⟩
  have hpos : 0 < xs.length := List.length_pos_of_ne_nil hne
  have hle : xs.length ≤ 1 := by
    simpa using simplePath_length_le_state_count hsimple
  omega

end FiniteBridge
