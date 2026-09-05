import Mathlib
import FiniteBridge.ReachabilityWitness

namespace FiniteBridge

/-- A chain remains a chain when a repeated endpoint and everything between
its two occurrences are removed. -/
theorem isChain_cycle_splice
    {α : Type} {r : α → α → Prop}
    {pre middle suffix : List α} {a : α}
    (hchain : List.IsChain r (pre ++ a :: middle ++ a :: suffix)) :
    List.IsChain r (pre ++ a :: suffix) := by
  have hleft : List.IsChain r (pre ++ [a]) := by
    rw [← List.nil_append (pre ++ [a])]
    apply List.IsChain.left_of_append
    simpa [List.append_assoc] using hchain
  have hright : List.IsChain r ([a] ++ suffix) := by
    rw [← List.nil_append ([a] ++ suffix)]
    apply List.IsChain.right_of_append
    simpa [List.append_assoc] using hchain
  have hoverlap := List.IsChain.append_overlap hleft hright (by simp : ([a] : List α) ≠ [])
  simpa [List.append_assoc] using hoverlap

end FiniteBridge
