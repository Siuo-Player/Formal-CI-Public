import Mathlib
import FiniteBridge.ReachabilityWitness

namespace FiniteBridge

/-- Removing the interior of a repeated-state segment preserves the local
chain relation. The repeated endpoint is retained once, so no transitivity of
`r` is required. -/
theorem isChain_cycle_splice
    {α : Type} {r : α → α → Prop}
    {prefix middle suffix : List α} {a : α}
    (hchain : List.IsChain r (prefix ++ a :: middle ++ a :: suffix)) :
    List.IsChain r (prefix ++ a :: suffix) := by
  induction prefix with
  | nil =>
      induction middle with
      | nil => simpa using hchain
      | cons b middle ih =>
          simpa [List.isChain_append] using hchain
  | cons p prefix ih =>
      simp only [List.cons_append] at hchain ⊢
      exact List.IsChain.cons_of_ne_nil
        (by simp)
        (ih (by
          simpa [List.cons_append, List.isChain_append] using hchain))
        (by
          simpa [List.isChain_append] using hchain)

end FiniteBridge
