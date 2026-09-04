import Mathlib
import FiniteBridge.ReachabilityWitness

namespace FiniteBridge

/-- A chain remains a chain when a repeated endpoint and everything between
its two occurrences are removed. The proof is directed: it uses only the
adjacent edge into the first occurrence and the adjacent edge out of the
second occurrence. -/
theorem isChain_cycle_splice
    {α : Type} {r : α → α → Prop}
    {prefix middle suffix : List α} {a : α}
    (hchain : List.IsChain r (prefix ++ a :: middle ++ a :: suffix)) :
    List.IsChain r (prefix ++ a :: suffix) := by
  induction prefix with
  | nil =>
      cases middle with
      | nil => simpa using hchain
      | cons b middle =>
          simpa only [List.nil_append, List.cons_append] at hchain ⊢
          exact hchain
  | cons p prefix ih =>
      simpa only [List.cons_append] at hchain ⊢
      apply List.IsChain.cons_of_ne_nil
      · simp
      · exact ih (by simpa only [List.cons_append] using hchain)
      · simpa only [List.isChain_append] using hchain

end FiniteBridge
