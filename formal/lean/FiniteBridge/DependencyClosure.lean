import FiniteBridge.Dependency

namespace FiniteBridge

theorem affected_of_seed
    {α : Type} {Edge : α → α → Prop}
    {Seeds : Set α} {seed : α}
    (hseed : seed ∈ Seeds) :
    Affected Edge Seeds seed := by
  exact ⟨seed, hseed, Relation.ReflTransGen.refl⟩

theorem affected_of_affected_path
    {α : Type} {Edge : α → α → Prop}
    {Seeds : Set α} {mid node : α}
    (hmid : Affected Edge Seeds mid)
    (hpath : DependsOn Edge mid node) :
    Affected Edge Seeds node := by
  rcases hmid with ⟨seed, hseed, hseedmid⟩
  exact ⟨seed, hseed, hseedmid.trans hpath⟩

theorem affected_mono_seeds
    {α : Type} {Edge : α → α → Prop}
    {Seeds₁ Seeds₂ : Set α}
    (hseeds : Seeds₁ ⊆ Seeds₂) :
    ∀ {node}, Affected Edge Seeds₁ node → Affected Edge Seeds₂ node := by
  intro node haffected
  rcases haffected with ⟨seed, hseed, hpath⟩
  exact ⟨seed, hseeds hseed, hpath⟩

end FiniteBridge
