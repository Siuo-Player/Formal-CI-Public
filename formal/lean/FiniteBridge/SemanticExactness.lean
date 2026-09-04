import FiniteBridge.SemanticDependency

namespace FiniteBridge

/-- A deliberately restricted dependency family: every earlier natural-number
node is a direct semantic predecessor of every later node. -/
def ChainEdge : Nat → Nat → Prop :=
  fun pred node => pred < node

def ChainBefore : Nat → Prop :=
  fun _ => False

def ChainAfter (seed : Nat) : Nat → Prop :=
  fun node => seed ≤ node

def ChainSeeds (seed : Nat) : Set Nat :=
  {seed}

theorem chain_affected_to_semantically_changed
    (seed node : Nat)
    (h : Affected ChainEdge (ChainSeeds seed) node) :
    SemanticallyChanged ChainBefore (ChainAfter seed) node := by
  rcases h with ⟨source, hsource, hpath⟩
  have hsource_eq : source = seed := by
    simpa [ChainSeeds] using hsource
  subst source
  have hle : seed ≤ node := by
    induction hpath with
    | refl => exact Nat.le_refl seed
    | tail hpath hstep ih =>
        exact Nat.le_trans ih (Nat.le_of_lt hstep)
  exact by
    simpa [SemanticallyChanged, StableUnderEdit, ChainBefore, ChainAfter]
    using hle

theorem chain_semantically_changed_to_affected
    (seed node : Nat)
    (h : SemanticallyChanged ChainBefore (ChainAfter seed) node) :
    Affected ChainEdge (ChainSeeds seed) node := by
  have hle : seed ≤ node := by
    simpa [SemanticallyChanged, StableUnderEdit, ChainBefore, ChainAfter]
      using h
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · exact affected_of_seed (Seeds := ChainSeeds seed) (seed := seed)
      (by simp [ChainSeeds])
  · refine ⟨seed, ?_, ?_⟩
    · simp [ChainSeeds]
    · exact Relation.ReflTransGen.single hlt

/-- In this non-circular restricted family, affectedness and semantic change
coincide exactly. The edge relation is structural (`<`); semantic change is
computed independently as membership in the suffix starting at the edited
seed. -/
theorem chain_affected_iff_semantically_changed
    (seed node : Nat) :
    Affected ChainEdge (ChainSeeds seed) node ↔
      SemanticallyChanged ChainBefore (ChainAfter seed) node := by
  constructor
  · exact chain_affected_to_semantically_changed seed node
  · exact chain_semantically_changed_to_affected seed node

end FiniteBridge
