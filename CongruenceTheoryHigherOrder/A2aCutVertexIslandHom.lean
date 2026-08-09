import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexFixesC0
import CongruenceTheoryHigherOrder.A2aCutVertexIslandMap
import CongruenceTheoryHigherOrder.A2aCutVertexIslandPermMul
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInstance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandG
import CongruenceTheoryHigherOrder.A2aCutVertexIslandHperm
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**The island-restriction `MonoidHom`.** Bundles `islandPermOfPtStab` (with its `map_one'`/
`map_mul'` laws already proved) into a genuine `MonoidHom (PtStab A p₀) →* Equiv.Perm(island)`,
setting up the Noether/Lagrange cardinality factorization
`Nat.card(PtStab A p₀) = Nat.card(range) * Nat.card(ker)` — the same technique
`card_le_prod_factorial_mul_card_fixBlocks` uses for a single block, now for a whole island —
with `range` to be bounded via `card_le_root_bound` (giving the per-component cut-vertex factor)
and `ker` (elements fixing the whole island pointwise) the subgroup to recurse into for the
remaining components.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- The island-restriction `MonoidHom` from `PtStab A p₀`. -/
noncomputable def islandHom {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} {c0 : BlockComponent V g u}
    (hreach : Reaches g u p₀ c0) :
    ↥(PtStab A p₀) →* Equiv.Perm {x : Ω // InComponentPlus g u c0 x} where
  toFun φ := islandPermOfPtStab hpart hne hcent hperm hblock_u hreach φ.1 φ.2
  map_one' := islandPermOfPtStab_one hpart hne hcent hperm hblock_u hreach
    (Subgroup.one_mem (PtStab A p₀))
  map_mul' a b := islandPermOfPtStab_mul hpart hne hcent hperm hblock_u hreach b.1 a.1 b.2 a.2
