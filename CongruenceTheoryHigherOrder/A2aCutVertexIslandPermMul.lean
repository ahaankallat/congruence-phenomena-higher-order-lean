import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexFixesC0
import CongruenceTheoryHigherOrder.A2aCutVertexIslandMap
import CongruenceTheoryHigherOrder.A2aCutVertexIslandPerm
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**`islandPermOfPtStab`'s composition law**, the last piece needed to bundle it into a genuine
`MonoidHom (PtStab A p₀) →* Equiv.Perm(island)` and apply Noether's isomorphism theorem
(`Nat.card(PtStab A p₀) = Nat.card(range) * Nat.card(ker)`), the same technique
`card_le_prod_factorial_mul_card_fixBlocks` used for single blocks, now for a whole island.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

theorem islandPermOfPtStab_coe {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} {c0 : BlockComponent V g u}
    (hreach : Reaches g u p₀ c0) (φ : Equiv.Perm Ω) (hφ : φ ∈ PtStab A p₀)
    (x : {x : Ω // InComponentPlus g u c0 x}) :
    (islandPermOfPtStab hpart hne hcent hperm hblock_u hreach φ hφ x : Ω) = φ x.1 := rfl

theorem islandPermOfPtStab_one {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} {c0 : BlockComponent V g u}
    (hreach : Reaches g u p₀ c0) (hφ : (1 : Equiv.Perm Ω) ∈ PtStab A p₀) :
    islandPermOfPtStab hpart hne hcent hperm hblock_u hreach 1 hφ = 1 := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rw [islandPermOfPtStab_coe]
  rfl

theorem islandPermOfPtStab_mul {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} {c0 : BlockComponent V g u}
    (hreach : Reaches g u p₀ c0) (φ ψ : Equiv.Perm Ω) (hφ : φ ∈ PtStab A p₀)
    (hψ : ψ ∈ PtStab A p₀) :
    islandPermOfPtStab hpart hne hcent hperm hblock_u hreach (ψ * φ) ((PtStab A p₀).mul_mem hψ hφ) =
      islandPermOfPtStab hpart hne hcent hperm hblock_u hreach ψ hψ *
        islandPermOfPtStab hpart hne hcent hperm hblock_u hreach φ hφ := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rw [islandPermOfPtStab_coe]
  show (ψ * φ) x.1 = _
  rfl
