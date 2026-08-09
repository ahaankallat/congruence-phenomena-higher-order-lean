import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandMap
import CongruenceTheoryHigherOrder.A2aCutVertexIslandPerm
import CongruenceTheoryHigherOrder.A2aCutVertexIslandPermMul
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInstance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandG
import CongruenceTheoryHigherOrder.A2aCutVertexIslandHom
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**The kernel of `islandHom`, mapped back into the ambient `Equiv.Perm Ω`.** `MonoidHom.ker
(islandHom ...)` is a subgroup of `↥(PtStab A p₀)`; for it to serve as the acting subgroup for the
*next* component's peel (needing `hcent`/`hperm`/`hblock_u` stated over `Equiv.Perm Ω`, and its own
`componentHom`), it needs to be re-embedded as a genuine `Subgroup (Equiv.Perm Ω)` via the
inclusion `(PtStab A p₀).subtype`. This file builds that image, its cardinality-preservation, its
containment in `A` (so it inherits `hcent`/`hperm`/`hblock_u`), and the key fact that it fixes all
of `c0`'s island pointwise.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- The kernel of `islandHom`, re-embedded as a subgroup of the ambient `Equiv.Perm Ω`. -/
noncomputable def KerAmbient {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} {c0 : BlockComponent V g u}
    (hreach : Reaches g u p₀ c0) : Subgroup (Equiv.Perm Ω) :=
  (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u hreach)).map (PtStab A p₀).subtype

theorem card_kerAmbient {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} {c0 : BlockComponent V g u}
    (hreach : Reaches g u p₀ c0) :
    Nat.card (KerAmbient hpart hne hcent hperm hblock_u hreach) =
      Nat.card (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u hreach)) := by
  unfold KerAmbient
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective _ _ (PtStab A p₀).subtype_injective).symm.toEquiv

theorem kerAmbient_le_A {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} {c0 : BlockComponent V g u}
    (hreach : Reaches g u p₀ c0) :
    KerAmbient hpart hne hcent hperm hblock_u hreach ≤ A := by
  unfold KerAmbient
  rintro ψ ⟨φ, -, rfl⟩
  exact (mem_PtStab.mp φ.2).1

/-- Elements of `KerAmbient` fix all of `c0`'s island pointwise. -/
theorem kerAmbient_fixes_island {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} {c0 : BlockComponent V g u}
    (hreach : Reaches g u p₀ c0) (ψ : Equiv.Perm Ω)
    (hψ : ψ ∈ KerAmbient hpart hne hcent hperm hblock_u hreach) {x : Ω}
    (hx : InComponentPlus g u c0 x) : ψ x = x := by
  obtain ⟨φ, hφker, rfl⟩ := hψ
  have hcoe : (islandPermOfPtStab hpart hne hcent hperm hblock_u hreach φ.1 φ.2 ⟨x, hx⟩ : Ω) =
      φ.1 x := islandPermOfPtStab_coe hpart hne hcent hperm hblock_u hreach φ.1 φ.2 ⟨x, hx⟩
  have heq1 : islandPermOfPtStab hpart hne hcent hperm hblock_u hreach φ.1 φ.2 = 1 := hφker
  rw [heq1] at hcoe
  simp only [Equiv.Perm.coe_one, id_eq] at hcoe
  exact hcoe.symm
