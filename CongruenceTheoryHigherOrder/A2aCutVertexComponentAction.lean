import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aBlockPermutation
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexAction
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**`A`'s induced permutation action on `BlockComponent`s**, bundling `blockPermSub` (which acts on
individual blocks of `ι∖{u}`) into a genuine permutation of the *components themselves*
(`componentPermOfMem`), together with its composition law (`componentPermOfMem_mul`). The orbits
of this action are exactly (A2a)'s cut-vertex case's "rooted-isomorphism types `τ`" — two
components lie in the same orbit exactly when some `φ∈A` maps one onto the other.
-/

open Equiv

variable {Ω ι : Type*} [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- The induced permutation of `BlockComponent`s from `φ ∈ A` fixing block `u` setwise. -/
noncomputable def componentPermOfMem {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    {φ : Equiv.Perm Ω} (hφ : φ ∈ A) (hu : (V u).image φ = V u) :
    Equiv.Perm (BlockComponent V g u) :=
  BlockComponent.mapPerm (blockPermSub hpart hne hperm hφ hu)
    (blockAdjSub_iff_of_commute hpart hne hcent hperm hφ hu)

theorem componentPermOfMem_mk {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    {φ : Equiv.Perm Ω} (hφ : φ ∈ A) (hu : (V u).image φ = V u) (x : {x : ι // x ≠ u}) :
    componentPermOfMem hpart hne hcent hperm hφ hu (Quot.mk (BlockReach V g u) x) =
      Quot.mk (BlockReach V g u) (blockPermSub hpart hne hperm hφ hu x) := rfl

/-- `componentPermOfMem` respects multiplication. -/
theorem componentPermOfMem_mul {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    {φ ψ : Equiv.Perm Ω} (hφ : φ ∈ A) (hψ : ψ ∈ A) (hu : (V u).image φ = V u)
    (hu' : (V u).image ψ = V u) (hu'' : (V u).image (ψ * φ) = V u) :
    componentPermOfMem hpart hne hcent hperm (A.mul_mem hψ hφ) hu'' =
      componentPermOfMem hpart hne hcent hperm hψ hu' *
        componentPermOfMem hpart hne hcent hperm hφ hu := by
  apply Equiv.ext
  intro c
  refine Quot.inductionOn c (fun x => ?_)
  show componentPermOfMem hpart hne hcent hperm (A.mul_mem hψ hφ) hu''
    (Quot.mk (BlockReach V g u) x) = _
  rw [componentPermOfMem_mk]
  show Quot.mk (BlockReach V g u) (blockPermSub hpart hne hperm (A.mul_mem hψ hφ) hu'' x) = _
  have hcoe : (blockPermSub hpart hne hperm (A.mul_mem hψ hφ) hu'' x : ι) =
      (blockPermSub hpart hne hperm hψ hu' (blockPermSub hpart hne hperm hφ hu x) : ι) := by
    rw [blockPermSub_coe, blockPermSub_coe, blockPermSub_coe]
    exact blockOfElt_comp hpart hne hperm φ ψ hφ hψ x.1
  have := Subtype.ext hcoe
  rw [this]
  rfl
