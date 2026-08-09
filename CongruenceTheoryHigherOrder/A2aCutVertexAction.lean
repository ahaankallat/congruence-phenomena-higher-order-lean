import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aBlockPermutation
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**`A`'s action on `ι∖{u}` preserves block-adjacency**, the next piece toward (A2a)'s cut-vertex
case. Given `φ ∈ A` fixes block `u` setwise (`hu`), `blockPermOfMem`'s restriction to `ι∖{u}`
(`blockPermSub`) is well-defined, and — since `φ` commutes with `g` — sends block-adjacent pairs
to block-adjacent pairs in both directions (`blockAdjSub_iff_of_commute`). Combined with
`BlockComponent.mapPerm` (`A2aCutVertexComponents.lean`), this is exactly what's needed for `A`
to act on the *set of connected components themselves*, whose orbits will be (A2a)'s
rooted-isomorphism types `τ` in the next file.
-/

open Equiv

variable {Ω ι : Type*} [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- If `φ` fixes block `i` setwise, `blockOfElt` fixes `i`. -/
theorem blockOfElt_eq_of_image_eq {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)}
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {φ : Equiv.Perm Ω} (hφ : φ ∈ A) {i : ι}
    (hfix : (V i).image φ = V i) : blockOfElt hpart hperm φ hφ i = i := by
  have hspec := blockOfElt_spec hpart hperm φ hφ i
  rw [hfix] at hspec
  obtain ⟨p, hp⟩ := hne i
  have hp' : p ∈ V (blockOfElt hpart hperm φ hφ i) := by rw [← hspec]; exact hp
  obtain ⟨i0, hi0, huniq⟩ := hpart p
  exact (huniq (blockOfElt hpart hperm φ hφ i) hp').trans (huniq i hp).symm

/-- `blockPermOfMem φ hφ`, restricted to `{x // x≠u}`, given `φ` fixes block `u` setwise. -/
noncomputable def blockPermSub {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)}
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι} {φ : Equiv.Perm Ω} (hφ : φ ∈ A)
    (hu : (V u).image φ = V u) : Equiv.Perm {x : ι // x ≠ u} :=
  have hfu : blockPermOfMem hpart hne hperm φ hφ u = u :=
    blockOfElt_eq_of_image_eq hpart hne hperm hφ hu
  (blockPermOfMem hpart hne hperm φ hφ).subtypePerm (fun x => by
    rw [ne_eq, ne_eq, not_iff_not]
    exact Iff.intro (fun heq => (blockPermOfMem hpart hne hperm φ hφ).injective (heq.trans hfu.symm))
      (fun heq => by rw [heq]; exact hfu))

theorem blockPermSub_coe {V : ι → Finset Ω} (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    {A : Subgroup (Equiv.Perm Ω)} (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    {φ : Equiv.Perm Ω} (hφ : φ ∈ A) (hu : (V u).image φ = V u) (x : {x : ι // x ≠ u}) :
    (blockPermSub hpart hne hperm hφ hu x : ι) = blockOfElt hpart hperm φ hφ x.1 := rfl

/-- `φ`, commuting with `g`, maps block-adjacent pairs to block-adjacent pairs. -/
theorem blockAdjSub_apply_of_commute {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    {φ : Equiv.Perm Ω} (hφ : φ ∈ A) (hu : (V u).image φ = V u) {i j : {x : ι // x ≠ u}}
    (hadj : BlockAdjSub V g u i j) :
    BlockAdjSub V g u (blockPermSub hpart hne hperm hφ hu i)
      (blockPermSub hpart hne hperm hφ hu j) := by
  obtain ⟨x, hx, y, hy, k, hk⟩ := hadj
  refine ⟨φ x, ?_, φ y, ?_, k, ?_⟩
  · rw [blockPermSub_coe, ← blockOfElt_spec hpart hperm φ hφ i.1]
    exact Finset.mem_image_of_mem φ hx
  · rw [blockPermSub_coe, ← blockOfElt_spec hpart hperm φ hφ j.1]
    exact Finset.mem_image_of_mem φ hy
  · have h1 : (φ * g ^ k) x = (g ^ k * φ) x := by rw [((hcent φ hφ).zpow_right k).eq]
    simp only [Equiv.Perm.mul_apply] at h1
    rw [hk] at h1
    exact h1.symm

/-- `blockPermSub` preserves block-adjacency in both directions. -/
theorem blockAdjSub_iff_of_commute {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    {φ : Equiv.Perm Ω} (hφ : φ ∈ A) (hu : (V u).image φ = V u) (i j : {x : ι // x ≠ u}) :
    BlockAdjSub V g u i j ↔ BlockAdjSub V g u (blockPermSub hpart hne hperm hφ hu i)
      (blockPermSub hpart hne hperm hφ hu j) := by
  constructor
  · exact blockAdjSub_apply_of_commute hpart hne hcent hperm hφ hu
  · intro hadj
    have hφ' : φ⁻¹ ∈ A := A.inv_mem hφ
    have hu' : (V u).image (⇑φ⁻¹) = V u := by
      have h1 : ((V u).image φ).image (⇑φ⁻¹) = (V u).image (⇑φ⁻¹) := by rw [hu]
      rw [Finset.image_image, show (⇑φ⁻¹ ∘ ⇑φ : Ω → Ω) = ⇑(φ⁻¹ * φ : Equiv.Perm Ω) from rfl,
        inv_mul_cancel, Equiv.Perm.coe_one, Finset.image_id] at h1
      exact h1.symm
    have hback := blockAdjSub_apply_of_commute hpart hne hcent hperm hφ' hu'
      (i := blockPermSub hpart hne hperm hφ hu i) (j := blockPermSub hpart hne hperm hφ hu j) hadj
    have hii : blockPermSub hpart hne hperm hφ' hu' (blockPermSub hpart hne hperm hφ hu i) = i := by
      apply Subtype.ext
      rw [blockPermSub_coe, blockPermSub_coe]
      have h := blockOfElt_comp hpart hne hperm φ φ⁻¹ hφ hφ' i.1
      rw [← h, blockOfElt_congr hpart hperm (inv_mul_cancel φ) (A.mul_mem hφ' hφ)
        (Subgroup.one_mem A)]
      exact blockOfElt_one hpart hne hperm (Subgroup.one_mem A) i.1
    have hjj : blockPermSub hpart hne hperm hφ' hu' (blockPermSub hpart hne hperm hφ hu j) = j := by
      apply Subtype.ext
      rw [blockPermSub_coe, blockPermSub_coe]
      have h := blockOfElt_comp hpart hne hperm φ φ⁻¹ hφ hφ' j.1
      rw [← h, blockOfElt_congr hpart hperm (inv_mul_cancel φ) (A.mul_mem hφ' hφ)
        (Subgroup.one_mem A)]
      exact blockOfElt_one hpart hne hperm (Subgroup.one_mem A) j.1
    rwa [hii, hjj] at hback
