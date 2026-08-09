import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound

/-!
**The induced block-permutation homomorphism**, a piece of infrastructure toward (A2a)'s "`u` is
a cut vertex" case. That case needs `A` to act not just on individual blocks (`hperm` already
gives this) but on the *set of connected components* of the graph obtained by deleting `u` from
the block-adjacency structure — which requires first packaging `hperm`'s bare existence
statement into a genuine `Equiv.Perm ι`-valued function of `φ ∈ A`, respecting multiplication.
-/

open Equiv

variable {Ω ι : Type*} [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- The block-index that `φ ∈ A` sends block `i` to. -/
noncomputable def blockOfElt {V : ι → Finset Ω} (hpart : IsPartition V)
    {A : Subgroup (Equiv.Perm Ω)} (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j)
    (φ : Equiv.Perm Ω) (hφ : φ ∈ A) (i : ι) : ι :=
  (hperm φ hφ i).choose

theorem blockOfElt_spec {V : ι → Finset Ω} (hpart : IsPartition V) {A : Subgroup (Equiv.Perm Ω)}
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (φ : Equiv.Perm Ω) (hφ : φ ∈ A) (i : ι) :
    (V i).image φ = V (blockOfElt hpart hperm φ hφ i) :=
  (hperm φ hφ i).choose_spec

/-- `blockOfElt` only depends on the *value* of the group element, not the membership proof. -/
theorem blockOfElt_congr {V : ι → Finset Ω} (hpart : IsPartition V) {A : Subgroup (Equiv.Perm Ω)}
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {φ₁ φ₂ : Equiv.Perm Ω} (heq : φ₁ = φ₂)
    (hφ₁ : φ₁ ∈ A) (hφ₂ : φ₂ ∈ A) (i : ι) :
    blockOfElt hpart hperm φ₁ hφ₁ i = blockOfElt hpart hperm φ₂ hφ₂ i := by
  subst heq
  rfl

theorem blockOfElt_one {V : ι → Finset Ω} (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    {A : Subgroup (Equiv.Perm Ω)} (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j)
    (hφ : (1 : Equiv.Perm Ω) ∈ A) (i : ι) :
    blockOfElt hpart hperm 1 hφ i = i := by
  have hspec := blockOfElt_spec hpart hperm 1 hφ i
  simp only [Equiv.Perm.coe_one, Finset.image_id] at hspec
  obtain ⟨p, hp⟩ := hne i
  have hp' : p ∈ V (blockOfElt hpart hperm 1 hφ i) := by rw [← hspec]; exact hp
  obtain ⟨i0, hi0, huniq⟩ := hpart p
  exact (huniq (blockOfElt hpart hperm 1 hφ i) hp').trans (huniq i hp).symm

theorem blockOfElt_comp {V : ι → Finset Ω} (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    {A : Subgroup (Equiv.Perm Ω)} (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j)
    (φ ψ : Equiv.Perm Ω) (hφ : φ ∈ A) (hψ : ψ ∈ A) (i : ι) :
    blockOfElt hpart hperm (ψ * φ) (A.mul_mem hψ hφ) i =
      blockOfElt hpart hperm ψ hψ (blockOfElt hpart hperm φ hφ i) := by
  have h1 := blockOfElt_spec hpart hperm φ hφ i
  have h2 := blockOfElt_spec hpart hperm ψ hψ (blockOfElt hpart hperm φ hφ i)
  have h3 := blockOfElt_spec hpart hperm (ψ * φ) (A.mul_mem hψ hφ) i
  rw [← h1] at h2
  rw [Finset.image_image] at h2
  rw [show (ψ ∘ φ : Ω → Ω) = (ψ * φ : Equiv.Perm Ω) from rfl] at h2
  obtain ⟨p, hp⟩ := hne i
  have hp2 : (ψ * φ) p ∈ (V i).image (ψ * φ) := Finset.mem_image_of_mem _ hp
  rw [h2] at hp2
  have hp3 : (ψ * φ) p ∈ V (blockOfElt hpart hperm (ψ * φ) (A.mul_mem hψ hφ) i) := by
    rw [← h3]; exact Finset.mem_image_of_mem _ hp
  obtain ⟨i0, hi0, huniq⟩ := hpart ((ψ * φ) p)
  exact (huniq _ hp3).trans (huniq _ hp2).symm

/-- The induced block-permutation of `φ ∈ A`, packaged as an actual `Equiv.Perm ι`. -/
noncomputable def blockPermOfMem {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)}
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (φ : Equiv.Perm Ω) (hφ : φ ∈ A) :
    Equiv.Perm ι where
  toFun := blockOfElt hpart hperm φ hφ
  invFun := blockOfElt hpart hperm φ⁻¹ (A.inv_mem hφ)
  left_inv i := by
    have h := blockOfElt_comp hpart hne hperm φ φ⁻¹ hφ (A.inv_mem hφ) i
    rw [← h, blockOfElt_congr hpart hperm (inv_mul_cancel φ) (A.mul_mem (A.inv_mem hφ) hφ)
      (Subgroup.one_mem A)]
    exact blockOfElt_one hpart hne hperm (Subgroup.one_mem A) i
  right_inv i := by
    have h := blockOfElt_comp hpart hne hperm φ⁻¹ φ (A.inv_mem hφ) hφ i
    rw [← h, blockOfElt_congr hpart hperm (mul_inv_cancel φ) (A.mul_mem hφ (A.inv_mem hφ))
      (Subgroup.one_mem A)]
    exact blockOfElt_one hpart hne hperm (Subgroup.one_mem A) i

theorem blockPermOfMem_apply {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)}
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (φ : Equiv.Perm Ω) (hφ : φ ∈ A) (i : ι) :
    blockPermOfMem hpart hne hperm φ hφ i = blockOfElt hpart hperm φ hφ i := rfl

/-- `blockPermOfMem` respects multiplication: the induced block-permutation homomorphism. -/
theorem blockPermOfMem_mul {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)}
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (φ ψ : Equiv.Perm Ω) (hφ : φ ∈ A)
    (hψ : ψ ∈ A) :
    blockPermOfMem hpart hne hperm (ψ * φ) (A.mul_mem hψ hφ) =
      blockPermOfMem hpart hne hperm ψ hψ * blockPermOfMem hpart hne hperm φ hφ := by
  apply Equiv.ext
  intro i
  show blockOfElt hpart hperm (ψ * φ) (A.mul_mem hψ hφ) i = _
  rw [blockOfElt_comp hpart hne hperm φ ψ hφ hψ i]
  rfl
