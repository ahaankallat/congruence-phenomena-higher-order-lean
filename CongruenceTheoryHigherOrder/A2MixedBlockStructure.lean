import Mathlib
import CongruenceTheoryHigherOrder.A2KernelEmbedding

/-!
**`thm:atomic-connected-content`'s (A2): transferring the block structure to the mixed points.**
`\sigma` preserves mixedness (a `\sigma`-cycle is uniformly mixed or non-mixed, since
`\mathrm{SameCycle}` is an equivalence relation and `A2MixedPoints.lean`'s
`isMixedPt_of_sameCycle` propagates mixedness both ways along it), so `\sigma` restricts to a
genuine permutation `sigmaMixed` of the mixed points. The block partition `V` likewise restricts
to `MixedBlock`, and the range of `restrictToMixed` is block-permuting for `MixedBlock` and
centralizes `sigmaMixed` — exactly the raw material `(A2a)`'s theorems
(`card_le_root_bound_valuation`, `factorization_card_le_cutVertex_unconditional`) need, once a
root block and connectivity-among-mixed-points witness are supplied (the one genuinely
`\widetilde H`-specific input this generic framework does not derive on its own).
-/

namespace CongruenceTheory

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]
  {V : ι → Finset Ω} {A : Subgroup (Equiv.Perm Ω)} {σ : Equiv.Perm Ω}

/-- **`\sigma` preserves mixedness.** -/
theorem isMixed_sigma_apply_iff (hpart : IsPartition V) (x : Ω) :
    IsMixedPt V σ (σ x) ↔ IsMixedPt V σ x := by
  constructor
  · intro h
    exact isMixedPt_of_sameCycle hpart (⟨-1, by simp⟩ : σ.SameCycle (σ x) x) h
  · intro h
    exact isMixedPt_of_sameCycle hpart (⟨1, by simp⟩ : σ.SameCycle x (σ x)) h

/-- **`\sigma` restricted to the mixed points.** -/
noncomputable def sigmaMixed (hpart : IsPartition V) (σ : Equiv.Perm Ω) :
    Equiv.Perm {x // IsMixedPt V σ x} :=
  Equiv.Perm.subtypePerm σ (isMixed_sigma_apply_iff hpart)

@[simp]
theorem sigmaMixed_apply (hpart : IsPartition V) (y : {x // IsMixedPt V σ x}) :
    (sigmaMixed hpart σ y : Ω) = σ (y : Ω) := rfl

noncomputable instance instFintypeMixed : Fintype {x // IsMixedPt V σ x} := Fintype.ofFinite _

/-- **The mixed points of block `i`.** -/
noncomputable def MixedBlock (V : ι → Finset Ω) (σ : Equiv.Perm Ω) (i : ι) :
    Finset {x // IsMixedPt V σ x} :=
  Finset.univ.filter (fun y => y.1 ∈ V i)

open scoped Classical in
theorem mem_MixedBlock {i : ι} {y : {x // IsMixedPt V σ x}} :
    y ∈ MixedBlock V σ i ↔ y.1 ∈ V i := by simp [MixedBlock]

theorem isPartition_MixedBlock (hpart : IsPartition V) : IsPartition (MixedBlock V σ) := by
  intro y
  obtain ⟨i, hi, huniq⟩ := hpart y.1
  exact ⟨i, mem_MixedBlock.mpr hi, fun j hj => huniq j (mem_MixedBlock.mp hj)⟩

/-- **Block-image transfer**: if `\varphi` sends block `i` to block `j`, the corresponding range
element sends `\mathrm{MixedBlock}\,i` to `\mathrm{MixedBlock}\,j`. -/
theorem mixedBlock_image_of_range (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ)
    {φ : A} {i j : ι} (hij : (V i).image (φ : Equiv.Perm Ω) = V j) :
    (MixedBlock V σ i).image (restrictToMixed hpart hne hperm hcent φ) = MixedBlock V σ j := by
  ext y
  simp only [Finset.mem_image, mem_MixedBlock]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [restrictToMixed_apply, ← hij]
    exact Finset.mem_image_of_mem _ hz
  · intro hy
    rw [← hij] at hy
    obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp hy
    have hphiw : IsMixedPt V σ ((φ.1 : Equiv.Perm Ω) w) := by rw [hweq]; exact y.2
    have hwmixed : IsMixedPt V σ w :=
      (isMixedPt_apply_iff hpart hne hperm hcent φ.1 φ.2 w).mp hphiw
    exact ⟨⟨w, hwmixed⟩, hw, Subtype.ext (by rw [restrictToMixed_apply]; exact hweq)⟩

/-- **The range subgroup is block-permuting on `MixedBlock`.** -/
theorem mixedBlock_hperm (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ) :
    ∀ φ' ∈ MonoidHom.range (restrictToMixed hpart hne hperm hcent), ∀ i,
      ∃ j, (MixedBlock V σ i).image φ' = MixedBlock V σ j := by
  rintro φ' ⟨φ, rfl⟩ i
  obtain ⟨j, hj⟩ := hperm φ.1 φ.2 i
  exact ⟨j, mixedBlock_image_of_range hpart hne hperm hcent hj⟩

/-- **The range subgroup centralizes `sigmaMixed`.** -/
theorem mixedBlock_hcent (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ) :
    ∀ φ' ∈ MonoidHom.range (restrictToMixed hpart hne hperm hcent),
      Commute φ' (sigmaMixed hpart σ) := by
  rintro φ' ⟨φ, rfl⟩
  have hc : (φ.1 : Equiv.Perm Ω) * σ = σ * (φ.1 : Equiv.Perm Ω) := hcent φ.1 φ.2
  have h : ∀ y : {x // IsMixedPt V σ x},
      (φ.1 : Equiv.Perm Ω) (σ (y : Ω)) = σ ((φ.1 : Equiv.Perm Ω) (y : Ω)) := fun y => by
    have hh := congrArg (fun e : Equiv.Perm Ω => e (y : Ω)) hc
    simpa [Equiv.Perm.mul_apply] using hh
  apply Equiv.ext
  intro y
  apply Subtype.ext
  simp only [Equiv.Perm.mul_apply, restrictToMixed_apply, sigmaMixed_apply]
  exact h y

#print axioms isMixed_sigma_apply_iff
#print axioms sigmaMixed_apply
#print axioms mem_MixedBlock
#print axioms isPartition_MixedBlock
#print axioms mixedBlock_image_of_range
#print axioms mixedBlock_hperm
#print axioms mixedBlock_hcent

end CongruenceTheory
