import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aBlockPermutation
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexAction
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInstance
import CongruenceTheoryHigherOrder.A2aCutVertexDistinguished
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**Confinement for an arbitrary component fixed setwise (not just the manuscript's distinguished
`C_0`).** `A2aCutVertexDistinguished.lean`'s confinement lemmas derived "the component-permutation
fixes `c0`" from "`A` fixes a specific block `V_{j2}` setwise". For (A2a)'s other
rooted-isomorphism-type branches, the component-fixing fact instead comes directly from being in
the *stabilizer* of that component under the component-permutation action — this file generalizes
the confinement mechanism to take that fact directly.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- `A` maps `c`'s attachment set to itself setwise, given directly that `A`'s
component-permutation fixes `c` setwise (generalizing `ambientC0Attach_image_eq`, which derived
this from a specific block being fixed). -/
theorem ambientAttach_image_eq_of_component_fixed {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {c : BlockComponent V g u}
    (hfix : ∀ (φ : Equiv.Perm Ω) (hφ : φ ∈ A),
      componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ) c = c)
    {φ : Equiv.Perm Ω} (hφ : φ ∈ A) :
    (AmbientC0Attach g u c).image φ = AmbientC0Attach g u c := by
  have hfixc : componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ) c = c := hfix φ hφ
  apply Finset.ext
  intro y
  simp only [Finset.mem_image, mem_ambientC0Attach]
  constructor
  · rintro ⟨x, ⟨hxV, hxreach⟩, rfl⟩
    refine ⟨(hblock_u φ hφ) ▸ Finset.mem_image_of_mem φ hxV,
      reaches_apply_of_component_fixed hpart hne hcent hperm hφ (hblock_u φ hφ) hfixc hxreach⟩
  · rintro ⟨hyV, hyreach⟩
    have hφinv : φ⁻¹ ∈ A := A.inv_mem hφ
    have hu' : (V u).image (⇑φ⁻¹) = V u := by
      have h1 : ((V u).image φ).image (⇑φ⁻¹) = (V u).image (⇑φ⁻¹) := by rw [hblock_u φ hφ]
      rw [Finset.image_image, show (⇑φ⁻¹ ∘ ⇑φ : Ω → Ω) = ⇑(φ⁻¹ * φ : Equiv.Perm Ω) from rfl,
        inv_mul_cancel, Equiv.Perm.coe_one, Finset.image_id] at h1
      exact h1.symm
    have hfixc' : componentPermOfMem hpart hne hcent hperm hφinv hu' c = c := hfix φ⁻¹ hφinv
    have hxreach : Reaches g u (φ⁻¹ y) c :=
      reaches_apply_of_component_fixed hpart hne hcent hperm hφinv hu' hfixc' hyreach
    refine ⟨φ⁻¹ y, ⟨(hu' ▸ Finset.mem_image_of_mem (⇑φ⁻¹) hyV), hxreach⟩, by simp⟩

/-- The confinement bound for an arbitrary component fixed setwise by all of `A`: `A`'s orbit of
a point reaching `c` is confined to `c`'s own attachment set. -/
theorem card_le_ambientAttach_mul_card_ptStab_of_component_fixed {V : ι → Finset Ω}
    (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)}
    {g : Equiv.Perm Ω} (hcent : ∀ φ ∈ A, Commute φ g)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {c : BlockComponent V g u}
    (hfix : ∀ (φ : Equiv.Perm Ω) (hφ : φ ∈ A),
      componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ) c = c)
    {p₀ : Ω} (hp₀ : p₀ ∈ V u) (hp₀reach : Reaches g u p₀ c) :
    Nat.card A ≤ (AmbientC0Attach g u c).card * Nat.card (PtStab A p₀) := by
  have h := card_le_card_block_mul_card_stabilizer (G := A)
    (fun _ : Unit => AmbientC0Attach g u c) () p₀
    ((mem_ambientC0Attach g u c p₀).mpr ⟨hp₀, hp₀reach⟩)
    (fun φ => ambientAttach_image_eq_of_component_fixed hpart hne hcent hperm hblock_u hfix φ.2)
  have hEquiv : MulAction.stabilizer A p₀ ≃ PtStab A p₀ :=
  { toFun := fun a => ⟨a.1.1, mem_PtStab.mpr ⟨a.1.2, a.2⟩⟩
    invFun := fun a => ⟨⟨a.1, (mem_PtStab.mp a.2).1⟩, (mem_PtStab.mp a.2).2⟩
    left_inv := fun a => rfl
    right_inv := fun a => rfl }
  rwa [Nat.card_congr hEquiv] at h
