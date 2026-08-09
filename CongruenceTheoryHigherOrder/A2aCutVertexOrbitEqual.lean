import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aBlockPermutation
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexAction
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.A2aCutVertexComponentHom
import CongruenceTheoryHigherOrder.A2aCutVertexComponentInv
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInstance
import CongruenceTheoryHigherOrder.A2aCutVertexDistinguished
import CongruenceTheoryHigherOrder.A2aCutVertexBranchOrbitStab
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**Components in the same orbit (under a block/component-permuting subgroup) share the same
attachment count and block-size product.** Needed for the outer induction across (A2a)'s
cut-vertex case: when `card_le_branch_bound` peels a whole orbit at once (the manuscript's `m_τ`
identical branches), the resulting bound `|orbit|·a_{c1}·∏_{i∈c1}(R_i-1)!` must match the "clean"
per-component product form `∏_{c∈orbit}(a_c·∏_{i∈c}(R_i-1)!)` used by the outer induction's own
telescoping — which requires every component in the orbit to have the *same* `a_c` and the *same*
block-size product as `c1`, since `φ` (an ambient bijection of `Ω`) carries `c1`'s whole structure
onto `c2`'s.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- If `φ`'s component-permutation moves `c1` to `c2`, `φ⁻¹`'s moves `c2` back to `c1`. -/
theorem componentPermOfMem_inv_moves {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {φ : Equiv.Perm Ω} (hφ : φ ∈ A)
    {c1 c2 : BlockComponent V g u}
    (hmove : componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ) c1 = c2) :
    componentPermOfMem hpart hne hcent hperm (A.inv_mem hφ) (hblock_u φ⁻¹ (A.inv_mem hφ)) c2 =
      c1 := by
  have hinv := componentPermOfMem_inv hpart hne hcent hperm hblock_u hφ
  have heq2 : componentPermOfMem hpart hne hcent hperm (A.inv_mem hφ)
      (hblock_u φ⁻¹ (A.inv_mem hφ)) c2 =
      (componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ))⁻¹ c2 :=
    congrArg (fun e => e c2) hinv
  rw [heq2, ← hmove]
  simp

/-- If `φ`'s component-permutation moves `c1` to `c2`, `φ` moves points reaching `c1` to points
reaching `c2` (the general, "moving" version of `reaches_apply_of_component_fixed`). -/
theorem reaches_apply_of_component_moved {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    {φ : Equiv.Perm Ω} (hφ : φ ∈ A) (hu : (V u).image φ = V u) {c1 c2 : BlockComponent V g u}
    (hmove : componentPermOfMem hpart hne hcent hperm hφ hu c1 = c2) {x : Ω}
    (hxreach : Reaches g u x c1) : Reaches g u (φ x) c2 := by
  obtain ⟨x1, hx1, y1, hy1, k, hk⟩ := hxreach
  refine ⟨blockPermSub hpart hne hperm hφ hu x1, ?_, φ y1, ?_, k, ?_⟩
  · have hmk := componentPermOfMem_mk hpart hne hcent hperm hφ hu x1
    rw [hx1, hmove] at hmk
    exact hmk.symm
  · rw [blockPermSub_coe, ← blockOfElt_spec hpart hperm φ hφ x1.1]
    exact Finset.mem_image_of_mem φ hy1
  · have h1 : (φ * g ^ k) x = (g ^ k * φ) x := by rw [((hcent φ hφ).zpow_right k).eq]
    simp only [Equiv.Perm.mul_apply] at h1
    rw [hk] at h1
    exact h1.symm

/-- `φ` maps `c1`'s attachment set onto `c2`'s attachment set, given `φ`'s component-permutation
moves `c1` to `c2`. -/
theorem ambientAttach_image_eq_of_component_moved {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {φ : Equiv.Perm Ω} (hφ : φ ∈ A)
    {c1 c2 : BlockComponent V g u}
    (hmove : componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ) c1 = c2) :
    (AmbientC0Attach g u c1).image φ = AmbientC0Attach g u c2 := by
  apply Finset.ext
  intro y
  simp only [Finset.mem_image, mem_ambientC0Attach]
  constructor
  · rintro ⟨x, ⟨hxV, hxreach⟩, rfl⟩
    exact ⟨(hblock_u φ hφ) ▸ Finset.mem_image_of_mem φ hxV,
      reaches_apply_of_component_moved hpart hne hcent hperm hφ (hblock_u φ hφ) hmove hxreach⟩
  · rintro ⟨hyV, hyreach⟩
    have hφinv : φ⁻¹ ∈ A := A.inv_mem hφ
    have hu' : (V u).image (⇑φ⁻¹) = V u := hblock_u φ⁻¹ hφinv
    have hmove' := componentPermOfMem_inv_moves hpart hne hcent hperm hblock_u hφ hmove
    have hxreach : Reaches g u (φ⁻¹ y) c1 :=
      reaches_apply_of_component_moved hpart hne hcent hperm hφinv hu' hmove' hyreach
    refine ⟨φ⁻¹ y, ⟨(hu' ▸ Finset.mem_image_of_mem (⇑φ⁻¹) hyV), hxreach⟩, by simp⟩

/-- **Components in the same orbit have equal attachment counts.** -/
theorem card_ambientAttach_eq_of_moved {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {φ : Equiv.Perm Ω} (hφ : φ ∈ A)
    {c1 c2 : BlockComponent V g u}
    (hmove : componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ) c1 = c2) :
    (AmbientC0Attach g u c1).card = (AmbientC0Attach g u c2).card := by
  rw [← ambientAttach_image_eq_of_component_moved hpart hne hcent hperm hblock_u hφ hmove]
  exact (Finset.card_image_of_injective _ φ.injective).symm

/-- The set of blocks belonging to a component, as a Finset of the fixed ambient type `{k≠u}`. -/
noncomputable def BlockSet {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι)
    (c : BlockComponent V g u) : Finset {i : ι // i ≠ u} :=
  Finset.univ.filter (fun i => Quot.mk (BlockReach V g u) i = c)

theorem mem_blockSet {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι) (c : BlockComponent V g u)
    (i : {i : ι // i ≠ u}) : i ∈ BlockSet g u c ↔ Quot.mk (BlockReach V g u) i = c := by
  simp [BlockSet]

theorem blockSet_image_eq_of_moved {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {φ : Equiv.Perm Ω} (hφ : φ ∈ A)
    {c1 c2 : BlockComponent V g u}
    (hmove : componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ) c1 = c2) :
    (BlockSet g u c1).image (blockPermSub hpart hne hperm hφ (hblock_u φ hφ)) = BlockSet g u c2 := by
  apply Finset.ext
  intro j
  simp only [Finset.mem_image, mem_blockSet]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hmk := componentPermOfMem_mk hpart hne hcent hperm hφ (hblock_u φ hφ) i
    rw [hi, hmove] at hmk
    exact hmk.symm
  · intro hj
    have hφinv : φ⁻¹ ∈ A := A.inv_mem hφ
    have hu' : (V u).image (⇑φ⁻¹) = V u := hblock_u φ⁻¹ hφinv
    have hmove' := componentPermOfMem_inv_moves hpart hne hcent hperm hblock_u hφ hmove
    set i := blockPermSub hpart hne hperm hφinv hu' j with hidef
    refine ⟨i, ?_, ?_⟩
    · have hmk := componentPermOfMem_mk hpart hne hcent hperm hφinv hu' j
      rw [hj, hmove'] at hmk
      exact hmk.symm
    · apply Subtype.ext
      rw [blockPermSub_coe, hidef, blockPermSub_coe, ← blockOfElt_comp hpart hne hperm φ⁻¹ φ hφinv
        hφ j.1]
      rw [blockOfElt_congr hpart hperm (mul_inv_cancel φ) (A.mul_mem hφ hφinv)
        (Subgroup.one_mem A)]
      exact blockOfElt_one hpart hne hperm (Subgroup.one_mem A) j.1

/-- **Components in the same orbit have equal block-size products.** -/
theorem prod_blockSet_eq_of_moved {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {φ : Equiv.Perm Ω} (hφ : φ ∈ A)
    {c1 c2 : BlockComponent V g u}
    (hmove : componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ) c1 = c2) :
    ∏ i ∈ BlockSet g u c1, Nat.factorial ((V i.1).card - 1) =
      ∏ i ∈ BlockSet g u c2, Nat.factorial ((V i.1).card - 1) := by
  rw [← blockSet_image_eq_of_moved hpart hne hcent hperm hblock_u hφ hmove]
  rw [Finset.prod_image (fun a _ b _ hab => (blockPermSub hpart hne hperm hφ (hblock_u φ hφ)
    ).injective hab)]
  apply Finset.prod_congr rfl
  intro i _
  congr 2
  rw [blockPermSub_coe, ← blockOfElt_spec hpart hperm φ hφ i.1]
  exact (Finset.card_image_of_injective _ φ.injective).symm
