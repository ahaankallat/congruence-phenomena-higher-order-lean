import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aBlockPermutation
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexAction
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInstance
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**Confining the orbit of `p₀` to the distinguished component's attachment set.** (A2a)'s cut-vertex
case distinguishes one component `C_0` as "the component containing a second fixed root block
`V_{j2}`" — since `A` fixes `V_{j2}` setwise (the theorem's own global hypothesis), `A`'s induced
component-permutation fixes `C_0` setwise too, hence `A` cannot map a point reaching `C_0` to a
point reaching a different component: the orbit of any `p₀` reaching `C_0` is confined to `C_0`'s
own `a_0`-sized attachment set within `V u`, not all of `V u`. This is the mechanism that lets
(A2a)'s cut-vertex bound use `a_0` (not `R_u`) as the outer multiplicative factor, avoiding the
double-counting that a naive re-application of `card_le_root_bound` to the island would introduce.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- If `φ` fixes block `j2` setwise, its induced component-permutation fixes `j2`'s own
component setwise. -/
theorem componentPermOfMem_fixes_of_block_fixed {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    {φ : Equiv.Perm Ω} (hφ : φ ∈ A) (hu : (V u).image φ = V u) {j2 : ι} (hj2u : j2 ≠ u)
    (hj2fix : (V j2).image φ = V j2) :
    componentPermOfMem hpart hne hcent hperm hφ hu (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩) =
      Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩ := by
  rw [componentPermOfMem_mk]
  congr 1
  apply Subtype.ext
  rw [blockPermSub_coe]
  exact blockOfElt_eq_of_image_eq hpart hne hperm hφ hj2fix

/-- If `φ`'s component-permutation fixes `c0` setwise, `φ` maps points reaching `c0` to points
reaching `c0` (a generalization of `inComponentPlus_apply_of_fixes`'s `V u`-disjunct case, taking
the component-fixing fact directly rather than deriving it from a fixed point). -/
theorem reaches_apply_of_component_fixed {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    {φ : Equiv.Perm Ω} (hφ : φ ∈ A) (hu : (V u).image φ = V u) {c0 : BlockComponent V g u}
    (hfixc : componentPermOfMem hpart hne hcent hperm hφ hu c0 = c0) {x : Ω}
    (hxreach : Reaches g u x c0) : Reaches g u (φ x) c0 := by
  obtain ⟨x1, hx1, y1, hy1, k, hk⟩ := hxreach
  refine ⟨blockPermSub hpart hne hperm hφ hu x1, ?_, φ y1, ?_, k, ?_⟩
  · have hmk := componentPermOfMem_mk hpart hne hcent hperm hφ hu x1
    rw [hx1, hfixc] at hmk
    exact hmk.symm
  · rw [blockPermSub_coe, ← blockOfElt_spec hpart hperm φ hφ x1.1]
    exact Finset.mem_image_of_mem φ hy1
  · have h1 : (φ * g ^ k) x = (g ^ k * φ) x := by rw [((hcent φ hφ).zpow_right k).eq]
    simp only [Equiv.Perm.mul_apply] at h1
    rw [hk] at h1
    exact h1.symm

/-- The ambient (non-island) Finset of `V u`'s points reaching component `c0`. -/
noncomputable def AmbientC0Attach {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι)
    (c0 : BlockComponent V g u) : Finset Ω :=
  (V u).filter (fun x => Reaches g u x c0)

theorem mem_ambientC0Attach {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι)
    (c0 : BlockComponent V g u) (x : Ω) :
    x ∈ AmbientC0Attach g u c0 ↔ x ∈ V u ∧ Reaches g u x c0 := by
  simp [AmbientC0Attach]

/-- `A` maps `C0`'s attachment set to itself setwise, given `A` fixes both `V u` and the
distinguished block `V_{j2}` (whose component is `c0`) setwise. -/
theorem ambientC0Attach_image_eq {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {j2 : ι} (hj2u : j2 ≠ u)
    (hblock_j2 : ∀ φ ∈ A, (V j2).image φ = V j2) {φ : Equiv.Perm Ω} (hφ : φ ∈ A) :
    (AmbientC0Attach g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)).image φ =
      AmbientC0Attach g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩) := by
  set c0 := Quot.mk (BlockReach V g u) (⟨j2, hj2u⟩ : {i : ι // i ≠ u})
  have hfixc : componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ) c0 = c0 :=
    componentPermOfMem_fixes_of_block_fixed hpart hne hcent hperm hφ (hblock_u φ hφ) hj2u
      (hblock_j2 φ hφ)
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
    have hj2fix' : (V j2).image (⇑φ⁻¹) = V j2 := by
      have h1 : ((V j2).image φ).image (⇑φ⁻¹) = (V j2).image (⇑φ⁻¹) := by
        rw [hblock_j2 φ hφ]
      rw [Finset.image_image, show (⇑φ⁻¹ ∘ ⇑φ : Ω → Ω) = ⇑(φ⁻¹ * φ : Equiv.Perm Ω) from rfl,
        inv_mul_cancel, Equiv.Perm.coe_one, Finset.image_id] at h1
      exact h1.symm
    have hfixc' : componentPermOfMem hpart hne hcent hperm hφinv hu' c0 = c0 :=
      componentPermOfMem_fixes_of_block_fixed hpart hne hcent hperm hφinv hu' hj2u hj2fix'
    have hxreach : Reaches g u (φ⁻¹ y) c0 :=
      reaches_apply_of_component_fixed hpart hne hcent hperm hφinv hu' hfixc' hyreach
    refine ⟨φ⁻¹ y, ⟨(hu' ▸ Finset.mem_image_of_mem (⇑φ⁻¹) hyV), hxreach⟩, by simp⟩

/-- **The confinement bound**: `A`'s orbit of `p₀` (reaching the distinguished component `c0`) is
confined to `c0`'s own attachment set, giving `Nat.card A ≤ a_0 * Nat.card(PtStab A p₀)` — using
`a_0`, not `R_u`, as the outer factor. -/
theorem card_le_ambientC0Attach_mul_card_ptStab {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {j2 : ι} (hj2u : j2 ≠ u)
    (hblock_j2 : ∀ φ ∈ A, (V j2).image φ = V j2) {p₀ : Ω} (hp₀ : p₀ ∈ V u)
    (hp₀reach : Reaches g u p₀ (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)) :
    Nat.card A ≤
      (AmbientC0Attach g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)).card *
        Nat.card (PtStab A p₀) := by
  have h := card_le_card_block_mul_card_stabilizer (G := A)
    (fun _ : Unit => AmbientC0Attach g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)) ()
    p₀ ((mem_ambientC0Attach g u _ p₀).mpr ⟨hp₀, hp₀reach⟩)
    (fun φ => ambientC0Attach_image_eq hpart hne hcent hperm hblock_u hj2u hblock_j2 φ.2)
  have hEquiv : MulAction.stabilizer A p₀ ≃ PtStab A p₀ :=
  { toFun := fun a => ⟨a.1.1, mem_PtStab.mpr ⟨a.1.2, a.2⟩⟩
    invFun := fun a => ⟨⟨a.1, (mem_PtStab.mp a.2).1⟩, (mem_PtStab.mp a.2).2⟩
    left_inv := fun a => rfl
    right_inv := fun a => rfl }
  rwa [Nat.card_congr hEquiv] at h
