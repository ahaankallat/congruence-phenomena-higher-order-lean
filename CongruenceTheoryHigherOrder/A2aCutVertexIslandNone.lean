import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexFixesC0
import CongruenceTheoryHigherOrder.A2aCutVertexIslandMap
import CongruenceTheoryHigherOrder.A2aCutVertexIslandPerm
import CongruenceTheoryHigherOrder.A2aCutVertexIslandPermMul
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInstance
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**The virtual-root block maps to itself under `islandPermOfPtStab`.** A sharper, standalone form
of the `none` case of `islandPermOfPtStab_perm`, giving the exact target block (not just
existence) — needed for the `hblock_u` hypothesis `card_le_root_bound` requires for the island.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- `islandPermOfPtStab φ` maps the virtual-root block (`none`) to itself: since `φ` maps `V u`
onto `V u` setwise, and `none`'s block is exactly the island points lying in `V u`. -/
theorem islandPermOfPtStab_none {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} {c0 : BlockComponent V g u}
    (hreach : Reaches g u p₀ c0) (φ : Equiv.Perm Ω) (hφ : φ ∈ PtStab A p₀) :
    (IslandV g u c0 none).image (islandPermOfPtStab hpart hne hcent hperm hblock_u hreach φ hφ) =
      IslandV g u c0 none := by
  have hφA : φ ∈ A := (mem_PtStab.mp hφ).1
  have hφinv : φ⁻¹ ∈ PtStab A p₀ := (PtStab A p₀).inv_mem hφ
  have hφinvA : φ⁻¹ ∈ A := (mem_PtStab.mp hφinv).1
  apply Finset.ext
  rintro y
  simp only [Finset.mem_image]
  rw [mem_islandV_none]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_islandV_none] at hx
    rw [islandPermOfPtStab_coe]
    rw [← hblock_u φ hφA]
    exact Finset.mem_image_of_mem φ hx
  · intro hy
    have hy' : φ⁻¹ y.1 ∈ V u := by
      have heq := hblock_u φ⁻¹ hφinvA
      rw [← heq]
      exact Finset.mem_image_of_mem (⇑φ⁻¹) hy
    have hx0' : InComponentPlus g u c0 (φ⁻¹ y.1) :=
      inComponentPlus_apply_of_fixes hpart hne hcent hperm hφinvA (hblock_u φ⁻¹ hφinvA)
        (mem_PtStab.mp hφinv).2 hreach y.2
    refine ⟨⟨φ⁻¹ y.1, hx0'⟩, (mem_islandV_none g u c0 _).mpr hy', ?_⟩
    apply Subtype.ext
    rw [islandPermOfPtStab_coe]
    simp
