import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexFixesC0
import CongruenceTheoryHigherOrder.A2aCutVertexIslandMap
import CongruenceTheoryHigherOrder.A2aCutVertexIslandPermMul
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInstance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandG
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**`islandPermOfPtStab φ` permutes the island's own blocks.** The last hypothesis
(`hperm`) `card_le_root_bound` needs to be applicable to `PtStab A p₀`'s image on the island: the
virtual-root block (`none`, `V u`'s attachment points reaching `c0`) maps to itself, using `φ⁻¹`
(also in `PtStab A p₀`) to build the reverse inclusion witness directly rather than reconstructing
`Reaches`-membership from scratch; each real block (`some i`) maps to `some (blockPermSub i)`,
reusing `componentPermOfMem_fixes_reached` to confirm the image block still lies in `c0`.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- `islandPermOfPtStab φ` permutes the island's own blocks. -/
theorem islandPermOfPtStab_perm {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} {c0 : BlockComponent V g u}
    (hreach : Reaches g u p₀ c0) (φ : Equiv.Perm Ω) (hφ : φ ∈ PtStab A p₀)
    (b : IslandBlockIdx g u c0) :
    ∃ b' : IslandBlockIdx g u c0,
      (IslandV g u c0 b).image (islandPermOfPtStab hpart hne hcent hperm hblock_u hreach φ hφ) =
        IslandV g u c0 b' := by
  have hφA : φ ∈ A := (mem_PtStab.mp hφ).1
  rcases b with _ | i
  · refine ⟨none, ?_⟩
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
  · refine ⟨some ⟨blockPermSub hpart hne hperm hφA (hblock_u φ hφA) i.1,
      by
        have hfixc : componentPermOfMem hpart hne hcent hperm hφA (hblock_u φ hφA) c0 = c0 :=
          componentPermOfMem_fixes_reached hpart hne hcent hperm hφA (hblock_u φ hφA)
            (mem_PtStab.mp hφ).2 hreach
        have hmk := componentPermOfMem_mk hpart hne hcent hperm hφA (hblock_u φ hφA) i.1
        rw [i.2, hfixc] at hmk
        exact hmk.symm⟩, ?_⟩
    apply Finset.ext
    rintro y
    simp only [Finset.mem_image]
    rw [mem_islandV_some]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_islandV_some] at hx
      rw [islandPermOfPtStab_coe, blockPermSub_coe]
      exact (blockOfElt_spec hpart hperm φ hφA i.1.1) ▸ Finset.mem_image_of_mem φ hx
    · intro hy
      have hy' : y.1 ∈ (V i.1.1).image φ := by
        rw [blockOfElt_spec hpart hperm φ hφA i.1.1]; exact hy
      obtain ⟨x0, hx0, hx0y⟩ := Finset.mem_image.mp hy'
      have hx0' : InComponentPlus g u c0 x0 := Or.inl ⟨i.1, i.2, hx0⟩
      refine ⟨⟨x0, hx0'⟩, (mem_islandV_some g u c0 i _).mpr hx0, ?_⟩
      apply Subtype.ext
      rw [islandPermOfPtStab_coe]
      exact hx0y
