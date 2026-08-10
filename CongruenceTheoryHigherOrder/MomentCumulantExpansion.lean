import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.GeneralizedConnectivity
import CongruenceTheoryHigherOrder.GeneralizedConnectivityTransport
import CongruenceTheoryHigherOrder.GeneralizedConnectivityTop
import CongruenceTheoryHigherOrder.GeneralizedPartitionGluing
import CongruenceTheoryHigherOrder.GeneralizedAssembleTop
import CongruenceTheoryHigherOrder.GeneralizedPiOfAssemble
import CongruenceTheoryHigherOrder.GeneralizedGfunTopK
import CongruenceTheoryHigherOrder.GeneralizedGfunProd
import CongruenceTheoryHigherOrder.PartitionShape
import CongruenceTheoryHigherOrder.ShapeCpSplit
import CongruenceTheoryHigherOrder.MicroblockPartition

/-!
**(A7), the moment-cumulant expansion of the multiplicative defect, for a genuinely heterogeneous
tuple.** The manuscript's `\Delta_{p\mathbf u} := C(pT) - \prod_i C(pu_i)` (`T=\sum u_i`) expands
as `\sum_\lambda A_\lambda(\mathbf u)C_p^{m_1}\prod_{j\ge2}K_j(p)^{m_j}`, where `A_\lambda(u)`
counts set partitions of the `T` labelled `p`-microblocks of type `\lambda` not refining the
macroblock partition. Assembled entirely from the already-general `Generalized*`/
`PartitionShape`/`ShapeCpSplit` machinery (none of which assumes uniform block size) plus
`MicroblockPartition.lean`'s heterogeneous fiber-partition construction — the one new gadget this
identity needs.
-/

namespace CongruenceTheory

open scoped Classical

variable {r : ℕ}

/-- `⊤`'s unique part, for a nonempty base finset. -/
theorem finpartition_top_parts_eq_singleton {α : Type*} [DecidableEq α] {s : Finset α}
    (hs : s.Nonempty) : (⊤ : Finpartition s).parts = {s} := by
  apply Finset.Subset.antisymm (Finpartition.parts_top_subset s)
  obtain ⟨x0, hx0⟩ := hs
  have hmem : (⊤ : Finpartition s).part x0 ∈ (⊤ : Finpartition s).parts :=
    (⊤ : Finpartition s).part_mem.mpr hx0
  have heq : (⊤ : Finpartition s).part x0 = s := by
    have hsub := Finpartition.parts_top_subset s hmem
    exact Finset.mem_singleton.mp hsub
  rw [heq] at hmem
  exact Finset.singleton_subset_iff.mpr hmem

/-- The moment side `\prod_i C(p u_i)` equals the macroblock-partition product
`\prod_{B\in\rho.parts} C(B.card\cdot p)`. -/
theorem prod_C_macroPartition_parts_eq (u : Fin r → ℕ) (hu : ∀ i, 0 < u i) (p : ℕ) :
    ∏ i, C (u i * p) = ∏ B ∈ (macroPartition u).parts, C (B.card * p) := by
  apply Finset.prod_bij (fun i (_ : i ∈ (Finset.univ : Finset (Fin r))) =>
    (macroPartition u).part (⟨i, ⟨0, hu i⟩⟩ : MicroIdx u))
  · intro i _
    exact (macroPartition u).part_mem.mpr (Finset.mem_univ _)
  · intro i1 _ i2 _ heq
    have h1 : (⟨i1, ⟨0, hu i1⟩⟩ : MicroIdx u) ∈
        (macroPartition u).part (⟨i1, ⟨0, hu i1⟩⟩ : MicroIdx u) :=
      (macroPartition u).mem_part_self.mpr (Finset.mem_univ _)
    rw [heq] at h1
    have := (mem_macroPartition_part_iff (⟨i2, ⟨0, hu i2⟩⟩ : MicroIdx u)
      (⟨i1, ⟨0, hu i1⟩⟩ : MicroIdx u)).mp h1
    exact this.symm
  · intro B hB
    obtain ⟨y, hy⟩ := (macroPartition u).nonempty_of_mem_parts hB
    refine ⟨y.1, Finset.mem_univ _, ?_⟩
    have hBeq : (macroPartition u).part y = B :=
      (macroPartition u).part_eq_of_mem hB hy
    have hmem : y ∈ (macroPartition u).part (⟨y.1, ⟨0, hu y.1⟩⟩ : MicroIdx u) :=
      (mem_macroPartition_part_iff (⟨y.1, ⟨0, hu y.1⟩⟩ : MicroIdx u) y).mpr rfl
    have hpeq : (macroPartition u).part y = (macroPartition u).part
        (⟨y.1, ⟨0, hu y.1⟩⟩ : MicroIdx u) :=
      (macroPartition u).part_eq_of_mem
        ((macroPartition u).part_mem.mpr (Finset.mem_univ _)) hmem
    rw [← hpeq, hBeq]
  · intro i _
    rw [card_macroPartition_part]

#print axioms finpartition_top_parts_eq_singleton
#print axioms prod_C_macroPartition_parts_eq

/-- `GenFfun` (the filter-sum form) equals the block-product of `C`, bridging
`GeneralizedConnectivity.lean`'s definition to `GeneralizedPartitionGluing.lean`'s
`gen_sum_ci_respects_eq_prod_C`. -/
theorem GenFfun_eq_prod_C {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} (τ : GenPartLat ι) :
    GenFfun (q := q) τ = ∏ B ∈ τ.parts, C (B.card * q) := by
  unfold GenFfun
  rw [Finset.sum_subtype
    (p := fun g : Equiv.Perm (ι × Fin q) => ∀ x : ι × Fin q, (g x).1 ∈ (τ.part x.1 : Finset ι))
    _ (fun g => by simp) ci]
  exact gen_sum_ci_respects_eq_prod_C τ

/-- **(A7): the moment-cumulant expansion of the multiplicative defect `\Delta_{p\mathbf u}`.**
For a genuinely heterogeneous tuple `u_1,\ldots,u_r`, the defect `C(pT)-\prod_iC(pu_i)`
(`T=\sum u_i`) expands as a sum, over partitions of the `T` labelled `p`-microblocks not
refining the macroblock partition, of the corresponding product of connected cumulants. -/
theorem defect_eq_sum_prod_K {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ) (hu : ∀ i, 0 < u i) (p : ℕ) :
    C ((∑ i, u i) * p) - ∏ i, C (u i * p) =
      ∑ π ∈ (Finset.univ : Finset (GenPartLat (MicroIdx u))).filter
          (fun π => ¬ π ≤ macroPartition u),
        ∏ B ∈ π.parts, K B.card p := by
  have hne : (Finset.univ : Finset (MicroIdx u)).Nonempty := by
    haveI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
    obtain ⟨i0⟩ := ‹Nonempty (Fin r)›
    exact ⟨⟨i0, ⟨0, hu i0⟩⟩, Finset.mem_univ _⟩
  have htopparts : (⊤ : GenPartLat (MicroIdx u)).parts = {Finset.univ} := by
    apply Finset.Subset.antisymm (Finpartition.parts_top_subset _)
    obtain ⟨x0, hx0⟩ := hne
    have hmem : (⊤ : GenPartLat (MicroIdx u)).part x0 ∈ (⊤ : GenPartLat (MicroIdx u)).parts :=
      (⊤ : GenPartLat (MicroIdx u)).part_mem.mpr hx0
    have heq : (⊤ : GenPartLat (MicroIdx u)).part x0 = Finset.univ := by
      have hsub := Finpartition.parts_top_subset (Finset.univ : Finset (MicroIdx u)) hmem
      exact Finset.mem_singleton.mp hsub
    rw [heq] at hmem
    exact Finset.singleton_subset_iff.mpr hmem
  have htop : C ((∑ i, u i) * p) = GenFfun (q := p) (⊤ : GenPartLat (MicroIdx u)) := by
    rw [GenFfun_eq_prod_C, htopparts, Finset.prod_singleton]
    congr 1
    rw [Finset.card_univ, card_microIdx]
  have hrho : ∏ i, C (u i * p) = GenFfun (q := p) (macroPartition u) := by
    rw [prod_C_macroPartition_parts_eq u hu p, GenFfun_eq_prod_C]
  rw [htop, hrho, GenFfun_eq_sum_GenGfun (⊤ : GenPartLat (MicroIdx u)),
    GenFfun_eq_sum_GenGfun (macroPartition u), Finset.Iic_top]
  have hsub : Finset.Iic (macroPartition u) ⊆ (Finset.univ : Finset (GenPartLat (MicroIdx u))) :=
    Finset.subset_univ _
  rw [← Finset.sum_sdiff_eq_sub hsub]
  have hset : (Finset.univ : Finset (GenPartLat (MicroIdx u))) \ Finset.Iic (macroPartition u) =
      (Finset.univ : Finset (GenPartLat (MicroIdx u))).filter
        (fun π => ¬ π ≤ macroPartition u) := by
    apply Finset.ext
    intro π
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Iic]
  rw [hset]
  exact Finset.sum_congr rfl (fun π _ => genGfun_eq_prod_K π)

#print axioms GenFfun_eq_prod_C
#print axioms defect_eq_sum_prod_K

end CongruenceTheory
