import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.GeneralizedConnectivity

/-!
**The fiber partition of a heterogeneous macroblock decomposition**: given block sizes
`u : Fin r → ℕ`, the `T = Σu_i` p-microblocks (indexed by the Sigma type `MicroIdx u`) split
canonically into `r` macroblocks of sizes `u_1,\ldots,u_r`, grouped by their first (macroblock)
coordinate. This is the one genuinely new combinatorial gadget the moment-cumulant expansion (A7)
needs beyond the already-general `Generalized*`/`PartitionShape`/`ShapeCpSplit` machinery, which
places no uniformity assumption on block sizes but never previously needed a *specific*
heterogeneous partition constructed from a tuple.
-/

namespace CongruenceTheory

open scoped Classical

variable {r : ℕ}

/-- The `T = Σu_i` p-microblocks, indexed by macroblock then position within it. -/
abbrev MicroIdx (u : Fin r → ℕ) := Σ i : Fin r, Fin (u i)

theorem card_microIdx (u : Fin r → ℕ) : Fintype.card (MicroIdx u) = ∑ i, u i := by
  rw [Fintype.card_sigma]
  simp

noncomputable instance instDecidableRelKerFst (u : Fin r → ℕ) :
    DecidableRel (Setoid.ker (Sigma.fst : MicroIdx u → Fin r)).r := Classical.decRel _

/-- The canonical macroblock partition of the microblocks, grouping by first coordinate. -/
noncomputable def macroPartition (u : Fin r → ℕ) : GenPartLat (MicroIdx u) :=
  Finpartition.ofSetoid (Setoid.ker (Sigma.fst : MicroIdx u → Fin r))

theorem mem_macroPartition_part_iff {u : Fin r → ℕ} (x y : MicroIdx u) :
    y ∈ (macroPartition u).part x ↔ x.1 = y.1 := by
  unfold macroPartition
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  exact Iff.rfl

/-- The macroblock containing `⟨i,j⟩` is exactly the fiber over `i`. -/
theorem macroPartition_part_eq_filter {u : Fin r → ℕ} (i : Fin r) (j : Fin (u i)) :
    (macroPartition u).part ⟨i, j⟩ = Finset.univ.filter (fun y : MicroIdx u => y.1 = i) := by
  ext y
  rw [Finset.mem_filter, mem_macroPartition_part_iff]
  simp only [Finset.mem_univ, true_and]
  exact eq_comm

/-- Each macroblock's canonical bijection with `Fin (u i)`. -/
noncomputable def microFiberEquiv (u : Fin r → ℕ) (i : Fin r) :
    {y : MicroIdx u // y.1 = i} ≃ Fin (u i) where
  toFun y := y.2 ▸ y.1.2
  invFun j := ⟨⟨i, j⟩, rfl⟩
  left_inv y := by
    obtain ⟨⟨i', j'⟩, (rfl : i' = i)⟩ := y
    rfl
  right_inv j := rfl

/-- Every macroblock of `macroPartition u` has exactly the size `u i` of its index. -/
theorem card_macroPartition_part {u : Fin r → ℕ} (i : Fin r) (j : Fin (u i)) :
    ((macroPartition u).part ⟨i, j⟩).card = u i := by
  rw [macroPartition_part_eq_filter i j, ← Fintype.card_subtype,
    Fintype.card_congr (microFiberEquiv u i)]
  simp

#print axioms card_macroPartition_part

end CongruenceTheory
