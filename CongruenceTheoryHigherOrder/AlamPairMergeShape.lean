import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.DefectValuationExactWeight
import CongruenceTheoryHigherOrder.CommonPrimeClassificationDepth

/-!
**`A_\lambda(\mathbf u)` at the "pair-merge" shape `(2,1^{U-2})`, `U=\sum_iu_i`, equals
`\sum_{i<j}u_iu_j`.** Every non-refining partition of this shape merges exactly two microblocks
`x,y` from *different* macroblocks (all other microblocks stay singleton, since a partition all
of whose non-singleton block is `\{x,y\}` is non-refining iff `x,y` lie in different macroblocks
— the same characterization `exists_ge_two_of_not_le_macroPartition` already established the
"non-singleton block exists" half of). This is the manuscript's `A_2` in
`thm:complete-prime-local`(ii)'s delicate `b\le E` branch.
-/

namespace CongruenceTheory

open scoped Classical

variable {r : ℕ} (u : Fin r → ℕ)

/-- **The "merge exactly `x,y`" partition**: singletons everywhere except the one block
`\{x,y\}`. -/
noncomputable def mergePair {x y : MicroIdx u} (hxy : x ≠ y) : GenPartLat (MicroIdx u) :=
  (⊥ : Finpartition ((Finset.univ : Finset (MicroIdx u)) \ ({x, y} : Finset (MicroIdx u)))).extend
    (b := ({x, y} : Finset (MicroIdx u)))
    (by
      rw [Finset.bot_eq_empty]
      exact Finset.Nonempty.ne_empty ⟨x, by simp⟩)
    (by
      rw [Finset.disjoint_left]
      intro a ha hab
      exact (Finset.mem_sdiff.mp ha).2 hab)
    (by
      rw [Finset.sup_eq_union, Finset.sdiff_union_of_subset (Finset.subset_univ _)])

theorem mergePair_parts {x y : MicroIdx u} (hxy : x ≠ y) :
    (mergePair u hxy).parts =
      insert ({x, y} : Finset (MicroIdx u))
        ((((Finset.univ : Finset (MicroIdx u)) \ ({x, y} : Finset (MicroIdx u)))).map
          ⟨singleton, Finset.singleton_injective⟩) := by
  unfold mergePair
  rw [Finpartition.extend_parts, Finpartition.parts_bot]

/-- **The shape of `mergePair` is exactly `\{2\}+\text{replicate}(U-2)\,1`,** `U =
\text{Fintype.card}(MicroIdx\,u)`. -/
theorem shape_mergePair {x y : MicroIdx u} (hxy : x ≠ y) :
    GenPartLatShape (mergePair u hxy) =
      {2} + Multiset.replicate (Fintype.card (MicroIdx u) - 2) 1 := by
  unfold GenPartLatShape
  rw [mergePair_parts]
  have hxynotmem : ({x, y} : Finset (MicroIdx u)) ∉
      (((Finset.univ : Finset (MicroIdx u)) \ ({x, y} : Finset (MicroIdx u)))).map
        ⟨singleton, Finset.singleton_injective⟩ := by
    intro hmem
    obtain ⟨a, ha, heq⟩ := Finset.mem_map.mp hmem
    simp only [Function.Embedding.coeFn_mk] at heq
    have hcard : ({a} : Finset (MicroIdx u)).card = ({x, y} : Finset (MicroIdx u)).card := by
      rw [heq]
    rw [Finset.card_singleton, Finset.card_pair_eq_two_iff.mpr hxy] at hcard
    omega
  rw [Finset.insert_val_of_notMem hxynotmem]
  rw [Multiset.map_cons, Finset.card_pair_eq_two_iff.mpr hxy]
  have htail : Multiset.map Finset.card
      (Finset.map (⟨singleton, Finset.singleton_injective⟩ : MicroIdx u ↪ Finset (MicroIdx u))
        ((Finset.univ : Finset (MicroIdx u)) \ ({x, y} : Finset (MicroIdx u)))).val =
      Multiset.replicate (Fintype.card (MicroIdx u) - 2) 1 := by
    rw [Finset.map_val, Multiset.map_map]
    have hcard : (((Finset.univ : Finset (MicroIdx u)) \
        ({x, y} : Finset (MicroIdx u)))).card = Fintype.card (MicroIdx u) - 2 := by
      rw [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ,
        Finset.card_pair_eq_two_iff.mpr hxy]
    rw [← hcard]
    apply Multiset.eq_replicate.mpr
    refine ⟨?_, ?_⟩
    · rw [Multiset.card_map]; rfl
    · intro b hb
      obtain ⟨a, -, heq⟩ := Multiset.mem_map.mp hb
      simp only [Function.Embedding.coeFn_mk, Function.comp_apply] at heq
      rw [← heq, Finset.card_singleton]
  rw [htail]
  simp

/-- **Non-refining characterization of `mergePair`**: it is non-refining exactly when `x,y`
belong to different macroblocks. -/
theorem mergePair_mem_nonRefiningPartitions_iff {x y : MicroIdx u} (hxy : x ≠ y) :
    mergePair u hxy ∈ nonRefiningPartitions u ↔ x.1 ≠ y.1 := by
  unfold nonRefiningPartitions
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hnle
    by_contra hxy1
    apply hnle
    intro b hb
    rw [mergePair_parts] at hb
    simp only [Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · refine ⟨(macroPartition u).part x, (macroPartition u).part_mem.mpr (Finset.mem_univ x), ?_⟩
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz
      · rw [hz]; exact (macroPartition u).mem_part_self.mpr (Finset.mem_univ x)
      · rw [hz, mem_macroPartition_part_iff]; exact hxy1
    · obtain ⟨a, -, heq⟩ := Finset.mem_map.mp hb
      simp only [Function.Embedding.coeFn_mk] at heq
      refine ⟨(macroPartition u).part a, (macroPartition u).part_mem.mpr (Finset.mem_univ a), ?_⟩
      rw [← heq]
      intro z hz
      rw [Finset.mem_singleton] at hz
      rw [hz]
      exact (macroPartition u).mem_part_self.mpr (Finset.mem_univ a)
  · intro hxy1 hle
    apply hxy1
    obtain ⟨c, hcmem, hsub⟩ := hle (show ({x, y} : Finset (MicroIdx u)) ∈ (mergePair u hxy).parts
      from by rw [mergePair_parts]; exact Finset.mem_insert_self _ _)
    have hxc : x ∈ c := hsub (by simp)
    have hyc : y ∈ c := hsub (by simp)
    have hceq : (macroPartition u).part x = c := (macroPartition u).part_eq_of_mem hcmem hxc
    rw [← hceq] at hyc
    exact (mem_macroPartition_part_iff x y).mp hyc

#print axioms mergePair_parts
#print axioms shape_mergePair
#print axioms mergePair_mem_nonRefiningPartitions_iff

end CongruenceTheory
