import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.AlamPairMergeShape

/-!
**`A_\lambda(\mathbf u)` at the pair-merge shape `(2,1^{U-2})` equals `\sum_{i<j}u_iu_j`
exactly.** A non-refining partition of this shape is *determined* by its unique size-`2` block
`\{x,y\}` (all other parts are forced to be singletons by the shape), giving a bijection with
ordered pairs `(x,y)` of microblocks in different macroblocks with `x.1<y.1`.
-/

namespace CongruenceTheory

open scoped Classical

variable {r : ℕ} (u : Fin r → ℕ)

/-- **A partition all of whose parts besides `\{x,y\}` are singletons, and which contains
`\{x,y\}`, is exactly `mergePair` at `x,y`.** -/
theorem eq_mergePair_of_parts_eq {π : GenPartLat (MicroIdx u)} {x y : MicroIdx u} (hxy : x ≠ y)
    (hBmem : ({x, y} : Finset (MicroIdx u)) ∈ π.parts)
    (hrest : ∀ C ∈ π.parts, C ≠ ({x, y} : Finset (MicroIdx u)) → C.card = 1) :
    π = mergePair u hxy := by
  have hparts : π.parts = insert ({x, y} : Finset (MicroIdx u))
      ((((Finset.univ : Finset (MicroIdx u)) \ ({x, y} : Finset (MicroIdx u)))).map
        ⟨singleton, Finset.singleton_injective⟩) := by
    apply Finset.ext
    intro C
    rw [Finset.mem_insert]
    constructor
    · intro hC
      by_cases hCxy : C = ({x, y} : Finset (MicroIdx u))
      · exact Or.inl hCxy
      · right
        have hC1 := hrest C hC hCxy
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hC1
        rw [Finset.mem_map]
        refine ⟨v, ?_, by rw [hv]; rfl⟩
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ v, ?_⟩
        intro hvxy
        have hvC : v ∈ C := hv ▸ Finset.mem_singleton_self v
        have hveq : π.part v = ({v} : Finset (MicroIdx u)) := by
          rw [π.part_eq_of_mem hC hvC, hv]
        have hveq2 : π.part v = ({x, y} : Finset (MicroIdx u)) :=
          π.part_eq_of_mem hBmem hvxy
        rw [hveq2] at hveq
        have hcardeq := congrArg Finset.card hveq
        rw [Finset.card_pair_eq_two_iff.mpr hxy, Finset.card_singleton] at hcardeq
        omega
    · intro hC
      rcases hC with rfl | hC
      · exact hBmem
      · obtain ⟨v, hv, heq⟩ := Finset.mem_map.mp hC
        simp only [Function.Embedding.coeFn_mk] at heq
        rw [Finset.mem_sdiff] at hv
        rw [← heq]
        obtain ⟨c, hcmem, hvc⟩ := π.exists_mem (Finset.mem_univ v)
        have hcne : c ≠ ({x, y} : Finset (MicroIdx u)) := by
          intro hceq; rw [hceq] at hvc; exact hv.2 hvc
        have hc1 := hrest c hcmem hcne
        obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc1
        have hwv : w = v := by
          have hvw : v ∈ ({w} : Finset (MicroIdx u)) := hw ▸ hvc
          exact (Finset.mem_singleton.mp hvw).symm
        rw [← hwv, ← hw]
        exact hcmem
  have hmergeParts := mergePair_parts u hxy
  exact Finpartition.ext (hparts.trans hmergeParts.symm)

/-- **Every partition of the pair-merge shape has a unique size-`2` block.** -/
theorem exists_unique_pair_block {π : GenPartLat (MicroIdx u)}
    (hshape : GenPartLatShape π = {2} + Multiset.replicate (Fintype.card (MicroIdx u) - 2) 1) :
    ∃! B, B ∈ π.parts ∧ B.card = 2 := by
  have hcount : (GenPartLatShape π).count 2 = 1 := by
    rw [hshape, Multiset.count_add, Multiset.count_singleton_self]
    have hz : Multiset.count 2 (Multiset.replicate (Fintype.card (MicroIdx u) - 2) 1) = 0 := by
      rw [Multiset.count_replicate]
      simp
    rw [hz]
  unfold GenPartLatShape at hcount
  rw [Multiset.count_map] at hcount
  have hval : (π.parts.filter (fun C => C.card = 2)).val =
      π.parts.val.filter (fun C => (2 : ℕ) = C.card) := by
    rw [Finset.filter_val]
    apply Multiset.filter_congr
    intro C _
    exact eq_comm
  have hcard1 : (π.parts.filter (fun C => C.card = 2)).card = 1 :=
    calc (π.parts.filter (fun C => C.card = 2)).card
        = (π.parts.filter (fun C => C.card = 2)).val.card := rfl
      _ = (π.parts.val.filter (fun C => (2 : ℕ) = C.card)).card := by rw [hval]
      _ = 1 := hcount
  obtain ⟨B, hB⟩ := Finset.card_eq_one.mp hcard1
  refine ⟨B, ?_, ?_⟩
  · have hBmem : B ∈ π.parts.filter (fun C => C.card = 2) := by
      rw [hB]; exact Finset.mem_singleton_self _
    exact Finset.mem_filter.mp hBmem
  · intro B' hB'
    have hB'mem : B' ∈ π.parts.filter (fun C => C.card = 2) := Finset.mem_filter.mpr hB'
    rw [hB, Finset.mem_singleton] at hB'mem
    exact hB'mem

#print axioms eq_mergePair_of_parts_eq
#print axioms exists_unique_pair_block

end CongruenceTheory
