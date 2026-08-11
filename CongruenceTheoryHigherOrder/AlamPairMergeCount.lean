import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.AlamPairMergeShape
import CongruenceTheoryHigherOrder.TranspositionCoefficientClosedForm

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

/-- **`mergePair` does not depend on the order of `x,y`.** -/
theorem mergePair_symm {x y : MicroIdx u} (hxy : x ≠ y) :
    mergePair u hxy = mergePair u hxy.symm := by
  apply eq_mergePair_of_parts_eq u hxy.symm
  · rw [Finset.pair_comm]
    rw [mergePair_parts]
    exact Finset.mem_insert_self _ _
  · intro C hC hCne
    have hCne' : C ≠ ({x, y} : Finset (MicroIdx u)) := by
      rw [Finset.pair_comm]; exact hCne
    rw [mergePair_parts] at hC
    rw [Finset.mem_insert] at hC
    rcases hC with hC | hC
    · exact absurd hC hCne'
    · obtain ⟨v, -, heq⟩ := Finset.mem_map.mp hC
      simp only [Function.Embedding.coeFn_mk] at heq
      rw [← heq, Finset.card_singleton]

/-- The ordered cross-macroblock pairs of microblocks: `(x,y)` with `x` in a strictly earlier
macroblock than `y`. -/
noncomputable def crossPairsOrdered (u : Fin r → ℕ) : Finset (MicroIdx u × MicroIdx u) :=
  (Finset.univ : Finset (MicroIdx u × MicroIdx u)).filter (fun p => p.1.1 < p.2.1)

theorem mem_crossPairsOrdered {u : Fin r → ℕ} {p : MicroIdx u × MicroIdx u} :
    p ∈ crossPairsOrdered u ↔ p.1.1 < p.2.1 := by
  unfold crossPairsOrdered
  rw [Finset.mem_filter]
  simp

/-- Elements related by `<` on their macroblock coordinate are distinct. -/
theorem ne_of_fst_lt {x y : MicroIdx u} (h : x.1 < y.1) : x ≠ y :=
  fun heq => absurd (congrArg Sigma.fst heq) (ne_of_lt h)

/-- **`A_\lambda(\mathbf u)` at the pair-merge shape equals the number of ordered cross-macroblock
pairs.** -/
theorem Alam_pairMergeShape_eq_card_crossPairsOrdered :
    Alam u ({2} + Multiset.replicate (Fintype.card (MicroIdx u) - 2) 1) =
      (crossPairsOrdered u).card := by
  set lam : Multiset ℕ := {2} + Multiset.replicate (Fintype.card (MicroIdx u) - 2) 1 with hlam
  have hAlam : Alam u lam =
      ((nonRefiningPartitions u).filter (fun π => GenPartLatShape π = lam)).card := rfl
  rw [hAlam, eq_comm]
  apply Finset.card_bij (fun p hp => mergePair u
    (ne_of_fst_lt u (mem_crossPairsOrdered.mp hp)))
  · intro p hp
    rw [Finset.mem_filter]
    have hlt : p.1.1 < p.2.1 := mem_crossPairsOrdered.mp hp
    refine ⟨?_, shape_mergePair u _⟩
    rw [mergePair_mem_nonRefiningPartitions_iff]
    exact ne_of_lt hlt
  · intro p1 hp1 p2 hp2 heq
    have hlt1 : p1.1.1 < p1.2.1 := mem_crossPairsOrdered.mp hp1
    have hlt2 : p2.1.1 < p2.2.1 := mem_crossPairsOrdered.mp hp2
    set x1 := p1.1; set y1 := p1.2; set x2 := p2.1; set y2 := p2.2
    -- extract the unique pair-block from both sides
    have hshape1 : GenPartLatShape (mergePair u (ne_of_fst_lt u hlt1)) = lam :=
      shape_mergePair u _
    obtain ⟨B, ⟨hBmem, hBcard⟩, hBuniq⟩ := exists_unique_pair_block u hshape1
    have hx1y1mem : ({x1, y1} : Finset (MicroIdx u)) ∈
        (mergePair u (ne_of_fst_lt u hlt1)).parts ∧
        ({x1, y1} : Finset (MicroIdx u)).card = 2 :=
      ⟨by rw [mergePair_parts]; exact Finset.mem_insert_self _ _,
        Finset.card_pair_eq_two_iff.mpr (ne_of_fst_lt u hlt1)⟩
    have hx2y2mem : ({x2, y2} : Finset (MicroIdx u)) ∈
        (mergePair u (ne_of_fst_lt u hlt1)).parts ∧
        ({x2, y2} : Finset (MicroIdx u)).card = 2 := by
      rw [heq]
      exact ⟨by rw [mergePair_parts]; exact Finset.mem_insert_self _ _,
        Finset.card_pair_eq_two_iff.mpr (ne_of_fst_lt u hlt2)⟩
    have e1 : ({x1, y1} : Finset (MicroIdx u)) = B := hBuniq _ hx1y1mem
    have e2 : ({x2, y2} : Finset (MicroIdx u)) = B := hBuniq _ hx2y2mem
    have hpairset : ({x1, y1} : Finset (MicroIdx u)) = ({x2, y2} : Finset (MicroIdx u)) :=
      e1.trans e2.symm
    have hx2mem : x2 ∈ ({x1, y1} : Finset (MicroIdx u)) := by
      rw [hpairset]; exact Finset.mem_insert_self _ _
    have hy2mem : y2 ∈ ({x1, y1} : Finset (MicroIdx u)) := by
      rw [hpairset]; simp
    rw [Finset.mem_insert, Finset.mem_singleton] at hx2mem hy2mem
    rcases hx2mem with hx2 | hx2
    · rcases hy2mem with hy2 | hy2
      · exact absurd (congrArg Sigma.fst (hx2.trans hy2.symm)) (ne_of_lt hlt2)
      · exact Prod.ext hx2.symm hy2.symm
    · rcases hy2mem with hy2 | hy2
      · exfalso
        have hrev : y1.1 < x1.1 := by rw [hx2, hy2] at hlt2; exact hlt2
        exact absurd hlt1 (not_lt.mpr hrev.le)
      · exact absurd (congrArg Sigma.fst (hx2.trans hy2.symm)) (ne_of_lt hlt2)
  · intro π hπ
    rw [Finset.mem_filter] at hπ
    obtain ⟨hπnr, hπshape⟩ := hπ
    obtain ⟨B, ⟨hBmem, hBcard⟩, hBuniq⟩ := exists_unique_pair_block u hπshape
    obtain ⟨x, y, hxy, hBxy⟩ := Finset.card_eq_two.mp hBcard
    have hxymem : ({x, y} : Finset (MicroIdx u)) ∈ π.parts := hBxy ▸ hBmem
    have hrest : ∀ C ∈ π.parts, C ≠ ({x, y} : Finset (MicroIdx u)) → C.card = 1 := by
      intro C hCmem hCne
      have hCin : C.card ∈ lam := by
        have : C.card ∈ GenPartLatShape π := by
          unfold GenPartLatShape
          exact Multiset.mem_map_of_mem _ hCmem
        rwa [hπshape] at this
      rw [hlam, Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_replicate] at hCin
      rcases hCin with hC2 | ⟨-, hC1⟩
      · exfalso
        apply hCne
        have hCcard2 : C.card = 2 := hC2
        have := hBuniq C ⟨hCmem, hCcard2⟩
        rw [hBxy] at this
        exact this
      · exact hC1
    have hπeq : π = mergePair u hxy :=
      eq_mergePair_of_parts_eq u hxy hxymem hrest
    rcases lt_or_gt_of_ne (show x.1 ≠ y.1 from by
      rw [hπeq] at hπnr
      exact mergePair_mem_nonRefiningPartitions_iff u hxy |>.mp hπnr) with hlt | hgt
    · exact ⟨(x, y), mem_crossPairsOrdered.mpr hlt, hπeq.symm⟩
    · refine ⟨(y, x), mem_crossPairsOrdered.mpr hgt, ?_⟩
      show mergePair u (show y ≠ x from Ne.symm hxy) = π
      rw [← mergePair_symm u hxy]
      exact hπeq.symm

/-- The pairwise cross-sum `\sum_{i<j}n_in_j` as a natural number. -/
noncomputable def natCrossSum {r : ℕ} (n : Fin r → ℕ) : ℕ :=
  ∑ i : Fin r, ∑ j : Fin r, (if i < j then n i * n j else 0)

theorem natCrossSum_cons {t : ℕ} (a : ℕ) (m : Fin t → ℕ) :
    natCrossSum (Fin.cons a m : Fin (t + 1) → ℕ) = a * (∑ i, m i) + natCrossSum m := by
  unfold natCrossSum
  rw [Fin.sum_univ_succ]
  have hj0 : (∑ j : Fin (t + 1),
      (if (0 : Fin (t + 1)) < j then (Fin.cons a m : Fin (t+1) → ℕ) 0 *
        (Fin.cons a m : Fin (t+1) → ℕ) j else 0)) = a * (∑ i, m i) := by
    rw [Fin.sum_univ_succ]
    simp only [lt_irrefl, if_false, Fin.cons_zero, Fin.cons_succ, zero_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hpos : (0 : Fin (t+1)) < i.succ := by rw [Fin.lt_iff_val_lt_val]; simp
    simp [hpos]
  rw [hj0]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ]
  have h0 : ¬ (i.succ < (0 : Fin (t+1))) := by rw [Fin.lt_iff_val_lt_val]; simp
  simp only [h0, if_false, Fin.cons_succ, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  have hiff : (i.succ < j.succ) ↔ (i < j) := by rw [Fin.succ_lt_succ_iff]
  by_cases hij : i < j
  · rw [if_pos hij, if_pos (hiff.mpr hij)]
  · rw [if_neg hij, if_neg (fun h => hij (hiff.mp h))]

/-- **The cardinality of the ordered cross-macroblock pairs is the double sum
`\sum_{i<j}u_iu_j`.** -/
theorem card_crossPairsOrdered_eq_sum (u : Fin r → ℕ) :
    (crossPairsOrdered u).card = natCrossSum u := by
  unfold natCrossSum
  unfold crossPairsOrdered
  rw [Finset.card_filter]
  rw [Fintype.sum_prod_type]
  have hstep : ∀ x : MicroIdx u, (∑ y : MicroIdx u, if x.1 < y.1 then (1 : ℕ) else 0) =
      ∑ j : Fin r, (if x.1 < j then u j else 0) := by
    intro x
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    by_cases hj : x.1 < j <;>
      simp [hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  calc ∑ x : MicroIdx u, ∑ y : MicroIdx u, (if x.1 < y.1 then (1 : ℕ) else 0)
      = ∑ x : MicroIdx u, ∑ j : Fin r, (if x.1 < j then u j else 0) := by
        apply Finset.sum_congr rfl; intro x _; exact hstep x
    _ = ∑ i : Fin r, ∑ (_ : Fin (u i)), ∑ j : Fin r, (if i < j then u j else 0) := by
        rw [Fintype.sum_sigma]
    _ = ∑ i : Fin r, u i * ∑ j : Fin r, (if i < j then u j else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ = ∑ i : Fin r, ∑ j : Fin r, (if i < j then u i * u j else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i < j <;> simp [hij]

/-- **`\text{pairSum}(\mathbf n) = \text{natCrossSum}(\mathbf n)` (cast to `ℤ`).** -/
theorem pairSum_eq_natCrossSum {r : ℕ} (n : Fin r → ℕ) :
    pairSum n = (natCrossSum n : ℤ) := by
  induction r with
  | zero => unfold pairSum natCrossSum; simp
  | succ t ih =>
    have hn0 : n = Fin.cons (n 0) (Fin.tail n) := (Fin.cons_self_tail n).symm
    rw [hn0, pairSum_cons, ih (Fin.tail n), natCrossSum_cons]
    push_cast
    ring

/-- **`A_\lambda(\mathbf u)` at the pair-merge shape `(2,1^{U-2})` equals `\sum_{i<j}u_iu_j`
exactly**, matching the closed form of the transposition coefficient. -/
theorem Alam_pairMergeShape_eq :
    (Alam u ({2} + Multiset.replicate (Fintype.card (MicroIdx u) - 2) 1) : ℤ) = pairSum u := by
  rw [Alam_pairMergeShape_eq_card_crossPairsOrdered, card_crossPairsOrdered_eq_sum,
    pairSum_eq_natCrossSum]

#print axioms eq_mergePair_of_parts_eq
#print axioms exists_unique_pair_block
#print axioms mergePair_symm
#print axioms Alam_pairMergeShape_eq_card_crossPairsOrdered
#print axioms natCrossSum_cons
#print axioms card_crossPairsOrdered_eq_sum
#print axioms pairSum_eq_natCrossSum
#print axioms Alam_pairMergeShape_eq

end CongruenceTheory
