import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheory.ContentBounds
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.WreathProduct
import CongruenceTheoryHigherOrder.Semiregularity
import CongruenceTheoryHigherOrder.ConjugationInvariance
import CongruenceTheoryHigherOrder.StabilizerBound
import CongruenceTheoryHigherOrder.OrbitCounting

/-!
**Inequality (A1) of `thm:atomic-connected-content`, fully assembled**: `(r-1)!q^{r-1} ∣ K_r(q)`,
at the level of a single coefficient. **`coeff_K_dvd`**: for every connected permutation `g`, the
coefficient of `K_r(q)` at `g`'s cycle-type monomial is divisible by `q^{r-1}(r-1)!`. This closes
out every remaining piece flagged as open in `OrbitCounting.lean`.

**What's added on top of `OrbitCounting.lean`'s abstract index divisibility**:
- **`wreathOrbit hq g`**: the actual `Finset` of wreath-conjugates of `g` inside
  `Equiv.Perm (Fin r × Fin q)` (not just an abstract subgroup index). `card_wreathOrbit_mul`
  shows `|wreathOrbit g| · |wreathStab g| = |Wreath r q|` directly, via a from-scratch
  fiber-counting argument (`card_conj_fiber`: every fiber of the conjugation map has the same
  size `|wreathStab g|`, since fibers are exactly the cosets of `wreathStab g` — made precise by
  the general group identity `conj_eq_conj_iff_commute`, `a·x·a⁻¹ = b·x·b⁻¹ ↔ Commute (b⁻¹a) x`).
  Combined with `OrbitCounting.lean`'s `index_wreathStab_dvd_mul` (via `Subgroup.index_mul_card`),
  this gives **`card_wreathOrbit_dvd_mul`**: `|wreathOrbit g|` is a literal multiple of
  `q^{r-1}(r-1)!`.
- **`wreathOrbit_subset`**: conjugates of a connected `g` stay connected and same-cycle-type
  (via `ConjugationInvariance.lean`'s `piOf_conj_eq_top` and Mathlib's
  `Equiv.Perm.cycleType_conj`).
- **`connSameTypeFinset g`**: the actual coefficient-counting set,
  `{h : π(h)=⊤ ∧ cycleType h = cycleType g}`. Its cardinality is exactly the coefficient of
  `K_r(q)` at `g`'s cycle-type monomial, via **`coeff_sum_ci_eq_card_cycleType_filter`**
  (generalizing `ContentBounds.lean`'s `coeff_sum_ci_eq_card_cycleType` from `Finset.univ` to an
  arbitrary `Finset`) applied to `ConnectedCount.lean`'s `K_eq_Gfun_top`/`Gfun`.
- **The union-of-orbits argument**: `wreathRel`/`wreathSetoid` (wreath-conjugacy is an equivalence
  relation on `Equiv.Perm (Fin r × Fin q)`) lets Mathlib's `Finpartition.ofSetSetoid` decompose
  `connSameTypeFinset g` into wreath-orbits (`wreathOrbit_eq_part`: each part of this partition
  *is* literally a `wreathOrbit`, using `wreathOrbit_subset` to confirm orbits don't leak outside
  the counting set). **`card_connSameTypeFinset_dvd`** applies `card_wreathOrbit_dvd_mul` to
  *every* part (not just `g`'s own orbit — every representative in the set is itself connected,
  so the same divisibility applies to it) and sums (`Finpartition.sum_card_parts` +
  `Finset.dvd_sum`) to conclude the *entire* coefficient-counting set's size is a multiple of
  `q^{r-1}(r-1)!`.

Combining the last two points gives **`coeff_K_dvd`**, the fully assembled inequality.

**Honest scope note**: this completes inequality (A1) itself — the manuscript's own
`(r-1)!q^{r-1} ∣ K_r(q)` — at the coefficient level (equivalent to divisibility of
`cont K_r(q)`, since content is the gcd of all coefficients and this holds for every connected
`g`'s cycle type; the manuscript's own further step of also covering non-connected coefficients
via `K_r(q)`'s definition is not separately re-derived here). What remains for
`thm:atomic-connected-content` as a whole is everything beyond (A1): (A2)'s stabilizer bound via
the bipartite incidence-graph automorphism induction with cut-vertex case splits (A2a), the
moment-cumulant expansion (A4), the mod-`p` algebraic-independence argument via triangular
Jacobians (A5), the falling-factorial Vandermonde identity combined with `HypertreeEnumerator.lean`
(A6), and Lucas' theorem for the sharpness direction — each its own substantial, research-scale
undertaking, none attempted here.
-/

namespace CongruenceTheory

open scoped Classical

theorem conj_eq_conj_iff_commute {G : Type*} [Group G] (a b x : G) :
    a * x * a⁻¹ = b * x * b⁻¹ ↔ Commute (b⁻¹ * a) x := by
  rw [Commute, SemiconjBy]
  constructor
  · intro h
    have hxc : b⁻¹ * a * x * (b⁻¹ * a)⁻¹ = x := by
      rw [mul_inv_rev, inv_inv]
      calc b⁻¹ * a * x * (a⁻¹ * b)
          = b⁻¹ * (a * x * a⁻¹) * b := by group
        _ = b⁻¹ * (b * x * b⁻¹) * b := by rw [h]
        _ = x := by group
    calc b⁻¹ * a * x = b⁻¹ * a * x * (b⁻¹ * a)⁻¹ * (b⁻¹ * a) := by group
      _ = x * (b⁻¹ * a) := by rw [hxc]
  · intro h
    have hxc : b⁻¹ * a * x * (b⁻¹ * a)⁻¹ = x := by
      rw [h]; group
    calc a * x * a⁻¹ = b * (b⁻¹ * a * x * (b⁻¹ * a)⁻¹) * b⁻¹ := by
          rw [mul_inv_rev, inv_inv]; group
      _ = b * x * b⁻¹ := by rw [hxc]

/-- **General coefficient extraction over an arbitrary Finset of permutations**, generalizing
`coeff_sum_ci_eq_card_cycleType` (which is the case `S = Finset.univ`). -/
theorem coeff_sum_ci_eq_card_cycleType_filter {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset (Equiv.Perm α)) (m : Multiset ℕ) (hm2 : ∀ x ∈ m, 2 ≤ x) :
    MvPolynomial.coeff (ciExp (Fintype.card α - m.sum) m) (∑ g ∈ S, ci g) =
      ((S.filter (fun g : Equiv.Perm α => g.cycleType = m)).card : ℤ) := by
  rw [MvPolynomial.coeff_sum]
  have hcast : ((S.filter (fun g : Equiv.Perm α => g.cycleType = m)).card : ℤ) =
      ∑ g ∈ S, (if g.cycleType = m then (1 : ℤ) else 0) := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [hcast]
  apply Finset.sum_congr rfl
  intro g _
  rw [ci_eq_monomial', MvPolynomial.coeff_monomial]
  have hgne : ∀ x ∈ g.cycleType, x ≠ 1 := fun x hx => by
    have := Equiv.Perm.two_le_of_mem_cycleType hx; omega
  have hmne : ∀ x ∈ m, x ≠ 1 := fun x hx => by have := hm2 x hx; omega
  by_cases hgm : g.cycleType = m
  · simp [hgm]
  · have hne : ciExp (Fintype.card α - g.cycleType.sum) g.cycleType ≠
        ciExp (Fintype.card α - m.sum) m := by
      intro hcontra
      exact hgm ((ciExp_eq_iff hgne hmne).mp hcontra).2
    simp [hne, hgm]

variable {r q : ℕ} [NeZero r] [NeZero q] (hq : 2 ≤ q)

noncomputable instance : Fintype (Wreath r q) :=
  Fintype.ofEquiv (WreathN r q × Equiv.Perm (Fin r)) (SemidirectProduct.equivProd).symm

/-- The (finite) set of wreath-conjugates of `g`. -/
noncomputable def wreathOrbit (g : Equiv.Perm (Fin r × Fin q)) :
    Finset (Equiv.Perm (Fin r × Fin q)) :=
  Finset.univ.image
    (fun w : Wreath r q => wreathToPermRotate r q hq w * g * (wreathToPermRotate r q hq w)⁻¹)

omit [NeZero r] in
theorem conj_fiber_eq {g : Equiv.Perm (Fin r × Fin q)} (w2 : Wreath r q) :
    (Finset.univ.filter (fun w1 : Wreath r q =>
      wreathToPermRotate r q hq w1 * g * (wreathToPermRotate r q hq w1)⁻¹ =
        wreathToPermRotate r q hq w2 * g * (wreathToPermRotate r q hq w2)⁻¹)) =
      Finset.univ.filter (fun w1 => w2⁻¹ * w1 ∈ wreathStab hq g) := by
  ext w1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [conj_eq_conj_iff_commute]
  show _ ↔ Commute (wreathToPermRotate r q hq (w2⁻¹ * w1)) g
  rw [map_mul, map_inv]

omit [NeZero r] in
theorem card_conj_fiber {g : Equiv.Perm (Fin r × Fin q)} (w2 : Wreath r q) :
    (Finset.univ.filter (fun w1 : Wreath r q =>
      wreathToPermRotate r q hq w1 * g * (wreathToPermRotate r q hq w1)⁻¹ =
        wreathToPermRotate r q hq w2 * g * (wreathToPermRotate r q hq w2)⁻¹)).card =
      Nat.card (wreathStab hq g) := by
  rw [conj_fiber_eq hq w2]
  rw [show (Finset.univ.filter (fun w1 : Wreath r q => w2⁻¹ * w1 ∈ wreathStab hq g)) =
      Finset.image (fun s : wreathStab hq g => w2 * (s : Wreath r q)) Finset.univ from by
    ext w1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨⟨w2⁻¹ * w1, h⟩, by show w2 * (w2⁻¹ * w1) = w1; group⟩
    · rintro ⟨s, rfl⟩
      show w2⁻¹ * (w2 * (s : Wreath r q)) ∈ wreathStab hq g
      have hs : (s : Wreath r q) ∈ wreathStab hq g := s.2
      have heq : w2⁻¹ * (w2 * (s : Wreath r q)) = (s : Wreath r q) := by group
      rw [heq]
      exact hs]
  rw [Finset.card_image_of_injective _ (fun a b hab => by
    exact Subtype.ext (mul_left_cancel hab))]
  rw [Finset.card_univ, Nat.card_eq_fintype_card]

omit [NeZero r] in
theorem card_wreathOrbit_mul {g : Equiv.Perm (Fin r × Fin q)} :
    (wreathOrbit hq g).card * Nat.card (wreathStab hq g) = Nat.card (Wreath r q) := by
  have hcard : (Finset.univ : Finset (Wreath r q)).card =
      ∑ y ∈ wreathOrbit hq g,
        (Finset.univ.filter (fun w : Wreath r q =>
          wreathToPermRotate r q hq w * g * (wreathToPermRotate r q hq w)⁻¹ = y)).card :=
    Finset.card_eq_sum_card_image
      (fun w : Wreath r q => wreathToPermRotate r q hq w * g * (wreathToPermRotate r q hq w)⁻¹)
      Finset.univ
  have hconst : ∀ y ∈ wreathOrbit hq g,
      (Finset.univ.filter (fun w : Wreath r q =>
        wreathToPermRotate r q hq w * g * (wreathToPermRotate r q hq w)⁻¹ = y)).card =
      Nat.card (wreathStab hq g) := by
    intro y hy
    obtain ⟨w2, -, rfl⟩ := Finset.mem_image.mp hy
    exact card_conj_fiber hq w2
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul] at hcard
  rw [← hcard, Nat.card_eq_fintype_card, Finset.card_univ]

/-- **The full numeric statement of inequality (A1)**: for `g` connected, the number of
wreath-conjugates of `g` — the size of its actual conjugacy orbit inside
`Equiv.Perm (Fin r × Fin q)` — is a multiple of `q^{r-1}(r-1)!`. -/
theorem card_wreathOrbit_dvd_mul {g : Equiv.Perm (Fin r × Fin q)} (hg : piOf g = ⊤) :
    ∃ M, (wreathOrbit hq g).card = M * (q ^ (r - 1) * (r - 1).factorial) := by
  obtain ⟨M, hM⟩ := index_wreathStab_dvd_mul hq hg
  refine ⟨M, ?_⟩
  have hmul := card_wreathOrbit_mul hq (g := g)
  have hidx := (wreathStab hq g).index_mul_card
  have hstabpos : 0 < Nat.card (wreathStab hq g) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hstabpos
  rw [hmul, ← hidx, hM]

theorem wreathOrbit_subset {g : Equiv.Perm (Fin r × Fin q)} (hg : piOf g = ⊤) :
    ↑(wreathOrbit hq g) ⊆
      {h : Equiv.Perm (Fin r × Fin q) | piOf h = ⊤ ∧ h.cycleType = g.cycleType} := by
  intro h hh
  simp only [wreathOrbit, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.mem_range] at hh
  obtain ⟨w, rfl⟩ := hh
  exact ⟨piOf_conj_eq_top hq hg w, Equiv.Perm.cycleType_conj⟩

omit [NeZero r] in
theorem mem_wreathOrbit_self (g : Equiv.Perm (Fin r × Fin q)) : g ∈ wreathOrbit hq g := by
  refine Finset.mem_image.mpr ⟨1, Finset.mem_univ 1, ?_⟩
  simp

/-- **The orbit relation**: `h1`, `h2` are wreath-conjugate. -/
def wreathRel (h1 h2 : Equiv.Perm (Fin r × Fin q)) : Prop := h2 ∈ wreathOrbit hq h1

omit [NeZero r] in
theorem wreathRel_refl (h : Equiv.Perm (Fin r × Fin q)) : wreathRel hq h h :=
  mem_wreathOrbit_self hq h

omit [NeZero r] in
theorem wreathRel_symm {h1 h2 : Equiv.Perm (Fin r × Fin q)} (h : wreathRel hq h1 h2) :
    wreathRel hq h2 h1 := by
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp h
  refine Finset.mem_image.mpr ⟨w⁻¹, Finset.mem_univ _, ?_⟩
  rw [map_inv]
  group

omit [NeZero r] in
theorem wreathRel_trans {h1 h2 h3 : Equiv.Perm (Fin r × Fin q)} (h12 : wreathRel hq h1 h2)
    (h23 : wreathRel hq h2 h3) : wreathRel hq h1 h3 := by
  obtain ⟨w1, -, rfl⟩ := Finset.mem_image.mp h12
  obtain ⟨w2, -, rfl⟩ := Finset.mem_image.mp h23
  refine Finset.mem_image.mpr ⟨w2 * w1, Finset.mem_univ _, ?_⟩
  rw [map_mul]
  group

noncomputable def wreathSetoid : Setoid (Equiv.Perm (Fin r × Fin q)) where
  r := wreathRel hq
  iseqv := ⟨wreathRel_refl hq, wreathRel_symm hq, wreathRel_trans hq⟩

noncomputable def connSameTypeFinset (g : Equiv.Perm (Fin r × Fin q)) :
    Finset (Equiv.Perm (Fin r × Fin q)) :=
  Finset.univ.filter (fun h => piOf h = ⊤ ∧ h.cycleType = g.cycleType)

theorem wreathOrbit_eq_part {g h0 : Equiv.Perm (Fin r × Fin q)}
    (hh0 : h0 ∈ connSameTypeFinset g) :
    (Finpartition.ofSetSetoid (wreathSetoid hq) (connSameTypeFinset g)).part h0 =
      wreathOrbit hq h0 := by
  apply Finset.Subset.antisymm
  · intro h hh
    rw [Finpartition.mem_part_ofSetSetoid_iff_rel] at hh
    exact hh.2.2
  · have hh0' : piOf h0 = ⊤ := (Finset.mem_filter.mp hh0).2.1
    have hsub := wreathOrbit_subset hq hh0'
    intro h hh
    rw [Finpartition.mem_part_ofSetSetoid_iff_rel]
    refine ⟨hh0, ?_, hh⟩
    have hmem := hsub hh
    simp only [Set.mem_setOf_eq] at hmem
    have hcyc0 : h0.cycleType = g.cycleType := (Finset.mem_filter.mp hh0).2.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem.1, hmem.2.trans hcyc0⟩

theorem card_connSameTypeFinset_dvd (hq : 2 ≤ q) (g : Equiv.Perm (Fin r × Fin q)) :
    ∃ M, (connSameTypeFinset g).card = M * (q ^ (r - 1) * (r - 1).factorial) := by
  have hsum := (Finpartition.ofSetSetoid (wreathSetoid hq) (connSameTypeFinset g)).sum_card_parts
  have hpartsdvd : ∀ B ∈ (Finpartition.ofSetSetoid (wreathSetoid hq)
      (connSameTypeFinset g)).parts, (q ^ (r - 1) * (r - 1).factorial) ∣ B.card := by
    intro B hB
    obtain ⟨h0, hh0B⟩ :=
      (Finpartition.ofSetSetoid (wreathSetoid hq) (connSameTypeFinset g)).nonempty_of_mem_parts hB
    have hh0S : h0 ∈ connSameTypeFinset g :=
      (Finpartition.ofSetSetoid (wreathSetoid hq) (connSameTypeFinset g)).le hB hh0B
    have hBeq : B = (Finpartition.ofSetSetoid (wreathSetoid hq)
        (connSameTypeFinset g)).part h0 :=
      ((Finpartition.ofSetSetoid (wreathSetoid hq) (connSameTypeFinset g)).part_eq_of_mem
        hB hh0B).symm
    rw [hBeq, wreathOrbit_eq_part hq hh0S]
    have hh0' : piOf h0 = ⊤ := (Finset.mem_filter.mp hh0S).2.1
    obtain ⟨M, hM⟩ := card_wreathOrbit_dvd_mul hq hh0'
    exact ⟨M, by rw [hM]; ring⟩
  obtain ⟨M, hM⟩ := Finset.dvd_sum hpartsdvd
  exact ⟨M, by rw [hsum] at hM; rw [hM]; ring⟩

/-- **Inequality (A1), fully assembled**: for every connected permutation `g`, the coefficient
of `K_r(q)` at `g`'s cycle-type monomial is divisible by `q^{r-1}(r-1)!` — the manuscript's own
`(r-1)!q^{r-1} ∣ K_r(q)`, at the level of a single coefficient. -/
theorem coeff_K_dvd (hq : 2 ≤ q) (g : Equiv.Perm (Fin r × Fin q)) (_hg : piOf g = ⊤) :
    ∃ M, MvPolynomial.coeff
        (ciExp (Fintype.card (Fin r × Fin q) - g.cycleType.sum) g.cycleType) (K r q) =
      M * (q ^ (r - 1) * (r - 1).factorial) := by
  have hcoeff : MvPolynomial.coeff
      (ciExp (Fintype.card (Fin r × Fin q) - g.cycleType.sum) g.cycleType) (K r q) =
      ((connSameTypeFinset g).card : ℤ) := by
    rw [K_eq_Gfun_top]
    unfold Gfun
    have hm2 : ∀ x ∈ g.cycleType, 2 ≤ x := fun x hx => Equiv.Perm.two_le_of_mem_cycleType hx
    have := coeff_sum_ci_eq_card_cycleType_filter
      (Finset.univ.filter (fun h : Equiv.Perm (Fin r × Fin q) => piOf h = ⊤))
      g.cycleType hm2
    rw [this]
    congr 1
    unfold connSameTypeFinset
    rw [Finset.filter_filter]
  obtain ⟨M, hM⟩ := card_connSameTypeFinset_dvd hq g
  refine ⟨M, ?_⟩
  rw [hcoeff, hM]
  push_cast
  ring

end CongruenceTheory
