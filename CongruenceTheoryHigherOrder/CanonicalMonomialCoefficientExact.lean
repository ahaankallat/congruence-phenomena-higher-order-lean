import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.NontrivialPartCountK
import CongruenceTheoryHigherOrder.CanonicalMonomialCoefficient
import CongruenceTheoryHigherOrder.CanonicalMonomialCoefficientUnified
import CongruenceTheoryHigherOrder.CanonicalMonomialCoefficientFinal
import CongruenceTheoryHigherOrder.A3Final
import CongruenceTheoryHigherOrder.KOneAllFixedCoeff

/-!
**The exact coefficient of a shape's block product at its own canonical monomial.** Combines
`coeff_canonSum_prod_K_strong`'s forced-uniqueness with the per-factor exact coefficient values
(`coeff_single_one_K_one` for `j=1`, `A3_coeff_eq_factorial` for `j\ge2`) to compute
`coeff (\sum_j \text{canonTarget}(p,j)) (\prod_j K_j(p)) = \prod_j \text{canonCoeff}(p,j)` exactly,
via `coeff_mul_eq_of_forced_unique` chained across the shape multiset.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **A single canonical target's own `nontrivialPartCount`**: `0` for `j=1`, `1` for `j\ge2`. -/
theorem nontrivialPartCount_canonTarget {p : ℕ} (hp : 2 ≤ p) {j : ℕ} (hj1 : 1 ≤ j) :
    nontrivialPartCount (canonTarget p j) = (if j = 1 then 0 else 1) := by
  unfold canonTarget
  by_cases hj : j = 1
  · rw [if_pos hj, if_pos hj, nontrivialPartCount_eq_sum, Finsupp.sum_single_index (by simp)]
    norm_num
  · rw [if_neg hj, if_neg hj, nontrivialPartCount_eq_sum, Finsupp.sum_single_index (by simp)]
    have hj2 : 2 ≤ j := by omega
    rw [if_pos (show 2 ≤ j * p from by nlinarith)]

/-- **The canonical monomial of a shape achieves exactly the minimal `nontrivialPartCount`.** -/
theorem nontrivialPartCount_canonSum_eq_card {p : ℕ} (hp : 2 ≤ p) :
    ∀ lam : Multiset ℕ, (∀ j ∈ lam, 1 ≤ j) →
      nontrivialPartCount ((lam.map (canonTarget p)).sum) = (lam.filter (2 ≤ ·)).card := by
  intro lam
  induction lam using Multiset.induction with
  | empty => intro _; unfold nontrivialPartCount; simp
  | cons j0 s ih =>
    intro hlam
    have hj01 : 1 ≤ j0 := hlam j0 (Multiset.mem_cons_self j0 s)
    have hs1 : ∀ j' ∈ s, 1 ≤ j' := fun j' hj' => hlam j' (Multiset.mem_cons_of_mem hj')
    rw [Multiset.map_cons, Multiset.sum_cons, nontrivialPartCount_add,
      nontrivialPartCount_canonTarget hp hj01, ih hs1]
    by_cases hj2 : 2 ≤ j0
    · rw [Multiset.filter_cons_of_pos (p := fun x => 2 ≤ x) s hj2, Multiset.card_cons,
        if_neg (by omega : ¬ j0 = 1)]
      omega
    · have hjeq1 : j0 = 1 := by omega
      rw [Multiset.filter_cons_of_neg (p := fun x => 2 ≤ x) s hj2, if_pos hjeq1]
      omega

/-- **Forced uniqueness of the canonical decomposition**: any way of splitting the shape `j::s`'s
own canonical target into a `K_j(p)`-monomial plus a rest-block monomial, both with nonzero
coefficient, must be the canonical split. -/
theorem forced_unique_canon {p : ℕ} (hp : 2 ≤ p) {j : ℕ} (hj1 : 1 ≤ j) {s : Multiset ℕ}
    (hs1 : ∀ j' ∈ s, 1 ≤ j') :
    ∀ x y : ℕ →₀ ℕ, x + y = canonTarget p j + (s.map (canonTarget p)).sum →
      coeff x (K j p) ≠ 0 → coeff y ((s.map (fun j' => K j' p)).prod) ≠ 0 →
      x = canonTarget p j ∧ y = (s.map (canonTarget p)).sum := by
  intro x y hxy hxne hyne
  obtain ⟨hbound_s, hpos1_s, huniq_s⟩ := coeff_canonSum_prod_K_strong hp s hs1 y hyne
  haveI : NeZero j := ⟨by omega⟩
  have hbound_x : (if j = 1 then 0 else 1) ≤ nontrivialPartCount x := by
    by_cases hjeq : j = 1
    · simp [hjeq]
    · rw [if_neg hjeq]
      have hj2 : 2 ≤ j := by omega
      exact nontrivialPartCount_pos_of_coeff_K_ne_zero hj2 hxne
  have hcardeq : (Multiset.filter (2 ≤ ·) (j ::ₘ s)).card =
      (if j = 1 then 0 else 1) + (s.filter (2 ≤ ·)).card := by
    by_cases hj2 : 2 ≤ j
    · rw [Multiset.filter_cons_of_pos (p := fun x => 2 ≤ x) s hj2, Multiset.card_cons,
        if_neg (by omega : ¬ j = 1)]
      omega
    · have hjeq1 : j = 1 := by omega
      rw [Multiset.filter_cons_of_neg (p := fun x => 2 ≤ x) s hj2, if_pos hjeq1]
      omega
  have hnpsum : nontrivialPartCount (x + y) = nontrivialPartCount x + nontrivialPartCount y :=
    nontrivialPartCount_add x y
  have hstep : (Multiset.map (canonTarget p) (j ::ₘ s)).sum =
      canonTarget p j + (Multiset.map (canonTarget p) s).sum := by
    rw [Multiset.map_cons, Multiset.sum_cons]
  have hyeqtarget : x + y = (Multiset.map (canonTarget p) (j ::ₘ s)).sum := by
    rw [hxy, hstep]
  have hjs1 : ∀ j' ∈ (j ::ₘ s), 1 ≤ j' := by
    intro j' hj'
    rcases Multiset.mem_cons.mp hj' with rfl | hj'
    · exact hj1
    · exact hs1 j' hj'
  have htarget : nontrivialPartCount (x + y) = (Multiset.filter (2 ≤ ·) (j ::ₘ s)).card := by
    rw [hyeqtarget, nontrivialPartCount_canonSum_eq_card hp (j ::ₘ s) hjs1]
  have hxmin : nontrivialPartCount x = (if j = 1 then 0 else 1) := by omega
  have hymin : nontrivialPartCount y = (s.filter (2 ≤ ·)).card := by omega
  have hxforce := coeff_K_min_forces_canon hp hj1 hxne hxmin
  have hxbound := hxforce.1
  have hy1 := hpos1_s hymin
  have hxy1 : x 1 + y 1 = (Multiset.map (canonTarget p) (j ::ₘ s)).sum 1 := by
    rw [← Finsupp.add_apply, hyeqtarget]
  rw [hstep, Finsupp.add_apply] at hxy1
  have hx1eq : x 1 = canonTarget p j 1 := by omega
  have hy1eq : y 1 = (s.map (canonTarget p)).sum 1 := by omega
  exact ⟨hxforce.2 hx1eq, huniq_s ⟨hymin, hy1eq⟩⟩

/-- **The exact coefficient of a shape's block product at its own canonical monomial.** -/
theorem coeff_canonSum_prod_K_eq {p : ℕ} (hp : 2 ≤ p) :
    ∀ lam : Multiset ℕ, (∀ j ∈ lam, 1 ≤ j) →
      coeff ((lam.map (canonTarget p)).sum) ((lam.map (fun j => K j p)).prod) =
        (lam.map (canonCoeff p)).prod := by
  intro lam
  induction lam using Multiset.induction with
  | empty => simp [coeff_one]
  | cons j s ih =>
    intro hlam
    have hj1 : 1 ≤ j := hlam j (Multiset.mem_cons_self j s)
    have hs1 : ∀ j' ∈ s, 1 ≤ j' := fun j' hj' => hlam j' (Multiset.mem_cons_of_mem hj')
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
    rw [coeff_mul_eq_of_forced_unique (forced_unique_canon hp hj1 hs1)]
    rw [ih hs1]
    congr 1
    unfold canonCoeff
    by_cases hjeq : j = 1
    · subst hjeq
      rw [if_pos rfl]
      unfold canonTarget
      rw [if_pos rfl, coeff_single_one_K_one]
    · rw [if_neg hjeq]
      unfold canonTarget
      rw [if_neg hjeq]
      have hj2 : 2 ≤ j := by omega
      have hjp2 : 2 ≤ j * p := by nlinarith
      exact A3_coeff_eq_factorial hjp2

#print axioms nontrivialPartCount_canonTarget
#print axioms nontrivialPartCount_canonSum_eq_card
#print axioms forced_unique_canon
#print axioms coeff_canonSum_prod_K_eq

end CongruenceTheory
