import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.NontrivialPartCountK
import CongruenceTheoryHigherOrder.CanonicalMonomialCoefficient
import CongruenceTheoryHigherOrder.CanonicalMonomialCoefficientUnified

/-!
**The full multiset induction: a shape's canonical mixed monomial is the unique
`nontrivialPartCount`-minimal, position-`1`-minimal monomial of its block product.**
Combines `coeff_K_min_forces_canon`'s per-factor fact with `nontrivialPartCount`'s exact
additivity (and the exponent-at-`1` coordinate's own exact additivity) across the whole shape
multiset via strong induction.
-/

namespace CongruenceTheory

open MvPolynomial

theorem coeff_canonSum_prod_K_strong {p : ℕ} (hp : 2 ≤ p) :
    ∀ lam : Multiset ℕ, (∀ j ∈ lam, 1 ≤ j) →
    ∀ y : ℕ →₀ ℕ, coeff y ((lam.map (fun j => K j p)).prod) ≠ 0 →
      (lam.filter (2 ≤ ·)).card ≤ nontrivialPartCount y ∧
      (nontrivialPartCount y = (lam.filter (2 ≤ ·)).card →
        (lam.map (canonTarget p)).sum 1 ≤ y 1) ∧
      (nontrivialPartCount y = (lam.filter (2 ≤ ·)).card ∧ y 1 = (lam.map (canonTarget p)).sum 1 →
        y = (lam.map (canonTarget p)).sum) := by
  intro lam
  induction lam using Multiset.induction with
  | empty =>
    intro _ y hy
    rw [Multiset.map_zero, Multiset.prod_zero] at hy
    rw [coeff_one] at hy
    have hy0 : y = 0 := by
      by_contra hne
      exact hy (if_neg (fun h => hne h.symm))
    subst hy0
    simp
  | cons j s ih =>
    intro hlam y hy
    have hj1 : 1 ≤ j := hlam j (Multiset.mem_cons_self j s)
    have hs1 : ∀ j' ∈ s, 1 ≤ j' := fun j' hj' => hlam j' (Multiset.mem_cons_of_mem hj')
    rw [Multiset.map_cons, Multiset.prod_cons] at hy
    have hexists : ∃ x1 y1, x1 + y1 = y ∧ coeff x1 (K j p) ≠ 0 ∧
        coeff y1 ((s.map (fun j' => K j' p)).prod) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hy
      rw [coeff_mul]
      apply Finset.sum_eq_zero
      rintro ⟨x1, y1⟩ hxy
      rw [Finset.mem_antidiagonal] at hxy
      by_cases hx1 : coeff x1 (K j p) = 0
      · rw [hx1, zero_mul]
      · rw [hcon x1 y1 hxy hx1, mul_zero]
    obtain ⟨x1, y1, hxy, hx1ne, hy1ne⟩ := hexists
    obtain ⟨hbound_s, hpos1_s, huniq_s⟩ := ih hs1 y1 hy1ne
    haveI : NeZero j := ⟨by omega⟩
    have hbound_x1 : (if j = 1 then 0 else 1) ≤ nontrivialPartCount x1 := by
      by_cases hjeq : j = 1
      · simp [hjeq]
      · rw [if_neg hjeq]
        have hj2 : 2 ≤ j := by omega
        exact nontrivialPartCount_pos_of_coeff_K_ne_zero hj2 hx1ne
    have hcardeq : (Multiset.filter (2 ≤ ·) (j ::ₘ s)).card =
        (if j = 1 then 0 else 1) + (s.filter (2 ≤ ·)).card := by
      by_cases hj2 : 2 ≤ j
      · rw [Multiset.filter_cons_of_pos (p := fun x => 2 ≤ x) s hj2, Multiset.card_cons,
          if_neg (by omega : ¬ j = 1)]
        omega
      · have hjeq1 : j = 1 := by omega
        rw [Multiset.filter_cons_of_neg (p := fun x => 2 ≤ x) s hj2, if_pos hjeq1]
        omega
    have hcanoneq : (Multiset.map (canonTarget p) (j ::ₘ s)).sum =
        canonTarget p j + (s.map (canonTarget p)).sum := by
      rw [Multiset.map_cons, Multiset.sum_cons]
    have hnpsum : nontrivialPartCount y = nontrivialPartCount x1 + nontrivialPartCount y1 := by
      rw [← hxy, nontrivialPartCount_add]
    refine ⟨?_, ?_, ?_⟩
    · rw [hcardeq, hnpsum]; omega
    · intro hyeqmin
      rw [hcardeq] at hyeqmin
      have hx1min : nontrivialPartCount x1 = (if j = 1 then 0 else 1) := by omega
      have hy1min : nontrivialPartCount y1 = (s.filter (2 ≤ ·)).card := by omega
      have hpos1s' := hpos1_s hy1min
      have hxbound := (coeff_K_min_forces_canon hp hj1 hx1ne hx1min).1
      rw [hcanoneq, Finsupp.add_apply, ← hxy, Finsupp.add_apply]
      omega
    · rintro ⟨hyeqmin, hy1eq⟩
      rw [hcardeq] at hyeqmin
      have hx1min : nontrivialPartCount x1 = (if j = 1 then 0 else 1) := by omega
      have hy1min : nontrivialPartCount y1 = (s.filter (2 ≤ ·)).card := by omega
      have hpos1s' := hpos1_s hy1min
      have hxforce := coeff_K_min_forces_canon hp hj1 hx1ne hx1min
      have hxbound := hxforce.1
      rw [hcanoneq, Finsupp.add_apply] at hy1eq
      rw [← hxy, Finsupp.add_apply] at hy1eq
      have hx1eq : x1 1 = canonTarget p j 1 := by omega
      have hy1eq' : y1 1 = (s.map (canonTarget p)).sum 1 := by omega
      have hx1canon : x1 = canonTarget p j := hxforce.2 hx1eq
      have hy1canon : y1 = (s.map (canonTarget p)).sum := huniq_s ⟨hy1min, hy1eq'⟩
      rw [hcanoneq, ← hxy, hx1canon, hy1canon]

#print axioms coeff_canonSum_prod_K_strong

end CongruenceTheory
