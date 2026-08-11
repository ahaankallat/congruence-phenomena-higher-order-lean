import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.CanonicalMonomialCoefficient

/-!
**`canonTarget`'s shape sum determines the shape exactly.** Reading off `Multiset.count j lam`
from `(lam.map (canonTarget p)).sum` at position `j*p` (for `j\ge2`) or `1` (recovering
`p * count 1 lam`), for `p\ge2`. This is the injectivity fact ruling out cross-shape collisions
in `thm:common-prime-classification`'s witness-depth (`\delta_p`) sharpness argument: distinct
shapes cannot share the same canonical mixed monomial.
-/

namespace CongruenceTheory

/-- **Readout at a nontrivial position `j*p` (`j\ge2`)**: the canonical sum's value there is
exactly the shape's own multiplicity of `j`. -/
theorem canonSum_apply_mul_eq_count {p : ℕ} (hp : 2 ≤ p) (lam : Multiset ℕ) {j : ℕ} (hj : 2 ≤ j) :
    (lam.map (canonTarget p)).sum (j * p) = Multiset.count j lam := by
  induction lam using Multiset.induction with
  | empty => simp
  | cons j0 s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Finsupp.add_apply, ih, Multiset.count_cons]
    unfold canonTarget
    by_cases hj0 : j0 = 1
    · rw [if_pos hj0, Finsupp.single_apply]
      have h1ne : (1 : ℕ) ≠ j * p := by nlinarith
      rw [if_neg h1ne]
      have hjj0 : j ≠ j0 := by omega
      rw [if_neg hjj0]
      simp
    · rw [if_neg hj0, Finsupp.single_apply]
      by_cases hj0j : j0 = j
      · rw [if_pos (by rw [hj0j])]
        rw [if_pos hj0j.symm]
        omega
      · have hne : j0 * p ≠ j * p := by
          intro he
          exact hj0j (Nat.eq_of_mul_eq_mul_right (by omega) he)
        rw [if_neg hne, if_neg (Ne.symm hj0j)]
        simp

/-- **Readout at position `1`**: the canonical sum's value there is `p` times the shape's own
multiplicity of `1`. -/
theorem canonSum_apply_one_eq_mul_count {p : ℕ} (hp : 2 ≤ p) (lam : Multiset ℕ) :
    (lam.map (canonTarget p)).sum 1 = p * Multiset.count 1 lam := by
  induction lam using Multiset.induction with
  | empty => simp
  | cons j0 s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Finsupp.add_apply, ih, Multiset.count_cons]
    unfold canonTarget
    by_cases hj0 : j0 = 1
    · rw [if_pos hj0, Finsupp.single_apply, if_pos rfl, if_pos hj0.symm]
      ring
    · rw [if_neg hj0, Finsupp.single_apply]
      have hne : j0 * p ≠ 1 := by
        intro he
        rcases Nat.eq_one_of_mul_eq_one_right he with h
        omega
      rw [if_neg hne, if_neg (fun h => hj0 h.symm)]
      ring

/-- **`canonTarget`'s shape sum is injective** on shapes with all parts `\ge1`. -/
theorem canonTarget_sum_injOn {p : ℕ} (hp : 2 ≤ p) {lam lam' : Multiset ℕ}
    (hlam : ∀ j ∈ lam, 1 ≤ j) (hlam' : ∀ j ∈ lam', 1 ≤ j)
    (heq : (lam.map (canonTarget p)).sum = (lam'.map (canonTarget p)).sum) : lam = lam' := by
  apply Multiset.ext.mpr
  intro a
  rcases Nat.lt_or_ge a 2 with ha | ha
  · interval_cases a
    · rw [Multiset.count_eq_zero_of_notMem (fun h => by have := hlam 0 h; omega),
        Multiset.count_eq_zero_of_notMem (fun h => by have := hlam' 0 h; omega)]
    · have h1 : (lam.map (canonTarget p)).sum 1 = p * Multiset.count 1 lam :=
        canonSum_apply_one_eq_mul_count hp lam
      have h1' : (lam'.map (canonTarget p)).sum 1 = p * Multiset.count 1 lam' :=
        canonSum_apply_one_eq_mul_count hp lam'
      have heq1 := DFunLike.congr_fun heq 1
      rw [h1, h1'] at heq1
      exact Nat.eq_of_mul_eq_mul_left (by omega) heq1
  · have h2 : (lam.map (canonTarget p)).sum (a * p) = Multiset.count a lam :=
      canonSum_apply_mul_eq_count hp lam ha
    have h2' : (lam'.map (canonTarget p)).sum (a * p) = Multiset.count a lam' :=
      canonSum_apply_mul_eq_count hp lam' ha
    have heq2 := DFunLike.congr_fun heq (a * p)
    rw [h2, h2'] at heq2
    exact heq2

#print axioms canonSum_apply_mul_eq_count
#print axioms canonSum_apply_one_eq_mul_count
#print axioms canonTarget_sum_injOn

end CongruenceTheory
