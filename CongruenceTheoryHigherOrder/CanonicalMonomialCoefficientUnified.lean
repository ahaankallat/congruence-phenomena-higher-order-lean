import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.KWeightedHomogeneous
import CongruenceTheoryHigherOrder.NontrivialPartCountK
import CongruenceTheoryHigherOrder.CanonicalMonomialCoefficient
import CongruenceTheoryHigherOrder.CanonicalMonomialCoefficientMain

/-!
**A single per-factor "minimum forces canonical" fact, unifying the `j=1` and `j\ge2` cases.**
-/

namespace CongruenceTheory

open MvPolynomial

/-- `K_1(p)`'s exponent at position `1` is exactly `p` whenever `nontrivialPartCount=0`. -/
theorem apply_one_eq_of_coeff_K_one_nontrivialPartCount_zero {p : ℕ} {x : ℕ →₀ ℕ}
    (hx : coeff x (K 1 p) ≠ 0) (hxmin : nontrivialPartCount x = 0) : x 1 = p := by
  have hw : Finsupp.weight (fun k : ℕ => k) x = 1 * p := isWeightedHomogeneous_K 1 p hx
  rw [one_mul, Finsupp.weight_apply, Finsupp.sum] at hw
  simp only [smul_eq_mul] at hw
  rw [nontrivialPartCount_eq_sum] at hxmin
  have hx0 : x 0 = 0 := apply_zero_eq_zero_of_coeff_K_ne_zero hx
  have hall0 : ∀ a ∈ x.support, (if 2 ≤ a then x a else 0) = 0 := by
    have h := hxmin
    rw [Finsupp.sum] at h
    exact Finset.sum_eq_zero_iff.mp h
  by_cases hxs : (1 : ℕ) ∈ x.support
  · have hsplit : x.support = insert 1 (x.support.erase 1) :=
      (Finset.insert_erase hxs).symm
    have hsum : ∑ a ∈ x.support, x a * a = x 1 * 1 + ∑ a ∈ x.support.erase 1, x a * a := by
      conv_lhs => rw [hsplit]
      rw [Finset.sum_insert (Finset.notMem_erase 1 x.support)]
    rw [hsum, mul_one] at hw
    have hrest : ∑ a ∈ x.support.erase 1, x a * a = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      obtain ⟨hane1, hamem⟩ := Finset.mem_erase.mp ha
      have ha2 : 2 ≤ a := by
        rcases Nat.lt_or_ge a 2 with h | h
        · interval_cases a
          · exact absurd hx0 (Finsupp.mem_support_iff.mp hamem)
          · exact absurd rfl hane1
        · exact h
      have := hall0 a hamem
      rw [if_pos ha2] at this
      rw [this, zero_mul]
    omega
  · have hx1 : x 1 = 0 := Finsupp.notMem_support_iff.mp hxs
    have hall : ∑ a ∈ x.support, x a * a = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      by_cases ha2 : 2 ≤ a
      · have := hall0 a ha
        rw [if_pos ha2] at this
        rw [this, zero_mul]
      · have ha1 : a = 0 ∨ a = 1 := by omega
        rcases ha1 with rfl | rfl
        · exact absurd hx0 (Finsupp.mem_support_iff.mp ha)
        · exact absurd hx1 (Finsupp.mem_support_iff.mp ha)
    omega

/-- **The unified per-factor "minimum forces canonical" fact.** -/
theorem coeff_K_min_forces_canon {p j : ℕ} (hp : 2 ≤ p) (hj : 1 ≤ j) {x : ℕ →₀ ℕ}
    (hx : coeff x (K j p) ≠ 0) (hxmin : nontrivialPartCount x = (if j = 1 then 0 else 1)) :
    canonTarget p j 1 ≤ x 1 ∧ (x 1 = canonTarget p j 1 → x = canonTarget p j) := by
  unfold canonTarget
  by_cases hj1 : j = 1
  · subst hj1
    rw [if_pos rfl] at hxmin ⊢
    have hxeq : x 1 = p := apply_one_eq_of_coeff_K_one_nontrivialPartCount_zero hx hxmin
    rw [hxeq, Finsupp.single_eq_same]
    exact ⟨le_refl p, fun _ => eq_single_of_coeff_K_one_apply_one_eq hp hx hxeq⟩
  · rw [if_neg hj1] at hxmin
    rw [if_neg hj1]
    have hj2 : 2 ≤ j := by omega
    have hjp4 : 4 ≤ j * p := Nat.mul_le_mul hj2 hp
    rw [Finsupp.single_eq_of_ne (show (1 : ℕ) ≠ j * p from by omega)]
    refine ⟨Nat.zero_le _, fun h01 => ?_⟩
    exact eq_single_of_coeff_K_apply_one_eq_zero hj2 hx h01 hxmin

#print axioms apply_one_eq_of_coeff_K_one_nontrivialPartCount_zero
#print axioms coeff_K_min_forces_canon

end CongruenceTheory
