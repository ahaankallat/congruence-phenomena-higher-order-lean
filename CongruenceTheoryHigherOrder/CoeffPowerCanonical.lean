import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.A3Final
import CongruenceTheoryHigherOrder.LegendreA3
import CongruenceTheoryHigherOrder.FirstPrimeLayer
import CongruenceTheoryHigherOrder.KWeightedHomogeneous

/-!
**The coefficient of `K_j(p)^m` at the canonical "power of the full-cycle monomial"
`m\cdot X_{jp}` is exactly `((jp-1)!)^m`.** The natural generalization of `A3Final.lean`'s
`A3_coeff_eq_factorial` (`m=1`) needed for the sharpness half of
`thm:common-prime-classification`'s valuation formula, where a minimum-weight shape
`\lambda=(1^{m_1}2^{m_2}\cdots)` contributes a product `\prod_jK_j(p)^{m_j}`, and each factor's
own canonical monomial (a power of its single full-cycle term) is the unique source of the
shape's own canonical target monomial.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **If a polynomial's only nonzero coefficient along the "pure `X_a`" line is at exponent
`1`, the same holds for its `m`-th power at exponent `m`, with the coefficient raised to the
`m`-th power.** -/
theorem coeff_single_pow_of_only_linear {P : MvPolynomial ℕ ℤ} {a : ℕ} {c : ℤ}
    (hP1 : coeff (Finsupp.single a 1) P = c)
    (hPk : ∀ k : ℕ, k ≠ 1 → coeff (Finsupp.single a k) P = 0) :
    ∀ m : ℕ, coeff (Finsupp.single a m) (P ^ m) = c ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hsingle_add : Finsupp.single a (m + 1) = Finsupp.single a m + Finsupp.single a 1 := by
      rw [← Finsupp.single_add]
    rw [pow_succ, coeff_mul]
    rw [Finset.sum_eq_single (Finsupp.single a m, Finsupp.single a 1)]
    · rw [ih, hP1, pow_succ]
    · rintro ⟨x, y⟩ hxy hne
      rw [Finset.mem_antidiagonal] at hxy
      have hxpure : ∀ k ≠ a, x k = 0 := by
        intro k hk
        have hxy0 : x k + y k = 0 := by
          have := congrArg (fun f : ℕ →₀ ℕ => f k) hxy
          simpa [Finsupp.single_apply, hk] using this
        omega
      have hypure : ∀ k ≠ a, y k = 0 := by
        intro k hk
        have hxy0 : x k + y k = 0 := by
          have := congrArg (fun f : ℕ →₀ ℕ => f k) hxy
          simpa [Finsupp.single_apply, hk] using this
        omega
      have hxeq : x = Finsupp.single a (x a) := by
        apply Finsupp.ext
        intro k
        by_cases hk : k = a
        · subst hk; simp
        · rw [hxpure k hk, Finsupp.single_apply, if_neg (Ne.symm hk)]
      have hyeq : y = Finsupp.single a (y a) := by
        apply Finsupp.ext
        intro k
        by_cases hk : k = a
        · subst hk; simp
        · rw [hypure k hk, Finsupp.single_apply, if_neg (Ne.symm hk)]
      have hsum : x a + y a = m + 1 := by
        have := congrArg (fun f : ℕ →₀ ℕ => f a) hxy
        simpa [Finsupp.single_apply] using this
      by_cases hy1 : y a = 1
      · exfalso
        apply hne
        have hxm : x a = m := by omega
        rw [hxeq, hyeq, hxm, hy1]
      · rw [hyeq, hPk (y a) hy1, mul_zero]
    · intro h
      rw [Finset.mem_antidiagonal] at h
      exact (h hsingle_add.symm).elim

/-- **The coefficient of `K_j(p)^m` at `m` copies of the full-cycle variable `X_{jp}` is
`((jp-1)!)^m`.** -/
theorem coeff_pow_eq_factorial_pow {r q : ℕ} (hn : 2 ≤ r * q) (m : ℕ) :
    coeff (Finsupp.single (r * q) m) (K r q ^ m) =
      ((Nat.factorial (r * q - 1) : ℤ)) ^ m := by
  apply coeff_single_pow_of_only_linear (a := r * q) (c := (Nat.factorial (r * q - 1) : ℤ))
  · exact A3_coeff_eq_factorial hn
  · intro k hk
    by_contra hne
    have hweight := (isWeightedHomogeneous_K r q) hne
    rw [Finsupp.weight_single, smul_eq_mul] at hweight
    apply hk
    have hrqpos : 0 < r * q := by omega
    have : k * (r * q) = 1 * (r * q) := by rw [one_mul]; exact hweight
    exact Nat.eq_of_mul_eq_mul_right hrqpos this

#print axioms coeff_single_pow_of_only_linear
#print axioms coeff_pow_eq_factorial_pow

end CongruenceTheory
