import Mathlib
import CongruenceTheory.Basic

/-!
**`C_n` never involves `X_0`.** By induction on the falling-factorial recurrence: every term
`\text{fall}(n,r)\cdot X_{r+1}\cdot C_{n-r}` only ever multiplies in `X_{r+1}` (`r+1\ge1`), so if
`C_{n-r}` is already `X_0`-free (inductively), so is the whole term, and hence the sum `C_n`.
Needed to identify `\text{nontrivialPartCount}` (which excludes both indices `0` and `1`) with
`\text{wDeg nontrivialWeight}` (which only excludes index `1`) on `\Delta_{\mathbf n}`'s own
support.
-/

namespace CongruenceTheory

open MvPolynomial Finset

theorem apply_zero_eq_zero_of_mem_support_C :
    ∀ n : ℕ, ∀ d ∈ (C n).support, d 0 = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    match n with
    | 0 =>
      intro d hd
      rw [C_zero, MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hd
      by_contra hd0
      apply hd
      rw [if_neg]
      intro heq
      apply hd0
      rw [← heq]
      simp
    | m + 1 =>
      intro d hd
      rw [C_succ, MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum] at hd
      by_contra hd0
      apply hd
      apply Finset.sum_eq_zero
      intro r _
      by_contra hterm
      apply hd0
      have hcast : (fall m r : MvPolynomial ℕ ℤ) = MvPolynomial.C (fall m r) := rfl
      rw [hcast] at hterm
      rw [MvPolynomial.coeff_C_mul] at hterm
      have hne2 : MvPolynomial.coeff d (MvPolynomial.X (r + 1) * C (m - r)) ≠ 0 :=
        fun hz => hterm (by rw [hz, mul_zero])
      have hdmem2 : d ∈ (MvPolynomial.X (r + 1) * C (m - r) :
          MvPolynomial ℕ ℤ).support := MvPolynomial.mem_support_iff.mpr hne2
      rw [MvPolynomial.support_X_mul] at hdmem2
      rw [Finset.mem_map] at hdmem2
      obtain ⟨e, he, hde⟩ := hdmem2
      have heIH : e 0 = 0 := IH (m - r) (by omega) e he
      rw [← hde]
      simp only [addLeftEmbedding_apply, Finsupp.add_apply, Finsupp.single_apply]
      rw [if_neg (by omega), heIH]

#print axioms apply_zero_eq_zero_of_mem_support_C

end CongruenceTheory
