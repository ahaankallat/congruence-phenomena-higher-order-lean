import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.ShiftCongruenceSetup
import CongruenceTheoryHigherOrder.ShiftCongruenceOrbit
import CongruenceTheoryHigherOrder.ShiftCongruenceOrbitSize
import CongruenceTheoryHigherOrder.ShiftCongruenceCentralizerSum
import CongruenceTheoryHigherOrder.ShiftCongruenceCentralizerFinal
import CongruenceTheory.PrimeValue

/-!
**`thm:complete-prime-local`(iii)'s `(A10)` shift congruence, `q=1` case.**
`\text{Cperm}(p+M)\equiv\text{Cperm}(p)\cdot\text{Cperm}(M)\pmod p`, assembled from the
centralizer-sum decomposition, the rotation sum, and Wilson's lemma (via
`Cperm_prime_decomp`, which supplies the `(p-1)!\cdot X_p` exceptional term that the rotation
sum's `(p-1)\cdot X_p` term must match mod `p`).
-/

namespace CongruenceTheory

open Equiv Equiv.Perm

variable {p M : ℕ}

/-- **Wilson's lemma, shifted form**: `p \mid ((p-1) - (p-1)!)` as integers. -/
theorem dvd_sub_one_sub_factorial (hp : p.Prime) :
    (p : ℤ) ∣ (((p - 1 : ℕ) : ℤ) - ((Nat.factorial (p - 1) : ℕ) : ℤ)) := by
  have hwilson : (p : ℤ) ∣ ((Nat.factorial (p - 1) : ℕ) : ℤ) + 1 := by
    haveI := Fact.mk hp
    have hw := ZMod.wilsons_lemma p
    have hcast : ((Nat.factorial (p - 1) + 1 : ℕ) : ZMod p) = 0 := by
      push_cast
      rw [hw]
      ring
    have h2 : p ∣ (Nat.factorial (p - 1) + 1) := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    exact_mod_cast h2
  obtain ⟨c, hc⟩ := hwilson
  refine ⟨1 - c, ?_⟩
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    have := hp.one_lt
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hp1]
  linarith [hc]

/-- **The `(A10)` shift congruence, `q=1` case**:
`\text{Cperm}(p+M)\equiv\text{Cperm}(p)\cdot\text{Cperm}(M)\pmod p`. -/
theorem Cperm_shift_cong_q1 (hp : p.Prime) :
    (p : MvPolynomial ℕ ℤ) ∣ (Cperm (p + M) - Cperm p * Cperm M) := by
  obtain ⟨Q, hQ⟩ := Cperm_eq_centralizer_sum_add_mul (M := M) hp
  rw [ci_centralizer_sum_eq hp, sum_ci_finRotate_pow hp] at hQ
  obtain ⟨Q', hQ'⟩ := Cperm_prime_decomp p hp
  obtain ⟨c, hc⟩ := dvd_sub_one_sub_factorial (p := p) hp
  refine ⟨Q - Q' * Cperm M + (MvPolynomial.C c) * MvPolynomial.X p * Cperm M, ?_⟩
  rw [hQ, hQ']
  have hcast : ((p - 1 : ℕ) : MvPolynomial ℕ ℤ) - ((Nat.factorial (p - 1) : ℕ) :
      MvPolynomial ℕ ℤ) = (p : MvPolynomial ℕ ℤ) * (MvPolynomial.C c) := by
    have := hc
    have hcast2 : (((p - 1 : ℕ) : ℤ) - ((Nat.factorial (p - 1) : ℕ) : ℤ) :
        MvPolynomial ℕ ℤ) = ((p : ℤ) * c : MvPolynomial ℕ ℤ) := by
      exact_mod_cast congrArg (Int.cast (R := MvPolynomial ℕ ℤ)) hc
    push_cast at hcast2
    simpa [MvPolynomial.C_eq_coe_nat, mul_comm] using hcast2
  linear_combination (MvPolynomial.X p * Cperm M) * hcast

#print axioms dvd_sub_one_sub_factorial
#print axioms Cperm_shift_cong_q1

end CongruenceTheory
