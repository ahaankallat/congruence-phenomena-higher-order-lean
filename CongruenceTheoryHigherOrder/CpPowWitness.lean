import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.PrimeShiftCongruence
import CongruenceTheoryHigherOrder.WeightedOrder

/-!
**`C_p^Q`'s unique `\text{nontrivialWeight}`-degree-`0` witness.** `C_p^Q\equiv(X_1^p-X_p)^Q
\pmod p`, and every monomial of its expansion other than `X_1^{pQ}` (the "all `X_1^p`" term) has
positive `X_p`-content, hence positive `\text{nontrivialWeight}`-degree. Proved by induction on
`Q`, peeling off one factor of `C_p` at a time via `coeff_mul_X'`/`coeff_mul_monomial'`, rather
than the full binomial expansion.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`C_p^Q`'s coefficient at `X_1^{pQ}` is `1`, and this is its unique `X_p`-free monomial.** -/
theorem coeff_and_support_Cp_pow (p : ℕ) (hp : p.Prime) :
    ∀ Q : ℕ,
      MvPolynomial.coeff (Finsupp.single 1 (p * Q))
        ((MvPolynomial.map (Int.castRingHom (ZMod p)) (C p)) ^ Q) = 1 ∧
      ∀ d ∈ ((MvPolynomial.map (Int.castRingHom (ZMod p)) (C p)) ^ Q).support,
        d p = 0 → d = Finsupp.single 1 (p * Q) := by
  classical
  haveI := Fact.mk hp
  have hp2 : 2 ≤ p := hp.two_le
  have hpne1 : (1 : ℕ) ≠ p := by omega
  intro Q
  induction Q with
  | zero =>
    constructor
    · simp
    · intro d hd _
      rw [pow_zero] at hd
      have hd0 : d = 0 := by
        by_contra hne
        rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm hne)] at hd
        exact hd rfl
      simp [hd0]
  | succ Q ih =>
    obtain ⟨ihcoeff, ihsupp⟩ := ih
    have hcpQ : (MvPolynomial.map (Int.castRingHom (ZMod p)) (C p)) ^ (Q + 1) =
        (MvPolynomial.map (Int.castRingHom (ZMod p)) (C p)) ^ Q *
          MvPolynomial.map (Int.castRingHom (ZMod p)) (C p) := pow_succ _ _
    rw [hcpQ]
    set A := (MvPolynomial.map (Int.castRingHom (ZMod p)) (C p)) ^ Q with hAdef
    rw [map_C_p_eq p hp]
    have hmuldist : A * (MvPolynomial.X 1 ^ p - MvPolynomial.X p) =
        A * MvPolynomial.X 1 ^ p - A * MvPolynomial.X p := by ring
    rw [hmuldist]
    have hsingeq : Finsupp.single 1 (p * (Q + 1)) - Finsupp.single 1 p =
        (Finsupp.single 1 (p * Q) : ℕ →₀ ℕ) := by
      rw [← Finsupp.single_tsub]
      congr 1
      have hexp : p * (Q + 1) = p * Q + p := by ring
      omega
    have hle1 : (Finsupp.single 1 p : ℕ →₀ ℕ) ≤ Finsupp.single 1 (p * (Q + 1)) := by
      rw [Finsupp.single_le_single]
      nlinarith
    constructor
    · rw [MvPolynomial.coeff_sub]
      have ht1 : MvPolynomial.coeff (Finsupp.single 1 (p * (Q + 1))) (A * MvPolynomial.X 1 ^ p)
          = 1 := by
        rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial', if_pos hle1,
          mul_one, hsingeq, ihcoeff]
      have ht2 : MvPolynomial.coeff (Finsupp.single 1 (p * (Q + 1)))
          (A * MvPolynomial.X p) = 0 := by
        rw [MvPolynomial.coeff_mul_X', if_neg]
        intro hmem
        rw [Finsupp.mem_support_iff, Finsupp.single_apply, if_neg hpne1] at hmem
        exact hmem rfl
      rw [ht1, ht2]
      ring
    · intro d hd hdp0
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub] at hd
      have hd2 : MvPolynomial.coeff d (A * MvPolynomial.X p) = 0 := by
        rw [MvPolynomial.coeff_mul_X', if_neg]
        intro hmem
        rw [Finsupp.mem_support_iff] at hmem
        exact hmem hdp0
      rw [hd2, sub_zero] at hd
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial'] at hd
      by_cases hle : (Finsupp.single 1 p : ℕ →₀ ℕ) ≤ d
      · rw [if_pos hle, mul_one] at hd
        have hdmem : (d - Finsupp.single 1 p) ∈ A.support := MvPolynomial.mem_support_iff.mpr hd
        have hdp0' : (d - Finsupp.single 1 p : ℕ →₀ ℕ) p = 0 := by
          rw [Finsupp.tsub_apply, Finsupp.single_apply]
          split_ifs with hcond
          · omega
          · simpa using hdp0
        have heq := ihsupp _ hdmem hdp0'
        have hdrecon : d = (d - Finsupp.single 1 p) + Finsupp.single 1 p :=
          (tsub_add_cancel_of_le hle).symm
        rw [hdrecon, heq]
        ext j
        rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply]
        have hexp2 : p * (Q + 1) = p * Q + p := by ring
        split_ifs <;> omega
      · rw [if_neg hle] at hd
        exact absurd rfl hd

#print axioms coeff_and_support_Cp_pow

end CongruenceTheory
