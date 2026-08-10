import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.FirstPrimeLayer
import CongruenceTheoryHigherOrder.KWeightedHomogeneous

/-!
**A common `p`-power divisor of every coefficient of a product is the sum of common divisors of
the factors' own coefficients.** Needed to bound the `p`-adic valuation of every coefficient of
`\prod_{j}K_j(p)^{m_j}` in `thm:common-prime-classification`'s proof, from the per-factor bound
`prop:first-prime-layer` supplies.
-/

namespace CongruenceTheory

open MvPolynomial

/-- If `n^a` divides every coefficient of `P` and `n^b` divides every coefficient of `Q`, then
`n^{a+b}` divides every coefficient of `P*Q`. -/
theorem dvd_coeff_mul_of_dvd_coeff {P Q : MvPolynomial ℕ ℤ} {n : ℤ} {a b : ℕ}
    (hP : ∀ d, n ^ a ∣ coeff d P) (hQ : ∀ d, n ^ b ∣ coeff d Q) :
    ∀ d, n ^ (a + b) ∣ coeff d (P * Q) := by
  intro d
  rw [coeff_mul]
  apply Finset.dvd_sum
  intro x _
  rw [pow_add]
  exact mul_dvd_mul (hP x.1) (hQ x.2)

/-- If `n^a` divides every coefficient of `P`, then `n^{k\cdot a}` divides every coefficient of
`P^k`. -/
theorem dvd_coeff_pow_of_dvd_coeff {P : MvPolynomial ℕ ℤ} {n : ℤ} {a : ℕ}
    (hP : ∀ d, n ^ a ∣ coeff d P) (k : ℕ) :
    ∀ d, n ^ (k * a) ∣ coeff d (P ^ k) := by
  induction k with
  | zero => intro d; simp
  | succ k ih =>
    have := dvd_coeff_mul_of_dvd_coeff (a := k * a) (b := a) ih hP (P := P ^ k) (Q := P)
    simpa [pow_succ, Nat.succ_mul] using this

/-- **Every coefficient of `K_j(p)`, not merely those at `ciExp`-shaped monomials, is divisible
by `p^{e_p(j)}`.** Every nonzero-coefficient monomial of `K_j(p)` is automatically of `ciExp`
shape: its exponent at index `0` vanishes (`isWeightedHomogeneous_K_zero`), so subtracting off
its exponent at index `1` leaves a multiset of parts all `\ge2`. -/
theorem firstPrimeLayer_dvd_arbitrary {p j : ℕ} (hp : p.Prime) [NeZero j] (d : ℕ →₀ ℕ) :
    (p : ℤ) ^ (firstPrimeLayerExponent p j) ∣ MvPolynomial.coeff d (K j p) := by
  by_cases hd : MvPolynomial.coeff d (K j p) = 0
  · simp [hd]
  have hd0 : d 0 = 0 := by
    have hw0 := isWeightedHomogeneous_K_zero j p hd
    have heqw : (fun k : ℕ => if k = 0 then (1 : ℕ) else 0) = Pi.single 0 1 := by
      funext k; rw [Pi.single_apply]
    rwa [heqw, Finsupp.weight_single_one_apply] at hw0
  set rem : ℕ →₀ ℕ := d - Finsupp.single 1 (d 1) with hremdef
  have hremval : ∀ k, rem k = if k = 1 then 0 else d k := by
    intro k
    rw [hremdef, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hk : k = 1
    · subst hk; simp
    · rw [if_neg hk, if_neg (Ne.symm hk)]
      simp
  set m : Multiset ℕ := Multiset.toFinsupp.symm rem with hmdef
  have hcount : ∀ k, m.count k = rem k := by
    intro k
    conv_lhs => rw [hmdef, ← Multiset.toFinsupp_apply]
    rw [Multiset.toFinsupp.apply_symm_apply]
  have hdm : d = ciExp (d 1) m := by
    apply Finsupp.ext
    intro k
    rw [ciExp_apply, hcount, hremval]
    by_cases hk : k = 1
    · subst hk; simp
    · rw [if_neg hk, if_neg hk, zero_add]
  have hm2 : ∀ x ∈ m, 2 ≤ x := by
    intro x hx
    rw [← Multiset.count_pos, hcount, hremval] at hx
    split_ifs at hx with h1
    · omega
    · have hxne : d x ≠ 0 := hx.ne'
      by_cases hx0 : x = 0
      · exact absurd (hx0 ▸ hd0) hxne
      · omega
  have hdecomp : Finsupp.single 1 (d 1) + rem = d := by
    rw [hremdef]
    apply add_tsub_cancel_of_le
    rw [Finsupp.single_le_iff]
  have hmsum : (m.map (fun k : ℕ => k)).sum = Finsupp.weight (fun k : ℕ => k) rem := by
    rw [hmdef, ← weight_toFinsupp (fun k : ℕ => k), Multiset.toFinsupp.apply_symm_apply]
  have hw : Finsupp.weight (fun k : ℕ => k) d = j * p := isWeightedHomogeneous_K j p hd
  have hweq : Finsupp.weight (fun k : ℕ => k) d =
      d 1 + Finsupp.weight (fun k : ℕ => k) rem := by
    conv_lhs => rw [← hdecomp]
    rw [map_add, Finsupp.weight_single, smul_eq_mul, mul_one]
  have hd1 : d 1 = Fintype.card (Fin j × Fin p) - m.sum := by
    have hcard : Fintype.card (Fin j × Fin p) = j * p := by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have hsumeq : (m.map (fun k : ℕ => k)).sum = m.sum := by simp
    rw [hsumeq] at hmsum
    omega
  rw [hdm, hd1]
  exact firstPrimeLayer_dvd hp m hm2

/-- **The `p`-adic valuation of a coefficient of a product of `K_j(p)`'s is at least the
weighted sum of the individual `e_p(j)`'s.** For a multiset `m` of block sizes `\ge2`, every
coefficient of `\prod_{j\in m}K_j(p)` (with multiplicity) is divisible by
`p^{\sum_j e_p(j)}`. -/
theorem dvd_coeff_prod_K_of_multiset {p : ℕ} (hp : p.Prime) (lam : Multiset ℕ)
    (hlam : ∀ j ∈ lam, 1 ≤ j) (hn2 : ∀ j ∈ lam, 2 ≤ j * p) :
    ∀ d, (p : ℤ) ^ ((lam.map (firstPrimeLayerExponent p)).sum) ∣
      coeff d ((lam.map (fun j => K j p)).prod) := by
  induction lam using Multiset.induction with
  | empty => intro d; simp
  | cons j s ih =>
    intro d
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons]
    have hj1 : 1 ≤ j := hlam j (Multiset.mem_cons_self j s)
    have hjn2 : 2 ≤ j * p := hn2 j (Multiset.mem_cons_self j s)
    haveI : NeZero j := ⟨by omega⟩
    have hjdvd : ∀ d', (p : ℤ) ^ (firstPrimeLayerExponent p j) ∣ coeff d' (K j p) :=
      fun d' => firstPrimeLayer_dvd_arbitrary hp d'
    have hsdvd : ∀ d', (p : ℤ) ^ ((s.map (firstPrimeLayerExponent p)).sum) ∣
        coeff d' ((s.map (fun j => K j p)).prod) :=
      ih (fun j' hj' => hlam j' (Multiset.mem_cons_of_mem hj'))
        (fun j' hj' => hn2 j' (Multiset.mem_cons_of_mem hj'))
    exact dvd_coeff_mul_of_dvd_coeff hjdvd hsdvd d

#print axioms firstPrimeLayer_dvd_arbitrary
#print axioms dvd_coeff_prod_K_of_multiset

end CongruenceTheory
