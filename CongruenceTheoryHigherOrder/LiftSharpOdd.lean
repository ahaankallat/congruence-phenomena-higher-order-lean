import Mathlib
import CongruenceTheoryHigherOrder.KWeightedHomogeneous
import CongruenceTheoryHigherOrder.LiftAllPrimes
import CongruenceTheory.CoeffExtraction
import CongruenceTheory.CpermEqC
import CongruenceTheory.PrimeWitness
import CongruenceTheory.OptimalDivisorC


/-!
**Sharpness of the lift** (main paper, Theorem `thm:strong-all-primes` "Lifting at every prime",
Remark `rem:lift-sharp`, and Proposition `prop:lift-sharp-odd` in Appendix "Sharpness of the lift
for odd primes").

* `lift_sharp_odd` is Proposition `prop:lift-sharp-odd`.  For an odd prime `p`, `k > 0`, `p ∣ k`
  and `s = v_p(k)`, the coefficient of `X_p^(k-2) X_{2p}` in `C_{pk} - C_k^p` is divisible by
  `p^(2s)` and not by `p^(2s+1)` (valuation exactly `2s`).  The monomial is written
  `Finsupp.single p (k-2) + Finsupp.single (2*p) 1`.
* `lift_sharp_two` and `lift_sharp_two_not_dvd` are the `p = 2` case of Remark `rem:lift-sharp`:
  the coefficient of `X_1^(2k-4) X_4` in `C_{2k} - C_k^2` has 2-adic valuation exactly `2s - 1`
  (`s = v_2(k)`), which is the exact content `2^(2s-1)` of Theorem `thm:optimal-divisor`
  (obtained from `prime_witness`).

*Proof of the odd case (formalized).*  With `U_n = (pn)!/(p^n n!)` (`Ufun`, the product of the
integers up to `pn` prime to `p`), the coefficient of `X_p^(n-2) X_{2p}` in `C_{pn}` is
`p U_n C(n,2)` (`coeff_two_p_C'`) and that of `X_p^n` is `U_n` (`coeff_single_C`), both from
the cycle-type count `Equiv.Perm.card_of_cycleType`.  The coefficient in `C_k^p`, `k = pq`, is
computed by the specialization `X_p ↦ Y`, `X_{2p} ↦ ε` into the dual numbers `ℤ[Y][ε]`
(`spec_eq_of_weighted`, `coeff_pow_two_p`), which gives `p U_q^(p-1) · p U_q C(q,2)`.  Gauss's
theorem that the product of the units modulo `p^s` is `-1` for odd `p` (`prod_units_eq_neg_one`)
gives `U_k ≡ U_q^p (mod p^s)` (`Ufun_cong`), and the paper's identity
`2 (c_1 - c_2) = p^2 q E` with `E = (k-1) U_k - (q-1) U_q^p` finishes the valuation count
(`sharp_arith`).
-/

namespace CongruenceTheory.LiftSharp

open scoped Nat

open MvPolynomial

/-- Dual numbers over `ℤ[Y]`. -/
abbrev DN := TrivSqZeroExt (Polynomial ℤ) (Polynomial ℤ)

/-- `X_p ↦ Y`, `X_{2p} ↦ ε`, all other variables to `0`. -/
noncomputable def specF (p : ℕ) : ℕ → DN := fun j =>
  if j = p then TrivSqZeroExt.inl Polynomial.X
  else if j = 2 * p then TrivSqZeroExt.inr 1 else 0

noncomputable def spec (p : ℕ) : MvPolynomial ℕ ℤ →ₐ[ℤ] DN := MvPolynomial.aeval (specF p)

lemma inr_one_sq : (TrivSqZeroExt.inr (1 : Polynomial ℤ) : DN) ^ 2 = 0 := by
  rw [sq]; ext <;> simp

lemma inr_one_pow_ge {b : ℕ} (hb : 2 ≤ b) : (TrivSqZeroExt.inr (1 : Polynomial ℤ) : DN) ^ b = 0 := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hb
  rw [pow_add, inr_one_sq, zero_mul]

lemma spec_monomial_other {p : ℕ} (d : ℕ →₀ ℕ) {j : ℕ} (hj : j ∈ d.support) (h1 : j ≠ p)
    (h2 : j ≠ 2 * p) : spec p (monomial d 1) = 0 := by
  rw [spec, aeval_monomial, Finsupp.prod]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero hj
  have : specF p j = 0 := by simp [specF, h1, h2]
  rw [this]
  exact zero_pow (Finsupp.mem_support_iff.mp hj)

lemma spec_monomial_two {p : ℕ} (hp : 0 < p) (a b : ℕ) :
    spec p (monomial (Finsupp.single p a + Finsupp.single (2 * p) b) 1) =
      (TrivSqZeroExt.inl (Polynomial.X ^ a) : DN) * (TrivSqZeroExt.inr (1 : Polynomial ℤ)) ^ b := by
  rw [spec, aeval_monomial, map_one, one_mul]
  have hne : p ≠ 2 * p := by omega
  rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add])]
  rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]
  have h1 : specF p p = TrivSqZeroExt.inl Polynomial.X := by simp [specF]
  have h2 : specF p (2 * p) = TrivSqZeroExt.inr 1 := by simp [specF, hne.symm]
  rw [h1, h2, ← TrivSqZeroExt.inl_pow]


section extraction
variable {p Q : ℕ}

lemma eq_single_add (hp : 0 < p) (d : ℕ →₀ ℕ) (h : ∀ j ∈ d.support, j = p ∨ j = 2 * p) :
    d = Finsupp.single p (d p) + Finsupp.single (2 * p) (d (2 * p)) := by
  have hne : p ≠ 2 * p := by omega
  have hne' : 2 * p ≠ p := by omega
  ext j
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  by_cases h1 : j = p
  · subst h1; simp [hne, hne']
  · by_cases h2 : j = 2 * p
    · subst h2; simp [hne, hne']
    · have : d j = 0 := by
        by_contra hc
        rcases h j (Finsupp.mem_support_iff.mpr hc) with h3 | h3 <;> contradiction
      have e1 : p ≠ j := fun h => h1 h.symm
      have e2 : 2 * p ≠ j := fun h => h2 h.symm
      simp [this, e1, e2]

lemma weight_two (hp : 0 < p) (a b : ℕ) :
    Finsupp.weight (fun k : ℕ => k) (Finsupp.single p a + Finsupp.single (2 * p) b) =
      a * p + b * (2 * p) := by
  rw [map_add, Finsupp.weight_single, Finsupp.weight_single]
  simp

lemma spec_term (hp : 0 < p) {P : MvPolynomial ℕ ℤ}
    (hP : IsWeightedHomogeneous (fun k : ℕ => k) P (p * Q)) (d : ℕ →₀ ℕ)
    (hd : coeff d P ≠ 0) :
    coeff d P • spec p (monomial d 1) =
      (if d = Finsupp.single p Q then
          coeff (Finsupp.single p Q) P • (TrivSqZeroExt.inl (Polynomial.X ^ Q) : DN) else 0) +
      (if d = Finsupp.single p (Q - 2) + Finsupp.single (2 * p) 1 then
          coeff (Finsupp.single p (Q - 2) + Finsupp.single (2 * p) 1) P •
            (TrivSqZeroExt.inr (Polynomial.X ^ (Q - 2)) : DN) else 0) := by
  have hne : p ≠ 2 * p := by omega
  by_cases hs : ∃ j ∈ d.support, j ≠ p ∧ j ≠ 2 * p
  · obtain ⟨j, hj, h1, h2⟩ := hs
    rw [spec_monomial_other d hj h1 h2, zsmul_zero]
    have hd0 : d ≠ Finsupp.single p Q := by
      rintro rfl
      have := Finsupp.mem_support_iff.mp hj
      simp [Finsupp.single_apply, h1.symm] at this
    have hd1 : d ≠ Finsupp.single p (Q - 2) + Finsupp.single (2 * p) 1 := by
      rintro rfl
      have := Finsupp.mem_support_iff.mp hj
      simp [Finsupp.single_apply, h1.symm, h2.symm] at this
    rw [if_neg hd0, if_neg hd1, add_zero]
  · push Not at hs
    have hs' : ∀ j ∈ d.support, j = p ∨ j = 2 * p := by
      intro j hj
      by_cases h1 : j = p
      · exact Or.inl h1
      · exact Or.inr (hs j hj h1)
    have hdeq := eq_single_add hp d hs'
    have hw := hP hd
    rw [hdeq, weight_two hp] at hw
    set a := d p
    set b := d (2 * p)
    rw [hdeq, spec_monomial_two hp]
    rcases Nat.lt_or_ge b 2 with hb | hb
    · interval_cases b
      · have ha : a = Q := by nlinarith
        subst ha
        simp only [pow_zero, mul_one, Finsupp.single_zero, add_zero, ite_true]
        have : (Finsupp.single p a : ℕ →₀ ℕ) ≠ Finsupp.single p (a - 2) + Finsupp.single (2 * p) 1 := by
          intro h
          have := congrArg (fun f => f (2 * p)) h
          simp [Finsupp.single_apply, hne.symm] at this
        rw [if_neg this, add_zero]
      · have ha : a + 2 = Q := by nlinarith
        have ha' : a = Q - 2 := by omega
        rw [ha']
        simp only [pow_one, mul_one]
        have : (Finsupp.single p (Q - 2) + Finsupp.single (2 * p) 1 : ℕ →₀ ℕ) ≠ Finsupp.single p Q := by
          intro h
          have := congrArg (fun f => f (2 * p)) h
          simp [Finsupp.single_apply, hne.symm] at this
        have hmul : (TrivSqZeroExt.inl (Polynomial.X ^ (Q - 2)) * TrivSqZeroExt.inr (1 : Polynomial ℤ) : DN) =
            TrivSqZeroExt.inr (Polynomial.X ^ (Q - 2)) := by ext <;> simp
        rw [hmul, if_neg this, zero_add]
        simp
    · rw [inr_one_pow_ge hb, mul_zero, zsmul_zero]
      have hd0 : (Finsupp.single p a + Finsupp.single (2 * p) b : ℕ →₀ ℕ) ≠ Finsupp.single p Q := by
        intro h
        have := congrArg (fun f => f (2 * p)) h
        simp [Finsupp.single_apply, hne.symm] at this
        omega
      have hd1 : (Finsupp.single p a + Finsupp.single (2 * p) b : ℕ →₀ ℕ) ≠
          Finsupp.single p (Q - 2) + Finsupp.single (2 * p) 1 := by
        intro h
        have := congrArg (fun f => f (2 * p)) h
        simp [Finsupp.single_apply, hne.symm] at this
        omega
      rw [if_neg hd0, if_neg hd1, add_zero]

/-- **Extraction.**  For `P` weighted homogeneous of degree `p Q` (with `X_j` of weight `j`),
the specialization `X_p ↦ Y`, `X_{2p} ↦ ε` only sees the coefficients of `X_p^Q` and
`X_p^{Q-2} X_{2p}`. -/
theorem spec_eq_of_weighted (hp : 0 < p) {P : MvPolynomial ℕ ℤ}
    (hP : IsWeightedHomogeneous (fun k : ℕ => k) P (p * Q)) :
    spec p P = coeff (Finsupp.single p Q) P • (TrivSqZeroExt.inl (Polynomial.X ^ Q) : DN) +
      coeff (Finsupp.single p (Q - 2) + Finsupp.single (2 * p) 1) P •
        (TrivSqZeroExt.inr (Polynomial.X ^ (Q - 2)) : DN) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  have h1 : ∀ d ∈ P.support, spec p (monomial d (coeff d P)) =
      (if d = Finsupp.single p Q then
          coeff (Finsupp.single p Q) P • (TrivSqZeroExt.inl (Polynomial.X ^ Q) : DN) else 0) +
      (if d = Finsupp.single p (Q - 2) + Finsupp.single (2 * p) 1 then
          coeff (Finsupp.single p (Q - 2) + Finsupp.single (2 * p) 1) P •
            (TrivSqZeroExt.inr (Polynomial.X ^ (Q - 2)) : DN) else 0) := by
    intro d hd
    rw [← spec_term hp hP d (mem_support_iff.mp hd)]
    rw [show (monomial (R := ℤ) d (coeff d P) : MvPolynomial ℕ ℤ) = (MvPolynomial.C (coeff d P) : MvPolynomial ℕ ℤ) * monomial d (1 : ℤ) by
      rw [C_mul_monomial, mul_one], map_mul, ← algebraMap_eq, AlgHom.commutes, ← Algebra.smul_def]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  congr 1
  · split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, zero_smul]
  · split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, zero_smul]

end extraction

/-! ### The unit part of `(pn)!` -/

/-- `U_n = (pn)!/(p^n n!)` as the product of the integers up to `pn` that are prime to `p`. -/
def Ufun (p n : ℕ) : ℕ := ∏ i ∈ Finset.range (p * n), (if p ∣ i + 1 then 1 else i + 1)

lemma prod_block (p n : ℕ) (hp : 0 < p) :
    ∏ x ∈ Finset.range p, (p * n + x + 1) =
      (p * (n + 1)) * ∏ x ∈ Finset.range p, (if p ∣ p * n + x + 1 then 1 else p * n + x + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  rw [Finset.prod_range_succ, Finset.prod_range_succ]
  have hlast : (r + 1) ∣ (r + 1) * n + r + 1 := ⟨n + 1, by ring⟩
  rw [if_pos hlast]
  have hrest : ∏ x ∈ Finset.range r, ((r + 1) * n + x + 1) =
      ∏ x ∈ Finset.range r, (if (r + 1) ∣ (r + 1) * n + x + 1 then 1 else (r + 1) * n + x + 1) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hx' := Finset.mem_range.mp hx
    rw [if_neg]
    intro hd
    have : (r + 1) ∣ x + 1 := by
      have h2 : (r + 1) * n + x + 1 = (r + 1) * n + (x + 1) := by ring
      rw [h2] at hd
      exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp hd
    have := Nat.le_of_dvd (by omega) this
    omega
  rw [hrest]
  have : (r + 1) * n + r + 1 = (r + 1) * (n + 1) := by ring
  rw [this]
  ring

theorem factorial_eq_mul_Ufun (p : ℕ) (hp : 0 < p) (n : ℕ) :
    (p * n)! = p ^ n * n ! * Ufun p n := by
  induction n with
  | zero => simp [Ufun]
  | succ n ih =>
    have e1 : (p * (n + 1))! = (p * n)! * ∏ x ∈ Finset.range p, (p * n + x + 1) := by
      rw [← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_add_one_eq_factorial,
        show p * (n + 1) = p * n + p by ring, Finset.prod_range_add]
    have e2 : Ufun p (n + 1) = Ufun p n *
        ∏ x ∈ Finset.range p, (if p ∣ p * n + x + 1 then 1 else p * n + x + 1) := by
      unfold Ufun
      rw [show p * (n + 1) = p * n + p by ring, Finset.prod_range_add]
    rw [e1, prod_block p n hp, e2, ih, Nat.factorial_succ]
    ring

lemma Ufun_not_dvd {p : ℕ} (hp : p.Prime) (n : ℕ) : ¬ p ∣ Ufun p n := by
  unfold Ufun
  intro h
  rw [Prime.dvd_finsetProd_iff hp.prime] at h
  obtain ⟨i, _, hi⟩ := h
  split_ifs at hi with hd
  · exact hp.one_lt.ne' (Nat.dvd_one.mp hi)
  · exact hd hi

/-! ### Coefficients of `C_{pn}` -/

lemma ciExp_replicate {p : ℕ} (hp : 2 ≤ p) (q : ℕ) :
    ciExp 0 (Multiset.replicate q p) = Finsupp.single p q := by
  ext j
  rw [ciExp_apply, Multiset.count_replicate]
  simp only [Finsupp.single_apply]
  split_ifs <;> omega

lemma ciExp_two_p {p : ℕ} (hp : 2 ≤ p) (q : ℕ) :
    ciExp 0 ((2 * p) ::ₘ Multiset.replicate q p) =
      Finsupp.single p q + Finsupp.single (2 * p) 1 := by
  ext j
  rw [ciExp_apply, Multiset.count_cons, Multiset.count_replicate]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

/-- `[X_p^n] C_{pn} = U_n`. -/
theorem coeff_single_C {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    coeff (Finsupp.single p n) (C (p * n)) = (Ufun p n : ℤ) := by
  have hp0 : 0 < p := by omega
  rw [← Cperm_eq_C, ← ciExp_replicate hp n]
  have hsum : (Multiset.replicate n p).sum = p * n := by simp [mul_comm]
  have := coeff_Cperm_eq_card_cycleType (p * n) (Multiset.replicate n p) (by
    intro x hx; rw [Multiset.eq_of_mem_replicate hx]; exact hp)
  rw [hsum, Nat.sub_self] at this
  rw [this, Equiv.Perm.card_of_cycleType]
  simp only [Fintype.card_fin, hsum, Nat.sub_self, Nat.factorial_zero, one_mul]
  rw [if_pos ⟨le_refl _, fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; exact hp⟩]
  by_cases hn : n = 0
  · subst hn; simp [Ufun]
  · rw [Multiset.toFinset_replicate, if_neg hn, Finset.prod_singleton, Multiset.count_replicate_self,
      Multiset.prod_replicate]
    have hfe := factorial_eq_mul_Ufun p hp0 n
    have : (p * n)! / (p ^ n * n !) = Ufun p n := by
      rw [hfe]; exact Nat.mul_div_cancel_left _ (by positivity)
    exact_mod_cast this

/-- `[X_p^{n-2} X_{2p}] C_{pn} = p U_n C(n,2)`. -/
theorem coeff_two_p_C {p : ℕ} (hp : 2 ≤ p) (n : ℕ) (hn : 2 ≤ n) :
    coeff (Finsupp.single p (n - 2) + Finsupp.single (2 * p) 1) (C (p * n)) =
      (p : ℤ) * Ufun p n * (n.choose 2 : ℕ) := by
  have hp0 : 0 < p := by omega
  rw [← Cperm_eq_C, ← ciExp_two_p hp (n - 2)]
  set m : Multiset ℕ := (2 * p) ::ₘ Multiset.replicate (n - 2) p with hm
  have hsum : m.sum = p * n := by
    rw [hm, Multiset.sum_cons, Multiset.sum_replicate]
    simp only [smul_eq_mul]
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [Nat.add_sub_cancel_left]
    ring
  have hm2 : ∀ x ∈ m, 2 ≤ x := by
    intro x hx
    rw [hm, Multiset.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · rw [Multiset.eq_of_mem_replicate hx]; exact hp
  have := coeff_Cperm_eq_card_cycleType (p * n) m hm2
  rw [hsum, Nat.sub_self] at this
  rw [this, Equiv.Perm.card_of_cycleType]
  simp only [Fintype.card_fin, hsum, Nat.sub_self, Nat.factorial_zero, one_mul]
  rw [if_pos ⟨le_refl _, hm2⟩]
  have hprod : m.prod = 2 * p * p ^ (n - 2) := by
    rw [hm, Multiset.prod_cons, Multiset.prod_replicate]
  have hne : p ≠ 2 * p := by omega
  have hfin : ∏ x ∈ m.toFinset, (Multiset.count x m)! = (n - 2)! := by
    have hsub : m.toFinset ⊆ {p, 2 * p} := by
      intro x hx
      rw [Multiset.mem_toFinset, hm, Multiset.mem_cons] at hx
      rcases hx with rfl | hx
      · simp
      · rw [Multiset.eq_of_mem_replicate hx]; simp
    rw [Finset.prod_subset hsub (by
      intro x hx hx'
      rw [Multiset.mem_toFinset] at hx'
      rw [Multiset.count_eq_zero_of_notMem hx']; simp)]
    rw [Finset.prod_pair hne]
    have c1 : Multiset.count p m = n - 2 := by
      rw [hm, Multiset.count_cons, Multiset.count_replicate]; simp [hne, hne.symm]
    have c2 : Multiset.count (2 * p) m = 1 := by
      rw [hm, Multiset.count_cons, Multiset.count_replicate]; simp [hne, hne.symm]
    rw [c1, c2]; simp
  rw [hprod, hfin]
  have hfe := factorial_eq_mul_Ufun p hp0 n
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [Nat.add_sub_cancel_left] at *
  have key : (p * (2 + c))! / (2 * p * p ^ c * c !) = p * Ufun p (2 + c) * (2 + c).choose 2 := by
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    rw [hfe]
    have h2 : (2 + c)! = (2 + c) * (1 + c) * c ! := by
      rw [show 2 + c = (c + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]; ring
    have h3 : 2 * (2 + c).choose 2 = (2 + c) * (1 + c) := by
      rw [show 2 + c = (c + 1) + 1 by ring, Nat.choose_two_right]
      simp only [Nat.add_sub_cancel]
      have : (c + 1 + 1) * (c + 1) % 2 = 0 := by
        rcases Nat.even_or_odd c with ⟨t, ht⟩ | ⟨t, ht⟩ <;> subst ht <;> ring_nf <;> omega
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero this)]
      ring
    rw [h2, pow_add]
    have : (2 + c).choose 2 * 2 = (2 + c) * (1 + c) := by linarith
    calc p ^ 2 * p ^ c * ((2 + c) * (1 + c) * c !) * Ufun p (2 + c)
        = p * Ufun p (2 + c) * ((2 + c) * (1 + c)) * (p * p ^ c * c !) := by ring
      _ = p * Ufun p (2 + c) * ((2 + c).choose 2 * 2) * (p * p ^ c * c !) := by rw [this]
      _ = _ := by ring
  exact_mod_cast key

/-! ### Powers in the dual numbers, and the coefficient in `C_k^p` -/

lemma isWeightedHomogeneous_C (n : ℕ) :
    IsWeightedHomogeneous (fun k : ℕ => k) (C n) n := by
  rw [← Cperm_eq_C, Cperm]
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have := fun g : Equiv.Perm (Fin n) => isWeightedHomogeneous_ci g
  simp only [hcard] at this
  exact IsWeightedHomogeneous.sum _ _ _ (fun g _ => this g)

lemma dn_fst_pow (x : DN) (n : ℕ) : (x ^ n).fst = x.fst ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, TrivSqZeroExt.fst_mul, ih, pow_succ]

lemma dn_snd_pow_succ (x : DN) (n : ℕ) :
    (x ^ (n + 1)).snd = ((n + 1 : ℕ) : Polynomial ℤ) * (x.fst ^ n * x.snd) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, TrivSqZeroExt.snd_mul, ih, dn_fst_pow]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    push_cast
    ring

lemma dn_fst_zsmul (c : ℤ) (x : DN) : (c • x).fst = c • x.fst := by
  induction c using Int.induction_on with
  | zero => simp
  | succ i ih => rw [add_smul, one_smul, TrivSqZeroExt.fst_add, ih, add_smul, one_smul]
  | pred i ih => rw [sub_smul, one_smul, TrivSqZeroExt.fst_sub, ih, sub_smul, one_smul]

lemma dn_snd_zsmul (c : ℤ) (x : DN) : (c • x).snd = c • x.snd := by
  induction c using Int.induction_on with
  | zero => simp
  | succ i ih => rw [add_smul, one_smul, TrivSqZeroExt.snd_add, ih, add_smul, one_smul]
  | pred i ih => rw [sub_smul, one_smul, TrivSqZeroExt.snd_sub, ih, sub_smul, one_smul]

/-- The coefficient of `X_p^{pq-2} X_{2p}` in `C_{pq}^p` in terms of the two coefficients of
`C_{pq}` that matter. -/
theorem coeff_pow_two_p {p : ℕ} (hp : 2 ≤ p) {q : ℕ} (hq : 1 ≤ q) :
    coeff (Finsupp.single p (p * q - 2) + Finsupp.single (2 * p) 1) (C (p * q) ^ p) =
      (p : ℤ) * (coeff (Finsupp.single p q) (C (p * q))) ^ (p - 1) *
        coeff (Finsupp.single p (q - 2) + Finsupp.single (2 * p) 1) (C (p * q)) := by
  have hp0 : 0 < p := by omega
  have h1 := spec_eq_of_weighted (p := p) (Q := q) hp0 (isWeightedHomogeneous_C (p * q))
  have hpow : IsWeightedHomogeneous (fun k : ℕ => k) (C (p * q) ^ p) (p * (p * q)) := by
    have := (isWeightedHomogeneous_C (p * q)).pow p
    simpa [smul_eq_mul] using this
  have h2 := spec_eq_of_weighted (p := p) (Q := p * q) hp0 hpow
  rw [map_pow, h1] at h2
  have h3 := congrArg TrivSqZeroExt.snd h2
  obtain ⟨r, hr⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  set c0 := coeff (Finsupp.single p q) (C (p * q)) with hc0
  set c1 := coeff (Finsupp.single p (q - 2) + Finsupp.single (2 * p) 1) (C (p * q)) with hc1
  set c1' := coeff (Finsupp.single p (p * q - 2) + Finsupp.single (2 * p) 1) (C (p * q) ^ p) with hc1'
  rw [hr] at h3
  rw [dn_snd_pow_succ] at h3
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, dn_snd_zsmul, dn_fst_zsmul,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr,
    TrivSqZeroExt.snd_inr, zsmul_zero, add_zero, zero_add] at h3
  have h4 : c1' • (Polynomial.X : Polynomial ℤ) ^ (p * q - 2) =
      ((r + 1 : ℕ) : Polynomial ℤ) * ((c0 • (Polynomial.X : Polynomial ℤ) ^ q) ^ r *
        (c1 • (Polynomial.X : Polynomial ℤ) ^ (q - 2))) := by
    rw [← hr] at h3 ⊢
    exact h3.symm
  have h6 : ((r + 1 : ℕ) : Polynomial ℤ) * ((c0 • (Polynomial.X : Polynomial ℤ) ^ q) ^ r *
        (c1 • (Polynomial.X : Polynomial ℤ) ^ (q - 2))) =
      Polynomial.C ((r + 1 : ℤ) * (c0 ^ r * c1)) * Polynomial.X ^ (q * r + (q - 2)) := by
    simp only [zsmul_eq_mul, ← Polynomial.C_eq_intCast, mul_pow, ← pow_mul]
    rw [pow_add]
    simp only [Polynomial.C_mul, Polynomial.C_pow, map_natCast, Polynomial.C_add, map_one]
    push_cast
    ring_nf
  have hL : c1' • (Polynomial.X : Polynomial ℤ) ^ (p * q - 2) =
      Polynomial.C c1' * Polynomial.X ^ (p * q - 2) := by
    rw [zsmul_eq_mul, ← Polynomial.C_eq_intCast, Int.cast_id]
  rw [hL, h6] at h4
  have h5 := congrArg (fun f => Polynomial.coeff f (p * q - 2)) h4
  simp only [Polynomial.coeff_C_mul_X_pow, if_true] at h5
  by_cases hq2 : 2 ≤ q
  · have : p * q - 2 = q * r + (q - 2) := by
      rw [hr]; obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hq2; simp; ring_nf; omega
    rw [if_pos this] at h5
    rw [hr]
    simp only [Nat.add_sub_cancel]
    push_cast
    rw [h5]
    ring
  · have hq1 : q = 1 := by omega
    subst hq1
    have hc1z : c1 = 0 := by
      rw [hc1]
      apply IsWeightedHomogeneous.coeff_eq_zero (isWeightedHomogeneous_C (p * 1))
      rw [weight_two hp0]
      simp; omega
    have h5' : c1' = 0 := by rw [h5]; split_ifs <;> simp [hc1z]
    rw [h5', hc1z]; simp

/-! ### Gauss: the product of the units modulo `p^s` is `-1` for odd `p` -/

section units
variable {p s : ℕ}

lemma units_inv_eq_self (hp : p.Prime) (hodd : p ≠ 2) (hs : 1 ≤ s) (x : (ZMod (p ^ s))ˣ)
    (h : x⁻¹ = x) : x = 1 ∨ x = -1 := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective (x : ZMod (p ^ s))
  have hxx : (x : ZMod (p ^ s)) * x = 1 := by
    have h2 : x * x = 1 := by
      have := mul_inv_cancel x
      rwa [h] at this
    simpa using congrArg Units.val h2
  have hdvd : ((p ^ s : ℕ) : ℤ) ∣ (a - 1) * (a + 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [← ha] at hxx
    linear_combination hxx
  push_cast at hdvd
  have hnot : ¬ ((p : ℤ) ∣ a - 1 ∧ (p : ℤ) ∣ a + 1) := by
    rintro ⟨h1, h2⟩
    have h3 : (p : ℤ) ∣ (a + 1) - (a - 1) := dvd_sub h2 h1
    have h4 : (p : ℤ) ∣ 2 := by simpa using h3
    have h5 : p ∣ 2 := by exact_mod_cast h4
    have := Nat.le_of_dvd (by norm_num) h5
    have := hp.two_le
    omega
  by_cases h1 : (p : ℤ) ∣ a - 1
  · have h2 : ¬ (p : ℤ) ∣ a + 1 := fun h2 => hnot ⟨h1, h2⟩
    have hc : IsCoprime ((p : ℤ) ^ s) (a + 1) :=
      (hpz.irreducible.coprime_iff_not_dvd.mpr h2).pow_left
    have : (p : ℤ) ^ s ∣ a - 1 := hc.dvd_of_dvd_mul_right hdvd
    left
    apply Units.ext
    have h6 : ((a - 1 : ℤ) : ZMod (p ^ s)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast this
    push_cast at h6
    rw [← ha]
    simpa [sub_eq_zero] using h6
  · have hc : IsCoprime ((p : ℤ) ^ s) (a - 1) :=
      (hpz.irreducible.coprime_iff_not_dvd.mpr h1).pow_left
    have : (p : ℤ) ^ s ∣ a + 1 := hc.dvd_of_dvd_mul_left hdvd
    right
    apply Units.ext
    have h6 : ((a + 1 : ℤ) : ZMod (p ^ s)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast this
    push_cast at h6
    rw [← ha]
    simpa [add_eq_zero_iff_eq_neg] using h6

lemma prod_units_eq_neg_one [Fact p.Prime] (hodd : p ≠ 2) (hs : 1 ≤ s) :
    ∏ x : (ZMod (p ^ s))ˣ, (x : ZMod (p ^ s)) = -1 := by
  have hp : p.Prime := Fact.out
  have hU : ∏ x : (ZMod (p ^ s))ˣ, x = (-1 : (ZMod (p ^ s))ˣ) := by
    classical
    have : (∏ x ∈ (Finset.univ : Finset (ZMod (p ^ s))ˣ).erase (-1), x) = 1 :=
      Finset.prod_involution (fun x _ => x⁻¹) (by simp)
        (fun a ha hne => by
          intro heq
          rcases units_inv_eq_self hp hodd hs a heq with h | h
          · exact hne (by simp [h])
          · exact (Finset.mem_erase.mp ha).1 h)
        (fun a ha => by
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
          intro h
          apply (Finset.mem_erase.mp ha).1
          rw [inv_eq_iff_eq_inv] at h
          simpa using h)
        (by simp)
    rw [← Finset.mul_prod_erase Finset.univ (fun x => x) (Finset.mem_univ (-1 : (ZMod (p ^ s))ˣ)),
      this, mul_one]
  have := congrArg (fun u : (ZMod (p ^ s))ˣ => (u : ZMod (p ^ s))) hU
  simpa [Units.coe_prod] using this

/-- `G i` is `i` if `p ∤ i` and `1` otherwise, in `ZMod (p^s)`. -/
noncomputable def Gz (p s : ℕ) (i : ℕ) : ZMod (p ^ s) := if p ∣ i then 1 else (i : ZMod (p ^ s))

lemma prod_Gz_period (hp : p.Prime) (hodd : p ≠ 2) (hs : 1 ≤ s) :
    ∏ x ∈ Finset.range (p ^ s), Gz p s (x + 1) = -1 := by
  haveI := Fact.mk hp
  have hpN : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hG0 : Gz p s 0 = 1 := by simp [Gz]
  have hGN : Gz p s (p ^ s) = 1 := by simp [Gz, hpN]
  have h1 : ∏ x ∈ Finset.range (p ^ s), Gz p s (x + 1) = ∏ x ∈ Finset.range (p ^ s), Gz p s x := by
    have a := Finset.prod_range_succ (fun x => Gz p s x) (p ^ s)
    have b := Finset.prod_range_succ' (fun x => Gz p s x) (p ^ s)
    rw [hGN, mul_one] at a
    rw [hG0, mul_one] at b
    rw [← b, ← a]
  rw [h1]
  have h2 : ∏ x ∈ Finset.range (p ^ s), Gz p s x =
      ∏ x ∈ (Finset.range (p ^ s)).filter (fun x => ¬ p ∣ x), (x : ZMod (p ^ s)) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro x _
    unfold Gz
    by_cases h : p ∣ x <;> simp [h]
  rw [h2, ← prod_units_eq_neg_one hodd hs]
  symm
  refine Finset.prod_bij (fun (u : (ZMod (p ^ s))ˣ) _ => (u : ZMod (p ^ s)).val) ?_ ?_ ?_ ?_
  · intro u _
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt _, ?_⟩
    intro hd
    have hcop := ZMod.val_coe_unit_coprime u
    have : p ∣ Nat.gcd (u : ZMod (p ^ s)).val (p ^ s) := Nat.dvd_gcd hd hpN
    rw [hcop] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · intro u _ v _ h
    exact Units.ext (ZMod.val_injective _ h)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    have hcop : Nat.Coprime m (p ^ s) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm.2).symm
    refine ⟨ZMod.unitOfCoprime m hcop, Finset.mem_univ _, ?_⟩
    simp [ZMod.val_natCast_of_lt hm.1]
  · intro u _
    simp
end units

/-! ### Congruence of `U_k` and `U_q^p` modulo `p^s` -/

section cong
variable {p s : ℕ}

lemma Ufun_cast (p n : ℕ) (s : ℕ) :
    ((Ufun p n : ℕ) : ZMod (p ^ s)) = ∏ i ∈ Finset.range (p * n), Gz p s (i + 1) := by
  unfold Ufun Gz
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp

lemma prod_Gz_mul (hp : p.Prime) (hodd : p ≠ 2) (hs : 1 ≤ s) (M : ℕ) :
    ∏ i ∈ Finset.range (p ^ s * M), Gz p s (i + 1) = (-1) ^ M := by
  haveI := Fact.mk hp
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show p ^ s * (M + 1) = p ^ s * M + p ^ s by ring, Finset.prod_range_add, ih, pow_succ]
    congr 1
    rw [← prod_Gz_period (p := p) (s := s) hp hodd hs]
    apply Finset.prod_congr rfl
    intro x _
    have hpN : p ∣ p ^ s * M := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
    unfold Gz
    have e : p ^ s * M + x + 1 = p ^ s * M + (x + 1) := by ring
    rw [e]
    have hiff : p ∣ p ^ s * M + (x + 1) ↔ p ∣ x + 1 := (Nat.dvd_add_right hpN)
    by_cases h : p ∣ x + 1
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
      push_cast
      have : (p : ZMod (p ^ s)) ^ s = 0 := by exact_mod_cast ZMod.natCast_self (p ^ s)
      rw [this]
      simp

lemma Ufun_cast_neg_one_pow (hp : p.Prime) (hodd : p ≠ 2) (hs : 1 ≤ s) {n M : ℕ}
    (h : p * n = p ^ s * M) : ((Ufun p n : ℕ) : ZMod (p ^ s)) = (-1) ^ M := by
  rw [Ufun_cast, h, prod_Gz_mul hp hodd hs]

/-- `p^s ∣ U_{pq} - U_q^p` for `s = v_p(pq)`. -/
theorem Ufun_cong (hp : p.Prime) (hodd : p ≠ 2) {q : ℕ} (hq : 0 < q) :
    (p : ℤ) ^ ((p * q).factorization p) ∣ (Ufun p (p * q) : ℤ) - (Ufun p q : ℤ) ^ p := by
  set s := (p * q).factorization p with hs_def
  have hs : 1 ≤ s :=
    (Nat.Prime.dvd_iff_one_le_factorization hp (Nat.mul_ne_zero hp.ne_zero hq.ne')).mp
      (dvd_mul_right p q)
  obtain ⟨m, hm⟩ : p ^ s ∣ p * q := by
    rw [hs_def]; exact Nat.ordProj_dvd _ _
  have h1 : p * q = p ^ s * m := hm
  have h2 : p * (p * q) = p ^ s * (p * m) := by rw [h1]; ring
  have c1 := Ufun_cast_neg_one_pow hp hodd hs h1
  have c2 := Ufun_cast_neg_one_pow hp hodd hs h2
  have key : ((((Ufun p (p * q) : ℤ) - (Ufun p q : ℤ) ^ p : ℤ)) : ZMod (p ^ s)) = 0 := by
    push_cast
    rw [c1, c2, ← pow_mul, mul_comm m p, sub_self]
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ s)).mp key
  exact_mod_cast this

end cong

/-! ### The valuation -/

lemma choose_two_mul (n : ℕ) : (n.choose 2 : ℤ) * 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linarith

lemma sharp_arith {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (v : ℕ) (q' u w A : ℤ)
    (hq' : ¬ (p : ℤ) ∣ q') (hw : ¬ (p : ℤ) ∣ w)
    (hcong : (p : ℤ) ^ (v + 1) ∣ u - w ^ p)
    (hA : 2 * A = (p : ℤ) ^ 2 * ((p : ℤ) ^ v * q') *
      ((p * ((p : ℤ) ^ v * q') - 1) * u - ((p : ℤ) ^ v * q' - 1) * w ^ p)) :
    (p : ℤ) ^ (2 * (v + 1)) ∣ A ∧ ¬ (p : ℤ) ^ (2 * (v + 1) + 1) ∣ A := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have h5 : p ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) h5
    have := hp.two_le
    omega
  have hc2 : ∀ m : ℕ, IsCoprime ((p : ℤ) ^ m) 2 := fun m =>
    (hpz.irreducible.coprime_iff_not_dvd.mpr hp2).pow_left
  set q : ℤ := (p : ℤ) ^ v * q' with hq
  set E : ℤ := (p * q - 1) * u - (q - 1) * w ^ p with hE
  have hE2 : E = -(u - w ^ p) + q * (p * u - w ^ p) := by rw [hE]; ring
  have hpv_dvd : (p : ℤ) ^ v ∣ u - w ^ p :=
    (pow_dvd_pow (p : ℤ) (by omega : v ≤ v + 1)).trans hcong
  obtain ⟨e1, he1⟩ := hpv_dvd
  have hEv : E = (p : ℤ) ^ v * (-e1 + q' * (p * u - w ^ p)) := by
    rw [hE2, he1, hq]; ring
  set F : ℤ := -e1 + q' * (p * u - w ^ p) with hF
  constructor
  · have : (p : ℤ) ^ (2 * (v + 1)) ∣ 2 * A := by
      rw [hA, hEv, hq]
      exact ⟨q' * F * 1, by rw [hF]; ring⟩
    exact (hc2 _).dvd_of_dvd_mul_left this
  · intro hdiv
    have h2A : (p : ℤ) ^ (2 * (v + 1) + 1) ∣ 2 * A := dvd_mul_of_dvd_right hdiv 2
    rw [hA, hEv, hq] at h2A
    have hne : (p : ℤ) ^ (2 * v + 2) ≠ 0 := pow_ne_zero _ hpz.ne_zero
    have h3 : (p : ℤ) ^ (2 * v + 2) * (p : ℤ) ∣ (p : ℤ) ^ (2 * v + 2) * (q' * F) := by
      have e1' : (p : ℤ) ^ 2 * ((p : ℤ) ^ v * q') * ((p : ℤ) ^ v * F) =
          (p : ℤ) ^ (2 * v + 2) * (q' * F) := by ring
      rw [e1'] at h2A
      have e2' : (p : ℤ) ^ (2 * (v + 1) + 1) = (p : ℤ) ^ (2 * v + 2) * (p : ℤ) := by
        have : 2 * (v + 1) + 1 = (2 * v + 2) + 1 := by ring
        rw [this, pow_succ]
      rwa [e2'] at h2A
    have h4 := (mul_dvd_mul_iff_left hne).mp h3
    have h5 : (p : ℤ) ∣ F := (hpz.dvd_or_dvd h4).resolve_left hq'
    have h6 : (p : ℤ) ∣ e1 := by
      have : (p : ℤ) ^ v * (p : ℤ) ∣ (p : ℤ) ^ v * e1 := by
        rw [← pow_succ, ← he1]; exact hcong
      exact (mul_dvd_mul_iff_left (pow_ne_zero _ hpz.ne_zero)).mp this
    have h7 : (p : ℤ) ∣ q' * (p * u - w ^ p) := by
      have : q' * (p * u - w ^ p) = F + e1 := by rw [hF]; ring
      rw [this]; exact dvd_add h5 h6
    have h8 : (p : ℤ) ∣ p * u - w ^ p := (hpz.dvd_or_dvd h7).resolve_left hq'
    have h9 : (p : ℤ) ∣ w ^ p := by
      have : w ^ p = p * u - (p * u - w ^ p) := by ring
      rw [this]; exact dvd_sub (dvd_mul_right _ _) h8
    exact hw (hpz.dvd_of_dvd_pow h9)

/-! ### The theorem -/

theorem coeff_two_p_C' {p : ℕ} (hp : 2 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    coeff (Finsupp.single p (n - 2) + Finsupp.single (2 * p) 1) (C (p * n)) =
      (p : ℤ) * Ufun p n * (n.choose 2 : ℕ) := by
  by_cases h2 : 2 ≤ n
  · exact coeff_two_p_C hp n h2
  · have hn1 : n = 1 := by omega
    subst hn1
    have hp0 : 0 < p := by omega
    rw [IsWeightedHomogeneous.coeff_eq_zero (isWeightedHomogeneous_C (p * 1))]
    · simp
    · rw [weight_two hp0]; simp; omega

/-- **Proposition `prop:lift-sharp-odd`** (main paper, Appendix "Sharpness of the lift for odd
primes").  Let `p` be an odd prime, `p ∣ k`, `k > 0`, and `s = v_p(k)`.  The coefficient of the
monomial `X_p^(k-2) X_{2p}` in `C_{pk} - C_k^p` is divisible by `p^(2s)` and not by `p^(2s+1)`,
i.e. it has `p`-adic valuation exactly `2s`. -/
theorem lift_sharp_odd {p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hk : 0 < k) (hpk : p ∣ k) :
    (p : ℤ) ^ (2 * k.factorization p) ∣
        coeff (Finsupp.single p (k - 2) + Finsupp.single (2 * p) 1) (C (p * k) - C k ^ p) ∧
      ¬ (p : ℤ) ^ (2 * k.factorization p + 1) ∣
        coeff (Finsupp.single p (k - 2) + Finsupp.single (2 * p) 1) (C (p * k) - C k ^ p) := by
  obtain ⟨q, rfl⟩ := hpk
  have hq : 0 < q := Nat.pos_of_mul_pos_left hk
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : 0 < p := hp.pos
  -- the coefficient
  have hcoef : coeff (Finsupp.single p (p * q - 2) + Finsupp.single (2 * p) 1)
      (C (p * (p * q)) - C (p * q) ^ p) =
      (p : ℤ) * Ufun p (p * q) * ((p * q).choose 2 : ℕ) -
        (p : ℤ) * (Ufun p q : ℤ) ^ (p - 1) * ((p : ℤ) * Ufun p q * (q.choose 2 : ℕ)) := by
    rw [coeff_sub, coeff_pow_two_p hp2 hq, coeff_single_C hp2 q,
      coeff_two_p_C' hp2 hq, coeff_two_p_C' hp2 (Nat.mul_pos hp0 hq)]
  rw [hcoef]
  -- valuation bookkeeping
  have hfact : (p * q).factorization p = q.factorization p + 1 := by
    rw [Nat.factorization_mul hp.ne_zero hq.ne', Finsupp.add_apply, Nat.Prime.factorization_self hp]
    ring
  rw [hfact]
  set v := q.factorization p with hv
  obtain ⟨q', hq'ne, hqeq⟩ : ∃ q', ¬ p ∣ q' ∧ q = p ^ v * q' := by
    exact ⟨q / p ^ q.factorization p, Nat.not_dvd_ordCompl hp hq.ne',
      (Nat.ordProj_mul_ordCompl_eq_self q p).symm⟩
  have hcong := Ufun_cong hp hodd hq
  rw [hfact] at hcong
  have hA : 2 * ((p : ℤ) * Ufun p (p * q) * ((p * q).choose 2 : ℕ) -
        (p : ℤ) * (Ufun p q : ℤ) ^ (p - 1) * ((p : ℤ) * Ufun p q * (q.choose 2 : ℕ))) =
      (p : ℤ) ^ 2 * ((p : ℤ) ^ v * (q' : ℤ)) *
        ((p * ((p : ℤ) ^ v * q') - 1) * (Ufun p (p * q) : ℤ) -
          ((p : ℤ) ^ v * q' - 1) * (Ufun p q : ℤ) ^ p) := by
    have e1 := choose_two_mul (p * q)
    have e2 := choose_two_mul q
    have hqz : (q : ℤ) = (p : ℤ) ^ v * q' := by exact_mod_cast hqeq
    have hpp : (p : ℤ) ^ p = (p : ℤ) * (p : ℤ) ^ (p - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hwp : (Ufun p q : ℤ) ^ p = (Ufun p q : ℤ) * (Ufun p q : ℤ) ^ (p - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [← hqz, hwp]
    push_cast at e1 e2 ⊢
    linear_combination (↑p * ↑(Ufun p (p * q)) : ℤ) * e1 - ((p : ℤ) * (Ufun p q : ℤ) ^ (p - 1) * ((p : ℤ) * Ufun p q)) * e2
  have hw : ¬ (p : ℤ) ∣ (Ufun p q : ℤ) := by
    intro h
    exact Ufun_not_dvd hp q (by exact_mod_cast h)
  have hq'z : ¬ (p : ℤ) ∣ (q' : ℤ) := by
    intro h; exact hq'ne (by exact_mod_cast h)
  have := sharp_arith hp hodd v (q' : ℤ) (Ufun p (p * q) : ℤ) (Ufun p q : ℤ) _ hq'z hw hcong hA
  have e : 2 * (v + 1) = 2 * (v + 1) := rfl
  exact this

/-! ### The case `p = 2` -/

/-- **Sharpness of the lift for `p = 2`** (main paper, Remark `rem:lift-sharp`; it is the exact
content theorem `thm:optimal-divisor` with `n = k`, via `prime_witness`).  For `k > 0` even and
`s = v_2(k)`, the coefficient of `X_1^(2k-4) X_4` in `C_{2k} - C_k^2` has 2-adic valuation
`2s - 1` (stated as `+ 1 = 2 s`). -/
theorem lift_sharp_two {k : ℕ} (hk : 0 < k) (hk2 : 2 ∣ k) :
    padicValNat 2 (coeff (Finsupp.single 1 (2 * k - 4) + Finsupp.single 4 1)
        (C (2 * k) - C k ^ 2)).natAbs + 1 = 2 * padicValNat 2 k := by
  have h := prime_witness k k 2 Nat.prime_two hk2 hk2 hk.ne' hk.ne'
  have hcix : ciExp (k + k - 2 * 2) {2 * 2} =
      Finsupp.single 1 (2 * k - 4) + Finsupp.single 4 1 := by
    ext j
    rw [ciExp_apply]
    simp only [Finsupp.add_apply, Finsupp.single_apply, Multiset.count_singleton]
    split_ifs <;> omega
  have hP : CpermPair k k - Cperm k * Cperm k = C (2 * k) - C k ^ 2 := by
    rw [CpermPair_eq_Cperm, Cperm_eq_C, Cperm_eq_C, sq, two_mul]
  rw [hcix, hP] at h
  rw [h]
  ring

/-- `2^(2 v_2(k))` does not divide the coefficient of `X_1^(2k-4) X_4` in `C_{2k} - C_k^2`. -/
theorem lift_sharp_two_not_dvd {k : ℕ} (hk : 0 < k) (hk2 : 2 ∣ k) :
    ¬ (2 : ℤ) ^ (2 * padicValNat 2 k) ∣ coeff (Finsupp.single 1 (2 * k - 4) + Finsupp.single 4 1)
        (C (2 * k) - C k ^ 2) := by
  intro hdvd
  have h := lift_sharp_two hk hk2
  set c := coeff (Finsupp.single 1 (2 * k - 4) + Finsupp.single 4 1) (C (2 * k) - C k ^ 2) with hc
  have hc0 : c.natAbs ≠ 0 := by
    intro h0
    have h00 : padicValNat 2 (0 : ℕ) = 0 := by simp
    rw [h0, h00] at h
    omega
  have h2 : 2 ^ (2 * padicValNat 2 k) ∣ c.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa [Int.natAbs_pow] using this
  have := (padicValNat_dvd_iff_le hc0).mp h2
  omega

end CongruenceTheory.LiftSharp
