import Mathlib
import CongruenceTheoryHigherOrder.ZpShiftCongruence
import CongruenceTheoryHigherOrder.KWeightedHomogeneous
import CongruenceTheory.CoeffExtraction
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.LiftSharpOdd


/-!
**Bala's conjecture on OEIS A227937** (main paper, Section "Conjectures from the OEIS", Theorem
`thm:bala-A227937`), using the shift congruence with weights in `Z_(p)`
(`ZpShiftCongruence.lean`).

The sequence is `a(n) = n! [x^n] exp(x^2/2 + x^3/6)`, `1, 0, 1, 1, 3, 10, 25, 105, ...`.  It is
`A_w(n)` for the weights `w_2 = 1`, `w_3 = 1/2` and `w_m = 0` otherwise (`Wq`, `aq`), which are
in `Z_(p)` for every prime `p ≥ 3`.  We define the integer sequence `aInt` by the recurrence
`a(m+3) = (m+2) a(m+1) + C(m+2,2) a(m)` (the recurrence for `C_n` at these weights), prove
`aInt n = A_w(n)` (`aInt_eq_aq`) and the explicit formula `a(n) = ∑_{2i+3j=n} n!/(i! j! 2^i 6^j)`
(`aInt_eq_sum`, from the cycle-type count of the coefficient of `X_2^i X_3^j` in `C_n`).

* `pow_dvd_aInt_self`: `p^r ∣ a(p^r)` for primes `p ≥ 5` (each coefficient of `X_2^i X_3^j` in
  `C_{p^r}` is divisible by `p^r` because `M!/(i+j)!` is, and `2^i 3^j` is a `p`-adic unit).
* `pow_dvd_aInt_of_le`: `p^r ∣ a(N)` for all `N ≥ p^r` (the `lcm` form of the `Z_(p)` shift
  congruence plus the previous item, as in the paper's proof).
* `bala_conjecture`: `n ∣ a(n+k)` for `n ≥ 1` coprime to `6` and all `k ≥ 0`
  (Chinese remainder step via `dvd_of_forall_prime_pow_dvd`).
-/

namespace CongruenceTheory.ZpShift

open MvPolynomial
open scoped Nat

/-- The weights of OEIS A227937: `w_2 = 1`, `w_3 = 1/2`, all others `0`
(so that `∑ w_m x^m / m = x^2/2 + x^3/6`). -/
noncomputable def Wq (m : ℕ) : ℚ := if m = 2 then 1 else if m = 3 then 1 / 2 else 0

/-- The pairs `(i, j)` with `2 i + 3 j = n`. -/
def pairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter (fun ij => 2 * ij.1 + 3 * ij.2 = n)

/-- The monomial `X_2^i X_3^j`. -/
noncomputable def mon23 (i j : ℕ) : ℕ →₀ ℕ := Finsupp.single 2 i + Finsupp.single 3 j

lemma mon23_apply_two (i j : ℕ) : mon23 i j 2 = i := by simp [mon23]
lemma mon23_apply_three (i j : ℕ) : mon23 i j 3 = j := by simp [mon23]

lemma mon23_inj {i j i' j' : ℕ} (h : mon23 i j = mon23 i' j') : i = i' ∧ j = j' := by
  constructor
  · simpa [mon23_apply_two] using congrArg (fun f => f 2) h
  · simpa [mon23_apply_three] using congrArg (fun f => f 3) h

lemma weight_mon23 (i j : ℕ) : Finsupp.weight (fun k : ℕ => k) (mon23 i j) = 2 * i + 3 * j := by
  unfold mon23
  rw [map_add, Finsupp.weight_single, Finsupp.weight_single]
  simp only [smul_eq_mul]
  ring

lemma eq_mon23 (d : ℕ →₀ ℕ) (h : ∀ j ∈ d.support, j = 2 ∨ j = 3) : d = mon23 (d 2) (d 3) := by
  ext j
  unfold mon23
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  by_cases h1 : j = 2
  · subst h1; simp
  · by_cases h2 : j = 3
    · subst h2; simp
    · have : d j = 0 := by
        by_contra hc
        rcases h j (Finsupp.mem_support_iff.mpr hc) with h3 | h3 <;> contradiction
      have e1 : (2 : ℕ) ≠ j := fun h => h1 h.symm
      have e2 : (3 : ℕ) ≠ j := fun h => h2 h.symm
      simp [this, e1, e2]

lemma aeval_monomial_other (d : ℕ →₀ ℕ) {j : ℕ} (hj : j ∈ d.support) (h1 : j ≠ 2) (h2 : j ≠ 3)
    (c : ℤ) : aeval Wq (monomial d c) = 0 := by
  rw [aeval_monomial, Finsupp.prod]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero hj
  have : Wq j = 0 := by simp [Wq, h1, h2]
  rw [this]
  exact zero_pow (Finsupp.mem_support_iff.mp hj)

lemma aeval_monomial_mon23 (i j : ℕ) (c : ℤ) :
    aeval Wq (monomial (mon23 i j) c) = (c : ℚ) * (1 / 2) ^ j := by
  rw [aeval_monomial, mon23, Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add])]
  rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]
  simp [Wq]

/-- Evaluation of a weighted-homogeneous polynomial at the weights `Wq`. -/
theorem aeval_Wq_eq_sum {n : ℕ} {P : MvPolynomial ℕ ℤ}
    (hP : IsWeightedHomogeneous (fun k : ℕ => k) P n) :
    aeval Wq P = ∑ ij ∈ pairs n, ((coeff (mon23 ij.1 ij.2) P : ℤ) : ℚ) * (1 / 2) ^ ij.2 := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  have h1 : ∀ d ∈ P.support, aeval Wq (monomial d (coeff d P)) =
      ∑ ij ∈ pairs n, if d = mon23 ij.1 ij.2 then ((coeff d P : ℤ) : ℚ) * (1 / 2) ^ ij.2 else 0 := by
    intro d hd
    have hd' := mem_support_iff.mp hd
    by_cases hs : ∃ j ∈ d.support, j ≠ 2 ∧ j ≠ 3
    · obtain ⟨j, hj, h2, h3⟩ := hs
      rw [aeval_monomial_other d hj h2 h3]
      symm
      apply Finset.sum_eq_zero
      intro ij _
      rw [if_neg]
      intro hdeq
      have := Finsupp.mem_support_iff.mp hj
      rw [hdeq] at this
      unfold mon23 at this
      simp [Finsupp.single_apply, h2.symm, h3.symm] at this
    · push Not at hs
      have hs' : ∀ j ∈ d.support, j = 2 ∨ j = 3 := by
        intro j hj
        by_cases h2 : j = 2
        · exact Or.inl h2
        · exact Or.inr (hs j hj h2)
      have hdeq := eq_mon23 d hs'
      have hw := hP hd'
      rw [hdeq, weight_mon23] at hw
      set a := d 2
      set b := d 3
      rw [hdeq, aeval_monomial_mon23]
      have hmem : (a, b) ∈ pairs n := by
        simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        refine ⟨⟨by omega, by omega⟩, hw⟩
      rw [Finset.sum_eq_single (a, b)]
      · simp
      · intro ij _ hne
        rw [if_neg]
        intro h
        exact hne (by
          obtain ⟨e1, e2⟩ := mon23_inj h
          exact Prod.ext e1.symm e2.symm)
      · intro h; exact absurd hmem h
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ij _
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h]; simp

/-! ### The coefficient of `X_2^i X_3^j` in `C_{2i+3j}` -/

lemma ciExp_mon23 (i j : ℕ) :
    ciExp 0 (Multiset.replicate i 2 + Multiset.replicate j 3) = mon23 i j := by
  ext x
  rw [ciExp_apply, Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
  simp only [mon23, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

theorem coeff_mon23_mul (i j : ℕ) :
    coeff (mon23 i j) (CongruenceTheory.C (2 * i + 3 * j)) *
        ((2 ^ i * 3 ^ j * (i ! * j !) : ℕ) : ℤ) = ((2 * i + 3 * j)! : ℕ) := by
  set m : Multiset ℕ := Multiset.replicate i 2 + Multiset.replicate j 3 with hm
  have hsum : m.sum = 2 * i + 3 * j := by
    simp [hm, Multiset.sum_replicate]; ring
  have hm2 : ∀ x ∈ m, 2 ≤ x := by
    intro x hx
    rw [hm, Multiset.mem_add] at hx
    rcases hx with hx | hx
    · rw [Multiset.eq_of_mem_replicate hx]
    · rw [Multiset.eq_of_mem_replicate hx]; norm_num
  have h1 := CongruenceTheory.coeff_Cperm_eq_card_cycleType (2 * i + 3 * j) m hm2
  rw [hsum, Nat.sub_self, ciExp_mon23] at h1
  rw [← CongruenceTheory.Cperm_eq_C, h1]
  have h2 := Equiv.Perm.card_of_cycleType_mul_eq (α := Fin (2 * i + 3 * j)) m
  rw [if_pos ⟨by rw [hsum]; simp, hm2⟩] at h2
  simp only [Fintype.card_fin, hsum, Nat.sub_self, Nat.factorial_zero, one_mul] at h2
  have hprod : m.prod = 2 ^ i * 3 ^ j := by simp [hm, Multiset.prod_replicate]
  have hfin : ∏ x ∈ m.toFinset, (Multiset.count x m)! = i ! * j ! := by
    have hsub : m.toFinset ⊆ {2, 3} := by
      intro x hx
      rw [Multiset.mem_toFinset, hm, Multiset.mem_add] at hx
      rcases hx with hx | hx
      · rw [Multiset.eq_of_mem_replicate hx]; simp
      · rw [Multiset.eq_of_mem_replicate hx]; simp
    rw [Finset.prod_subset hsub (by
      intro x hx hx'
      rw [Multiset.mem_toFinset] at hx'
      rw [Multiset.count_eq_zero_of_notMem hx']; simp)]
    rw [Finset.prod_pair (by norm_num)]
    have c1 : Multiset.count 2 m = i := by
      rw [hm, Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]; simp
    have c2 : Multiset.count 3 m = j := by
      rw [hm, Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]; simp
    rw [c1, c2]
  rw [hprod, hfin] at h2
  exact_mod_cast h2

/-! ### The integer sequence `a(n) = n! [x^n] exp(x^2/2 + x^3/6)` -/

/-- `A_w(n)` for the weights `Wq`. -/
noncomputable def aq (n : ℕ) : ℚ := Awq Wq n

/-- The triple `(a_m, a_{m+1}, a_{m+2})` of the integer recurrence
`a_{m+3} = (m+2) a_{m+1} + C(m+2,2) a_m`, `a_0 = 1`, `a_1 = 0`, `a_2 = 1`. -/
def abalaTrip : ℕ → ℤ × ℤ × ℤ
  | 0 => (1, 0, 1)
  | m + 1 =>
    ((abalaTrip m).2.1, (abalaTrip m).2.2,
      ((m + 2 : ℕ) : ℤ) * (abalaTrip m).2.1 + (((m + 2).choose 2 : ℕ) : ℤ) * (abalaTrip m).1)

/-- OEIS A227937 (the integer recurrence form):
`a(0) = 1`, `a(1) = 0`, `a(2) = 1`, `a(m+3) = (m+2) a(m+1) + C(m+2,2) a(m)`. -/
def aInt (n : ℕ) : ℤ := (abalaTrip n).1

lemma aInt_zero : aInt 0 = 1 := rfl
lemma aInt_one : aInt 1 = 0 := rfl
lemma aInt_two : aInt 2 = 1 := rfl

example : aInt 5 = 10 ∧ aInt 6 = 25 ∧ aInt 7 = 105 := by decide

lemma aInt_rec (m : ℕ) :
    aInt (m + 3) = ((m + 2 : ℕ) : ℤ) * aInt (m + 1) + (((m + 2).choose 2 : ℕ) : ℤ) * aInt m := rfl

lemma aq_zero : aq 0 = 1 := by
  simp [aq, Awq, CongruenceTheory.C_zero]

lemma aq_succ (n : ℕ) :
    aq (n + 1) = ∑ r ∈ Finset.range (n + 1),
      (CongruenceTheory.fall n r : ℚ) * (Wq (r + 1) * aq (n - r)) := by
  unfold aq Awq
  rw [CongruenceTheory.C_succ, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp [map_mul, map_intCast, aeval_X]

lemma aq_one : aq 1 = 0 := by
  rw [aq_succ]; simp [CongruenceTheory.fall, Wq]

lemma aq_two : aq 2 = 1 := by
  rw [aq_succ]
  simp [Finset.sum_range_succ, CongruenceTheory.fall, Wq, aq_zero, aq_one]

lemma fall_one' (n : ℕ) : (CongruenceTheory.fall n 1 : ℚ) = n := by
  simp [CongruenceTheory.fall]

lemma fall_two' (n : ℕ) : (CongruenceTheory.fall n 2 : ℚ) = n * (n - 1) := by
  simp [CongruenceTheory.fall, Finset.prod_range_succ]

lemma aq_rec (m : ℕ) :
    aq (m + 3) = ((m + 2 : ℕ) : ℚ) * aq (m + 1) + (((m + 2).choose 2 : ℕ) : ℚ) * aq m := by
  rw [aq_succ (m + 2)]
  have key : ∀ r ∈ Finset.range (m + 2 + 1),
      (CongruenceTheory.fall (m + 2) r : ℚ) * (Wq (r + 1) * aq (m + 2 - r)) =
        (if r = 1 then ((m + 2 : ℕ) : ℚ) * aq (m + 1) else 0) +
        (if r = 2 then (((m + 2).choose 2 : ℕ) : ℚ) * aq m else 0) := by
    intro r _
    by_cases h1 : r = 1
    · subst h1
      simp [Wq, fall_one']
    · by_cases h2 : r = 2
      · subst h2
        simp only [Wq, fall_two', Nat.cast_choose_two]
        simp
        ring
      · have : Wq (r + 1) = 0 := by
          simp only [Wq]
          rw [if_neg (by omega), if_neg (by omega)]
        simp [this, h1, h2]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem aInt_eq_aq (n : ℕ) : (aInt n : ℚ) = aq n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [aInt_zero, aq_zero]
    | 1, _ => simp [aInt_one, aq_one]
    | 2, _ => simp [aInt_two, aq_two]
    | m + 3, ih =>
      rw [aInt_rec, aq_rec, ← ih (m + 1) (by omega), ← ih m (by omega)]
      push_cast
      ring

/-- **The explicit formula** `a(n) = ∑_{2i+3j=n} n!/(i! j! 2^i 6^j)`. -/
theorem aInt_eq_sum (n : ℕ) :
    (aInt n : ℚ) = ∑ ij ∈ pairs n,
      (n ! : ℚ) / ((ij.1 ! : ℚ) * (ij.2 ! : ℚ) * 2 ^ ij.1 * 6 ^ ij.2) := by
  rw [aInt_eq_aq]
  unfold aq Awq
  rw [aeval_Wq_eq_sum (CongruenceTheory.LiftSharp.isWeightedHomogeneous_C n)]
  apply Finset.sum_congr rfl
  intro ij hij
  simp only [pairs, Finset.mem_filter] at hij
  obtain ⟨_, hn⟩ := hij
  have h := coeff_mon23_mul ij.1 ij.2
  rw [hn] at h
  have h' : ((coeff (mon23 ij.1 ij.2) (CongruenceTheory.C n) : ℤ) : ℚ) *
      (2 ^ ij.1 * 3 ^ ij.2 * (ij.1 ! * ij.2 !) : ℚ) = (n ! : ℚ) := by
    exact_mod_cast h
  have hD : (2 ^ ij.1 * 3 ^ ij.2 * (ij.1 ! * ij.2 !) : ℚ) ≠ 0 := by positivity
  rw [eq_div_iff (by positivity)]
  have e6 : (6 : ℚ) ^ ij.2 = 2 ^ ij.2 * 3 ^ ij.2 := by rw [← mul_pow]; norm_num
  rw [e6]
  simp only [one_div, inv_pow]
  field_simp
  linear_combination h'

/-! ### Divisibility -/

section bala
variable {p : ℕ} [Fact p.Prime]

lemma padicNorm_pow_prime (r : ℕ) : padicNorm p ((p : ℚ) ^ r) = ((p : ℚ) ^ r)⁻¹ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, padicNorm.mul, ih, padicNorm.padicNorm_p_of_prime, mul_inv]

/-- An integer that equals `p^r z` with `z ∈ Z_(p)` is divisible by `p^r`. -/
lemma int_dvd_of_norm (x : ℤ) (z : ℚ) (hz : padicNorm p z ≤ 1) (r : ℕ)
    (h : (x : ℚ) = (p : ℚ) ^ r * z) : ((p ^ r : ℕ) : ℤ) ∣ x := by
  rw [padicNorm.dvd_iff_norm_le, h, padicNorm.mul, padicNorm_pow_prime]
  have e : ((p : ℚ) ^ (-(r : ℤ))) = ((p : ℚ) ^ r)⁻¹ := by rw [zpow_neg, zpow_natCast]
  rw [e]
  calc ((p : ℚ) ^ r)⁻¹ * padicNorm p z ≤ ((p : ℚ) ^ r)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hz (by positivity)
    _ = ((p : ℚ) ^ r)⁻¹ := mul_one _

lemma norm_half_pow_le (hp5 : 5 ≤ p) (j : ℕ) : padicNorm p (((1 : ℚ) / 2) ^ j) ≤ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : padicNorm p (2 : ℚ) = 1 := by
    have := padicNorm.padicNorm_of_prime_of_ne (p := p) (q := 2) (by omega)
    simpa using this
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, padicNorm.mul, padicNorm.div, padicNorm.one, h2]
    simpa using ih

theorem Wq_norm_le_one (hp5 : 5 ≤ p) (m : ℕ) : padicNorm p (Wq m) ≤ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : padicNorm p (2 : ℚ) = 1 := by
    have := padicNorm.padicNorm_of_prime_of_ne (p := p) (q := 2) (by omega)
    simpa using this
  unfold Wq
  split_ifs
  · simp
  · rw [padicNorm.div, padicNorm.one, h2]; simp
  · simp

/-- Each coefficient `[X_2^i X_3^j] C_M`, `2i+3j = M = p^r`, is divisible by `M` for `p ≥ 5`. -/
lemma coeff_dvd_pow (hp5 : 5 ≤ p) {r : ℕ} (hr : 1 ≤ r) {i j : ℕ} (hij : 2 * i + 3 * j = p ^ r) :
    ((p ^ r : ℕ) : ℤ) ∣ coeff (mon23 i j) (CongruenceTheory.C (p ^ r)) := by
  have hM1 : 1 ≤ p ^ r := Nat.one_le_pow _ _ (by omega)
  have hlt : i + j < p ^ r := by omega
  have hmul := coeff_mon23_mul i j
  rw [hij] at hmul
  set c := coeff (mon23 i j) (CongruenceTheory.C (p ^ r)) with hc
  -- factorial identities
  have hfac : (p ^ r)! = (i + j)! * (p ^ r).descFactorial (p ^ r - (i + j)) := by
    have := Nat.factorial_mul_descFactorial (n := p ^ r) (k := p ^ r - (i + j)) (by omega)
    rw [show p ^ r - (p ^ r - (i + j)) = i + j by omega] at this
    exact this.symm
  have hdesc : p ^ r ∣ (p ^ r).descFactorial (p ^ r - (i + j)) := by
    obtain ⟨k, hk⟩ : ∃ k, p ^ r - (i + j) = k + 1 := ⟨p ^ r - (i + j) - 1, by omega⟩
    obtain ⟨M', hM'⟩ : ∃ M', p ^ r = M' + 1 := ⟨p ^ r - 1, by omega⟩
    rw [hk, hM', Nat.succ_descFactorial_succ]
    rw [← hM']
    exact dvd_mul_right _ _
  have hbin : (i + j).choose j * i ! * j ! = (i + j)! := Nat.add_choose_mul_factorial_mul_factorial i j
  have hpos : (0 : ℤ) < ((i ! * j ! : ℕ) : ℤ) := by positivity
  have h1 : c * ((2 ^ i * 3 ^ j : ℕ) : ℤ) = (((i + j).choose j * (p ^ r).descFactorial (p ^ r - (i + j)) : ℕ) : ℤ) := by
    have h2 : (c * ((2 ^ i * 3 ^ j : ℕ) : ℤ)) * ((i ! * j ! : ℕ) : ℤ) =
        (((i + j).choose j * (p ^ r).descFactorial (p ^ r - (i + j)) : ℕ) : ℤ) * ((i ! * j ! : ℕ) : ℤ) := by
      have hn : ((p ^ r)! : ℕ) = ((i + j).choose j * i ! * j ! * (p ^ r).descFactorial (p ^ r - (i + j)) : ℕ) := by
        rw [hfac, ← hbin]
      have := hmul
      rw [hn] at this
      push_cast at this ⊢
      linear_combination this
    exact mul_right_cancel₀ hpos.ne' h2
  have hdvd : ((p ^ r : ℕ) : ℤ) ∣ c * ((2 ^ i * 3 ^ j : ℕ) : ℤ) := by
    rw [h1]
    push_cast
    exact Dvd.dvd.mul_left (by exact_mod_cast hdesc) _
  have hcop : IsCoprime ((p ^ r : ℕ) : ℤ) ((2 ^ i * 3 ^ j : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    apply Nat.Coprime.mul_right
    · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr (by omega))
    · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_three).mpr (by omega))
  exact hcop.dvd_of_dvd_mul_right hdvd

/-- `p^r ∣ a(p^r)` for primes `p ≥ 5`. -/
theorem pow_dvd_aInt_self (hp5 : 5 ≤ p) {r : ℕ} (hr : 1 ≤ r) :
    ((p ^ r : ℕ) : ℤ) ∣ aInt (p ^ r) := by
  have hsum := aeval_Wq_eq_sum (CongruenceTheory.LiftSharp.isWeightedHomogeneous_C (p ^ r))
  have hdiv : ∀ ij ∈ pairs (p ^ r), ∃ t : ℤ,
      coeff (mon23 ij.1 ij.2) (CongruenceTheory.C (p ^ r)) = (p ^ r : ℕ) * t := by
    intro ij hij
    simp only [pairs, Finset.mem_filter] at hij
    exact coeff_dvd_pow hp5 hr hij.2
  choose! t ht using hdiv
  refine int_dvd_of_norm (aInt (p ^ r)) (∑ ij ∈ pairs (p ^ r), (t ij : ℚ) * (1 / 2) ^ ij.2) ?_ r ?_
  · apply padicNorm.sum_le' _ zero_le_one
    intro ij _
    rw [padicNorm.mul]
    exact mul_le_one₀ (by simpa using padicNorm.of_int (p := p) (t ij)) (padicNorm.nonneg _)
      (norm_half_pow_le hp5 _)
  · rw [aInt_eq_aq]
    unfold aq Awq
    rw [hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [ht ij hij]
    push_cast
    ring

end bala

section bala2
variable {p : ℕ} [Fact p.Prime]

/-- `p^r ∣ a(N)` for every `N ≥ p^r`, `p ≥ 5` prime, `r ≥ 1`. -/
theorem pow_dvd_aInt_of_le (hp5 : 5 ≤ p) {r : ℕ} (hr : 1 ≤ r) {N : ℕ} (hN : p ^ r ≤ N) :
    ((p ^ r : ℕ) : ℤ) ∣ aInt N := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using pow_dvd_aInt_self hp5 hr
  have hM1 : 1 ≤ p ^ r := Nat.one_le_pow _ _ (by omega)
  obtain ⟨y, hy, hyeq⟩ := shift_congruence_lcm_Zp (p := p) Wq (Wq_norm_le_one hp5) hM1 hk
  obtain ⟨z, hz⟩ := pow_dvd_aInt_self hp5 hr
  obtain ⟨t, ht⟩ := Nat.dvd_lcm_left (p ^ r) k
  have hq1 : aq (p ^ r) = (p : ℚ) ^ r * z := by
    rw [← aInt_eq_aq, hz]; push_cast; ring
  have hlcm : ((Nat.lcm (p ^ r) k : ℕ) : ℚ) = (p : ℚ) ^ r * t := by
    rw [ht]; push_cast; ring
  have hyeq' : aq (p ^ r + k) - aq (p ^ r) * aq k = ((Nat.lcm (p ^ r) k : ℕ) : ℚ) * y := hyeq
  have e : ((aInt (p ^ r + k) : ℤ) : ℚ) =
      (p : ℚ) ^ r * (((z * aInt k : ℤ) : ℚ) + (t : ℚ) * y) := by
    rw [aInt_eq_aq]
    have : aq (p ^ r + k) = aq (p ^ r) * aq k + ((Nat.lcm (p ^ r) k : ℕ) : ℚ) * y := by
      linarith
    rw [this, hq1, hlcm, ← aInt_eq_aq k]
    push_cast
    ring
  refine int_dvd_of_norm _ _ ?_ r e
  refine (padicNorm.nonarchimedean).trans (max_le ?_ ?_)
  · simpa using padicNorm.of_int (p := p) (z * aInt k)
  · rw [padicNorm.mul]
    exact mul_le_one₀ (by simpa using padicNorm.of_nat (p := p) t) (padicNorm.nonneg _) hy

end bala2

/-- **Theorem `thm:bala-A227937`** (Bala's conjecture on OEIS A227937).  Let
`a(n) = n! [x^n] exp(x^2/2 + x^3/6)` (`aInt`, with the explicit formula `aInt_eq_sum`).  For
`n ≥ 1` coprime to `6` and every `k ≥ 0`, `n ∣ a(n+k)`. -/
theorem bala_conjecture {n : ℕ} (hn : 1 ≤ n) (hn6 : Nat.Coprime n 6) (k : ℕ) :
    (n : ℤ) ∣ aInt (n + k) := by
  apply CongruenceTheory.dvd_of_forall_prime_pow_dvd (by omega)
  intro p hp
  by_cases hpn : p ∣ n
  · haveI := Fact.mk hp
    have h2 : ¬ 2 ∣ n := by
      intro h
      have := Nat.dvd_gcd h (by norm_num : 2 ∣ 6)
      rw [show Nat.gcd n 6 = 1 from hn6] at this
      omega
    have h3 : ¬ 3 ∣ n := by
      intro h
      have := Nat.dvd_gcd h (by norm_num : 3 ∣ 6)
      rw [show Nat.gcd n 6 = 1 from hn6] at this
      omega
    have hp5 : 5 ≤ p := by
      by_contra hlt
      have h2le := hp.two_le
      interval_cases p
      · exact h2 hpn
      · exact h3 hpn
      · exact absurd hp (by norm_num)
    have hr : 1 ≤ n.factorization p := (hp.dvd_iff_one_le_factorization (by omega)).mp hpn
    have hle : p ^ n.factorization p ≤ n + k :=
      (Nat.ordProj_le p (by omega : n ≠ 0)).trans (Nat.le_add_right n k)
    have := pow_dvd_aInt_of_le hp5 hr hle
    exact Int.natCast_dvd.mp this
  · rw [Nat.factorization_eq_zero_of_not_dvd hpn]
    simp

end CongruenceTheory.ZpShift
