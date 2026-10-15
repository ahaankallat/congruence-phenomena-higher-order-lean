import Mathlib
import CongruenceTheoryHigherOrder.EventualDivisibility

/-!
**Section "Conjectures from the OEIS"** of the main paper.

* Theorem `thm:hanna` (Hanna, A214724): with `w_j = 1` for `j ∈ {n^2+1}` and `0` otherwise
  (`hannaW`), if `p = m^2+1` is prime then `p ∣ A_w(n)` for all `n ≥ p` (`hanna_conjecture`),
  and if the prime `p` is not of this form then `A_w(n+p) ≡ A_w(n) (mod p)` (`hanna_converse`).
* Theorem `thm:richman` (Richman, A053871): with `w_1 = 0`, `w_m = 2^(m-1)` for `m ≥ 2`
  (`richmanW`), for odd `q` we have `A_w(q) ≡ -1 (mod q)` (`richman_value`),
  `A_w(n+q) ≡ -A_w(n) (mod q)` (`richman_shift`), and if `m ≡ n (mod q)` then
  `(-1)^m A_w(m) ≡ (-1)^n A_w(n) (mod q)` (`richman_conjecture`).
  The identification of `A_w` with `exp(-x)/sqrt(1-2x)` is not formalized, the theorems
  are stated for the weight sequence.
-/

namespace CongruenceTheory.Shift

open scoped Classical

theorem dvd_of_eq' {a b c : ℤ} (h : a ∣ b) (e : b = c) : a ∣ c := e ▸ h

/-! ### Hanna -/

/-- Hanna's weights: `w_j = 1` if `j = n^2 + 1` for some `n ≥ 0`, else `0`. -/
noncomputable def hannaW (j : ℕ) : ℤ := if ∃ n : ℕ, j = n ^ 2 + 1 then 1 else 0

theorem hannaW_one : hannaW 1 = 1 := by
  simp only [hannaW]; rw [if_pos ⟨0, by norm_num⟩]

/-- **Theorem `thm:hanna`.**  If `p = m^2 + 1` is prime then `p ∣ A_w(n)` for all `n ≥ p`. -/
theorem hanna_conjecture {p m : ℕ} (hp : p.Prime) (hpm : p = m ^ 2 + 1) (n : ℕ) (hn : p ≤ n) :
    (p : ℤ) ∣ Aw hannaW n := by
  have hwp : hannaW p = 1 := by simp only [hannaW]; rw [if_pos ⟨m, hpm⟩]
  have h1 := Aw_prime_cong hp hannaW
  rw [hannaW_one, hwp] at h1
  have hAp : (p : ℤ) ∣ Aw hannaW p := by
    exact dvd_of_eq' (dvd_add h1 (dvd_refl (p : ℤ))) (by ring)
  have h2 := Aw_shift_mod p hp.one_lt.le hannaW (n - p)
  rw [Nat.sub_add_cancel hn] at h2
  have := dvd_add h2 (hAp.mul_left (Aw hannaW (n - p)))
  exact dvd_of_eq' this (by ring)

/-- **Theorem `thm:hanna`, converse.**  If the prime `p` is not of the form `m^2+1` then
`A_w(n+p) ≡ A_w(n) (mod p)` for all `n`. -/
theorem hanna_converse {p : ℕ} (hp : p.Prime) (hnot : ¬ ∃ m : ℕ, p = m ^ 2 + 1) (n : ℕ) :
    (p : ℤ) ∣ Aw hannaW (n + p) - Aw hannaW n := by
  have hwp : hannaW p = 0 := by simp only [hannaW]; rw [if_neg hnot]
  have h1 := Aw_prime_cong hp hannaW
  rw [hannaW_one, hwp] at h1
  have h2 := Aw_shift_mod p hp.one_lt.le hannaW n
  have h3 : (p : ℤ) ∣ Aw hannaW n * (Aw hannaW p - 1) := by
    exact dvd_of_eq' (h1.mul_left (Aw hannaW n)) (by ring)
  exact dvd_of_eq' (dvd_add h2 h3) (by ring)

/-! ### Richman -/

/-- Richman's weights: `w_1 = 0` and `w_m = 2^(m-1)` for `m ≥ 2` (`w_0` is irrelevant). -/
def richmanW (m : ℕ) : ℤ := if m ≤ 1 then 0 else 2 ^ (m - 1)

/-- If `x ≡ y (mod p)` then `x^(p^s) ≡ y^(p^s) (mod p^(s+1))`. -/
theorem pow_pow_congr {p : ℕ} (hp : p.Prime) {x y : ℤ} (h : (p : ℤ) ∣ x - y) :
    ∀ s : ℕ, (p : ℤ) ^ (s + 1) ∣ x ^ (p ^ s) - y ^ (p ^ s) := by
  intro s
  induction s with
  | zero => simpa using h
  | succ s ih =>
    have := pth_power_congr hp (r := s + 1) (by omega) ih
    rwa [← pow_mul, ← pow_succ, ← pow_mul, ← pow_succ] at this

/-- `a(p^r) ≡ -1 (mod p^r)` for odd primes `p` and `r ≥ 1`. -/
theorem richman_prime_power {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) {r : ℕ} (hr : 1 ≤ r) :
    (p : ℤ) ^ r ∣ Aw richmanW (p ^ r) + 1 := by
  have hres := odd_prime_power_residue hp hodd richmanW r hr
  have hp2 : ¬ p ≤ 1 := by have := hp.two_le; omega
  have hw1 : richmanW 1 = 0 := by simp [richmanW]
  have hwp : richmanW p = 2 ^ (p - 1) := by simp [richmanW, hp2]
  have hfermat : (p : ℤ) ∣ 2 ^ (p - 1) - 1 := by
    have hcop : IsCoprime (2 : ℤ) (p : ℤ) := by
      have : Nat.Coprime 2 p := by
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
        intro hd
        have := Nat.le_of_dvd (by norm_num) hd
        have := hp.two_le
        omega
      exact_mod_cast Nat.isCoprime_iff_coprime.mpr this
    have := Int.ModEq.pow_card_sub_one_eq_one hp hcop
    exact (Int.modEq_iff_dvd.mp this.symm)
  have hγ : (p : ℤ) ∣ (richmanW 1 + ((p : ℤ) - 1) * richmanW p) - (-1) := by
    rw [hw1, hwp]
    have : (0 + ((p : ℤ) - 1) * 2 ^ (p - 1)) - (-1) =
        (p : ℤ) * 2 ^ (p - 1) - (2 ^ (p - 1) - 1) := by ring
    rw [this]
    exact dvd_sub (dvd_mul_right _ _) hfermat
  have h2 := pow_pow_congr hp hγ (r - 1)
  have hodd' : Odd (p ^ (r - 1)) := (hp.odd_of_ne_two hodd).pow
  rw [hodd'.neg_one_pow, Nat.sub_add_cancel hr] at h2
  have key : Aw richmanW (p ^ r) + 1 =
      (Aw richmanW (p ^ r) - (richmanW 1 + ((p : ℤ) - 1) * richmanW p) ^ (p ^ (r - 1)))
        + ((richmanW 1 + ((p : ℤ) - 1) * richmanW p) ^ (p ^ (r - 1)) - (-1)) := by ring
  rw [key]
  exact dvd_add hres h2

/-- **Theorem `thm:richman`, first claim.**  For odd `q`, `A_w(q) ≡ -1 (mod q)`. -/
theorem richman_value {q : ℕ} (hq : Odd q) : (q : ℤ) ∣ Aw richmanW q + 1 := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  -- reduce to prime powers exactly dividing `q`
  by_cases hx : Aw richmanW q + 1 = 0
  · rw [hx]; exact dvd_zero _
  have hxa : (Aw richmanW q + 1).natAbs ≠ 0 := by simpa using hx
  suffices hn : q ∣ (Aw richmanW q + 1).natAbs by
    exact Int.natCast_dvd.mpr hn
  rw [← Nat.factorization_prime_le_iff_dvd hq0 hxa]
  intro p hp
  by_cases hpq : q.factorization p = 0
  · rw [hpq]; exact Nat.zero_le _
  have hpdvd : p ∣ q := (hp.dvd_iff_one_le_factorization hq0).mpr (by omega)
  set e := q.factorization p with he
  have hodd : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hq) (even_iff_two_dvd.mpr hpdvd)
  set b := q / p ^ e with hb
  have hqb : q = b * p ^ e := by
    rw [hb, Nat.div_mul_cancel (Nat.ordProj_dvd q p)]
  have hbodd : Odd b := by
    rw [hqb] at hq
    exact (Nat.odd_mul.mp hq).1
  have hpe : (p : ℤ) ^ e ∣ Aw richmanW (p ^ e) + 1 :=
    richman_prime_power hp hodd (by omega)
  have hit := Aw_iterated (p ^ e) (Nat.one_le_pow _ _ hp.pos) richmanW 0 b
  rw [zero_add, Aw_zero', one_mul, ← hqb] at hit
  push_cast at hit
  have hpow : (p : ℤ) ^ e ∣ Aw richmanW (p ^ e) ^ b - (-1) ^ b := by
    have := sub_dvd_pow_sub_pow (Aw richmanW (p ^ e)) (-1) b
    exact (by simpa using hpe : (p : ℤ) ^ e ∣ Aw richmanW (p ^ e) - (-1)).trans this
  rw [hbodd.neg_one_pow] at hpow
  have : (p : ℤ) ^ e ∣ Aw richmanW q + 1 := by
    exact dvd_of_eq' (dvd_add hit hpow) (by ring)
  have h3 : p ^ e ∣ (Aw richmanW q + 1).natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr this
    simpa [Int.natAbs_pow] using this
  exact (hp.pow_dvd_iff_le_factorization hxa).mp h3

/-- **Theorem `thm:richman`, second claim.**  For odd `q`, `A_w(n+q) ≡ -A_w(n) (mod q)`. -/
theorem richman_shift {q : ℕ} (hq : Odd q) (n : ℕ) :
    (q : ℤ) ∣ Aw richmanW (n + q) + Aw richmanW n := by
  have hq1 : 1 ≤ q := hq.pos
  have h1 := Aw_shift_mod q hq1 richmanW n
  have h2 := richman_value hq
  exact dvd_of_eq' (dvd_add h1 (h2.mul_left (Aw richmanW n))) (by ring)

/-- `A_w(n + j q) ≡ (-1)^j A_w(n) (mod q)` for odd `q`. -/
theorem richman_shift_iter {q : ℕ} (hq : Odd q) (n j : ℕ) :
    (q : ℤ) ∣ Aw richmanW (n + j * q) - (-1) ^ j * Aw richmanW n := by
  have h1 := Aw_iterated q hq.pos richmanW n j
  have h2 : (q : ℤ) ∣ Aw richmanW q ^ j - (-1) ^ j := by
    have := sub_dvd_pow_sub_pow (Aw richmanW q) (-1) j
    exact (by simpa using richman_value hq : (q : ℤ) ∣ Aw richmanW q - (-1)).trans this
  exact dvd_of_eq' (dvd_add h1 (h2.mul_left (Aw richmanW n))) (by ring)

/-- **Theorem `thm:richman` (Richman's conjecture).**  If `m ≡ n (mod q)` with `q` odd, then
`(-1)^m A_w(m) ≡ (-1)^n A_w(n) (mod q)`. -/
theorem richman_conjecture {q : ℕ} (hq : Odd q) {m n : ℕ} (hmn : m ≡ n [MOD q]) :
    (q : ℤ) ∣ (-1) ^ m * Aw richmanW m - (-1) ^ n * Aw richmanW n := by
  have key : ∀ n j : ℕ, (q : ℤ) ∣
      (-1) ^ (n + j * q) * Aw richmanW (n + j * q) - (-1) ^ n * Aw richmanW n := by
    intro n j
    have h := richman_shift_iter hq n j
    have hpar : ((-1 : ℤ)) ^ (n + j * q) = (-1) ^ n * (-1) ^ j := by
      rw [pow_add, mul_comm j q, pow_mul, hq.neg_one_pow]
    rw [hpar]
    have hsq : ((-1 : ℤ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; simp
    exact dvd_of_eq' (h.mul_left ((-1) ^ n * (-1) ^ j))
      (by linear_combination (-((-1 : ℤ) ^ n * Aw richmanW n)) * hsq)
  rcases le_total n m with h | h
  · obtain ⟨j, hj⟩ : q ∣ m - n := (Nat.modEq_iff_dvd' h).mp hmn.symm
    have hm : m = n + j * q := by
      have : m - n = q * j := hj
      rw [mul_comm]; omega
    subst hm
    exact key n j
  · obtain ⟨j, hj⟩ : q ∣ n - m := (Nat.modEq_iff_dvd' h).mp hmn
    have hm : n = m + j * q := by
      have : n - m = q * j := hj
      rw [mul_comm]; omega
    have := key m j
    rw [← hm] at this
    exact dvd_of_eq' ((dvd_neg).mpr this) (by ring)

end CongruenceTheory.Shift
