import Mathlib
import CongruenceTheoryHigherOrder.OddPrimePower

/-!
Copy of the proof of Part I's `power_of_two_residue` (`thm:power-of-two`, levels `r ≥ 4`):
`A_w(2^r) ≡ (w_1 + w_2)^(2^(r-1)) (mod 2^r)`.  It is repeated here, in the namespace
`CongruenceTheory.Shift`, because the pinned Part I dependency predates `PowerOfTwoResidue.lean`.
Only used for the `p = 2` case of eventual divisibility.
-/

namespace CongruenceTheory.Shift

open Finset MvPolynomial

/-- `A_w(n+1)` by the falling-factorial recurrence, evaluated at the weights `w`. -/
lemma Aw_succ (w : ℕ → ℤ) (n : ℕ) :
    Aw w (n + 1) = ∑ r ∈ range (n + 1), fall n r * (w (r + 1) * Aw w (n - r)) := by
  unfold Aw
  rw [C_succ, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [map_mul, map_intCast]

lemma Aw_zero (w : ℕ → ℤ) : Aw w 0 = 1 := by simp [Aw, C_zero]

lemma Aw_one (w : ℕ → ℤ) : Aw w 1 = w 1 := by
  rw [Aw_succ]; simp [fall, Aw_zero]

lemma Aw_two (w : ℕ → ℤ) : Aw w 2 = w 1 ^ 2 + w 2 := by
  rw [Aw_succ]
  simp [Finset.sum_range_succ, fall, Aw_one, Aw_zero]
  ring

lemma Aw_three (w : ℕ → ℤ) : Aw w 3 = w 1 ^ 3 + 3 * w 1 * w 2 + 2 * w 3 := by
  rw [Aw_succ]
  simp [Finset.sum_range_succ, fall, Aw_one, Aw_two, Aw_zero]
  ring

lemma Aw_four (w : ℕ → ℤ) :
    Aw w 4 = w 1 ^ 4 + 6 * w 1 ^ 2 * w 2 + 3 * w 2 ^ 2 + 8 * w 1 * w 3 + 6 * w 4 := by
  rw [Aw_succ]
  simp [Finset.sum_range_succ, fall, Aw_one, Aw_two, Aw_three, Aw_zero]
  ring

/-- `A_w(n+n)` is the `n + n`-point enumerator `AwPermSum w n`. -/
lemma Aw_two_mul_eq_AwPermSum (w : ℕ → ℤ) (n : ℕ) : Aw w (n + n) = AwPermSum w n := by
  have h : Fintype.card (Fin n ⊕ Fin n) = n + n := by simp
  rw [Aw_eq_AwPerm, AwPerm, AwPermSum, CpermSum, Cperm_eq_sum_of_card_eq h]

/-- **Corollary `cor:weighted`** in terms of the recurrence-native `A_w`:
`A_w(2^{s+1}) ≡ A_w(2^s)^2 (mod 2^{2s-1})`. -/
theorem Aw_two_adic (w : ℕ → ℤ) (s : ℕ) (hs : 1 ≤ s) :
    (2 : ℤ) ^ (2 * s - 1) ∣ Aw w (2 ^ (s + 1)) - Aw w (2 ^ s) * Aw w (2 ^ s) := by
  have h := AwPerm_two_adic_dynamics s hs w
  rw [Aw_eq_AwPerm w (2 ^ s)]
  have e : Aw w (2 ^ (s + 1)) = AwPermSum w (2 ^ s) := by
    rw [← Aw_two_mul_eq_AwPermSum]; congr 1; ring
  rw [e]; exact h

/-- Squaring gains one power of two: `x ≡ y (mod 2^r)` with `r ≥ 1` gives
`x^2 ≡ y^2 (mod 2^(r+1))`. -/
lemma sq_congr_two {x y : ℤ} {r : ℕ} (hr : 1 ≤ r) (h : (2 : ℤ) ^ r ∣ x - y) :
    (2 : ℤ) ^ (r + 1) ∣ x ^ 2 - y ^ 2 := by
  obtain ⟨k, hk⟩ := h
  have h2 : (2 : ℤ) ∣ x - y := by
    refine ⟨2 ^ (r - 1) * k, ?_⟩
    rw [hk]
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    simp [pow_succ]; ring
  obtain ⟨j, hj⟩ := h2
  have hsum : x + y = 2 * (y + j) := by linarith
  refine ⟨k * (y + j), ?_⟩
  have : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by ring
  rw [this, hk, hsum, pow_succ]; ring

/-! ### The theorem -/

lemma dvd_of_zmod_zero {n : ℕ} [NeZero n] {x : ℤ} (h : ((x : ℤ) : ZMod n) = 0) :
    (n : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd x n).mp h

lemma aux_r1 (a b : ℤ) : (2 : ℤ) ∣ (a ^ 2 + b) - (a + b) := by
  have : (((a ^ 2 + b) - (a + b) : ℤ) : ZMod 2) = 0 := by
    push_cast
    generalize (a : ZMod 2) = x
    generalize (b : ZMod 2) = y
    revert x y; decide
  exact_mod_cast dvd_of_zmod_zero this

lemma aux_r2 (a b c d : ℤ) :
    (4 : ℤ) ∣ (a ^ 4 + 6 * a ^ 2 * b + 3 * b ^ 2 + 8 * a * c + 6 * d)
      - ((a + b) ^ 2 + 2 * (b + d)) := by
  have : ((((a ^ 4 + 6 * a ^ 2 * b + 3 * b ^ 2 + 8 * a * c + 6 * d)
      - ((a + b) ^ 2 + 2 * (b + d)) : ℤ)) : ZMod 4) = 0 := by
    push_cast
    generalize (a : ZMod 4) = x
    generalize (b : ZMod 4) = y
    generalize (c : ZMod 4) = z
    generalize (d : ZMod 4) = t
    revert x y z t; decide
  exact_mod_cast dvd_of_zmod_zero this

lemma aux_r4 (a b : ℤ) : (16 : ℤ) ∣ (a ^ 4 + 4 * a ^ 2 * b + 4 * b ^ 2) ^ 2 - a ^ 8 := by
  have : ((((a ^ 4 + 4 * a ^ 2 * b + 4 * b ^ 2) ^ 2 - a ^ 8 : ℤ)) : ZMod 16) = 0 := by
    push_cast
    generalize (a : ZMod 16) = x
    generalize (b : ZMod 16) = y
    revert x y; decide
  exact_mod_cast dvd_of_zmod_zero this

/-- Level `r = 1`: `A_w(2) ≡ w₁ + w₂ (mod 2)`. -/
theorem power_of_two_r1 (w : ℕ → ℤ) : (2 : ℤ) ∣ Aw w 2 - (w 1 + w 2) := by
  rw [Aw_two]; exact aux_r1 _ _

/-- Level `r = 2`: `A_w(4) ≡ α² + 2β (mod 4)`. -/
theorem power_of_two_r2 (w : ℕ → ℤ) :
    (4 : ℤ) ∣ Aw w 4 - ((w 1 + w 2) ^ 2 + 2 * (w 2 + w 4)) := by
  rw [Aw_four]; exact aux_r2 _ _ _ _

/-- Level `r = 3`: `A_w(8) ≡ α⁴ + 4α²β + 4β² (mod 8)`. -/
theorem power_of_two_r3 (w : ℕ → ℤ) :
    (8 : ℤ) ∣ Aw w 8 - ((w 1 + w 2) ^ 4 + 4 * (w 1 + w 2) ^ 2 * (w 2 + w 4)
      + 4 * (w 2 + w 4) ^ 2) := by
  have h1 : (8 : ℤ) ∣ Aw w 8 - Aw w 4 * Aw w 4 := by
    simpa using Aw_two_adic w 2 (by norm_num)
  have h2 : (2 : ℤ) ^ 2 ∣ Aw w 4 - ((w 1 + w 2) ^ 2 + 2 * (w 2 + w 4)) := by
    simpa using power_of_two_r2 w
  have h3 : (8 : ℤ) ∣ Aw w 4 ^ 2 - ((w 1 + w 2) ^ 2 + 2 * (w 2 + w 4)) ^ 2 := by
    simpa using sq_congr_two (by norm_num : 1 ≤ 2) h2
  have key : Aw w 8 - ((w 1 + w 2) ^ 4 + 4 * (w 1 + w 2) ^ 2 * (w 2 + w 4)
      + 4 * (w 2 + w 4) ^ 2)
      = (Aw w 8 - Aw w 4 * Aw w 4)
        + (Aw w 4 ^ 2 - ((w 1 + w 2) ^ 2 + 2 * (w 2 + w 4)) ^ 2) := by ring
  rw [key]; exact dvd_add h1 h3

/-- Level `r = 4`: `A_w(16) ≡ α⁸ (mod 16)`. -/
theorem power_of_two_r4 (w : ℕ → ℤ) : (16 : ℤ) ∣ Aw w 16 - (w 1 + w 2) ^ 8 := by
  have h1 : (16 : ℤ) ∣ Aw w 16 - Aw w 8 * Aw w 8 := by
    have := Aw_two_adic w 3 (by norm_num)
    have h32 : (16 : ℤ) ∣ (2 : ℤ) ^ (2 * 3 - 1) := by norm_num
    simpa using dvd_trans h32 this
  have h2 : (2 : ℤ) ^ 3 ∣ Aw w 8 - ((w 1 + w 2) ^ 4 + 4 * (w 1 + w 2) ^ 2 * (w 2 + w 4)
      + 4 * (w 2 + w 4) ^ 2) := by simpa using power_of_two_r3 w
  have h3 : (16 : ℤ) ∣ Aw w 8 ^ 2 - ((w 1 + w 2) ^ 4 + 4 * (w 1 + w 2) ^ 2 * (w 2 + w 4)
      + 4 * (w 2 + w 4) ^ 2) ^ 2 := by
    simpa using sq_congr_two (by norm_num : 1 ≤ 3) h2
  have h4 := aux_r4 (w 1 + w 2) (w 2 + w 4)
  have key : Aw w 16 - (w 1 + w 2) ^ 8
      = (Aw w 16 - Aw w 8 * Aw w 8)
        + (Aw w 8 ^ 2 - ((w 1 + w 2) ^ 4 + 4 * (w 1 + w 2) ^ 2 * (w 2 + w 4)
          + 4 * (w 2 + w 4) ^ 2) ^ 2)
        + (((w 1 + w 2) ^ 4 + 4 * (w 1 + w 2) ^ 2 * (w 2 + w 4)
          + 4 * (w 2 + w 4) ^ 2) ^ 2 - (w 1 + w 2) ^ 8) := by ring
  rw [key]; exact dvd_add (dvd_add h1 h3) h4

/-- **Theorem `thm:power-of-two`, levels `r ≥ 4`:**
`A_w(2^r) ≡ (w₁ + w₂)^(2^(r-1)) (mod 2^r)`. -/
theorem power_of_two_residue_local (w : ℕ → ℤ) :
    ∀ r : ℕ, 4 ≤ r → (2 : ℤ) ^ r ∣ Aw w (2 ^ r) - (w 1 + w 2) ^ (2 ^ (r - 1)) := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => simpa using power_of_two_r4 w
  | succ r hr ih =>
    have h1 := Aw_two_adic w r (by omega)
    have h2 := sq_congr_two (by omega : 1 ≤ r) ih
    have hle : (2 : ℤ) ^ (r + 1) ∣ (2 : ℤ) ^ (2 * r - 1) :=
      pow_dvd_pow 2 (by omega)
    have h1' := dvd_trans hle h1
    have e : (w 1 + w 2) ^ (2 ^ (r + 1 - 1)) = ((w 1 + w 2) ^ (2 ^ (r - 1))) ^ 2 := by
      rw [← pow_mul]
      congr 1
      obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      simp [pow_succ]
    rw [e]
    have key : Aw w (2 ^ (r + 1)) - ((w 1 + w 2) ^ (2 ^ (r - 1))) ^ 2
        = (Aw w (2 ^ (r + 1)) - Aw w (2 ^ r) * Aw w (2 ^ r))
          + (Aw w (2 ^ r) ^ 2 - ((w 1 + w 2) ^ (2 ^ (r - 1))) ^ 2) := by ring
    rw [key]; exact dvd_add h1' h2

end CongruenceTheory.Shift
