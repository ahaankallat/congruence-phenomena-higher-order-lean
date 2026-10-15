import Mathlib
import CongruenceTheory.Universal
import CongruenceTheory.WeightedSpecialization

/-!
**The shift congruence with weights in `Z_(p)`** (main paper, the remark following
Theorem `thm:universal`: "For a prime-power modulus `p^e` the proofs apply verbatim to weights in
`Z_(p)`, since the polynomial congruences hold in `Z[X_1,X_2,...]`").

For rational weights `w : ℕ → ℚ` put `A_w(n) = C_n(w)`, the evaluation of the universal
cycle-index polynomial `C_n ∈ Z[X_1,X_2,...]` at `X_m = w_m` (`Awq`).  For integer weights this
is `Aw` (`Awq_int`).  We say a rational `y` lies in `Z_(p)` when `padicNorm p y ≤ 1`.

* `padicNorm_aeval_le_one`: a polynomial with integer coefficients, evaluated at weights in
  `Z_(p)`, lies in `Z_(p)`.
* `shift_congruence_Zp`: for `k ≥ 1`, `A_w(n+k) - A_w(n) A_w(k) ∈ k Z_(p)` (the statement
  "`v_p(A_w(n+k) - A_w(n)A_w(k)) ≥ v_p(k)`" in the form `padicNorm_shift_le`).  This holds for
  every `k ≥ 1`, in particular for powers of `p`.
* `shift_congruence_lcm_Zp`: the `lcm(n,k)` form, `A_w(n+k) - A_w(n) A_w(k) ∈ lcm(n,k) Z_(p)`.
-/

namespace CongruenceTheory.ZpShift

open MvPolynomial

/-- `A_w(n) = C_n(w)` for rational weights. -/
noncomputable def Awq (w : ℕ → ℚ) (n : ℕ) : ℚ := MvPolynomial.aeval w (CongruenceTheory.C n)

/-- For integer weights, `Awq` is the cast of `Aw`. -/
theorem Awq_int (w : ℕ → ℤ) (n : ℕ) :
    Awq (fun m => (w m : ℚ)) n = ((CongruenceTheory.Aw w n : ℤ) : ℚ) := by
  unfold Awq CongruenceTheory.Aw
  have h := MvPolynomial.eval₂_comp_left (Int.castRingHom ℚ) (RingHom.id ℤ) w
    (CongruenceTheory.C n)
  simp only [RingHom.comp_id] at h
  rw [MvPolynomial.aeval_def, algebraMap_int_eq]
  rw [MvPolynomial.eval]
  exact h.symm

/-- A polynomial with integer coefficients, evaluated at weights in `Z_(p)`, lies in `Z_(p)`. -/
theorem padicNorm_aeval_le_one {p : ℕ} [Fact p.Prime] (w : ℕ → ℚ)
    (hw : ∀ m, padicNorm p (w m) ≤ 1) (P : MvPolynomial ℕ ℤ) :
    padicNorm p (MvPolynomial.aeval w P) ≤ 1 := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C]
    simpa using padicNorm.of_int (p := p) a
  | add P Q hP hQ =>
    rw [map_add]
    exact (padicNorm.nonarchimedean).trans (max_le hP hQ)
  | mul_X P n hP =>
    rw [map_mul, MvPolynomial.aeval_X, padicNorm.mul]
    exact mul_le_one₀ hP (padicNorm.nonneg _) (hw n)

/-- Coefficientwise divisibility by `m` passes to evaluations at weights in `Z_(p)`:
the value lies in `m Z_(p)`. -/
theorem aeval_mem_of_dvdCoeffs {p : ℕ} [Fact p.Prime] (w : ℕ → ℚ)
    (hw : ∀ m, padicNorm p (w m) ≤ 1) {m : ℕ} {P : MvPolynomial ℕ ℤ}
    (hP : ∀ d, (m : ℤ) ∣ MvPolynomial.coeff d P) :
    ∃ y : ℚ, padicNorm p y ≤ 1 ∧ MvPolynomial.aeval w P = (m : ℚ) * y := by
  obtain ⟨Q, hQ⟩ := (MvPolynomial.C_dvd_iff_dvd_coeff (m : ℤ) P).mpr hP
  refine ⟨MvPolynomial.aeval w Q, padicNorm_aeval_le_one w hw Q, ?_⟩
  rw [hQ, map_mul, MvPolynomial.aeval_C]
  simp

/-- **Shift congruence with weights in `Z_(p)`.**  For a prime `p`, weights `w_m ∈ Z_(p)` and every
`k ≥ 1`, `A_w(n+k) - A_w(n) A_w(k) ∈ k Z_(p)`. -/
theorem shift_congruence_Zp {p : ℕ} [Fact p.Prime] (w : ℕ → ℚ)
    (hw : ∀ m, padicNorm p (w m) ≤ 1) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    ∃ y : ℚ, padicNorm p y ≤ 1 ∧ Awq w (n + k) - Awq w n * Awq w k = (k : ℚ) * y := by
  have hD : CongruenceTheory.DvdCoeffs k
      (CongruenceTheory.C (n + k) - CongruenceTheory.C k * CongruenceTheory.C n) :=
    CongruenceTheory.dvdCoeffs_of_map_eq_zero (by
      rw [map_sub, map_mul]
      exact sub_eq_zero.mpr (CongruenceTheory.universal_shift_mod k hk n))
  obtain ⟨y, hy, hyeq⟩ := aeval_mem_of_dvdCoeffs (p := p) w hw hD
  refine ⟨y, hy, ?_⟩
  rw [map_sub, map_mul] at hyeq
  unfold Awq
  rw [← hyeq]
  ring

/-- **The `lcm` form.**  For `n, k ≥ 1`, `A_w(n+k) - A_w(n) A_w(k) ∈ lcm(n,k) Z_(p)`. -/
theorem shift_congruence_lcm_Zp {p : ℕ} [Fact p.Prime] (w : ℕ → ℚ)
    (hw : ∀ m, padicNorm p (w m) ≤ 1) {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∃ y : ℚ, padicNorm p y ≤ 1 ∧
      Awq w (n + k) - Awq w n * Awq w k = ((Nat.lcm n k : ℕ) : ℚ) * y := by
  obtain ⟨y, hy, hyeq⟩ := aeval_mem_of_dvdCoeffs (p := p) w hw
    (CongruenceTheory.universal_shift_lcm n k hn hk)
  refine ⟨y, hy, ?_⟩
  rw [map_sub, map_mul] at hyeq
  exact hyeq

/-- The valuation form of `shift_congruence_Zp`:
`|A_w(n+k) - A_w(n) A_w(k)|_p ≤ |k|_p`, i.e. `v_p(A_w(n+k) - A_w(n)A_w(k)) ≥ v_p(k)`. -/
theorem padicNorm_shift_le {p : ℕ} [Fact p.Prime] (w : ℕ → ℚ)
    (hw : ∀ m, padicNorm p (w m) ≤ 1) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    padicNorm p (Awq w (n + k) - Awq w n * Awq w k) ≤ padicNorm p (k : ℚ) := by
  obtain ⟨y, hy, hyeq⟩ := shift_congruence_Zp w hw hk n
  rw [hyeq, padicNorm.mul]
  exact mul_le_of_le_one_right (padicNorm.nonneg _) hy

/-- In particular, for `k = p^r`. -/
theorem shift_congruence_Zp_pow {p : ℕ} [Fact p.Prime] (w : ℕ → ℚ)
    (hw : ∀ m, padicNorm p (w m) ≤ 1) (r n : ℕ) :
    ∃ y : ℚ, padicNorm p y ≤ 1 ∧
      Awq w (n + p ^ r) - Awq w n * Awq w (p ^ r) = ((p : ℚ) ^ r) * y := by
  have hk : 1 ≤ p ^ r := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  obtain ⟨y, hy, h⟩ := shift_congruence_Zp (p := p) w hw hk n
  exact ⟨y, hy, by rw [h]; push_cast; ring⟩

end CongruenceTheory.ZpShift
