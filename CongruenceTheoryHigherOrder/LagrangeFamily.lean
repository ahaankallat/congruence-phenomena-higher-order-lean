import Mathlib
import CongruenceTheory.WeightedSpecialization

/-!
**Lagrange-type integrality** (Part I, `thm:lagrange`, `lem:a-k-mod-k`, `cor:n-n-1`).
-/

open PowerSeries

namespace LagrangeFamily

section FixedPoint

variable {R : Type*} [CommRing R]

/-- Coefficients of a series `T` agreeing modulo `X^(n+1)` give the same coefficient `n` of
`F.subst T`. -/
theorem coeff_subst_congr (F A B : R⟦X⟧) (hA : constantCoeff A = 0) (hB : constantCoeff B = 0)
    (n : ℕ) (h : (X : R⟦X⟧) ^ (n + 1) ∣ A - B) :
    coeff n (F.subst A) = coeff n (F.subst B) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hA),
    coeff_subst' (HasSubst.of_constantCoeff_zero' hB)]
  refine finsum_congr fun d => ?_
  obtain ⟨Q, hQ⟩ := h.trans (sub_dvd_pow_sub_pow A B d)
  rw [sub_eq_iff_eq_add.mp hQ]
  simp [coeff_X_pow_mul']

/-- Coefficients of the solution of `T = X * F(T)`. -/
noncomputable def fpFun (F : R⟦X⟧) : ℕ → R
  | 0 => 0
  | n + 1 => coeff n (F.subst (∑ i : Fin (n + 1), C (fpFun F i.1) * X ^ i.1))

theorem exists_fixedPoint (F : R⟦X⟧) :
    ∃ T : R⟦X⟧, constantCoeff T = 0 ∧ T = X * F.subst T := by
  set T : R⟦X⟧ := PowerSeries.mk (fpFun F) with hTdef
  have hT0 : constantCoeff T = 0 := by simp [hTdef, fpFun]
  have key : ∀ n, coeff (n + 1) T = coeff n (F.subst T) := by
    intro n
    set P : R⟦X⟧ := ∑ i : Fin (n + 1), C (fpFun F i.1) * X ^ i.1 with hP
    have hP0 : constantCoeff P = 0 := by
      rw [hP, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases i with ⟨_ | j, hj⟩
      · simp [fpFun]
      · simp
    have hdvd : (X : R⟦X⟧) ^ (n + 1) ∣ T - P := by
      rw [X_pow_dvd_iff]
      intro m hm
      simp +contextual [hP, hTdef, coeff_X_pow, Finset.sum_eq_single (⟨m, hm⟩ : Fin (n + 1)),
        Fin.ext_iff, @eq_comm _ m]
    have h1 := coeff_subst_congr F T P hT0 hP0 n hdvd
    rw [h1]
    simp [hTdef, fpFun, hP]
  refine ⟨T, hT0, ?_⟩
  ext n
  cases n with
  | zero => simp [hT0]
  | succ n => rw [coeff_succ_X_mul, key]

end FixedPoint

section Lagrange

open scoped PowerSeries in
/-- `H = H(0) + X * K`. -/
theorem exists_decomp (H : ℚ⟦X⟧) : ∃ K : ℚ⟦X⟧, H = PowerSeries.C (constantCoeff H) + X * K :=
  ⟨PowerSeries.mk fun n => coeff (n + 1) H, by
    ext n
    cases n <;> simp⟩

theorem subst_decomp {T : ℚ⟦X⟧} (hS : HasSubst T) (H K : ℚ⟦X⟧)
    (hK : H = PowerSeries.C (constantCoeff H) + X * K) :
    H.subst T = PowerSeries.C (constantCoeff H) + T * K.subst T := by
  conv_lhs => rw [hK]
  rw [subst_add hS, subst_mul hS, subst_X hS, subst_C]
  rfl

theorem coeff_derivative_pow (F : ℚ⟦X⟧) (n : ℕ) :
    coeff n (derivative ℚ F * F ^ n) = coeff (n + 1) (F ^ (n + 1)) := by
  have h := coeff_derivative (R := ℚ) (F ^ (n + 1)) n
  rw [derivative_pow] at h
  have h2 : coeff n (((n + 1 : ℕ) : ℚ⟦X⟧) * F ^ n * derivative ℚ F)
      = coeff n (derivative ℚ F * F ^ n) * ((n : ℚ) + 1) := by
    rw [show ((n + 1 : ℕ) : ℚ⟦X⟧) * F ^ n * derivative ℚ F
      = PowerSeries.C ((n : ℚ) + 1) * (derivative ℚ F * F ^ n) by
        simp only [map_add, map_natCast, map_one]; push_cast; ring]
    rw [coeff_C_mul]; ring
  simp only [Nat.add_sub_cancel] at h
  rw [h2] at h
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  exact mul_right_cancel₀ hn h

/-- **Lagrange inversion, second form** (Gessel, Thm 2.1.1), over `ℚ`:
if `T = X F(T)` and `u = 1/(1 - X F'(T))`, then `[y^n] H(T) u = [x^n] H F^n`. -/
theorem lagrange_second (F T u : ℚ⟦X⟧) (hT0 : constantCoeff T = 0) (hT : T = X * F.subst T)
    (hu : u * (1 - X * (derivative ℚ F).subst T) = 1) :
    ∀ (n : ℕ) (H : ℚ⟦X⟧), coeff n (H.subst T * u) = coeff n (H * F ^ n) := by
  have hS : HasSubst T := HasSubst.of_constantCoeff_zero' hT0
  have hu0 : constantCoeff u = 1 := by
    have := congrArg constantCoeff hu
    simpa [hT0] using this
  have hu1 : u = 1 + X * ((derivative ℚ F).subst T * u) := by linear_combination hu
  intro n
  induction n with
  | zero =>
    intro H
    obtain ⟨K, hK⟩ := exists_decomp H
    rw [subst_decomp hS H K hK, coeff_zero_eq_constantCoeff]
    simp [hT0, hu0]
  | succ n ih =>
    intro H
    obtain ⟨K, hK⟩ := exists_decomp H
    have e1 : H.subst T * u = PowerSeries.C (constantCoeff H) * u
        + X * ((F * K).subst T * u) := by
      rw [subst_decomp hS H K hK, subst_mul hS]
      have : T * K.subst T = X * (F.subst T * K.subst T) := by
        calc T * K.subst T = (X * F.subst T) * K.subst T := by rw [← hT]
          _ = _ := by ring
      rw [this]; ring
    have e2 : H * F ^ (n + 1) = PowerSeries.C (constantCoeff H) * F ^ (n + 1)
        + X * (F * K * F ^ n) := by
      conv_lhs => rw [hK]
      ring
    rw [e1, e2, map_add, map_add, coeff_C_mul, coeff_C_mul, coeff_succ_X_mul, coeff_succ_X_mul,
      ih (F * K)]
    congr 2
    conv_lhs => rw [hu1]
    rw [map_add, coeff_succ_X_mul, ih, coeff_derivative_pow]
    simp

end Lagrange

section AwRecurrence

open Finset in
theorem fall_cast_mul_factorial (n r : ℕ) (hr : r ≤ n) :
    (CongruenceTheory.fall n r : ℚ) * ((n - r).factorial : ℚ) = (n.factorial : ℚ) := by
  have h1 : CongruenceTheory.fall n r = (n.descFactorial r : ℤ) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [CongruenceTheory.fall_succ, ih (by omega), Nat.descFactorial_succ]
      push_cast [Nat.cast_sub (show r ≤ n by omega)]
      ring
  rw [h1]
  have := Nat.factorial_mul_descFactorial hr
  have h2 : (((n - r).factorial * n.descFactorial r : ℕ) : ℚ) = (n.factorial : ℚ) := by
    exact_mod_cast this
  push_cast at h2 ⊢
  rw [← h2]; ring

theorem Aw_succ_cast (w : ℕ → ℤ) (n : ℕ) :
    ((CongruenceTheory.Aw w (n + 1) : ℤ) : ℚ) =
      ∑ r ∈ Finset.range (n + 1), (CongruenceTheory.fall n r : ℚ) *
        ((w (r + 1) : ℚ) * (CongruenceTheory.Aw w (n - r) : ℚ)) := by
  unfold CongruenceTheory.Aw
  rw [CongruenceTheory.C_succ]
  simp [map_sum]

theorem Aw_eq_of_ode (w : ℕ → ℤ) (hw0 : w 0 = 0) (B : ℚ⟦X⟧) (hB0 : constantCoeff B = 1)
    (h : X * derivative ℚ B = PowerSeries.mk (fun m => (w m : ℚ)) * B) :
    ∀ n, ((CongruenceTheory.Aw w n : ℤ) : ℚ) = (n.factorial : ℚ) * coeff n B := by
  have hrec : ∀ n : ℕ, ((n : ℚ) + 1) * coeff (n + 1) B =
      ∑ r ∈ Finset.range (n + 1), (w (r + 1) : ℚ) * coeff (n - r) B := by
    intro n
    have := congrArg (coeff (n + 1)) h
    rw [coeff_succ_X_mul, coeff_derivative, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ'] at this
    simp only [coeff_mk, hw0, Int.cast_zero, zero_mul, add_zero, Nat.add_sub_add_right] at this
    rw [mul_comm]; exact this
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      have : CongruenceTheory.Aw w 0 = 1 := by simp [CongruenceTheory.Aw, CongruenceTheory.C_zero]
      simp [this, hB0]
    | succ n =>
      rw [Aw_succ_cast]
      have hsum : ∀ r ∈ Finset.range (n + 1),
          (CongruenceTheory.fall n r : ℚ) * ((w (r + 1) : ℚ) * (CongruenceTheory.Aw w (n - r) : ℚ))
          = (n.factorial : ℚ) * ((w (r + 1) : ℚ) * coeff (n - r) B) := by
        intro r hr
        have hr' : r ≤ n := by simpa [Nat.lt_succ_iff] using hr
        rw [ih (n - r) (by omega)]
        have := fall_cast_mul_factorial n r hr'
        calc (CongruenceTheory.fall n r : ℚ) * ((w (r + 1) : ℚ) *
              ((((n - r).factorial : ℕ) : ℚ) * coeff (n - r) B))
            = ((CongruenceTheory.fall n r : ℚ) * ((n - r).factorial : ℚ)) *
              ((w (r + 1) : ℚ) * coeff (n - r) B) := by ring
          _ = _ := by rw [this]
      rw [Finset.sum_congr rfl hsum, ← Finset.mul_sum, ← hrec n, Nat.factorial_succ]
      push_cast
      ring

end AwRecurrence

section Main

/-- The coefficient ring map `ℤ → ℚ`. -/
abbrev toQ : ℤ →+* ℚ := Int.castRingHom ℚ

/-- `exp (x G(x))` as a series over `ℚ`. -/
noncomputable def Hseries (G : ℤ⟦X⟧) : ℚ⟦X⟧ := (exp ℚ).subst (X * G.map toQ)

/-- `b(n) = n! [x^n] exp(x G(x)) F(x)^n`, as a rational number. -/
noncomputable def bq (F G : ℤ⟦X⟧) (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * coeff n (Hseries G * (F.map toQ) ^ n)

/-- `θ(y) = y F'(x(y))`. -/
noncomputable def theta (F T : ℤ⟦X⟧) : ℤ⟦X⟧ := X * (derivative ℤ F).subst T

/-- `1 / (1 - θ)` over `ℤ`. -/
noncomputable def lagInv (F T : ℤ⟦X⟧) : ℤ⟦X⟧ := invOfUnit (1 - theta F T) 1

/-- `∑ w_m y^m = y d/dy (x G(x)) + y θ' / (1 - θ)`, with `x = T(y)`. -/
noncomputable def lagWSeries (F G T : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  X * derivative ℤ ((X * G).subst T) + X * (derivative ℤ (theta F T) * lagInv F T)

/-- The integral weights `w_m` of `thm:lagrange`. -/
noncomputable def lagW (F G T : ℤ⟦X⟧) (m : ℕ) : ℤ := coeff m (lagWSeries F G T)

theorem constantCoeff_mapQ (f : ℤ⟦X⟧) : constantCoeff (f.map toQ) = toQ (constantCoeff f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]

theorem map_subst' {T : ℤ⟦X⟧} (hS : HasSubst T) (f : ℤ⟦X⟧) :
    PowerSeries.map toQ (f.subst T) = (f.map toQ).subst (T.map toQ) := map_subst hS f

theorem map_derivative (f : ℤ⟦X⟧) : (derivative ℤ f).map toQ = derivative ℚ (f.map toQ) := by
  ext n; simp [coeff_derivative]

/-- **Theorem `thm:lagrange`, identification of `b` with `A_w`.**  If `T = X F(T)` (with `T(0) = 0`)
then `b(n) = A_w(n)` for the integral weights `w = lagW F G T`. -/
theorem lagrange_family (F G T : ℤ⟦X⟧) (hT0 : constantCoeff T = 0) (hT : T = X * F.subst T)
    (n : ℕ) : ((CongruenceTheory.Aw (lagW F G T) n : ℤ) : ℚ) = bq F G n := by
  have hS : HasSubst T := HasSubst.of_constantCoeff_zero' hT0
  set Fq : ℚ⟦X⟧ := F.map toQ with hFq
  set Gq : ℚ⟦X⟧ := G.map toQ with hGq
  set Tq : ℚ⟦X⟧ := T.map toQ with hTq
  have hTq0 : constantCoeff Tq = 0 := by rw [hTq, constantCoeff_mapQ, hT0]; simp
  have hSq : HasSubst Tq := HasSubst.of_constantCoeff_zero' hTq0
  have hTqe : Tq = X * Fq.subst Tq := by
    have := congrArg (PowerSeries.map toQ) hT
    rw [map_mul, map_subst' hS] at this
    simpa using this
  set P : ℚ⟦X⟧ := X * Gq with hP
  have hP0 : HasSubst P := HasSubst.of_constantCoeff_zero' (by simp [hP])
  set θ : ℤ⟦X⟧ := theta F T with hθ
  have hθ0 : constantCoeff θ = 0 := by simp [hθ, theta]
  have huz : (1 - θ) * lagInv F T = 1 := by
    apply mul_invOfUnit
    simp [hθ0]
  set θq : ℚ⟦X⟧ := θ.map toQ with hθq
  have hθqe : θq = X * (derivative ℚ Fq).subst Tq := by
    simp only [hθq, hθ, theta, map_mul, map_X]
    rw [map_subst' hS, map_derivative]
  set uq : ℚ⟦X⟧ := (lagInv F T).map toQ with huq
  have hu1 : uq * (1 - θq) = 1 := by
    have := congrArg (PowerSeries.map toQ) huz
    simp only [map_mul, map_sub, map_one] at this
    rw [mul_comm]; exact this
  have hu : uq * (1 - X * (derivative ℚ Fq).subst Tq) = 1 := by rw [← hθqe]; exact hu1
  set S : ℚ⟦X⟧ := (Hseries G).subst Tq with hSdef
  set B : ℚ⟦X⟧ := S * uq with hB
  have hBcoef := lagrange_second Fq Tq uq hTq0 hTqe hu
  -- derivative of `H`
  have hdH : derivative ℚ (Hseries G) = Hseries G * derivative ℚ P := by
    unfold Hseries
    rw [← hGq, ← hP, derivative_subst ℚ hP0, derivative_exp]
  have hPT : derivative ℚ (P.subst Tq) = (derivative ℚ P).subst Tq * derivative ℚ Tq :=
    derivative_subst ℚ hSq
  have hdS : derivative ℚ S = S * derivative ℚ (P.subst Tq) := by
    rw [hSdef, derivative_subst ℚ hSq, hdH, subst_mul hSq, hPT]
    ring
  have hdu : derivative ℚ uq = uq ^ 2 * derivative ℚ θq := by
    have e1 : derivative ℚ (uq * (1 - θq)) = 0 := by rw [hu1]; simp
    simp only [Derivation.leibniz, smul_eq_mul, map_sub, Derivation.map_one_eq_zero] at e1
    linear_combination uq * e1 - (derivative ℚ uq) * hu1
  have hode : X * derivative ℚ B = PowerSeries.mk (fun m => ((lagW F G T m : ℤ) : ℚ)) * B := by
    have hW : PowerSeries.mk (fun m => ((lagW F G T m : ℤ) : ℚ))
        = X * derivative ℚ (P.subst Tq) + X * (derivative ℚ θq * uq) := by
      have hmap : (lagWSeries F G T).map toQ
          = X * derivative ℚ (P.subst Tq) + X * (derivative ℚ θq * uq) := by
        simp only [lagWSeries, map_add, map_mul, map_X, ← hθ]
        rw [map_derivative, map_derivative, map_subst' hS]
        simp [hP, hGq, hTq, hθq, huq]
      rw [← hmap]
      ext m
      simp [lagW, coeff_map]
    rw [hW, hB, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hdS, hdu]
    ring
  have hB0 : constantCoeff B = 1 := by
    have hHs0 : constantCoeff (Hseries G) = 1 := by
      obtain ⟨K, hK⟩ := exists_decomp (exp ℚ)
      have := subst_decomp hP0 _ K hK
      unfold Hseries
      rw [← hGq, ← hP, this]
      simp [hP]
    have h1 : coeff 0 B = coeff 0 (Hseries G * Fq ^ 0) := hBcoef 0 _
    rw [pow_zero, mul_one, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply] at h1
    rw [h1, hHs0]
  have := Aw_eq_of_ode (lagW F G T) (by simp [lagW, lagWSeries]) B hB0 hode n
  have h2 : coeff n B = coeff n (Hseries G * Fq ^ n) := hBcoef n _
  rw [this, h2]
  rfl

end Main

section Congruence

/-- `e_i = i! [x^i] exp(x G(x))`, as an explicit integer:
`e_i = ∑_{l ≤ i} (i!/l!) [x^{i-l}] G^l`. -/
noncomputable def eInt (G : ℤ⟦X⟧) (i : ℕ) : ℤ :=
  ∑ l ∈ Finset.range (i + 1), (i.descFactorial (i - l) : ℤ) * coeff (i - l) (G ^ l)

theorem cast_eInt (G : ℤ⟦X⟧) (i : ℕ) :
    (eInt G i : ℚ) = (i.factorial : ℚ) * coeff i (Hseries G) := by
  set Gq : ℚ⟦X⟧ := G.map toQ with hGq
  set P : ℚ⟦X⟧ := X * Gq with hP
  have hP0 : HasSubst P := HasSubst.of_constantCoeff_zero' (by simp [hP])
  have hterm : ∀ d : ℕ, coeff d (exp ℚ) • coeff i (P ^ d)
      = if d ≤ i then (1 / (d.factorial : ℚ)) * coeff (i - d) (Gq ^ d) else 0 := by
    intro d
    rw [coeff_exp, hP, mul_pow, coeff_X_pow_mul', smul_eq_mul]
    split_ifs <;> simp
  unfold Hseries
  rw [← hGq, ← hP, coeff_subst' hP0]
  simp_rw [hterm]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (i + 1))]
  · rw [Finset.mul_sum, eInt]
    push_cast
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ i := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hl
    rw [if_pos hl']
    have h1 : ((i - (i - l)).factorial : ℚ) * (i.descFactorial (i - l) : ℚ)
        = (i.factorial : ℚ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial (show i - l ≤ i by omega)
    rw [show i - (i - l) = l by omega] at h1
    have h2 : coeff (i - l) (Gq ^ l) = ((coeff (i - l) (G ^ l) : ℤ) : ℚ) := by
      rw [hGq, ← map_pow, coeff_map]; rfl
    rw [h2, ← h1]
    have : (l.factorial : ℚ) ≠ 0 := by positivity
    field_simp
  · intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hd (by rw [if_neg (by omega)])

theorem eInt_dvd_pow (G : ℤ⟦X⟧) (k : ℕ) (hk : 1 ≤ k) :
    (k : ℤ) ∣ eInt G k - constantCoeff G ^ k := by
  unfold eInt
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, Nat.descFactorial_zero, Nat.cast_one, one_mul]
  have h0 : coeff 0 (G ^ k) = constantCoeff G ^ k := by
    rw [coeff_zero_eq_constantCoeff_apply, map_pow]
  rw [h0, add_sub_cancel_right]
  refine Finset.dvd_sum fun l hl => ?_
  have hl' : l < k := Finset.mem_range.mp hl
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, m + 1 - l = j + 1 := ⟨m - l, by omega⟩
  rw [hj, Nat.succ_descFactorial_succ]
  push_cast
  exact Dvd.dvd.mul_right (Dvd.intro _ rfl) _

/-- The common integrality/divisibility core: for `P ∈ ℤ[[x]]` and `k ≥ 1`,
`k! [x^k] exp(xG) P` is an integer congruent to `e_k P(0)` modulo `k`. -/
theorem coeff_mul_Hseries (G P : ℤ⟦X⟧) (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℤ, (c : ℚ) = (k.factorial : ℚ) * coeff k (Hseries G * P.map toQ) ∧
      (k : ℤ) ∣ c - eInt G k * constantCoeff P := by
  refine ⟨∑ j ∈ Finset.range (k + 1), (k.descFactorial j : ℤ) * eInt G (k - j) * coeff j P,
    ?_, ?_⟩
  · rw [mul_comm (Hseries G), coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b =>
      coeff a (P.map toQ) * coeff b (Hseries G)), Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ k := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
    rw [cast_eInt, coeff_map]
    have h1 : ((k - j).factorial : ℚ) * (k.descFactorial j : ℚ) = (k.factorial : ℚ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hj'
    rw [← h1]
    simp only [eq_intCast, toQ]
    ring
  · rw [Finset.sum_range_succ']
    simp only [Nat.descFactorial_zero, Nat.cast_one, one_mul, Nat.sub_zero,
      coeff_zero_eq_constantCoeff_apply, add_sub_cancel_right]
    refine Finset.dvd_sum fun j _ => ?_
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.succ_descFactorial_succ]
    push_cast
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.intro _ rfl) _) _

/-- **Lemma `lem:a-k-mod-k`.**  If `∑ a(n) x^n/n! = F(x) exp(x G(x))` with `F, G ∈ ℤ[[x]]`, then
`a(k)` is an integer with `a(k) ≡ F(0) G(0)^k (mod k)` for all `k ≥ 1`. -/
theorem a_k_mod_k (F G : ℤ⟦X⟧) (k : ℕ) (hk : 1 ≤ k) :
    ∃ a : ℤ, (a : ℚ) = (k.factorial : ℚ) * coeff k (F.map toQ * Hseries G) ∧
      (k : ℤ) ∣ a - constantCoeff F * constantCoeff G ^ k := by
  obtain ⟨c, hc, hd⟩ := coeff_mul_Hseries G F k hk
  refine ⟨c, by rw [hc, mul_comm (F.map toQ)], ?_⟩
  have h2 := eInt_dvd_pow G k hk
  have : c - constantCoeff F * constantCoeff G ^ k
      = (c - eInt G k * constantCoeff F) + (eInt G k - constantCoeff G ^ k) * constantCoeff F := by
    ring
  rw [this]
  exact dvd_add hd (Dvd.dvd.mul_right h2 _)

end Congruence

section Final

/-- **Theorem `thm:lagrange`.**  For integer series `F, G` there is an integral weight sequence `w`
(with `w 0 = 0`, i.e. `w = (w_1, w_2, …)` shifted) such that `b(n) = n! [x^n] exp(xG(x)) F(x)^n`
equals `A_w(n)` for all `n`, and `A_w(k) ≡ (F(0) G(0))^k (mod k)` for every `k ≥ 1`. -/
theorem lagrange_type (F G : ℤ⟦X⟧) :
    ∃ w : ℕ → ℤ, w 0 = 0 ∧ (∀ n, ((CongruenceTheory.Aw w n : ℤ) : ℚ) = bq F G n) ∧
      ∀ k : ℕ, 1 ≤ k →
        (k : ℤ) ∣ CongruenceTheory.Aw w k - (constantCoeff F * constantCoeff G) ^ k := by
  obtain ⟨T, hT0, hT⟩ := exists_fixedPoint F
  refine ⟨lagW F G T, by simp [lagW, lagWSeries], lagrange_family F G T hT0 hT, ?_⟩
  intro k hk
  obtain ⟨c, hc, hd⟩ := coeff_mul_Hseries G (F ^ k) k hk
  have hcA : CongruenceTheory.Aw (lagW F G T) k = c := by
    have h1 := lagrange_family F G T hT0 hT k
    have h2 : ((c : ℤ) : ℚ) = bq F G k := by rw [hc, bq, map_pow]
    exact_mod_cast h1.trans h2.symm
  rw [hcA]
  have h0 : constantCoeff (F ^ k) = constantCoeff F ^ k := by rw [map_pow]
  rw [h0] at hd
  have h2 := eInt_dvd_pow G k hk
  have : c - (constantCoeff F * constantCoeff G) ^ k
      = (c - eInt G k * constantCoeff F ^ k)
        + (eInt G k - constantCoeff G ^ k) * constantCoeff F ^ k := by ring
  rw [this]
  exact dvd_add hd (Dvd.dvd.mul_right h2 _)

/-- Consequence of `thm:lagrange` and `thm:universal`: if `F(0) = G(0) = 1` then
`b(n+k) ≡ b(n) (mod k)`. -/
theorem lagrange_type_shift (F G : ℤ⟦X⟧) (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) :
    ∃ w : ℕ → ℤ, (∀ n, ((CongruenceTheory.Aw w n : ℤ) : ℚ) = bq F G n) ∧
      ∀ n k : ℕ, 1 ≤ k → (k : ℤ) ∣ CongruenceTheory.Aw w (n + k) - CongruenceTheory.Aw w n := by
  obtain ⟨w, -, hb, hk⟩ := lagrange_type F G
  refine ⟨w, hb, fun n k hk1 => ?_⟩
  have h1 := CongruenceTheory.Aw_shift_mod k hk1 w n
  have h2 := hk k hk1
  rw [hF, hG, one_mul, one_pow] at h2
  have : CongruenceTheory.Aw w (n + k) - CongruenceTheory.Aw w n
      = (CongruenceTheory.Aw w (n + k) - CongruenceTheory.Aw w n * CongruenceTheory.Aw w k)
        + CongruenceTheory.Aw w n * (CongruenceTheory.Aw w k - 1) := by ring
  rw [this]
  exact dvd_add h1 (Dvd.dvd.mul_left h2 _)

/-- **Corollary `cor:n-n-1`.**  If `w_1 = 1` and `A_w(k) ≡ 1 (mod k)` for all `k ≥ 1`, then
`A_w(n) ≡ 1 (mod n(n-1))` for all `n ≥ 2`. -/
theorem Aw_mod_n_mul_pred (w : ℕ → ℤ) (hw1 : w 1 = 1)
    (hk : ∀ k : ℕ, 1 ≤ k → (k : ℤ) ∣ CongruenceTheory.Aw w k - 1) (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℤ) * ((n : ℤ) - 1)) ∣ CongruenceTheory.Aw w n - 1 := by
  have hA1 : CongruenceTheory.Aw w 1 = 1 := by
    unfold CongruenceTheory.Aw
    rw [CongruenceTheory.C_succ]
    simp [CongruenceTheory.fall, CongruenceTheory.C_zero, hw1]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have h1 := CongruenceTheory.Aw_shift_mod m hm w 1
  rw [hA1, one_mul, add_comm 1 m] at h1
  have h2 := hk m hm
  have hmm : (m : ℤ) ∣ CongruenceTheory.Aw w (m + 1) - 1 := by
    have : CongruenceTheory.Aw w (m + 1) - 1
        = (CongruenceTheory.Aw w (m + 1) - CongruenceTheory.Aw w m)
          + (CongruenceTheory.Aw w m - 1) := by ring
    rw [this]; exact dvd_add h1 h2
  have hn' : ((m + 1 : ℕ) : ℤ) ∣ CongruenceTheory.Aw w (m + 1) - 1 := hk (m + 1) (by omega)
  have hcop : IsCoprime ((m + 1 : ℕ) : ℤ) (m : ℤ) := by
    push_cast
    exact ⟨1, -1, by ring⟩
  have := hcop.mul_dvd hn' hmm
  push_cast at this ⊢
  simpa using this

end Final

end LagrangeFamily

