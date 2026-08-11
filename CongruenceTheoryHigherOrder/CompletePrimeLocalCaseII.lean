import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.CompletePrimeLocalDefect
import CongruenceTheoryHigherOrder.TwoTermDefectValuation
import CongruenceTheoryHigherOrder.GaussLemmaModP
import CongruenceTheoryHigherOrder.KOneAllFixedCoeff

/-!
**`thm:complete-prime-local`, case (ii), the `E < b` branch.** Writes `\Delta_{a,\mathbf m}` via
(A9) as `(C_{a+B}-C_aC_B) + C_a\Delta_{\mathbf m}` (`Delta_cons_eq`), and combines the exact
two-term valuation (`padicValNat_cont_two_term_of_not_dvd_left`, `b` exactly) with Gauss's lemma
mod `p` (`factorization_cont_mul_of_map_ne_zero`, giving `C_a\Delta_{\mathbf m}`'s content
valuation `E` exactly, since `C_a` has unit content) to pin `v_p(\operatorname{cont}
\Delta_{a,\mathbf m}) = E` exactly whenever `E < b`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`C_n`'s content is exactly `1`** (it has a unit coefficient at the all-fixed-points
monomial). -/
theorem cont_C_eq_one (n : ℕ) : cont (C n) = 1 := by
  have hcoeff : coeff (Finsupp.single 1 n) (C n) = 1 := by
    rw [← K_one n]; exact coeff_single_one_K_one n
  have hne : C n ≠ (0 : MvPolynomial ℕ ℤ) := by
    intro h0
    rw [h0, coeff_zero] at hcoeff
    exact one_ne_zero hcoeff.symm
  have hdvd : cont (C n) ∣ 1 := by
    have hmem : Finsupp.single 1 n ∈ (C n).support :=
      mem_support_iff.mpr (by rw [hcoeff]; exact one_ne_zero)
    have := Finset.gcd_dvd (f := fun d => (coeff d (C n)).natAbs) hmem
    rwa [hcoeff, Int.natAbs_one] at this
  exact Nat.dvd_one.mp hdvd

/-- **The general higher-order defect for the `a`-plus-`m` tuple decomposes via (A9)**:
`\Delta_{a,\mathbf m} = (C_{a+B}-C_aC_B) + C_a\Delta_{\mathbf m}`, `B=\sum_i m_i`. -/
theorem Delta_cons_eq {t : ℕ} (a : ℕ) (m : Fin t → ℕ) :
    Delta (Fin.cons a m : Fin (t + 1) → ℕ) =
      (C (a + ∑ i, m i) - C a * C (∑ i, m i)) + C a * Delta m := by
  unfold Delta
  rw [Fin.sum_cons]
  have hprod : (∏ i, C ((Fin.cons a m : Fin (t + 1) → ℕ) i)) = C a * ∏ i, C (m i) := by
    calc ∏ i, C ((Fin.cons a m : Fin (t + 1) → ℕ) i)
        = ∏ i, (C ∘ (Fin.cons a m : Fin (t + 1) → ℕ)) i := rfl
      _ = ∏ i, (Fin.cons (C a) (fun i => C (m i)) : Fin (t + 1) → MvPolynomial ℕ ℤ) i := by
          rw [Fin.comp_cons]; rfl
      _ = C a * ∏ i, C (m i) := Fin.prod_cons _ _
  rw [hprod]
  ring

/-- **A `p`-adic gcd-content achieves its own minimum**: if `v_p(\operatorname{cont}\varphi)=E`,
some coefficient of `\varphi` is not divisible by `p^{E+1}`. -/
theorem exists_not_dvd_pow_succ_of_factorization_cont_eq {p : ℕ} (hp : p.Prime)
    {φ : MvPolynomial ℕ ℤ} (hφ : φ ≠ 0) {E : ℕ} (hE : (cont φ).factorization p = E) :
    ∃ d, ¬ (p : ℤ) ^ (E + 1) ∣ coeff d φ := by
  by_contra hcon
  push_neg at hcon
  have hdvd : p ^ (E + 1) ∣ cont φ := by
    unfold cont
    apply Finset.dvd_gcd
    intro d _
    have h1 := hcon d
    have h2 := Int.natAbs_dvd_natAbs.mpr h1
    rwa [Int.natAbs_pow, Int.natAbs_natCast] at h2
  have hcontne := cont_ne_zero_of_ne_zero hφ
  have := (Nat.Prime.pow_dvd_iff_le_factorization hp hcontne).mp hdvd
  omega

/-- **Every coefficient of `\varphi` has `p`-adic valuation `\ge k`** whenever
`k \le v_p(\operatorname{cont}\varphi)`. -/
theorem dvd_coeff_of_factorization_cont_le {p : ℕ} {φ : MvPolynomial ℕ ℤ} {k : ℕ}
    (hk : k ≤ (cont φ).factorization p) (d : ℕ →₀ ℕ) : (p : ℤ) ^ k ∣ coeff d φ := by
  by_cases hd : d ∈ φ.support
  · have h1 : p ^ (cont φ).factorization p ∣ cont φ := Nat.ordProj_dvd (cont φ) p
    have h2 : cont φ ∣ (coeff d φ).natAbs := by unfold cont; exact Finset.gcd_dvd hd
    have h3 : p ^ (cont φ).factorization p ∣ (coeff d φ).natAbs := dvd_trans h1 h2
    have h4 : p ^ k ∣ p ^ (cont φ).factorization p := pow_dvd_pow p hk
    have h5 : p ^ k ∣ (coeff d φ).natAbs := dvd_trans h4 h3
    have h6 := Int.natCast_dvd_natCast.mpr h5
    rwa [Int.dvd_natAbs, Int.natCast_pow] at h6
  · rw [mem_support_iff, not_not] at hd
    rw [hd]; exact dvd_zero _

/-- **`thm:complete-prime-local`(ii), valuation formula, the `E<b` branch.** For `p\nmid a`,
`E := v_p(\operatorname{cont}\Delta_{\mathbf m}) < b := v_p(B)` (`B=\sum_i m_i`):
`v_p(\operatorname{cont}\Delta_{a,\mathbf m}) = E` exactly. -/
theorem complete_prime_local_case_ii_valuation_E_lt_b {t : ℕ} {a : ℕ} (m : Fin t → ℕ)
    {p : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (ha1 : 1 ≤ a) (hB1 : 1 ≤ ∑ i, m i)
    {E : ℕ} (hE : (cont (Delta m)).factorization p = E) (hmne : Delta m ≠ 0)
    (hb : E < padicValNat p (∑ i, m i)) :
    (cont (Delta (Fin.cons a m : Fin (t + 1) → ℕ))).factorization p = E := by
  set B := ∑ i, m i with hBdef
  have hcontCa := cont_C_eq_one a
  have hCamapne : MvPolynomial.map (Int.castRingHom (ZMod p)) (C a) ≠ 0 := by
    intro h0
    have hdvd := (map_eq_zero_iff_dvd_cont hp (C a)).mp h0
    rw [hcontCa] at hdvd
    exact (Nat.Prime.one_lt hp).ne' (Nat.dvd_one.mp hdvd)
  have hterm2fact : (cont (C a * Delta m)).factorization p = E :=
    factorization_cont_mul_of_map_ne_zero hp hCamapne E (Delta m) hE hmne
  have hterm1fact : (cont (C (a + B) - C a * C B)).factorization p =
      padicValNat p B :=
    padicValNat_cont_two_term_of_not_dvd_left hp ha1 hB1 hpa
  rw [Delta_cons_eq, ← hBdef]
  have hCane0 : C (a : ℕ) ≠ (0 : MvPolynomial ℕ ℤ) := by
    intro h0; rw [h0] at hcontCa; unfold cont at hcontCa; simp at hcontCa
  have hterm2ne : C a * Delta m ≠ 0 := mul_ne_zero hCane0 hmne
  obtain ⟨d0, hd0⟩ := exists_not_dvd_pow_succ_of_factorization_cont_eq hp hterm2ne hterm2fact
  have hd0term1 : (p : ℤ) ^ (E + 1) ∣ coeff d0 (C (a + B) - C a * C B) :=
    dvd_coeff_of_factorization_cont_le (φ := C (a + B) - C a * C B) (k := E + 1)
      (by rw [hterm1fact]; omega) d0
  have hupper : ¬ (p : ℤ) ^ (E + 1) ∣
      coeff d0 ((C (a + B) - C a * C B) + C a * Delta m) := by
    rw [coeff_add]
    intro hcon
    apply hd0
    have := dvd_sub hcon hd0term1
    simpa using this
  have hlower : ∀ d, (p : ℤ) ^ E ∣
      coeff d ((C (a + B) - C a * C B) + C a * Delta m) := by
    intro d
    rw [coeff_add]
    exact dvd_add
      (dvd_coeff_of_factorization_cont_le (φ := C (a + B) - C a * C B) (k := E)
        (by rw [hterm1fact]; omega) d)
      (dvd_coeff_of_factorization_cont_le (φ := C a * Delta m) (k := E)
        (by rw [hterm2fact]) d)
  have hcontne : cont ((C (a + B) - C a * C B) + C a * Delta m) ≠ 0 := by
    intro h0
    apply hupper
    have hzero : (C (a + B) - C a * C B) + C a * Delta m = 0 := by
      by_contra hne
      exact (cont_ne_zero_of_ne_zero hne) h0
    rw [hzero, coeff_zero]
    exact dvd_zero _
  have hge : E ≤ (cont ((C (a + B) - C a * C B) + C a * Delta m)).factorization p := by
    have hdvd : p ^ E ∣ cont ((C (a + B) - C a * C B) + C a * Delta m) := by
      unfold cont
      apply Finset.dvd_gcd
      intro d _
      have h1 := hlower d
      have h2 := Int.natAbs_dvd_natAbs.mpr h1
      rwa [Int.natAbs_pow, Int.natAbs_natCast] at h2
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp hcontne).mp hdvd
  have hle : (cont ((C (a + B) - C a * C B) + C a * Delta m)).factorization p ≤ E := by
    by_contra hcon
    push_neg at hcon
    apply hupper
    exact dvd_coeff_of_factorization_cont_le (k := E + 1) (by omega) d0
  omega

#print axioms cont_C_eq_one
#print axioms Delta_cons_eq
#print axioms exists_not_dvd_pow_succ_of_factorization_cont_eq
#print axioms dvd_coeff_of_factorization_cont_le
#print axioms complete_prime_local_case_ii_valuation_E_lt_b

end CongruenceTheory
