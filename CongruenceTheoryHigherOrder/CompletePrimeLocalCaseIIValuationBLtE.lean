import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.CompletePrimeLocalCaseII

/-!
**`thm:complete-prime-local`(ii), valuation formula, the `b<E` branch.** Symmetric to
`complete_prime_local_case_ii_valuation_E_lt_b`: when `b < E`, `C_a\Delta_{\mathbf m}`'s content
is divisible by `p^{b+1}` (its own valuation `E` exceeds `b`), so the two-term piece
`C_{a+B}-C_aC_B` (valuation exactly `b`) dominates, giving `v_p(\operatorname{cont}
\Delta_{a,\mathbf m}) = b` exactly.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`thm:complete-prime-local`(ii), valuation formula, the `b<E` branch.** For `p\nmid a`,
`b := v_p(B) < E := v_p(\operatorname{cont}\Delta_{\mathbf m})` (`B=\sum_i m_i`):
`v_p(\operatorname{cont}\Delta_{a,\mathbf m}) = b` exactly. -/
theorem complete_prime_local_case_ii_valuation_b_lt_E {t : ℕ} {a : ℕ} (m : Fin t → ℕ)
    {p : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (ha1 : 1 ≤ a) (hB1 : 1 ≤ ∑ i, m i)
    {E : ℕ} (hE : (cont (Delta m)).factorization p = E) (hmne : Delta m ≠ 0)
    (hb : padicValNat p (∑ i, m i) < E) :
    (cont (Delta (Fin.cons a m : Fin (t + 1) → ℕ))).factorization p =
      padicValNat p (∑ i, m i) := by
  set B := ∑ i, m i with hBdef
  set b := padicValNat p B with hbdef
  have hcontCa := cont_C_eq_one a
  have hCamapne : MvPolynomial.map (Int.castRingHom (ZMod p)) (C a) ≠ 0 := by
    intro h0
    have hdvd := (map_eq_zero_iff_dvd_cont hp (C a)).mp h0
    rw [hcontCa] at hdvd
    exact (Nat.Prime.one_lt hp).ne' (Nat.dvd_one.mp hdvd)
  have hterm2fact : (cont (C a * Delta m)).factorization p = E :=
    factorization_cont_mul_of_map_ne_zero hp hCamapne E (Delta m) hE hmne
  have hterm1fact : (cont (C (a + B) - C a * C B)).factorization p = b :=
    padicValNat_cont_two_term_of_not_dvd_left hp ha1 hB1 hpa
  rw [Delta_cons_eq, ← hBdef]
  have hCane0 : C (a : ℕ) ≠ (0 : MvPolynomial ℕ ℤ) := by
    intro h0; rw [h0] at hcontCa; unfold cont at hcontCa; simp at hcontCa
  have hterm1ne : C (a + B) - C a * C B ≠ 0 := by
    intro h0
    have hcoeff := coeff_defect_two_eq_mul a B
    rw [h0, coeff_zero] at hcoeff
    have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
    have hB0 : (B : ℤ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
    exact (mul_ne_zero ha0 hB0) hcoeff.symm
  obtain ⟨d0, hd0⟩ :=
    exists_not_dvd_pow_succ_of_factorization_cont_eq hp hterm1ne hterm1fact
  have hd0term2 : (p : ℤ) ^ (b + 1) ∣ coeff d0 (C a * Delta m) :=
    dvd_coeff_of_factorization_cont_le (φ := C a * Delta m) (k := b + 1)
      (by rw [hterm2fact]; omega) d0
  have hupper : ¬ (p : ℤ) ^ (b + 1) ∣
      coeff d0 ((C (a + B) - C a * C B) + C a * Delta m) := by
    rw [coeff_add]
    intro hcon
    apply hd0
    have := dvd_sub hcon hd0term2
    simpa using this
  have hlower : ∀ d, (p : ℤ) ^ b ∣
      coeff d ((C (a + B) - C a * C B) + C a * Delta m) := by
    intro d
    rw [coeff_add]
    exact dvd_add
      (dvd_coeff_of_factorization_cont_le (φ := C (a + B) - C a * C B) (k := b)
        (by rw [hterm1fact]) d)
      (dvd_coeff_of_factorization_cont_le (φ := C a * Delta m) (k := b)
        (by rw [hterm2fact]; omega) d)
  have hcontne : cont ((C (a + B) - C a * C B) + C a * Delta m) ≠ 0 := by
    intro h0
    apply hupper
    have hzero : (C (a + B) - C a * C B) + C a * Delta m = 0 := by
      by_contra hne
      exact (cont_ne_zero_of_ne_zero hne) h0
    rw [hzero, coeff_zero]
    exact dvd_zero _
  have hge : b ≤ (cont ((C (a + B) - C a * C B) + C a * Delta m)).factorization p := by
    have hdvd : p ^ b ∣ cont ((C (a + B) - C a * C B) + C a * Delta m) := by
      unfold cont
      apply Finset.dvd_gcd
      intro d _
      have h1 := hlower d
      have h2 := Int.natAbs_dvd_natAbs.mpr h1
      rwa [Int.natAbs_pow, Int.natAbs_natCast] at h2
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp hcontne).mp hdvd
  have hle : (cont ((C (a + B) - C a * C B) + C a * Delta m)).factorization p ≤ b := by
    by_contra hcon
    push_neg at hcon
    apply hupper
    exact dvd_coeff_of_factorization_cont_le (k := b + 1) (by omega) d0
  omega

#print axioms complete_prime_local_case_ii_valuation_b_lt_E

end CongruenceTheory
