import Mathlib
import CongruenceTheoryHigherOrder.DcDef
import CongruenceTheoryHigherOrder.DcDegree1
import CongruenceTheoryHigherOrder.DcOrderOneReverse
import CongruenceTheoryHigherOrder.PolyOrder
import CongruenceTheoryHigherOrder.FmConstantTerm

/-!
**`thm:complete-prime-local`(iii)'s `(A11)`: `D_{\mathbf c}` has order exactly `1` when the
digit conditions fail.** Assembles `coeff_zero_Dc` (`D_{\mathbf c}`'s constant term is `0`,
always) with the contrapositive of `Dc_deg1_zero_imp_digit_conditions` to conclude
`\text{MinDeg}(D_{\mathbf c})\,1` whenever the digit conditions (A8) fail — the base case of
the manuscript's order-`p^\kappa` recursion.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`D_{\mathbf c}`'s constant term is `0`.** -/
theorem coeff_zero_Dc (p r h : ℕ) (c : ℕ → ℕ) :
    MvPolynomial.coeff (0 : ℕ →₀ ℕ) (Dc p r h c) = 0 := by
  unfold Dc
  rw [MvPolynomial.coeff_sub, ← MvPolynomial.constantCoeff_eq]
  have hFmZ0 : ∀ m : ℕ, MvPolynomial.constantCoeff (FmZ p m) = 1 := by
    intro m
    unfold FmZ
    rw [MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_map, coeff_zero_Fm]
    simp
  have h1 : MvPolynomial.constantCoeff (FmZ p r * (1 - MvPolynomial.X p) ^ h) = 1 := by
    rw [map_mul, map_pow, hFmZ0]
    have hone : MvPolynomial.constantCoeff
        (1 - MvPolynomial.X p : MvPolynomial ℕ (ZMod p)) = 1 := by
      rw [map_sub, map_one, MvPolynomial.constantCoeff_X]
      ring
    rw [hone]
    ring
  have h2 : MvPolynomial.constantCoeff (∏ s ∈ Finset.Icc 1 (p - 1), FmZ p s ^ c s) = 1 := by
    rw [map_prod]
    apply Finset.prod_eq_one
    intro s _
    rw [map_pow, hFmZ0]
    simp
  rw [h1, h2]
  ring

/-- **`D_{\mathbf c}` has order exactly `1` when the digit conditions fail.** -/
theorem MinDeg_one_Dc_of_not_digit_conditions (p r h : ℕ) (hp : p.Prime) (c : ℕ → ℕ)
    (hr2 : 2 ≤ r) (hrp : r ≤ p - 1)
    (hfail : ¬((∀ s, 2 ≤ s → s ≤ p - 1 → (c s : ZMod p) = if s = r then 1 else 0) ∧
      (h : ZMod p) = 0)) :
    MinDeg (Dc p r h c) 1 := by
  have hexists : ∃ t, 2 ≤ t ∧ t ≤ p ∧
      MvPolynomial.coeff (Finsupp.single t 1) (Dc p r h c) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hfail (Dc_deg1_zero_imp_digit_conditions p r h hp c hr2 hrp hcon)
  obtain ⟨t, ht2, htp, htne⟩ := hexists
  constructor
  · intro d hd
    by_contra hlt
    push_neg at hlt
    have hd0 : d = 0 := by
      have hdeg0 : monoDeg d = 0 := by omega
      rw [monoDeg_eq_sum, Finsupp.sum] at hdeg0
      by_contra hne
      obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hne
      have hdi : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
      have hle : d i ≤ ∑ a ∈ d.support, d a :=
        Finset.single_le_sum (fun a _ => Nat.zero_le (d a)) hi
      omega
    rw [hd0] at hd
    exact absurd (coeff_zero_Dc p r h c) (MvPolynomial.mem_support_iff.mp hd)
  · refine ⟨Finsupp.single t 1, MvPolynomial.mem_support_iff.mpr htne, ?_⟩
    rw [monoDeg_eq_sum]
    simp

#print axioms coeff_zero_Dc
#print axioms MinDeg_one_Dc_of_not_digit_conditions

end CongruenceTheory
