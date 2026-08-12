import Mathlib
import CongruenceTheoryHigherOrder.DcDef
import CongruenceTheoryHigherOrder.DcDegree1
import CongruenceTheoryHigherOrder.DcOrderOneReverse
import CongruenceTheoryHigherOrder.DcOrderOne
import CongruenceTheoryHigherOrder.DcFrobenius
import CongruenceTheoryHigherOrder.DcPowOrder
import CongruenceTheoryHigherOrder.DigitDecomposition

/-!
**`thm:complete-prime-local`(iii)'s `(A11)`/`(A12)`, assembled: the single recursive step.**
Whenever the digit conditions hold, `\text{ord}_J(D_{\mathbf c})=p\cdot\text{ord}_J(D_{\mathbf
c'})` exactly, where `\mathbf c'` is the (uniquely determined) digit-shifted tuple; whenever they
fail, `\text{ord}_J(D_{\mathbf c})=1`. This is the manuscript's full order recursion, in one
theorem, obtained entirely through exact algebra (`Dc_frobenius_factorization`+`MinDeg_pow_p`+
`MinDeg_unit_mul`) rather than the truncated-log isomorphism route.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`F_r` is a `J`-adic unit**: its constant term is `1\ne0`. -/
theorem FmZ_coeff_zero_ne_zero (p r : ℕ) (hp : p.Prime) :
    MvPolynomial.coeff (0 : ℕ →₀ ℕ) (FmZ p r) ≠ 0 := by
  haveI := Fact.mk hp
  unfold FmZ
  rw [MvPolynomial.coeff_map, coeff_zero_Fm]
  simp

/-- **The single recursive step**: if the digit conditions hold, `D_{\mathbf c}`'s order is
exactly `p` times the order of the digit-shifted `D_{\mathbf c'}`. -/
theorem MinDeg_Dc_step_of_digit_conditions (p r h : ℕ) (hp : p.Prime) (c : ℕ → ℕ)
    (hr2 : 2 ≤ r) (hrp : r ≤ p - 1)
    (hdig : (∀ s, 2 ≤ s → s ≤ p - 1 → (c s : ZMod p) = if s = r then 1 else 0) ∧
      (h : ZMod p) = 0) {m : ℕ}
    (hc' : ∀ h' : ℕ, h = p * h' → ∀ c' : ℕ → ℕ,
      (∀ s ∈ Finset.Icc 2 (p - 1), c s = p * c' s + (if s = r then 1 else 0)) →
      MinDeg (Dc p 1 h' c') m) :
    MinDeg (Dc p r h c) (p * m) := by
  obtain ⟨h', hh'⟩ := exists_decomp_of_dvd hdig.2
  have hcex : ∀ s ∈ Finset.Icc 2 (p - 1), ∃ c'0 : ℕ, c s = p * c'0 + (if s = r then 1 else 0) := by
    intro s hs
    have hsmem : s ∈ Finset.Icc 2 (p - 1) := hs
    simp only [Finset.mem_Icc] at hsmem
    by_cases hsr : s = r
    · subst hsr
      have hcs : (c s : ZMod p) = 1 := by rw [hdig.1 s hsmem.1 hsmem.2]; simp
      obtain ⟨c'0, hc'0⟩ := exists_decomp_of_modEq (ε := 1) hp.one_lt (by simpa using hcs)
      exact ⟨c'0, by simpa using hc'0⟩
    · have hcs : (c s : ZMod p) = 0 := by
        rw [hdig.1 s hsmem.1 hsmem.2]
        simp [hsr]
      obtain ⟨c'0, hc'0⟩ := exists_decomp_of_modEq (ε := 0) hp.pos (by simpa using hcs)
      refine ⟨c'0, ?_⟩
      simpa [hsr] using hc'0
  choose c'fun hc'fun using hcex
  set c' : ℕ → ℕ := fun s => if hs : s ∈ Finset.Icc 2 (p - 1) then c'fun s hs else 0 with hc'def
  have hc'spec : ∀ s ∈ Finset.Icc 2 (p - 1), c s = p * c' s + (if s = r then 1 else 0) := by
    intro s hs
    simp only [hc'def, dif_pos hs]
    exact hc'fun s hs
  have hstep := hc' h' hh' c' hc'spec
  have hfrob := Dc_frobenius_factorization p r h h' hp c c' hr2 hrp hh' hc'spec
  rw [hfrob]
  exact MinDeg_unit_mul hp (FmZ_coeff_zero_ne_zero p r hp) (MinDeg_pow_p hp hstep)

#print axioms FmZ_coeff_zero_ne_zero
#print axioms MinDeg_Dc_step_of_digit_conditions

end CongruenceTheory
