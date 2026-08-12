import Mathlib
import CongruenceTheoryHigherOrder.DcDef
import CongruenceTheoryHigherOrder.DcDegree1
import CongruenceTheoryHigherOrder.TriangularIndep
import CongruenceTheoryHigherOrder.FmModP
import CongruenceTheoryHigherOrder.FmConstantTerm
import CongruenceTheoryHigherOrder.PolyOrder
import CongruenceTheoryHigherOrder.DcFrobenius
import CongruenceTheoryHigherOrder.DcPowOrder
import CongruenceTheoryHigherOrder.DcOrderOne
import CongruenceTheoryHigherOrder.DigitDecomposition

/-!
**`thm:complete-prime-local`(iii)'s `(A11)`/`(A12)`, the residual (`r=1`) recursion step.**
After one Frobenius factorization, the manuscript's recursion always lands on `D_{\mathbf
c}=D_{r=1,h,\mathbf c}`, i.e. `r_k=0` for every `k\ge1` (proved by hand: since
`R_0=\sum s\,c_s=ph_0`, the next weighted sum `R_1=\sum s\,c'_s` equals `h_0`, which is
`\equiv0\pmod p` exactly when the recursion continues, so `r_1=0`, and by induction `r_k=0`
forever after). Since `F_1=F_0=1`, there is no unit factor left to peel off, and Frobenius gives
the even simpler EXACT identity `D_{1,h,\mathbf c}=D_{1,h',\mathbf c'}^p` (no `MinDeg_unit_mul`
needed). This file supplies the `r=1` companions to `DcOrderOneReverse.lean`, `DcOrderOne.lean`,
`DcFrobenius.lean`, `DcOrderStep.lean`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`r=1` companion to `Dc_deg1_zero_imp_digit_conditions`**: degree-one vanishing of
`D_{1,h,\mathbf c}` forces `c_s\equiv0\pmod p` (`2\le s\le p-1`) and `h\equiv0\pmod p`. -/
theorem Dc_deg1_zero_imp_digit_conditions_r1 (p h : ℕ) (hp : p.Prime) (c : ℕ → ℕ)
    (hzero : ∀ t, 2 ≤ t → t ≤ p → MvPolynomial.coeff (Finsupp.single t 1) (Dc p 1 h c) = 0) :
    (∀ s, 2 ≤ s → s ≤ p - 1 → (c s : ZMod p) = 0) ∧ (h : ZMod p) = 0 := by
  have hp1 : 2 ≤ p := hp.two_le
  set v : ℕ → ℕ → ZMod p := fun s t => MvPolynomial.coeff (Finsupp.single t 1) (FmZ p s) with hv
  have hv1_raw : ∀ t, MvPolynomial.coeff (Finsupp.single t 1) (FmZ p 1) = 0 := by
    intro t
    unfold FmZ
    rw [Fm_one]
    simp only [map_one, MvPolynomial.coeff_one]
    rw [if_neg]
    intro heq
    have := DFunLike.congr_fun heq t
    simp at this
  have hv1 : ∀ t, v 1 t = 0 := hv1_raw
  have hveq : ∀ s, 2 ≤ s → s ≤ p - 1 →
      (0 : ZMod p) = ∑ s' ∈ Finset.Icc 1 (p - 1), (c s' : ZMod p) * v s' s := by
    intro s hs2 hsp
    have hd := hzero s hs2 (by omega)
    rw [coeff_single_Dc] at hd
    have htnp : s ≠ p := by omega
    rw [if_neg htnp, mul_zero, add_zero, hv1_raw s] at hd
    exact sub_eq_zero.mp hd
  have hxsum : ∀ t, 2 ≤ t → t ≤ p - 1 →
      ∑ s ∈ Finset.Icc 2 (p - 1), (c s : ZMod p) * v s t = 0 := by
    intro t ht2 htp
    have hveq' := hveq t ht2 htp
    have hicceq : Finset.Icc 1 (p - 1) = insert 1 (Finset.Icc 2 (p - 1)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hsplit : ∑ s' ∈ Finset.Icc 1 (p - 1), (c s' : ZMod p) * v s' t =
        (c 1 : ZMod p) * v 1 t + ∑ s' ∈ Finset.Icc 2 (p - 1), (c s' : ZMod p) * v s' t := by
      rw [hicceq, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    rw [hv1 t, mul_zero, zero_add] at hsplit
    rw [hsplit] at hveq'
    exact hveq'.symm
  have hcresult := triangular_indep hp 2 (p - 1)
    (fun s t => v s t)
    (fun s t hs2 hsp ht2 htp hst => coeff_single_FmZ_eq_zero_of_lt p hst)
    (fun s hs2 hsp => by
      show v s s ≠ 0
      show MvPolynomial.coeff (Finsupp.single s 1) (FmZ p s) ≠ 0
      rw [coeff_single_FmZ p s hs2]
      exact factorial_ne_zero_mod_p hp (by omega))
    (fun s => (c s : ZMod p)) hxsum
  refine ⟨hcresult, ?_⟩
  have hd := hzero p (by omega) (le_refl p)
  rw [coeff_single_Dc] at hd
  rw [if_pos rfl] at hd
  have hv1p : v 1 p = 0 := hv1 p
  have hvsp : ∀ s' ∈ Finset.Icc 1 (p - 1), (c s' : ZMod p) * v s' p = 0 := by
    intro s' hs'
    have hz : v s' p = 0 := coeff_single_FmZ_eq_zero_of_lt p
      (by simp only [Finset.mem_Icc] at hs'; omega)
    rw [hz, mul_zero]
  rw [Finset.sum_eq_zero hvsp] at hd
  have hd2 : v 1 p + (h : ZMod p) * (-1) - 0 = 0 := hd
  rw [hv1p] at hd2
  linear_combination -hd2

/-- **`r=1` companion to `MinDeg_one_Dc_of_not_digit_conditions`**: `D_{1,h,\mathbf c}` has order
exactly `1` when the (residual) digit conditions fail. -/
theorem MinDeg_one_Dc_of_not_digit_conditions_r1 (p h : ℕ) (hp : p.Prime) (c : ℕ → ℕ)
    (hfail : ¬((∀ s, 2 ≤ s → s ≤ p - 1 → (c s : ZMod p) = 0) ∧ (h : ZMod p) = 0)) :
    MinDeg (Dc p 1 h c) 1 := by
  have hexists : ∃ t, 2 ≤ t ∧ t ≤ p ∧
      MvPolynomial.coeff (Finsupp.single t 1) (Dc p 1 h c) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hfail (Dc_deg1_zero_imp_digit_conditions_r1 p h hp c hcon)
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
    exact absurd (coeff_zero_Dc p 1 h c) (MvPolynomial.mem_support_iff.mp hd)
  · refine ⟨Finsupp.single t 1, MvPolynomial.mem_support_iff.mpr htne, ?_⟩
    rw [monoDeg_eq_sum]
    simp

/-- **`r=1` companion to `Dc_frobenius_factorization`**: under the residual digit conditions
(`c_s=pc'_s` for `2\le s\le p-1`, `h=ph'`), `D_{1,h,\mathbf c}=D_{1,h',\mathbf c'}^p` EXACTLY —
no unit factor, since `F_1=1`. -/
theorem Dc_frobenius_factorization_r1 (p h h' : ℕ) (hp : p.Prime) (c c' : ℕ → ℕ)
    (hh : h = p * h')
    (hc : ∀ s ∈ Finset.Icc 2 (p - 1), c s = p * c' s) :
    Dc p 1 h c = (Dc p 1 h' c') ^ p := by
  have hc0 : ∀ s ∈ Finset.Icc 2 (p - 1), c s = p * c' s + (if s = 1 then 1 else 0) := by
    intro s hs
    have hs2 : 2 ≤ s := (Finset.mem_Icc.mp hs).1
    rw [hc s hs, if_neg (by omega)]
    ring
  have hprod : ∏ s ∈ Finset.Icc 1 (p - 1), FmZ p s ^ c s =
      FmZ p 1 * (∏ s ∈ Finset.Icc 1 (p - 1), FmZ p s ^ c' s) ^ p := by
    have hstep1 : ∀ s ∈ Finset.Icc 1 (p - 1),
        FmZ p s ^ c s = (FmZ p s ^ c' s) ^ p * (if s = 1 then FmZ p s else 1) := by
      intro s hs
      by_cases hs1 : s = 1
      · subst hs1
        rw [FmZ_one, if_pos rfl]
        simp
      · have hs2 : 2 ≤ s := by
          simp only [Finset.mem_Icc] at hs; omega
        rw [hc0 s (Finset.mem_Icc.mpr ⟨hs2, (Finset.mem_Icc.mp hs).2⟩), pow_add, pow_mul']
        rw [if_neg hs1, if_neg hs1, pow_zero]
    rw [Finset.prod_congr rfl hstep1, Finset.prod_mul_distrib, Finset.prod_pow]
    have hindic : ∏ s ∈ Finset.Icc 1 (p - 1), (if s = 1 then FmZ p s else 1) = FmZ p 1 := by
      rw [Finset.prod_ite_eq' (Finset.Icc 1 (p - 1)) 1 (FmZ p)]
      rw [if_pos (by have := hp.two_le; simp only [Finset.mem_Icc]; omega)]
    rw [hindic]
    ring
  unfold Dc
  rw [hh, pow_mul', hprod]
  simp only [FmZ_one, one_mul]
  exact sub_pow_char hp _ _

/-- **The residual single step**: whenever the residual digit conditions hold, `D_{1,h,\mathbf
c}`'s order is exactly `p` times that of the digit-shifted `D_{1,h',\mathbf c'}`. -/
theorem MinDeg_Dc_step_r1 (p h : ℕ) (hp : p.Prime) (c : ℕ → ℕ)
    (hdig : (∀ s, 2 ≤ s → s ≤ p - 1 → (c s : ZMod p) = 0) ∧ (h : ZMod p) = 0) {m : ℕ}
    (hc' : ∀ h' : ℕ, h = p * h' → ∀ c' : ℕ → ℕ,
      (∀ s ∈ Finset.Icc 2 (p - 1), c s = p * c' s) → MinDeg (Dc p 1 h' c') m) :
    MinDeg (Dc p 1 h c) (p * m) := by
  obtain ⟨h', hh'⟩ := exists_decomp_of_dvd hdig.2
  have hcex : ∀ s ∈ Finset.Icc 2 (p - 1), ∃ c'0 : ℕ, c s = p * c'0 := by
    intro s hs
    have hsmem : s ∈ Finset.Icc 2 (p - 1) := hs
    simp only [Finset.mem_Icc] at hsmem
    have hcs : (c s : ZMod p) = 0 := hdig.1 s hsmem.1 hsmem.2
    obtain ⟨c'0, hc'0⟩ := exists_decomp_of_modEq (ε := 0) hp.pos (by simpa using hcs)
    exact ⟨c'0, by simpa using hc'0⟩
  choose c'fun hc'fun using hcex
  set c' : ℕ → ℕ := fun s => if hs : s ∈ Finset.Icc 2 (p - 1) then c'fun s hs else 0 with hc'def
  have hc'spec : ∀ s ∈ Finset.Icc 2 (p - 1), c s = p * c' s := by
    intro s hs
    simp only [hc'def, dif_pos hs]
    exact hc'fun s hs
  have hstep := hc' h' hh' c' hc'spec
  have hfrob := Dc_frobenius_factorization_r1 p h h' hp c c' hh' hc'spec
  rw [hfrob]
  exact MinDeg_pow_p hp hstep

#print axioms Dc_deg1_zero_imp_digit_conditions_r1
#print axioms MinDeg_one_Dc_of_not_digit_conditions_r1
#print axioms Dc_frobenius_factorization_r1
#print axioms MinDeg_Dc_step_r1

end CongruenceTheory
