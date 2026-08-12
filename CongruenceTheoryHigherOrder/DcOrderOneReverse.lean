import Mathlib
import CongruenceTheoryHigherOrder.DcDef
import CongruenceTheoryHigherOrder.DcDegree1
import CongruenceTheoryHigherOrder.TriangularIndep
import CongruenceTheoryHigherOrder.FmModP

/-!
**`thm:complete-prime-local`(iii)'s `(A11)`: degree-one vanishing forces the digit
conditions.** If `D_{\mathbf c}`'s degree-one part vanishes entirely, then `c_s\equiv[s=r]
\pmod p` for `2\le s\le p-1` and `h\equiv0\pmod p` — half of the manuscript's claim that (A11)
"has order at least `p` exactly under the digit conditions (A8)", via `TriangularIndep.lean`'s
nullspace lemma applied to `D_{\mathbf c}`'s explicit degree-one coefficient formula
(`DcDegree1.lean`).
-/

namespace CongruenceTheory

open MvPolynomial

theorem Dc_deg1_zero_imp_digit_conditions (p r h : ℕ) (hp : p.Prime) (c : ℕ → ℕ)
    (hr2 : 2 ≤ r) (hrp : r ≤ p - 1)
    (hzero : ∀ t, 2 ≤ t → t ≤ p → MvPolynomial.coeff (Finsupp.single t 1) (Dc p r h c) = 0) :
    (∀ s, 2 ≤ s → s ≤ p - 1 → (c s : ZMod p) = if s = r then 1 else 0) ∧
      (h : ZMod p) = 0 := by
  have hp1 : 2 ≤ p := hp.two_le
  set v : ℕ → ℕ → ZMod p := fun s t => MvPolynomial.coeff (Finsupp.single t 1) (FmZ p s) with hv
  have hveq : ∀ s, 2 ≤ s → s ≤ p - 1 →
      v r s = ∑ s' ∈ Finset.Icc 1 (p - 1), (c s' : ZMod p) * v s' s := by
    intro s hs2 hsp
    have hd := hzero s hs2 (by omega)
    rw [coeff_single_Dc] at hd
    have htnp : s ≠ p := by omega
    rw [if_neg htnp, mul_zero, add_zero] at hd
    exact sub_eq_zero.mp hd
  have hxsum : ∀ t, 2 ≤ t → t ≤ p - 1 →
      ∑ s ∈ Finset.Icc 2 (p - 1),
        ((c s : ZMod p) - (if s = r then 1 else 0)) * v s t = 0 := by
    intro t ht2 htp
    have hveq' := hveq t ht2 htp
    have hicceq : Finset.Icc 1 (p - 1) = insert 1 (Finset.Icc 2 (p - 1)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hsplit : ∑ s' ∈ Finset.Icc 1 (p - 1), (c s' : ZMod p) * v s' t =
        (c 1 : ZMod p) * v 1 t + ∑ s' ∈ Finset.Icc 2 (p - 1), (c s' : ZMod p) * v s' t := by
      rw [hicceq, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    have hv1 : v 1 t = 0 := by
      show MvPolynomial.coeff (Finsupp.single t 1) (FmZ p 1) = 0
      unfold FmZ
      rw [Fm_one]
      simp only [map_one, MvPolynomial.coeff_one]
      rw [if_neg]
      intro heq
      have := DFunLike.congr_fun heq t
      simp at this
    rw [hv1, mul_zero, zero_add] at hsplit
    rw [hsplit] at hveq'
    have hindic : v r t =
        ∑ s ∈ Finset.Icc 2 (p - 1), (if s = r then (1 : ZMod p) else 0) * v s t := by
      have hrw2 : ∀ s ∈ Finset.Icc 2 (p - 1),
          (if s = r then (1 : ZMod p) else 0) * v s t = if s = r then v s t else 0 := by
        intro s _
        by_cases hsr : s = r
        · rw [if_pos hsr, if_pos hsr, one_mul]
        · rw [if_neg hsr, if_neg hsr, zero_mul]
      rw [Finset.sum_congr rfl hrw2,
        Finset.sum_ite_eq' (Finset.Icc 2 (p - 1)) r (fun x => v x t)]
      rw [if_pos (Finset.mem_Icc.mpr ⟨hr2, hrp⟩)]
    rw [hindic] at hveq'
    have hrw : ∀ s ∈ Finset.Icc 2 (p - 1),
        ((c s : ZMod p) - (if s = r then 1 else 0)) * v s t =
          (c s : ZMod p) * v s t - (if s = r then (1 : ZMod p) else 0) * v s t := by
      intro s _; ring
    rw [Finset.sum_congr rfl hrw, Finset.sum_sub_distrib, hveq']
    ring
  have hcresult := triangular_indep hp 2 (p - 1)
    (fun s t => v s t)
    (fun s t hs2 hsp ht2 htp hst => coeff_single_FmZ_eq_zero_of_lt p hst)
    (fun s hs2 hsp => by
      show v s s ≠ 0
      show MvPolynomial.coeff (Finsupp.single s 1) (FmZ p s) ≠ 0
      rw [coeff_single_FmZ p s hs2]
      exact factorial_ne_zero_mod_p hp (by omega))
    (fun s => (c s : ZMod p) - (if s = r then 1 else 0)) hxsum
  refine ⟨fun s hs2 hsp => sub_eq_zero.mp (hcresult s hs2 hsp), ?_⟩
  have hd := hzero p (by omega) (le_refl p)
  rw [coeff_single_Dc] at hd
  rw [if_pos rfl] at hd
  have hvrp : v r p = 0 := coeff_single_FmZ_eq_zero_of_lt p (by omega)
  have hvsp : ∀ s' ∈ Finset.Icc 1 (p - 1), (c s' : ZMod p) * v s' p = 0 := by
    intro s' hs'
    have hz : v s' p = 0 := coeff_single_FmZ_eq_zero_of_lt p
      (by simp only [Finset.mem_Icc] at hs'; omega)
    rw [hz, mul_zero]
  rw [Finset.sum_eq_zero hvsp] at hd
  have hd2 : v r p + (h : ZMod p) * (-1) - 0 = 0 := hd
  rw [hvrp] at hd2
  linear_combination -hd2

#print axioms Dc_deg1_zero_imp_digit_conditions

end CongruenceTheory
