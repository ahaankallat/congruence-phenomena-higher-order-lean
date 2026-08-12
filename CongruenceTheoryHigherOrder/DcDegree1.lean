import Mathlib
import CongruenceTheoryHigherOrder.FmDef
import CongruenceTheoryHigherOrder.FmModP
import CongruenceTheoryHigherOrder.FmConstantTerm
import CongruenceTheoryHigherOrder.DcDef
import CongruenceTheoryHigherOrder.PolyOrder
import CongruenceTheoryHigherOrder.LinPart
import CongruenceTheoryHigherOrder.LinPartPow

/-!
**`thm:complete-prime-local`(iii)'s `(A11)`: `D_{\mathbf c}`'s degree-one coefficient.**
Assembles the explicit formula for `\text{coeff}_{X_t}(D_{\mathbf c})` from the degree-one
linearization machinery (`LinPart.lean`, `LinPartPow.lean`).
-/

namespace CongruenceTheory

open MvPolynomial

/-- `F_mZ - 1` lies in `J`. -/
theorem FmZ_sub_one_deg_ge_one (p m : ℕ) : ∀ d ∈ (FmZ p m - 1).support, 1 ≤ monoDeg d := by
  intro d hd
  have heq : FmZ p m - 1 = MvPolynomial.map (Int.castRingHom (ZMod p)) (Fm m - 1) := by
    unfold FmZ
    rw [map_sub, map_one]
  rw [heq] at hd
  apply Fm_sub_one_deg_ge_one m
  rw [MvPolynomial.mem_support_iff] at hd ⊢
  intro hz
  apply hd
  rw [MvPolynomial.coeff_map, hz]
  simp

/-- `-X_p` lies in `J`. -/
theorem neg_X_deg_ge_one (p : ℕ) :
    ∀ d ∈ (-(MvPolynomial.X p) : MvPolynomial ℕ (ZMod p)).support, 1 ≤ monoDeg d := by
  intro d hd
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_neg] at hd
  by_contra hcon
  push_neg at hcon
  have hd0 : monoDeg d = 0 := by omega
  have hdeq : d = Finsupp.single p 1 := by
    by_contra hne
    apply hd
    rw [MvPolynomial.coeff_X, if_neg (Ne.symm hne)]
    simp
  rw [hdeq, monoDeg_eq_sum] at hd0
  simp at hd0

/-- **`(1-X_p) = 1 + (-X_p)`**, phrased for direct use with the `1+J`-unit machinery. -/
theorem one_sub_X_eq (p : ℕ) :
    (1 - MvPolynomial.X p : MvPolynomial ℕ (ZMod p)) = 1 + (-(MvPolynomial.X p)) := by ring

/-- `\text{coeff}_{X_t}(-X_p) = \text{if }t=p\text{ then }-1\text{ else }0`. -/
theorem coeff_single_neg_X (p : ℕ) {t : ℕ} :
    MvPolynomial.coeff (Finsupp.single t 1) (-(MvPolynomial.X p) : MvPolynomial ℕ (ZMod p)) =
      if t = p then (-1 : ZMod p) else 0 := by
  rw [MvPolynomial.coeff_neg, MvPolynomial.coeff_X]
  by_cases htp : t = p
  · subst htp
    simp
  · have hne : ¬ (Finsupp.single p 1 : ℕ →₀ ℕ) = Finsupp.single t 1 := by
      intro heq
      apply htp
      have hv := DFunLike.congr_fun heq p
      rw [Finsupp.single_apply, Finsupp.single_apply, if_pos rfl] at hv
      by_contra hne2
      rw [if_neg hne2] at hv
      exact one_ne_zero hv
    rw [if_neg hne, if_neg htp]
    simp

/-- `\text{coeff}_{X_t}(1-X_p)^h = h\cdot(\text{if }t=p\text{ then }-1\text{ else }0)`. -/
theorem coeff_single_one_sub_X_pow (p h : ℕ) {t : ℕ} :
    MvPolynomial.coeff (Finsupp.single t 1) ((1 - MvPolynomial.X p : MvPolynomial ℕ (ZMod p)) ^ h)
      = (h : ZMod p) * (if t = p then (-1 : ZMod p) else 0) := by
  rw [one_sub_X_eq, coeff_single_pow_add_one _ h (neg_X_deg_ge_one p), coeff_single_neg_X]

/-- **`D_{\mathbf c}`'s degree-one coefficient.** -/
theorem coeff_single_Dc (p r h : ℕ) (c : ℕ → ℕ) {t : ℕ} :
    MvPolynomial.coeff (Finsupp.single t 1) (Dc p r h c) =
      (MvPolynomial.coeff (Finsupp.single t 1) (FmZ p r) +
          (h : ZMod p) * (if t = p then (-1 : ZMod p) else 0)) -
        ∑ s ∈ Finset.Icc 1 (p - 1),
          (c s : ZMod p) * MvPolynomial.coeff (Finsupp.single t 1) (FmZ p s) := by
  unfold Dc
  rw [MvPolynomial.coeff_sub]
  have hsingle_ne : (Finsupp.single t 1 : ℕ →₀ ℕ) ≠ 0 := by
    intro heq
    have := DFunLike.congr_fun heq t
    simp at this
  congr 1
  · have hmuleq : FmZ p r * (1 - MvPolynomial.X p) ^ h =
        (1 + (FmZ p r - 1)) * (1 + ((1 - MvPolynomial.X p) ^ h - 1)) := by ring
    rw [hmuleq]
    have hpowdeg : ∀ d ∈ ((1 - MvPolynomial.X p : MvPolynomial ℕ (ZMod p)) ^ h - 1).support,
        1 ≤ monoDeg d := by
      rw [one_sub_X_eq]
      exact pow_one_add_sub_one_deg_ge_one _ h (neg_X_deg_ge_one p)
    rw [coeff_single_mul_add_one _ _ (FmZ_sub_one_deg_ge_one p r) hpowdeg]
    have hsub1 : MvPolynomial.coeff (Finsupp.single t 1) (FmZ p r - 1) =
        MvPolynomial.coeff (Finsupp.single t 1) (FmZ p r) := by
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one, if_neg (Ne.symm hsingle_ne)]; ring
    have hsub2 : MvPolynomial.coeff (Finsupp.single t 1)
        ((1 - MvPolynomial.X p : MvPolynomial ℕ (ZMod p)) ^ h - 1) =
        MvPolynomial.coeff (Finsupp.single t 1)
          ((1 - MvPolynomial.X p : MvPolynomial ℕ (ZMod p)) ^ h) := by
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one, if_neg (Ne.symm hsingle_ne)]; ring
    rw [hsub1, hsub2, coeff_single_one_sub_X_pow]
  · have heq2 : ∀ s, FmZ p s ^ c s = (1 + (FmZ p s - 1)) ^ c s := by intro s; ring
    have hkey : ∀ s ∈ Finset.Icc 1 (p - 1),
        ∀ d ∈ (FmZ p s ^ c s - 1).support, 1 ≤ monoDeg d := by
      intro s _
      rw [heq2 s]
      exact pow_one_add_sub_one_deg_ge_one _ (c s) (FmZ_sub_one_deg_ge_one p s)
    have hprodeq : ∏ s ∈ Finset.Icc 1 (p - 1), FmZ p s ^ c s =
        ∏ s ∈ Finset.Icc 1 (p - 1), (1 + (FmZ p s ^ c s - 1)) := by
      apply Finset.prod_congr rfl
      intro s _
      ring
    rw [hprodeq, coeff_single_finset_prod_add_one (Finset.Icc 1 (p - 1))
      (fun s => FmZ p s ^ c s - 1) hkey]
    apply Finset.sum_congr rfl
    intro s _
    have hsub3 : MvPolynomial.coeff (Finsupp.single t 1) (FmZ p s ^ c s - 1) =
        MvPolynomial.coeff (Finsupp.single t 1) (FmZ p s ^ c s) := by
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one, if_neg (Ne.symm hsingle_ne)]; ring
    have hsub4 : MvPolynomial.coeff (Finsupp.single t 1) (FmZ p s - 1) =
        MvPolynomial.coeff (Finsupp.single t 1) (FmZ p s) := by
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one, if_neg (Ne.symm hsingle_ne)]; ring
    rw [hsub3, heq2 s, coeff_single_pow_add_one _ (c s) (FmZ_sub_one_deg_ge_one p s), hsub4]

#print axioms FmZ_sub_one_deg_ge_one
#print axioms neg_X_deg_ge_one
#print axioms coeff_single_neg_X
#print axioms coeff_single_one_sub_X_pow
#print axioms coeff_single_Dc

end CongruenceTheory
