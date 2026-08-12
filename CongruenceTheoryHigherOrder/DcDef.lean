import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.Perm
import CongruenceTheory.CpermEqC
import CongruenceTheory.CoeffExtraction
import CongruenceTheory.PrimeWitness
import CongruenceTheoryHigherOrder.FmDef
import CongruenceTheoryHigherOrder.FmModP
import CongruenceTheoryHigherOrder.PolyOrder
import CongruenceTheoryHigherOrder.DefectWeightedHomogeneous

/-!
**`thm:complete-prime-local`(iii)'s `(A11)`: `D_{\mathbf c}(y)`, and the triangular vanishing
fact.** `D_{\mathbf c}(y) = F_r(y)(1-y_p)^h - \prod_{s=1}^{p-1}F_s(y)^{c_s}`, working mod `p`
(`\mathbb F_p[X_2,X_3,\ldots]`, using `X_i` for the manuscript's `y_i`). The key structural fact
behind the manuscript's linear-independence argument: `F_j` (`j<s`) has **zero** coefficient at
`X_s` (`coeff_single_Fm_eq_zero_of_lt`), while `F_s` itself has coefficient `(s-1)!`
(`coeff_single_Fm`, already proven) — the "triangular" pattern.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`D_{\mathbf c}(y)`**: `F_r(y)(1-y_p)^h - \prod_{s=1}^{p-1}F_s(y)^{c_s}`, for `p` prime,
`r : ℕ`, `h : ℕ`, and `c : ℕ → ℕ` the per-residue exponents `c_1,\ldots,c_{p-1}`. -/
noncomputable def Dc (p r h : ℕ) (c : ℕ → ℕ) : MvPolynomial ℕ (ZMod p) :=
  FmZ p r * (1 - MvPolynomial.X p) ^ h -
    ∏ s ∈ Finset.Icc 1 (p - 1), (FmZ p s) ^ c s

/-- **`F_j` has zero coefficient at `X_s` whenever `s>j`** (matches the manuscript's "`F_j`
contains no `y_s` when `j<s`"). -/
theorem coeff_single_Fm_eq_zero_of_lt {j s : ℕ} (hjs : j < s) :
    MvPolynomial.coeff (Finsupp.single s 1) (Fm j) = 0 := by
  unfold Fm
  rw [MvPolynomial.bind₁, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro d hdmem
  have halg : algebraMap ℤ (MvPolynomial ℕ ℤ) (MvPolynomial.coeff d (C j)) =
      MvPolynomial.C (MvPolynomial.coeff d (C j)) := rfl
  rw [halg, MvPolynomial.coeff_C_mul]
  have hprodeq : (∏ i ∈ d.support,
      (if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) ^ d i) =
      d.prod fun i e => (if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) ^ e := rfl
  rw [hprodeq, prod_subst_eq_monomial_erase, MvPolynomial.coeff_monomial]
  rw [if_neg]
  · ring
  · intro herase
    have hw : Finsupp.weight (fun k : ℕ => k) d = j :=
      CongruenceTheory.isWeightedHomogeneous_C j (MvPolynomial.mem_support_iff.mp hdmem)
    have hrecon : d = d.erase 1 + Finsupp.single 1 (d 1) := by
      ext i
      rw [Finsupp.add_apply, Finsupp.erase_apply, Finsupp.single_apply]
      rcases eq_or_ne i 1 with rfl | hi
      · simp
      · simp [hi, Ne.symm hi]
    have hweq : Finsupp.weight (fun k : ℕ => k) d =
        Finsupp.weight (fun k : ℕ => k) (d.erase 1) +
          Finsupp.weight (fun k : ℕ => k) (Finsupp.single 1 (d 1)) := by
      conv_lhs => rw [hrecon]
      exact map_add _ _ _
    rw [herase, Finsupp.weight_single, Finsupp.weight_single, smul_eq_mul, smul_eq_mul,
      one_mul, mul_one] at hweq
    rw [hw] at hweq
    omega

theorem coeff_single_FmZ_eq_zero_of_lt (p : ℕ) {j s : ℕ} (hjs : j < s) :
    MvPolynomial.coeff (Finsupp.single s 1) (FmZ p j) = 0 := by
  unfold FmZ
  rw [MvPolynomial.coeff_map, coeff_single_Fm_eq_zero_of_lt hjs]
  simp

#print axioms coeff_single_Fm_eq_zero_of_lt
#print axioms coeff_single_FmZ_eq_zero_of_lt

end CongruenceTheory
