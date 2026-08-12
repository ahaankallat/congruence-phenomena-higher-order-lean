import Mathlib
import CongruenceTheoryHigherOrder.DcDef
import CongruenceTheoryHigherOrder.FmModP

/-!
**`thm:complete-prime-local`(iii)'s `(A12)`: the Frobenius factorization.**
Under the digit conditions (`c_s=pc'_s+\varepsilon_s`, `h=ph'`), `D_{\mathbf c}` factors
*exactly* (not just mod `J^p`) as `F_r\cdot D_{\mathbf c'}^p`, via the char-`p` Frobenius identity
`a^p-b^p=(a-b)^p` — a purely algebraic identity needing no order/degree machinery at all. This
is dramatically simpler than building the manuscript's truncated-log route, and gives both
(A12) itself and (A11)'s "order `\ge p`" direction together (via `PolyOrder.lean`'s degree
machinery applied to this exact factorization).
-/

namespace CongruenceTheory

open MvPolynomial

/-- **Frobenius**: `a^p - b^p = (a-b)^p` in a commutative ring of characteristic `p`. -/
theorem sub_pow_char {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) [CharP R p] (a b : R) :
    a ^ p - b ^ p = (a - b) ^ p := by
  haveI := Fact.mk hp
  have h2 : (a - b + b) ^ p = (a - b) ^ p + b ^ p := add_pow_char (a - b) b p
  rw [show a - b + b = a from by ring] at h2
  linear_combination h2

theorem FmZ_one (p : ℕ) : FmZ p 1 = 1 := by
  unfold FmZ
  rw [Fm_one, map_one]

/-- **The product side of the Frobenius factorization.** Only the digits `c_s` for `2\le s\le
p-1` are constrained: `c_1` is irrelevant to `D_{\mathbf c}` since `F_1\equiv1`
(`FmZ_one`). -/
theorem prod_FmZ_pow_eq (p r : ℕ) (hr2 : 2 ≤ r) (hrp : r ≤ p - 1) (c c' : ℕ → ℕ)
    (hc : ∀ s ∈ Finset.Icc 2 (p - 1), c s = p * c' s + (if s = r then 1 else 0)) :
    ∏ s ∈ Finset.Icc 1 (p - 1), FmZ p s ^ c s =
      FmZ p r * (∏ s ∈ Finset.Icc 1 (p - 1), FmZ p s ^ c' s) ^ p := by
  have hstep1 : ∀ s ∈ Finset.Icc 1 (p - 1),
      FmZ p s ^ c s = (FmZ p s ^ c' s) ^ p * (if s = r then FmZ p s else 1) := by
    intro s hs
    by_cases hs1 : s = 1
    · subst hs1
      have hsr : (1 : ℕ) ≠ r := by omega
      rw [FmZ_one, if_neg hsr]
      simp
    · have hs2 : 2 ≤ s := by
        simp only [Finset.mem_Icc] at hs; omega
      rw [hc s (Finset.mem_Icc.mpr ⟨hs2, (Finset.mem_Icc.mp hs).2⟩), pow_add, pow_mul']
      by_cases hsr : s = r
      · rw [if_pos hsr, if_pos hsr, pow_one]
      · rw [if_neg hsr, if_neg hsr, pow_zero]
  rw [Finset.prod_congr rfl hstep1, Finset.prod_mul_distrib, Finset.prod_pow]
  have hindic : ∏ s ∈ Finset.Icc 1 (p - 1), (if s = r then FmZ p s else 1) = FmZ p r := by
    rw [Finset.prod_ite_eq' (Finset.Icc 1 (p - 1)) r (FmZ p)]
    rw [if_pos (Finset.mem_Icc.mpr ⟨by omega, hrp⟩)]
  rw [hindic]
  ring

/-- **The Frobenius factorization (A12)**: under the digit conditions, `D_{\mathbf c}` factors
exactly as `F_r\cdot D_{\mathbf c'}^p`. -/
theorem Dc_frobenius_factorization (p r h h' : ℕ) (hp : p.Prime) (c c' : ℕ → ℕ)
    (hr2 : 2 ≤ r) (hrp : r ≤ p - 1)
    (hh : h = p * h')
    (hc : ∀ s ∈ Finset.Icc 2 (p - 1), c s = p * c' s + (if s = r then 1 else 0)) :
    Dc p r h c = FmZ p r * (Dc p 1 h' c') ^ p := by
  unfold Dc
  rw [hh, pow_mul', prod_FmZ_pow_eq p r hr2 hrp c c' hc]
  rw [FmZ_one, one_mul]
  rw [show FmZ p r * ((1 - MvPolynomial.X p) ^ h') ^ p -
      FmZ p r * (∏ s ∈ Finset.Icc 1 (p - 1), FmZ p s ^ c' s) ^ p =
      FmZ p r * (((1 - MvPolynomial.X p) ^ h') ^ p -
        (∏ s ∈ Finset.Icc 1 (p - 1), FmZ p s ^ c' s) ^ p) from by ring]
  rw [sub_pow_char hp]

#print axioms sub_pow_char
#print axioms FmZ_one
#print axioms prod_FmZ_pow_eq
#print axioms Dc_frobenius_factorization

end CongruenceTheory
