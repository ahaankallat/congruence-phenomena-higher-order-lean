import Mathlib
import CongruenceTheoryHigherOrder.PolyOrder

/-!
**`thm:complete-prime-local`(iii)'s `(A11)`: the truncated logarithm.**
`\log_{<p}(1+z) = \sum_{k=1}^{p-1}(-1)^{k+1}z^k/k`, a genuine polynomial function of `z` (a
finite sum, so no formal-power-series or quotient-ring machinery is needed) valued in
`\mathbb F_p[X_2,X_3,\ldots]`. Its degree-one part matches `z`'s own degree-one part; the
manuscript's harder fact (`\log_{<p}` is additive up to degree `p`, i.e. an isomorphism
`1+J\to J` in `\mathbb F_p[\ldots]/J^p`) is the target of the next file.

Degree here always means **ordinary total degree** (`monoDeg`, `PolyOrder.lean`, weighting
every variable `1`) — the grading the `J`-adic order works with — never the cycle-index
weighted degree (weight `X_i` by `i`) used for `C_n`/`F_m`'s own internal weighted-homogeneity.
-/

namespace CongruenceTheory

open MvPolynomial

variable {p : ℕ}

/-- **The truncated logarithm** `\log_{<p}(1+z) = \sum_{k=1}^{p-1}(-1)^{k+1}z^k/k`. -/
noncomputable def logTrunc (p : ℕ) (z : MvPolynomial ℕ (ZMod p)) : MvPolynomial ℕ (ZMod p) :=
  ∑ k ∈ Finset.Icc 1 (p - 1),
    MvPolynomial.C (((-1 : ZMod p) ^ (k + 1)) * (k : ZMod p)⁻¹) * z ^ k

/-- If every monomial of `z` has ordinary degree `\ge m`, every monomial of `z^k` has ordinary
degree `\ge k\cdot m`. -/
theorem monoDeg_pow_ge {R : Type*} [CommRing R] (z : MvPolynomial ℕ R) (m : ℕ)
    (hz : ∀ d ∈ z.support, m ≤ monoDeg d) :
    ∀ k : ℕ, ∀ d ∈ (z ^ k).support, k * m ≤ monoDeg d := by
  intro k
  induction k with
  | zero => intro d hd; simp at hd; simp [hd]
  | succ k ih =>
    intro d hd
    rw [pow_succ] at hd
    have hd' : d ∈ (z ^ k * z).support := hd
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at hd'
    by_contra hcon
    push_neg at hcon
    apply hd'
    apply Finset.sum_eq_zero
    rintro ⟨d1, d2⟩ hmem
    simp only [Finset.mem_antidiagonal] at hmem
    by_cases hd1 : MvPolynomial.coeff d1 (z ^ k) = 0
    · simp [hd1]
    by_cases hd2 : MvPolynomial.coeff d2 z = 0
    · simp [hd2]
    exfalso
    have hge1 : k * m ≤ monoDeg d1 := ih d1 (MvPolynomial.mem_support_iff.mpr hd1)
    have hge2 : m ≤ monoDeg d2 := hz d2 (MvPolynomial.mem_support_iff.mpr hd2)
    have hdeq : monoDeg d = monoDeg d1 + monoDeg d2 := by rw [← hmem, monoDeg_add]
    have : (k + 1) * m = k * m + m := by ring
    omega

/-- **The degree-one part of `\log_{<p}(1+z)` matches `z`'s own degree-one part**, for `z` with
ordinary degree `\ge1` throughout (`z\in J`). -/
theorem coeff_single_logTrunc (hp : 2 ≤ p) (z : MvPolynomial ℕ (ZMod p)) {s : ℕ} (hs1 : 1 ≤ s)
    (hz : ∀ d ∈ z.support, 1 ≤ monoDeg d) :
    MvPolynomial.coeff (Finsupp.single s 1) (logTrunc p z) =
      MvPolynomial.coeff (Finsupp.single s 1) z := by
  unfold logTrunc
  rw [MvPolynomial.coeff_sum]
  have hp1 : (1 : ℕ) ∈ Finset.Icc 1 (p - 1) := by
    simp only [Finset.mem_Icc]; omega
  rw [← Finset.sum_erase_add _ _ hp1]
  have hzero : ∑ k ∈ (Finset.Icc 1 (p - 1)).erase 1,
      MvPolynomial.coeff (Finsupp.single s 1)
        (MvPolynomial.C (((-1 : ZMod p) ^ (k + 1)) * (k : ZMod p)⁻¹) * z ^ k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk2 : 2 ≤ k := by
      simp only [Finset.mem_erase, Finset.mem_Icc] at hk
      omega
    rw [MvPolynomial.coeff_C_mul]
    have hsingle_deg : monoDeg (Finsupp.single s 1 : ℕ →₀ ℕ) = 1 := by
      rw [monoDeg_eq_sum]
      simp
    have hcoeffzero : MvPolynomial.coeff (Finsupp.single s 1) (z ^ k) = 0 := by
      by_contra hne
      have hmem : (Finsupp.single s 1 : ℕ →₀ ℕ) ∈ (z ^ k).support :=
        MvPolynomial.mem_support_iff.mpr hne
      have hge := monoDeg_pow_ge z 1 hz k _ hmem
      rw [hsingle_deg] at hge
      omega
    rw [hcoeffzero, mul_zero]
  rw [hzero, zero_add]
  simp

#print axioms monoDeg_pow_ge
#print axioms coeff_single_logTrunc

end CongruenceTheory
