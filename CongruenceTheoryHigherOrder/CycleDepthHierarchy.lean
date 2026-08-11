import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.DefectWeightedHomogeneous

/-!
**`cor:cycle-depth-hierarchy` and `def:prime-cycle-depth`, formalized.** For an integer
polynomial `\varphi` (in practice `\Delta_{\mathbf n}`), `cont(\varphi)` is the gcd of all its
coefficients, and `D_s(\varphi)` the gcd of only those coefficients indexed by monomials with at
most `s` "nontrivial" (exponent-`\ge2`-index) parts. Enlarging `s` only shrinks the index set's
gcd, giving the hierarchy `cont(\varphi)\mid D_{s+1}(\varphi)\mid D_s(\varphi)`; and since
`\Delta_{\mathbf n}` is weighted homogeneous of degree `N` (`isWeightedHomogeneous_defect`), every
one of its monomials has at most `N/2` nontrivial parts, so `D_{N/2}=\operatorname{cont}`. This is
the foundational apparatus `\delta_p` (`def:prime-cycle-depth`) is built from.
-/

namespace CongruenceTheory

open MvPolynomial

/-- The number of "nontrivial" (index `\ge2`) parts of a monomial exponent, counted with
multiplicity — the manuscript's own notion of how many parts of the underlying partition of `N`
exceed `1`. -/
noncomputable def nontrivialPartCount (d : ℕ →₀ ℕ) : ℕ := ∑ k ∈ d.support.filter (2 ≤ ·), d k

/-- **The content of an integer polynomial**: the gcd of all its coefficients. -/
noncomputable def cont (φ : MvPolynomial ℕ ℤ) : ℕ :=
  φ.support.gcd (fun d => (coeff d φ).natAbs)

/-- **`D_s(\varphi)`**: the gcd of the coefficients of `\varphi` indexed by monomials having at
most `s` nontrivial parts. -/
noncomputable def Dgcd (φ : MvPolynomial ℕ ℤ) (s : ℕ) : ℕ :=
  (φ.support.filter (fun d => nontrivialPartCount d ≤ s)).gcd (fun d => (coeff d φ).natAbs)

/-- **`cont(\varphi)` divides every `D_s(\varphi)`.** -/
theorem cont_dvd_Dgcd (φ : MvPolynomial ℕ ℤ) (s : ℕ) : cont φ ∣ Dgcd φ s :=
  Finset.gcd_mono (Finset.filter_subset _ _)

/-- **`D_{s+1}(\varphi) \mid D_s(\varphi)`**: enlarging the allowed nontrivial-part count only
shrinks the gcd. -/
theorem Dgcd_succ_dvd (φ : MvPolynomial ℕ ℤ) (s : ℕ) : Dgcd φ (s + 1) ∣ Dgcd φ s := by
  apply Finset.gcd_mono
  intro d hd
  rw [Finset.mem_filter] at hd ⊢
  exact ⟨hd.1, by omega⟩

/-- **Every monomial of a weighted-homogeneous-of-degree-`N` polynomial has at most `N/2`
nontrivial parts.** -/
theorem nontrivialPartCount_le_half {φ : MvPolynomial ℕ ℤ} {N : ℕ}
    (hφ : IsWeightedHomogeneous (fun k : ℕ => k) φ N) {d : ℕ →₀ ℕ} (hd : coeff d φ ≠ 0) :
    nontrivialPartCount d ≤ N / 2 := by
  have hw : Finsupp.weight (fun k : ℕ => k) d = N := hφ hd
  rw [Finsupp.weight_apply, Finsupp.sum] at hw
  simp only [smul_eq_mul] at hw
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  unfold nontrivialPartCount
  rw [← hw]
  calc (∑ k ∈ d.support.filter (2 ≤ ·), d k) * 2
      = ∑ k ∈ d.support.filter (2 ≤ ·), d k * 2 := by rw [Finset.sum_mul]
    _ ≤ ∑ k ∈ d.support.filter (2 ≤ ·), d k * k := by
        apply Finset.sum_le_sum
        intro k hk
        have h2 : 2 ≤ k := (Finset.mem_filter.mp hk).2
        exact Nat.mul_le_mul_left (d k) h2
    _ ≤ ∑ k ∈ d.support, d k * k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        exact Nat.zero_le _

/-- **`D_{N/2}(\varphi)=\operatorname{cont}(\varphi)`** for `\varphi` weighted homogeneous of
degree `N`: every monomial already has at most `N/2` nontrivial parts, so the filter is vacuous
and `D_{N/2}` ranges over the full support. -/
theorem Dgcd_half_eq_cont {φ : MvPolynomial ℕ ℤ} {N : ℕ}
    (hφ : IsWeightedHomogeneous (fun k : ℕ => k) φ N) : Dgcd φ (N / 2) = cont φ := by
  unfold Dgcd cont
  congr 1
  apply Finset.filter_true_of_mem
  intro d hd
  exact nontrivialPartCount_le_half hφ (mem_support_iff.mp hd)

#print axioms cont_dvd_Dgcd
#print axioms Dgcd_succ_dvd
#print axioms nontrivialPartCount_le_half
#print axioms Dgcd_half_eq_cont

end CongruenceTheory
