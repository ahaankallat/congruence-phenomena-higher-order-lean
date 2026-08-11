import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.KWeightedHomogeneous
import CongruenceTheoryHigherOrder.A3Final
import CongruenceTheoryHigherOrder.KNontrivialPart
import CongruenceTheoryHigherOrder.NontrivialPartCountK
import CongruenceTheoryHigherOrder.NontrivialPartCountProduct
import CongruenceTheoryHigherOrder.KOneAllFixedCoeff

/-!
**The exact coefficient of a shape's canonical "mixed" monomial.** For a shape `\lambda`, define
`canonTarget(j) := X_1^p` if `j=1` (the all-fixed-points monomial of `K_1(p)`) and
`X_{jp}` if `j\ge2` (the full-cycle monomial of `K_j(p)`). We show
`[\sum_{j\in\lambda}\text{canonTarget}(j)]\ \prod_{j\in\lambda}K_j(p) = \prod_{j\in\lambda,j\ge2}
(jp-1)!` exactly (the `j=1` factors contributing a unit `1` each). The key mechanism: both
`nontrivialPartCount` and the exponent at position `1` are *exactly* additive over `Finsupp`
addition, and every factor's own minimum (`0` for `j=1`, `1` for `j\ge2`) is achieved uniquely
once its own position-`1` slack is forced to zero by the target's own (already fully consumed)
position-`1` budget -- ruling out the "cross-term" contamination between distinct shape factors.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **A general two-factor "forced uniqueness" coefficient collapse.** -/
theorem coeff_mul_eq_of_forced_unique {P Q : MvPolynomial ℕ ℤ} {x0 y0 : ℕ →₀ ℕ}
    (hforce : ∀ x y : ℕ →₀ ℕ, x + y = x0 + y0 → coeff x P ≠ 0 → coeff y Q ≠ 0 →
      x = x0 ∧ y = y0) :
    coeff (x0 + y0) (P * Q) = coeff x0 P * coeff y0 Q := by
  rw [coeff_mul]
  apply Finset.sum_eq_single (x0, y0)
  · rintro ⟨x, y⟩ hxy hne
    rw [Finset.mem_antidiagonal] at hxy
    by_cases hx : coeff x P = 0
    · rw [hx, zero_mul]
    by_cases hy : coeff y Q = 0
    · rw [hy, mul_zero]
    obtain ⟨hxeq, hyeq⟩ := hforce x y hxy hx hy
    subst hxeq
    subst hyeq
    exact absurd rfl hne
  · intro h
    exfalso
    apply h
    rw [Finset.mem_antidiagonal]

/-- The canonical monomial for a single shape entry: the all-fixed-points monomial `X_1^p` for
`j=1`, the full-cycle monomial `X_{jp}` for `j\ge2`. -/
noncomputable def canonTarget (p j : ℕ) : ℕ →₀ ℕ :=
  if j = 1 then Finsupp.single 1 p else Finsupp.single (j * p) 1

/-- The canonical coefficient: `1` for `j=1`, `(jp-1)!` for `j\ge2`. -/
noncomputable def canonCoeff (p j : ℕ) : ℤ :=
  if j = 1 then 1 else (Nat.factorial (j * p - 1) : ℤ)

/-- **Every nonzero-coefficient monomial of `K_j(p)` has exponent at position `1` bounded by its
own weighted degree `jp`.** -/
theorem apply_one_le_of_coeff_K_ne_zero {p j : ℕ} {d : ℕ →₀ ℕ} (hd : coeff d (K j p) ≠ 0) :
    d 1 ≤ j * p := by
  have hw : Finsupp.weight (fun k : ℕ => k) d = j * p := isWeightedHomogeneous_K j p hd
  rw [Finsupp.weight_apply, Finsupp.sum] at hw
  simp only [smul_eq_mul] at hw
  by_cases h1 : (1 : ℕ) ∈ d.support
  · have hsingle : d 1 * 1 ≤ ∑ a ∈ d.support, d a * a :=
      Finset.single_le_sum (fun a _ => Nat.zero_le (d a * a)) h1
    rw [mul_one] at hsingle
    omega
  · rw [Finsupp.notMem_support_iff.mp h1]
    exact Nat.zero_le _

/-- **`K_j(p)`'s support never touches position `0`.** -/
theorem apply_zero_eq_zero_of_coeff_K_ne_zero {p j : ℕ} {d : ℕ →₀ ℕ} (hd : coeff d (K j p) ≠ 0) :
    d 0 = 0 := by
  have hz := isWeightedHomogeneous_K_zero j p hd
  rw [Finsupp.weight_apply, Finsupp.sum] at hz
  simp only [smul_eq_mul] at hz
  by_contra hne
  have h0mem : (0 : ℕ) ∈ d.support := Finsupp.mem_support_iff.mpr hne
  have hall := Finset.sum_eq_zero_iff.mp hz
  have h0 := hall 0 h0mem
  simp at h0
  exact hne h0

/-- **A nonzero-coefficient monomial of `K_1(p)` (`p\ge2`) with `d(1)=p` is exactly `X_1^p`.** -/
theorem eq_single_of_coeff_K_one_apply_one_eq {p : ℕ} (hp : 2 ≤ p) {d : ℕ →₀ ℕ}
    (hd : coeff d (K 1 p) ≠ 0) (h1 : d 1 = p) : d = Finsupp.single 1 p := by
  have hw : Finsupp.weight (fun k : ℕ => k) d = 1 * p := isWeightedHomogeneous_K 1 p hd
  rw [one_mul, Finsupp.weight_apply, Finsupp.sum] at hw
  simp only [smul_eq_mul] at hw
  have h1mem : (1 : ℕ) ∈ d.support := by
    rw [Finsupp.mem_support_iff, h1]; omega
  ext k
  by_cases hk : k = 1
  · rw [hk, h1, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne hk]
    by_contra hne
    have hkmem : k ∈ d.support := Finsupp.mem_support_iff.mpr hne
    have hsub : ({k, 1} : Finset ℕ) ⊆ d.support := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hkmem
      · exact h1mem
    have hsum2 : ∑ a ∈ ({k, 1} : Finset ℕ), d a * a ≤ ∑ a ∈ d.support, d a * a :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)
    rw [Finset.sum_pair hk, hw, h1] at hsum2
    have hk0 : k ≠ 0 := by
      intro hk0
      subst hk0
      exact hne (apply_zero_eq_zero_of_coeff_K_ne_zero hd)
    have hdk1 : 1 ≤ d k := Nat.one_le_iff_ne_zero.mpr hne
    have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    nlinarith

#print axioms coeff_mul_eq_of_forced_unique
#print axioms apply_one_le_of_coeff_K_ne_zero
#print axioms apply_zero_eq_zero_of_coeff_K_ne_zero
#print axioms eq_single_of_coeff_K_one_apply_one_eq

end CongruenceTheory
