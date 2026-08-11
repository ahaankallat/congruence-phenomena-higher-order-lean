import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.CommonPrimeClassificationValuation
import CongruenceTheoryHigherOrder.CommonPrimeClassificationDepth
import CongruenceTheoryHigherOrder.CycleDepthHierarchy

/-!
**`thm:complete-prime-local`'s general defect notation and case (i).** `Delta n := C(N) -
\prod_i C(n_i)` for a general tuple `n`, matching the manuscript's `\Delta_{\mathbf n}`. Case (i)
(`U_p(\mathbf n)=\varnothing`, i.e. `p\mid n_i` for all `i`) reduces directly to
`thm:common-prime-classification` (`common_prime_classification_valuation` /
`common_prime_classification_depth`), already fully assembled.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **The general higher-order defect** `\Delta_{\mathbf n} = C(N) - \prod_i C(n_i)`,
`N=\sum_i n_i`. -/
noncomputable def Delta {r : ℕ} (n : Fin r → ℕ) : MvPolynomial ℕ ℤ :=
  C (∑ i, n i) - ∏ i, C (n i)

theorem Delta_eq_common_prime {r : ℕ} (u : Fin r → ℕ) (p : ℕ) :
    Delta (fun i => p * u i) = C ((∑ i, u i) * p) - ∏ i, C (u i * p) := by
  unfold Delta
  have hsum : (∑ i, p * u i) = (∑ i, u i) * p := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => mul_comm p (u i))
  rw [hsum]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => by dsimp only; rw [mul_comm p (u i)])

/-- **`thm:complete-prime-local`, case (i)**: for `U_p(\mathbf n)=\varnothing` (i.e. `p \mid n_i`
for every `i`, encoded as `n_i = p u_i`), content and depth are given by
`thm:common-prime-classification`. -/
theorem complete_prime_local_case_i {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ) (hu : ∀ i, 0 < u i)
    {p : ℕ} [Fact (Nat.Prime p)]
    (hne : ((nonRefiningPartitions u).image GenPartLatShape).Nonempty) :
    (∀ d, (p : ℤ) ^ ((((nonRefiningPartitions u).image GenPartLatShape).image (Wp u p)).min'
          (hne.image _)) ∣ coeff d (Delta (fun i => p * u i))) ∧
      ∃ d, ¬ ((p : ℤ) ^ ((((nonRefiningPartitions u).image GenPartLatShape).image (Wp u p)).min'
            (hne.image _) + 1) ∣ coeff d (Delta (fun i => p * u i))) := by
  rw [Delta_eq_common_prime]
  exact common_prime_classification_valuation hr u hu hne

theorem complete_prime_local_case_i_depth {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ)
    (hu : ∀ i, 0 < u i) {p : ℕ} [Fact (Nat.Prime p)] (E : ℕ)
    (hE : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape, E ≤ Wp u p lam)
    (lamE : Multiset ℕ) (hlamEmem : lamE ∈ (nonRefiningPartitions u).image GenPartLatShape)
    (hlamEeq : Wp u p lamE = E) :
    ∃ kmin : ℕ, 1 ≤ kmin ∧
      IsLeast {s : ℕ | 1 ≤ s ∧ (Dgcd (Delta (fun i => p * u i)) s).factorization p = E} kmin := by
  rw [Delta_eq_common_prime]
  exact common_prime_classification_depth hr u hu E hE lamE hlamEmem hlamEeq

#print axioms Delta_eq_common_prime
#print axioms complete_prime_local_case_i
#print axioms complete_prime_local_case_i_depth

end CongruenceTheory
