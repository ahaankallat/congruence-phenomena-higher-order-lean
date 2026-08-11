import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.DefectValuationExactWeight
import CongruenceTheoryHigherOrder.DefectSharpness

/-!
**`thm:common-prime-classification`'s valuation formula, fully assembled.** Writing
`E:=\min_{A_\lambda(\mathbf u)>0}W_p(\lambda;\mathbf u)` (well defined whenever some non-refining
partition exists), `p^E` divides every coefficient of `\Delta_{p\mathbf u}`
(`dvd_coeff_defect_Wp`), and some coefficient is not divisible by `p^{E+1}`
(`exists_coeff_not_dvd_pow_succ`, applied at any shape realizing the minimum) — together pinning
down `v_p(\operatorname{cont}\Delta_{p\mathbf u})=E` exactly, matching the manuscript's boxed
formula.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`thm:common-prime-classification`'s valuation formula.** For `p\mid n_i` all `i` (encoded
as `n_i=pu_i`), writing `E` for the minimum `W_p`-weight among shapes actually achieved by some
non-refining partition of the `p`-microblocks: `p^E` divides every coefficient of
`\Delta_{p\mathbf u}`, and some coefficient is not divisible by `p^{E+1}` — i.e. `E` is exactly
`v_p(\operatorname{cont}\Delta_{p\mathbf u})`. -/
theorem common_prime_classification_valuation {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ)
    (hu : ∀ i, 0 < u i) {p : ℕ} [Fact (Nat.Prime p)]
    (hne : ((nonRefiningPartitions u).image GenPartLatShape).Nonempty) :
    (∀ d, (p : ℤ) ^ ((((nonRefiningPartitions u).image GenPartLatShape).image (Wp u p)).min'
          (hne.image _)) ∣
        coeff d (C ((∑ i, u i) * p) - ∏ i, C (u i * p))) ∧
      ∃ d, ¬ ((p : ℤ) ^ ((((nonRefiningPartitions u).image GenPartLatShape).image (Wp u p)).min'
            (hne.image _) + 1) ∣
          coeff d (C ((∑ i, u i) * p) - ∏ i, C (u i * p))) := by
  set W := ((nonRefiningPartitions u).image GenPartLatShape).image (Wp u p) with hW
  have hWne : W.Nonempty := hne.image _
  show (∀ d, (p : ℤ) ^ (W.min' hWne) ∣
      coeff d (C ((∑ i, u i) * p) - ∏ i, C (u i * p))) ∧
    ∃ d, ¬ ((p : ℤ) ^ (W.min' hWne + 1) ∣
      coeff d (C ((∑ i, u i) * p) - ∏ i, C (u i * p)))
  set E := W.min' hWne with hEdef
  have hE : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape, E ≤ Wp u p lam := by
    intro lam hlam
    rw [hEdef]
    exact Finset.min'_le W (Wp u p lam) (by rw [hW]; exact Finset.mem_image_of_mem _ hlam)
  refine ⟨dvd_coeff_defect_Wp hr u hu (Fact.out (p := Nat.Prime p)) E hE, ?_⟩
  have hEmem : E ∈ W := by rw [hEdef]; exact Finset.min'_mem W hWne
  rw [hW] at hEmem
  obtain ⟨lam0, hlam0mem, hlam0eq⟩ := Finset.mem_image.mp hEmem
  exact exists_coeff_not_dvd_pow_succ hr u hu E hE lam0 hlam0mem hlam0eq

#print axioms common_prime_classification_valuation

end CongruenceTheory
