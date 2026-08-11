import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.FirstPrimeLayer
import CongruenceTheoryHigherOrder.KWeightedHomogeneous
import CongruenceTheoryHigherOrder.SpecializationUnitCoeff
import CongruenceTheoryHigherOrder.ProductValuation

/-!
**The exact identity `K j p = p^{e_p(j)}\cdot\text{normalizedLayer}(p,j)`.** Since
`p^{e_p(j)}` divides *every* coefficient of `K_j(p)` exactly (`firstPrimeLayer_dvd_arbitrary`),
`divPoly`'s coefficientwise integer division recovers `K_j(p)` exactly upon remultiplying. This
is the algebraic bridge `thm:common-prime-classification`'s sharpness argument needs: writing
`K_j(p) = p^{e_p(j)}\cdot L_j'` as an honest identity of integer polynomials lets the `(A7)` sum be
regrouped as `p^{W_p(\lambda)}` times a polynomial that survives specialization mod `p`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`K_j(p)` equals `p^{e_p(j)}` times its normalized layer, exactly.** -/
theorem K_eq_pow_mul_normalizedLayer {p j : ℕ} (hp : p.Prime) [NeZero j] :
    K j p = MvPolynomial.C ((p : ℤ) ^ firstPrimeLayerExponent p j) * normalizedLayer p j := by
  apply MvPolynomial.ext
  intro d
  rw [coeff_C_mul]
  unfold normalizedLayer
  rw [coeff_divPoly]
  have hdvd : (p : ℤ) ^ firstPrimeLayerExponent p j ∣ coeff d (K j p) :=
    firstPrimeLayer_dvd_arbitrary hp d
  exact (Int.mul_ediv_cancel' hdvd).symm

#print axioms K_eq_pow_mul_normalizedLayer

end CongruenceTheory
