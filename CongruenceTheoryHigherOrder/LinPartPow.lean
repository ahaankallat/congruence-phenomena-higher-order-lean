import Mathlib
import CongruenceTheoryHigherOrder.PolyOrder
import CongruenceTheoryHigherOrder.LinPart

/-!
**`thm:complete-prime-local`(iii)'s `(A11)`: degree-one linearization of powers.**
Specializes `LinPart.lean`'s finite-product results to `k`-fold self-products (i.e. powers) of
a single `1+J`-unit, via the constant function on `Finset.range k`.
-/

namespace CongruenceTheory

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- `(1+a)^k - 1` lies in `J`, given `a\in J`. -/
theorem pow_one_add_sub_one_deg_ge_one (a : MvPolynomial ℕ R) (k : ℕ)
    (ha : ∀ d ∈ a.support, 1 ≤ monoDeg d) :
    ∀ d ∈ ((1 + a) ^ k - 1).support, 1 ≤ monoDeg d := by
  have hrw : (1 + a) ^ k - 1 = ∏ i ∈ Finset.range k, (1 + a) - 1 := by
    rw [Finset.prod_const, Finset.card_range]
  rw [hrw]
  exact prod_one_add_sub_one_deg_ge_one (Finset.range k) (fun _ => a) (fun i _ => ha)

/-- **Degree-one linearization of a power**: `\text{coeff}_{X_t}((1+a)^k) = k\cdot
\text{coeff}_{X_t}(a)`. -/
theorem coeff_single_pow_add_one (a : MvPolynomial ℕ R) (k : ℕ)
    (ha : ∀ d ∈ a.support, 1 ≤ monoDeg d) {t : ℕ} :
    MvPolynomial.coeff (Finsupp.single t 1) ((1 + a) ^ k) =
      (k : R) * MvPolynomial.coeff (Finsupp.single t 1) a := by
  have hrw : (1 + a) ^ k = ∏ i ∈ Finset.range k, (1 + a) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [hrw, coeff_single_finset_prod_add_one (Finset.range k) (fun _ => a) (fun i _ => ha)]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

#print axioms pow_one_add_sub_one_deg_ge_one
#print axioms coeff_single_pow_add_one

end CongruenceTheory
