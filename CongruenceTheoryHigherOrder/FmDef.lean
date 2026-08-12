import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.Perm
import CongruenceTheory.CpermEqC
import CongruenceTheory.CoeffExtraction
import CongruenceTheory.PrimeWitness

/-!
**`thm:complete-prime-local`(iii)'s `(A11)`: `F_m(y) := C_m(1,y_2,\ldots,y_m)`.**
Defines `Fm` as the `X_1\mapsto1` specialization of `C_m` (working directly in
`MvPolynomial \N \Z`, using `X_i` itself in place of the manuscript's `y_i`), and computes the
coefficient of its lowest-degree witness monomial `X_m` — needed for the base case of the
(A11)/(A12) order argument.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **The coefficient of `X_m` (the full `m`-cycle monomial) in `C_m` is `(m-1)!`.** -/
theorem coeff_single_C (m : ℕ) (hm : 2 ≤ m) :
    MvPolynomial.coeff (Finsupp.single m 1) (C m) = (Nat.factorial (m - 1) : ℤ) := by
  rw [← Cperm_eq_C]
  have hkey := coeff_Cperm_eq_card_cycleType m ({m} : Multiset ℕ) (by simpa using hm)
  have hexp : ciExp (m - ({m} : Multiset ℕ).sum) ({m} : Multiset ℕ) = Finsupp.single m 1 := by
    have h0 : m - ({m} : Multiset ℕ).sum = 0 := by simp
    simp [ciExp, h0]
  rw [hexp] at hkey
  rw [hkey]
  have hcard := card_singleCycle_eq_choose_mul (α := Fin m) m hm
  rw [Fintype.card_fin, Nat.choose_self, one_mul] at hcard
  rw [hcard]

/-- **`F_m(y) := C_m(1,y_2,\ldots,y_m)`**: the `X_1\mapsto1` specialization of `C_m`, working
directly in `\text{MvPolynomial}\;\N\;\Z` (`X_i`, `i\ge2`, plays the role of `y_i`). -/
noncomputable def Fm (m : ℕ) : MvPolynomial ℕ ℤ :=
  MvPolynomial.bind₁ (fun i => if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) (C m)

theorem Fm_zero : Fm 0 = 1 := by simp [Fm, C_zero]

theorem Fm_one : Fm 1 = 1 := by
  have hC1 : C 1 = MvPolynomial.X 1 := by
    rw [C_succ]; simp [fall, C_zero]
  simp [Fm, hC1]

#print axioms coeff_single_C
#print axioms Fm_zero
#print axioms Fm_one

end CongruenceTheory
