import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.Perm
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.FullCycleConnected
import CongruenceTheoryHigherOrder.CiFullCycle
import CongruenceTheoryHigherOrder.CiConverse
import CongruenceTheoryHigherOrder.FullCycleCount
import CongruenceTheoryHigherOrder.A3Final
import CongruenceTheoryHigherOrder.LegendreA3
import CongruenceTheoryHigherOrder.KWeightedHomogeneous
import CongruenceTheoryHigherOrder.SpecializationVars
import CongruenceTheoryHigherOrder.FirstPrimeLayer
import CongruenceTheoryHigherOrder.TriangularIndependence
import CongruenceTheoryHigherOrder.SpecializationUnitCoeff
import CongruenceTheoryHigherOrder.SpecializationCoefficient
import CongruenceTheoryHigherOrder.TriangularAssembly
import CongruenceTheoryHigherOrder.TriangularIndependenceFinal

/-!
**The noncancellation step `cor:triangular-independence` feeds into `thm:common-prime-classification`**:
"minimum-weight terms cannot cancel modulo `p`." Formalized here as its natural general form: a
finite `ZMod p`-linear combination of *distinct* monomials in the algebraically independent family
`triangularFamily p` vanishes only if every coefficient vanishes. This is the translation from
`AlgebraicIndependent` (an abstract injectivity statement) to the concrete "distinct exponent
patterns in `L_1,L_2,\ldots` don't cancel" fact the manuscript's proof of (A7)'s minimum-weight
argument actually uses.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **Distinct monomials in an algebraically independent family are `R`-linearly independent
after evaluation.** If `\sum_\lambda c_\lambda\prod_j x_j^{m_\lambda(j)}=0` for *distinct*
exponent patterns `m_\lambda`, every `c_\lambda` vanishes. -/
theorem eq_zero_of_sum_aeval_monomial_eq_zero {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x : ℕ → A} (hx : AlgebraicIndependent R x) {Λ : Type*} [Fintype Λ]
    [DecidableEq Λ] (m : Λ → ℕ →₀ ℕ) (hinj : Function.Injective m) (c : Λ → R)
    (hsum : ∑ lam, c lam • aeval x (monomial (m lam) (1 : R)) = 0) :
    ∀ lam, c lam = 0 := by
  have hpre : aeval x (∑ lam, c lam • monomial (m lam) (1 : R)) = 0 := by
    rw [map_sum]
    simp only [map_smul]
    exact hsum
  have hzero : (∑ lam, c lam • monomial (m lam) (1 : R) : MvPolynomial ℕ R) = 0 :=
    hx.eq_zero_of_aeval_eq_zero _ hpre
  intro lam0
  have hcoeff := congrArg (MvPolynomial.coeff (m lam0)) hzero
  rw [coeff_sum] at hcoeff
  simp only [coeff_smul, coeff_monomial] at hcoeff
  rw [Finset.sum_eq_single lam0] at hcoeff
  · simpa using hcoeff
  · intro lam _ hne
    rw [if_neg (fun h => hne (hinj h))]
    simp
  · intro h
    exact absurd (Finset.mem_univ lam0) h

#print axioms eq_zero_of_sum_aeval_monomial_eq_zero

end CongruenceTheory
