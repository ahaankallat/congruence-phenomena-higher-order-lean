import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.FirstPrimeLayer
import CongruenceTheoryHigherOrder.SpecializationVars
import CongruenceTheoryHigherOrder.SpecializationUnitCoeff
import CongruenceTheoryHigherOrder.TriangularIndependenceFinal
import CongruenceTheoryHigherOrder.Noncancellation
import CongruenceTheoryHigherOrder.DefectValuationExactWeight
import CongruenceTheoryHigherOrder.DefectLeadingTermDecomposition

/-!
**`thm:common-prime-classification`'s sharpness direction, assembled.** `specialize` sends
`divPoly \Delta_{p\mathbf u} (p^E)` to `\sum_{\lambda:W_p(\lambda)=E}\bar a_\lambda\prod_{j\in
\lambda}L_j` (the `p`-divisible remainder vanishing outright), which is exactly `\text{aeval}
(\text{triangularFamily}\,p)` applied to a sum of *distinct* monomials (`Multiset.toFinsupp` is
injective). `triangular_independence`'s noncancellation then shows this is nonzero whenever some
minimum-weight shape survives with `\bar a_\lambda\ne0`, giving a coefficient of `\Delta_{p\mathbf
u}` not divisible by `p^{E+1}`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **A multiset product, mapped through any function `x`, equals the `Finsupp.prod` of the
multiset's own multiplicity function.** -/
theorem multiset_prod_map_eq_finsuppProd {A : Type*} [CommMonoid A] (lam : Multiset ℕ) (x : ℕ → A) :
    (lam.map x).prod = (Multiset.toFinsupp lam).prod (fun i k => x i ^ k) := by
  induction lam using Multiset.induction with
  | empty => simp
  | cons j s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih]
    have heq1 : Multiset.toFinsupp (j ::ₘ s) = Finsupp.single j 1 + Multiset.toFinsupp s := by
      rw [show (j ::ₘ s) = {j} + s from by simp, Multiset.toFinsupp_add,
        Multiset.toFinsupp_singleton]
    rw [heq1, Finsupp.prod_add_index' (h_zero := fun a => pow_zero (x a))
      (h_add := fun a b1 b2 => pow_add (x a) b1 b2)]
    congr 1
    exact ((Finsupp.prod_single_index (h := fun i k => x i ^ k) (pow_zero (x j))).trans
      (pow_one _)).symm

/-- **`aeval` of the bare monomial at a multiset's own multiplicity Finsupp equals the multiset
product of `x`.** -/
theorem aeval_monomial_toFinsupp {p : ℕ} {A : Type*} [CommRing A] [Algebra (ZMod p) A] (x : ℕ → A)
    (lam : Multiset ℕ) :
    aeval x (monomial (Multiset.toFinsupp lam) (1 : ZMod p)) = (lam.map x).prod := by
  rw [aeval_monomial, multiset_prod_map_eq_finsuppProd lam x]
  simp

variable (p : ℕ) [Fact (Nat.Prime p)]

theorem specialize_C (x : ℤ) :
    specialize p (MvPolynomial.C x) = MvPolynomial.C ((x : ZMod p)) := by
  simp

/-- **`specialize` sends a product of normalized layers to the corresponding product of
`triangularFamily` terms**, for a multiset of block sizes all `\ge1`. -/
theorem specialize_prod_normalizedLayer (lam : Multiset ℕ) (hlam : ∀ j ∈ lam, 1 ≤ j) :
    specialize p ((lam.map (fun j => normalizedLayer p j)).prod) =
      (lam.map (fun j => triangularFamily p j)).prod := by
  rw [map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro j hj
  have hj1 := hlam j hj
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rfl

/-- **`divPoly \Delta_{p\mathbf u}(p^E)` equals the leading sum plus `p` times the remainder,
exactly.** -/
theorem divPoly_defect_eq {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ) (hu : ∀ i, 0 < u i) (E : ℕ)
    (hE : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape, E ≤ Wp u p lam) :
    divPoly (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) ((p : ℤ) ^ E) =
      (∑ lam ∈ ((nonRefiningPartitions u).image GenPartLatShape).filter
            (fun lam => Wp u p lam = E),
          MvPolynomial.C ((ordCompl[p] (Alam u lam) : ℕ) : ℤ) *
            (lam.map (fun j => normalizedLayer p j)).prod) +
        MvPolynomial.C (p : ℤ) *
          (∑ lam ∈ ((nonRefiningPartitions u).image GenPartLatShape).filter
                (fun lam => E < Wp u p lam),
              MvPolynomial.C ((p : ℤ) ^ (Wp u p lam - E - 1) *
                ((ordCompl[p] (Alam u lam) : ℕ) : ℤ)) *
                (lam.map (fun j => normalizedLayer p j)).prod) := by
  apply MvPolynomial.ext
  intro d
  rw [coeff_divPoly, defect_eq_leading_add_remainder hr u hu (Fact.out (p := Nat.Prime p)) E hE,
    coeff_C_mul]
  have hne : ((p : ℤ) ^ E) ≠ 0 :=
    pow_ne_zero E (by exact_mod_cast (Fact.out (p := Nat.Prime p)).pos.ne')
  exact Int.mul_ediv_cancel_left _ hne

/-- **`specialize` sends `divPoly \Delta_{p\mathbf u}(p^E)` to the reduction of the leading sum
alone** — the `p`-divisible remainder vanishes outright. -/
theorem specialize_divPoly_defect_eq {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ) (hu : ∀ i, 0 < u i)
    (E : ℕ) (hE : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape, E ≤ Wp u p lam) :
    specialize p (divPoly (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) ((p : ℤ) ^ E)) =
      ∑ lam ∈ ((nonRefiningPartitions u).image GenPartLatShape).filter
            (fun lam => Wp u p lam = E),
        MvPolynomial.C (((ordCompl[p] (Alam u lam) : ℕ) : ℤ) : ZMod p) *
          (lam.map (fun j => triangularFamily p j)).prod := by
  have hshape1 : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape, ∀ j ∈ lam, 1 ≤ j := by
    intro lam hlam j hj
    obtain ⟨π, -, hπ⟩ := Finset.mem_image.mp hlam
    rw [← hπ] at hj
    obtain ⟨B, hB, hBj⟩ := Multiset.mem_map.mp hj
    have hBmem : B ∈ π.parts := hB
    have := Finset.card_pos.mpr (π.nonempty_of_mem_parts hBmem)
    omega
  rw [divPoly_defect_eq p hr u hu E hE]
  simp only [map_add, map_sum, map_mul, specialize_C, Int.cast_natCast, ZMod.natCast_self,
    MvPolynomial.C_0, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro lam hlam
  rw [Finset.mem_filter] at hlam
  rw [specialize_prod_normalizedLayer p lam (hshape1 lam hlam.1)]

#print axioms multiset_prod_map_eq_finsuppProd
#print axioms aeval_monomial_toFinsupp
#print axioms specialize_C
#print axioms specialize_prod_normalizedLayer
#print axioms divPoly_defect_eq
#print axioms specialize_divPoly_defect_eq

end CongruenceTheory
