import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.Perm
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.KWeightedHomogeneous

/-!
**`C n` and `\Delta_{\mathbf n}` are weighted homogeneous**, weighting `X_k` by `k`: `C n` has
weighted degree `n` (`Cperm_eq_C` transports `isWeightedHomogeneous_ci`'s cycle-index fact from
`Cperm` to `C`), and consequently `\Delta_{\mathbf n}=C(N)-\prod_iC(n_i)` (`N=\sum_in_i`) has
weighted degree `N` too — every monomial occurring in the defect corresponds to an honest
partition of `N`, the fact `D_s`/witness-depth's "coefficients indexed by partitions of `N`"
language depends on.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`C n` is weighted homogeneous of weighted degree `n`**, weighting `X_k` by `k`. -/
theorem isWeightedHomogeneous_C (n : ℕ) : IsWeightedHomogeneous (fun k : ℕ => k) (C n) n := by
  rw [← Cperm_eq_C]
  unfold Cperm
  have hsum : IsWeightedHomogeneous (fun k : ℕ => k)
      (∑ g : Equiv.Perm (Fin n), ci g) (Fintype.card (Fin n)) := by
    apply IsWeightedHomogeneous.sum
    intro g _
    exact isWeightedHomogeneous_ci g
  rwa [Fintype.card_fin] at hsum

/-- Subtracting two weighted-homogeneous polynomials of the same degree stays weighted
homogeneous of that degree. -/
theorem IsWeightedHomogeneous.sub {σ M R : Type*} [CommRing R] [AddCommMonoid M]
    {w : σ → M} {φ ψ : MvPolynomial σ R} {n : M}
    (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ - ψ) n := by
  intro d hd
  rw [MvPolynomial.coeff_sub] at hd
  by_cases h : coeff d φ = 0
  · have hψne : coeff d ψ ≠ 0 := by
      intro hc
      apply hd
      rw [h, hc]
      ring
    exact hψ hψne
  · exact hφ h

/-- A finite product of weighted-homogeneous polynomials is weighted homogeneous of the sum of
their degrees. -/
theorem IsWeightedHomogeneous.finset_prod {σ ι : Type*} {w : σ → ℕ}
    (s : Finset ι) (f : ι → MvPolynomial σ ℤ) (deg : ι → ℕ)
    (h : ∀ i ∈ s, IsWeightedHomogeneous w (f i) (deg i)) :
    IsWeightedHomogeneous w (∏ i ∈ s, f i) (∑ i ∈ s, deg i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    intro d hd
    rw [coeff_one] at hd
    split_ifs at hd with heq
    · rw [← heq]; simp
    · exact absurd rfl hd
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **`\Delta_{p\mathbf u}=C((\sum u_i)p)-\prod_iC(u_ip)` is weighted homogeneous of weighted
degree `(\sum u_i)p`.** -/
theorem isWeightedHomogeneous_defect {r : ℕ} (u : Fin r → ℕ) (p : ℕ) :
    IsWeightedHomogeneous (fun k : ℕ => k)
      (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) ((∑ i, u i) * p) := by
  apply IsWeightedHomogeneous.sub
  · exact isWeightedHomogeneous_C _
  · have hprod := IsWeightedHomogeneous.finset_prod (Finset.univ : Finset (Fin r))
      (fun i => C (u i * p)) (fun i => u i * p) (fun i _ => isWeightedHomogeneous_C (u i * p))
    rwa [← Finset.sum_mul] at hprod

#print axioms isWeightedHomogeneous_C
#print axioms isWeightedHomogeneous_defect

end CongruenceTheory
