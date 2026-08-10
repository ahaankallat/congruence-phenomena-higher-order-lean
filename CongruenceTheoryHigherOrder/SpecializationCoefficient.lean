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

/-!
**`cor:triangular-independence`, fully assembled.** Combines `specialize_K_vars_subset`
(`SpecializationVars.lean`) and `eq_single_of_specSubst_finsuppProd_eq_target`
(`SpecializationUnitCoeff.lean`) to compute `specialize p (normalizedLayer p j)`'s coefficient at
the bare target monomial `X_j` exactly: it is the image of `ordCompl[p]((jp-1)!)`, a `p`-unit by
`Nat.not_dvd_ordCompl` combined with `firstPrimeLayer`'s exact-valuation fact. Packaging `L_j`
(`j\ge2`) alongside `L_1 := C_p` as a single family, `algebraicIndependent_of_triangular`
(`TriangularIndependence.lean`) then gives `triangular_independence`, the manuscript's
`cor:triangular-independence` itself.
-/

namespace CongruenceTheory

open MvPolynomial

/-- `normalizedLayer p j`'s coefficient at the full-cycle monomial `X_{jp}`, computed exactly. -/
theorem coeff_single_normalizedLayer {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) (hn : 2 ≤ j * p) :
    coeff (Finsupp.single (j * p) 1) (normalizedLayer p j) =
      ((Nat.factorial (j * p - 1) / p ^ firstPrimeLayerExponent p j : ℕ) : ℤ) := by
  unfold normalizedLayer
  rw [coeff_divPoly, (firstPrimeLayer hp hj hn).2.1]
  have hfact : (Nat.factorial (j * p - 1)).factorization p = firstPrimeLayerExponent p j :=
    (firstPrimeLayer hp hj hn).2.2
  have hdvd : p ^ firstPrimeLayerExponent p j ∣ Nat.factorial (j * p - 1) := by
    rw [← hfact]
    exact Nat.ordProj_dvd (Nat.factorial (j * p - 1)) p
  rw [Int.natCast_div]
  push_cast
  rfl

/-- **The coefficient of `z_j` in `specialize p (normalizedLayer p j)` is exactly the image of
`ordCompl[p]((jp-1)!)`, a `p`-unit.** -/
theorem coeff_target_specialize_normalizedLayer {p j : ℕ} [Fact (Nat.Prime p)] (hj : 1 ≤ j)
    (hn : 2 ≤ j * p) :
    coeff (Finsupp.single j 1) (specialize p (normalizedLayer p j)) ≠ 0 := by
  set φ := normalizedLayer p j with hφ
  have hspec : specialize p φ =
      bind₁ (specSubst p) (MvPolynomial.map (Int.castRingHom (ZMod p)) φ) := specialize_apply p φ
  have hmapsum : MvPolynomial.map (Int.castRingHom (ZMod p)) φ =
      ∑ d ∈ φ.support, monomial d ((Int.castRingHom (ZMod p)) (coeff d φ)) := by
    conv_lhs => rw [φ.as_sum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [map_monomial]
  rw [hspec, hmapsum, map_sum]
  rw [coeff_sum]
  have hsingle : (Finsupp.single (j * p) 1 : ℕ →₀ ℕ) ∈ φ.support := by
    rw [mem_support_iff]
    have := (firstPrimeLayer (Fact.out (p := Nat.Prime p)) hj hn).2.1
    rw [hφ, coeff_single_normalizedLayer (Fact.out (p := Nat.Prime p)) hj hn]
    intro hzero
    have hdvd : p ^ firstPrimeLayerExponent p j ∣ Nat.factorial (j * p - 1) := by
      rw [← (firstPrimeLayer (Fact.out (p := Nat.Prime p)) hj hn).2.2]
      exact Nat.ordProj_dvd (Nat.factorial (j * p - 1)) p
    have hne0 : Nat.factorial (j * p - 1) / p ^ firstPrimeLayerExponent p j ≠ 0 := by
      intro hcontra
      have := Nat.div_mul_cancel hdvd
      rw [hcontra, zero_mul] at this
      exact Nat.factorial_ne_zero _ this.symm
    exact hne0 (by exact_mod_cast hzero)
  rw [Finset.sum_eq_single (Finsupp.single (j * p) 1)]
  · rw [bind₁_monomial]
    have hsupp : (Finsupp.single (j * p) 1 : ℕ →₀ ℕ).support = {j * p} :=
      Finsupp.support_single_ne_zero _ (by norm_num)
    have hdprod : ∀ i ∈ (Finsupp.single (j * p) 1 : ℕ →₀ ℕ).support,
        specSubst p i ^ (Finsupp.single (j * p) 1 : ℕ →₀ ℕ) i = specSubst p i := by
      intro i hi
      rw [hsupp, Finset.mem_singleton] at hi
      subst hi
      simp
    have hprodeq : (∏ i ∈ (Finsupp.single (j * p) 1 : ℕ →₀ ℕ).support,
        specSubst p i ^ (Finsupp.single (j * p) 1 : ℕ →₀ ℕ) i) = X j := by
      rw [hsupp, Finset.prod_singleton,
        hdprod (j * p) (by rw [hsupp]; exact Finset.mem_singleton_self _)]
      unfold specSubst
      have hjp1 : j * p ≠ 1 := by omega
      have hjpdvd : p ∣ j * p := dvd_mul_left p j
      rw [if_neg hjp1, if_pos hjpdvd]
      congr 1
      exact Nat.mul_div_cancel j (Fact.out (p := Nat.Prime p)).pos
    rw [hprodeq, coeff_C_mul, coeff_X, if_pos rfl, mul_one]
    rw [coeff_single_normalizedLayer (Fact.out (p := Nat.Prime p)) hj hn]
    intro hcontra
    rw [map_natCast] at hcontra
    have hdvd : p ^ firstPrimeLayerExponent p j ∣ Nat.factorial (j * p - 1) := by
      rw [← (firstPrimeLayer (Fact.out (p := Nat.Prime p)) hj hn).2.2]
      exact Nat.ordProj_dvd (Nat.factorial (j * p - 1)) p
    rw [← (firstPrimeLayer (Fact.out (p := Nat.Prime p)) hj hn).2.2] at hcontra
    rw [ZMod.natCast_eq_zero_iff] at hcontra
    exact Nat.not_dvd_ordCompl (Fact.out (p := Nat.Prime p)) (Nat.factorial_ne_zero _) hcontra
  · intro d hdmem hdne
    rw [bind₁_monomial,
      show (∏ i ∈ d.support, specSubst p i ^ d i) = d.prod (fun i k => specSubst p i ^ k)
        from rfl]
    by_cases hall : ∀ a ∈ (Multiset.toFinsupp.symm d), p ∣ a ∨ a = 1
    · have hweightφ : (Finsupp.weight (fun k : ℕ => k) d) = j * p := by
        have hK : coeff d (K j p) ≠ 0 :=
          coeff_ne_zero_of_coeff_divPoly_ne_zero (φ := K j p)
            (c := (p : ℤ) ^ firstPrimeLayerExponent p j) (mem_support_iff.mp hdmem)
        exact isWeightedHomogeneous_K j p hK
      have := eq_single_of_specSubst_finsuppProd_eq_target (p := p) (j := j) (d := d)
      by_cases htarget :
          (d.prod fun i k => specSubst p i ^ k) = monomial (Finsupp.single j 1) (1 : ZMod p)
      · exact absurd (this hweightφ htarget) hdne
      · rw [coeff_C_mul]
        have hne0 : coeff (Finsupp.single j 1) (d.prod fun i k => specSubst p i ^ k) = 0 := by
          rw [specSubst_finsuppProd_eq_monomial d hall] at htarget ⊢
          rw [coeff_monomial, if_neg (fun heq => htarget (by rw [heq]))]
        rw [hne0, mul_zero]
    · push_neg at hall
      obtain ⟨a, ha, hna⟩ := hall
      rw [specSubst_finsuppProd_eq_zero d ⟨a, ha, by tauto⟩, coeff_C_mul, coeff_zero, mul_zero]
  · intro hnmem
    exact absurd hsingle hnmem

#print axioms coeff_target_specialize_normalizedLayer

end CongruenceTheory
