import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.TriangularIndependenceFinal
import CongruenceTheoryHigherOrder.Noncancellation
import CongruenceTheoryHigherOrder.DefectValuationExactWeight
import CongruenceTheoryHigherOrder.DefectLeadingTermDecomposition
import CongruenceTheoryHigherOrder.DefectSpecializeAeval

/-!
**`thm:common-prime-classification`'s sharpness direction.** If some shape `\lambda_0` achieves
the minimum weight `E`, some coefficient of `\Delta_{p\mathbf u}` is *not* divisible by
`p^{E+1}` — combined with `dvd_coeff_defect_Wp`'s lower bound, this pins down
`v_p(\operatorname{cont}\Delta_{p\mathbf u})=E` exactly.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`A_\lambda(\mathbf u)>0` for every shape `\lambda` actually achieved by some non-refining
partition.** -/
theorem Alam_pos_of_mem_image {r : ℕ} (u : Fin r → ℕ) {lam : Multiset ℕ}
    (hlam : lam ∈ (nonRefiningPartitions u).image GenPartLatShape) : 0 < Alam u lam := by
  obtain ⟨π0, hπ0mem, hπ0eq⟩ := Finset.mem_image.mp hlam
  exact Finset.card_pos.mpr ⟨π0, Finset.mem_filter.mpr ⟨hπ0mem, hπ0eq⟩⟩

/-- **Sharpness**: if some shape `\lambda_0` achieves the minimum weight `E`, some coefficient of
`\Delta_{p\mathbf u}` is not divisible by `p^{E+1}`. -/
theorem exists_coeff_not_dvd_pow_succ {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ) (hu : ∀ i, 0 < u i)
    {p : ℕ} [Fact (Nat.Prime p)] (E : ℕ)
    (hE : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape, E ≤ Wp u p lam)
    (lam0 : Multiset ℕ) (hlam0mem : lam0 ∈ (nonRefiningPartitions u).image GenPartLatShape)
    (hlam0min : Wp u p lam0 = E) :
    ∃ d, ¬ ((p : ℤ) ^ (E + 1) ∣ coeff d (C ((∑ i, u i) * p) - ∏ i, C (u i * p))) := by
  set S := ((nonRefiningPartitions u).image GenPartLatShape).filter (fun lam => Wp u p lam = E)
    with hS
  have hlam0S : lam0 ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨hlam0mem, hlam0min⟩
  set m : ↥S → ℕ →₀ ℕ := fun l => Multiset.toFinsupp l.1 with hm
  have hminj : Function.Injective m := by
    intro l1 l2 hl
    apply Subtype.ext
    exact Multiset.toFinsupp.injective hl
  set c : ↥S → ZMod p := fun l => (((ordCompl[p] (Alam u l.1) : ℕ) : ℤ) : ZMod p) with hc
  have hcne : c ⟨lam0, hlam0S⟩ ≠ 0 := by
    rw [hc]
    simp only [Int.cast_natCast]
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_ordCompl (Fact.out (p := Nat.Prime p))
      (Alam_pos_of_mem_image u hlam0mem).ne'
  have hsum_eq : ∑ l : ↥S, c l • aeval (triangularFamily p) (monomial (m l) (1 : ZMod p)) =
      specialize p (divPoly (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) ((p : ℤ) ^ E)) := by
    rw [specialize_divPoly_defect_eq p hr u hu E hE, ← hS, ← Finset.sum_coe_sort S]
    apply Finset.sum_congr rfl
    intro l _
    rw [hc, hm]
    simp only
    rw [aeval_monomial_toFinsupp, MvPolynomial.smul_eq_C_mul]
  have hne0 : ∑ l : ↥S, c l • aeval (triangularFamily p) (monomial (m l) (1 : ZMod p)) ≠ 0 := by
    intro hcontra
    have hall := eq_zero_of_sum_aeval_monomial_eq_zero (triangular_independence p) m hminj c
      hcontra
    exact hcne (hall ⟨lam0, hlam0S⟩)
  rw [hsum_eq] at hne0
  have hmapne : MvPolynomial.map (Int.castRingHom (ZMod p))
      (divPoly (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) ((p : ℤ) ^ E)) ≠ 0 := by
    intro hcontra
    apply hne0
    rw [specialize_apply, hcontra, map_zero]
  by_contra hall
  push_neg at hall
  apply hmapne
  apply MvPolynomial.ext
  intro d
  rw [coeff_map, coeff_zero]
  simp only [eq_intCast]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, coeff_divPoly]
  obtain ⟨k, hk⟩ := hall d
  have hne : ((p : ℤ) ^ E) ≠ 0 :=
    pow_ne_zero E (by exact_mod_cast (Fact.out (p := Nat.Prime p)).pos.ne')
  rw [hk, pow_succ, show (p : ℤ) ^ E * p * k = (p : ℤ) ^ E * (p * k) from by ring,
    Int.mul_ediv_cancel_left _ hne]
  exact ⟨k, rfl⟩

#print axioms Alam_pos_of_mem_image
#print axioms exists_coeff_not_dvd_pow_succ

end CongruenceTheory
