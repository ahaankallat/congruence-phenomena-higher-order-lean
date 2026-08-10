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

/-!
**`cor:triangular-independence`, fully assembled.** The last piece needed to invoke
`algebraicIndependent_of_triangular` is that `L_j := specialize p (normalizedLayer p j)`, after
subtracting off its own `z_j`-coefficient term, involves no occurrence of `z_j` itself (not merely
`z_m` for `m>j`, which `specialize_K_vars_subset` already gives). This needs pinning down an
exponent Finsupp of weighted degree `j*p` from a single nonzero coordinate at `j*p`: combined with
`isWeightedHomogeneous_K_zero` (ruling out any contribution from the unrelated index `0`), the only
such Finsupp is the bare `Finsupp.single (j*p) 1` itself — so `z_j` can only ever arise from the one
monomial already being subtracted off.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **An exponent Finsupp of weighted degree `n` with a nonzero coordinate at `n` itself (and a
zero coordinate at `0`) is the bare `single n 1`.** -/
theorem eq_single_of_weight_eq_self {n : ℕ} (hn : 0 < n) {d : ℕ →₀ ℕ}
    (hw : Finsupp.weight (fun k : ℕ => k) d = n) (h0 : d 0 = 0) (hpos : 1 ≤ d n) :
    d = Finsupp.single n 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum] at hw
  simp only [smul_eq_mul] at hw
  have hnmem : n ∈ d.support := Finsupp.mem_support_iff.mpr (by omega)
  have hle : d n * n ≤ ∑ i ∈ d.support, d i * i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (d i * i)) hnmem
  have hdn_le1 : d n ≤ 1 := by
    rw [hw] at hle
    nlinarith
  have hdn_eq1 : d n = 1 := le_antisymm hdn_le1 hpos
  have hsum_eq : ∑ i ∈ d.support, d i * i = d n * n := by rw [hw, hdn_eq1, one_mul]
  rw [← Finset.insert_erase hnmem, Finset.sum_insert (Finset.notMem_erase _ _)] at hsum_eq
  have hrest : ∑ i ∈ d.support.erase n, d i * i = 0 := by omega
  have hrest0 : ∀ i ∈ d.support.erase n, d i * i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)).mp hrest
  ext i
  by_cases hi : i = n
  · subst hi; simp [hdn_eq1]
  · by_contra hine
    rw [Finsupp.single_apply, if_neg (Ne.symm hi)] at hine
    have hipos : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr hine
    by_cases hi0 : i = 0
    · rw [hi0] at hipos; omega
    · have himem : i ∈ d.support.erase n :=
        Finset.mem_erase.mpr ⟨hi, Finsupp.mem_support_iff.mpr hine⟩
      have hzero := hrest0 i himem
      rcases Nat.mul_eq_zero.mp hzero with h | h
      · exact hine h
      · exact hi0 h

/-- **For `d` in `K_j(p)`'s support other than the full-cycle monomial, `z_j` does not occur in
the specialized image `d.prod (specSubst p ·)^·`.** -/
theorem j_notMem_vars_specSubst_finsuppProd {p j : ℕ} [Fact (Nat.Prime p)] (hj : 1 ≤ j)
    {d : ℕ →₀ ℕ} (hK : coeff d (K j p) ≠ 0) (hne : d ≠ Finsupp.single (j * p) 1) :
    j ∉ (d.prod fun i k => specSubst p i ^ k).vars := by
  have hjppos : 0 < j * p := Nat.mul_pos (by omega) (Fact.out (p := Nat.Prime p)).pos
  have hw : Finsupp.weight (fun k : ℕ => k) d = j * p := isWeightedHomogeneous_K j p hK
  have h0 : d 0 = 0 := by
    have hw0 := isWeightedHomogeneous_K_zero j p hK
    have heqw : (fun k : ℕ => if k = 0 then (1 : ℕ) else 0) = Pi.single 0 1 := by
      funext k; rw [Pi.single_apply]
    rw [heqw, Finsupp.weight_single_one_apply] at hw0
    exact hw0
  by_cases hall : ∀ a ∈ (Multiset.toFinsupp.symm d), p ∣ a ∨ a = 1
  · rw [specSubst_finsuppProd_eq_monomial d hall]
    intro hmem
    rw [vars_monomial one_ne_zero] at hmem
    have hdjp : d (j * p) = 0 := by
      by_contra hcontra
      have hpos : 1 ≤ d (j * p) := Nat.one_le_iff_ne_zero.mpr hcontra
      exact hne (eq_single_of_weight_eq_self hjppos hw h0 hpos)
    rw [Finsupp.mem_support_iff] at hmem
    apply hmem
    rw [Multiset.toFinsupp_apply]
    rw [Multiset.count_eq_zero]
    intro hcontra
    rw [Multiset.mem_map] at hcontra
    obtain ⟨a, ha, hadiv⟩ := hcontra
    obtain ⟨hamem, hane⟩ := Multiset.mem_filter.mp ha
    have hadvd : p ∣ a := (hall a hamem).resolve_right hane
    have haeq : a = j * p := by
      obtain ⟨k, hk⟩ := hadvd
      rw [hk] at hadiv ⊢
      rw [Nat.mul_div_cancel_left k (Fact.out (p := Nat.Prime p)).pos] at hadiv
      rw [← hadiv]; ring
    have hcount : (Multiset.toFinsupp.symm d).count (j * p) = 0 := by
      have := hdjp
      conv_lhs at this => rw [← Multiset.toFinsupp.apply_symm_apply d]
      rwa [Multiset.toFinsupp_apply] at this
    rw [← haeq] at hcount
    exact Multiset.count_eq_zero.mp hcount hamem
  · rw [specSubst_finsuppProd_eq_zero d (by
      push_neg at hall
      obtain ⟨a, ha, hna⟩ := hall
      exact ⟨a, ha, by tauto⟩)]
    simp

#print axioms j_notMem_vars_specSubst_finsuppProd

end CongruenceTheory
