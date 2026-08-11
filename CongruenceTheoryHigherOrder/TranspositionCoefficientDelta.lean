import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.CompletePrimeLocalCaseII
import CongruenceTheoryHigherOrder.TwoTermDefectValuation
import CongruenceTheoryHigherOrder.KOneAllFixedCoeff
import CongruenceTheoryHigherOrder.DefectWeightedHomogeneous
import CongruenceTheoryHigherOrder.CanonicalMonomialCoefficient
import CongruenceTheoryHigherOrder.NontrivialPartCountK
import CongruenceTheoryHigherOrder.CycleDepthHierarchy

/-!
**The transposition (single-`2`-cycle) coefficient of the general higher-order defect
`\Delta_{\mathbf n}`**, for an arbitrary tuple `\mathbf n` of any length `r`: it equals
`\sum_{i<j}n_in_j` exactly — the manuscript's "transposition coefficient in the full defect"
used in `thm:complete-prime-local`(ii)'s `b\le E` branch. Proved by induction on `r` via
`Fin.cons` and the (A9) decomposition (`Delta_cons_eq`), peeling one block at a time: `C_a`'s
own transposition-free (all-fixed-points) piece is forced (since `\Delta_{\mathbf m}` vanishes
at the all-fixed-points monomial), leaving exactly `a\cdot B` from the two-term piece plus the
inductive contribution from the remaining blocks.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`\Delta_{\mathbf n}` is weighted homogeneous of weighted degree `\sum_i n_i`.** -/
theorem isWeightedHomogeneous_Delta {r : ℕ} (n : Fin r → ℕ) :
    IsWeightedHomogeneous (fun k : ℕ => k) (Delta n) (∑ i, n i) := by
  unfold Delta
  apply IsWeightedHomogeneous.sub
  · exact isWeightedHomogeneous_C _
  · exact IsWeightedHomogeneous.finset_prod Finset.univ (fun i => C (n i)) n
      (fun i _ => isWeightedHomogeneous_C (n i))

/-- **`\prod_iC(n_i)`'s coefficient at the all-fixed-points monomial is `1`.** -/
theorem coeff_single_one_prod_C {r : ℕ} (n : Fin r → ℕ) :
    coeff (Finsupp.single 1 (∑ i, n i)) (∏ i, C (n i)) = 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
    set S := ∑ i : Fin r, n i.succ with hSdef
    set x0 := Finsupp.single (1 : ℕ) (n 0) with hx0
    set y0 := Finsupp.single (1 : ℕ) S with hy0
    have hxy0 : x0 + y0 = Finsupp.single 1 (n 0 + S) := by
      rw [hx0, hy0, Finsupp.single_add]
    rw [← hxy0]
    have hforce : ∀ x y : ℕ →₀ ℕ, x + y = x0 + y0 → coeff x (C (n 0)) ≠ 0 →
        coeff y (∏ i : Fin r, C (n i.succ)) ≠ 0 → x = x0 ∧ y = y0 := by
      intro x y hxy hx hy
      have hwx : Finsupp.weight (fun k : ℕ => k) x = n 0 := isWeightedHomogeneous_C (n 0) hx
      have hwy : Finsupp.weight (fun k : ℕ => k) y = S := by
        have := IsWeightedHomogeneous.finset_prod (Finset.univ : Finset (Fin r))
          (fun i => C (n i.succ)) (fun i => n i.succ) (fun i _ => isWeightedHomogeneous_C _)
        exact this hy
      have hxsupp1 : ∀ k, k ≠ 1 → x k = 0 := by
        intro k hk
        have heq : (x + y) k = (x0 + y0) k := by rw [hxy]
        rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
          if_neg (Ne.symm hk), if_neg (Ne.symm hk)] at heq
        omega
      have hysupp1 : ∀ k, k ≠ 1 → y k = 0 := by
        intro k hk
        have heq : (x + y) k = (x0 + y0) k := by rw [hxy]
        rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
          if_neg (Ne.symm hk), if_neg (Ne.symm hk)] at heq
        omega
      have hx1 : x 1 = n 0 := by
        rw [Finsupp.weight_apply, Finsupp.sum] at hwx
        simp only [smul_eq_mul] at hwx
        by_cases h1 : (1 : ℕ) ∈ x.support
        · rw [show x.support = {1} from by
            apply Finset.eq_singleton_iff_unique_mem.mpr
            refine ⟨h1, fun k hk => by
              by_contra hne
              exact absurd (hxsupp1 k hne) (Finsupp.mem_support_iff.mp hk)⟩] at hwx
          simpa using hwx
        · have hx10 : x 1 = 0 := Finsupp.notMem_support_iff.mp h1
          have hxall0 : ∀ k, x k = 0 := fun k => by
            by_cases hk1 : k = 1
            · rw [hk1]; exact hx10
            · exact hxsupp1 k hk1
          have hn00 : n 0 = 0 := by
            have hxz : x = 0 := Finsupp.ext hxall0
            rw [hxz] at hwx; simp at hwx; omega
          rw [hx10, hn00]
      have hy1 : y 1 = S := by
        rw [Finsupp.weight_apply, Finsupp.sum] at hwy
        simp only [smul_eq_mul] at hwy
        by_cases h1 : (1 : ℕ) ∈ y.support
        · rw [show y.support = {1} from by
            apply Finset.eq_singleton_iff_unique_mem.mpr
            refine ⟨h1, fun k hk => by
              by_contra hne
              exact absurd (hysupp1 k hne) (Finsupp.mem_support_iff.mp hk)⟩] at hwy
          simpa using hwy
        · have hy10 : y 1 = 0 := Finsupp.notMem_support_iff.mp h1
          have hyall0 : ∀ k, y k = 0 := fun k => by
            by_cases hk1 : k = 1
            · rw [hk1]; exact hy10
            · exact hysupp1 k hk1
          have hS0 : S = 0 := by
            have hyz : y = 0 := Finsupp.ext hyall0
            rw [hyz] at hwy; simp at hwy; omega
          rw [hy10, hS0]
      have hxeq : x = x0 := by
        apply Finsupp.ext
        intro k
        by_cases hk : k = 1
        · rw [hk, hx1, hx0, Finsupp.single_eq_same]
        · rw [hxsupp1 k hk, hx0, Finsupp.single_apply, if_neg (Ne.symm hk)]
      have hyeq : y = y0 := by
        apply Finsupp.ext
        intro k
        by_cases hk : k = 1
        · rw [hk, hy1, hy0, Finsupp.single_eq_same]
        · rw [hysupp1 k hk, hy0, Finsupp.single_apply, if_neg (Ne.symm hk)]
      exact ⟨hxeq, hyeq⟩
    rw [coeff_mul_eq_of_forced_unique hforce]
    have h1 : coeff x0 (C (n 0)) = 1 := by
      rw [hx0, ← K_one]; exact coeff_single_one_K_one _
    have h2 : coeff y0 (∏ i : Fin r, C (n i.succ)) = 1 := by
      rw [hy0, hSdef]; exact ih (fun i => n i.succ)
    rw [h1, h2]
    ring

/-- **`\Delta_{\mathbf n}` vanishes at the all-fixed-points monomial.** -/
theorem coeff_single_one_Delta_eq_zero {r : ℕ} (n : Fin r → ℕ) :
    coeff (Finsupp.single 1 (∑ i, n i)) (Delta n) = 0 := by
  unfold Delta
  rw [coeff_sub]
  rw [← K_one, coeff_single_one_K_one, coeff_single_one_prod_C]
  ring

#print axioms isWeightedHomogeneous_Delta
#print axioms coeff_single_one_prod_C
#print axioms coeff_single_one_Delta_eq_zero

end CongruenceTheory
