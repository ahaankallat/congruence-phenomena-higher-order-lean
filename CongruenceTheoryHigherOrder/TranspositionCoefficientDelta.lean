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

/-- **The transposition target's value**, pointwise. -/
theorem ciExp_two_apply (N j : ℕ) :
    ciExp N ({2} : Multiset ℕ) j = (if j = 1 then N else 0) + (if j = 2 then 1 else 0) := by
  rw [ciExp_apply]
  congr 1
  simp [Multiset.count_singleton]

/-- **A monomial concentrated at position `1` is determined by its own weight.** -/
theorem eq_single_one_of_weight_eq_of_forall_ne_one_eq_zero {d : ℕ →₀ ℕ} {w : ℕ}
    (hw : Finsupp.weight (fun k : ℕ => k) d = w) (hd : ∀ k, k ≠ 1 → d k = 0) :
    d = Finsupp.single 1 w := by
  have hval : d 1 = w := by
    rw [Finsupp.weight_apply, Finsupp.sum] at hw
    simp only [smul_eq_mul] at hw
    by_cases h1 : (1 : ℕ) ∈ d.support
    · rw [show d.support = {1} from by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        exact ⟨h1, fun k hk => by
          by_contra hne
          exact absurd (hd k hne) (Finsupp.mem_support_iff.mp hk)⟩] at hw
      simpa using hw
    · have hd10 : d 1 = 0 := Finsupp.notMem_support_iff.mp h1
      have hall0 : ∀ k, d k = 0 := fun k => by
        by_cases hk1 : k = 1
        · rw [hk1]; exact hd10
        · exact hd k hk1
      have hw0 : w = 0 := by
        have hz : d = 0 := Finsupp.ext hall0
        rw [hz] at hw; simp at hw; omega
      rw [hd10, hw0]
  apply Finsupp.ext
  intro k
  by_cases hk : k = 1
  · rw [hk, hval, Finsupp.single_eq_same]
  · rw [hd k hk, Finsupp.single_apply, if_neg (Ne.symm hk)]

/-- **`\text{nontrivialPartCount}\,d=0` forces `d` to vanish at every position `\ge2`.** -/
theorem eq_zero_of_two_le_of_nontrivialPartCount_eq_zero {d : ℕ →₀ ℕ}
    (hd : nontrivialPartCount d = 0) : ∀ k, 2 ≤ k → d k = 0 := by
  intro k hk
  rw [nontrivialPartCount_eq_sum, Finsupp.sum] at hd
  by_contra hne
  have hmem : k ∈ d.support := Finsupp.mem_support_iff.mpr hne
  have := Finset.sum_eq_zero_iff.mp hd k hmem
  rw [if_pos hk] at this
  exact hne this

/-- **The transposition-coefficient recursion**: peeling one block off via `Fin.cons`. -/
theorem coeff_transposition_cons {t : ℕ} (a : ℕ) (m : Fin t → ℕ) (hB2 : 2 ≤ ∑ i, m i) :
    coeff (ciExp ((a + ∑ i, m i) - 2) {2}) (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) =
      (a : ℤ) * (∑ i, m i : ℤ) + coeff (ciExp ((∑ i, m i) - 2) {2}) (Delta m) := by
  set B := ∑ i, m i with hBdef
  rw [Delta_cons_eq, ← hBdef, coeff_add]
  have hterm1 : coeff (ciExp ((a + B) - 2) {2}) (C (a + B) - C a * C B) =
      (a : ℤ) * (∑ i, (m i : ℤ)) := by
    rw [coeff_defect_two_eq_mul a B, hBdef]
    push_cast
    ring
  rw [hterm1]
  congr 1
  set x0 : ℕ →₀ ℕ := Finsupp.single 1 a with hx0
  set y0 : ℕ →₀ ℕ := ciExp (B - 2) {2} with hy0
  have hxy0 : x0 + y0 = ciExp (a + B - 2) {2} := by
    apply Finsupp.ext
    intro j
    rw [Finsupp.add_apply, hx0, hy0, Finsupp.single_apply, ciExp_two_apply, ciExp_two_apply]
    split_ifs <;> omega
  rw [← hxy0]
  have hforce : ∀ x y : ℕ →₀ ℕ, x + y = x0 + y0 → coeff x (C a) ≠ 0 →
      coeff y (Delta m) ≠ 0 → x = x0 ∧ y = y0 := by
    intro x y hxy hx hy
    have hwx : Finsupp.weight (fun k : ℕ => k) x = a := isWeightedHomogeneous_C a hx
    have hwy : Finsupp.weight (fun k : ℕ => k) y = B := isWeightedHomogeneous_Delta m hy
    have hnp : nontrivialPartCount x + nontrivialPartCount y = 1 := by
      rw [← nontrivialPartCount_add, hxy, hxy0]
      exact nontrivialPartCount_ciExp (a + B - 2) {2}
        (by intro z hz; simp at hz; omega)
    have hsupp02 : ∀ k, k ≠ 1 → k ≠ 2 → x k = 0 ∧ y k = 0 := by
      intro k hk1 hk2
      have heq : (x + y) k = (x0 + y0) k := by rw [hxy]
      rw [Finsupp.add_apply, hxy0, ciExp_two_apply, if_neg hk1, if_neg hk2, add_zero] at heq
      omega
    rcases (show nontrivialPartCount x = 0 ∧ nontrivialPartCount y = 1 ∨
        nontrivialPartCount x = 1 ∧ nontrivialPartCount y = 0 from by omega) with
      ⟨hx0c, hy1c⟩ | ⟨hx1c, hy0c⟩
    · -- x achieves the trivial (all-fixed-points) piece; y must carry the transposition.
      have hxall : ∀ k, k ≠ 1 → x k = 0 := by
        intro k hk1
        by_cases hk2 : k = 2
        · subst hk2; exact eq_zero_of_two_le_of_nontrivialPartCount_eq_zero hx0c 2 le_rfl
        · exact (hsupp02 k hk1 hk2).1
      have hxeq : x = x0 := by
        rw [hx0]; exact eq_single_one_of_weight_eq_of_forall_ne_one_eq_zero hwx hxall
      have hyeq : y = y0 := by
        have := hxy
        rw [hxeq] at this
        exact add_left_cancel this
      exact ⟨hxeq, hyeq⟩
    · -- x would carry the transposition itself; but then y is the all-fixed-points piece,
      -- forcing y = single 1 B, contradicting Delta m's vanishing there.
      exfalso
      have hyall : ∀ k, k ≠ 1 → y k = 0 := by
        intro k hk1
        by_cases hk2 : k = 2
        · subst hk2; exact eq_zero_of_two_le_of_nontrivialPartCount_eq_zero hy0c 2 le_rfl
        · exact (hsupp02 k hk1 hk2).2
      have hyeq : y = Finsupp.single 1 B :=
        eq_single_one_of_weight_eq_of_forall_ne_one_eq_zero hwy hyall
      rw [hyeq] at hy
      exact hy (coeff_single_one_Delta_eq_zero m)
  rw [coeff_mul_eq_of_forced_unique hforce]
  have hcx0 : coeff x0 (C a) = 1 := by
    rw [hx0, ← K_one]; exact coeff_single_one_K_one a
  rw [hcx0]
  ring

#print axioms isWeightedHomogeneous_Delta
#print axioms coeff_single_one_prod_C
#print axioms coeff_single_one_Delta_eq_zero
#print axioms ciExp_two_apply
#print axioms eq_single_one_of_weight_eq_of_forall_ne_one_eq_zero
#print axioms eq_zero_of_two_le_of_nontrivialPartCount_eq_zero
#print axioms coeff_transposition_cons

end CongruenceTheory
