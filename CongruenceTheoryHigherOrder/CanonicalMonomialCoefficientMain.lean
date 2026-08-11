import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.KWeightedHomogeneous
import CongruenceTheoryHigherOrder.A3Final
import CongruenceTheoryHigherOrder.NontrivialPartCountK
import CongruenceTheoryHigherOrder.NontrivialPartCountProduct
import CongruenceTheoryHigherOrder.CanonicalMonomialCoefficient

/-!
**The exact coefficient of a shape's canonical mixed monomial, assembled.** Combines
`CanonicalMonomialCoefficient.lean`'s ingredients into the full multiset induction: among
monomials `x` with `coeff x (K_j(p)) \ne 0` achieving the minimal `nontrivialPartCount`
(`0` for `j=1`, `1` for `j\ge2`), the canonical monomial `\text{canonTarget}(p,j)` achieves the
*least* possible exponent at position `1` -- uniquely. Chaining this fact through the shape
multiset (via `coeff_mul_eq_of_forced_unique`) shows the canonical mixed monomial is the *only*
way any nontrivial-part-count-minimal monomial of the full block-product can arise, giving the
exact coefficient `\prod_{j\ge2}(jp-1)!`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **A nonzero-coefficient monomial of `K_j(p)` (`j\ge2`) with `d(1)=0` and
`nontrivialPartCount d=1` is exactly `X_{jp}`.** -/
theorem eq_single_of_coeff_K_apply_one_eq_zero {p j : ℕ} (hj : 2 ≤ j) {d : ℕ →₀ ℕ}
    (hd : coeff d (K j p) ≠ 0) (hd1 : d 1 = 0) (hnp : nontrivialPartCount d = 1) :
    d = Finsupp.single (j * p) 1 := by
  have hw : Finsupp.weight (fun k : ℕ => k) d = j * p := isWeightedHomogeneous_K j p hd
  rw [Finsupp.weight_apply, Finsupp.sum] at hw
  simp only [smul_eq_mul] at hw
  rw [nontrivialPartCount_eq_sum] at hnp
  have hd0 : d 0 = 0 := apply_zero_eq_zero_of_coeff_K_ne_zero hd
  have hexists : ∃ k₀ ∈ d.support, 2 ≤ k₀ ∧ d k₀ = 1 ∧
      ∀ k ∈ d.support, 2 ≤ k → k ≠ k₀ → d k = 0 := by
    have hcard : (d.support.filter (2 ≤ ·)).card = 1 ∨
        (∃ k₀ ∈ d.support.filter (2 ≤ ·), d k₀ ≥ 2) := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨hne1, hall2⟩ := hcon
      have hallone : ∀ k ∈ d.support.filter (2 ≤ ·), d k = 1 := by
        intro k hk
        have hk1 := hall2 k hk
        rw [Finset.mem_filter] at hk
        have hkpos : d k ≠ 0 := Finsupp.mem_support_iff.mp hk.1
        omega
      have hsumeq : d.sum (fun k v => if 2 ≤ k then v else 0) =
          (d.support.filter (2 ≤ ·)).card := by
        rw [Finsupp.sum]
        rw [show ∑ a ∈ d.support, (if 2 ≤ a then d a else 0) =
            ∑ a ∈ d.support.filter (2 ≤ ·), d a from by
          rw [Finset.sum_filter]]
        rw [Finset.sum_congr rfl (fun k hk => hallone k hk)]
        simp
      rw [hsumeq] at hnp
      have hcardpos : 0 < (d.support.filter (2 ≤ ·)).card := by omega
      have hcardne : (d.support.filter (2 ≤ ·)).card ≠ 1 := hne1
      omega
    rcases hcard with hcard1 | ⟨k₀, hk₀mem, hk₀ge2⟩
    · obtain ⟨k₀, hk₀⟩ := Finset.card_eq_one.mp hcard1
      have hk₀mem : k₀ ∈ d.support.filter (2 ≤ ·) := by rw [hk₀]; exact Finset.mem_singleton_self _
      rw [Finset.mem_filter] at hk₀mem
      refine ⟨k₀, hk₀mem.1, hk₀mem.2, ?_, ?_⟩
      · have : d.sum (fun k v => if 2 ≤ k then v else 0) = d k₀ := by
          rw [Finsupp.sum]
          rw [show ∑ a ∈ d.support, (if 2 ≤ a then d a else 0) =
              ∑ a ∈ d.support.filter (2 ≤ ·), d a from by rw [Finset.sum_filter]]
          rw [hk₀]
          simp
        omega
      · intro k hkmem hk2 hkne
        by_contra hne
        have : k ∈ d.support.filter (2 ≤ ·) := Finset.mem_filter.mpr ⟨hkmem, hk2⟩
        rw [hk₀, Finset.mem_singleton] at this
        exact hkne this
    · exfalso
      rw [Finset.mem_filter] at hk₀mem
      have hsingle : (if 2 ≤ k₀ then d k₀ else 0) ≤
          ∑ a ∈ d.support, (if 2 ≤ a then d a else 0) :=
        Finset.single_le_sum (f := fun a => if 2 ≤ a then d a else 0)
          (fun a _ => by split_ifs <;> simp) hk₀mem.1
      have hnp2 : ∑ a ∈ d.support, (if 2 ≤ a then d a else 0) = 1 := by
        have h := hnp
        rwa [Finsupp.sum] at h
      rw [if_pos hk₀mem.2, hnp2] at hsingle
      omega
  obtain ⟨k₀, hk₀mem, hk₀ge2, hk₀val, hk₀uniq⟩ := hexists
  have hsupp : d.support = {k₀} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hk₀mem, ?_⟩
    intro x hxmem
    by_contra hxne
    have hx0 : x ≠ 0 := by
      intro hx0; subst hx0
      exact (Finsupp.mem_support_iff.mp hxmem) hd0
    have hx1 : x ≠ 1 := by
      intro hx1; subst hx1
      exact (Finsupp.mem_support_iff.mp hxmem) hd1
    have hx2 : 2 ≤ x := by omega
    have := hk₀uniq x hxmem hx2 hxne
    exact (Finsupp.mem_support_iff.mp hxmem) this
  have hweq : d k₀ * k₀ = j * p := by
    rw [← hw]
    rw [Finset.sum_congr hsupp (fun _ _ => rfl)]
    simp
  rw [hk₀val, one_mul] at hweq
  ext k
  by_cases hk : k = j * p
  · subst hk
    rw [Finsupp.single_eq_same, ← hweq, hk₀val]
  · rw [Finsupp.single_eq_of_ne hk]
    by_contra hne
    have hkmem : k ∈ d.support := Finsupp.mem_support_iff.mpr hne
    rw [hsupp, Finset.mem_singleton] at hkmem
    apply hk
    rw [hkmem, ← hweq]

#print axioms eq_single_of_coeff_K_apply_one_eq_zero

end CongruenceTheory
