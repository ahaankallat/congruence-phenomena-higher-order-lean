import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CoeffExtraction
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.KNontrivialPart
import CongruenceTheoryHigherOrder.CycleDepthHierarchy
import CongruenceTheoryHigherOrder.A3Final

/-!
**Every nonzero-coefficient monomial of `K_j(p)^m` (`j\ge2`) has at least `m` nontrivial
parts**, and consequently every nonzero-coefficient monomial of a product
`\prod_{j}K_j(p)^{m_j}` has at least `\sum_jm_j` nontrivial parts. This is the lower-bound half
of the witness-depth (`\delta_p`) argument: no coefficient of `\Delta_{p\mathbf u}` with fewer
than `k(\lambda)` nontrivial parts can receive any contribution from the shape-`\lambda` term of
(A7).
-/

namespace CongruenceTheory

open scoped Classical
open MvPolynomial

/-- `nontrivialPartCount` agrees with the `Finsupp.sum` form, letting `Finsupp.sum_add_index'`
handle additivity under `+`. -/
theorem nontrivialPartCount_eq_sum (d : ℕ →₀ ℕ) :
    nontrivialPartCount d = d.sum (fun k v => if 2 ≤ k then v else 0) := by
  unfold nontrivialPartCount Finsupp.sum
  rw [Finset.sum_filter]

/-- **Additivity of `nontrivialPartCount` under `Finsupp` addition.** -/
theorem nontrivialPartCount_add (d₁ d₂ : ℕ →₀ ℕ) :
    nontrivialPartCount (d₁ + d₂) = nontrivialPartCount d₁ + nontrivialPartCount d₂ := by
  rw [nontrivialPartCount_eq_sum, nontrivialPartCount_eq_sum, nontrivialPartCount_eq_sum]
  exact Finsupp.sum_add_index' (fun a => by simp) (fun a b1 b2 => by by_cases h : 2 ≤ a <;> simp [h])

/-- **`nontrivialPartCount (\text{ciExp } a\ m) = \#m$`** when every part of `m` is `\ge2`. -/
theorem nontrivialPartCount_ciExp (a : ℕ) (m : Multiset ℕ) (hm : ∀ x ∈ m, 2 ≤ x) :
    nontrivialPartCount (ciExp a m) = Multiset.card m := by
  induction m using Multiset.induction with
  | empty =>
    simp only [ciExp, Multiset.map_zero, Multiset.sum_zero, add_zero, Multiset.card_zero]
    rw [nontrivialPartCount_eq_sum, Finsupp.sum_single_index (by simp)]
    norm_num
  | cons x s ih =>
    have hxs : ∀ y ∈ s, 2 ≤ y := fun y hy => hm y (Multiset.mem_cons_of_mem hy)
    have hx2 : 2 ≤ x := hm x (Multiset.mem_cons_self x s)
    have hcieq : ciExp a (x ::ₘ s) = ciExp a s + Finsupp.single x 1 := by
      unfold ciExp
      rw [Multiset.map_cons, Multiset.sum_cons]
      abel
    rw [hcieq, nontrivialPartCount_add, ih hxs, Multiset.card_cons]
    have hsingle : nontrivialPartCount (Finsupp.single x 1) = 1 := by
      rw [nontrivialPartCount_eq_sum, Finsupp.sum_single_index (by simp), if_pos hx2]
    omega

/-- **Every nonzero-coefficient monomial of `K_r(q)` (`r\ge2`) has `\ge1` nontrivial part.** -/
theorem nontrivialPartCount_pos_of_coeff_K_ne_zero {r q : ℕ} (hr : 2 ≤ r) {d : ℕ →₀ ℕ}
    (hd : MvPolynomial.coeff d (K r q) ≠ 0) : 1 ≤ nontrivialPartCount d := by
  rw [K_eq_Gfun_top] at hd
  unfold Gfun at hd
  rw [MvPolynomial.coeff_sum] at hd
  have hne : ∃ g ∈ (Finset.univ : Finset (Equiv.Perm (Fin r × Fin q))).filter
      (fun g => piOf g = ⊤), MvPolynomial.coeff d (ci g) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hd (Finset.sum_eq_zero hall)
  obtain ⟨g, hgmem, hgcoeff⟩ := hne
  have hgtop : piOf g = ⊤ := (Finset.mem_filter.mp hgmem).2
  have hgcyc : g.cycleType ≠ 0 := cycleType_ne_zero_of_piOf_eq_top hr hgtop
  have hciexp : ciExp (Fintype.card (Fin r × Fin q) - g.cycleType.sum) g.cycleType =
      Finsupp.single 1 (Fintype.card (Fin r × Fin q) - g.cycleType.sum) +
        g.cycleType.toFinsupp := by
    unfold ciExp
    congr 1
    induction g.cycleType using Multiset.induction with
    | empty => simp
    | cons x s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih]
      rw [show (x ::ₘ s) = {x} + s from by simp, Multiset.toFinsupp_add,
        Multiset.toFinsupp_singleton]
  have hdmono : ci g = MvPolynomial.monomial (ciExp (Fintype.card (Fin r × Fin q) - g.cycleType.sum)
      g.cycleType) (1 : ℤ) := by
    rw [hciexp, ci_eq_monomial_toFinsupp]
  rw [hdmono, MvPolynomial.coeff_monomial] at hgcoeff
  split_ifs at hgcoeff with heq
  · rw [← heq]
    have hcard : Fintype.card (Fin r × Fin q) - g.cycleType.sum =
        Fintype.card (Fin r × Fin q) - g.cycleType.sum := rfl
    rw [nontrivialPartCount_ciExp _ g.cycleType (fun x hx => Equiv.Perm.two_le_of_mem_cycleType hx)]
    exact Nat.one_le_iff_ne_zero.mpr (fun h => hgcyc (Multiset.card_eq_zero.mp h))
  · exact absurd rfl hgcoeff

#print axioms nontrivialPartCount_eq_sum
#print axioms nontrivialPartCount_add
#print axioms nontrivialPartCount_ciExp
#print axioms nontrivialPartCount_pos_of_coeff_K_ne_zero

end CongruenceTheory
