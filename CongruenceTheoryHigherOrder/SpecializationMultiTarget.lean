import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.KWeightedHomogeneous
import CongruenceTheoryHigherOrder.SpecializationVars
import CongruenceTheoryHigherOrder.SpecializationUnitCoeff

/-!
**Multi-part generalization of `eq_single_of_specSubst_finsuppProd_eq_target`.** The only
exponent vector `d` of weighted degree `\sum_j(jp)m_j` (`\lambda`'s own scaled weight) whose
specialized product is the *multi-variable* target monomial `\prod_jz_j^{m_j}` (`\lambda`'s own
multiplicity Finsupp) is the scaled source monomial `d=\sum_jm_j\cdot X_{jp}` itself — i.e. the
"canonical" monomial for shape `\lambda`. This is the collision-freeness fact needed to identify
an *explicit* witness (rather than a merely existential one) for `thm:common-prime-classification`'s
sharpness direction at a controlled `\lambda`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **The multi-part collision-freeness fact.** -/
theorem eq_scaled_of_specSubst_finsuppProd_eq_target {p : ℕ} [Fact (Nat.Prime p)] {d : ℕ →₀ ℕ}
    {lam : Multiset ℕ}
    (hw : Finsupp.weight (fun k : ℕ => k) d = (lam.map (· * p)).sum)
    (heq : (d.prod fun i k => specSubst p i ^ k) =
      monomial (Multiset.toFinsupp lam) (1 : ZMod p)) :
    d = Multiset.toFinsupp (lam.map (· * p)) := by
  set m := Multiset.toFinsupp.symm d with hm
  by_cases hall : ∀ a ∈ m, p ∣ a ∨ a = 1
  · rw [specSubst_finsuppProd_eq_monomial d hall] at heq
    rw [monomial_eq_monomial_iff] at heq
    have hfeq : Multiset.toFinsupp ((m.filter (· ≠ 1)).map (· / p)) = Multiset.toFinsupp lam := by
      rcases heq with ⟨he, -⟩ | ⟨hz, -⟩
      · exact he
      · exact absurd hz one_ne_zero
    have hmeq : (m.filter (· ≠ 1)).map (· / p) = lam := Multiset.toFinsupp.injective hfeq
    have hfilter_eq : m.filter (· ≠ 1) = lam.map (· * p) := by
      have hstep : (m.filter (· ≠ 1)).map (· / p * p) = m.filter (· ≠ 1) := by
        conv_rhs => rw [← Multiset.map_id (m.filter (· ≠ 1))]
        apply Multiset.map_congr rfl
        intro x hx
        obtain ⟨hxmem, hxne⟩ := Multiset.mem_filter.mp hx
        have hxdvd : p ∣ x := (hall x hxmem).resolve_right hxne
        show x / p * p = id x
        rw [id, Nat.div_mul_cancel hxdvd]
      have hstep2 : (m.filter (· ≠ 1)).map (· / p * p) =
          ((m.filter (· ≠ 1)).map (· / p)).map (· * p) := by
        rw [Multiset.map_map]
        rfl
      rw [← hstep, hstep2, hmeq]
    have hm1 : m.filter (· = 1) = 0 := by
      have hsplit : m = m.filter (· = 1) + m.filter (· ≠ 1) := (Multiset.filter_add_not _ m).symm
      have hweight : Finsupp.weight (fun k : ℕ => k) d = m.sum := by
        have hdeq : d = Multiset.toFinsupp m := by rw [hm]; simp
        rw [hdeq, weight_toFinsupp]
        simp
      have hsum2 : (m.filter (· ≠ 1)).sum = (lam.map (· * p)).sum := by rw [hfilter_eq]
      rw [hweight, hsplit, Multiset.sum_add, hsum2] at hw
      have hm1sum : (m.filter (· = 1)).sum = Multiset.card (m.filter (· = 1)) := by
        have hrepl : m.filter (· = 1) =
            Multiset.replicate (Multiset.card (m.filter (· = 1))) 1 :=
          Multiset.eq_replicate_of_mem (fun x hx => (Multiset.mem_filter.mp hx).2)
        rw [hrepl, Multiset.sum_replicate]
        simp
      rw [hm1sum] at hw
      have : Multiset.card (m.filter (· = 1)) = 0 := by omega
      exact Multiset.card_eq_zero.mp this
    have hmfinal : m = lam.map (· * p) := by
      have hsplit : m = m.filter (· = 1) + m.filter (· ≠ 1) := (Multiset.filter_add_not _ m).symm
      rw [hsplit, hm1, zero_add, hfilter_eq]
    rw [show d = Multiset.toFinsupp m from by rw [hm]; simp, hmfinal]
  · push_neg at hall
    obtain ⟨a, ha, hna⟩ := hall
    exfalso
    have hzero : (d.prod fun i k => specSubst p i ^ k) = 0 :=
      specSubst_finsuppProd_eq_zero d ⟨a, by rw [← hm]; exact ha, by tauto⟩
    rw [hzero] at heq
    exact one_ne_zero (monomial_eq_zero.mp heq.symm)

#print axioms eq_scaled_of_specSubst_finsuppProd_eq_target

end CongruenceTheory
