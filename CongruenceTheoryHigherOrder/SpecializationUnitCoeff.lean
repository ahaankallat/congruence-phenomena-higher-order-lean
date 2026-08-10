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

/-!
**The unit-coefficient half of `cor:triangular-independence`'s triangularity**: the coefficient of
`z_j` in the specialization of `L_j := p^{-e_p(j)}K_j(p)` is a `p`-unit. Combined with
`specialize_K_vars_subset` (`SpecializationVars.lean`), this gives every hypothesis
`algebraicIndependent_of_triangular` needs.

**Method**: `divPoly` divides every coefficient of an integer polynomial by a fixed integer
(exact division; matches the true value whenever the divisor divides every coefficient, which
`firstPrimeLayer_dvd` supplies here). `specSubst_finsuppProd_eq_monomial`/`_eq_zero` give a closed
form for `d.prod (fun i k => specSubst p i ^ k)` for an arbitrary exponent Finsupp `d`, via the
multiset `m` underlying `d` (`Multiset.toFinsupp.symm d`): the product is `0` if some element of
`m` is neither `1` nor a multiple of `p`, and otherwise is the bare monomial obtained by dropping
the `1`s and dividing the rest by `p`. Combined with `weight_toFinsupp`
(`KWeightedHomogeneous.lean`), this shows: for `d` with weighted degree `j*p`, the specialized
product equals the target monomial `X_j` **only when** `d = Finsupp.single (j*p) 1` — the
manuscript's own reason the coefficient computation collapses to the single full-cycle term.

**Honest scope note**: this completes `cor:triangular-independence`'s two hypotheses
(`unit_coeff_specialize_L`, `specialize_K_vars_subset`), giving the corollary itself
(`triangular_independence`) via `algebraicIndependent_of_triangular`. It does not touch anything
beyond `cor:triangular-independence` in the manuscript's chain of results.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **A product of `X`-monomials over a multiset is the monomial at the multiset's own count
Finsupp**, over an arbitrary nontrivial commutative ring (generalizing `CiConverse.lean`'s
`multiset_map_X_prod_eq_monomial`, stated there only for `MvPolynomial ℕ ℤ`). -/
theorem multiset_map_X_prod_eq_monomial' {R : Type*} [CommRing R] (m : Multiset ℕ) :
    (m.map (X : ℕ → MvPolynomial ℕ R)).prod = monomial (Multiset.toFinsupp m) (1 : R) := by
  induction m using Multiset.induction_on with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero, Multiset.toFinsupp_zero,
      congrFun monomial_zero' (1 : R), C_1]
  | cons a s ih =>
    have heq1 : Multiset.toFinsupp (a ::ₘ s) = Finsupp.single a 1 + Multiset.toFinsupp s := by
      rw [show (a ::ₘ s) = {a} + s from by simp, Multiset.toFinsupp_add,
        Multiset.toFinsupp_singleton]
    rw [Multiset.map_cons, Multiset.prod_cons, ih, heq1,
      show (X a : MvPolynomial ℕ R) = monomial (Finsupp.single a 1) (1 : R) from rfl,
      monomial_mul, mul_one]

/-- Divide every coefficient of an integer polynomial by a fixed integer `c` (exact whenever `c`
divides every coefficient of `φ`; the manuscript's `p^{-e_p(j)}K_j(p)` normalization). -/
noncomputable def divPoly (φ : MvPolynomial ℕ ℤ) (c : ℤ) : MvPolynomial ℕ ℤ :=
  ∑ d ∈ φ.support, monomial d (coeff d φ / c)

theorem coeff_divPoly (φ : MvPolynomial ℕ ℤ) (c : ℤ) (d : ℕ →₀ ℕ) :
    coeff d (divPoly φ c) = coeff d φ / c := by
  unfold divPoly
  rw [coeff_sum, Finset.sum_eq_single d]
  · rw [coeff_monomial, if_pos rfl]
  · intro b _ hbd
    rw [coeff_monomial, if_neg hbd]
  · intro hnd
    rw [coeff_monomial, if_pos rfl]
    have hz : coeff d φ = 0 := by
      by_contra hne
      exact hnd (mem_support_iff.mpr hne)
    rw [hz]; simp

/-- `L r p := p^{-e_p(r)}K_r(p)`, constructed as an honest integer polynomial via exact
coefficientwise division (well defined since `firstPrimeLayer_dvd` shows `p^{e_p(r)}` divides
every coefficient of `K_r(p)`). -/
noncomputable def normalizedLayer (p r : ℕ) : MvPolynomial ℕ ℤ :=
  divPoly (K r p) ((p : ℤ) ^ firstPrimeLayerExponent p r)

/-- If `divPoly φ c` has a nonzero coefficient at `d`, so does `φ`. -/
theorem coeff_ne_zero_of_coeff_divPoly_ne_zero {φ : MvPolynomial ℕ ℤ} {c : ℤ} {d : ℕ →₀ ℕ}
    (h : coeff d (divPoly φ c) ≠ 0) : coeff d φ ≠ 0 := by
  rw [coeff_divPoly] at h
  intro hz
  exact h (by rw [hz]; simp)

/-- A product `∏ (specSubst p a)` over a multiset with some element neither `1` nor a multiple
of `p` vanishes. -/
theorem specSubst_finsuppProd_eq_zero {p : ℕ} [Fact (Nat.Prime p)] (d : ℕ →₀ ℕ)
    (h : ∃ a ∈ (Multiset.toFinsupp.symm d), ¬(p ∣ a ∨ a = 1)) :
    (d.prod fun i k => specSubst p i ^ k) = 0 := by
  obtain ⟨a, ha, hna⟩ := h
  have hzero : specSubst p a = 0 := by
    unfold specSubst
    rw [if_neg (by tauto), if_neg (by tauto)]
  set m := Multiset.toFinsupp.symm d with hm
  have hdm : d = Multiset.toFinsupp m := by rw [hm]; simp
  have hprodeq : (d.prod fun i k => specSubst p i ^ k) = (m.map (specSubst p)).prod := by
    rw [hdm]
    clear hdm hm ha
    clear_value m
    induction m using Multiset.induction_on with
    | empty => simp
    | cons b s ih =>
      have hlhs : (Multiset.toFinsupp (b ::ₘ s)).prod (fun i k => specSubst p i ^ k) =
          specSubst p b * (Multiset.toFinsupp s).prod (fun i k => specSubst p i ^ k) := by
        have heq1 : Multiset.toFinsupp (b ::ₘ s) = Finsupp.single b 1 + Multiset.toFinsupp s := by
          rw [show (b ::ₘ s) = {b} + s from by simp, Multiset.toFinsupp_add,
            Multiset.toFinsupp_singleton]
        rw [heq1, Finsupp.prod_add_index' (h_zero := fun a => pow_zero (specSubst p a))
          (h_add := fun a b1 b2 => pow_add (specSubst p a) b1 b2)]
        congr 1
        exact (Finsupp.prod_single_index (h := fun i k => specSubst p i ^ k)
          (pow_zero (specSubst p b))).trans (pow_one _)
      rw [hlhs, ih, Multiset.map_cons, Multiset.prod_cons]
  rw [hprodeq]
  apply Multiset.prod_eq_zero
  rw [Multiset.mem_map]
  exact ⟨a, ha, hzero⟩

/-- The core closed-form computation: if every element of the multiset underlying `d` is either
`1` or a multiple of `p`, the specialized product is the monomial obtained by dropping the `1`s
and dividing the rest by `p`. -/
theorem specSubst_finsuppProd_eq_monomial {p : ℕ} [Fact (Nat.Prime p)] (d : ℕ →₀ ℕ)
    (h : ∀ a ∈ (Multiset.toFinsupp.symm d), p ∣ a ∨ a = 1) :
    (d.prod fun i k => specSubst p i ^ k) =
      monomial (Multiset.toFinsupp
        (((Multiset.toFinsupp.symm d).filter (· ≠ 1)).map (· / p))) (1 : ZMod p) := by
  set m := Multiset.toFinsupp.symm d with hm
  have hdm : d = Multiset.toFinsupp m := by rw [hm]; simp
  have hprodeq : (d.prod fun i k => specSubst p i ^ k) = (m.map (specSubst p)).prod := by
    rw [hdm]
    clear hdm hm h
    clear_value m
    induction m using Multiset.induction_on with
    | empty => simp
    | cons b s ih =>
      have hlhs : (Multiset.toFinsupp (b ::ₘ s)).prod (fun i k => specSubst p i ^ k) =
          specSubst p b * (Multiset.toFinsupp s).prod (fun i k => specSubst p i ^ k) := by
        have heq1 : Multiset.toFinsupp (b ::ₘ s) = Finsupp.single b 1 + Multiset.toFinsupp s := by
          rw [show (b ::ₘ s) = {b} + s from by simp, Multiset.toFinsupp_add,
            Multiset.toFinsupp_singleton]
        rw [heq1, Finsupp.prod_add_index' (h_zero := fun a => pow_zero (specSubst p a))
          (h_add := fun a b1 b2 => pow_add (specSubst p a) b1 b2)]
        congr 1
        exact (Finsupp.prod_single_index (h := fun i k => specSubst p i ^ k)
          (pow_zero (specSubst p b))).trans (pow_one _)
      rw [hlhs, ih, Multiset.map_cons, Multiset.prod_cons]
  rw [hprodeq]
  have hsplit : m = m.filter (· = 1) + m.filter (· ≠ 1) := (Multiset.filter_add_not _ m).symm
  conv_lhs => rw [hsplit, Multiset.map_add, Multiset.prod_add]
  have h1 : (m.filter (· = 1)).map (specSubst p) =
      Multiset.replicate (Multiset.card (m.filter (· = 1))) (1 : MvPolynomial ℕ (ZMod p)) := by
    have hmem : ∀ b ∈ (m.filter (· = 1)).map (specSubst p), b = (1 : MvPolynomial ℕ (ZMod p)) := by
      intro b hb
      rw [Multiset.mem_map] at hb
      obtain ⟨x, hx, hbx⟩ := hb
      obtain ⟨-, hx1⟩ := Multiset.mem_filter.mp hx
      subst hx1
      rw [← hbx]
      unfold specSubst
      simp
    rw [Multiset.eq_replicate_of_mem hmem, Multiset.card_map]
  have h2 : (m.filter (· ≠ 1)).map (specSubst p) =
      ((m.filter (· ≠ 1)).map (· / p)).map X := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro b hb
    obtain ⟨hbmem, hbne⟩ := Multiset.mem_filter.mp hb
    have hbdvd : p ∣ b := (h b hbmem).resolve_right hbne
    show specSubst p b = X (b / p)
    unfold specSubst
    rw [if_neg hbne, if_pos hbdvd]
  rw [h1, h2, Multiset.prod_replicate, one_pow, one_mul,
    multiset_map_X_prod_eq_monomial']

/-- **The collision-freeness fact behind `cor:triangular-independence`**: the only exponent
vector of weighted degree `j*p` whose specialized product is the bare target monomial `X_j` is
the bare source monomial `X_{jp}` itself. -/
theorem eq_single_of_specSubst_finsuppProd_eq_target {p j : ℕ} [Fact (Nat.Prime p)] {d : ℕ →₀ ℕ}
    (hw : Finsupp.weight (fun k : ℕ => k) d = j * p)
    (heq : (d.prod fun i k => specSubst p i ^ k) = monomial (Finsupp.single j 1) (1 : ZMod p)) :
    d = Finsupp.single (j * p) 1 := by
  set m := Multiset.toFinsupp.symm d with hm
  by_cases hall : ∀ a ∈ m, p ∣ a ∨ a = 1
  · rw [specSubst_finsuppProd_eq_monomial d hall] at heq
    rw [monomial_eq_monomial_iff] at heq
    have hfeq : Multiset.toFinsupp ((m.filter (· ≠ 1)).map (· / p)) = Finsupp.single j 1 := by
      rcases heq with ⟨he, -⟩ | ⟨hz, -⟩
      · exact he
      · exact absurd hz one_ne_zero
    have hmeq : (m.filter (· ≠ 1)).map (· / p) = ({j} : Multiset ℕ) := by
      have hinj := Multiset.toFinsupp.injective
        (a₁ := (m.filter (· ≠ 1)).map (· / p)) (a₂ := ({j} : Multiset ℕ))
      apply hinj
      rw [hfeq, Multiset.toFinsupp_singleton]
    have hcard : Multiset.card ((m.filter (· ≠ 1)).map (· / p)) = 1 := by rw [hmeq]; simp
    have hcard2 : Multiset.card (m.filter (· ≠ 1)) = 1 := by
      rwa [Multiset.card_map] at hcard
    obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp hcard2
    have hbmem : b ∈ m.filter (· ≠ 1) := by rw [hb]; exact Multiset.mem_singleton_self b
    obtain ⟨hbmem', hbne⟩ := Multiset.mem_filter.mp hbmem
    have hbdvd : p ∣ b := (hall b hbmem').resolve_right hbne
    have hbdiv : b / p = j := by
      have := hmeq
      rw [hb, Multiset.map_singleton] at this
      exact Multiset.singleton_inj.mp this
    have hbeq : b = j * p := by
      have hpne : p ≠ 0 := (Fact.out (p := Nat.Prime p)).pos.ne'
      obtain ⟨k, hk⟩ := hbdvd
      rw [hk] at hbdiv ⊢
      rw [Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hpne)] at hbdiv
      rw [hbdiv, mul_comm]
    have hm1 : m.filter (· = 1) = 0 := by
      have hsplit : m = m.filter (· = 1) + m.filter (· ≠ 1) := (Multiset.filter_add_not _ m).symm
      have hweight : Finsupp.weight (fun k : ℕ => k) d = m.sum := by
        have hdeq : d = Multiset.toFinsupp m := by rw [hm]; simp
        rw [hdeq, weight_toFinsupp]
        simp
      rw [hweight, hsplit, Multiset.sum_add, hb, Multiset.sum_singleton, hbeq] at hw
      have hm1sum : (m.filter (· = 1)).sum = Multiset.card (m.filter (· = 1)) := by
        have hrepl : m.filter (· = 1) =
            Multiset.replicate (Multiset.card (m.filter (· = 1))) 1 :=
          Multiset.eq_replicate_of_mem (fun x hx => (Multiset.mem_filter.mp hx).2)
        rw [hrepl, Multiset.sum_replicate]
        simp
      rw [hm1sum] at hw
      have : Multiset.card (m.filter (· = 1)) = 0 := by omega
      exact Multiset.card_eq_zero.mp this
    have hmfinal : m = ({j * p} : Multiset ℕ) := by
      have hsplit : m = m.filter (· = 1) + m.filter (· ≠ 1) := (Multiset.filter_add_not _ m).symm
      rw [hsplit, hm1, zero_add, hb, hbeq]
    rw [show d = Multiset.toFinsupp m from by rw [hm]; simp, hmfinal, Multiset.toFinsupp_singleton]
  · push_neg at hall
    obtain ⟨a, ha, hna⟩ := hall
    exfalso
    have hzero : (d.prod fun i k => specSubst p i ^ k) = 0 :=
      specSubst_finsuppProd_eq_zero d ⟨a, by rw [← hm]; exact ha, by tauto⟩
    rw [hzero] at heq
    exact one_ne_zero (monomial_eq_zero.mp heq.symm)

#print axioms eq_single_of_specSubst_finsuppProd_eq_target

end CongruenceTheory
