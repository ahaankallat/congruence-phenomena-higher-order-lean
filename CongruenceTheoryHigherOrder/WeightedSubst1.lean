import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.FmDef
import CongruenceTheoryHigherOrder.FmModP
import CongruenceTheoryHigherOrder.PolyOrder
import CongruenceTheoryHigherOrder.CycleDepthHierarchy

/-!
**The general `X_1\mapsto1` substitution correspondence for weighted-homogeneous polynomials.**
Generalizes `FmModP.lean`'s `coeff_single_Fm` (specific to `\varphi=C_m`, target monomial
`\text{single }m\,1`) to an arbitrary weighted-homogeneous `\varphi` (weight `=\text{id}`) and
arbitrary target monomial `e` supported away from index `1`. This is the algebraic core of
"removing the common factor `C_p^{\sum q_i}` and using weighted homogeneity to put `X_1=1`"
(`thm:complete-prime-local`(iii)'s proof): it identifies `\varphi`'s monomials with the
substituted polynomial's monomials, matching `\text{nontrivialPartCount}` (the manuscript's
partition-depth count) to `monoDeg` (`D_{\mathbf c}`'s own `J`-adic order notion) exactly.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **The `X_1\mapsto1` substitution**, matching `Fm`'s own construction generally. -/
noncomputable def subst1 (φ : MvPolynomial ℕ ℤ) : MvPolynomial ℕ ℤ :=
  MvPolynomial.bind₁ (fun i => if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) φ

theorem subst1_C (m : ℕ) : subst1 (C m) = Fm m := rfl

/-- **The coefficient correspondence**: for `\varphi` weighted-homogeneous of degree `N` and `e`
supported away from index `1`, `\text{coeff}_e(\text{subst1}\,\varphi)` is the coefficient of
`\varphi` at the unique degree-`N` monomial extending `e` (`e` with `X_1`-exponent
`N-\text{weight}(e)`), or `0` if `\text{weight}(e)>N`. -/
theorem coeff_subst1_of_weighted_homogeneous {φ : MvPolynomial ℕ ℤ} {N : ℕ}
    (hφ : IsWeightedHomogeneous (fun k : ℕ => k) φ N) (e : ℕ →₀ ℕ) (he1 : e 1 = 0) :
    MvPolynomial.coeff e (subst1 φ) =
      if Finsupp.weight (fun k : ℕ => k) e ≤ N then
        MvPolynomial.coeff (e + Finsupp.single 1 (N - Finsupp.weight (fun k : ℕ => k) e)) φ
      else 0 := by
  unfold subst1
  rw [MvPolynomial.bind₁, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, MvPolynomial.coeff_sum]
  have hterm : ∀ d ∈ φ.support,
      MvPolynomial.coeff e
        (algebraMap ℤ (MvPolynomial ℕ ℤ) (MvPolynomial.coeff d φ) *
          ∏ i ∈ d.support, (if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) ^ d i) =
        if d.erase 1 = e then MvPolynomial.coeff d φ else 0 := by
    intro d hdmem
    have halg : algebraMap ℤ (MvPolynomial ℕ ℤ) (MvPolynomial.coeff d φ) =
        MvPolynomial.C (MvPolynomial.coeff d φ) := rfl
    rw [halg, MvPolynomial.coeff_C_mul]
    have hprodeq : (∏ i ∈ d.support,
        (if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) ^ d i) =
        d.prod fun i e => (if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) ^ e := rfl
    rw [hprodeq, prod_subst_eq_monomial_erase, MvPolynomial.coeff_monomial]
    by_cases hde : d.erase 1 = e
    · rw [if_pos hde, if_pos hde, mul_one]
    · rw [if_neg hde, if_neg hde, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  have hrecon : ∀ d ∈ φ.support, d.erase 1 = e →
      d = e + Finsupp.single 1 (N - Finsupp.weight (fun k : ℕ => k) e) := by
    intro d hdmem hde
    have hw : Finsupp.weight (fun k : ℕ => k) d = N := hφ (MvPolynomial.mem_support_iff.mp hdmem)
    have hrecond : d = d.erase 1 + Finsupp.single 1 (d 1) := by
      ext j
      rw [Finsupp.add_apply, Finsupp.erase_apply, Finsupp.single_apply]
      rcases eq_or_ne j 1 with rfl | hj
      · simp
      · simp [hj, Ne.symm hj]
    have hweq : Finsupp.weight (fun k : ℕ => k) d =
        Finsupp.weight (fun k : ℕ => k) (d.erase 1) +
          Finsupp.weight (fun k : ℕ => k) (Finsupp.single 1 (d 1)) := by
      conv_lhs => rw [hrecond]
      exact map_add _ _ _
    rw [hde, Finsupp.weight_single, smul_eq_mul, mul_one] at hweq
    rw [hw] at hweq
    have hd1 : d 1 = N - Finsupp.weight (fun k : ℕ => k) e := by omega
    rw [hrecond, hde, hd1]
  by_cases hle : Finsupp.weight (fun k : ℕ => k) e ≤ N
  · rw [if_pos hle]
    set d₀ := e + Finsupp.single 1 (N - Finsupp.weight (fun k : ℕ => k) e) with hd₀def
    by_cases hd₀mem : d₀ ∈ φ.support
    · rw [Finset.sum_eq_single d₀]
      · rw [if_pos]
        have : d₀.erase 1 = e := by
          ext j
          rw [Finsupp.erase_apply, hd₀def, Finsupp.add_apply, Finsupp.single_apply]
          rcases eq_or_ne j 1 with rfl | hj
          · rw [if_pos rfl, he1]
          · rw [if_neg hj, if_neg (Ne.symm hj), add_zero]
        exact this
      · intro d hdmem hdne
        rw [if_neg]
        intro hde
        exact hdne (hrecon d hdmem hde)
      · intro hnotmem
        exact absurd hd₀mem hnotmem
    · have hd₀coeff0 : MvPolynomial.coeff d₀ φ = 0 := by
        by_contra h
        exact hd₀mem (MvPolynomial.mem_support_iff.mpr h)
      rw [hd₀coeff0]
      apply Finset.sum_eq_zero
      intro d hdmem
      rw [if_neg]
      intro hde
      exact hd₀mem (hrecon d hdmem hde ▸ hdmem)
  · rw [if_neg hle]
    apply Finset.sum_eq_zero
    intro d hdmem
    rw [if_neg]
    intro hde
    apply hle
    have hw : Finsupp.weight (fun k : ℕ => k) d = N :=
      hφ (MvPolynomial.mem_support_iff.mp hdmem)
    have hrecond : d = d.erase 1 + Finsupp.single 1 (d 1) := by
      ext j
      rw [Finsupp.add_apply, Finsupp.erase_apply, Finsupp.single_apply]
      rcases eq_or_ne j 1 with rfl | hj
      · simp
      · simp [hj, Ne.symm hj]
    have hweq : Finsupp.weight (fun k : ℕ => k) d =
        Finsupp.weight (fun k : ℕ => k) (d.erase 1) +
          Finsupp.weight (fun k : ℕ => k) (Finsupp.single 1 (d 1)) := by
      conv_lhs => rw [hrecond]
      exact map_add _ _ _
    rw [hde, hw] at hweq
    omega

/-- **`\text{nontrivialPartCount}` of a monomial equals `monoDeg` of its `X_1`-erasure**,
provided the monomial has no `X_0`-component (always true for the partition-type monomials this
project's `C_n`/`\Delta_{\mathbf n}` produce, since cycle lengths are positive). -/
theorem nontrivialPartCount_eq_monoDeg_erase (d : ℕ →₀ ℕ) (hd0 : d 0 = 0) :
    nontrivialPartCount d = monoDeg (d.erase 1) := by
  unfold nontrivialPartCount
  rw [monoDeg_eq_sum, Finsupp.sum]
  have hseteq : d.support.filter (2 ≤ ·) = (d.erase 1).support := by
    ext k
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, Finsupp.erase_apply]
    constructor
    · rintro ⟨hk, hk2⟩
      rw [if_neg (by omega)]
      exact hk
    · intro hk
      by_cases hk1 : k = 1
      · subst hk1; simp at hk
      · rw [if_neg hk1] at hk
        refine ⟨hk, ?_⟩
        by_contra hlt
        push_neg at hlt
        interval_cases k
        · exact hk hd0
        · exact hk1 rfl
  rw [hseteq]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : k ≠ 1 := by
    intro hEq
    subst hEq
    rw [Finsupp.mem_support_iff, Finsupp.erase_same] at hk
    exact hk rfl
  rw [Finsupp.erase_ne hk1]

#print axioms subst1_C
#print axioms coeff_subst1_of_weighted_homogeneous
#print axioms nontrivialPartCount_eq_monoDeg_erase

end CongruenceTheory
