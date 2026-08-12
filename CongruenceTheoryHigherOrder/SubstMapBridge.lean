import Mathlib
import CongruenceTheoryHigherOrder.WeightedSubst1
import CongruenceTheoryHigherOrder.WeightedOrder

/-!
**The `\text{subst1}`/`\text{map}` bridge, mod `p`.** Combines `WeightedSubst1.lean`'s
`coeff_subst1_of_weighted_homogeneous` (an integer-level fact) with the observation that
`\text{MvPolynomial.map}` is a ring hom (hence commutes with `\text{if-then-else}` via
`coeff_map`) to get the SAME coefficient correspondence one level down, in
`\text{MvPolynomial}\;\N\;(\Z/p)` directly, and assembles the final translation:
`\text{MinDeg}` of the (mod-`p`) `X_1=1`-substituted polynomial gives `\text{WOrder
nontrivialWeight}` of the (mod-`p`) original — this is what's needed to compare
`\Delta_{\mathbf n}`'s own `\text{nontrivialWeight}`-graded structure to `D_{\mathbf c}`'s
`\text{monoDeg}`-graded structure.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`\text{subst1}\,\varphi` never has an `X_1`-component**, for any `\varphi` (no
weighted-homogeneity needed). -/
theorem subst1_apply_one_eq_zero (φ : MvPolynomial ℕ ℤ) :
    ∀ d ∈ (subst1 φ).support, d 1 = 0 := by
  intro d hd
  rw [MvPolynomial.mem_support_iff] at hd
  by_contra hd1
  apply hd
  unfold subst1
  rw [MvPolynomial.bind₁, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro d' hd'mem
  have halg : algebraMap ℤ (MvPolynomial ℕ ℤ) (MvPolynomial.coeff d' φ) =
      MvPolynomial.C (MvPolynomial.coeff d' φ) := rfl
  rw [halg, MvPolynomial.coeff_C_mul]
  have hprodeq : (∏ i ∈ d'.support,
      (if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) ^ d' i) =
      d'.prod fun i e => (if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) ^ e := rfl
  rw [hprodeq, prod_subst_eq_monomial_erase, MvPolynomial.coeff_monomial]
  rw [if_neg]
  · ring
  · intro hde
    apply hd1
    rw [← hde, Finsupp.erase_same]

/-- **The `\text{subst1}`/`\text{map}` coefficient bridge, mod `p`**: for `\varphi`
weighted-homogeneous of degree `N` and `e` supported away from index `1`,
`\text{coeff}_e((\text{subst1}\,\varphi).\text{map}(\Z/p))` is the mod-`p` coefficient of
`\varphi` at the unique degree-`N` monomial extending `e`. -/
theorem coeff_subst1_map_of_weighted_homogeneous {φ : MvPolynomial ℕ ℤ} {N p : ℕ}
    (hφ : IsWeightedHomogeneous (fun k : ℕ => k) φ N) (e : ℕ →₀ ℕ) (he1 : e 1 = 0) :
    MvPolynomial.coeff e ((subst1 φ).map (Int.castRingHom (ZMod p))) =
      if Finsupp.weight (fun k : ℕ => k) e ≤ N then
        MvPolynomial.coeff (e + Finsupp.single 1 (N - Finsupp.weight (fun k : ℕ => k) e))
          (φ.map (Int.castRingHom (ZMod p)))
      else 0 := by
  rw [MvPolynomial.coeff_map, coeff_subst1_of_weighted_homogeneous hφ e he1]
  split_ifs with h
  · rw [MvPolynomial.coeff_map]
  · simp

/-- **`\text{WOrder}` of `\varphi.\text{map}(\Z/p)` from `\text{MinDeg}` of
`(\text{subst1}\,\varphi).\text{map}(\Z/p)`**: the `X_1=1` substitution turns
`\text{nontrivialWeight}`-order into ordinary `\text{monoDeg}`-order exactly, for `\varphi`
weighted-homogeneous. -/
theorem WOrder_of_MinDeg_subst1_map {φ : MvPolynomial ℕ ℤ} {N p : ℕ}
    (hφ : IsWeightedHomogeneous (fun k : ℕ => k) φ N) {k : ℕ}
    (hDc : MinDeg ((subst1 φ).map (Int.castRingHom (ZMod p))) k) :
    WOrder nontrivialWeight (φ.map (Int.castRingHom (ZMod p))) k := by
  constructor
  · intro d hd
    have hdmem : d ∈ (φ.map (Int.castRingHom (ZMod p))).support :=
      MvPolynomial.mem_support_iff.mpr (MvPolynomial.mem_support_iff.mp hd)
    have hdφ : d ∈ φ.support :=
      Finset.mem_of_subset (MvPolynomial.support_map_subset (Int.castRingHom (ZMod p)) φ) hdmem
    have hdweight : Finsupp.weight (fun k : ℕ => k) d = N :=
      hφ (MvPolynomial.mem_support_iff.mp hdφ)
    set e := d.erase 1 with hedef
    have he1 : e 1 = 0 := Finsupp.erase_same
    have hde : d = e + Finsupp.single 1 (d 1) := by
      ext j
      rw [Finsupp.add_apply, hedef, Finsupp.erase_apply, Finsupp.single_apply]
      rcases eq_or_ne j 1 with rfl | hj
      · simp
      · simp [hj, Ne.symm hj]
    have hweq : Finsupp.weight (fun k : ℕ => k) d =
        Finsupp.weight (fun k : ℕ => k) e + d 1 := by
      conv_lhs => rw [hde]
      rw [map_add, Finsupp.weight_single, smul_eq_mul, mul_one]
    rw [hdweight] at hweq
    have hele : Finsupp.weight (fun k : ℕ => k) e ≤ N := by omega
    have hbridge := coeff_subst1_map_of_weighted_homogeneous (p := p) hφ e he1
    rw [if_pos hele] at hbridge
    have hNsub : N - Finsupp.weight (fun k : ℕ => k) e = d 1 := by omega
    rw [hNsub, ← hde] at hbridge
    have hemem : e ∈ ((subst1 φ).map (Int.castRingHom (ZMod p))).support := by
      rw [MvPolynomial.mem_support_iff, hbridge]
      exact MvPolynomial.mem_support_iff.mp hdmem
    have hkle : k ≤ monoDeg e := hDc.le hemem
    have hwdeq : wDeg nontrivialWeight d = wDeg nontrivialWeight e := by
      conv_lhs => rw [hde]
      rw [wDeg_add]
      have : wDeg nontrivialWeight (Finsupp.single 1 (d 1)) = 0 := by
        rw [wDeg, Finsupp.weight_single]
        unfold nontrivialWeight
        simp
      rw [this, add_zero]
    rw [hwdeq, wDeg_nontrivialWeight_eq_monoDeg_of_apply_one_eq_zero e he1]
    exact hkle
  · obtain ⟨e₀, he₀mem, he₀deg⟩ := hDc.2
    have he₀mem' : e₀ ∈ (subst1 φ).support :=
      Finset.mem_of_subset
        (MvPolynomial.support_map_subset (Int.castRingHom (ZMod p)) (subst1 φ)) he₀mem
    have he₀1 : e₀ 1 = 0 := subst1_apply_one_eq_zero φ e₀ he₀mem'
    have hbridge := coeff_subst1_map_of_weighted_homogeneous (p := p) hφ e₀ he₀1
    rw [MvPolynomial.mem_support_iff] at he₀mem
    have hle0 : Finsupp.weight (fun k : ℕ => k) e₀ ≤ N := by
      by_contra hcon
      rw [if_neg hcon] at hbridge
      exact he₀mem hbridge
    rw [if_pos hle0] at hbridge
    set d₀ := e₀ + Finsupp.single 1 (N - Finsupp.weight (fun k : ℕ => k) e₀) with hd₀def
    have hd₀mem : d₀ ∈ (φ.map (Int.castRingHom (ZMod p))).support := by
      rw [MvPolynomial.mem_support_iff, ← hbridge]
      exact he₀mem
    refine ⟨d₀, hd₀mem, ?_⟩
    have hwdeq : wDeg nontrivialWeight d₀ = wDeg nontrivialWeight e₀ := by
      rw [hd₀def, wDeg_add]
      have : wDeg nontrivialWeight
          (Finsupp.single 1 (N - Finsupp.weight (fun k : ℕ => k) e₀)) = 0 := by
        rw [wDeg, Finsupp.weight_single]
        unfold nontrivialWeight
        simp
      rw [this, add_zero]
    rw [hwdeq, wDeg_nontrivialWeight_eq_monoDeg_of_apply_one_eq_zero e₀ he₀1]
    exact he₀deg

#print axioms subst1_apply_one_eq_zero
#print axioms coeff_subst1_map_of_weighted_homogeneous
#print axioms WOrder_of_MinDeg_subst1_map

end CongruenceTheory
