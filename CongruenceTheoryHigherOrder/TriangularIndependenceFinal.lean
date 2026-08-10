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
import CongruenceTheoryHigherOrder.TriangularAssembly

/-!
**`cor:triangular-independence`, fully assembled.** Packages `L_1 := C_p`, `L_j :=
p^{-e_p(j)}K_j(p)` (`j\ge2`) as a single family `triangularFamily`, verifies
`algebraicIndependent_of_triangular`'s hypotheses using every piece proved so far, and concludes
`AlgebraicIndependent (ZMod p) (triangularFamily p)` — the manuscript's own corollary, for every
`M` (algebraic independence of the full family restricts to any finite sub-family).
-/

namespace CongruenceTheory

open MvPolynomial

/-- Ring-generic version of `le_of_mem_vars_isWeightedHomogeneous` (`SpecializationVars.lean`
proves it only for `MvPolynomial ℕ ℤ`; the argument is ring-agnostic). -/
theorem le_of_mem_vars_isWeightedHomogeneous' {R : Type*} [CommRing R] {φ : MvPolynomial ℕ R}
    {n : ℕ} (hφ : IsWeightedHomogeneous (fun k : ℕ => k) φ n) {i : ℕ} (hi : i ∈ φ.vars) :
    i ≤ n := by
  obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support i).mp hi
  have hcoeff : coeff d φ ≠ 0 := mem_support_iff.mp hd
  have hweight : Finsupp.weight (fun k : ℕ => k) d = n := hφ hcoeff
  rw [Finsupp.weight_apply, Finsupp.sum] at hweight
  simp only [smul_eq_mul] at hweight
  have hdi : d i ≠ 0 := Finsupp.mem_support_iff.mp hid
  have hsingle : d i * i ≤ ∑ a ∈ d.support, d a * a :=
    Finset.single_le_sum (fun a _ => Nat.zero_le (d a * a)) hid
  have hdi1 : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr hdi
  calc i = 1 * i := (one_mul i).symm
    _ ≤ d i * i := Nat.mul_le_mul_right i hdi1
    _ ≤ ∑ a ∈ d.support, d a * a := hsingle
    _ = n := hweight

/-- Every coefficient index `i` occurring in `d.prod (specSubst p ·)^·`'s underlying source
support is bounded by `j*p`'s target image `j`, for `d` in `K_j(p)`'s support. -/
theorem vars_specSubst_finsuppProd_subset {p j : ℕ} [Fact (Nat.Prime p)] {d : ℕ →₀ ℕ}
    (hK : coeff d (K j p) ≠ 0) :
    ∀ m ∈ (d.prod fun i k => specSubst p i ^ k).vars, m ≤ j := by
  intro m hm
  have hw : Finsupp.weight (fun k : ℕ => k) d = j * p := isWeightedHomogeneous_K j p hK
  have hbind : (d.prod fun i k => specSubst p i ^ k) =
      bind₁ (specSubst p) (monomial d (1 : ZMod p)) := by
    rw [bind₁_monomial, C_1, one_mul, Finsupp.prod]
  rw [hbind] at hm
  obtain ⟨i, hi, hmi⟩ := mem_vars_bind₁ (specSubst p) (monomial d (1 : ZMod p)) hm
  have hmono : IsWeightedHomogeneous (fun k : ℕ => k) (monomial d (1 : ZMod p)) (j * p) :=
    isWeightedHomogeneous_monomial _ d 1 hw
  have hile : i ≤ j * p := le_of_mem_vars_isWeightedHomogeneous' hmono hi
  have hmeq : m = i / p := Finset.mem_singleton.mp (specSubst_vars_subset p i hmi)
  have hppos : 0 < p := (Fact.out (p := Nat.Prime p)).pos
  rw [hmeq]
  calc i / p ≤ (j * p) / p := Nat.div_le_div_right hile
    _ = j := Nat.mul_div_cancel j hppos

/-- Every variable occurring in `specialize p (normalizedLayer p j)` is at most `j`. -/
theorem specialize_normalizedLayer_vars_subset (p j : ℕ) [Fact (Nat.Prime p)] :
    ∀ m ∈ (specialize p (normalizedLayer p j)).vars, m ≤ j := by
  intro m hm
  obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.mp (vars_specialize_subset p (normalizedLayer p j) hm)
  have hhomog : IsWeightedHomogeneous (fun k : ℕ => k) (normalizedLayer p j) (j * p) := by
    intro d hd
    exact isWeightedHomogeneous_K j p (coeff_ne_zero_of_coeff_divPoly_ne_zero hd)
  have hile : i ≤ j * p := le_of_mem_vars_isWeightedHomogeneous hhomog hi
  have hmeq : m = i / p := Finset.mem_singleton.mp (specSubst_vars_subset p i hmi)
  have hppos : 0 < p := (Fact.out (p := Nat.Prime p)).pos
  rw [hmeq]
  calc i / p ≤ (j * p) / p := Nat.div_le_div_right hile
    _ = j := Nat.mul_div_cancel j hppos

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The manuscript's family: `L_1 = C_p` (matching `normalizedLayer p 1 = K_1(p) = C_p`, since
`e_p(1)=0`), `L_j = p^{-e_p(j)}K_j(p)` for `j\ge2`, padded by `X_0` at index `0` (unused). -/
noncomputable def triangularFamily : ℕ → MvPolynomial ℕ (ZMod p)
  | 0 => X 0
  | (j + 1) => specialize p (normalizedLayer p (j + 1))

theorem two_le_succ_mul (j : ℕ) : 2 ≤ (j + 1) * p := by
  have h2 := (Fact.out (p := Nat.Prime p)).two_le
  nlinarith

noncomputable def triangularC : (j : ℕ) → (ZMod p)ˣ
  | 0 => 1
  | (j + 1) => (isUnit_iff_ne_zero.mpr
      (coeff_target_specialize_normalizedLayer (p := p) (j := j + 1) (Nat.le_add_left 1 j)
        (two_le_succ_mul p j))).unit

noncomputable def triangularG (j : ℕ) : MvPolynomial ℕ (ZMod p) :=
  triangularFamily p j - MvPolynomial.C ((triangularC p j : ZMod p)) * X j

theorem triangularFamily_eq (j : ℕ) :
    triangularFamily p j = MvPolynomial.C ((triangularC p j : ZMod p)) * X j + triangularG p j := by
  unfold triangularG; ring

set_option maxHeartbeats 0 in
-- The Finset.sum_eq_single/Finset.add_sum_erase chain over large cast/monomial expressions
-- pushes elaboration well past the default heartbeat budget; no step here is actually looping.
theorem triangularG_vars_lt (j : ℕ) : ∀ i ∈ (triangularG p j).vars, i < j := by
  intro i hi
  match j with
  | 0 =>
    exfalso
    unfold triangularG triangularFamily triangularC at hi
    simp at hi
  | (j' + 1) =>
    set φ := normalizedLayer p (j' + 1) with hφ
    have hcj : (triangularC p (j' + 1) : ZMod p) =
        coeff (Finsupp.single (j' + 1) 1) (specialize p φ) := by
      show ((isUnit_iff_ne_zero.mpr
        (coeff_target_specialize_normalizedLayer (p := p) (j := j' + 1) (Nat.le_add_left 1 j')
          (two_le_succ_mul p j'))).unit : ZMod p) = _
      rw [IsUnit.unit_spec]
    have hspec : specialize p φ =
        ∑ d ∈ φ.support, bind₁ (specSubst p)
          (MvPolynomial.map (Int.castRingHom (ZMod p)) (monomial d (coeff d φ))) := by
      conv_lhs => rw [specialize_apply, φ.as_sum]
      rw [map_sum, map_sum]
    have hsingle : (Finsupp.single ((j' + 1) * p) 1 : ℕ →₀ ℕ) ∈ φ.support := by
      rw [mem_support_iff, hφ, coeff_single_normalizedLayer (Fact.out (p := Nat.Prime p))
        (Nat.le_add_left 1 j') (two_le_succ_mul p j')]
      intro hzero
      have hdvd : p ^ firstPrimeLayerExponent p (j' + 1) ∣ Nat.factorial ((j' + 1) * p - 1) := by
        rw [← (firstPrimeLayer (Fact.out (p := Nat.Prime p)) (Nat.le_add_left 1 j')
          (two_le_succ_mul p j')).2.2]
        exact Nat.ordProj_dvd (Nat.factorial ((j' + 1) * p - 1)) p
      have hne0 : Nat.factorial ((j' + 1) * p - 1) /
          p ^ firstPrimeLayerExponent p (j' + 1) ≠ 0 := by
        intro hcontra
        have := Nat.div_mul_cancel hdvd
        rw [hcontra, zero_mul] at this
        exact Nat.factorial_ne_zero _ this.symm
      exact hne0 (by exact_mod_cast hzero)
    have hterm0 : bind₁ (specSubst p) (MvPolynomial.map (Int.castRingHom (ZMod p))
        (monomial (Finsupp.single ((j' + 1) * p) 1) (coeff (Finsupp.single ((j' + 1) * p) 1) φ))) =
        MvPolynomial.C ((Int.castRingHom (ZMod p)) (coeff (Finsupp.single ((j' + 1) * p) 1) φ)) *
          X (j' + 1) := by
      rw [map_monomial, bind₁_monomial]
      have hsupp : (Finsupp.single ((j' + 1) * p) 1 : ℕ →₀ ℕ).support = {(j' + 1) * p} :=
        Finsupp.support_single_ne_zero _ (by norm_num)
      rw [hsupp, Finset.prod_singleton]
      have hdprod : specSubst p ((j' + 1) * p) ^
          (Finsupp.single ((j' + 1) * p) 1 : ℕ →₀ ℕ) ((j' + 1) * p) = X (j' + 1) := by
        rw [Finsupp.single_eq_same, pow_one]
        unfold specSubst
        have hjp1 : (j' + 1) * p ≠ 1 := by
          have h2 := (Fact.out (p := Nat.Prime p)).two_le; nlinarith
        have hjpdvd : p ∣ (j' + 1) * p := dvd_mul_left p (j' + 1)
        rw [if_neg hjp1, if_pos hjpdvd]
        congr 1
        exact Nat.mul_div_cancel (j' + 1) (Fact.out (p := Nat.Prime p)).pos
      rw [hdprod]
    have hval : coeff (Finsupp.single (j' + 1) 1) (specialize p φ) =
        (Int.castRingHom (ZMod p)) (coeff (Finsupp.single ((j' + 1) * p) 1) φ) := by
      rw [hspec, coeff_sum, Finset.sum_eq_single (Finsupp.single ((j' + 1) * p) 1)]
      · rw [hterm0, coeff_C_mul, coeff_X, if_pos rfl, mul_one]
      · intro d hdmem hdne
        have hK : coeff d (K (j' + 1) p) ≠ 0 :=
          coeff_ne_zero_of_coeff_divPoly_ne_zero (φ := K (j' + 1) p)
            (c := (p : ℤ) ^ firstPrimeLayerExponent p (j' + 1)) (mem_support_iff.mp hdmem)
        have hjnot : (j' + 1) ∉ (d.prod fun i k => specSubst p i ^ k).vars :=
          j_notMem_vars_specSubst_finsuppProd (Nat.le_add_left 1 j') hK hdne
        have heqform : bind₁ (specSubst p) (MvPolynomial.map (Int.castRingHom (ZMod p))
            (monomial d (coeff d φ))) =
            MvPolynomial.C ((Int.castRingHom (ZMod p)) (coeff d φ)) *
              (d.prod fun i k => specSubst p i ^ k) := by
          rw [map_monomial, bind₁_monomial, Finsupp.prod]
        rw [heqform, coeff_C_mul]
        have hzero : coeff (Finsupp.single (j' + 1) 1)
            (d.prod fun i k => specSubst p i ^ k) = 0 := by
          by_contra hne
          apply hjnot
          rw [mem_vars_iff_mem_support]
          refine ⟨Finsupp.single (j' + 1) 1, mem_support_iff.mpr hne, ?_⟩
          rw [Finsupp.mem_support_iff, Finsupp.single_eq_same]
          exact one_ne_zero
        rw [hzero, mul_zero]
      · intro hnmem
        exact absurd hsingle hnmem
    rw [hval] at hcj
    have hterm : bind₁ (specSubst p) (MvPolynomial.map (Int.castRingHom (ZMod p))
        (monomial (Finsupp.single ((j' + 1) * p) 1) (coeff (Finsupp.single ((j' + 1) * p) 1) φ))) =
        MvPolynomial.C ((triangularC p (j' + 1) : ZMod p)) * X (j' + 1) := by
      rw [hcj, hterm0]
    have hdecomp : specialize p φ =
        MvPolynomial.C ((triangularC p (j' + 1) : ZMod p)) * X (j' + 1) +
        ∑ d ∈ φ.support.erase (Finsupp.single ((j' + 1) * p) 1),
          bind₁ (specSubst p) (MvPolynomial.map (Int.castRingHom (ZMod p))
            (monomial d (coeff d φ))) := by
      rw [hspec, ← hterm]
      exact (Finset.add_sum_erase φ.support
        (fun d => bind₁ (specSubst p)
          (MvPolynomial.map (Int.castRingHom (ZMod p)) (monomial d (coeff d φ))))
        hsingle).symm
    have hG : triangularG p (j' + 1) =
        ∑ d ∈ φ.support.erase (Finsupp.single ((j' + 1) * p) 1),
          bind₁ (specSubst p) (MvPolynomial.map (Int.castRingHom (ZMod p))
            (monomial d (coeff d φ))) := by
      show triangularFamily p (j' + 1) - _ = _
      rw [show triangularFamily p (j' + 1) = specialize p φ from rfl, hdecomp]
      ring
    rw [hG] at hi
    obtain ⟨d, hd, hid⟩ := Finset.mem_biUnion.mp (vars_sum_subset _ _ hi)
    obtain ⟨hdne, hdmem⟩ := Finset.mem_erase.mp hd
    have hterm_eq : bind₁ (specSubst p) (MvPolynomial.map (Int.castRingHom (ZMod p))
        (monomial d (coeff d φ))) =
        MvPolynomial.C ((Int.castRingHom (ZMod p)) (coeff d φ)) *
          (d.prod fun i k => specSubst p i ^ k) := by
      rw [map_monomial, bind₁_monomial]
      congr 1
    rw [hterm_eq] at hid
    have hvars_sub : i ∈ (d.prod fun i k => specSubst p i ^ k).vars := by
      have hsub := vars_mul (MvPolynomial.C ((Int.castRingHom (ZMod p)) (coeff d φ)))
        (d.prod fun i k => specSubst p i ^ k)
      rcases Finset.mem_union.mp (hsub hid) with h | h
      · rw [vars_C] at h; exact absurd h (Finset.notMem_empty i)
      · exact h
    have hK : coeff d (K (j' + 1) p) ≠ 0 :=
      coeff_ne_zero_of_coeff_divPoly_ne_zero (φ := K (j' + 1) p)
        (c := (p : ℤ) ^ firstPrimeLayerExponent p (j' + 1)) (mem_support_iff.mp hdmem)
    have hile : i ≤ j' + 1 := vars_specSubst_finsuppProd_subset hK i hvars_sub
    have hine : i ≠ j' + 1 :=
      fun heq => (j_notMem_vars_specSubst_finsuppProd (Nat.le_add_left 1 j') hK hdne)
        (heq ▸ hvars_sub)
    omega

/-- **`cor:triangular-independence`, the manuscript's own corollary.** Writing `L_1=C_p`,
`L_j=p^{-e_p(j)}K_j(p)` for `j\ge2`, the reductions of `L_1,\ldots,L_M` modulo `p` are
algebraically independent over `\mathbb F_p`, for every `M`. -/
theorem triangular_independence : AlgebraicIndependent (ZMod p) (triangularFamily p) :=
  algebraicIndependent_of_triangular (triangularFamily p) (triangularC p) (triangularG p)
    (triangularFamily_eq p) (triangularG_vars_lt p)

#print axioms triangular_independence

end CongruenceTheory
