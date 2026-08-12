import Mathlib
import CongruenceTheoryHigherOrder.DeltaFactorization
import CongruenceTheoryHigherOrder.WeightedSubst1
import CongruenceTheoryHigherOrder.FmZPrimeValue
import CongruenceTheoryHigherOrder.DcDef
import CongruenceTheoryHigherOrder.DefectWeightedHomogeneous

/-!
**The bracket/`D_{\mathbf c}` identity.** `\text{bracketZ}(n,p):=C_R\cdot C_p^H-\prod_{s=1}^{p-1}
C_s^{c_s}` (the integer version of `DeltaFactorization.lean`'s mod-`p` bracket) satisfies
`(\text{subst1}\,\text{bracketZ}).\text{map}(\Z/p)=D_{\mathbf c}` exactly, via `subst1(C_m)=F_m`
(`subst1_C`) and `F_p\equiv1-X_p\pmod p` (`FmZ_p_eq`) — identifying the manuscript's "remove the
common factor `C_p^{\sum q_i}`, use weighted homogeneity to put `X_1=1`" step with this
project's `D_{\mathbf c}` exactly.
-/

namespace CongruenceTheory

open MvPolynomial

variable {r : ℕ} (n : Fin r → ℕ) (p : ℕ)

/-- **The integer bracket**: `C_R\cdot C_p^H-\prod_{s=1}^{p-1}C_s^{c_s}`. -/
noncomputable def bracketZ : MvPolynomial ℕ ℤ :=
  C (RTot n p) * (C p) ^ (HTot n p) - ∏ s ∈ Finset.Icc 1 (p - 1), (C s) ^ (cCount n p s)

variable {p}

/-- **`\text{bracketZ}` is weighted-homogeneous of degree `pH+R`.** -/
theorem isWeightedHomogeneous_bracketZ (hp0 : 0 < p) :
    IsWeightedHomogeneous (fun k : ℕ => k) (bracketZ n p)
      (p * (HTot n p) + RTot n p) := by
  unfold bracketZ
  rw [show p * HTot n p + RTot n p = RTot n p + p * HTot n p from by ring]
  apply IsWeightedHomogeneous.sub
  · have hp1 := IsWeightedHomogeneous.finset_prod (Finset.range (HTot n p))
      (fun _ => C p) (fun _ => p) (fun i _ => isWeightedHomogeneous_C p)
    have hp2 : ∏ _i ∈ Finset.range (HTot n p), C p = C p ^ (HTot n p) := by
      rw [Finset.prod_const, Finset.card_range]
    rw [hp2] at hp1
    have hp3 : ∑ _i ∈ Finset.range (HTot n p), p = p * HTot n p := by
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
    rw [hp3] at hp1
    exact (isWeightedHomogeneous_C (RTot n p)).mul hp1
  · have hprodhom := IsWeightedHomogeneous.finset_prod (Finset.Icc 1 (p - 1))
      (fun s => C s ^ (cCount n p s)) (fun s => cCount n p s • s)
      (fun s _ => (isWeightedHomogeneous_C s).pow (cCount n p s))
    simp only [smul_eq_mul] at hprodhom
    have hsumeq : ∑ s ∈ Finset.Icc 1 (p - 1), cCount n p s * s = RTot n p + p * HTot n p := by
      have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin r)), n i % p ∈ Finset.range p :=
        fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ hp0)
      have hfiber := Finset.sum_fiberwise_of_maps_to' hmaps (fun s => s)
      have hswap : ∑ i : Fin r, n i % p = ∑ s ∈ Finset.range p, cCount n p s * s := by
        rw [← hfiber]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.sum_const, smul_eq_mul]
        rfl
      have hrangeeq : Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) := by
        ext x
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hrangeeq, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)] at hswap
      simp only [mul_zero, zero_add] at hswap
      rw [← hswap, sum_mod_eq n hp0]
      ring
    rwa [hsumeq] at hprodhom

variable (p)

/-- **The bracket/`D_{\mathbf c}` identity**: `(\text{subst1}\,\text{bracketZ}).\text{map}
(\Z/p)=D_{\mathbf c}` exactly. -/
theorem subst1_bracketZ_map_eq_Dc (hp : p.Prime) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (subst1 (bracketZ n p)) =
      Dc p (RTot n p) (HTot n p) (cCount n p) := by
  have hR : MvPolynomial.map (Int.castRingHom (ZMod p)) (subst1 (C (RTot n p))) =
      FmZ p (RTot n p) := by
    rw [subst1_C]; rfl
  have hP : MvPolynomial.map (Int.castRingHom (ZMod p)) (subst1 (C p)) =
      1 - MvPolynomial.X p := by
    rw [subst1_C]; exact FmZ_p_eq p hp
  have hS : ∀ s, MvPolynomial.map (Int.castRingHom (ZMod p)) (subst1 (C s)) = FmZ p s := by
    intro s; rw [subst1_C]; rfl
  unfold bracketZ subst1
  rw [map_sub, map_mul, map_pow, map_prod, map_sub, map_mul, map_pow, map_prod]
  unfold subst1 at hR hP hS
  rw [hR, hP]
  unfold Dc
  congr 1
  apply Finset.prod_congr rfl
  intro s _
  simp only [map_pow, hS]

#print axioms isWeightedHomogeneous_bracketZ
#print axioms subst1_bracketZ_map_eq_Dc

end CongruenceTheory
