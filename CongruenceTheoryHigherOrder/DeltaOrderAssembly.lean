import Mathlib
import CongruenceTheoryHigherOrder.BracketDcIdentity
import CongruenceTheoryHigherOrder.SubstMapBridge
import CongruenceTheoryHigherOrder.DcOrderRecursion
import CongruenceTheoryHigherOrder.CpPowWitness
import CongruenceTheoryHigherOrder.WeightedOrder

/-!
**`thm:complete-prime-local`(iii)'s full order assembly (the `R\ge2` case).**
Combines every ingredient built this session into `WOrder nontrivialWeight (\Delta_{\mathbf
n}.\text{map}(\Z/p)) p^\kappa`: `C_p^Q`'s isolated `\text{nontrivialWeight}`-degree-`0` witness
(`CpPowWitness.lean`) combined with `D_{\mathbf c}`'s own order (`exists_MinDeg_Dc`, translated
via `WOrder_of_MinDeg_subst1_map` and `subst1_bracketZ_map_eq_Dc`) through `WOrder.mul_exact`,
then identified with `\Delta_{\mathbf n}` itself via `map_Delta_eq`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`\text{wDeg nontrivialWeight}\,d=0` forces `d\,p=0`**, given `p\ne1`. -/
theorem apply_p_eq_zero_of_wDeg_nontrivialWeight_eq_zero {p : ℕ} (hpne1 : p ≠ 1) (d : ℕ →₀ ℕ)
    (hd : wDeg nontrivialWeight d = 0) : d p = 0 := by
  by_contra hdp
  have hdp_pos : 0 < d p := Nat.pos_of_ne_zero hdp
  rw [wDeg_eq_sum] at hd
  have hpmem : p ∈ d.support := Finsupp.mem_support_iff.mpr hdp
  have hle : nontrivialWeight p * d p ≤ d.sum (fun i e => nontrivialWeight i * e) := by
    rw [Finsupp.sum]
    exact Finset.single_le_sum (f := fun i => nontrivialWeight i * d i)
      (fun i _ => Nat.zero_le _) hpmem
  rw [hd] at hle
  unfold nontrivialWeight at hle
  rw [if_neg hpne1, one_mul] at hle
  omega

/-- **`C_p^Q`'s `\text{WOrder}`**: order exactly `0`, with the unique witness `X_1^{pQ}`. -/
theorem WOrder_Cp_pow {p : ℕ} (hp : p.Prime) (Q : ℕ) :
    WOrder nontrivialWeight
      ((MvPolynomial.map (Int.castRingHom (ZMod p)) (C p)) ^ Q) 0 := by
  haveI := Fact.mk hp
  obtain ⟨hcoeff, -⟩ := coeff_and_support_Cp_pow p hp Q
  refine ⟨fun d _ => Nat.zero_le _, Finsupp.single 1 (p * Q), ?_, ?_⟩
  · exact MvPolynomial.mem_support_iff.mpr (by rw [hcoeff]; exact one_ne_zero)
  · rw [wDeg, Finsupp.weight_single]
    unfold nontrivialWeight
    simp

/-- **The full order assembly**: `\text{WOrder nontrivialWeight}\,(\Delta_{\mathbf
n}.\text{map}(\Z/p))\,p^\kappa`, for `2\le R\le p-1` (`R:=\text{RTot}\,n\,p`) and `D_{\mathbf
c}\ne0`. -/
theorem WOrder_Delta_map {r : ℕ} (n : Fin r → ℕ) {p : ℕ} (hp : p.Prime)
    (hR2 : 2 ≤ RTot n p) (hRp : RTot n p ≤ p - 1)
    (hDcne : Dc p (RTot n p) (HTot n p) (cCount n p) ≠ 0) :
    ∃ κ : ℕ, WOrder nontrivialWeight
      (MvPolynomial.map (Int.castRingHom (ZMod p)) (Delta n)) (p ^ κ) := by
  haveI := Fact.mk hp
  obtain ⟨κ, hκ⟩ := exists_MinDeg_Dc p (RTot n p) (HTot n p) hp (cCount n p) hR2 hRp hDcne
  rw [← subst1_bracketZ_map_eq_Dc n p hp] at hκ
  have hφhomog := isWeightedHomogeneous_bracketZ n hp.pos
  have hbracketOrder := WOrder_of_MinDeg_subst1_map hφhomog hκ
  have hCpOrder := WOrder_Cp_pow hp (QTot n p)
  have hCpUnique : ∀ d ∈ ((MvPolynomial.map (Int.castRingHom (ZMod p)) (C p)) ^ (QTot n p)).support,
      wDeg nontrivialWeight d = 0 →
        d = Classical.choose hCpOrder.2 := by
    intro d hdmem hddeg
    have hdp0 : d p = 0 := apply_p_eq_zero_of_wDeg_nontrivialWeight_eq_zero hp.ne_one d hddeg
    have hchoosespec := Classical.choose_spec hCpOrder.2
    obtain ⟨hcoeff, hunique⟩ := coeff_and_support_Cp_pow p hp (QTot n p)
    have hdeq := hunique d hdmem hdp0
    have hchooseval : Classical.choose hCpOrder.2 = Finsupp.single 1 (p * QTot n p) := by
      have hchoosemem := hchoosespec.1
      exact hunique _ hchoosemem
        (apply_p_eq_zero_of_wDeg_nontrivialWeight_eq_zero hp.ne_one _ hchoosespec.2)
    rw [hchooseval]
    exact hdeq
  have hprodOrder := WOrder.mul_exact hCpOrder hCpUnique hbracketOrder
  rw [zero_add] at hprodOrder
  refine ⟨κ, ?_⟩
  have hbracketZmapeq : MvPolynomial.map (Int.castRingHom (ZMod p)) (bracketZ n p) =
      MvPolynomial.map (Int.castRingHom (ZMod p)) (C (RTot n p)) *
          MvPolynomial.map (Int.castRingHom (ZMod p)) (C p) ^ (HTot n p) -
        ∏ s ∈ Finset.Icc 1 (p - 1),
          MvPolynomial.map (Int.castRingHom (ZMod p)) (C s) ^ (cCount n p s) := by
    unfold bracketZ
    rw [map_sub, map_mul, map_pow, map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro s _
    rw [map_pow]
  rw [hbracketZmapeq] at hprodOrder
  have hDeltaeq := map_Delta_eq hp n
  rw [← hDeltaeq] at hprodOrder
  exact hprodOrder

#print axioms apply_p_eq_zero_of_wDeg_nontrivialWeight_eq_zero
#print axioms WOrder_Cp_pow
#print axioms WOrder_Delta_map

end CongruenceTheory
