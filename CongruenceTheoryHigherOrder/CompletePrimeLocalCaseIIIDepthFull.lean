import Mathlib
import CongruenceTheoryHigherOrder.CompletePrimeLocalCaseIIIDepth
import CongruenceTheoryHigherOrder.DcResidualStep

/-!
**`thm:complete-prime-local`(iii)'s depth theorem, fully general (`R\ge0` unrestricted).**
Extends `CompletePrimeLocalCaseIIIDepth.lean`'s `R\ge2` result to the full range `R\ge0`: when
`R\in\{0,1\}`, `F_R=1` (`FmZ_zero`/`FmZ_one`), so `D_{R,h,c}=D_{1,h,c}` identically, and the
*residual* order recursion (`exists_MinDeg_Dc_r1`, `DcResidualStep.lean`/`DcOrderRecursion.lean`)
applies directly in place of the general step. Combined with the `R\ge2` case, this covers every
possible shift residue `R=\text{RTot}\,n\,p\in\{0,\ldots,p-1\}` arising from `thm:complete-
prime-local`(iii)'s own hypotheses.
-/

namespace CongruenceTheory

open MvPolynomial

theorem FmZ_zero (p : ℕ) : FmZ p 0 = 1 := by
  unfold FmZ
  rw [Fm_zero]
  simp

/-- **`D_{r,h,c}=D_{1,h,c}` whenever `r<2`.** -/
theorem Dc_r_lt_two_eq_r1 (p h : ℕ) (c : ℕ → ℕ) {r : ℕ} (hr : r < 2) :
    Dc p r h c = Dc p 1 h c := by
  interval_cases r
  · unfold Dc
    rw [FmZ_zero, FmZ_one]
  · rfl

/-- **`\exists\kappa,\text{MinDeg}(D_{r,h,c})\,p^\kappa`, unconditionally on `r`** (given
nonzero), combining the general step (`r\ge2`) with the residual step (`r<2`). -/
theorem exists_MinDeg_Dc_general (p r h : ℕ) (hp : p.Prime) (c : ℕ → ℕ)
    (hrp : r ≤ p - 1) (hDcne : Dc p r h c ≠ 0) :
    ∃ κ : ℕ, MinDeg (Dc p r h c) (p ^ κ) := by
  by_cases hr2 : 2 ≤ r
  · exact exists_MinDeg_Dc p r h hp c hr2 hrp hDcne
  · push_neg at hr2
    have heq : Dc p r h c = Dc p 1 h c := Dc_r_lt_two_eq_r1 p h c hr2
    rw [heq] at hDcne ⊢
    exact exists_MinDeg_Dc_r1 p hp _ h c rfl hDcne

/-- **The full order assembly, `R` unrestricted.** -/
theorem WOrder_Delta_map_full {r : ℕ} (n : Fin r → ℕ) {p : ℕ} (hp : p.Prime)
    (hRp : RTot n p ≤ p - 1)
    (hDcne : Dc p (RTot n p) (HTot n p) (cCount n p) ≠ 0) :
    ∃ κ : ℕ, WOrder nontrivialWeight
      (MvPolynomial.map (Int.castRingHom (ZMod p)) (Delta n)) (p ^ κ) := by
  haveI := Fact.mk hp
  obtain ⟨κ, hκ⟩ :=
    exists_MinDeg_Dc_general p (RTot n p) (HTot n p) hp (cCount n p) hRp hDcne
  rw [← subst1_bracketZ_map_eq_Dc n p hp] at hκ
  have hφhomog := isWeightedHomogeneous_bracketZ n hp.pos
  have hbracketOrder := WOrder_of_MinDeg_subst1_map hφhomog hκ
  have hCpOrder := WOrder_Cp_pow hp (QTot n p)
  have hCpUnique : ∀ d ∈ ((MvPolynomial.map (Int.castRingHom (ZMod p)) (C p)) ^
      (QTot n p)).support, wDeg nontrivialWeight d = 0 →
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

/-- **The full `thm:complete-prime-local`(iii) depth theorem, `R` unrestricted.** `p^\kappa` is
the least `s\ge1` at which `\text{Dgcd}(\Delta_{\mathbf n},s)` is both nonzero and not divisible
by `p`. -/
theorem complete_prime_local_case_iii_depth_full {r : ℕ} (n : Fin r → ℕ) {p : ℕ} (hp : p.Prime)
    (hRp : RTot n p ≤ p - 1)
    (hDcne : Dc p (RTot n p) (HTot n p) (cCount n p) ≠ 0) :
    ∃ κ : ℕ, IsLeast {s : ℕ | 1 ≤ s ∧ Dgcd (Delta n) s ≠ 0 ∧
        (Dgcd (Delta n) s).factorization p = 0} (p ^ κ) := by
  haveI := Fact.mk hp
  obtain ⟨κ, hWOrder⟩ := WOrder_Delta_map_full n hp hRp hDcne
  refine ⟨κ, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero κ hp.pos.ne')
  · obtain ⟨d₀, hd₀mem, hd₀deg⟩ := hWOrder.2
    have hd₀memΔ : d₀ ∈ (Delta n).support :=
      Finset.mem_of_subset
        (MvPolynomial.support_map_subset (Int.castRingHom (ZMod p)) (Delta n)) hd₀mem
    have hd₀0 : d₀ 0 = 0 := apply_zero_eq_zero_of_mem_support_Delta n d₀ hd₀memΔ
    have hd₀npc : nontrivialPartCount d₀ = p ^ κ := by
      rw [← wDeg_nontrivialWeight_eq d₀ hd₀0]
      exact hd₀deg
    have hd₀filt : d₀ ∈ (Delta n).support.filter (fun d => nontrivialPartCount d ≤ p ^ κ) :=
      Finset.mem_filter.mpr ⟨hd₀memΔ, le_of_eq hd₀npc⟩
    intro h0
    unfold Dgcd at h0
    have hdvd : (Finset.gcd ((Delta n).support.filter
        (fun d => nontrivialPartCount d ≤ p ^ κ)) (fun d => (coeff d (Delta n)).natAbs)) ∣
        (coeff d₀ (Delta n)).natAbs := Finset.gcd_dvd hd₀filt
    rw [h0] at hdvd
    have : coeff d₀ (Delta n) = 0 := by
      have := Nat.eq_zero_of_zero_dvd hdvd
      exact Int.natAbs_eq_zero.mp this
    exact (MvPolynomial.mem_support_iff.mp hd₀memΔ) this
  · obtain ⟨d₀, hd₀mem, hd₀deg⟩ := hWOrder.2
    have hd₀memΔ : d₀ ∈ (Delta n).support :=
      Finset.mem_of_subset
        (MvPolynomial.support_map_subset (Int.castRingHom (ZMod p)) (Delta n)) hd₀mem
    have hd₀0 : d₀ 0 = 0 := apply_zero_eq_zero_of_mem_support_Delta n d₀ hd₀memΔ
    have hd₀npc : nontrivialPartCount d₀ = p ^ κ := by
      rw [← wDeg_nontrivialWeight_eq d₀ hd₀0]
      exact hd₀deg
    have hd₀filt : d₀ ∈ (Delta n).support.filter (fun d => nontrivialPartCount d ≤ p ^ κ) :=
      Finset.mem_filter.mpr ⟨hd₀memΔ, le_of_eq hd₀npc⟩
    have hdvd : Dgcd (Delta n) (p ^ κ) ∣ (coeff d₀ (Delta n)).natAbs := by
      unfold Dgcd
      exact Finset.gcd_dvd hd₀filt
    have hndvd : ¬ (p : ℤ) ∣ coeff d₀ (Delta n) := (mem_support_map_iff d₀).mp hd₀mem
    have hDgne : Dgcd (Delta n) (p ^ κ) ≠ 0 := by
      obtain ⟨d₀', hd₀'mem, hd₀'deg⟩ := hWOrder.2
      have hd₀'memΔ : d₀' ∈ (Delta n).support :=
        Finset.mem_of_subset
          (MvPolynomial.support_map_subset (Int.castRingHom (ZMod p)) (Delta n)) hd₀'mem
      have hd₀'0 : d₀' 0 = 0 := apply_zero_eq_zero_of_mem_support_Delta n d₀' hd₀'memΔ
      have hd₀'npc : nontrivialPartCount d₀' = p ^ κ := by
        rw [← wDeg_nontrivialWeight_eq d₀' hd₀'0]; exact hd₀'deg
      have hd₀'filt : d₀' ∈ (Delta n).support.filter
          (fun d => nontrivialPartCount d ≤ p ^ κ) :=
        Finset.mem_filter.mpr ⟨hd₀'memΔ, le_of_eq hd₀'npc⟩
      intro h0
      unfold Dgcd at h0
      have hdvd' : (Finset.gcd ((Delta n).support.filter
          (fun d => nontrivialPartCount d ≤ p ^ κ)) (fun d => (coeff d (Delta n)).natAbs)) ∣
          (coeff d₀' (Delta n)).natAbs := Finset.gcd_dvd hd₀'filt
      rw [h0] at hdvd'
      have : coeff d₀' (Delta n) = 0 := by
        have := Nat.eq_zero_of_zero_dvd hdvd'
        exact Int.natAbs_eq_zero.mp this
      exact (MvPolynomial.mem_support_iff.mp hd₀'memΔ) this
    by_contra hcon
    have h1le : 1 ≤ (Dgcd (Delta n) (p ^ κ)).factorization p := Nat.one_le_iff_ne_zero.mpr hcon
    have hpdvd : p ∣ Dgcd (Delta n) (p ^ κ) :=
      (Nat.Prime.dvd_iff_one_le_factorization hp hDgne).mpr h1le
    have hpdvdz : (p : ℤ) ∣ coeff d₀ (Delta n) := by
      have h1 : p ∣ (coeff d₀ (Delta n)).natAbs := hpdvd.trans hdvd
      have h2 := Int.natCast_dvd_natCast.mpr h1
      rwa [Int.dvd_natAbs] at h2
    exact hndvd hpdvdz
  · rintro s ⟨hs1, hDsne, hsfact⟩
    by_contra hlt
    push_neg at hlt
    have hall : ∀ d ∈ (Delta n).support, nontrivialPartCount d ≤ s →
        (p : ℤ) ∣ coeff d (Delta n) := by
      intro d hdmem hdcount
      by_contra hndvd
      have hd0 : d 0 = 0 := apply_zero_eq_zero_of_mem_support_Delta n d hdmem
      have hdmap : d ∈ (MvPolynomial.map (Int.castRingHom (ZMod p)) (Delta n)).support :=
        (mem_support_map_iff d).mpr hndvd
      have hge := hWOrder.1 d hdmap
      rw [wDeg_nontrivialWeight_eq d hd0] at hge
      omega
    have hpdvd : (p : ℕ) ∣ Dgcd (Delta n) s := by
      unfold Dgcd
      apply Finset.dvd_gcd
      intro d hd
      rw [Finset.mem_filter] at hd
      have h1 := hall d hd.1 hd.2
      have h2 := Int.natAbs_dvd_natAbs.mpr h1
      rwa [Int.natAbs_natCast] at h2
    have h1le : 1 ≤ (Dgcd (Delta n) s).factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hp hDsne).mp hpdvd
    omega

#print axioms FmZ_zero
#print axioms Dc_r_lt_two_eq_r1
#print axioms exists_MinDeg_Dc_general
#print axioms WOrder_Delta_map_full
#print axioms complete_prime_local_case_iii_depth_full

end CongruenceTheory
