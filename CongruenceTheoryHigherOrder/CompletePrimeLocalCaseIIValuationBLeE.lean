import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.CompletePrimeLocalCaseII
import CongruenceTheoryHigherOrder.AlamPairMergeCount
import CongruenceTheoryHigherOrder.TranspositionCoefficientDelta
import CongruenceTheoryHigherOrder.TranspositionCoefficientClosedForm

/-!
**`thm:complete-prime-local`(ii), valuation formula, the `b\le E` (tie) branch.** Unlike the
`E\ne b` branches, coefficient domination through `cont`/`Delta_cons_eq` alone cannot separate the
two terms since both have the *same* `p`-adic valuation `b`. Following the manuscript, we instead
pin down the exact value of a *single* coefficient — the transposition coefficient
`aB+p^2A_2` (`A_2:=\sum_{i<j}u_iu_j=` `Alam u lam` at the pair-merge shape,
`AlamPairMergeCount.Alam_pairMergeShape_eq`) — using `E\le1+v_p(A_2)` (an instance of
`thm:common-prime-classification`'s valuation formula at the pair-merge shape) to show this single
coefficient already has valuation exactly `b`, forcing `\operatorname{cont}` to be sharp there too.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`\text{natCrossSum}` scales quadratically.** -/
theorem natCrossSum_smul {r : ℕ} (c : ℕ) (n : Fin r → ℕ) :
    natCrossSum (fun i => c * n i) = c ^ 2 * natCrossSum n := by
  unfold natCrossSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · rw [if_pos hij, if_pos hij]; ring
  · rw [if_neg hij, if_neg hij, mul_zero]

/-- **`\text{pairSum}` scales quadratically.** -/
theorem pairSum_smul {r : ℕ} (c : ℕ) (n : Fin r → ℕ) :
    pairSum (fun i => c * n i) = (c : ℤ) ^ 2 * pairSum n := by
  rw [pairSum_eq_natCrossSum, pairSum_eq_natCrossSum, natCrossSum_smul]
  push_cast
  ring

/-- **A tuple with nonzero defect has at least two blocks.** -/
theorem two_le_of_Delta_ne_zero {t : ℕ} (n : Fin t → ℕ) (h : Delta n ≠ 0) : 2 ≤ t := by
  match t with
  | 0 => exact absurd (by unfold Delta; simp [C_zero_eq_one]) h
  | 1 => exact absurd (Delta_eq_zero_of_one n) h
  | (t + 2) => omega

/-- **`W_p` at the pair-merge shape is `v_p(A_\lambda(\mathbf u))+1`.** -/
theorem Wp_pairMergeShape_eq {r : ℕ} (u : Fin r → ℕ) (p : ℕ) :
    Wp u p ({2} + Multiset.replicate (Fintype.card (MicroIdx u) - 2) 1) =
      (Alam u ({2} + Multiset.replicate (Fintype.card (MicroIdx u) - 2) 1)).factorization p
        + 1 := by
  unfold Wp
  congr 1
  rw [Multiset.map_add, Multiset.sum_add]
  have h2 : (Multiset.map (firstPrimeLayerExponent p) {2}).sum = 1 := by
    simp [firstPrimeLayerExponent]
  have h1 : (Multiset.map (firstPrimeLayerExponent p)
      (Multiset.replicate (Fintype.card (MicroIdx u) - 2) 1)).sum = 0 := by
    rw [Multiset.map_replicate, Multiset.sum_replicate, firstPrimeLayerExponent]
    simp
  rw [h2, h1]

/-- **The pair-merge shape is achieved** whenever there are at least two macroblocks. -/
theorem mem_image_pairMergeShape {r : ℕ} (u : Fin r → ℕ) (hu : ∀ i, 0 < u i) (hr2 : 2 ≤ r) :
    ({2} + Multiset.replicate (Fintype.card (MicroIdx u) - 2) 1) ∈
      (nonRefiningPartitions u).image GenPartLatShape := by
  have h01 : (⟨0, by omega⟩ : Fin r) ≠ (⟨1, by omega⟩ : Fin r) := by
    simp [Fin.ext_iff]
  set x : MicroIdx u := ⟨⟨0, by omega⟩, ⟨0, hu ⟨0, by omega⟩⟩⟩ with hxdef
  set y : MicroIdx u := ⟨⟨1, by omega⟩, ⟨0, hu ⟨1, by omega⟩⟩⟩ with hydef
  have hxy : x ≠ y := by
    intro h
    exact h01 (congrArg Sigma.fst h)
  have hxy1 : x.1 ≠ y.1 := h01
  apply Finset.mem_image.mpr
  refine ⟨mergePair u hxy, ?_, shape_mergePair u hxy⟩
  rw [mergePair_mem_nonRefiningPartitions_iff]
  exact hxy1

/-- **`E \le W_p(\lambda;\mathbf u)` for any achieved shape `\lambda`**, where `E` is the
`p`-adic valuation of `\operatorname{cont}\Delta_{p\mathbf u}`. -/
theorem E_le_Wp_of_mem {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ) (hu : ∀ i, 0 < u i)
    {p : ℕ} (hp : p.Prime) {E : ℕ}
    (hE : (cont (Delta (fun i => p * u i))).factorization p = E)
    (hmne : Delta (fun i => p * u i) ≠ 0)
    {lam : Multiset ℕ} (hlam : lam ∈ (nonRefiningPartitions u).image GenPartLatShape) :
    E ≤ Wp u p lam := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hne : ((nonRefiningPartitions u).image GenPartLatShape).Nonempty := ⟨lam, hlam⟩
  obtain ⟨hall, d0, hd0⟩ := complete_prime_local_case_i (p := p) hr u hu hne
  set E' := ((((nonRefiningPartitions u).image GenPartLatShape).image (Wp u p)).min'
    (hne.image _)) with hE'def
  have hcontne : cont (Delta (fun i => p * u i)) ≠ 0 := by
    intro h0
    apply hd0
    have hzero : Delta (fun i => p * u i) = 0 := by
      by_contra hne'
      exact (cont_ne_zero_of_ne_zero hne') h0
    rw [hzero, coeff_zero]
    exact dvd_zero _
  have hge : E' ≤ (cont (Delta (fun i => p * u i))).factorization p := by
    have hdvd : p ^ E' ∣ cont (Delta (fun i => p * u i)) := by
      unfold cont
      apply Finset.dvd_gcd
      intro d _
      have h2 := Int.natAbs_dvd_natAbs.mpr (hall d)
      rwa [Int.natAbs_pow, Int.natAbs_natCast] at h2
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp hcontne).mp hdvd
  have hle : (cont (Delta (fun i => p * u i))).factorization p ≤ E' := by
    by_contra hcon
    push_neg at hcon
    apply hd0
    exact dvd_coeff_of_factorization_cont_le (k := E' + 1) (by omega) d0
  have hEeq : E = E' := by omega
  rw [hEeq]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hlam)

/-- **`thm:complete-prime-local`(ii), valuation formula, the `b\le E` (tie) branch.** For
`p\nmid a`, `\mathbf m=(pu_1,\ldots,pu_t)`, `b:=v_p(B)\le E:=v_p(\operatorname{cont}\Delta_{\mathbf
m})`: `v_p(\operatorname{cont}\Delta_{a,\mathbf m})=b` exactly. -/
theorem complete_prime_local_case_ii_valuation_b_le_E {t : ℕ} {a : ℕ} (u : Fin t → ℕ)
    (hu : ∀ i, 0 < u i) {p : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (ha1 : 1 ≤ a)
    {E : ℕ} (hE : (cont (Delta (fun i => p * u i))).factorization p = E)
    (hmne : Delta (fun i => p * u i) ≠ 0)
    (hb : padicValNat p (∑ i, p * u i) ≤ E) :
    (cont (Delta (Fin.cons a (fun i => p * u i) : Fin (t + 1) → ℕ))).factorization p =
      padicValNat p (∑ i, p * u i) := by
  set m : Fin t → ℕ := fun i => p * u i with hmdef
  set U : ℕ := ∑ i, u i with hUdef
  set B : ℕ := ∑ i, m i with hBdef
  set b : ℕ := padicValNat p B with hbdef
  have ht2 : 2 ≤ t := two_le_of_Delta_ne_zero m hmne
  have htpos : 0 < t := by omega
  have hUpos : 0 < U := by
    rw [hUdef]
    obtain ⟨i0⟩ : Nonempty (Fin t) := ⟨⟨0, htpos⟩⟩
    calc 0 < u i0 := hu i0
      _ ≤ ∑ i, u i := Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ i0)
  have hBeq : B = p * U := by
    rw [hBdef, hUdef, hmdef, Finset.mul_sum]
  have hbeq : b = 1 + U.factorization p := by
    rw [hbdef, ← Nat.factorization_def B hp, hBeq,
      Nat.factorization_mul (Nat.Prime.ne_zero hp) (by omega), Finsupp.coe_add, Pi.add_apply,
      Nat.Prime.factorization_self hp]
  set lam : Multiset ℕ := {2} + Multiset.replicate (Fintype.card (MicroIdx u) - 2) 1 with hlamdef
  have hlammem : lam ∈ (nonRefiningPartitions u).image GenPartLatShape :=
    mem_image_pairMergeShape u hu ht2
  have hEleWp : E ≤ Wp u p lam := E_le_Wp_of_mem htpos u hu hp hE hmne hlammem
  rw [Wp_pairMergeShape_eq, ← hlamdef] at hEleWp
  have hA2val : U.factorization p ≤ (Alam u lam).factorization p := by omega
  -- the transposition coefficient of the full defect
  have hm2 : ∀ i, 2 ≤ m i := fun i => by
    rw [hmdef]; dsimp only
    calc 2 ≤ p := hp.two_le
      _ ≤ p * u i := Nat.le_mul_of_pos_right p (hu i)
  have hB2 : 2 ≤ B := by
    rw [hBeq]; calc 2 ≤ p := hp.two_le
      _ ≤ p * U := Nat.le_mul_of_pos_right p hUpos
  have htrans : coeff (ciExp ((a + B) - 2) {2})
      (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) = (a : ℤ) * (B : ℤ) + pairSum m := by
    rw [coeff_transposition_cons a m hB2]
    congr 1
    · rw [hBdef]; push_cast; ring
    · exact coeff_transposition_eq_pairSum m hm2
  have hpairSumm : pairSum m = (p : ℤ) ^ 2 * (Alam u lam : ℤ) := by
    rw [hmdef, pairSum_smul, Alam_pairMergeShape_eq]
  set d0 : ℕ →₀ ℕ := ciExp ((a + B) - 2) {2} with hd0def
  have hcoeffd0 : coeff d0 (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) =
      (a : ℤ) * (B : ℤ) + (p : ℤ) ^ 2 * (Alam u lam : ℤ) := by
    rw [hd0def, htrans, hpairSumm]
  -- upper bound: p^{b+1} does not divide this coefficient
  have hnotdvd_aB : ¬ (p : ℕ) ^ (b + 1) ∣ a * B := by
    intro hdvd
    have hane : a ≠ 0 := by omega
    have hBne : B ≠ 0 := by omega
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization hp (Nat.mul_ne_zero hane hBne)).mp hdvd
    rw [Nat.factorization_mul hane hBne, Finsupp.coe_add, Pi.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpa] at h1
    have hBfact : B.factorization p = b := (Nat.factorization_def B hp).trans hbdef.symm
    omega
  have hdvd_p2A2 : (p : ℕ) ^ (b + 1) ∣ p ^ 2 * (Alam u lam) := by
    have h1 : p ^ (b - 1) ∣ Alam u lam := by
      rcases Nat.eq_zero_or_pos (Alam u lam) with h0 | h0
      · rw [h0]; exact dvd_zero _
      · exact (pow_dvd_pow p (by omega : b - 1 ≤ (Alam u lam).factorization p)).trans
          (Nat.ordProj_dvd (Alam u lam) p)
    have h2 : p ^ (b + 1) = p ^ 2 * p ^ (b - 1) := by
      rw [← pow_add]; congr 1; omega
    rw [h2]
    exact mul_dvd_mul_left _ h1
  have hupper : ¬ (p : ℤ) ^ (b + 1) ∣ coeff d0 (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) := by
    rw [hcoeffd0]
    intro hcon
    apply hnotdvd_aB
    have hdvd2 : (p : ℤ) ^ (b + 1) ∣ (p : ℤ) ^ 2 * (Alam u lam : ℤ) := by
      exact_mod_cast hdvd_p2A2
    have hdvd1 : (p : ℤ) ^ (b + 1) ∣ (a : ℤ) * (B : ℤ) := by
      have := dvd_sub hcon hdvd2
      simpa using this
    exact_mod_cast hdvd1
  -- lower bound: p^b divides every coefficient
  have hEb : b ≤ E := hb
  have hcontCa := cont_C_eq_one a
  have hCamapne : MvPolynomial.map (Int.castRingHom (ZMod p)) (C a) ≠ 0 := by
    intro h0
    have hdvd := (map_eq_zero_iff_dvd_cont hp (C a)).mp h0
    rw [hcontCa] at hdvd
    exact (Nat.Prime.one_lt hp).ne' (Nat.dvd_one.mp hdvd)
  have hterm2fact : (cont (C a * Delta m)).factorization p = E :=
    factorization_cont_mul_of_map_ne_zero hp hCamapne E (Delta m) hE hmne
  have hterm1fact : (cont (C (a + B) - C a * C B)).factorization p = b :=
    padicValNat_cont_two_term_of_not_dvd_left hp ha1 (by omega) hpa
  have hlower : ∀ d, (p : ℤ) ^ b ∣
      coeff d ((C (a + B) - C a * C B) + C a * Delta m) := by
    intro d
    rw [coeff_add]
    exact dvd_add
      (dvd_coeff_of_factorization_cont_le (φ := C (a + B) - C a * C B) (k := b)
        (by rw [hterm1fact]) d)
      (dvd_coeff_of_factorization_cont_le (φ := C a * Delta m) (k := b)
        (by rw [hterm2fact]; omega) d)
  have hcontne : cont (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) ≠ 0 := by
    intro h0
    apply hupper
    have hzero : Delta (Fin.cons a m : Fin (t + 1) → ℕ) = 0 := by
      by_contra hne'
      exact (cont_ne_zero_of_ne_zero hne') h0
    rw [hzero, coeff_zero]
    exact dvd_zero _
  have hge : b ≤ (cont (Delta (Fin.cons a m : Fin (t + 1) → ℕ))).factorization p := by
    have hdvd : p ^ b ∣ cont (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) := by
      unfold cont
      apply Finset.dvd_gcd
      intro d _
      have h1 : (p : ℤ) ^ b ∣ coeff d (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) := by
        rw [Delta_cons_eq]; exact hlower d
      have h2 := Int.natAbs_dvd_natAbs.mpr h1
      rwa [Int.natAbs_pow, Int.natAbs_natCast] at h2
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp hcontne).mp hdvd
  have hle : (cont (Delta (Fin.cons a m : Fin (t + 1) → ℕ))).factorization p ≤ b := by
    by_contra hcon
    push_neg at hcon
    have hd0eq : (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) =
        (C (a + B) - C a * C B) + C a * Delta m := Delta_cons_eq a m
    rw [hd0eq] at hcon
    apply hupper
    rw [hd0eq]
    exact dvd_coeff_of_factorization_cont_le (k := b + 1) (by omega) d0
  omega

#print axioms natCrossSum_smul
#print axioms pairSum_smul
#print axioms two_le_of_Delta_ne_zero
#print axioms Wp_pairMergeShape_eq
#print axioms mem_image_pairMergeShape
#print axioms E_le_Wp_of_mem
#print axioms complete_prime_local_case_ii_valuation_b_le_E

end CongruenceTheory
