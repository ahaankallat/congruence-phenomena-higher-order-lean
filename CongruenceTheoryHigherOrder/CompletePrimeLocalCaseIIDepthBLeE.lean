import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.CompletePrimeLocalCaseIIValuationBLeE

/-!
**`thm:complete-prime-local`(ii), depth formula, the `b\le E` branch.** `\delta_p(a,\mathbf m)=1`:
the transposition coefficient `d_0:=\text{ciExp}((a+B)-2)\{2\}` has `\text{nontrivialPartCount}
\,d_0=1`, so it lies in the domain of `D_1`, and its exact `p`-adic valuation `b` (already pinned
down in `CompletePrimeLocalCaseIIValuationBLeE`) forces `D_1`'s own valuation to be `b` as well —
matching `\operatorname{cont}`'s valuation exactly at `s=1`, the least possible witness depth.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **The transposition coefficient's monomial has `\text{nontrivialPartCount}=1`.** -/
theorem nontrivialPartCount_transposition_monomial (N : ℕ) :
    nontrivialPartCount (ciExp (N - 2) {2}) = 1 := by
  rw [nontrivialPartCount_ciExp (N - 2) {2} (by intro x hx; simp at hx; omega)]
  simp

/-- **`thm:complete-prime-local`(ii), depth formula, the `b\le E` branch.** For `p\nmid a`,
`\mathbf m=(pu_1,\ldots,pu_t)`, `b:=v_p(B)\le E:=v_p(\operatorname{cont}\Delta_{\mathbf m})`:
`\delta_p(a,\mathbf m)=1`, i.e. `1` is the least `s\ge1` with `(D_s(\Delta_{a,\mathbf
m})).factorization\,p=b`. -/
theorem complete_prime_local_case_ii_depth_b_le_E {t : ℕ} {a : ℕ} (u : Fin t → ℕ)
    (hu : ∀ i, 0 < u i) {p : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (ha1 : 1 ≤ a)
    {E : ℕ} (hE : (cont (Delta (fun i => p * u i))).factorization p = E)
    (hmne : Delta (fun i => p * u i) ≠ 0)
    (hb : padicValNat p (∑ i, p * u i) ≤ E) :
    IsLeast {s : ℕ | 1 ≤ s ∧
        (Dgcd (Delta (Fin.cons a (fun i => p * u i) : Fin (t + 1) → ℕ)) s).factorization p =
          padicValNat p (∑ i, p * u i)} 1 := by
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
  have hBeq : B = p * U := by rw [hBdef, hUdef, hmdef, Finset.mul_sum]
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
  have hcontfact : (cont (Delta (Fin.cons a m : Fin (t + 1) → ℕ))).factorization p = b :=
    complete_prime_local_case_ii_valuation_b_le_E u hu hp hpa ha1 hE hmne hb
  have hd0mem : nontrivialPartCount d0 ≤ 1 := by
    rw [hd0def, nontrivialPartCount_transposition_monomial]
  have hd0ne : coeff d0 (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) ≠ 0 := by
    intro h0; apply hupper; rw [h0]; exact dvd_zero _
  have hd0supp : d0 ∈ (Delta (Fin.cons a m : Fin (t + 1) → ℕ)).support := mem_support_iff.mpr hd0ne
  have hDgcd1dvd : Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) 1 ∣
      (coeff d0 (Delta (Fin.cons a m : Fin (t + 1) → ℕ))).natAbs := by
    apply Finset.gcd_dvd
    rw [Finset.mem_filter]
    exact ⟨hd0supp, hd0mem⟩
  have hcontne : cont (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) ≠ 0 := by
    intro h0
    apply hupper
    have hzero : Delta (Fin.cons a m : Fin (t + 1) → ℕ) = 0 := by
      by_contra hne'
      exact (cont_ne_zero_of_ne_zero hne') h0
    rw [hzero, coeff_zero]
    exact dvd_zero _
  have hDgcd1ne : Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) 1 ≠ 0 := by
    intro h0
    apply hd0ne
    rw [h0] at hDgcd1dvd
    have hnat0 := Nat.eq_zero_of_zero_dvd hDgcd1dvd
    exact Int.natAbs_eq_zero.mp hnat0
  have hle1 : (Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) 1).factorization p ≤ b := by
    by_contra hcon
    push_neg at hcon
    apply hupper
    have hpdvd : p ^ (b + 1) ∣ Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) 1 :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hDgcd1ne).mpr (by omega)
    have hpdvd2 : p ^ (b + 1) ∣ (coeff d0 (Delta (Fin.cons a m : Fin (t + 1) → ℕ))).natAbs :=
      hpdvd.trans hDgcd1dvd
    have h3 := Int.natCast_dvd_natCast.mpr hpdvd2
    rw [Int.natCast_pow, Int.dvd_natAbs] at h3
    exact_mod_cast h3
  have hge1 : b ≤ (Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) 1).factorization p := by
    have hdvd := cont_dvd_Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) 1
    have h1 := (Nat.factorization_le_iff_dvd hcontne hDgcd1ne).mpr hdvd
    have h2 := h1 p
    omega
  have hfinal : (Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) 1).factorization p = b := by omega
  exact ⟨⟨le_refl 1, hfinal⟩, fun s hs => hs.1⟩

#print axioms nontrivialPartCount_transposition_monomial
#print axioms complete_prime_local_case_ii_depth_b_le_E

end CongruenceTheory
