import Mathlib
import CongruenceTheoryHigherOrder.DefectValuationExactWeight
import CongruenceTheoryHigherOrder.AlamPairMergeCount
import CongruenceTheoryHigherOrder.InequalityA1Content
import CongruenceTheoryHigherOrder.TwoTermDefectValuation
import CongruenceTheoryHigherOrder.CommonPrimeClassificationDepth

/-!
**The lifting theorem at every prime** (Part I, `thm:strong-all-primes`).  For a prime `p` and
`k > 0` with `p ∣ k`, every coefficient of `C_{pk} - C_k^p` is divisible by `p^(2 v_p(k))` if `p`
is odd and by `p^(2 v_p(k) - 1)` if `p = 2`.

*Proof structure (formalized).*  Apply the moment-cumulant expansion `defect_eq_sum_Alam_smul`
to `p` blocks of size `k` (all `u_i = 1`), so that the defect is
`∑_λ A_λ • ∏_{j ∈ λ} K_j(k)` over the shapes `λ` of non-discrete partitions of `p` points.
Each connected cumulant `K_j(k)` has coefficients divisible by `k^(j-1)` for `j ≥ 3`
(`content_dvd_K`) and by `treeM k k = k^2/rad(k)` for `j = 2` (`K_two` and `treeM_dvd_cont`).
Then: a shape with a part of size `≥ 3` contributes `p^(2 v_p(k))`; a shape with `t ≥ 2` pairs
contributes `p^(t (2 v_p(k) - 1))`; the shape with exactly one pair occurs `A_λ = C(p,2) = p(p-1)/2`
times (`Alam_pairMergeShape_eq`), which is divisible by `p` exactly when `p` is odd, giving
`p^(2 v_p(k))` for odd `p` and `p^(2 v_p(k) - 1)` for `p = 2`.
-/

namespace CongruenceTheory
open MvPolynomial
open scoped Classical

theorem partLat_two_cases : ∀ π : PartLat 2, π = ⊥ ∨ π = ⊤ := by decide
theorem partLat_two_bot_ne_top : (⊥ : PartLat 2) ≠ ⊤ := by decide
theorem partLat_two_top_parts : (⊤ : PartLat 2).parts = {Finset.univ} := by decide

theorem mu_bot_top_two : IncidenceAlgebra.mu ℤ (⊥ : PartLat 2) ⊤ = -1 := by
  have h := IncidenceAlgebra.sum_Icc_mu_left (𝕜 := ℤ) (⊥ : PartLat 2) ⊤
  rw [if_neg partLat_two_bot_ne_top] at h
  have hIcc : Finset.Icc (⊥ : PartLat 2) ⊤ = {⊥, ⊤} := by
    ext π
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro _; exact partLat_two_cases π
    · rintro (rfl | rfl) <;> simp
  rw [hIcc, Finset.sum_pair partLat_two_bot_ne_top, IncidenceAlgebra.mu_self] at h
  linarith

/-- `K_2(q) = C_{2q} - C_q^2`. -/
theorem K_two (q : ℕ) : K 2 q = C (2 * q) - C q ^ 2 := by
  unfold K
  have huniv : (Finset.univ : Finset (PartLat 2)) = {⊥, ⊤} := by
    ext π
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact partLat_two_cases π
  rw [huniv, Finset.sum_pair partLat_two_bot_ne_top, mu_bot_top_two, IncidenceAlgebra.mu_self,
    partLat_two_top_parts, Finpartition.parts_bot, Finset.prod_map, Finset.prod_singleton]
  simp only [Function.Embedding.coeFn_mk, Finset.card_singleton, one_mul, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [neg_smul, one_smul, one_smul]
  ring

/-- Coefficientwise divisibility is preserved by multiplication on the right. -/
theorem dvd_coeff_mul_of_left {m : ℤ} {P : MvPolynomial ℕ ℤ} (Q : MvPolynomial ℕ ℤ)
    (h : ∀ d, m ∣ coeff d P) : ∀ d, m ∣ coeff d (P * Q) := by
  intro d
  have hP : MvPolynomial.C m ∣ P := (MvPolynomial.C_dvd_iff_dvd_coeff m P).mpr h
  exact (MvPolynomial.C_dvd_iff_dvd_coeff m _).mp (dvd_mul_of_dvd_left hP Q) d

/-- Divisibilities of coefficients multiply. -/
theorem dvd_coeff_mul_of_both {m n : ℤ} {P Q : MvPolynomial ℕ ℤ}
    (hP : ∀ d, m ∣ coeff d P) (hQ : ∀ d, n ∣ coeff d Q) : ∀ d, m * n ∣ coeff d (P * Q) := by
  intro d
  have hP' : MvPolynomial.C m ∣ P := (MvPolynomial.C_dvd_iff_dvd_coeff m P).mpr hP
  have hQ' : MvPolynomial.C n ∣ Q := (MvPolynomial.C_dvd_iff_dvd_coeff n Q).mpr hQ
  have := mul_dvd_mul hP' hQ'
  rw [← map_mul] at this
  exact (MvPolynomial.C_dvd_iff_dvd_coeff (m * n) _).mp this d

/-- A divisor of the content divides every coefficient. -/
theorem dvd_coeff_of_dvd_cont {n : ℕ} {P : MvPolynomial ℕ ℤ} (h : n ∣ cont P) (d : ℕ →₀ ℕ) :
    (n : ℤ) ∣ coeff d P := by
  by_cases hd : coeff d P = 0
  · simp [hd]
  · have hmem : d ∈ P.support := mem_support_iff.mpr hd
    have : cont P ∣ (coeff d P).natAbs := Finset.gcd_dvd hmem
    exact Int.natCast_dvd.mpr (h.trans this)

/-- Product over a multiset of coefficientwise-divisible polynomials. -/
theorem dvd_coeff_prod_map (m : ℕ → ℕ) (f : ℕ → MvPolynomial ℕ ℤ) (lam : Multiset ℕ)
    (h : ∀ j ∈ lam, ∀ d, (m j : ℤ) ∣ coeff d (f j)) :
    ∀ d, (((lam.map m).prod : ℕ) : ℤ) ∣ coeff d ((lam.map f).prod) := by
  induction lam using Multiset.induction_on with
  | empty =>
    intro d
    simp only [Multiset.map_zero, Multiset.prod_zero, Nat.cast_one, one_dvd]
  | cons a s ih =>
    intro d
    have ha : ∀ d, (m a : ℤ) ∣ coeff d (f a) := h a (Multiset.mem_cons_self a s)
    have hs : ∀ d, (((s.map m).prod : ℕ) : ℤ) ∣ coeff d ((s.map f).prod) :=
      ih (fun j hj => h j (Multiset.mem_cons_of_mem hj))
    have := dvd_coeff_mul_of_both ha hs d
    simpa [Multiset.map_cons, Multiset.prod_cons, Nat.cast_mul] using this

/-- Divisibility of the coefficients of `K_j(k)`: `1` for `j = 1`, `treeM k k` for `j = 2`,
`k^(j-1)` for `j ≥ 3`. -/
noncomputable def Kdiv (k j : ℕ) : ℕ := if j = 1 then 1 else if j = 2 then treeM k k else k ^ (j - 1)

theorem dvd_coeff_K_Kdiv {k : ℕ} (hk : 2 ≤ k) {j : ℕ} (hj : 1 ≤ j) :
    ∀ d, (Kdiv k j : ℤ) ∣ coeff d (K j k) := by
  intro d
  unfold Kdiv
  by_cases h1 : j = 1
  · simp [h1]
  · rw [if_neg h1]
    by_cases h2 : j = 2
    · rw [if_pos h2, h2, K_two]
      have h := treeM_dvd_cont k k (by omega) (by omega)
      have h' := dvd_coeff_of_dvd_cont h d
      have e : C (2 * k) - C k ^ 2 = C (k + k) - C k * C k := by rw [two_mul, sq]
      rw [e]
      exact h'
    · rw [if_neg h2]
      haveI : NeZero j := ⟨by omega⟩
      haveI : NeZero k := ⟨by omega⟩
      have h := content_dvd_K (r := j) (q := k) hk
      have h2' : k ^ (j - 1) ∣ cont (K j k) :=
        (Dvd.intro_left _ rfl : k ^ (j - 1) ∣ (j - 1).factorial * k ^ (j - 1)).trans h
      have := dvd_coeff_of_dvd_cont h2' d
      simpa using this


/-- `pairSum` of the all-ones tuple: `2 * pairSum = r (r - 1)`. -/
theorem pairSum_one_two_mul : ∀ r : ℕ,
    2 * pairSum (fun _ : Fin r => (1 : ℕ)) = (r : ℤ) * ((r : ℤ) - 1)
  | 0 => by simp [pairSum]
  | t + 1 => by
    have h := pairSum_one_two_mul t
    have e : pairSum (fun _ : Fin (t + 1) => (1 : ℕ)) = (t : ℤ) + pairSum (fun _ : Fin t => (1 : ℕ)) := by
      simp [pairSum]
      rfl
    rw [e]
    push_cast
    nlinarith [h]

/-- **The lifting theorem at every prime.** For a prime `p` and `k > 0` with `p ∣ k`, every
coefficient of `C_{pk} - C_k^p` is divisible by `p^(2 v_p(k))` if `p` is odd and by
`p^(2 v_p(k) - 1)` if `p = 2`. -/
theorem lift_all_primes {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hpk : p ∣ k) (d : ℕ →₀ ℕ) :
    (p : ℤ) ^ (if p = 2 then 2 * k.factorization p - 1 else 2 * k.factorization p) ∣
      coeff d (C (p * k) - C k ^ p) := by
  have hk2 : 2 ≤ k := le_trans hp.two_le (Nat.le_of_dvd hk hpk)
  set s := k.factorization p with hs_def
  have hs1 : 1 ≤ s := (hp.dvd_iff_one_le_factorization hk.ne').mp hpk
  have hpsk : p ^ s ∣ k := Nat.ordProj_dvd k p
  set E := (if p = 2 then 2 * s - 1 else 2 * s) with hE
  have hE2s : E ≤ 2 * s := by rw [hE]; split_ifs <;> omega
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let u : Fin p → ℕ := fun _ => 1
  have hexp := defect_eq_sum_Alam_smul (r := p) hp.pos u (fun _ => one_pos) k
  have hlhs : C ((∑ i, u i) * k) - ∏ i, C (u i * k) = C (p * k) - C k ^ p := by
    simp [u]
  rw [hlhs] at hexp
  rw [hexp, coeff_sum]
  apply Finset.dvd_sum
  intro lam hlam
  obtain ⟨π, hπmem, hπeq⟩ := Finset.mem_image.mp hlam
  have hge1 : ∀ j ∈ lam, 1 ≤ j := by
    intro j hj
    rw [← hπeq] at hj
    obtain ⟨B, hB, hBj⟩ := Multiset.mem_map.mp hj
    have := Finset.card_pos.mpr (π.nonempty_of_mem_parts hB)
    omega
  have hcard : Fintype.card (MicroIdx u) = p := by
    rw [card_microIdx]; simp [u]
  have hsum : lam.sum = p := by
    rw [← hπeq]
    unfold GenPartLatShape
    have h1 : ((π.parts.val.map Finset.card).sum) = ∑ B ∈ π.parts, B.card := rfl
    rw [h1, Finpartition.sum_card_parts, Finset.card_univ, hcard]
  have hone : 1 ≤ (lam.filter (2 ≤ ·)).card := one_le_card_filter_of_mem_image u hlam
  rw [coeff_smul, nsmul_eq_mul]
  have hprod : (((lam.map (Kdiv k)).prod : ℕ) : ℤ) ∣ coeff d ((lam.map (fun j => K j k)).prod) :=
    dvd_coeff_prod_map (Kdiv k) (fun j => K j k) lam
      (fun j hj => dvd_coeff_K_Kdiv hk2 (hge1 j hj)) d
  refine dvd_trans ?_ (mul_dvd_mul_left (Alam u lam : ℤ) hprod)
  have hnat : p ^ E ∣ Alam u lam * (lam.map (Kdiv k)).prod := by
    by_cases h3 : ∃ j ∈ lam, 3 ≤ j
    · obtain ⟨j, hj, hj3⟩ := h3
      have hjd : Kdiv k j ∣ (lam.map (Kdiv k)).prod :=
        Multiset.dvd_prod (Multiset.mem_map_of_mem _ hj)
      have hKj : Kdiv k j = k ^ (j - 1) := by
        unfold Kdiv
        rw [if_neg (by omega), if_neg (by omega)]
      have hj1 : 2 ≤ j - 1 := by omega
      have hsj : 2 * s ≤ s * (j - 1) := by
        have := Nat.mul_le_mul_left s hj1
        omega
      have hpow : p ^ E ∣ k ^ (j - 1) := by
        calc p ^ E ∣ p ^ (s * (j - 1)) := pow_dvd_pow p (by omega)
          _ = (p ^ s) ^ (j - 1) := pow_mul p s (j - 1)
          _ ∣ k ^ (j - 1) := pow_dvd_pow_of_dvd hpsk _
      exact Dvd.dvd.mul_left (hpow.trans (hKj ▸ hjd)) _
    · simp only [not_exists, not_and, not_le] at h3
      set t := (lam.filter (2 ≤ ·)).card with ht
      have h2parts : lam.filter (2 ≤ ·) = Multiset.replicate t 2 := by
        rw [Multiset.eq_replicate]
        refine ⟨rfl, fun b hb => ?_⟩
        obtain ⟨hbmem, hb2⟩ := Multiset.mem_filter.mp hb
        have := h3 b hbmem
        omega
      set c := (lam.filter (fun j => ¬ 2 ≤ j)).card with hc
      have h1parts : lam.filter (fun j => ¬ 2 ≤ j) = Multiset.replicate c 1 := by
        rw [Multiset.eq_replicate]
        refine ⟨rfl, fun b hb => ?_⟩
        obtain ⟨hbmem, hb2⟩ := Multiset.mem_filter.mp hb
        have := hge1 b hbmem
        omega
      have hsplit : lam = Multiset.replicate t 2 + Multiset.replicate c 1 := by
        rw [← h2parts, ← h1parts]
        exact (Multiset.filter_add_not (2 ≤ ·) lam).symm
      have hsum2 : 2 * t + c = p := by
        have h := hsum
        rw [hsplit] at h
        simpa [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_comm] using h
      have e2 : Kdiv k 2 = treeM k k := by unfold Kdiv; simp
      have e1 : Kdiv k 1 = 1 := by unfold Kdiv; simp
      have hprodeq : (lam.map (Kdiv k)).prod = (treeM k k) ^ t := by
        rw [hsplit, Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
          Multiset.map_replicate, Multiset.prod_replicate, Multiset.prod_replicate, e2, e1,
          one_pow, mul_one]
      have hM : p ^ (2 * s - 1) ∣ treeM k k := by
        have hne : treeM k k ≠ 0 := treeM_ne_zero k k (by omega) (by omega)
        rw [hp.pow_dvd_iff_le_factorization hne, treeM_factorization k k hk.ne' hk.ne' p hp,
          if_pos (by simpa using hpk)]
        have : padicValNat p k = s := (Nat.factorization_def k hp).symm
        omega
      rw [hprodeq]
      by_cases ht2 : 2 ≤ t
      · have hpt : p ^ E ∣ (treeM k k) ^ t := by
          obtain ⟨a, ha⟩ : ∃ a, 2 * s - 1 = a := ⟨_, rfl⟩
          rw [ha] at hM
          have ha1 : 1 ≤ a := by omega
          have h2a : 2 * s ≤ 2 * a := by omega
          calc p ^ E ∣ p ^ (a * t) := pow_dvd_pow p (by nlinarith)
            _ = (p ^ a) ^ t := pow_mul p a t
            _ ∣ (treeM k k) ^ t := pow_dvd_pow_of_dvd hM t
        exact Dvd.dvd.mul_left hpt _
      · have ht1 : t = 1 := by omega
        have hc' : c = p - 2 := by omega
        have hlam2 : lam = {2} + Multiset.replicate (Fintype.card (MicroIdx u) - 2) 1 := by
          rw [hsplit, ht1, hcard, ← hc', Multiset.replicate_one]
        have hAlam : (Alam u lam : ℤ) = pairSum u := by
          rw [hlam2]; exact Alam_pairMergeShape_eq u
        rw [ht1, pow_one]
        by_cases hp2 : p = 2
        · have hEv : E = 2 * s - 1 := by rw [hE, if_pos hp2]
          rw [hEv]
          exact Dvd.dvd.mul_left hM _
        · have hEv : E = 2 * s := by rw [hE, if_neg hp2]
          have hAp : p ∣ Alam u lam := by
            have h2 : 2 * pairSum u = (p : ℤ) * ((p : ℤ) - 1) := pairSum_one_two_mul p
            have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
            have hdvd : (p : ℤ) ∣ 2 * pairSum u := ⟨(p : ℤ) - 1, h2⟩
            rcases hpZ.dvd_or_dvd hdvd with h | h
            · exfalso
              have h' : p ∣ 2 := by exact_mod_cast h
              exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
            · have h'' : (p : ℤ) ∣ (Alam u lam : ℤ) := hAlam ▸ h
              exact Int.natCast_dvd_natCast.mp h''
          rw [hEv]
          have h2s : 2 * s = (2 * s - 1) + 1 := by omega
          have hpp : p ^ (2 * s) = p * p ^ (2 * s - 1) := by
            conv_lhs => rw [h2s]
            exact pow_succ' p (2 * s - 1)
          rw [hpp]
          exact mul_dvd_mul hAp hM
  have hfin := Int.natCast_dvd_natCast.mpr hnat
  rw [Nat.cast_mul, Nat.cast_pow] at hfin
  exact hfin

#print axioms K_two
#print axioms lift_all_primes

end CongruenceTheory
