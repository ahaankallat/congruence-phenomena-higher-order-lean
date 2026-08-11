import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.CompletePrimeLocalCaseIIValuationBLeE
import CongruenceTheoryHigherOrder.CompletePrimeLocalCaseIIDepthBLeE
import CongruenceTheoryHigherOrder.TranspositionCoefficientDelta

/-!
**`thm:complete-prime-local`(ii), depth formula, the `E<b` branch.** `\delta_p(a,\mathbf m)=d:=
\delta_p(\mathbf m)`. Writing `C_a=X_1^a+R_a` (`R_a` collects every cycle-index term of `a` with
at least one nontrivial cycle), `\Delta_{a,\mathbf m}=\text{term}_1+X_1^a\Delta_{\mathbf
m}+R_a\Delta_{\mathbf m}`: `\text{term}_1` is entirely divisible by `p^{E+1}` (`E<b`), the `X_1^a`
piece exactly *shifts* every coefficient of `\Delta_{\mathbf m}$ (no contamination, monomial
multiplication), and `R_a\Delta_{\mathbf m}$'s coefficient at any monomial with `\le s` nontrivial
parts is a combination of `\Delta_{\mathbf m}$'s coefficients at *strictly fewer* than `s`
nontrivial parts (since every term of `R_a` itself has `\ge1`), hence divisible by `p^{E+1}`
whenever `s<d` by `\mathbf m`'s own minimality. Together these transport `\mathbf m`'s witness
depth `d` exactly to `\Delta_{a,\mathbf m}`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`C_n`'s support avoids position `0`.** -/
theorem apply_zero_eq_zero_of_coeff_C_ne_zero {n : ℕ} {d : ℕ →₀ ℕ} (hd : coeff d (C n) ≠ 0) :
    d 0 = 0 := by
  rw [← K_one] at hd
  exact apply_zero_eq_zero_of_coeff_K_ne_zero hd

/-- **`\Delta_{\mathbf n}` is weighted homogeneous of weighted degree `0`** with respect to the
"position-`0`" weight — i.e. its support avoids position `0`. -/
theorem isWeightedHomogeneous_Delta_zero {r : ℕ} (n : Fin r → ℕ) :
    IsWeightedHomogeneous (fun k : ℕ => if k = 0 then (1 : ℕ) else 0) (Delta n) 0 := by
  unfold Delta
  apply IsWeightedHomogeneous.sub
  · have h1 := isWeightedHomogeneous_K_zero 1 (∑ i, n i)
    rwa [K_one] at h1
  · have hprod := IsWeightedHomogeneous.finset_prod (Finset.univ : Finset (Fin r))
      (fun i => C (n i)) (fun _ => 0)
      (fun i _ => by
        have h1 := isWeightedHomogeneous_K_zero 1 (n i)
        rwa [K_one] at h1)
    rwa [Finset.sum_const_zero] at hprod

/-- **`\Delta_{\mathbf n}`'s support avoids position `0`.** -/
theorem apply_zero_eq_zero_of_coeff_Delta_ne_zero {r : ℕ} {n : Fin r → ℕ} {d : ℕ →₀ ℕ}
    (hd : coeff d (Delta n) ≠ 0) : d 0 = 0 := by
  have hz := isWeightedHomogeneous_Delta_zero n hd
  rw [Finsupp.weight_apply, Finsupp.sum] at hz
  simp only [smul_eq_mul] at hz
  by_contra hne
  have h0mem : (0 : ℕ) ∈ d.support := Finsupp.mem_support_iff.mpr hne
  have hall := Finset.sum_eq_zero_iff.mp hz
  have h0 := hall 0 h0mem
  simp at h0
  exact hne h0

/-- **A nonzero-coefficient monomial of `\Delta_{\mathbf n}` with `\text{nontrivialPartCount}=0`
is the all-fixed-points monomial**, forcing the coefficient to vanish
(`coeff_single_one_Delta_eq_zero`). -/
theorem coeff_eq_zero_of_nontrivialPartCount_eq_zero_Delta {r : ℕ} (n : Fin r → ℕ)
    {d : ℕ →₀ ℕ} (hd : nontrivialPartCount d = 0) : coeff d (Delta n) = 0 := by
  by_contra hne
  have hd0 : d 0 = 0 := apply_zero_eq_zero_of_coeff_Delta_ne_zero hne
  have hdall : ∀ k, k ≠ 1 → d k = 0 := by
    intro k hk
    by_cases hk0 : k = 0
    · rw [hk0]; exact hd0
    · exact eq_zero_of_two_le_of_nontrivialPartCount_eq_zero hd k (by omega)
  have hw : Finsupp.weight (fun k : ℕ => k) d = ∑ i, n i := isWeightedHomogeneous_Delta n hne
  have hdeq : d = Finsupp.single 1 (∑ i, n i) :=
    eq_single_one_of_weight_eq_of_forall_ne_one_eq_zero hw hdall
  rw [hdeq] at hne
  exact hne (coeff_single_one_Delta_eq_zero n)

/-- **A nonzero-coefficient monomial of `C_a` with `\text{nontrivialPartCount}=0` is exactly
`X_1^a`.** -/
theorem eq_single_one_of_coeff_C_ne_zero_of_nontrivialPartCount_eq_zero {a : ℕ} {d : ℕ →₀ ℕ}
    (hd : coeff d (C a) ≠ 0) (h0 : nontrivialPartCount d = 0) : d = Finsupp.single 1 a := by
  have hd0 : d 0 = 0 := apply_zero_eq_zero_of_coeff_C_ne_zero hd
  have hdall : ∀ k, k ≠ 1 → d k = 0 := by
    intro k hk
    by_cases hk0 : k = 0
    · rw [hk0]; exact hd0
    · exact eq_zero_of_two_le_of_nontrivialPartCount_eq_zero h0 k (by omega)
  have hw : Finsupp.weight (fun k : ℕ => k) d = a := isWeightedHomogeneous_C a hd
  exact eq_single_one_of_weight_eq_of_forall_ne_one_eq_zero hw hdall

#print axioms apply_zero_eq_zero_of_coeff_C_ne_zero
#print axioms isWeightedHomogeneous_Delta_zero
#print axioms apply_zero_eq_zero_of_coeff_Delta_ne_zero
#print axioms coeff_eq_zero_of_nontrivialPartCount_eq_zero_Delta
#print axioms eq_single_one_of_coeff_C_ne_zero_of_nontrivialPartCount_eq_zero

/-- **Every coefficient of `\Delta_{\mathbf m}` at a monomial with fewer nontrivial parts than
the least witness depth `d` is divisible by `p^{E+1}`.** -/
theorem coeff_Delta_dvd_pow_succ_of_lt_depth {t : ℕ} (m : Fin t → ℕ) {p E : ℕ} (hp : p.Prime)
    (hE : (cont (Delta m)).factorization p = E) (hmne : Delta m ≠ 0)
    {d : ℕ} (hleast : IsLeast {s : ℕ | 1 ≤ s ∧ (Dgcd (Delta m) s).factorization p = E} d)
    {s : ℕ} (hslt : s < d) {e : ℕ →₀ ℕ} (he : nontrivialPartCount e ≤ s) :
    (p : ℤ) ^ (E + 1) ∣ coeff e (Delta m) := by
  rcases Nat.eq_zero_or_pos (nontrivialPartCount e) with h0 | hpos
  · rw [coeff_eq_zero_of_nontrivialPartCount_eq_zero_Delta m h0]
    exact dvd_zero _
  · have hs1 : 1 ≤ s := le_trans hpos he
    by_cases hd0 : e ∈ (Delta m).support
    · have hDsne : Dgcd (Delta m) s ≠ 0 := by
        intro h0'
        have hmemfilt : e ∈ (Delta m).support.filter (fun x => nontrivialPartCount x ≤ s) :=
          Finset.mem_filter.mpr ⟨hd0, he⟩
        unfold Dgcd at h0'
        have := (Finset.gcd_eq_zero_iff).mp h0' e hmemfilt
        exact (mem_support_iff.mp hd0) (Int.natAbs_eq_zero.mp this)
      have hcontne : cont (Delta m) ≠ 0 := cont_ne_zero_of_ne_zero hmne
      have hge : E ≤ (Dgcd (Delta m) s).factorization p := by
        rw [← hE]
        exact (Nat.factorization_le_iff_dvd hcontne hDsne).mpr (cont_dvd_Dgcd (Delta m) s) p
      have hne : (Dgcd (Delta m) s).factorization p ≠ E := by
        intro heq
        exact absurd (hleast.2 ⟨hs1, heq⟩) (not_le.mpr hslt)
      have hgt : E + 1 ≤ (Dgcd (Delta m) s).factorization p := by omega
      have hdvd2 : p ^ (E + 1) ∣ Dgcd (Delta m) s :=
        (Nat.Prime.pow_dvd_iff_le_factorization hp hDsne).mpr hgt
      have hdvd3 : Dgcd (Delta m) s ∣ (coeff e (Delta m)).natAbs := by
        unfold Dgcd
        apply Finset.gcd_dvd
        exact Finset.mem_filter.mpr ⟨hd0, he⟩
      have h4 := hdvd2.trans hdvd3
      have h5 := Int.natCast_dvd_natCast.mpr h4
      rwa [Int.natCast_pow, Int.dvd_natAbs] at h5
    · rw [mem_support_iff, not_not] at hd0
      rw [hd0]
      exact dvd_zero _

/-- **`thm:complete-prime-local`(ii), depth formula, the `E<b` branch.** For `p\nmid a`,
`\mathbf m=(pu_1,\ldots,pu_t)`, `E:=v_p(\operatorname{cont}\Delta_{\mathbf m})<b:=v_p(B)`, with
`d` the least witness depth of `\mathbf m$ itself (and `\operatorname{Dgcd}(\Delta_{\mathbf
m})=E\ge1$` always, since any achieved shape contributing to `E` needs at least one non-singleton
block): `\delta_p(a,\mathbf m)=d`. -/
theorem complete_prime_local_case_ii_depth_E_lt_b {t : ℕ} {a : ℕ} (u : Fin t → ℕ)
    (hu : ∀ i, 0 < u i) {p : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (ha1 : 1 ≤ a)
    {E : ℕ} (hE1 : 1 ≤ E) (hE : (cont (Delta (fun i => p * u i))).factorization p = E)
    (hmne : Delta (fun i => p * u i) ≠ 0)
    {d : ℕ} (hleast : IsLeast
      {s : ℕ | 1 ≤ s ∧ (Dgcd (Delta (fun i => p * u i)) s).factorization p = E} d)
    (hb : E < padicValNat p (∑ i, p * u i)) :
    IsLeast {s : ℕ | 1 ≤ s ∧
        (Dgcd (Delta (Fin.cons a (fun i => p * u i) : Fin (t + 1) → ℕ)) s).factorization p = E}
      d := by
  set m : Fin t → ℕ := fun i => p * u i with hmdef
  set B : ℕ := ∑ i, m i with hBdef
  have ht2 := two_le_of_Delta_ne_zero m hmne
  have hB1 : 1 ≤ B := by
    rw [hBdef]
    obtain ⟨i0⟩ : Nonempty (Fin t) := ⟨⟨0, by omega⟩⟩
    have hpos : 0 < m i0 := by rw [hmdef]; exact Nat.mul_pos hp.pos (hu i0)
    calc 1 ≤ m i0 := hpos
      _ ≤ ∑ i, m i := Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ i0)
  have hterm1fact : (cont (C (a + B) - C a * C B)).factorization p = padicValNat p B :=
    padicValNat_cont_two_term_of_not_dvd_left hp ha1 hB1 hpa
  have hterm1dvd : ∀ d0, (p : ℤ) ^ (E + 1) ∣ coeff d0 (C (a + B) - C a * C B) := fun d0 =>
    dvd_coeff_of_factorization_cont_le (φ := C (a + B) - C a * C B) (k := E + 1)
      (by rw [hterm1fact]; omega) d0
  set x0 : ℕ →₀ ℕ := Finsupp.single 1 a with hx0def
  have hx0a : coeff x0 (C a) = 1 := by rw [hx0def, ← K_one]; exact coeff_single_one_K_one a
  set Ra : MvPolynomial ℕ ℤ := C a - MvPolynomial.monomial x0 (1 : ℤ) with hRadef
  have hCasplit : C a = MvPolynomial.monomial x0 (1 : ℤ) + Ra := by rw [hRadef]; ring
  have hRa_coeff : ∀ e1, coeff e1 Ra = if e1 = x0 then 0 else coeff e1 (C a) := by
    intro e1
    rw [hRadef, coeff_sub, coeff_monomial]
    by_cases he1 : e1 = x0
    · simp [he1, hx0a]
    · rw [if_neg (Ne.symm he1), if_neg he1, sub_zero]
  have hRa_ge1 : ∀ e1, coeff e1 Ra ≠ 0 → 1 ≤ nontrivialPartCount e1 := by
    intro e1 hne
    rw [hRa_coeff] at hne
    by_cases he1 : e1 = x0
    · simp [he1] at hne
    · rw [if_neg he1] at hne
      by_contra hlt
      push_neg at hlt
      exact he1 (eq_single_one_of_coeff_C_ne_zero_of_nontrivialPartCount_eq_zero hne (by omega))
  have hRa_contam : ∀ d0, nontrivialPartCount d0 ≤ d →
      (p : ℤ) ^ (E + 1) ∣ coeff d0 (Ra * Delta m) := by
    intro d0 hd0
    rw [coeff_mul]
    apply Finset.dvd_sum
    rintro ⟨x, y⟩ hxy
    rw [Finset.mem_antidiagonal] at hxy
    dsimp only at hxy ⊢
    by_cases hRa0 : coeff x Ra = 0
    · rw [hRa0, zero_mul]; exact dvd_zero _
    · have h1 : 1 ≤ nontrivialPartCount x := hRa_ge1 x hRa0
      have h2 : nontrivialPartCount x + nontrivialPartCount y = nontrivialPartCount d0 := by
        rw [← nontrivialPartCount_add, hxy]
      have h3 : nontrivialPartCount y < d := by omega
      have h4 : (p : ℤ) ^ (E + 1) ∣ coeff y (Delta m) :=
        coeff_Delta_dvd_pow_succ_of_lt_depth m hp hE hmne hleast h3 (le_refl _)
      exact dvd_mul_of_dvd_right h4 _
  have hshift : ∀ e2, coeff (x0 + e2) (MvPolynomial.monomial x0 (1 : ℤ) * Delta m) =
      coeff e2 (Delta m) := by
    intro e2
    rw [coeff_monomial_mul]
    ring
  have hDgcd_dvd_coeff : ∀ e, nontrivialPartCount e ≤ d → (p : ℤ) ^ E ∣ coeff e (Delta m) := by
    intro e he
    by_cases hz : coeff e (Delta m) = 0
    · rw [hz]; exact dvd_zero _
    · have hmemsupp : e ∈ (Delta m).support := mem_support_iff.mpr hz
      have h1 : Dgcd (Delta m) d ∣ (coeff e (Delta m)).natAbs := by
        unfold Dgcd
        apply Finset.gcd_dvd
        exact Finset.mem_filter.mpr ⟨hmemsupp, he⟩
      have h2 : p ^ E ∣ Dgcd (Delta m) d := by
        have h := Nat.ordProj_dvd (Dgcd (Delta m) d) p
        rwa [hleast.1.2] at h
      have h3 := h2.trans h1
      have h4 := Int.natCast_dvd_natCast.mpr h3
      rwa [Int.natCast_pow, Int.dvd_natAbs] at h4
  have hDdne : Dgcd (Delta m) d ≠ 0 := by
    intro h0
    have h1 := hleast.1.2
    rw [h0] at h1
    simp only [Nat.factorization_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
    omega
  have hwitness : ∃ e2, nontrivialPartCount e2 ≤ d ∧ ¬ (p : ℤ) ^ (E + 1) ∣ coeff e2 (Delta m) := by
    by_contra hcon
    push_neg at hcon
    have hdvd : p ^ (E + 1) ∣ Dgcd (Delta m) d := by
      unfold Dgcd
      apply Finset.dvd_gcd
      intro e2 he2
      rw [Finset.mem_filter] at he2
      have h1 := hcon e2 he2.2
      have h2 := Int.natAbs_dvd_natAbs.mpr h1
      rwa [Int.natAbs_pow, Int.natAbs_natCast] at h2
    have h3 := (Nat.Prime.pow_dvd_iff_le_factorization hp hDdne).mp hdvd
    have h4 := hleast.1.2
    omega
  have hx0zero : nontrivialPartCount x0 = 0 := by
    rw [hx0def, show (Finsupp.single 1 a : ℕ →₀ ℕ) = ciExp a (0 : Multiset ℕ) from by
      unfold ciExp; simp]
    rw [nontrivialPartCount_ciExp a (0 : Multiset ℕ) (by simp)]
    simp
  have heqdecomp : Delta (Fin.cons a m : Fin (t + 1) → ℕ) =
      (C (a + B) - C a * C B) +
        (MvPolynomial.monomial x0 (1 : ℤ) * Delta m + Ra * Delta m) := by
    rw [Delta_cons_eq, hCasplit]
    ring
  have hmem : 1 ≤ d ∧
      (Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) d).factorization p = E := by
    refine ⟨hleast.1.1, ?_⟩
    obtain ⟨e2star, he2bound, he2notdvd⟩ := hwitness
    set d0star : ℕ →₀ ℕ := x0 + e2star with hd0stardef
    have hd0starcount : nontrivialPartCount d0star ≤ d := by
      rw [hd0stardef, nontrivialPartCount_add, hx0zero]
      omega
    have hcoeffd0star : coeff d0star (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) =
        coeff d0star (C (a + B) - C a * C B) + coeff e2star (Delta m) +
          coeff d0star (Ra * Delta m) := by
      rw [heqdecomp, coeff_add, coeff_add, hd0stardef, hshift]
      ring
    have hnotdvd_total : ¬ (p : ℤ) ^ (E + 1) ∣
        coeff d0star (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) := by
      rw [hcoeffd0star]
      intro hcon
      apply he2notdvd
      have h1 := hterm1dvd d0star
      have h2 := hRa_contam d0star hd0starcount
      have heq : coeff e2star (Delta m) =
          (coeff d0star (C (a + B) - C a * C B) + coeff e2star (Delta m) +
            coeff d0star (Ra * Delta m)) - coeff d0star (C (a + B) - C a * C B) -
          coeff d0star (Ra * Delta m) := by ring
      rw [heq]
      exact dvd_sub (dvd_sub hcon h1) h2
    have hd0starsupp : d0star ∈ (Delta (Fin.cons a m : Fin (t + 1) → ℕ)).support := by
      rw [mem_support_iff]
      intro hz
      apply hnotdvd_total
      rw [hz]
      exact dvd_zero _
    have hDgcdne2 : Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) d ≠ 0 := by
      intro h0
      have hmemfilt : d0star ∈ (Delta (Fin.cons a m : Fin (t + 1) → ℕ)).support.filter
          (fun x => nontrivialPartCount x ≤ d) := Finset.mem_filter.mpr ⟨hd0starsupp, hd0starcount⟩
      unfold Dgcd at h0
      have := Finset.gcd_eq_zero_iff.mp h0 d0star hmemfilt
      exact (mem_support_iff.mp hd0starsupp) (Int.natAbs_eq_zero.mp this)
    have hupperfact : (Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) d).factorization p ≤ E := by
      by_contra hcon
      push_neg at hcon
      apply hnotdvd_total
      have hdvd2 : p ^ (E + 1) ∣ Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) d :=
        (Nat.Prime.pow_dvd_iff_le_factorization hp hDgcdne2).mpr (by omega)
      have hdvd3 : Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) d ∣
          (coeff d0star (Delta (Fin.cons a m : Fin (t + 1) → ℕ))).natAbs := by
        unfold Dgcd
        apply Finset.gcd_dvd
        exact Finset.mem_filter.mpr ⟨hd0starsupp, hd0starcount⟩
      have h5 := hdvd2.trans hdvd3
      have h6 := Int.natCast_dvd_natCast.mpr h5
      rwa [Int.natCast_pow, Int.dvd_natAbs] at h6
    have hlower : ∀ e, nontrivialPartCount e ≤ d →
        (p : ℤ) ^ E ∣ coeff e (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) := by
      intro e he
      rw [heqdecomp, coeff_add, coeff_add]
      refine dvd_add ?_ (dvd_add ?_ ?_)
      · exact dvd_trans (pow_dvd_pow _ (by omega)) (hterm1dvd e)
      · rw [coeff_monomial_mul']
        split_ifs with hxle
        · have heq2 : x0 + (e - x0) = e := add_tsub_cancel_of_le hxle
          have heq3 : nontrivialPartCount x0 + nontrivialPartCount (e - x0) =
              nontrivialPartCount e := by
            conv_rhs => rw [← heq2]
            rw [nontrivialPartCount_add]
          have hnpc : nontrivialPartCount (e - x0) ≤ d := by omega
          have h5 := hDgcd_dvd_coeff (e - x0) hnpc
          simpa using h5
        · exact dvd_zero _
      · exact dvd_trans (pow_dvd_pow _ (by omega)) (hRa_contam e he)
    have hlowerfact : E ≤ (Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) d).factorization p := by
      have hdvd : p ^ E ∣ Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) d := by
        unfold Dgcd
        apply Finset.dvd_gcd
        intro e he
        rw [Finset.mem_filter] at he
        have h1 := hlower e he.2
        have h2 := Int.natAbs_dvd_natAbs.mpr h1
        rwa [Int.natAbs_pow, Int.natAbs_natCast] at h2
      exact (Nat.Prime.pow_dvd_iff_le_factorization hp hDgcdne2).mp hdvd
    omega
  have hlb : ∀ s ∈ {s : ℕ | 1 ≤ s ∧
      (Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) s).factorization p = E}, d ≤ s := by
    intro s hs
    obtain ⟨hs1, hsE⟩ := hs
    by_contra hcon
    push_neg at hcon
    have hallDvd : ∀ e, nontrivialPartCount e ≤ s →
        (p : ℤ) ^ (E + 1) ∣ coeff e (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) := by
      intro e he
      rw [heqdecomp, coeff_add, coeff_add]
      refine dvd_add ?_ (dvd_add ?_ ?_)
      · exact hterm1dvd e
      · rw [coeff_monomial_mul']
        split_ifs with hxle
        · have heq2 : x0 + (e - x0) = e := add_tsub_cancel_of_le hxle
          have heq3 : nontrivialPartCount x0 + nontrivialPartCount (e - x0) =
              nontrivialPartCount e := by
            conv_rhs => rw [← heq2]
            rw [nontrivialPartCount_add]
          have hnpc : nontrivialPartCount (e - x0) < d := by omega
          have h5 := coeff_Delta_dvd_pow_succ_of_lt_depth m hp hE hmne hleast hnpc (le_refl _)
          simpa using h5
        · exact dvd_zero _
      · exact hRa_contam e (by omega)
    have hDsne : Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) s ≠ 0 := by
      intro h0
      rw [h0] at hsE
      simp only [Nat.factorization_zero, Finsupp.coe_zero, Pi.zero_apply] at hsE
      omega
    have hdvd : p ^ (E + 1) ∣ Dgcd (Delta (Fin.cons a m : Fin (t + 1) → ℕ)) s := by
      unfold Dgcd
      apply Finset.dvd_gcd
      intro e he
      rw [Finset.mem_filter] at he
      have h1 := hallDvd e he.2
      have h2 := Int.natAbs_dvd_natAbs.mpr h1
      rwa [Int.natAbs_pow, Int.natAbs_natCast] at h2
    have h3 := (Nat.Prime.pow_dvd_iff_le_factorization hp hDsne).mp hdvd
    omega
  exact ⟨hmem, hlb⟩

#print axioms coeff_Delta_dvd_pow_succ_of_lt_depth
#print axioms complete_prime_local_case_ii_depth_E_lt_b

end CongruenceTheory
