import Mathlib
import CongruenceTheory.ContentBounds

/-!
**Proposition `prop:prime-witness`** ("Explicit prime-adic sharpness witness"): for a prime
`p` dividing both `n` and `k`, the coefficient of `X_{2p}X_1^{N-2p}` (`N = n+k`) in
`C_N - C_n C_k` has `p`-adic valuation exactly `v_p(n) + v_p(k) - 1` — matching the sharp
side of `thm:optimal-divisor`. This file generalizes `ContentBounds.lean`'s single-`2`-cycle
coefficient-extraction argument to a single-`2p`-cycle, then does the valuation analysis.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm MvPolynomial Nat

open scoped Classical

/-- The count of `ℓ`-cycles (single cycle of length `ℓ`, rest fixed) in `Perm α`,
generalizing `twoCycleCount`. -/
noncomputable def singleCycleCount (n ℓ : ℕ) : ℤ :=
  ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.cycleType = ({ℓ} : Multiset ℕ))).card : ℤ)

/-- **Generalized `card_twoCycle_eq_choose`**: the number of single-`ℓ`-cycles in `Perm α` is
`C(N,ℓ)·(ℓ-1)!`, `N = Fintype.card α`. -/
theorem card_singleCycle_eq_choose_mul {α : Type*} [Fintype α] [DecidableEq α] (ℓ : ℕ)
    (hℓ : 2 ≤ ℓ) :
    (Finset.univ.filter (fun g : Equiv.Perm α => g.cycleType = ({ℓ} : Multiset ℕ))).card =
      (Fintype.card α).choose ℓ * (ℓ - 1)! := by
  have hcard := Equiv.Perm.card_of_cycleType α ({ℓ} : Multiset ℕ)
  rw [show (Finset.univ.filter (fun σ : Equiv.Perm α => σ.cycleType = {ℓ})) =
      ({g : Equiv.Perm α | g.cycleType = {ℓ}} : Finset (Equiv.Perm α)) from rfl, hcard]
  by_cases hN : ℓ ≤ Fintype.card α
  · rw [if_pos ⟨by simpa using hN, by intro a ha; simp at ha; omega⟩]
    simp only [Multiset.sum_singleton, Multiset.prod_singleton, Multiset.toFinset_singleton,
      Finset.prod_singleton, Multiset.count_singleton_self, Nat.factorial_one, mul_one]
    have key : (Fintype.card α)! =
        ((Fintype.card α - ℓ)! * ℓ) * ((Fintype.card α).choose ℓ * (ℓ - 1)!) := by
      have h1 := Nat.choose_mul_factorial_mul_factorial hN
      have h2 : ℓ ! = ℓ * (ℓ - 1)! := by
        conv_lhs => rw [show ℓ = (ℓ - 1) + 1 from by omega]
        rw [Nat.factorial_succ]
        congr 1
        omega
      rw [← h1, h2]; ring
    rw [key, Nat.mul_div_cancel_left _ (by positivity)]
  · rw [if_neg (by simp [hN]), Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- **Generalized `coeff_ci_sumCongr_target`**, for a general single-cycle type `{ℓ}`. -/
lemma coeff_ci_sumCongr_target_singleCycle {n k ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (p : Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) :
    MvPolynomial.coeff (ciExp (n + k - ℓ) {ℓ}) (ci (Equiv.Perm.sumCongr p.1 p.2)) =
      (if p.1.cycleType = ({ℓ} : Multiset ℕ) ∧ p.2.cycleType = (0 : Multiset ℕ) then (1 : ℤ)
        else 0) +
      (if p.1.cycleType = (0 : Multiset ℕ) ∧ p.2.cycleType = ({ℓ} : Multiset ℕ) then (1 : ℤ)
        else 0) := by
  rw [ci_sumCongr, ci_eq_monomial, ci_eq_monomial, MvPolynomial.monomial_mul, one_mul,
    MvPolynomial.coeff_monomial]
  have hn : p.1.cycleType.sum ≤ n := by have := Equiv.Perm.sum_cycleType_le p.1; simpa using this
  have hk : p.2.cycleType.sum ≤ k := by have := Equiv.Perm.sum_cycleType_le p.2; simpa using this
  have hgne : ∀ x ∈ p.1.cycleType, x ≠ 1 := fun x hx => by
    have := Equiv.Perm.two_le_of_mem_cycleType hx; omega
  have hgne' : ∀ x ∈ p.2.cycleType, x ≠ 1 := fun x hx => by
    have := Equiv.Perm.two_le_of_mem_cycleType hx; omega
  have hgnesum : ∀ x ∈ p.1.cycleType + p.2.cycleType, x ≠ 1 := by
    intro x hx
    rw [Multiset.mem_add] at hx
    rcases hx with hx | hx
    · exact hgne x hx
    · exact hgne' x hx
  have hℓne : ∀ x ∈ ({ℓ} : Multiset ℕ), x ≠ 1 := by intro x hx; simp at hx; omega
  have key : (ciExp (n - p.1.cycleType.sum) p.1.cycleType +
      ciExp (k - p.2.cycleType.sum) p.2.cycleType = ciExp (n + k - ℓ) ({ℓ} : Multiset ℕ)) ↔
      (p.1.cycleType = {ℓ} ∧ p.2.cycleType = (0 : Multiset ℕ)) ∨
        (p.1.cycleType = (0 : Multiset ℕ) ∧ p.2.cycleType = {ℓ}) := by
    rw [ciExp_add, ciExp_eq_iff hgnesum hℓne, ← multiset_add_eq_singleton_iff]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have hsuml : p.1.cycleType.sum + p.2.cycleType.sum = ℓ := by
        have := congrArg Multiset.sum h; simpa using this
      omega
  simp only [key]
  by_cases h1 : p.1.cycleType = ({ℓ} : Multiset ℕ) ∧ p.2.cycleType = (0 : Multiset ℕ)
  · have h2 : ¬ (p.1.cycleType = (0 : Multiset ℕ) ∧ p.2.cycleType = {ℓ}) := by
      rintro ⟨h2a, -⟩
      rw [h1.1] at h2a
      have : ({ℓ} : Multiset ℕ) ≠ (0 : Multiset ℕ) := by
        intro hc; have := congrArg Multiset.card hc; simp at this
      exact this h2a
    rw [if_pos (Or.inl h1), if_pos h1, if_neg h2]; ring
  · by_cases h2 : p.1.cycleType = (0 : Multiset ℕ) ∧ p.2.cycleType = {ℓ}
    · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2]; ring
    · rw [if_neg (not_or.mpr ⟨h1, h2⟩), if_neg h1, if_neg h2]; ring

/-- **Generalized `coeff_Cperm_mul`**: the coefficient of `X_1^{n+k-ℓ}X_ℓ` in `Cperm n * Cperm k`
is `singleCycleCount n ℓ + singleCycleCount k ℓ`. -/
theorem coeff_Cperm_mul_singleCycle (n k ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    MvPolynomial.coeff (ciExp (n + k - ℓ) {ℓ}) (Cperm n * Cperm k) =
      singleCycleCount n ℓ + singleCycleCount k ℓ := by
  rw [Cperm_mul, MvPolynomial.coeff_sum]
  have hpt : ∀ p : Equiv.Perm (Fin n) × Equiv.Perm (Fin k),
      MvPolynomial.coeff (ciExp (n + k - ℓ) {ℓ}) (ci (Equiv.Perm.sumCongr p.1 p.2)) =
      (if p.1.cycleType = ({ℓ} : Multiset ℕ) then (1 : ℤ) else 0) *
        (if p.2.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0) +
      (if p.1.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0) *
        (if p.2.cycleType = ({ℓ} : Multiset ℕ) then (1 : ℤ) else 0) := by
    intro p
    rw [coeff_ci_sumCongr_target_singleCycle hℓ]
    by_cases h1 : p.1.cycleType = ({ℓ} : Multiset ℕ) <;>
      by_cases h2 : p.2.cycleType = (0 : Multiset ℕ) <;>
      by_cases h3 : p.1.cycleType = (0 : Multiset ℕ) <;>
      by_cases h4 : p.2.cycleType = ({ℓ} : Multiset ℕ) <;>
      simp_all
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type]
  dsimp only
  have e1 : (∑ x : Equiv.Perm (Fin n), (if x.cycleType = ({ℓ} : Multiset ℕ) then (1 : ℤ) else 0)) *
      (∑ y : Equiv.Perm (Fin k), (if y.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0)) =
      ∑ x : Equiv.Perm (Fin n), ∑ y : Equiv.Perm (Fin k),
        (if x.cycleType = {ℓ} then (1 : ℤ) else 0) * (if y.cycleType = 0 then (1 : ℤ) else 0) :=
    Finset.sum_mul_sum Finset.univ Finset.univ _ _
  have e2 : (∑ x : Equiv.Perm (Fin n), (if x.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0)) *
      (∑ y : Equiv.Perm (Fin k), (if y.cycleType = ({ℓ} : Multiset ℕ) then (1 : ℤ) else 0)) =
      ∑ x : Equiv.Perm (Fin n), ∑ y : Equiv.Perm (Fin k),
        (if x.cycleType = 0 then (1 : ℤ) else 0) * (if y.cycleType = {ℓ} then (1 : ℤ) else 0) :=
    Finset.sum_mul_sum Finset.univ Finset.univ _ _
  rw [← e1, ← e2]
  have hz1 : (∑ x : Equiv.Perm (Fin n), (if x.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0))
      = 1 := by
    have heq : (∑ x : Equiv.Perm (Fin n), (if x.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0))
        = ((Finset.univ.filter (fun x : Equiv.Perm (Fin n) => x.cycleType = 0)).card : ℤ) := by
      rw [Finset.card_filter]; push_cast; rfl
    rw [heq, card_cycleType_zero]; norm_num
  have hz2 : (∑ y : Equiv.Perm (Fin k), (if y.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0))
      = 1 := by
    have heq : (∑ y : Equiv.Perm (Fin k), (if y.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0))
        = ((Finset.univ.filter (fun y : Equiv.Perm (Fin k) => y.cycleType = 0)).card : ℤ) := by
      rw [Finset.card_filter]; push_cast; rfl
    rw [heq, card_cycleType_zero]; norm_num
  rw [hz1, hz2, mul_one, one_mul]
  simp only [singleCycleCount, Finset.card_filter]
  push_cast
  ring

/-- **Generalized `coeff_CpermPair`**: the coefficient of `X_1^{n+k-ℓ}X_ℓ` in `CpermPair n k`
is `C(n+k,ℓ)·(ℓ-1)!`. -/
theorem coeff_CpermPair_singleCycle (n k ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    MvPolynomial.coeff (ciExp (n + k - ℓ) {ℓ}) (CpermPair n k) =
      ((n + k).choose ℓ * (ℓ - 1)! : ℤ) := by
  have hcard : Fintype.card (Fin n ⊕ Fin k) = n + k := by simp
  have hcnt := coeff_sum_ci_eq_card_cycleType (α := Fin n ⊕ Fin k) ({ℓ} : Multiset ℕ) (by
    intro x hx; simp at hx; omega)
  simp only [Multiset.sum_singleton] at hcnt
  rw [hcard] at hcnt
  show MvPolynomial.coeff (ciExp (n + k - ℓ) {ℓ}) (∑ g : Equiv.Perm (Fin n ⊕ Fin k), ci g) = _
  rw [hcnt, card_singleCycle_eq_choose_mul (α := Fin n ⊕ Fin k) ℓ hℓ, hcard]
  push_cast
  ring

/-- **The single-`ℓ`-cycle coefficient of the defect, general form**:
`[X_1^{n+k-ℓ}X_ℓ](CpermPair n k - Cperm n · Cperm k) = (ℓ-1)!·(C(n+k,ℓ) - C(n,ℓ) - C(k,ℓ))`. -/
theorem coeff_defect_singleCycle (n k ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    MvPolynomial.coeff (ciExp (n + k - ℓ) {ℓ}) (CpermPair n k - Cperm n * Cperm k) =
      ((ℓ - 1)! : ℤ) * (((n + k).choose ℓ : ℤ) - (n.choose ℓ : ℤ) - (k.choose ℓ : ℤ)) := by
  rw [MvPolynomial.coeff_sub, coeff_CpermPair_singleCycle n k ℓ hℓ,
    coeff_Cperm_mul_singleCycle n k ℓ hℓ]
  have hsn : singleCycleCount n ℓ = (n.choose ℓ * (ℓ - 1)! : ℤ) := by
    rw [singleCycleCount, card_singleCycle_eq_choose_mul ℓ hℓ, Fintype.card_fin]; push_cast; ring
  have hsk : singleCycleCount k ℓ = (k.choose ℓ * (ℓ - 1)! : ℤ) := by
    rw [singleCycleCount, card_singleCycle_eq_choose_mul ℓ hℓ, Fintype.card_fin]; push_cast; ring
  rw [hsn, hsk]
  ring

/-! ### Valuation analysis -/

/-- **Ultrametric dominance**: if one term of a finite sum of naturals has `p`-adic valuation
exactly `V` and every other term is divisible by `p^(V+1)`, the whole sum has valuation
exactly `V`. -/
theorem padicValNat_sum_eq_of_unique_min (p : ℕ) (hp : p.Prime) {ι : Type*} (s : Finset ι)
    (f : ι → ℕ) (i0 : ι) (hi0 : i0 ∈ s) (V : ℕ) (hV : padicValNat p (f i0) = V)
    (hne0 : f i0 ≠ 0) (hother : ∀ i ∈ s, i ≠ i0 → p ^ (V + 1) ∣ f i) :
    padicValNat p (∑ i ∈ s, f i) = V := by
  haveI := Fact.mk hp
  have hsplit : f i0 + ∑ i ∈ s.erase i0, f i = ∑ i ∈ s, f i := Finset.add_sum_erase s f hi0
  have hRdvd : p ^ (V + 1) ∣ ∑ i ∈ s.erase i0, f i :=
    Finset.dvd_sum (fun i hi => hother i (Finset.mem_of_mem_erase hi)
      (Finset.ne_of_mem_erase hi))
  obtain ⟨w, hw⟩ := hRdvd
  have hudvd : p ^ V ∣ f i0 := hV ▸ pow_padicValNat_dvd
  obtain ⟨u, hu⟩ := hudvd
  have hune0 : u ≠ 0 := by rintro rfl; simp at hu; exact hne0 hu
  have hpu : ¬ p ∣ u := by
    intro hdvd
    obtain ⟨u', hu'⟩ := hdvd
    have heq : f i0 = p ^ (V + 1) * u' := by rw [hu, hu']; ring
    have hge : V + 1 ≤ padicValNat p (f i0) := (padicValNat_dvd_iff_le hne0).mp ⟨u', heq⟩
    omega
  rw [← hsplit, hw, hu, show p ^ V * u + p ^ (V + 1) * w = p ^ V * (u + p * w) from by ring]
  have hne : u + p * w ≠ 0 := by omega
  rw [padicValNat.mul (pow_ne_zero V hp.pos.ne') hne, padicValNat.prime_pow]
  have hz : padicValNat p (u + p * w) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hdvd
    apply hpu
    have hpw : p ∣ p * w := dvd_mul_right p w
    rw [add_comm] at hdvd
    exact (Nat.dvd_add_right hpw).mp hdvd
  omega

/-- The `2p`-defect is `(2p-1)!` times the Vandermonde-reduced sum. -/
theorem coeff_defect_twoP (n k p : ℕ) (hp : p.Prime) :
    MvPolynomial.coeff (ciExp (n + k - 2 * p) {2 * p}) (CpermPair n k - Cperm n * Cperm k) =
      ((2 * p - 1)! : ℤ) * ∑ i ∈ Finset.Ico 1 (2 * p), (n.choose i * k.choose (2 * p - i) : ℤ) := by
  have hppos : 0 < p := hp.pos
  rw [coeff_defect_singleCycle n k (2 * p) (by have := hp.two_le; omega)]
  congr 1
  have hvdm := Nat.add_choose_eq n k (2 * p)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hvdm
  dsimp only at hvdm
  have hexpand : ∑ i ∈ Finset.range (2 * p + 1), n.choose i * k.choose (2 * p - i) =
      n.choose 0 * k.choose (2 * p) + n.choose (2 * p) * k.choose 0 +
        ∑ i ∈ Finset.Ico 1 (2 * p), n.choose i * k.choose (2 * p - i) := by
    rw [show Finset.range (2 * p + 1) = insert 0 (insert (2 * p) (Finset.Ico 1 (2 * p))) from by
      ext i; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega]
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp)]
    simp only [Nat.sub_zero, Nat.sub_self]
    ring
  rw [hexpand] at hvdm
  simp only [Nat.choose_zero_right, one_mul, mul_one] at hvdm
  have hcast := congrArg (Nat.cast : ℕ → ℤ) hvdm
  push_cast at hcast
  linarith [hcast]

/-- `v_p((2p-1)!) = 1`, for any prime `p`. -/
theorem padicValNat_factorial_twoP_sub_one (p : ℕ) (hp : p.Prime) :
    padicValNat p ((2 * p - 1)!) = 1 := by
  haveI := Fact.mk hp
  have hp2 := hp.two_le
  have hb : Nat.log p (2 * p - 1) < 2 := by
    have h1' : 2 * p < p ^ 2 + 1 := by nlinarith
    have h1 : 2 * p - 1 < p ^ 2 := by omega
    exact Nat.log_lt_of_lt_pow (by omega) h1
  rw [padicValNat_factorial hb]
  have hrange : Finset.Ico 1 2 = ({1} : Finset ℕ) := rfl
  rw [hrange, Finset.sum_singleton, pow_one]
  have hlo : 1 ≤ (2 * p - 1) / p := Nat.le_div_iff_mul_le hp.pos |>.mpr (by omega)
  have hhi : (2 * p - 1) / p < 2 := Nat.div_lt_iff_lt_mul hp.pos |>.mpr (by omega)
  omega

/-- **The central-term exact valuation**: `v_p(C(n,p)) + 1 = v_p(n)`, for `p ∣ n`, `n ≠ 0`.
Among the `p` consecutive integers `n, n-1, …, n-p+1`, only `n` itself is divisible by `p`. -/
theorem padicValNat_choose_prime_self_add_one (p n : ℕ) (hp : p.Prime) (hpn : p ∣ n)
    (hn0 : n ≠ 0) : padicValNat p (n.choose p) + 1 = padicValNat p n := by
  haveI := Fact.mk hp
  have hpn_le : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn
  have hdesc : n.descFactorial p = ∏ i ∈ Finset.range p, (n - i) :=
    Nat.descFactorial_eq_prod_range n p
  have hne : ∀ i ∈ Finset.range p, n - i ≠ 0 := by
    intro i hi; simp only [Finset.mem_range] at hi; omega
  have hfact := Nat.factorization_prod (S := Finset.range p) (g := fun i => n - i) hne
  have hfactp := congrArg (fun f => f p) hfact
  simp only [Finset.sum_apply'] at hfactp
  have hzero : ∀ i ∈ Finset.range p, i ≠ 0 → (n - i).factorization p = 0 := by
    intro i hi hine
    simp only [Finset.mem_range] at hi
    rw [Nat.factorization_def _ hp]
    apply padicValNat.eq_zero_of_not_dvd
    intro hdvd
    have hpi : p ∣ (n - (n - i)) := Nat.dvd_sub hpn hdvd
    have heq : n - (n - i) = i := by omega
    rw [heq] at hpi
    have := Nat.le_of_dvd (by omega) hpi
    omega
  have hsum : (Finset.range p).sum (fun i => (n - i).factorization p) =
      (n - 0).factorization p := by
    rw [Finset.sum_eq_single 0]
    · exact fun i hi hine => hzero i hi hine
    · exact fun h0 => absurd (Finset.mem_range.mpr hp.pos) h0
  rw [hsum, ← hdesc] at hfactp
  simp only [Nat.sub_zero, Nat.factorization_def _ hp] at hfactp
  have hdc : n.descFactorial p = p ! * n.choose p :=
    Nat.descFactorial_eq_factorial_mul_choose n p
  rw [hdc] at hfactp
  have hchoosepos : n.choose p ≠ 0 := by
    rw [← Nat.pos_iff_ne_zero]; exact Nat.choose_pos hpn_le
  rw [padicValNat.mul (Nat.factorial_ne_zero p) hchoosepos] at hfactp
  have hpfact : padicValNat p (p !) = 1 := by
    have := padicValNat_factorial_mul (p := p) 1
    simpa using this
  rw [hpfact] at hfactp
  omega

/-- The central-term product `C(n,p)·C(k,p)` has `v_p + 1 = v_p(n) + v_p(k)`. -/
theorem padicValNat_two_p_defect (n k p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hpk : p ∣ k)
    (hn0 : n ≠ 0) (hk0 : k ≠ 0) :
    padicValNat p (n.choose p * k.choose p) + 2 = padicValNat p n + padicValNat p k := by
  haveI := Fact.mk hp
  have h1 := padicValNat_choose_prime_self_add_one p n hp hpn hn0
  have h2 := padicValNat_choose_prime_self_add_one p k hp hpk hk0
  have hne1 : n.choose p ≠ 0 := by
    rw [← Nat.pos_iff_ne_zero]
    exact Nat.choose_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn)
  have hne2 : k.choose p ≠ 0 := by
    rw [← Nat.pos_iff_ne_zero]
    exact Nat.choose_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hpk)
  rw [padicValNat.mul hne1 hne2]
  omega

/-- **The Vandermonde-sum valuation**: `v_p(∑_{i=1}^{2p-1} C(n,i)C(k,2p-i)) + 2 = v_p(n) + v_p(k)`,
via ultrametric dominance of the central (`i=p`) term. -/
theorem padicValNat_sum_eq (n k p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hpk : p ∣ k) (hn0 : n ≠ 0)
    (hk0 : k ≠ 0) :
    padicValNat p (∑ i ∈ Finset.Ico 1 (2 * p), n.choose i * k.choose (2 * p - i)) + 2 =
      padicValNat p n + padicValNat p k := by
  haveI := Fact.mk hp
  have hVeq := padicValNat_two_p_defect n k p hp hpn hpk hn0 hk0
  have hi0mem : p ∈ Finset.Ico 1 (2 * p) := by
    simp only [Finset.mem_Ico]; have := hp.two_le; omega
  have hterm : ∀ i ∈ Finset.Ico 1 (2 * p), i ≠ p →
      p ^ (padicValNat p (n.choose p * k.choose p) + 1) ∣
        n.choose i * k.choose (2 * p - i) := by
    intro i hi hine
    simp only [Finset.mem_Ico] at hi
    rcases le_or_gt i n with hile | higt
    · rcases le_or_gt (2 * p - i) k with hjle | hjgt
      · have hip : ¬ p ∣ i := by
          intro hdvd
          rcases lt_or_gt_of_ne hine with hlt | hgt
          · have := Nat.le_of_dvd (by omega) hdvd; omega
          · have hps : p ∣ (i - p) := Nat.dvd_sub hdvd (dvd_refl p)
            have hpos : 0 < i - p := by omega
            have := Nat.le_of_dvd hpos hps
            omega
        have hbi : padicValNat p n ≤ padicValNat p (n.choose i) := by
          have hchoose := Nat.factorization_le_factorization_choose_add (p := p) hile (by omega)
          rw [Nat.factorization_def n hp, Nat.factorization_def (n.choose i) hp,
            Nat.factorization_def i hp] at hchoose
          have hvi : padicValNat p i = 0 := padicValNat.eq_zero_of_not_dvd hip
          omega
        have hjne0 : 2 * p - i ≠ 0 := by omega
        have hjp : ¬ p ∣ (2 * p - i) := by
          intro hdvd
          apply hip
          have hps : p ∣ (2 * p - (2 * p - i)) := Nat.dvd_sub (dvd_mul_left p 2) hdvd
          have heq : 2 * p - (2 * p - i) = i := by omega
          rwa [heq] at hps
        have hbj : padicValNat p k ≤ padicValNat p (k.choose (2 * p - i)) := by
          have hchoose := Nat.factorization_le_factorization_choose_add (p := p) hjle hjne0
          rw [Nat.factorization_def k hp, Nat.factorization_def (k.choose (2 * p - i)) hp,
            Nat.factorization_def (2 * p - i) hp] at hchoose
          have hvj : padicValNat p (2 * p - i) = 0 := padicValNat.eq_zero_of_not_dvd hjp
          omega
        have hipos : n.choose i ≠ 0 := by rw [← Nat.pos_iff_ne_zero]; exact Nat.choose_pos hile
        have hjpos : k.choose (2 * p - i) ≠ 0 := by
          rw [← Nat.pos_iff_ne_zero]; exact Nat.choose_pos hjle
        have hne : n.choose i * k.choose (2 * p - i) ≠ 0 := Nat.mul_ne_zero hipos hjpos
        have hVp1 : padicValNat p (n.choose p * k.choose p) + 1 ≤
            padicValNat p (n.choose i * k.choose (2 * p - i)) := by
          rw [padicValNat.mul hipos hjpos]
          omega
        exact (padicValNat_dvd_iff_le hne).mpr hVp1
      · have hz : k.choose (2 * p - i) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [hz]
    · have hz : n.choose i = 0 := Nat.choose_eq_zero_of_lt higt
      simp [hz]
  have h2pp : 2 * p - p = p := by omega
  have hne0term : n.choose p * k.choose (2 * p - p) ≠ 0 := by
    rw [h2pp]
    apply Nat.mul_ne_zero
    · rw [← Nat.pos_iff_ne_zero]
      exact Nat.choose_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn)
    · rw [← Nat.pos_iff_ne_zero]
      exact Nat.choose_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hpk)
  have hVeq2 : padicValNat p (n.choose p * k.choose (2 * p - p)) =
      padicValNat p (n.choose p * k.choose p) := by rw [h2pp]
  have hsum := padicValNat_sum_eq_of_unique_min p hp (Finset.Ico 1 (2 * p))
    (fun i => n.choose i * k.choose (2 * p - i)) p hi0mem
    (padicValNat p (n.choose p * k.choose p)) hVeq2 hne0term hterm
  omega

/-- **Proposition `prop:prime-witness`**: for a prime `p` dividing both `n` and `k`, the
coefficient of `X_{2p}X_1^{n+k-2p}` in `C_{n+k} - C_n C_k` has `p`-adic valuation exactly
`v_p(n) + v_p(k) - 1` (stated as `+1 =` to avoid truncated subtraction). -/
theorem prime_witness (n k p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hpk : p ∣ k) (hn0 : n ≠ 0)
    (hk0 : k ≠ 0) :
    padicValNat p
        (MvPolynomial.coeff (ciExp (n + k - 2 * p) {2 * p})
          (CpermPair n k - Cperm n * Cperm k)).natAbs + 1 =
      padicValNat p n + padicValNat p k := by
  haveI := Fact.mk hp
  rw [coeff_defect_twoP n k p hp]
  rw [show ((2 * p - 1)! : ℤ) * ∑ i ∈ Finset.Ico 1 (2 * p), (n.choose i * k.choose (2 * p - i) : ℤ)
      = (((2 * p - 1)! * ∑ i ∈ Finset.Ico 1 (2 * p), n.choose i * k.choose (2 * p - i) : ℕ) : ℤ)
      from by push_cast; ring]
  rw [Int.natAbs_natCast]
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (by
    have hne0term : n.choose p * k.choose p ≠ 0 :=
      Nat.mul_ne_zero
        (by rw [← Nat.pos_iff_ne_zero]
            exact Nat.choose_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn))
        (by rw [← Nat.pos_iff_ne_zero]
            exact Nat.choose_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hpk))
    intro hz
    rw [Finset.sum_eq_zero_iff] at hz
    have hi0mem : p ∈ Finset.Ico 1 (2 * p) := by
      simp only [Finset.mem_Ico]; have := hp.two_le; omega
    have hzp := hz p hi0mem
    rw [show 2 * p - p = p from by omega] at hzp
    exact hne0term hzp)]
  rw [padicValNat_factorial_twoP_sub_one p hp]
  have := padicValNat_sum_eq n k p hp hpn hpk hn0 hk0
  omega

end CongruenceTheory
