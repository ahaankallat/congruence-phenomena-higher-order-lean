import Mathlib

/-!
**The Lucas'-theorem application from (A6)'s sharpness argument for
`thm:atomic-connected-content`.** In proving sharpness of the exact valuation
`v_p(cont K_r(q))=rt-1+v_p((r-1)!)-min{t-1,v_p(r-1)}`, the manuscript exhibits a specific
minimum-weight term in the moment-cumulant decomposition (A4) and needs its coefficient
`A_h=\frac{(r-1)!}{d(h-1)!^d}Q^r\binom{r(Q-1)}{d-1}` (A6) to be prime to `p`, which reduces
(everything else in `A_h` being manifestly prime to `p`) to: **"since `d∣Q` and `r≡1 (mod d)`,
Lucas' theorem gives `p∤C(r(Q-1),d-1)`"**, for `d=p^s`. This is a genuinely self-contained
number-theoretic fact, independent of everything else in the manuscript's argument (the
hypertree enumeration, the moment-cumulant identity, the algebraic-independence argument) — so
it is formalized here on its own, building on Mathlib's existing `Mathlib.Data.Nat.Choose.Lucas`.

**`not_dvd_choose_pow_sub_one_of_mod_eq`**: if `n≡p^s-1 (mod p^s)`, then `p∤C(n,p^s-1)`. This is
the general shape of the phenomenon: `k=p^s-1`'s base-`p` digits are all maxed out at `p-1`, and
`n`'s matching bottom `s` digits are too (from `n≡p^s-1 mod p^s`), so every digit-wise binomial
coefficient Lucas' theorem produces for `C(n,k)` is `C(p-1,p-1)=1`, and the top digit is
`C(anything,0)=1` — none of them are `0 mod p`, so neither is the product. Proved by induction on
`s`, peeling one base-`p` digit at a time via Mathlib's
`Choose.choose_modEq_choose_mod_mul_choose_div_nat`.

**`not_dvd_choose_of_dvd_and_modEq`**: the manuscript's own statement, `d=p^s∣Q` and `r≡1 (mod d)`
(stated as `d∣(r-1)`, `r≥1`, avoiding the `Nat`-subtraction awkwardness of `≡` mod a variable
modulus) imply `p∤C(r(Q-1),d-1)`. Reduces to the general fact above via
`r(Q-1)=(p^s-1)+p^s·(m(Q-1)+(Q'-1))` where `r=p^s·m+1` and `Q=p^s·Q'` — i.e. `r(Q-1)≡p^s-1
(mod p^s)`, since `Q≡0` and `r≡1` mod `p^s` force `r(Q-1)=r·Q-r≡0-1≡p^s-1 (mod p^s)`.
-/

open Choose

theorem not_dvd_choose_pow_sub_one_of_mod_eq {p : ℕ} [Fact p.Prime] :
    ∀ s n : ℕ, n % p ^ s = p ^ s - 1 → ¬ p ∣ Nat.choose n (p ^ s - 1) := by
  have hp := Fact.out (p := p.Prime)
  intro s
  induction s with
  | zero => intro n hn; simp [hp.ne_one]
  | succ s ih =>
    intro n hn
    obtain ⟨b, hb⟩ : ∃ b, p ^ s = b + 1 := by
      refine ⟨p ^ s - 1, ?_⟩
      have h1 : 1 ≤ p ^ s := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero s hp.pos.ne')
      omega
    have hpow : p ^ (s + 1) = p * (b + 1) := by rw [pow_succ', hb]
    have hpk : p ^ (s + 1) - 1 = (p - 1) + p * b := by
      rw [hpow]
      have heq : p * (b + 1) = p * b + p := by ring
      rw [heq, Nat.add_sub_assoc hp.pos]
      ring
    have hkp : (p ^ (s + 1) - 1) % p = p - 1 := by
      rw [hpk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.sub_lt hp.pos one_pos)]
    have hkd : (p ^ (s + 1) - 1) / p = b := by
      rw [hpk, Nat.add_mul_div_left _ _ hp.pos,
        Nat.div_eq_of_lt (Nat.sub_lt hp.pos one_pos), Nat.zero_add]
    have hnp : n % p = p - 1 := by
      have h1 : n % p = (n % p ^ (s + 1)) % p :=
        (Nat.mod_mod_of_dvd n (dvd_pow_self p s.succ_ne_zero)).symm
      rw [h1, hn, hkp]
    have hnd : (n / p) % p ^ s = p ^ s - 1 := by
      obtain ⟨a, ha⟩ : ∃ a, n = p ^ (s + 1) * a + (p ^ (s + 1) - 1) :=
        ⟨n / p ^ (s + 1), by rw [← hn]; exact (Nat.div_add_mod n (p ^ (s + 1))).symm⟩
      have han : n = (p - 1) + p * ((b + 1) * a + b) := by
        rw [ha, hpk, hpow]; ring
      have hnp2 : n / p = (b + 1) * a + b := by
        rw [han, Nat.add_mul_div_left _ _ hp.pos,
          Nat.div_eq_of_lt (Nat.sub_lt hp.pos one_pos), Nat.zero_add]
      rw [hnp2, hb, add_comm ((b + 1) * a) b, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (Nat.lt_succ_self b)]
      omega
    have hbeq : p ^ s - 1 = b := by omega
    have hrec := ih (n / p) hnd
    rw [hbeq] at hrec
    intro hdvd
    have hmod := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (n := n) (k := p ^ (s + 1) - 1) (p := p)
    rw [hnp, hkp, hkd] at hmod
    have hdvd2 : p ∣ Nat.choose (p - 1) (p - 1) * Nat.choose (n / p) b :=
      Nat.modEq_zero_iff_dvd.mp ((Nat.ModEq.symm hmod).trans
        (Nat.modEq_zero_iff_dvd.mpr hdvd))
    rw [Nat.choose_self, one_mul] at hdvd2
    exact hrec hdvd2

/-- The manuscript's Lucas'-theorem application in (A6)'s sharpness argument: for `d=p^s∣Q`
and `r≡1 (mod d)`, `p∤C(r(Q-1),d-1)`. -/
theorem not_dvd_choose_of_dvd_and_modEq {p s Q r : ℕ} [Fact p.Prime]
    (hQ : p ^ s ∣ Q) (hQpos : 1 ≤ Q) (hrpos : 1 ≤ r) (hr : p ^ s ∣ (r - 1)) :
    ¬ p ∣ Nat.choose (r * (Q - 1)) (p ^ s - 1) := by
  apply not_dvd_choose_pow_sub_one_of_mod_eq
  obtain ⟨Q', hQ'⟩ := hQ
  obtain ⟨m, hm⟩ := hr
  have hQ'pos : 1 ≤ Q' := by
    rcases Nat.eq_zero_or_pos Q' with h0 | h1
    · rw [h0, mul_zero] at hQ'; omega
    · exact h1
  have hreq : r = p ^ s * m + 1 := by omega
  have heq : r * (Q - 1) = (p ^ s - 1) + p ^ s * (m * (Q - 1) + (Q' - 1)) := by
    have hQeq : Q - 1 = p ^ s * (Q' - 1) + (p ^ s - 1) := by
      have hps : 1 ≤ p ^ s := Nat.one_le_iff_ne_zero.mpr
        (pow_ne_zero s (Fact.out (p := p.Prime)).pos.ne')
      rw [hQ']
      have : p ^ s * Q' = p ^ s * (Q' - 1) + p ^ s := by
        rw [← Nat.mul_add_one]
        congr 1
        omega
      omega
    rw [hreq, hQeq]
    ring
  rw [heq, Nat.add_mul_mod_self_left]
  have hps : 1 ≤ p ^ s := Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero s (Fact.out (p := p.Prime)).pos.ne')
  exact Nat.mod_eq_of_lt (by omega)
