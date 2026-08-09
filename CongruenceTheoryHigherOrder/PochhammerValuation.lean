import Mathlib

/-!
**The numeric ingredient (A2) needs to close, beyond (A2a).** Proving `(A2)` — the second
divisor `(r-2)!q^r/rad(q)∣K_r(q)` of `thm:atomic-connected-content` — the manuscript reduces (via
the two-root lemma of (A2a) applied to the kernel/image of restricting a centralizer to the mixed
part) to a purely numeric fact: **"Using `v_p((q)_R)≥t+v_p((R-1)!)` gives
`v_p(|H̃:C_H̃(σ)|)≥rt-1+v_p((r-2)!)`."** The falling-factorial valuation bound itself,
`v_p((q)_R)≥v_p(q)+v_p((R-1)!)` (with `(q)_R` the Pochhammer/falling factorial, `t=v_p(q)`), is a
genuinely self-contained number-theoretic fact, independent of everything else in the argument —
formalized here on its own.

**`factorization_descFactorial_ge`**: `v_p(q)+v_p((R-1)!) ≤ v_p((q)_R)` for `1≤R≤q`, where
`(q)_R = q.descFactorial R = q(q-1)\cdots(q-R+1)`. Proof: `q.descFactorial R =
q·(q-1).descFactorial(R-1)` (Mathlib's `Nat.succ_descFactorial_succ`), and `(R-1)!∣
(q-1).descFactorial(R-1)` (any descending factorial is a multiple of the corresponding ordinary
factorial, via `Nat.descFactorial_eq_factorial_mul_choose`: `n.descFactorial k=k!·n.choose k`).
So `q·(R-1)!` divides `(q)_R`, giving the valuation inequality directly via
`Nat.factorization_le_factorization_of_dvd_right`.

**`A2_valuation_bound`** completes the arithmetic: given `r` blocks `i∈s` with `1≤R_i≤q`, and
`v_p(H)=r·v_p(q!)+v_p((r-2)!)` (for `H=S_q^r⋊S_{r-2}`), plus the manuscript's own
`v_p(C)≤Σ_i v_p((q-R_i)!)+1+Σ_i v_p((R_i-1)!)` (the group-theoretic embedding fact — kernel of
restriction embeds in `∏S_{q-R_i}`, image satisfies (A2a)'s two-root lemma — taken as a
hypothesis here, **not** re-derived), it derives `v_p(H)+1 ≥ r·v_p(q)+v_p((r-2)!)+v_p(C)` — the
manuscript's `v_p(|H:C|)≥rt-1+v_p((r-2)!)`, stated in addition form to avoid `Nat` subtraction.
Proof: `factorization_descFactorial_ge` plus `Nat.factorial_mul_descFactorial`
(`q!=(q-R_i)!·q.descFactorial R_i`) give, for every block, `v_p(q)+v_p((R_i-1)!)+v_p((q-R_i)!) ≤
v_p(q!)`; summing over all `r` blocks and combining with the hypothesis on `v_p(C)` telescopes the
`v_p((R_i-1)!)` and `v_p((q-R_i)!)` sums away entirely, leaving exactly the stated bound.
**Honest scope note**: the group-theoretic embedding fact itself (`hCbound`) — let alone the
surrounding centralizer-restriction argument that produces it — is not derived here, only used;
what's proved is that the numeric bookkeeping from there to the final valuation bound is correct.
-/

/-- `v_p(q)+v_p((R-1)!) ≤ v_p((q)_R)` for the falling factorial `(q)_R = q.descFactorial R`,
given `1≤R≤q`. -/
theorem factorization_descFactorial_ge (p q R : ℕ) (hR : 1 ≤ R) (hRq : R ≤ q) :
    q.factorization p + (Nat.factorial (R - 1)).factorization p ≤
      (q.descFactorial R).factorization p := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.succ_descFactorial_succ]
  have hRq' : R' ≤ q' := by omega
  have hcdvd : Nat.factorial R' ∣ q'.descFactorial R' :=
    ⟨q'.choose R', Nat.descFactorial_eq_factorial_mul_choose q' R'⟩
  have hprod : (q' + 1) * Nat.factorial R' ∣ (q' + 1) * q'.descFactorial R' :=
    Nat.mul_dvd_mul_left _ hcdvd
  have hne : (q' + 1) * Nat.factorial R' ≠ 0 :=
    Nat.mul_ne_zero (Nat.succ_ne_zero q') (Nat.factorial_ne_zero R')
  have hne2 : (q' + 1) * q'.descFactorial R' ≠ 0 :=
    Nat.mul_ne_zero (Nat.succ_ne_zero q') (Nat.descFactorial_pos.mpr hRq').ne'
  have hle := Nat.factorization_le_factorization_of_dvd_right (a := p) hprod hne hne2
  rwa [Nat.factorization_mul (Nat.succ_ne_zero q') (Nat.factorial_ne_zero R'),
    Finsupp.add_apply] at hle

/-- The full numeric assembly of (A2)'s valuation bound around `factorization_descFactorial_ge`,
taking the manuscript's group-theoretic embedding fact `hCbound` as a hypothesis: derives
`v_p(H)+1 ≥ r·v_p(q)+v_p((r-2)!)+v_p(C)`, the manuscript's `v_p(|H:C|)≥rt-1+v_p((r-2)!)`. -/
theorem A2_valuation_bound {p q r : ℕ} [Fact p.Prime] {ι : Type*} {s : Finset ι} (hs : s.card = r)
    {R : ι → ℕ} (hR1 : ∀ i ∈ s, 1 ≤ R i) (hRq : ∀ i ∈ s, R i ≤ q)
    {C H : ℕ} (hHval : H.factorization p = r * q.factorial.factorization p +
      (Nat.factorial (r - 2)).factorization p)
    (hCbound : C.factorization p ≤
      (∑ i ∈ s, (Nat.factorial (q - R i)).factorization p) + 1 +
        ∑ i ∈ s, (Nat.factorial (R i - 1)).factorization p) :
    r * q.factorization p + (Nat.factorial (r - 2)).factorization p + C.factorization p ≤
      H.factorization p + 1 := by
  have hstep : ∀ i ∈ s, q.factorization p + (Nat.factorial (R i - 1)).factorization p +
      (Nat.factorial (q - R i)).factorization p ≤ q.factorial.factorization p := by
    intro i hi
    have h1 := factorization_descFactorial_ge p q (R i) (hR1 i hi) (hRq i hi)
    have h2 : (q.descFactorial (R i)).factorization p +
        (Nat.factorial (q - R i)).factorization p = q.factorial.factorization p := by
      have heq : (q - R i).factorial * q.descFactorial (R i) = q.factorial :=
        Nat.factorial_mul_descFactorial (hRq i hi)
      have hne1 : (q - R i).factorial ≠ 0 := Nat.factorial_ne_zero _
      have hne2 : q.descFactorial (R i) ≠ 0 := (Nat.descFactorial_pos.mpr (hRq i hi)).ne'
      rw [← heq, Nat.factorization_mul hne1 hne2, Finsupp.add_apply]
      ring
    omega
  have hsum : ∑ i ∈ s, (q.factorization p + (Nat.factorial (R i - 1)).factorization p +
      (Nat.factorial (q - R i)).factorization p) ≤ ∑ _i ∈ s, q.factorial.factorization p :=
    Finset.sum_le_sum hstep
  simp only [Finset.sum_add_distrib, Finset.sum_const, hs, smul_eq_mul] at hsum
  rw [hHval]
  omega
