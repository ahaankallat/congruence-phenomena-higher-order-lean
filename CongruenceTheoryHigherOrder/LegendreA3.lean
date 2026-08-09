import Mathlib

/-!
**The Legendre's-formula identity from (A3)'s sharpness argument.** Proving sharpness of
`thm:atomic-connected-content`'s exact valuation, the manuscript's first step is: "At the first
prime layer put `e_p(j)=j-1+v_p((j-1)!)`. The coefficient of `X_{jp}` in `K_j(p)` is `(jp-1)!`;
... Legendre's formula gives `v_p((jp-1)!)=e_p(j)`, so `v_p(cont K_j(p))=e_p(j)`. (A3)". The
Legendre's-formula identity itself, `v_p((jp-1)!)=(j-1)+v_p((j-1)!)`, is a genuinely self-contained
number-theoretic fact, independent of the combinatorial claim about `K_j(p)`'s coefficient (which
needs this project's `K_r(q)` machinery from `ConnectedCumulant.lean` and is not addressed here) —
formalized here on its own.

**`factorization_factorial_mul_sub_one`**: `v_p((jp-1)!)=(j-1)+v_p((j-1)!)` for `j≥1`. Proof: by
Mathlib's `Nat.Choose.Factorization.factorization_factorial_mul` (`v_p((pn)!)=v_p(n!)+n`) applied
at `n=j`, `v_p((jp)!)=v_p(j!)+j`; splitting `(jp)!=(jp)\cdot(jp-1)!` and `j!=j\cdot(j-1)!` via
`Nat.factorial_succ`, and using `v_p(jp)=v_p(j)+v_p(p)=v_p(j)+1` (`p` prime), the `v_p(j)` terms
cancel, leaving exactly `v_p((jp-1)!)=(j-1)+v_p((j-1)!)`. **Honest scope note**: this is the
numeric identity only, not the surrounding combinatorial claim about `K_j(p)`'s coefficient of
`X_{jp}`, nor the rest of (A3)'s sharpness argument.
-/

/-- `v_p((jp-1)!) = (j-1)+v_p((j-1)!)` — the Legendre's-formula identity `e_p(j)=v_p((jp-1)!)`
from (A3). -/
theorem factorization_factorial_mul_sub_one {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) :
    (Nat.factorial (j * p - 1)).factorization p =
      (j - 1) + (Nat.factorial (j - 1)).factorization p := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, (j' + 1) * p = m + 1 := by
    refine ⟨(j' + 1) * p - 1, ?_⟩
    have : 1 ≤ (j' + 1) * p := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.succ_ne_zero j') hp.pos.ne')
    omega
  rw [hm]
  simp only [Nat.add_sub_cancel]
  have hstep1 : (Nat.factorial (m + 1)).factorization p =
      (Nat.factorial (j' + 1)).factorization p + (j' + 1) := by
    rw [← hm, mul_comm]
    exact Nat.factorization_factorial_mul hp
  have hstep2 : (Nat.factorial (m + 1)).factorization p =
      (m + 1).factorization p + (Nat.factorial m).factorization p := by
    rw [Nat.factorial_succ, Nat.factorization_mul (Nat.succ_ne_zero m) (Nat.factorial_ne_zero m),
      Finsupp.add_apply]
  have hstep3 : (m + 1).factorization p = (j' + 1).factorization p + p.factorization p := by
    rw [← hm, Nat.factorization_mul (Nat.succ_ne_zero j') hp.pos.ne', Finsupp.add_apply]
  have hstep4 : p.factorization p = 1 := hp.factorization_self
  have hstep5 : (Nat.factorial (j' + 1)).factorization p =
      (j' + 1).factorization p + (Nat.factorial j').factorization p := by
    rw [Nat.factorial_succ,
      Nat.factorization_mul (Nat.succ_ne_zero j') (Nat.factorial_ne_zero j'), Finsupp.add_apply]
  omega
