import Mathlib

/-!
**The `(A1)`/`(A2)`-combination step of `thm:atomic-connected-content`'s exact lower bound.**
Having proved `(r-1)!q^{r-1}∣K_r(q)` (A1) and `(r-2)!q^r/\mathrm{rad}(q)∣K_r(q)` (A2), the
manuscript closes the lower-bound half of the theorem with: "The least common multiple of (A1)
and (A2) has the exponent stated in the theorem." Since `K_r(q)` is divisible by both quantities,
it is divisible by their lcm, whose `p`-adic valuation is the *maximum* of the two individual
valuations, `v_p(A1)=(r-1)t+v_p((r-1)!)` and `v_p(A2)=rt-1+v_p((r-2)!)` (for `p∣q`, `t=v_p(q)`,
using `v_p(\mathrm{rad}(q))=1`). This is a genuinely self-contained arithmetic fact, independent
of everything about `K_r(q)`, `(A1)`, or `(A2)` themselves — formalized here on its own.

**`atomic_connected_content_lower_bound`**: for `r≥2`, `t≥1`, and any `c,F1,F2` with
`F1=c+F2` (the case of interest being `c=v_p(r-1)`, `F1=v_p((r-1)!)`, `F2=v_p((r-2)!)`, related
via `(r-1)!=(r-1)·(r-2)!`),
\[
 \max\bigl((r-1)t+F_1,\;rt-1+F_2\bigr)=rt-1+F_1-\min(t-1,c),
\]
exactly the theorem's boxed valuation formula
`v_p(\operatorname{cont}K_r(q))=rt-1+v_p((r-1)!)-\min\{t-1,v_p(r-1)\}` (as a lower bound; matching
it with the *upper* bound is the content of the sharpness argument, (A3)–(A6)). Proof: case on
whether `t-1≤c`; in each case the claimed maximum is identified by direct computation
(`r*t=(r-1)*t+t`, so the two candidate valuations differ by exactly `(t-1)-c`), and `omega` closes
the resulting linear arithmetic. **Honest scope note**: this is the combination step only, not
`(A1)` or `(A2)` themselves, nor the sharpness argument that shows the bound is exact.
-/

/-- The `(A1)`/`(A2)`-combination step: `max((r-1)t+F1, rt-1+F2) = rt-1+F1-min(t-1,c)` given
`F1=c+F2`, matching the theorem's `rt-1+v_p((r-1)!)-min{t-1,v_p(r-1)}` lower bound. -/
theorem atomic_connected_content_lower_bound (r t c F1 F2 : ℕ) (hr : 2 ≤ r) (ht : 1 ≤ t)
    (hF : F1 = c + F2) :
    max ((r - 1) * t + F1) (r * t - 1 + F2) = r * t - 1 + F1 - min (t - 1) c := by
  have hrt : t ≤ r * t := Nat.le_mul_of_pos_left t (by omega)
  have hrtsub : r * t = (r - 1) * t + t := by rw [Nat.sub_mul]; omega
  by_cases h : t - 1 ≤ c
  · have hle : r * t - 1 + F2 ≤ (r - 1) * t + F1 := by omega
    rw [max_eq_left hle, min_eq_left h]
    omega
  · have hle : (r - 1) * t + F1 ≤ r * t - 1 + F2 := by omega
    rw [max_eq_right hle, min_eq_right (by omega)]
    omega
