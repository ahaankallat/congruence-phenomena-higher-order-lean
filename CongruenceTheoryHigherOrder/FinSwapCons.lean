import Mathlib

/-!
**Reindexing a tuple so a chosen index sits first**, via a transposition rather than
`Fin.insertNth`/`Fin.removeNth` (whose specific index-arithmetic proved troublesome elsewhere in
this project). For `n : Fin (t+1) → α` and any `i0 : Fin (t+1)`, `n ∘ Equiv.swap 0 i0` is *always*
exactly `Fin.cons (n i0) (fun j => n (Equiv.swap 0 i0 j.succ))` — no case split on `i0` needed,
since this is really just unwinding `Fin.cons`'s own characterization at `0` and at `succ j`.
The key extra fact `swapConsRest_ne_root`: since `Fin.succ` never hits `0`, and `swap 0 i0` is an
involution, the "rest" tuple's reindexing `swap 0 i0 ∘ Fin.succ` never lands on `i0` — so `rest`
only ever reads `n` at indices *other than* `i0`, letting hypotheses like "`n i ≠ n i0` implies
`P (n i)`" transport to `rest` directly.
-/

namespace CongruenceTheory

variable {t : ℕ} {α : Type*}

/-- **`n` composed with the `(0,i0)`-swap is `Fin.cons (n i0)` of the "rest" read through the
same swap.** -/
theorem comp_swap_eq_cons (n : Fin (t + 1) → α) (i0 : Fin (t + 1)) :
    n ∘ Equiv.swap 0 i0 = Fin.cons (n i0) (fun j => n (Equiv.swap 0 i0 j.succ)) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · show n (Equiv.swap 0 i0 0) = _
    rw [Equiv.swap_apply_left]
    simp
  · intro k
    show n (Equiv.swap 0 i0 k.succ) = _
    simp

/-- **The "rest" tuple never reads `n` at `i0`.** -/
theorem swapConsRest_ne_root (i0 : Fin (t + 1)) (j : Fin t) :
    Equiv.swap 0 i0 j.succ ≠ i0 := by
  intro h
  have := congrArg (Equiv.swap 0 i0) h
  rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
  exact (Fin.succ_ne_zero j) this

#print axioms comp_swap_eq_cons
#print axioms swapConsRest_ne_root

end CongruenceTheory
