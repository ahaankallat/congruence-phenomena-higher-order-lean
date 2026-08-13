import Mathlib
import CongruenceTheoryHigherOrder.CompletePrimeLocalDefect

/-!
**`Delta`'s invariance under reindexing the tuple.** `Delta n = C(\sum_i n_i) - \prod_i C(n_i)`
depends on `n` only through its sum and its product of `C`-images — both manifestly invariant
under precomposing `n` with any permutation of the index type. This lets `thm:complete-prime-
local`'s per-shape case theorems (stated for the *canonical* tuple shapes `p\cdot u` and
`Fin.cons a (p\cdot u)`) be applied to a tuple `n` in *any* order, by reindexing to the canonical
shape, invoking the case theorem, and transporting the conclusion back along the same
permutation — since `cont`/`Dgcd` depend on `Delta n` only, this transport is immediate once
`Delta (n ∘ σ) = Delta n` is established.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`Delta` is invariant under reindexing** by any permutation of `Fin r`. -/
theorem Delta_comp_equiv {r : ℕ} (n : Fin r → ℕ) (σ : Equiv.Perm (Fin r)) :
    Delta (n ∘ σ) = Delta n := by
  unfold Delta
  congr 1
  · congr 1
    exact Fintype.sum_equiv σ (fun i => n (σ i)) n (fun i => rfl)
  · exact Fintype.prod_equiv σ (fun i => C (n (σ i))) (fun i => C (n i)) (fun i => rfl)

#print axioms Delta_comp_equiv

end CongruenceTheory
