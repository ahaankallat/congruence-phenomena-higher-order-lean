import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.Perm
import CongruenceTheory.CpermEqC
import CongruenceTheory.CoeffExtraction
import CongruenceTheory.ContentBounds
import CongruenceTheoryHigherOrder.ConnectedCumulant

/-!
**The all-fixed-points coefficient of `K_1(q)=C_q`.** The identity permutation is the unique one
with `cycleType=0`, giving `[X_1^q]K_1(q)=1` exactly — the elementary fact behind the "trivial
part" (singleton microblock) contribution to a shape's canonical monomial in
`thm:common-prime-classification`'s witness-depth argument.
-/

namespace CongruenceTheory

open scoped Classical

theorem coeff_single_one_K_one (q : ℕ) :
    MvPolynomial.coeff (Finsupp.single 1 q) (K 1 q) = 1 := by
  rw [K_one, ← Cperm_eq_C]
  unfold Cperm
  have hcast := coeff_sum_ci_eq_card_cycleType (α := Fin q) (0 : Multiset ℕ) (by simp)
  simp only [Multiset.sum_zero, Nat.sub_zero, Fintype.card_fin] at hcast
  rw [show (Finsupp.single 1 q : ℕ →₀ ℕ) = ciExp q (0 : Multiset ℕ) from by
    unfold ciExp; simp]
  rw [hcast, card_cycleType_zero]
  norm_num

#print axioms coeff_single_one_K_one

end CongruenceTheory
