import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.GeneralizedConnectivity
import CongruenceTheoryHigherOrder.GeneralizedConnectivityTransport
import CongruenceTheoryHigherOrder.GeneralizedConnectivityTop
import CongruenceTheoryHigherOrder.GeneralizedPartitionGluing
import CongruenceTheoryHigherOrder.GeneralizedAssembleTop
import CongruenceTheoryHigherOrder.GeneralizedPiOfAssemble
import CongruenceTheoryHigherOrder.GeneralizedGfunTopK
import CongruenceTheoryHigherOrder.GeneralizedGfunProd
import CongruenceTheoryHigherOrder.A3Final

/-!
**A connectivity-predicate-filtered sum of `ci` regroups by canonical partition `genPiOf`, and
each fiber's sum factors as a product of `K`'s** (via `genGfun_eq_prod_K`). This is the generic
regrouping step (A4)'s concrete instantiation needs: filtering permutations of `ι × Fin q` by any
decidable predicate `C` of their canonical connectivity partition `genPiOf`, the sum of `ci`
regroups over the (finitely many) partitions `τ'` satisfying `C`, each contributing
`∏_{B∈τ'.parts} K(|B|,q)`.
-/

namespace CongruenceTheory

open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- Filtering `ci`-sums by a predicate on `genPiOf` regroups into a sum of `GenGfun` over the
partitions satisfying the predicate. -/
theorem sum_ci_filter_genPiOf_eq_sum_filter_genGfun (C : GenPartLat ι → Prop) [DecidablePred C] :
    ∑ g : Equiv.Perm (ι × Fin q), (if C (genPiOf g) then ci g else 0) =
      ∑ τ' ∈ (Finset.univ : Finset (GenPartLat ι)).filter C, GenGfun (q := q) τ' := by
  rw [← Finset.sum_filter]
  have hmaps : ∀ g ∈ (Finset.univ : Finset (Equiv.Perm (ι × Fin q))).filter
      (fun g => C (genPiOf g)),
      genPiOf g ∈ (Finset.univ : Finset (GenPartLat ι)).filter C := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    exact hg
  rw [← Finset.sum_fiberwise_of_maps_to hmaps ci]
  apply Finset.sum_congr rfl
  intro τ' hτ'
  unfold GenGfun
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, h2⟩; exact h2
  · intro h2
    refine ⟨?_, h2⟩
    rw [h2]
    exact (Finset.mem_filter.mp hτ').2

/-- **The connectivity-filtered `ci`-sum equals a sum of block-products of `K`.** Combines
`sum_ci_filter_genPiOf_eq_sum_filter_genGfun` with `genGfun_eq_prod_K`. -/
theorem sum_ci_filter_genPiOf_eq_sum_filter_prod_K (C : GenPartLat ι → Prop) [DecidablePred C] :
    ∑ g : Equiv.Perm (ι × Fin q), (if C (genPiOf g) then ci g else 0) =
      ∑ τ' ∈ (Finset.univ : Finset (GenPartLat ι)).filter C, ∏ B ∈ τ'.parts, K B.card q := by
  rw [sum_ci_filter_genPiOf_eq_sum_filter_genGfun C]
  exact Finset.sum_congr rfl (fun τ' _ => genGfun_eq_prod_K τ')

end CongruenceTheory
