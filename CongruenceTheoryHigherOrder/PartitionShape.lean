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
**Regrouping a sum of block-products of `K` by partition *shape*** (the multiset of block
sizes) — the generic mechanism the manuscript's `Σ_λ A^{\rm conn}_λ(Q;r) …` regrouping needs.
Since `∏_{B∈τ'.parts} K(|B|,q)` depends on `τ'` only through the multiset of its block
cardinalities, filtering a sum of such products by any Finset `S` regroups exactly into a sum
over the distinct shapes appearing in `S`, weighted by how many elements of `S` have that shape.
-/

namespace CongruenceTheory

open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **shape** of a partition: the multiset of its block sizes. -/
noncomputable def GenPartLatShape (τ' : GenPartLat ι) : Multiset ℕ :=
  τ'.parts.val.map Finset.card

/-- The block-product of `K` depends on `τ'` only through its shape. -/
theorem prod_K_eq_shape_prod (τ' : GenPartLat ι) (q : ℕ) :
    ∏ B ∈ τ'.parts, K B.card q = ((GenPartLatShape τ').map (fun j => K j q)).prod := by
  unfold GenPartLatShape Finset.prod
  rw [Multiset.map_map]
  rfl

/-- The number of elements of `S` with shape `λ`. -/
noncomputable def shapeCount (S : Finset (GenPartLat ι)) (lam : Multiset ℕ) : ℕ :=
  (S.filter (fun τ' => GenPartLatShape τ' = lam)).card

/-- **Regrouping a filtered sum of block-products of `K` by partition shape.** -/
theorem sum_prod_K_eq_sum_shapeCount (S : Finset (GenPartLat ι)) (q : ℕ) :
    ∑ τ' ∈ S, ∏ B ∈ τ'.parts, K B.card q =
      ∑ lam ∈ S.image GenPartLatShape, (shapeCount S lam) • ((lam.map (fun j => K j q)).prod) := by
  have hmaps : ∀ τ' ∈ S, GenPartLatShape τ' ∈ S.image GenPartLatShape := by
    intro τ' hτ'
    exact Finset.mem_image_of_mem GenPartLatShape hτ'
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun τ' => ∏ B ∈ τ'.parts, K B.card q)]
  apply Finset.sum_congr rfl
  intro lam hlam
  have hconst : ∀ τ' ∈ S.filter (fun τ' => GenPartLatShape τ' = lam),
      (∏ B ∈ τ'.parts, K B.card q) = ((lam.map (fun j => K j q)).prod) := by
    intro τ' hτ'
    rw [prod_K_eq_shape_prod, (Finset.mem_filter.mp hτ').2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const]
  rfl

end CongruenceTheory
