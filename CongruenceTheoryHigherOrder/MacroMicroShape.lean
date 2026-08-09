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
import CongruenceTheoryHigherOrder.MacroMicroRelabel
import CongruenceTheoryHigherOrder.MacroMicroReach
import CongruenceTheoryHigherOrder.PartGraph
import CongruenceTheoryHigherOrder.GeneralizedGfunFilter
import CongruenceTheoryHigherOrder.MacroMicroSum
import CongruenceTheoryHigherOrder.PartitionShape
import CongruenceTheoryHigherOrder.A3Final

/-!
**`K_r(Qp)` as a partition-shape-weighted sum**: the final regrouping step, combining
`MacroMicroSum.lean`'s connectivity-filtered sum with `PartitionShape.lean`'s generic
shape-regrouping mechanism. This is the closest this project comes to the manuscript's literal
`K_r(q)=Σ_λ A^{\rm conn}_λ(Q;r)C_p^{m_1}∏_{j≥2}K_j(p)^{m_j}`; see the **honest scope note** below
for exactly what is and isn't verified to match the manuscript's own notation.
-/

namespace CongruenceTheory

open scoped Classical

/-- The set of macro-connected microblock partitions, filtered as in
`K_eq_sum_filter_partGraphOf_connected_prod_K`. -/
noncomputable def connSet (r Q : ℕ) : Finset (GenPartLat (Fin r × Fin Q)) :=
  (Finset.univ : Finset (GenPartLat (Fin r × Fin Q))).filter
    (fun τ' => ∀ i j : Fin r, (partGraphOf τ').Reachable i j)

/-- **`K_r(Qp)` as a partition-shape-weighted sum.** `shapeCount (connSet r Q) lam` is exactly
the manuscript's `A^{\rm conn}_λ(Q;r)` *if* the manuscript's own definition of that enumerator
agrees with "number of macro-connected microblock partitions of shape `lam`" — a correspondence
this file does not independently verify (see the honest scope note in the README). -/
theorem K_eq_sum_shapeCount_prod_K (r Q p : ℕ) :
    K r (Q * p) = ∑ lam ∈ (connSet r Q).image GenPartLatShape,
      (shapeCount (connSet r Q) lam) • ((lam.map (fun j => K j p)).prod) := by
  rw [K_eq_sum_filter_partGraphOf_connected_prod_K r Q p]
  exact sum_prod_K_eq_sum_shapeCount (connSet r Q) p

end CongruenceTheory
