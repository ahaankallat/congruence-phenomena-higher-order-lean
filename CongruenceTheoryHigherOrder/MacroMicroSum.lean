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
import CongruenceTheoryHigherOrder.A3Final

/-!
**The core content of (A4)'s manuscript equation**: `K_r(Q*p)` equals the sum, over microblock
partitions `τ'` of `Fin r × Fin Q` whose induced macroblock hypergraph `partGraphOf τ'` is
connected, of `∏_{B∈τ'.parts} K(|B|,p)`. Combines `GeneralizedGfunFilter.lean`'s generic
connectivity-filtered regrouping with `PartGraph.lean`'s macroblock-connectivity characterization
and `MacroMicroRelabel.lean`'s `q=Qp` relabeling.
-/

namespace CongruenceTheory

open Equiv

open scoped Classical

/-- **`K_r(Qp)` as a connectivity-filtered sum of block-products of `K(·,p)`.** The core content
of (A4)'s manuscript equation, missing only the final regrouping by partition *shape* into
`A^{\rm conn}_λ(Q;r)` (a combinatorial bookkeeping step, not attempted here). -/
theorem K_eq_sum_filter_partGraphOf_connected_prod_K (r Q p : ℕ) :
    K r (Q * p) = ∑ τ' ∈ (Finset.univ : Finset (GenPartLat (Fin r × Fin Q))).filter
        (fun τ' => ∀ i j : Fin r, (partGraphOf τ').Reachable i j),
      ∏ B ∈ τ'.parts, K B.card p := by
  have hK : GenGfun (q := Q * p) (⊤ : GenPartLat (Fin r)) = K r (Q * p) := by
    rw [genGfun_top_eq_K, Fintype.card_fin]
  have hstep : K r (Q * p) =
      ∑ g : Equiv.Perm (Fin r × Fin (Q * p)), (if genPiOf g = (⊤ : GenPartLat (Fin r))
        then ci g else 0) := by
    rw [← hK]
    unfold GenGfun
    rw [Finset.sum_filter]
  rw [hstep]
  have hpt : ∀ g : Equiv.Perm (Fin r × Fin (Q * p)),
      (if (∀ i j : Fin r, (partGraphOf
            (genPiOf ((macroMicroEquiv r Q p).permCongr g))).Reachable i j)
          then ci ((macroMicroEquiv r Q p).permCongr g) else 0) =
        (if genPiOf g = (⊤ : GenPartLat (Fin r)) then ci g else 0) := by
    intro g
    have hci : ci ((macroMicroEquiv r Q p).permCongr g) = ci g :=
      ci_permCongr (macroMicroEquiv r Q p) g
    by_cases hg : genPiOf g = (⊤ : GenPartLat (Fin r))
    · have hC : ∀ i j : Fin r, (partGraphOf
          (genPiOf ((macroMicroEquiv r Q p).permCongr g))).Reachable i j :=
        genPiOf_macro_eq_top_iff_partGraphOf_connected.mp hg
      rw [if_pos hg, if_pos hC, hci]
    · have hnC : ¬ (∀ i j : Fin r, (partGraphOf
          (genPiOf ((macroMicroEquiv r Q p).permCongr g))).Reachable i j) :=
        fun hc => hg (genPiOf_macro_eq_top_iff_partGraphOf_connected.mpr hc)
      rw [if_neg hg, if_neg hnC]
  have heq : (∑ g : Equiv.Perm (Fin r × Fin (Q * p)),
        (if genPiOf g = (⊤ : GenPartLat (Fin r)) then ci g else 0)) =
      ∑ g : Equiv.Perm (Fin r × Fin (Q * p)),
        (if (∀ i j : Fin r, (partGraphOf
              (genPiOf ((macroMicroEquiv r Q p).permCongr g))).Reachable i j)
            then ci ((macroMicroEquiv r Q p).permCongr g) else 0) :=
    (Finset.sum_congr rfl (fun g _ => hpt g)).symm
  rw [heq]
  have hsum := Equiv.sum_comp (macroMicroEquiv r Q p).permCongr
    (fun g' : Equiv.Perm ((Fin r × Fin Q) × Fin p) =>
      if (∀ i j : Fin r, (partGraphOf (genPiOf g')).Reachable i j) then ci g' else 0)
  rw [hsum]
  exact sum_ci_filter_genPiOf_eq_sum_filter_prod_K
    (fun τ' : GenPartLat (Fin r × Fin Q) => ∀ i j : Fin r, (partGraphOf τ').Reachable i j)

end CongruenceTheory
