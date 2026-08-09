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
import CongruenceTheoryHigherOrder.A3Final

/-!
**`GenGfun(⊤)` at a general index type equals `K` at its cardinality.** Transports
`K_eq_Gfun_top` (stated for `Fin r`) to an arbitrary `ι` via `Fintype.equivFin`.
-/

namespace CongruenceTheory

open Equiv

open scoped Classical

variable {q : ℕ}

/-- `GenGfun`/`genPiOf` at `ι := Fin r` are exactly `Gfun`/`piOf` from `ConnectedCount.lean`. -/
theorem genGfun_top_eq_Gfun_top (r : ℕ) : GenGfun (q := q) (⊤ : GenPartLat (Fin r)) =
    Gfun (q := q) (⊤ : PartLat r) := rfl

theorem genGfun_top_permCongr_eq {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι ≃ ι') : GenGfun (q := q) (⊤ : GenPartLat ι) =
      GenGfun (q := q) (⊤ : GenPartLat ι') := by
  unfold GenGfun
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Equiv.sum_comp (e.prodCongr (Equiv.refl (Fin q))).permCongr
    (fun g : Equiv.Perm (ι' × Fin q) => if genPiOf g = ⊤ then ci g else 0)]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : genPiOf g = (⊤ : GenPartLat ι)
  · rw [if_pos hg, if_pos ((genPiOf_top_permCongr_iff e g).mpr hg), ci_permCongr]
  · rw [if_neg hg, if_neg (fun hc => hg ((genPiOf_top_permCongr_iff e g).mp hc))]

/-- **`GenGfun(⊤)` equals `K` at the index type's cardinality.** -/
theorem genGfun_top_eq_K {ι : Type*} [Fintype ι] [DecidableEq ι] :
    GenGfun (q := q) (⊤ : GenPartLat ι) = K (Fintype.card ι) q := by
  rw [genGfun_top_permCongr_eq (Fintype.equivFin ι), genGfun_top_eq_Gfun_top, ← K_eq_Gfun_top]

end CongruenceTheory
