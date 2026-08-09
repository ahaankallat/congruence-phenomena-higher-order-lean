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
**Macroblock/microblock relabeling for (A4)**: with `q = Q*p`, relates a macroblock-level
permutation's touches relation to the touches relation of its microblock-relabeled transport.
-/

namespace CongruenceTheory

open Equiv

open scoped Classical

variable {r Q p : ℕ}

/-- Relabels `Fin r × Fin (Q*p)` as `(Fin r × Fin Q) × Fin p` (macroblocks split into
`Q` microblocks of size `p`), keeping the macroblock component fixed. -/
def macroMicroEquiv (r Q p : ℕ) : Fin r × Fin (Q * p) ≃ (Fin r × Fin Q) × Fin p :=
  (Equiv.refl (Fin r)).prodCongr (finProdFinEquiv (m := Q) (n := p)).symm |>.trans
    (Equiv.prodAssoc (Fin r) (Fin Q) (Fin p)).symm

theorem macroMicroEquiv_fst (x : Fin r × Fin (Q * p)) :
    ((macroMicroEquiv r Q p) x).1.1 = x.1 := rfl

theorem genTouches_macro_iff_micro (g : Equiv.Perm (Fin r × Fin (Q * p))) (i j : Fin r) :
    genTouches g i j ↔
      ∃ y : (Fin r × Fin Q) × Fin p, y.1.1 = i ∧
        (((macroMicroEquiv r Q p).permCongr g) y).1.1 = j := by
  set E := macroMicroEquiv r Q p with hE_def
  unfold genTouches
  constructor
  · rintro ⟨x, hx1, hx2⟩
    refine ⟨E x, ?_, ?_⟩
    · rw [macroMicroEquiv_fst]; exact hx1
    · show (E (g (E.symm (E x)))).1.1 = j
      rw [Equiv.symm_apply_apply, macroMicroEquiv_fst]
      exact hx2
  · rintro ⟨y, hy1, hy2⟩
    refine ⟨E.symm y, ?_, ?_⟩
    · rw [show (E.symm y).1 = (E (E.symm y)).1.1 from (macroMicroEquiv_fst (E.symm y)).symm,
        Equiv.apply_symm_apply]
      exact hy1
    · show (g (E.symm y)).1 = j
      rw [← hy2]
      show (g (E.symm y)).1 = (E (g (E.symm y))).1.1
      exact (macroMicroEquiv_fst (g (E.symm y))).symm

end CongruenceTheory
