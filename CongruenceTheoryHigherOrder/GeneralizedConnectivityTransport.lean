import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.GeneralizedConnectivity
import CongruenceTheoryHigherOrder.A3Final

/-!
**`genTouches`/`genGraphOf` reachability transport along an index-relabeling equivalence.**
Needed for (A4)'s local/global connectivity comparison.
-/

namespace CongruenceTheory

open Equiv

open scoped Classical

variable {q : ℕ}

theorem genTouches_permCongr {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] (e : ι ≃ ι')
    (g : Equiv.Perm (ι × Fin q)) (i j : ι) :
    genTouches ((e.prodCongr (Equiv.refl (Fin q))).permCongr g) (e i) (e j) ↔ genTouches g i j := by
  set E := e.prodCongr (Equiv.refl (Fin q)) with hE_def
  have hE1 : ∀ x : ι × Fin q, (E x).1 = e x.1 := fun x => by
    simp [hE_def, Equiv.prodCongr_apply]
  have hE2 : ∀ x' : ι' × Fin q, (E.symm x').1 = e.symm x'.1 := fun x' => by
    simp [hE_def, Equiv.prodCongr_symm, Equiv.prodCongr_apply]
  unfold genTouches
  constructor
  · rintro ⟨x', hx1, hx2⟩
    refine ⟨E.symm x', ?_, ?_⟩
    · rw [hE2, hx1, Equiv.symm_apply_apply]
    · show (g (E.symm x')).1 = j
      apply e.injective
      rw [← hE1 (g (E.symm x'))]
      exact hx2
  · rintro ⟨x, hx1, hx2⟩
    refine ⟨E x, ?_, ?_⟩
    · rw [hE1, hx1]
    · show (E (g (E.symm (E x)))).1 = e j
      rw [Equiv.symm_apply_apply, hE1, hx2]

theorem genGraphOf_reachable_permCongr_of {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι']
    (e : ι ≃ ι') (g : Equiv.Perm (ι × Fin q)) {a b : ι} (h : (genGraphOf g).Reachable a b) :
    (genGraphOf ((e.prodCongr (Equiv.refl (Fin q))).permCongr g)).Reachable (e a) (e b) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hbc ih =>
    refine ih.trans (SimpleGraph.Adj.reachable ?_)
    unfold genGraphOf at hbc ⊢
    rw [SimpleGraph.fromRel_adj] at hbc ⊢
    refine ⟨fun hcontra => hbc.1 (e.injective hcontra), ?_⟩
    rcases hbc.2 with h1 | h2
    · left; exact (genTouches_permCongr e g b c).mpr h1
    · right; exact (genTouches_permCongr e g c b).mpr h2

theorem genGraphOf_reachable_permCongr_iff {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι']
    (e : ι ≃ ι') (g : Equiv.Perm (ι × Fin q)) (a b : ι) :
    (genGraphOf ((e.prodCongr (Equiv.refl (Fin q))).permCongr g)).Reachable (e a) (e b) ↔
      (genGraphOf g).Reachable a b := by
  constructor
  · intro h
    have hround := permCongr_symm_permCongr (e.prodCongr (Equiv.refl (Fin q))) g
    have h2 := genGraphOf_reachable_permCongr_of e.symm
      ((e.prodCongr (Equiv.refl (Fin q))).permCongr g) h
    rw [show (e.prodCongr (Equiv.refl (Fin q))).symm = e.symm.prodCongr (Equiv.refl (Fin q)) from
      Equiv.prodCongr_symm e (Equiv.refl (Fin q))] at hround
    rw [hround, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h2
    exact h2
  · exact genGraphOf_reachable_permCongr_of e g

end CongruenceTheory
