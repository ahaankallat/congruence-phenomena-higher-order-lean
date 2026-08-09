import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.WreathProduct
import CongruenceTheoryHigherOrder.Semiregularity

/-!
**Conjugation-invariance of connectedness, for (A1)**: the manuscript's proof of inequality (A1)
needs the wreath product `C_q^r ⋊ S_r` to act "by conjugation on connected permutations of every
fixed cycle type" — implicitly using that conjugating a connected permutation stays connected.
This file proves exactly that: **`piOf_conj_eq_top`**, if `g` is connected (`π(g) = ⊤`,
`ConnectedCount.lean`) and `w : Wreath r q`, then `w`'s image conjugate of `g` is connected too.

**Proof idea**: conjugating by `h := wreathToPermRotate w` relabels macroblock `i` to `w.right i`
(the block-permutation component of `w`) while leaving the *within-block* connectivity structure
otherwise intact. `touches_conj` makes this precise: `touches g i j` transfers to
`touches (h g h⁻¹) (w.right i) (w.right j)`, by tracking a witness point through the conjugation
directly via `wreathToPerm_apply`. This lifts to `graphOf`'s adjacency (`graphOf_conj_adj`, via
Mathlib's `SimpleGraph.fromRel_adj`) and then, by an induction along
`SimpleGraph.reachable_iff_reflTransGen`, to full reachability (`graphOf_conj_reachable`). Since
`g` connected means every pair of macroblocks is reachable (`reachable_of_piOf_top`), and
`w.right` is a bijection, every pair is reachable in the conjugate's graph too — hence (via the
converse direction, `piOf_eq_top_of_forall_reachable`, built directly from
`Finpartition`'s refinement order and `Finpartition.mem_part_ofSetoid_iff_rel`) the conjugate's
own connectivity partition is `⊤`.

**Honest scope note**: this closes one more piece needed for (A1) but does not assemble the
inequality itself — the "free action ⟹ group order divides set size" orbit-counting packaging and
combining across `K_r(q)`'s coefficients remain, as does all of (A2) through (A6) and Lucas'
theorem for `thm:atomic-connected-content` as a whole.
-/

namespace CongruenceTheory

open scoped Classical

theorem piOf_eq_top_of_forall_reachable {r q : ℕ} [NeZero r] {g : Equiv.Perm (Fin r × Fin q)}
    (h : ∀ a b : Fin r, (graphOf g).Reachable a b) : piOf g = ⊤ := by
  apply le_antisymm le_top
  intro b hb
  obtain rfl : b = Finset.univ :=
    Finset.mem_singleton.mp (Finpartition.parts_top_subset (Finset.univ : Finset (Fin r)) hb)
  refine ⟨(piOf g).part (Classical.arbitrary (Fin r)),
    (piOf g).part_mem.mpr (Finset.mem_univ _), ?_⟩
  intro j _
  unfold piOf
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  exact h _ j

theorem touches_conj {r q : ℕ} [NeZero q] (hq : 2 ≤ q) {g : Equiv.Perm (Fin r × Fin q)}
    {w : Wreath r q} {i j : Fin r} (hij : touches g i j) :
    touches (wreathToPermRotate r q hq w * g * (wreathToPermRotate r q hq w)⁻¹)
      (w.right i) (w.right j) := by
  set h := wreathToPermRotate r q hq w with hhdef
  obtain ⟨⟨x1, x2⟩, hx1, hx2⟩ := hij
  refine ⟨h (x1, x2), ?_, ?_⟩
  · show (h (x1, x2)).1 = w.right i
    rw [hhdef, wreathToPermRotate, wreathToPerm_apply]
    simp only at hx1; rw [hx1]
  · show (h (g (h⁻¹ (h (x1, x2))))).1 = w.right j
    have heq : h⁻¹ (h (x1, x2)) = (x1, x2) := by simp
    rw [heq, hhdef, wreathToPermRotate, wreathToPerm_apply, hx2]

theorem graphOf_conj_adj {r q : ℕ} [NeZero q] (hq : 2 ≤ q) {g : Equiv.Perm (Fin r × Fin q)}
    {w : Wreath r q} {i j : Fin r} (hadj : (graphOf g).Adj i j) :
    (graphOf (wreathToPermRotate r q hq w * g * (wreathToPermRotate r q hq w)⁻¹)).Adj
      (w.right i) (w.right j) := by
  unfold graphOf at hadj ⊢
  rw [SimpleGraph.fromRel_adj] at hadj ⊢
  refine ⟨fun he => hadj.1 (w.right.injective he), ?_⟩
  rcases hadj.2 with h1 | h1
  · exact Or.inl (touches_conj hq h1)
  · exact Or.inr (touches_conj hq h1)

theorem graphOf_conj_reachable {r q : ℕ} [NeZero q] (hq : 2 ≤ q) {g : Equiv.Perm (Fin r × Fin q)}
    {w : Wreath r q} {i j : Fin r} (hreach : (graphOf g).Reachable i j) :
    (graphOf (wreathToPermRotate r q hq w * g * (wreathToPermRotate r q hq w)⁻¹)).Reachable
      (w.right i) (w.right j) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach ⊢
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (graphOf_conj_adj hq hstep)

/-- **Conjugation by a wreath element preserves connectedness**: if `g`'s cycle-support
hypergraph is connected, so is the conjugate's, under the wreath action. -/
theorem piOf_conj_eq_top {r q : ℕ} [NeZero r] [NeZero q] (hq : 2 ≤ q)
    {g : Equiv.Perm (Fin r × Fin q)} (hg : piOf g = ⊤) (w : Wreath r q) :
    piOf (wreathToPermRotate r q hq w * g * (wreathToPermRotate r q hq w)⁻¹) = ⊤ := by
  apply piOf_eq_top_of_forall_reachable
  intro a b
  have := graphOf_conj_reachable (w := w) hq
    (reachable_of_piOf_top hg (w.right⁻¹ a) (w.right⁻¹ b))
  simpa using this

end CongruenceTheory
