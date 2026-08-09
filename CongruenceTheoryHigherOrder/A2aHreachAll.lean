import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aFullInduction
import CongruenceTheoryHigherOrder.A2aHconnFromReachable
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment

/-!
**Deriving `card_le_cutVertex_full_bound''`'s `hreach_all` hypothesis from ordinary
block-graph connectivity.** `hreach_all` ("every component of the `ι∖{u}` block-adjacency
structure has some point of `V u` reaching it") is the cut-vertex analog of `A2aFullInduction.lean`'s
`hconn` — flagged in the README as part of the same untranslated "connected block-support
hypergraph" hypothesis. This is the standard graph-theory fact that if a graph is connected, every
component left over after deleting a vertex `u` must have an edge back to `u` — otherwise that
component, having no edge to `u` and (by definition of "component of `G∖u`") no edge to any other
component either, would be an isolated piece of the original graph, contradicting connectivity.
-/

namespace CongruenceTheory

open Equiv

open scoped Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- **`hreach_all` from ordinary graph connectivity.** -/
theorem hreach_all_of_forall_reachable {V : ι → Finset Ω} {g : Equiv.Perm Ω} {u : ι}
    (hreach : ∀ i j : ι, (blockGraphOf V g).Reachable i j) :
    ∀ c : BlockComponent V g u, ∃ q ∈ V u, Reaches g u q c := by
  intro c
  obtain ⟨x0, hx0eq⟩ := Quot.exists_rep c
  have hkey : ∀ {b : ι}, Relation.ReflTransGen (blockGraphOf V g).Adj x0.1 b →
      (∃ hb : b ≠ u, Quot.mk (BlockReach V g u) (⟨b, hb⟩ : {x : ι // x ≠ u}) = c) ∨
        (∃ q ∈ V u, Reaches g u q c) := by
    intro b hb
    induction hb with
    | refl => exact Or.inl ⟨x0.2, hx0eq⟩
    | @tail y z _ hyz ih =>
      rcases ih with ⟨hyne, hyeq⟩ | hex
      · by_cases hzu : z = u
        · subst hzu
          unfold blockGraphOf at hyz
          rw [SimpleGraph.fromRel_adj] at hyz
          rcases hyz.2 with ⟨qx, hqx, qy, hqy, hxy⟩ | ⟨qx, hqx, qy, hqy, hxy⟩
          · exact Or.inr ⟨qy, hqy, ⟨⟨y, hyne⟩, hyeq, qx, hqx, hxy.symm⟩⟩
          · exact Or.inr ⟨qx, hqx, ⟨⟨y, hyne⟩, hyeq, qy, hqy, hxy⟩⟩
        · have hadj : BlockAdjSub V g u ⟨y, hyne⟩ ⟨z, hzu⟩ := by
            unfold blockGraphOf at hyz
            rw [SimpleGraph.fromRel_adj] at hyz
            rcases hyz.2 with h1 | h1
            · exact h1
            · obtain ⟨qx, hqx, qy, hqy, hxy⟩ := h1
              exact ⟨qy, hqy, qx, hqx, hxy.symm⟩
          have hzeq : Quot.mk (BlockReach V g u) (⟨z, hzu⟩ : {x : ι // x ≠ u}) = c := by
            rw [← hyeq]
            exact (Quot.sound (Relation.EqvGen.rel _ _ hadj)).symm
          exact Or.inl ⟨hzu, hzeq⟩
      · exact Or.inr hex
  have hru : Relation.ReflTransGen (blockGraphOf V g).Adj x0.1 u := by
    have h := hreach x0.1 u
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    exact h
  rcases hkey hru with
    ⟨hune, _⟩ | hex
  · exact absurd rfl hune
  · exact hex

end CongruenceTheory
