import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandMap
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInstance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandG
import CongruenceTheoryHigherOrder.A2aCutVertexIslandSameCycle
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**The initial-edge hypothesis for the island.** `card_le_root_bound` needs a witness edge from the
root to some other block; here the root is `none` (the virtual root of attachment points) and the
witness is extracted directly from `hreach`'s own data: `p₀`'s cycle already meets some point `y₀`
of some block `x` of `c0`, giving exactly `j₀ := some ⟨x, hx⟩` and `y₀` as an island point.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

theorem island_init_edge {V : ι → Finset Ω} (hpart : IsPartition V) (g : Equiv.Perm Ω) (u : ι)
    {p₀ : Ω} (hp₀u : p₀ ∈ V u) {c0 : BlockComponent V g u} (hreach : Reaches g u p₀ c0) :
    ∃ j₀ : IslandBlockIdx g u c0, j₀ ≠ none ∧
      ∃ y₀ : {x : Ω // InComponentPlus g u c0 x}, y₀ ∈ IslandV g u c0 j₀ ∧
        (islandG hpart g u c0).SameCycle
          (⟨p₀, Or.inr ⟨hp₀u, hreach⟩⟩ : {x : Ω // InComponentPlus g u c0 x}) y₀ := by
  obtain ⟨x, hx, y, hy, hpy⟩ := hreach
  have hyInC : InComponentPlus g u c0 y := Or.inl ⟨x, hx, hy⟩
  refine ⟨some ⟨x, hx⟩, by simp, ⟨y, hyInC⟩, ?_, ?_⟩
  · rw [mem_islandV_some]; exact hy
  · exact (islandG_sameCycle_iff hpart g u c0 _ _).mpr hpy
