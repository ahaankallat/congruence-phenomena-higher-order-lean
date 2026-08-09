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
**The `hmixed` hypothesis for the island.** Every point of the virtual-root block reaches outside
it via an island-native cycle — directly what `card_le_root_bound` needs, built from `Reaches`'s
own witness data (reusing `Reaches` rather than re-deriving connectivity from scratch).
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- Every attachment point (island point in the virtual root `none`) reaches `c0`, i.e. its
`InComponentPlus` witness must be the `Reaches` disjunct (the `V i` disjunct is impossible, since
`V` is a partition and `p.1 ∈ V u` already). -/
theorem reaches_of_mem_islandV_none {V : ι → Finset Ω} {g : Equiv.Perm Ω} {u : ι}
    (hpart : IsPartition V) {c0 : BlockComponent V g u}
    (p : {x : Ω // InComponentPlus g u c0 x}) (hp : p.1 ∈ V u) : Reaches g u p.1 c0 := by
  rcases p.2 with ⟨j, hj, hxj⟩ | ⟨-, hreachp⟩
  · exfalso
    obtain ⟨i0, hi0, huniq⟩ := hpart p.1
    have h1 := huniq u hp
    have h2 := huniq j.1 hxj
    exact j.2 (h2.trans h1.symm)
  · exact hreachp

/-- The `hmixed` hypothesis for the island: every point of the virtual root (`none`'s block)
has an island-cycle reaching outside it, since `Reaches` gives a witness point in some `c0` block,
which (being outside `V u`) can never lie in `none`'s block. -/
theorem island_hmixed {V : ι → Finset Ω} (hpart : IsPartition V) (g : Equiv.Perm Ω) (u : ι)
    (c0 : BlockComponent V g u) :
    ∀ p ∈ IslandV g u c0 none, ∃ y ∉ IslandV g u c0 none,
      (islandG hpart g u c0).SameCycle p y := by
  intro p hp
  rw [mem_islandV_none] at hp
  obtain ⟨x1, hx1, y1, hy1, hpy1⟩ := reaches_of_mem_islandV_none hpart p hp
  have hy1' : InComponentPlus g u c0 y1 := Or.inl ⟨x1, hx1, hy1⟩
  refine ⟨⟨y1, hy1'⟩, ?_, (islandG_sameCycle_iff hpart g u c0 p ⟨y1, hy1'⟩).mpr hpy1⟩
  rw [mem_islandV_none]
  intro hy1u
  obtain ⟨i0, hi0, huniq⟩ := hpart y1
  have h1 := huniq u hy1u
  have h2 := huniq x1.1 hy1
  exact x1.2 (h2.trans h1.symm)
