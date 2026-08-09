import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**The island as a self-contained partitioned instance.** `IslandBlockIdx g u c0` indexes the
island's own blocks: `none` for the virtual root (the attachment points of `V u` reaching `c0`),
`some i` for each actual block `i` of the component `c0`. `IslandV` gives these as `Finset`s of
the island subtype, and `islandV_isPartition`/`islandV_nonempty` confirm they form a genuine
partition with every block nonempty — exactly the `IsPartition`/`hne` hypotheses `card_le_root_
bound` needs, once the island's own group action and centralizing permutation are built (next).
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- The blocks of an island: `none` for the virtual root (`V u`'s own attachment points),
`some i` for each actual block `i` of the component `c0`. -/
abbrev IslandBlockIdx {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι) (c0 : BlockComponent V g u) :
    Type _ :=
  Option {i : {i : ι // i ≠ u} // Quot.mk (BlockReach V g u) i = c0}

noncomputable instance {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι) (c0 : BlockComponent V g u) :
    Fintype (IslandBlockIdx g u c0) := by unfold IslandBlockIdx; infer_instance

noncomputable instance {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι) (c0 : BlockComponent V g u) :
    DecidableEq (IslandBlockIdx g u c0) := Classical.decEq _

/-- The blocks of the island, as `Finset`s of the island subtype. -/
noncomputable def IslandV {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι) (c0 : BlockComponent V g u) :
    IslandBlockIdx g u c0 → Finset {x : Ω // InComponentPlus g u c0 x}
  | none => (V u).subtype (InComponentPlus g u c0)
  | some i => (V i.1.1).subtype (InComponentPlus g u c0)

theorem mem_islandV_none {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι) (c0 : BlockComponent V g u)
    (x : {x : Ω // InComponentPlus g u c0 x}) :
    x ∈ IslandV g u c0 none ↔ x.1 ∈ V u := by
  simp [IslandV, Finset.mem_subtype]

theorem mem_islandV_some {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι) (c0 : BlockComponent V g u)
    (i : {i : {i : ι // i ≠ u} // Quot.mk (BlockReach V g u) i = c0})
    (x : {x : Ω // InComponentPlus g u c0 x}) :
    x ∈ IslandV g u c0 (some i) ↔ x.1 ∈ V i.1.1 := by
  simp [IslandV, Finset.mem_subtype]

/-- The island's own blocks partition the island. -/
theorem islandV_isPartition {V : ι → Finset Ω} (hpart : IsPartition V) (g : Equiv.Perm Ω) (u : ι)
    (c0 : BlockComponent V g u) : IsPartition (IslandV g u c0) := by
  intro x
  obtain ⟨b, hb, hbuniq⟩ := hpart x.1
  by_cases hbu : b = u
  · refine ⟨none, (mem_islandV_none g u c0 x).mpr (hbu ▸ hb), ?_⟩
    intro j hj
    rcases j with _ | i
    · rfl
    · exfalso
      have h1 := hbuniq i.1.1 ((mem_islandV_some g u c0 i x).mp hj)
      exact i.1.2 (h1.trans hbu)
  · have hxi : ∃ i : {i : ι // i ≠ u}, Quot.mk (BlockReach V g u) i = c0 ∧ x.1 ∈ V i.1 := by
      rcases x.2 with ⟨i, hi, hxi⟩ | ⟨hxu, -⟩
      · exact ⟨i, hi, hxi⟩
      · exact absurd (hbuniq u hxu).symm hbu
    obtain ⟨i, hi, hxi⟩ := hxi
    refine ⟨some ⟨i, hi⟩, (mem_islandV_some g u c0 ⟨i, hi⟩ x).mpr hxi, ?_⟩
    intro j hj
    rcases j with _ | i'
    · exfalso
      exact hbu (hbuniq u ((mem_islandV_none g u c0 x).mp hj)).symm
    · have h1 := hbuniq i.1 hxi
      have h2 := hbuniq i'.1.1 ((mem_islandV_some g u c0 i' x).mp hj)
      have h3 : i.1 = i'.1.1 := h1.trans h2.symm
      congr 1
      exact Subtype.ext (Subtype.ext h3).symm

theorem islandV_nonempty {V : ι → Finset Ω} (hne : ∀ i, (V i).Nonempty)
    (g : Equiv.Perm Ω) (u : ι) (c0 : BlockComponent V g u) {p₀ : Ω}
    (hp₀u : p₀ ∈ V u) (hreach : Reaches g u p₀ c0) :
    ∀ b : IslandBlockIdx g u c0, (IslandV g u c0 b).Nonempty := by
  intro b
  rcases b with _ | i
  · exact ⟨⟨p₀, Or.inr ⟨hp₀u, hreach⟩⟩, (mem_islandV_none g u c0 _).mpr hp₀u⟩
  · obtain ⟨q, hq⟩ := hne i.1.1
    exact ⟨⟨q, Or.inl ⟨i.1, i.2, hq⟩⟩, (mem_islandV_some g u c0 i _).mpr hq⟩
