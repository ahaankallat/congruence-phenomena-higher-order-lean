import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandMap
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInstance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandG
import CongruenceTheoryHigherOrder.A2aCutVertexIslandSameCycle
import CongruenceTheoryHigherOrder.A2aCutVertexBoundaryEdge
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- `EqvGen` of an already-`EqvGen`-formed relation collapses back to it (needed since
`Quot.eqvGen_exact` only recovers `EqvGen (BlockReach V g u)`, not `BlockReach V g u` itself). -/
theorem blockReach_of_eqvGen {V : ι → Finset Ω} {g : Equiv.Perm Ω} {u : ι}
    {x y : {i : ι // i ≠ u}} (h : Relation.EqvGen (BlockReach V g u) x y) :
    BlockReach V g u x y := by
  induction h with
  | rel a b hab => exact hab
  | refl a => exact Relation.EqvGen.refl a
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc

/-- The `hconn` hypothesis for the island: any proper nonempty subset `L` of `c0`'s own blocks
has an edge leaving it, translating `exists_boundary_edge_of_blockReach` (a fact about the
underlying `{i≠u}` indices) into the island's `IslandBlockIdx` terms. -/
theorem island_hconn {V : ι → Finset Ω} (hpart : IsPartition V) (g : Equiv.Perm Ω) (u : ι)
    (c0 : BlockComponent V g u) :
    ∀ L : Finset (IslandBlockIdx g u c0), L.Nonempty →
      L ≠ Finset.univ.erase (none : IslandBlockIdx g u c0) →
      L ⊆ Finset.univ.erase (none : IslandBlockIdx g u c0) →
      ∃ i ∈ L, ∃ j, j ∉ L ∧ j ≠ none ∧ ∃ x ∈ IslandV g u c0 i, ∃ y ∈ IslandV g u c0 j,
        (islandG hpart g u c0).SameCycle x y := by
  intro L hLne hLuniv hLsub
  have hLsome : ∀ b ∈ L, b ≠ none := fun b hb => (Finset.mem_erase.mp (hLsub hb)).1
  obtain ⟨a, ha⟩ := hLne
  obtain ⟨a1, ha1⟩ := Option.ne_none_iff_exists.mp (hLsome a ha)
  obtain ⟨b, hbmem, hbL⟩ : ∃ b ∈ Finset.univ.erase (none : IslandBlockIdx g u c0), b ∉ L := by
    by_contra hcon
    push_neg at hcon
    exact hLuniv (Finset.Subset.antisymm hLsub hcon)
  obtain ⟨b1, hb1⟩ := Option.ne_none_iff_exists.mp (Finset.mem_erase.mp hbmem).1
  have hreach0 : BlockReach V g u a1.1 b1.1 := by
    have heq : Quot.mk (BlockReach V g u) a1.1 = Quot.mk (BlockReach V g u) b1.1 :=
      a1.2.trans b1.2.symm
    exact blockReach_of_eqvGen (Quot.eqvGen_exact heq)
  let L' : Finset {i : ι // i ≠ u} :=
    L.filterMap (fun x => x.map Subtype.val) (by
      intro a a' b hb hb'
      cases a with
      | none => simp at hb
      | some i =>
        cases a' with
        | none => simp at hb'
        | some j =>
          simp only [Option.mem_def, Option.map_some] at hb hb'
          have hij : i.1 = j.1 := Option.some.inj (hb.trans hb'.symm)
          exact congrArg some (Subtype.ext hij))
  have hmemL' : ∀ i, i ∈ L' ↔ ∃ c ∈ L, c.map Subtype.val = some i := fun i =>
    Finset.mem_filterMap ..
  have ha1L' : a1.1 ∈ L' := (hmemL' a1.1).mpr ⟨a, ha, by rw [← ha1]; rfl⟩
  have hb1L' : b1.1 ∉ L' := by
    rw [hmemL']
    rintro ⟨c, hcL, hceq⟩
    apply hbL
    have hcnone : c ≠ none := hLsome c hcL
    obtain ⟨c1, hc1⟩ := Option.ne_none_iff_exists.mp hcnone
    rw [← hc1] at hceq
    simp only [Option.map_some] at hceq
    have hval : c1.1 = b1.1 := Option.some.inj hceq
    have hc1b1 : c1 = b1 := Subtype.ext hval
    have hceqb : c = b := hc1.symm.trans ((congrArg some hc1b1).trans hb1)
    rw [← hceqb]
    exact hcL
  obtain ⟨p, hpL', q, hqL', hpq⟩ := exists_boundary_edge_of_blockReach hreach0 L' ha1L' hb1L'
  obtain ⟨cp, hcpL, hcpeq⟩ := (hmemL' p).mp hpL'
  have hcpnone : cp ≠ none := hLsome cp hcpL
  obtain ⟨p1, hp1⟩ := Option.ne_none_iff_exists.mp hcpnone
  rw [← hp1] at hcpeq
  simp only [Option.map_some] at hcpeq
  have hp1val : p1.1 = p := Option.some.inj hcpeq
  have hp1c0 : Quot.mk (BlockReach V g u) p1.1 = c0 := p1.2
  have hpc0 : Quot.mk (BlockReach V g u) p = c0 := by rw [← hp1val]; exact hp1c0
  have hpinL : (some p1 : IslandBlockIdx g u c0) ∈ L := by rw [hp1]; exact hcpL
  have hq' : Quot.mk (BlockReach V g u) p = Quot.mk (BlockReach V g u) q :=
    Quot.sound (Relation.EqvGen.rel _ _ hpq)
  have hqc0 : Quot.mk (BlockReach V g u) q = c0 := hq'.symm.trans hpc0
  have hqnotinL : (some ⟨q, hqc0⟩ : IslandBlockIdx g u c0) ∉ L := by
    intro hcontra
    apply hqL'
    exact (hmemL' q).mpr ⟨some ⟨q, hqc0⟩, hcontra, rfl⟩
  obtain ⟨x0, hx0, y0, hy0, hxy0⟩ := hpq
  have hxInC : InComponentPlus g u c0 x0 := Or.inl ⟨p, hpc0, hx0⟩
  have hyInC : InComponentPlus g u c0 y0 := Or.inl ⟨q, hqc0, hy0⟩
  refine ⟨some p1, hpinL, some ⟨q, hqc0⟩, hqnotinL, by simp, ?_⟩
  refine ⟨⟨x0, hxInC⟩, ?_, ⟨y0, hyInC⟩, ?_, ?_⟩
  · rw [mem_islandV_some, hp1val]; exact hx0
  · rw [mem_islandV_some]; exact hy0
  · exact (islandG_sameCycle_iff hpart g u c0 ⟨x0, hxInC⟩ ⟨y0, hyInC⟩).mpr hxy0
