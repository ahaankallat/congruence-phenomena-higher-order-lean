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
import CongruenceTheoryHigherOrder.A3Final

/-!
**The core lemma for (A4)**: `genAssemble p`'s global connectivity partition is exactly `τ` iff
every block's own permutation is *locally* fully connected.
-/

namespace CongruenceTheory

open Equiv

open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

theorem genGraphOf_reachable_assemble_of {τ : GenPartLat ι} (p : GenPartitionPerm (q := q) τ)
    (B : τ.parts) {a b : ↥(B : Finset ι)}
    (h : (genGraphOf ((genBlockTypeEquiv (B : Finset ι)).permCongr (p B))).Reachable a b) :
    (genGraphOf (genAssemble p)).Reachable (a : ι) (b : ι) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hbc ih =>
    refine ih.trans (SimpleGraph.Adj.reachable ?_)
    unfold genGraphOf at hbc ⊢
    rw [SimpleGraph.fromRel_adj] at hbc ⊢
    refine ⟨fun hcontra => hbc.1 (Subtype.ext hcontra), ?_⟩
    rcases hbc.2 with h1 | h2
    · left; exact (genTouches_assemble_iff p B b c).mpr h1
    · right; exact (genTouches_assemble_iff p B c b).mpr h2

/-- A point reachable (in `genAssemble p`'s connectivity graph) from a point of block `B`
stays within `B`. -/
theorem genGraphOf_reachable_assemble_mem_of {τ : GenPartLat ι} (p : GenPartitionPerm (q := q) τ)
    {B : Finset ι} (hB : B ∈ τ.parts) {a c : ι} (ha : a ∈ B)
    (h : (genGraphOf (genAssemble p)).Reachable a c) : c ∈ B := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ha
  | @tail b c _ hbc ih =>
    have hbB : b ∈ B := ih
    unfold genGraphOf at hbc
    rw [SimpleGraph.fromRel_adj] at hbc
    rcases hbc.2 with ⟨x, hx1, hx2⟩ | ⟨x, hx1, hx2⟩
    · have hmem : (genAssemble p x).1 ∈ τ.part x.1 := genRespects_assemble p x
      rw [hx1, τ.part_eq_of_mem hB hbB] at hmem
      rwa [hx2] at hmem
    · have hmem : (genAssemble p x).1 ∈ τ.part x.1 := genRespects_assemble p x
      rw [hx2, hx1] at hmem
      have hpart_eq : τ.part c = B :=
        τ.eq_of_mem_parts (τ.part_mem.mpr (Finset.mem_univ c)) hB hmem hbB
      rw [← hpart_eq]
      exact τ.mem_part_self.mpr (Finset.mem_univ c)

/-- Global reachability from `a` (with a **free** target `c`), packaged together with the
"stays in `B`" fact and the local reachability — avoids inducting on a `ReflTransGen` whose
endpoint is already a fixed coerced (`Subtype`-projected) term. -/
theorem genGraphOf_reachable_assemble_mem_local_of {τ : GenPartLat ι}
    (p : GenPartitionPerm (q := q) τ) {B : Finset ι} (hB : B ∈ τ.parts) {a : ι} (ha : a ∈ B)
    {c : ι} (h : (genGraphOf (genAssemble p)).Reachable a c) :
    ∃ hc : c ∈ B, (genGraphOf ((genBlockTypeEquiv B).permCongr
      (p ⟨B, hB⟩))).Reachable (⟨a, ha⟩ : ↥B) ⟨c, hc⟩ := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ⟨ha, SimpleGraph.Reachable.refl _⟩
  | @tail c d hac hcd ih =>
    obtain ⟨hc, ihloc⟩ := ih
    have hglobal_ad : (genGraphOf (genAssemble p)).Reachable a d := by
      rw [SimpleGraph.reachable_iff_reflTransGen]
      exact hac.tail hcd
    have hdB : d ∈ B := genGraphOf_reachable_assemble_mem_of p hB ha hglobal_ad
    refine ⟨hdB, ihloc.trans (SimpleGraph.Adj.reachable ?_)⟩
    unfold genGraphOf at hcd ⊢
    rw [SimpleGraph.fromRel_adj] at hcd ⊢
    refine ⟨fun hcontra => hcd.1 (congrArg Subtype.val hcontra), ?_⟩
    rcases hcd.2 with h1 | h2
    · left; exact (genTouches_assemble_iff p ⟨B, hB⟩ ⟨c, hc⟩ ⟨d, hdB⟩).mp h1
    · right; exact (genTouches_assemble_iff p ⟨B, hB⟩ ⟨d, hdB⟩ ⟨c, hc⟩).mp h2

theorem genGraphOf_reachable_assemble_iff {τ : GenPartLat ι} (p : GenPartitionPerm (q := q) τ)
    {B : Finset ι} (hB : B ∈ τ.parts) (a b : ↥B) :
    (genGraphOf (genAssemble p)).Reachable (a : ι) (b : ι) ↔
      (genGraphOf ((genBlockTypeEquiv B).permCongr (p ⟨B, hB⟩))).Reachable a b := by
  constructor
  · intro h
    obtain ⟨hb, hloc⟩ := genGraphOf_reachable_assemble_mem_local_of p hB a.2 h
    have hbeq : (⟨(b : ι), hb⟩ : ↥B) = b := Subtype.ext rfl
    rwa [hbeq] at hloc
  · exact genGraphOf_reachable_assemble_of p ⟨B, hB⟩

/-- **The core lemma for (A4)**: `genAssemble p`'s connectivity partition is exactly `τ` iff
every block's own permutation is locally fully connected. -/
theorem genPiOf_assemble_eq_tau_iff {τ : GenPartLat ι} (p : GenPartitionPerm (q := q) τ) :
    genPiOf (genAssemble p) = τ ↔
      ∀ B : τ.parts, genPiOf ((genBlockTypeEquiv (B : Finset ι)).permCongr (p B)) =
        (⊤ : GenPartLat (B : Finset ι)) := by
  constructor
  · intro htau B
    rw [genPiOf_eq_top_iff]
    intro a b
    have hparteq : (genPiOf (genAssemble p)).part (a : ι) = (B : Finset ι) := by
      rw [htau]
      exact τ.part_eq_of_mem B.2 a.2
    have hmem : (b : ι) ∈ (genPiOf (genAssemble p)).part (a : ι) := by rw [hparteq]; exact b.2
    have hglobal_ab : (genGraphOf (genAssemble p)).Reachable (a : ι) (b : ι) :=
      Finpartition.mem_part_ofSetoid_iff_rel.mp hmem
    exact (genGraphOf_reachable_assemble_iff p B.2 a b).mp hglobal_ab
  · intro hlocal
    apply le_antisymm
    · rw [← genRespects_iff_genPiOf_le]
      exact genRespects_assemble p
    · intro s hs
      obtain ⟨a0, ha0⟩ := τ.nonempty_of_mem_parts hs
      refine ⟨(genPiOf (genAssemble p)).part a0,
        (genPiOf (genAssemble p)).part_mem.mpr (Finset.mem_univ a0), ?_⟩
      intro y hy
      have hB : s ∈ τ.parts := hs
      have hy' : (genGraphOf ((genBlockTypeEquiv s).permCongr (p ⟨s, hB⟩))).Reachable
          (⟨a0, ha0⟩ : ↥s) ⟨y, hy⟩ := by
        have hlocs := hlocal ⟨s, hB⟩
        rw [genPiOf_eq_top_iff] at hlocs
        exact hlocs ⟨a0, ha0⟩ ⟨y, hy⟩
      have hglobal : (genGraphOf (genAssemble p)).Reachable a0 y :=
        (genGraphOf_reachable_assemble_iff p hB (⟨a0, ha0⟩ : ↥s) ⟨y, hy⟩).mpr hy'
      exact Finpartition.mem_part_ofSetoid_iff_rel.mpr hglobal

end CongruenceTheory
