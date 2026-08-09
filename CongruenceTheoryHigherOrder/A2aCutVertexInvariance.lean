import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**`g`-invariance of a component plus its attachment points**, toward restricting the cut-vertex
problem to one self-contained "island" (a component `c`'s own blocks, together with the points of
`V u` whose cycle reaches `c`). `InComponentPlus g u c x` is membership in this island;
`inComponentPlus_iff` shows it is exactly `g`-invariant (`x` is in the island iff `g x` is): a
single `g`-cycle can never cross between two *different* components (that would make them
adjacent, i.e. the same component by definition of `BlockReach`), and a point of `V u` reaching
component `c` stays "in the island" under `g` for the same reason. This is the structural fact
needed to legitimately restrict `g`, and eventually a suitable subgroup of `A`, to act purely
within one component at a time — the key remaining step for assembling (A2a)'s full cut-vertex
numeric bound.
-/

open Equiv

variable {Ω ι : Type*} [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- The union of a component's own blocks, plus the points of `V u` reaching it. -/
def InComponentPlus {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι) (c : BlockComponent V g u)
    (x : Ω) : Prop :=
  (∃ i : {i : ι // i ≠ u}, Quot.mk (BlockReach V g u) i = c ∧ x ∈ V i.1) ∨
    (x ∈ V u ∧ Reaches g u x c)

theorem inComponentPlus_apply {V : ι → Finset Ω} (hpart : IsPartition V) {g : Equiv.Perm Ω}
    {u : ι} {c : BlockComponent V g u} {x : Ω} (hx : InComponentPlus g u c x) :
    InComponentPlus g u c (g x) := by
  have hself : g.SameCycle x (g x) := ⟨1, by simp⟩
  rcases hx with ⟨i, hi, hxi⟩ | ⟨hxu, hreach⟩
  · obtain ⟨j0, hj0, -⟩ := hpart (g x)
    by_cases hju : j0 = u
    · right
      rw [hju] at hj0
      exact ⟨hj0, i, hi, x, hxi, hself.symm⟩
    · left
      refine ⟨⟨j0, hju⟩, ?_, hj0⟩
      rw [← hi]
      exact Quot.sound (Relation.EqvGen.rel _ _ ⟨g x, hj0, x, hxi, hself.symm⟩)
  · obtain ⟨x1, hx1, y1, hy1, hpy1⟩ := hreach
    obtain ⟨j0, hj0, -⟩ := hpart (g x)
    by_cases hju : j0 = u
    · right
      rw [hju] at hj0
      exact ⟨hj0, x1, hx1, y1, hy1, hself.symm.trans hpy1⟩
    · left
      refine ⟨⟨j0, hju⟩, ?_, hj0⟩
      rw [← hx1]
      exact Quot.sound (Relation.EqvGen.rel _ _ ⟨g x, hj0, y1, hy1, hself.symm.trans hpy1⟩)

theorem inComponentPlus_apply_inv {V : ι → Finset Ω} (hpart : IsPartition V) {g : Equiv.Perm Ω}
    {u : ι} {c : BlockComponent V g u} {x : Ω} (hx : InComponentPlus g u c x) :
    InComponentPlus g u c (g⁻¹ x) := by
  have hself : g.SameCycle x (g⁻¹ x) := ⟨-1, by simp⟩
  rcases hx with ⟨i, hi, hxi⟩ | ⟨hxu, hreach⟩
  · obtain ⟨j0, hj0, -⟩ := hpart (g⁻¹ x)
    by_cases hju : j0 = u
    · right
      rw [hju] at hj0
      exact ⟨hj0, i, hi, x, hxi, hself.symm⟩
    · left
      refine ⟨⟨j0, hju⟩, ?_, hj0⟩
      rw [← hi]
      exact Quot.sound (Relation.EqvGen.rel _ _ ⟨g⁻¹ x, hj0, x, hxi, hself.symm⟩)
  · obtain ⟨x1, hx1, y1, hy1, hpy1⟩ := hreach
    obtain ⟨j0, hj0, -⟩ := hpart (g⁻¹ x)
    by_cases hju : j0 = u
    · right
      rw [hju] at hj0
      exact ⟨hj0, x1, hx1, y1, hy1, hself.symm.trans hpy1⟩
    · left
      refine ⟨⟨j0, hju⟩, ?_, hj0⟩
      rw [← hx1]
      exact Quot.sound (Relation.EqvGen.rel _ _ ⟨g⁻¹ x, hj0, y1, hy1, hself.symm.trans hpy1⟩)

/-- `InComponentPlus` is `g`-invariant. -/
theorem inComponentPlus_iff {V : ι → Finset Ω} (hpart : IsPartition V) {g : Equiv.Perm Ω}
    {u : ι} {c : BlockComponent V g u} (x : Ω) :
    InComponentPlus g u c x ↔ InComponentPlus g u c (g x) := by
  constructor
  · exact inComponentPlus_apply hpart
  · intro hgx
    have h := inComponentPlus_apply_inv hpart hgx
    simpa using h
