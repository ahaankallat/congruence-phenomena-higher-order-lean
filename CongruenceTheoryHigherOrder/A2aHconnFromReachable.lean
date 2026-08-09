import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aFullInduction

/-!
**Deriving `key_induction`'s `hconn` hypothesis from ordinary graph connectivity.** Both
`A2aFullInduction.lean` and `A2aCutVertexFullBoundSharp.lean` flag the same gap: `hconn`
("every proper nonempty set of blocks has an edge leaving it") is supplied as a hypothesis
rather than derived from the manuscript's own "connected block-support hypergraph" assumption —
"a translation step, not a new mathematical difficulty, not attempted here." This file closes
exactly that step: build the block-touches graph `blockGraphOf V g` on the block index type `ι`
(mirroring `ConnectedCount.lean`/`GeneralizedConnectivity.lean`'s own `touches`/`graphOf` recipe,
adapted to an arbitrary partition `V : ι → Finset Ω` rather than the canonical product structure),
and show ordinary graph reachability between every pair of blocks implies `hconn` — the standard
graph-theory fact that a connected graph has no proper nonempty "closed" vertex subset.
-/

namespace CongruenceTheory

open Equiv

open scoped Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- Blocks `i, j` are touched by a shared `g`-cycle through representative points. -/
def blockTouches (V : ι → Finset Ω) (g : Equiv.Perm Ω) (i j : ι) : Prop :=
  ∃ x ∈ V i, ∃ y ∈ V j, g.SameCycle x y

noncomputable instance (V : ι → Finset Ω) (g : Equiv.Perm Ω) : DecidableRel (blockTouches V g) :=
  Classical.decRel _

/-- The block-support connectivity graph on `ι`, matching the manuscript's own "block-support
hypergraph." -/
noncomputable def blockGraphOf (V : ι → Finset Ω) (g : Equiv.Perm Ω) : SimpleGraph ι :=
  SimpleGraph.fromRel (blockTouches V g)

/-- **`hconn` from ordinary graph connectivity**: if every pair of blocks is reachable in the
block-support graph, then every proper nonempty set of blocks has an edge leaving it — the
standard fact that a connected graph has no nonempty proper "closed" vertex subset. -/
theorem hconn_of_forall_reachable {V : ι → Finset Ω} {g : Equiv.Perm Ω}
    (hreach : ∀ i j : ι, (blockGraphOf V g).Reachable i j) :
    ∀ L : Finset ι, L.Nonempty → L ≠ Finset.univ →
      ∃ i ∈ L, ∃ j, j ∉ L ∧ ∃ x ∈ V i, ∃ y ∈ V j, g.SameCycle x y := by
  intro L hLne hLuniv
  obtain ⟨i0, hi0⟩ := hLne
  obtain ⟨j0, hj0⟩ : ∃ j0, j0 ∉ L := by
    by_contra h
    push_neg at h
    exact hLuniv (Finset.eq_univ_of_forall h)
  have hkey : ∀ {b : ι}, Relation.ReflTransGen (blockGraphOf V g).Adj i0 b →
      b ∈ L ∨ ∃ a ∈ L, ∃ c, c ∉ L ∧ (blockGraphOf V g).Adj a c := by
    intro b hb
    induction hb with
    | refl => exact Or.inl hi0
    | @tail y z _ hyz ih =>
      rcases ih with hyL | hex
      · by_cases hzL : z ∈ L
        · exact Or.inl hzL
        · exact Or.inr ⟨y, hyL, z, hzL, hyz⟩
      · exact Or.inr hex
  have h2 : Relation.ReflTransGen (blockGraphOf V g).Adj i0 j0 := by
    rw [← SimpleGraph.reachable_iff_reflTransGen]
    exact hreach i0 j0
  rcases hkey h2 with hj0L | ⟨a, haL, c, hcL, hac⟩
  · exact absurd hj0L hj0
  · unfold blockGraphOf at hac
    rw [SimpleGraph.fromRel_adj] at hac
    rcases hac.2 with hcase | hcase
    · obtain ⟨x, hx, y, hy, hxy⟩ := hcase
      exact ⟨a, haL, c, hcL, x, hx, y, hy, hxy⟩
    · obtain ⟨x, hx, y, hy, hxy⟩ := hcase
      exact ⟨a, haL, c, hcL, y, hy, x, hx, hxy.symm⟩

/-- **`key_induction`, taking ordinary block-graph connectivity directly** (rather than the
low-level `hconn` form) as its hypothesis. -/
theorem key_induction_of_reachable {V : ι → Finset Ω} (hpart : IsPartition V) {g : Perm Ω}
    (hreach : ∀ i j : ι, (blockGraphOf V g).Reachable i j) :
    ∀ n : ℕ, ∀ L : Finset ι, (Finset.univ \ L).card ≤ n → L.Nonempty →
    ∀ A : Subgroup (Perm Ω), (∀ φ ∈ A, Commute φ g) →
    (∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) →
    (∀ i ∈ L, ∀ x ∈ V i, ∀ φ ∈ A, φ x = x) →
    Nat.card A ≤ ∏ i ∈ Lᶜ, Nat.factorial ((V i).card - 1) :=
  key_induction hpart (hconn_of_forall_reachable hreach)

end CongruenceTheory
