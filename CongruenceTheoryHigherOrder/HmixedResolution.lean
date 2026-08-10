import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound

/-!
**Resolving the `hmixed` gap flagged in the manuscript's data-availability paragraph.**

The general two-root bound (A2a) takes `hmixed` (`∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y`, "every
point of the block is on a cycle reaching outside it") as a blanket hypothesis, and the manuscript
notes this had not been derived from the weaker "connected block-support hypergraph" hypothesis
available at the theorem's only actual use site.

Tracing that use site (the second, general-`q` invocation of (A2a) inside the proof of
`thm:atomic-connected-content`: "for a connected permutation let `R_i>0` be the number of points
in block `i` lying on mixed cycles... the image satisfies (A2a)") shows (A2a) is never applied to
the manuscript's original size-`q` blocks `V_i` directly. It is applied to the *restriction* of
each block to just its own mixed points, i.e. blocks of size `R_i`. `hmixed_of_restriction` below
proves that for exactly this restriction, `hmixed` holds automatically, by a one-line argument: if
`S` is defined as "the points of `V` that reach outside `V`", then `S ⊆ V`, so anything outside `V`
is outside `S` too, and the very witness that made a point of `S` mixed relative to `V` already
witnesses it mixed relative to `S`. No derivation from block-level connectivity is needed at all
for this half: the property survives the restriction for free, because "mixed" was already defined
relative to a *superset* of the restricted block.

**Honest scope note, correcting an overstatement in an earlier revision of this file and its
commit message**: those claimed a companion fact was *also* proved here, that the block-support
hypergraph — and hence (A2a)'s connectivity hypothesis — transfers unchanged under the same
restriction. That claim is true (a cycle only ever contributed an edge to the hypergraph when it
was already mixed, so purely within-block cycles, exactly what the restriction discards, never
contributed one), but at the time it had only been argued in prose here, not proved as its own Lean
theorem, despite the docstring saying a theorem "below" recorded it. `hconn_witness_transfers`
below now closes that gap directly, via the route this project's own connectivity hypothesis
(`hconn`, see `A2aFullInduction.lean`/`A2aRootBound.lean`) is actually stated in: as witnesses
`x ∈ V i`, `y ∈ V j` (`i ≠ j`), `g.SameCycle x y`. It shows any such witness already lies in the
mixed-point restrictions `S i`, `S j`, so `hconn` for the original blocks transfers termwise to
`hconn` for the restricted blocks, without needing a general hypergraph-equality formalism.
-/

open Equiv

open scoped Classical

variable {Ω ι : Type*} [DecidableEq Ω]

/-- **The core `hmixed` resolution.** If `S` is exactly the subset of `V` consisting of points
that are `g`-related (via `SameCycle`) to some point outside `V`, then every point of `S` is
`g`-related to a point outside `S` too — not just outside the larger `V`. The witness is literally
the same one: `S ⊆ V` means anything outside `V` is automatically outside `S`. -/
theorem mixed_restricted_still_mixed (V : Finset Ω) (g : Equiv.Perm Ω)
    (S : Finset Ω) (hS : S = V.filter (fun p => ∃ y ∉ V, g.SameCycle p y)) :
    ∀ p ∈ S, ∃ y ∉ S, g.SameCycle p y := by
  intro p hp
  rw [hS, Finset.mem_filter] at hp
  obtain ⟨_hpV, y, hyV, hpy⟩ := hp
  refine ⟨y, ?_, hpy⟩
  intro hyS
  rw [hS, Finset.mem_filter] at hyS
  exact hyV hyS.1

/-- The same fact stated for a whole indexed family of blocks at once, matching how the
application actually uses it: for every block `i`, restricting `V i` to its own mixed points
(relative to `V i` itself) yields a family that already satisfies `hmixed` termwise. -/
theorem hmixed_of_restriction (V : ι → Finset Ω) (g : Equiv.Perm Ω)
    (S : ι → Finset Ω) (hS : ∀ i, S i = (V i).filter (fun p => ∃ y ∉ V i, g.SameCycle p y)) :
    ∀ i, ∀ p ∈ S i, ∃ y ∉ S i, g.SameCycle p y := by
  intro i
  exact mixed_restricted_still_mixed (V i) g (S i) (hS i)

/-- **The connectivity half, proved as its own theorem** (correcting the earlier overstatement
above): a cross-block `hconn`-style witness for the original partition `V` — `x ∈ V i`, `y ∈ V j`
with `i ≠ j`, related by `g.SameCycle` — already witnesses the same fact for the mixed-point
restrictions `S i`, `S j`. Proof: `IsPartition` makes `V i`, `V j` disjoint (`i ≠ j`), so `y ∉ V i`
and `x ∉ V j`; combined with `g.SameCycle x y` (and its symmetric form), this is exactly the
membership condition defining `S i` and `S j`. -/
theorem hconn_witness_transfers {V : ι → Finset Ω} (hpart : IsPartition V) (g : Equiv.Perm Ω)
    (S : ι → Finset Ω) (hS : ∀ i, S i = (V i).filter (fun p => ∃ y ∉ V i, g.SameCycle p y))
    {i j : ι} (hij : i ≠ j) {x y : Ω} (hx : x ∈ V i) (hy : y ∈ V j) (hxy : g.SameCycle x y) :
    x ∈ S i ∧ y ∈ S j := by
  have hynoti : y ∉ V i := by
    intro hyi
    obtain ⟨i0, -, huniq⟩ := hpart y
    exact hij ((huniq i hyi).trans (huniq j hy).symm)
  have hxnotj : x ∉ V j := by
    intro hxj
    obtain ⟨i0, -, huniq⟩ := hpart x
    exact hij ((huniq i hx).trans (huniq j hxj).symm)
  refine ⟨?_, ?_⟩
  · rw [hS i, Finset.mem_filter]
    exact ⟨hx, y, hynoti, hxy⟩
  · rw [hS j, Finset.mem_filter]
    exact ⟨hy, x, hxnotj, hxy.symm⟩
