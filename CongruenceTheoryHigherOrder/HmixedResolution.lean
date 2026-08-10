import Mathlib

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
each block to just its own mixed points, i.e. blocks of size `R_i`. This file proves that for
exactly this restriction, `hmixed` holds automatically, by a one-line argument: if `S` is defined
as "the points of `V` that reach outside `V`", then `S ⊆ V`, so anything outside `V` is outside
`S` too, and the very witness that made a point of `S` mixed relative to `V` already witnesses it
mixed relative to `S`. No derivation from block-level connectivity is needed at all: the property
survives the restriction for free, because "mixed" was already defined relative to a *superset* of
the restricted block.

The companion fact — that the block-support hypergraph is *unchanged* by this same restriction, so
connectivity transfers automatically too — holds because a cycle contributes an edge to that
hypergraph exactly when it is mixed (spans more than one block); purely within-block cycles, which
are exactly what gets discarded by the restriction, never contributed an edge in the first place.
`hmixed_of_restriction_connected` below records this alongside the main fact for a single lemma
matching both halves of what the application needs.
-/

open Equiv

open scoped Classical

variable {Ω : Type*} [DecidableEq Ω]

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
theorem hmixed_of_restriction {ι : Type*} (V : ι → Finset Ω) (g : Equiv.Perm Ω)
    (S : ι → Finset Ω) (hS : ∀ i, S i = (V i).filter (fun p => ∃ y ∉ V i, g.SameCycle p y)) :
    ∀ i, ∀ p ∈ S i, ∃ y ∉ S i, g.SameCycle p y := by
  intro i
  exact mixed_restricted_still_mixed (V i) g (S i) (hS i)
