import Mathlib
import CongruenceTheory.Basic

/-!
**Foundational setup for the atomic connected-cumulant chapter** (`thm:atomic-connected-content`
through `thm:one-singleton-repeated`), the "Hardest" tier flagged in the README: this is where
the manuscript's one *actual, previously-found-and-repaired* proof gap lived, and needs
wreath-product and hypertree (Prüfer-bijection) combinatorics with essentially no existing
Mathlib support for the deep content — comparable in scope to the entire `thm:strong` effort,
for one theorem cluster.

**What's formalized here** is the chapter's own starting definition, not yet the theorem: the
equal-block connected cumulant
`K_r(q) = ∑_{π∈Π_r} μ(π,1̂) ∏_{B∈π} C_{|B|q}`,
a Möbius-alternating sum over the partition lattice `Π_r` of `[r]`. This turns out to need
*no new infrastructure* — Mathlib already has both pieces: `Finpartition` (`Order/Partition/
Finpartition.lean`) gives the partition-lattice structure (a `PartialOrder`, `OrderTop`, and
`Fintype` instance for partitions of a finite set, ordered by refinement) and
`IncidenceAlgebra.mu` (`Combinatorics/Enumerative/IncidenceAlgebra.lean`) gives the Möbius
function of any locally finite order. `PartLat r := Finpartition (univ : Finset (Fin r))` is
`Π_r` exactly; `K` combines the two directly. `K_one` checks the manuscript's own stated base
case `K_1(q) = C_q` (the partition lattice of a single point has one partition, itself the top
element, with Möbius value `1`).

**What remains** for `thm:atomic-connected-content` itself is the deep content: the "Uniform-
hypertree Prüfer enumerator" lemma (a bijection between labelled `h`-uniform hypertrees and
Prüfer-style sequences, used to evaluate `cont K_r(q)` in closed form) and, further into the
chapter, wreath-product centralizer computations. Neither is attempted here. (A further
`K_2(q) = C_{2q} - C_q^2` sanity check — which would tie directly back to the already-proven
`thm:strong` — was attempted but abandoned: `decide` already fails to reduce at `r=2` since
`IncidenceAlgebra.mu`'s well-founded recursion isn't kernel-reducible at that scale, so it would
need a genuine non-computational proof instead, which wasn't pursued given it isn't on the path
to the chapter's real content.)
-/

namespace CongruenceTheory

open scoped Classical

/-- The partition lattice `Π_r` of `[r]`: partitions of `Finset.univ : Finset (Fin r)`. -/
abbrev PartLat (r : ℕ) := Finpartition (Finset.univ : Finset (Fin r))

noncomputable instance (r : ℕ) : LocallyFiniteOrder (PartLat r) :=
  Fintype.toLocallyFiniteOrder

noncomputable instance (r : ℕ) : OrderTop (PartLat r) := by
  unfold PartLat
  infer_instance

/-- The equal-block connected cumulant `K_r(q) = ∑_{π∈Π_r} μ(π,1̂) ∏_{B∈π} C_{|B|q}`. -/
noncomputable def K (r q : ℕ) : MvPolynomial ℕ ℤ :=
  ∑ π : PartLat r, (IncidenceAlgebra.mu ℤ π ⊤) • (∏ B ∈ π.parts, C (B.card * q))

theorem partLat_unique_of_one : ∀ π : PartLat 1, π = ⊤ := by
  decide

theorem partLat_top_parts_one : (⊤ : PartLat 1).parts = {Finset.univ} := by
  decide

/-- **The manuscript's own base case**: `K_1(q) = C_q`. -/
theorem K_one (q : ℕ) : K 1 q = C q := by
  unfold K
  rw [show (Finset.univ : Finset (PartLat 1)) = {⊤} from by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨Finset.mem_univ ⊤, fun π _ => partLat_unique_of_one π⟩]
  simp only [Finset.sum_singleton]
  rw [IncidenceAlgebra.mu_self, partLat_top_parts_one]
  simp

end CongruenceTheory
