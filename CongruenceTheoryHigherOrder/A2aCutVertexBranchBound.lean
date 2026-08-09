import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.A2aCutVertexComponentHom
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandMap
import CongruenceTheoryHigherOrder.A2aCutVertexIslandPerm
import CongruenceTheoryHigherOrder.A2aCutVertexIslandPermMul
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInstance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandG
import CongruenceTheoryHigherOrder.A2aCutVertexIslandHom
import CongruenceTheoryHigherOrder.A2aCutVertexIslandFactor
import CongruenceTheoryHigherOrder.A2aCutVertexIslandNone
import CongruenceTheoryHigherOrder.A2aCutVertexIslandMixed
import CongruenceTheoryHigherOrder.A2aCutVertexIslandConn
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInitEdge
import CongruenceTheoryHigherOrder.A2aCutVertexDistinguished
import CongruenceTheoryHigherOrder.A2aCutVertexBranchConfinement
import CongruenceTheoryHigherOrder.A2aCutVertexBranchOrbitStab
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.PtStabProdBound
import CongruenceTheoryHigherOrder.IslandTightBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**One branch-peel step of (A2a)'s cut-vertex case**: given a subgroup `A'` fixing block `u`
setwise, and a component `c1`, orbit-stabilizer at the component level
(`card_eq_orbit_mul_stabAmbient`) splits off the orbit size (the "`m_τ`" multiplicity) and reduces
to `StabAmbient A' c1`, which fixes `c1` setwise — letting the *same* confinement +
kernel-factorization + tight-island-bound machinery built for the manuscript's distinguished `C_0`
apply to `c1` too (this time via `stabAmbient_fixes_component` instead of a hypothesis-supplied
second root block). The result is exactly one more `a_τ·∏(R_i-1)!` factor, with a fresh kernel left
over to recurse into for the remaining components.

**This step is composable**: the fresh kernel `MonoidHom.ker (islandHom hcentS hpermS hblockS
hq1reach)` re-embeds into `Subgroup (Equiv.Perm Ω)` via `KerAmbient` applied with `A := StabAmbient
... c1`, `p₀ := q1` (`KerAmbient`'s own parameters `A`/`hcent`/`hperm`/`hblock_u`/`p₀`/`hreach` were
built generically, not hardcoded to the top-level `A`/`p₀`), so `card_le_branch_bound` can be
applied again to `KerAmbient hpart hne hcentS hpermS hblockS hq1reach` for a second component `c2`,
and so on.

Two further self-contained pieces the outer recursion will need are also now available:
`A2aCutVertexComponentComplement.lean`'s `componentMulAction_mapsTo_compl` (a subgroup fixing a
Finset of components pointwise maps the complement to itself setwise — the invariant needed so the
"unprocessed components" Finset actually shrinks under `card_eq_orbit_mul_stabAmbient`'s orbit
step) and `A2aCutVertexBaseCase.lean`'s `card_le_one_of_fixes_all_blocks` (a subgroup fixing every
block of `ι∖{u}` pointwise is trivial, since `hmixed` then forces `V u` fixed too — the base case
once every component is processed).

**Honest scope note — precisely what remains to reach the manuscript's literal cut-vertex bound**:
`card_le_cutVertex_c0_bound` (the distinguished component) and `card_le_branch_bound` (any other
single component, applied once) are both fully proved and match the manuscript's actual strategy
("adjoin `u` back to a component, so it is no longer a cut vertex, and the non-cut-vertex bound
applies to the core and every branch"). What is *not* assembled here is the outer well-founded
recursion chaining `card_le_branch_bound` across *all* remaining components until none are left.
Every individual *ingredient* that recursion needs is now proved standalone — `componentMulAction_
mapsTo_compl` (the shrinking-measure invariant), `card_le_one_of_fixes_all_blocks` (the base case),
and `card_le_branch_bound` itself (the step) — but assembling them requires: (1) a hypothesis that
every block's component is actually reachable from `V u` (so no component is left permanently
unaccounted for; not derived here, just as `hconn`'s own translation from the manuscript's
hypergraph-connectivity hypothesis is not derived in the non-cut-vertex case either); (2) correctly
threading an *accumulating* invariant through the recursion — that the acting subgroup fixes the
entire island (not just the block-set) of every component processed so far, since that is what both
`componentMulAction_mapsTo_compl` and the base case's `hfixblocks` actually need, and each
`card_le_branch_bound` step only directly hands back fixing information for the *one* component it
just peeled, not the accumulated history; (3) the strong induction on `M.card` itself packaging all
of the above, in the same style as `key_induction_rooted`
(`A2aFullInduction.lean`/`A2aLayerInduction.lean`). None of this needs *new* per-component
mathematics — `card_le_branch_bound` already supplies the one nontrivial step — but assembling the
bookkeeping is a further undertaking of the same scale
as `key_induction_rooted`'s own construction (`A2aFullInduction.lean`), not attempted here. Also not
assembled: translating the resulting literal `Nat` product bound into the manuscript's grouped
`a_0·∏_τ(a_τ)^{m_τ}·m_τ!`-style rooted-isomorphism-type form and the final `v_p` inequality via
`A2aCutVertexValuation.lean`'s two facts and `DisjointTupleSymmetry.lean`'s `m_τ!` divisibility.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

theorem card_le_branch_bound {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (c1 : BlockComponent V g u) {q1 : Ω}
    (hq1u : q1 ∈ V u) (hq1reach : Reaches g u q1 c1) :
    letI := componentMulAction hpart hne hcent' hperm' hblock_u'
    Nat.card A' ≤ Nat.card (MulAction.orbit ↥A' c1) *
      ((AmbientC0Attach g u c1).card *
        (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c1),
            Nat.factorial ((IslandV g u c1 i).card - 1)) *
        Nat.card (MonoidHom.ker
          (islandHom hpart hne
            (fun φ hφ => hcent' φ (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1 hφ))
            (fun φ hφ => hperm' φ (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1 hφ))
            (fun φ hφ => hblock_u' φ (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1 hφ))
            hq1reach))) := by
  letI := componentMulAction hpart hne hcent' hperm' hblock_u'
  set hcentS := fun φ (hφ : φ ∈ StabAmbient hpart hne hcent' hperm' hblock_u' c1) =>
    hcent' φ (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1 hφ) with hcentS_def
  set hpermS := fun φ (hφ : φ ∈ StabAmbient hpart hne hcent' hperm' hblock_u' c1) =>
    hperm' φ (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1 hφ) with hpermS_def
  set hblockS := fun φ (hφ : φ ∈ StabAmbient hpart hne hcent' hperm' hblock_u' c1) =>
    hblock_u' φ (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1 hφ) with hblockS_def
  have hstep1 := card_le_ambientAttach_mul_card_ptStab_of_component_fixed hpart hne hcentS hpermS
    hblockS (c := c1) (fun φ hφ => stabAmbient_fixes_component hpart hne hcent' hperm' hblock_u'
      c1 φ hφ) hq1u hq1reach
  have hstep2 := card_ptStab_eq_range_mul_ker hpart hne hcentS hpermS hblockS hq1reach
  have hstep3 := card_le_island_tight_bound hpart hne hcentS hpermS hblockS hq1u hq1reach
  have horbit := card_eq_orbit_mul_stabAmbient hpart hne hcent' hperm' hblock_u' c1
  rw [horbit]
  apply Nat.mul_le_mul_left
  calc Nat.card (StabAmbient hpart hne hcent' hperm' hblock_u' c1) ≤
        (AmbientC0Attach g u c1).card *
          Nat.card (PtStab (StabAmbient hpart hne hcent' hperm' hblock_u' c1) q1) := hstep1
    _ = (AmbientC0Attach g u c1).card *
          (Nat.card (MonoidHom.range (islandHom hpart hne hcentS hpermS hblockS hq1reach)) *
            Nat.card (MonoidHom.ker (islandHom hpart hne hcentS hpermS hblockS hq1reach))) := by
        rw [hstep2]
    _ ≤ (AmbientC0Attach g u c1).card *
          ((∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c1),
              Nat.factorial ((IslandV g u c1 i).card - 1)) *
            Nat.card (MonoidHom.ker (islandHom hpart hne hcentS hpermS hblockS hq1reach))) := by
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul_right _ hstep3
    _ = (AmbientC0Attach g u c1).card *
          (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c1),
              Nat.factorial ((IslandV g u c1 i).card - 1)) *
            Nat.card (MonoidHom.ker (islandHom hpart hne hcentS hpermS hblockS hq1reach)) := by
        rw [mul_assoc]
