import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aBlockPermutation

/-!
**Connected components of the block-adjacency structure on `ι ∖ {u}`**, the foundation of (A2a)'s
"`u` is a cut vertex" case. Two blocks `i,j≠u` are adjacent (`BlockAdjSub`) if some point of `V i`
and some point of `V j` share a `g`-cycle — the same adjacency notion `key_induction`/
`key_induction_rooted` already use for `hconn`. `BlockComponent` is the type of connected
components (equivalence classes of the equivalence closure `BlockReach` of this adjacency), built
via a raw `Quot` rather than `Quotient`/`Setoid` to avoid needing `DecidableRel` for an arbitrary
`EqvGen`-generated relation. `BlockComponent.mapPerm` shows any adjacency-preserving permutation of
`ι∖{u}` descends to a permutation of the components — this is what lets a block-permuting subgroup
`A` act on the *set of components themselves*, whose orbits are (A2a)'s "rooted-isomorphism types
`τ`", in the next file.
-/

open Equiv

variable {Ω ι : Type*} [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- Two blocks `i,j ≠ u` are adjacent if some point of `V i` and some point of `V j` share a
`g`-cycle. -/
def BlockAdjSub (V : ι → Finset Ω) (g : Equiv.Perm Ω) (u : ι) (i j : {x : ι // x ≠ u}) : Prop :=
  ∃ x ∈ V i.1, ∃ y ∈ V j.1, g.SameCycle x y

/-- Reachability: the equivalence closure of `BlockAdjSub`. Its equivalence classes are the
connected components of the block-adjacency structure on `ι ∖ {u}`. -/
def BlockReach (V : ι → Finset Ω) (g : Equiv.Perm Ω) (u : ι) :
    {x : ι // x ≠ u} → {x : ι // x ≠ u} → Prop :=
  Relation.EqvGen (BlockAdjSub V g u)

/-- The type of connected components of the block-adjacency structure on `ι ∖ {u}`, as a raw
`Quot` (avoiding needing `DecidableRel`/`Setoid`-instance registration for an arbitrary
`EqvGen`-generated relation). -/
abbrev BlockComponent (V : ι → Finset Ω) (g : Equiv.Perm Ω) (u : ι) : Type _ :=
  Quot (BlockReach V g u)

noncomputable instance (V : ι → Finset Ω) (g : Equiv.Perm Ω) (u : ι) :
    Fintype (BlockComponent V g u) :=
  have : Finite (BlockComponent V g u) := Finite.of_surjective (Quot.mk (BlockReach V g u))
    (fun x => Quot.exists_rep x)
  Fintype.ofFinite _

/-- If a permutation `π` of `{x // x≠u}` sends adjacent blocks to adjacent blocks, it preserves
`BlockReach`, since `EqvGen` propagates any relation-preserving map along its generators. -/
theorem blockReach_of_adj_preserved {V : ι → Finset Ω} {g : Equiv.Perm Ω} {u : ι}
    (π : Equiv.Perm {x : ι // x ≠ u})
    (hpres : ∀ i j, BlockAdjSub V g u i j → BlockAdjSub V g u (π i) (π j))
    {i j : {x : ι // x ≠ u}} (h : BlockReach V g u i j) :
    BlockReach V g u (π i) (π j) := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (hpres x y hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ihxy ihyz => exact Relation.EqvGen.trans _ _ _ ihxy ihyz

/-- A permutation `π` of `{x // x≠u}` that preserves `BlockAdjSub` (in both directions) descends
to a permutation of the quotient `BlockComponent`. -/
noncomputable def BlockComponent.mapPerm {V : ι → Finset Ω} {g : Equiv.Perm Ω} {u : ι}
    (π : Equiv.Perm {x : ι // x ≠ u})
    (hpres : ∀ i j, BlockAdjSub V g u i j ↔ BlockAdjSub V g u (π i) (π j)) :
    Equiv.Perm (BlockComponent V g u) where
  toFun := Quot.map π (fun a b hab =>
    blockReach_of_adj_preserved π (fun i j hij => (hpres i j).mp hij) hab)
  invFun := Quot.map π.symm (fun a b hab => by
    have hpres' : ∀ i j, BlockAdjSub V g u i j → BlockAdjSub V g u (π.symm i) (π.symm j) := by
      intro i j hij
      have := (hpres (π.symm i) (π.symm j)).mpr
      simpa using this (by simpa using hij)
    exact blockReach_of_adj_preserved π.symm hpres' hab)
  left_inv x := by
    refine Quot.inductionOn x (fun a => ?_)
    show Quot.mk _ (π.symm (π a)) = Quot.mk _ a
    rw [Equiv.symm_apply_apply]
  right_inv x := by
    refine Quot.inductionOn x (fun a => ?_)
    show Quot.mk _ (π (π.symm a)) = Quot.mk _ a
    rw [Equiv.apply_symm_apply]
