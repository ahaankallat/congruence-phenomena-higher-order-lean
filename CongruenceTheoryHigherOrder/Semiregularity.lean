import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.WreathProduct

/-!
**The mathematical core of inequality (A1)** of `thm:atomic-connected-content`'s proof: the
manuscript's own argument, made precise. Quoting the manuscript: "A stabilizer acts semiregularly
on the `rq` labels: if an element fixes one point, it is the identity on that block; commutation
fixes every mixed cycle meeting the block pointwise, and connectedness propagates this to every
block." This file proves exactly that claim as **`wreathToPermRotate_eq_one_of_fixes`**: if `g`
is connected (`piOf g = ⊤`, `ConnectedCount.lean`) and `w : Wreath r q` centralizes `g`'s image
under `WreathProduct.lean`'s action, then `w`'s image fixing *any* point forces it to be the
identity — i.e. the stabilizer of a connected permutation, under the wreath action built in
`WreathProduct.lean`, acts freely (semiregularly) on the `rq` labels.

**Proof structure, matching the manuscript's own three sentences exactly**:
- *"if an element fixes one point, it is the identity on that block"* — `wreathToPermRotate_fixes_block`:
  fixing one point of a block forces the local cyclic power there to vanish (using that a
  nontrivial power of a full `q`-cycle has no fixed points at all, Mathlib's
  `IsCycle.pow_eq_one_iff'`), hence the wreath element fixes the *entire* block.
- *"commutation fixes every mixed cycle meeting the block pointwise"* — the `hclosed` step inside
  the main proof: if a stabilizer element fixes a whole block `j`, and some cycle of `g` connects
  `j` to another block `j'` (`touches`, `ConnectedCount.lean`), then commuting `w`'s image past `g`
  along that cycle (`h(gy) = g(hy)`) shows it fixes a point of `j'` too — hence (by the block
  lemma again) the *entire* block `j'`.
- *"connectedness propagates this to every block"* — `reachable_of_piOf_top` (every block is
  reachable from every other when `π(g)=⊤`) combined with a `Relation.ReflTransGen` induction
  along that reachability, propagating the "whole block fixed" property from the one block reached
  by the original fixed point to *every* block — hence the stabilizer element is the identity
  everywhere.

**Honest scope note**: this is the semiregularity claim itself, but assembling the full inequality
`(r-1)!q^{r-1} ∣ K_r(q)` still needs: orbit-stabilizer applied to the (as-yet-unformalized)
conjugation action of `Wreath r q` on connected permutations of a fixed cycle type (needing
conjugation-invariance of connectedness, itself not yet proved), the "free action ⟹ group order
divides set size" packaging, and combining across the coefficients making up `cont K_r(q)`. None
of that, nor (A2) through (A6) or Lucas' theorem, is attempted here.
-/

namespace CongruenceTheory

open scoped Classical

/-- If `wreathToPermRotate w` fixes one point of block `j`, it fixes every point of block `j`. -/
theorem wreathToPermRotate_fixes_block {r q : ℕ} [NeZero q] (hq : 2 ≤ q) {w : Wreath r q}
    {j : Fin r} {k0 : Fin q} (hfix : wreathToPermRotate r q hq w (j, k0) = (j, k0)) :
    ∀ k, wreathToPermRotate r q hq w (j, k) = (j, k) := by
  rw [wreathToPermRotate] at hfix ⊢
  rw [wreathToPerm_apply] at hfix
  have hj : w.right j = j := congrArg Prod.fst hfix
  have hk0 : (finRotate q ^ (Multiplicative.toAdd (w.left (w.right j))).val) k0 = k0 := by
    have := congrArg Prod.snd hfix
    simpa using this
  have hsupp : finRotate q k0 ≠ k0 := by
    have : k0 ∈ Equiv.Perm.support (finRotate q) := by
      rw [support_finRotate_of_le hq]; exact Finset.mem_univ k0
    rwa [Equiv.Perm.mem_support] at this
  have hcpow1 : finRotate q ^ (Multiplicative.toAdd (w.left (w.right j))).val = 1 :=
    (isCycle_finRotate_of_le hq).pow_eq_one_iff' hsupp |>.mpr hk0
  intro k
  rw [wreathToPerm_apply, hcpow1, hj]
  simp

theorem top_part_eq_univ {r : ℕ} [NeZero r] (τ : PartLat r) (hτ : τ = ⊤) (i0 : Fin r) :
    τ.part i0 = Finset.univ := by
  subst hτ
  have hne : (Finset.univ : Finset (Fin r)) ≠ ⊥ := by
    simp only [Finset.bot_eq_empty, ne_eq, Finset.univ_eq_empty_iff]
    exact not_isEmpty_of_nonempty (Fin r)
  obtain ⟨t, ht⟩ := (⊤ : PartLat r).parts_nonempty hne
  have hsub := Finpartition.parts_top_subset (Finset.univ : Finset (Fin r))
  have htu : t = Finset.univ := Finset.mem_singleton.mp (hsub ht)
  have hi0t : i0 ∈ t := htu ▸ Finset.mem_univ i0
  exact ((⊤ : PartLat r).part_eq_of_mem ht hi0t).trans htu

/-- If `g`'s cycle-support hypergraph is connected, every macroblock is reachable in `graphOf g`
from every other. -/
theorem reachable_of_piOf_top {r q : ℕ} [NeZero r] {g : Equiv.Perm (Fin r × Fin q)}
    (hg : piOf g = ⊤) (i0 j : Fin r) : (graphOf g).Reachable i0 j := by
  have hmem : j ∈ (piOf g).part i0 := by
    rw [top_part_eq_univ (piOf g) hg]; exact Finset.mem_univ j
  unfold piOf at hmem
  exact Finpartition.mem_part_ofSetoid_iff_rel.mp hmem

/-- **The semiregularity argument (A1)**: if `g` is connected and `w` centralizes `g` under the
wreath action, and `w`'s image fixes any point at all, then `w`'s image is the identity — the
stabilizer of a connected permutation acts freely (semiregularly) on the `rq` labels. -/
theorem wreathToPermRotate_eq_one_of_fixes {r q : ℕ} [NeZero r] [NeZero q] (hq : 2 ≤ q)
    {g : Equiv.Perm (Fin r × Fin q)} (hg : piOf g = ⊤) {w : Wreath r q}
    (hcomm : Commute (wreathToPermRotate r q hq w) g) {x : Fin r × Fin q}
    (hfix : wreathToPermRotate r q hq w x = x) :
    wreathToPermRotate r q hq w = 1 := by
  set h := wreathToPermRotate r q hq w with hhdef
  have hcommpt : ∀ y, h (g y) = g (h y) := fun y => by
    have hmul : (h * g) y = (g * h) y := DFunLike.congr_fun hcomm y
    simpa [Equiv.Perm.mul_apply] using hmul
  set S : Set (Fin r) := {j | ∀ k, h (j, k) = (j, k)} with hSdef
  have hi0 : x.1 ∈ S := by
    intro k
    apply wreathToPermRotate_fixes_block hq (w := w) (j := x.1) (k0 := x.2)
    rw [← hhdef]
    rwa [show (x.1, x.2) = x from rfl]
  have hclosed : ∀ j j', (graphOf g).Adj j j' → j ∈ S → j' ∈ S := by
    intro j j' hadj hjS
    unfold graphOf at hadj
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with ⟨y, hy1, hy2⟩ | ⟨y, hy1, hy2⟩
    · have hjy : h y = y := by
        rw [show y = (j, y.2) from by rw [← hy1]]
        exact hjS y.2
      have hgy : h (g y) = g y := by rw [hcommpt, hjy]
      intro k
      apply wreathToPermRotate_fixes_block hq (w := w) (j := j') (k0 := (g y).2)
      rw [show (j', (g y).2) = g y from by rw [← hy2]]
      exact hgy
    · have hgyj : h (g y) = g y := by
        rw [show g y = (j, (g y).2) from by rw [← hy2]]
        exact hjS (g y).2
      have : g (h y) = g y := (hcommpt y).symm.trans hgyj
      have hhy : h y = y := g.injective this
      intro k
      apply wreathToPermRotate_fixes_block hq (w := w) (j := j') (k0 := y.2)
      rw [show (j', y.2) = y from by rw [← hy1]]
      exact hhy
  have hSall : ∀ j, j ∈ S := by
    intro j
    have hreach := reachable_of_piOf_top hg x.1 j
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    induction hreach with
    | refl => exact hi0
    | tail _ hstep ih => exact hclosed _ _ hstep ih
  apply Equiv.ext
  intro p
  exact hSall p.1 p.2

end CongruenceTheory
