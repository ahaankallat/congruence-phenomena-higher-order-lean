import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**The "no separating cut" property of `BlockReach`-connected components**: if `x` and `y` are
`BlockReach`-related (in the same component), then for any Finset `L` containing `x` but not `y`,
some element of `L` is `BlockAdjSub`-adjacent to some element outside `L`. This is exactly the
`hconn` hypothesis `key_induction_rooted`/`card_le_root_bound` need — proved here as a genuine
graph-connectivity fact (not assumed) by induction on the `EqvGen` proof witnessing `x`'s and `y`'s
reachability: any path from `x` to `y` must cross the boundary of `L` somewhere.
-/

open Equiv

variable {Ω ι : Type*} [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

theorem blockAdjSub_symm {V : ι → Finset Ω} {g : Equiv.Perm Ω} {u : ι}
    {a b : {i : ι // i ≠ u}} (hab : BlockAdjSub V g u a b) : BlockAdjSub V g u b a := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hab
  exact ⟨y, hy, x, hx, hxy.symm⟩

/-- If `x` and `y` are `BlockReach`-related, then for any Finset `L` containing `x` but not `y`,
some element of `L` is `BlockAdjSub`-adjacent to some element outside `L`. -/
theorem exists_boundary_edge_of_blockReach {V : ι → Finset Ω} {g : Equiv.Perm Ω} {u : ι}
    {x y : {i : ι // i ≠ u}} (hxy : BlockReach V g u x y) :
    ∀ L : Finset {i : ι // i ≠ u}, x ∈ L → y ∉ L →
      ∃ a ∈ L, ∃ b, b ∉ L ∧ BlockAdjSub V g u a b := by
  induction hxy with
  | rel a b hab => intro L haL hbL; exact ⟨a, haL, b, hbL, hab⟩
  | refl a => intro L haL hbL; exact absurd haL hbL
  | symm a b _ ih =>
    intro L hbL haL
    obtain ⟨p, hp, q, hq, hpq⟩ := ih Lᶜ (Finset.mem_compl.mpr haL) (by
      simp only [Finset.mem_compl, not_not]; exact hbL)
    refine ⟨q, ?_, p, ?_, blockAdjSub_symm hpq⟩
    · simpa using hq
    · simpa using hp
  | trans a b c _ _ ihab ihbc =>
    intro L haL hcL
    by_cases hbL : b ∈ L
    · exact ihbc L hbL hcL
    · exact ihab L haL hbL
