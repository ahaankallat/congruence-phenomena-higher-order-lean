import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**`Stab_A(p₀)` fixes `p₀`'s own reached component setwise**, a key structural fact for (A2a)'s
cut-vertex case: any `φ` fixing `p₀` and commuting with `g` maps `p₀`'s own component to itself
under `componentPermOfMem` — since `φ` fixes `p₀`'s whole cycle (`Perm.fixed_of_commute_of_fixed_
point`), in particular the specific point `y` witnessing `p₀`'s reach into component `c0`, and `y`
being fixed pins its own block (partition uniqueness), hence the component containing it. This
means `Stab_A(p₀)` — unlike a generic subgroup of `A` — has genuine internal structure relative to
`c0`: it maps `c0`'s own blocks among themselves (never mixing them with another component's), so
the within-`c0` sub-problem can be treated as a smaller, self-contained instance.
-/

open Equiv

variable {Ω ι : Type*} [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- If `φ` fixes `p₀` and commutes with `g`, `φ`'s induced component-permutation fixes whichever
component `p₀`'s cycle reaches. -/
theorem componentPermOfMem_fixes_reached {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    {φ : Equiv.Perm Ω} (hφ : φ ∈ A) (hu : (V u).image φ = V u) {p₀ : Ω} (hfix : φ p₀ = p₀)
    {c0 : BlockComponent V g u} (hreach : Reaches g u p₀ c0) :
    componentPermOfMem hpart hne hcent hperm hφ hu c0 = c0 := by
  obtain ⟨x, hx, y, hy, hpy⟩ := hreach
  have hφy : φ y = y := Perm.fixed_of_commute_of_fixed_point (hcent φ hφ) hfix hpy
  have heq : blockOfElt hpart hperm φ hφ x.1 = x.1 := by
    have hspec := blockOfElt_spec hpart hperm φ hφ x.1
    have hy' : φ y ∈ V (blockOfElt hpart hperm φ hφ x.1) := hspec ▸ Finset.mem_image_of_mem φ hy
    rw [hφy] at hy'
    obtain ⟨i0, hi0, huniq⟩ := hpart y
    exact (huniq (blockOfElt hpart hperm φ hφ x.1) hy').trans (huniq x.1 hy).symm
  have hxx : blockPermSub hpart hne hperm hφ hu x = x := by
    apply Subtype.ext
    rw [blockPermSub_coe]
    exact heq
  rw [← hx, componentPermOfMem_mk, hxx]
