import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInstance
import CongruenceTheoryHigherOrder.A2aCutVertexDistinguished
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**The base case for the outer induction across (A2a)'s cut-vertex case's components**: if a
subgroup `A'` fixes *every* block of `ι∖{u}` pointwise, and fixes `V u` pointwise too (the latter
derived from `hmixed` plus the former: every point of `V u` reaches some component via `hmixed`,
and once that component's block is fixed pointwise, `Perm.fixed_of_commute_of_fixed_point`
propagates the fixing back through the shared cycle to the `V u` point itself), then `A'` is
trivial. This mirrors `key_induction_rooted`'s own base case (all of `Ω` fixed pointwise ⟹ trivial
group), generalized to not need `eq_on_block_of_eq_off_block_of_commute`'s "mixed cycle" trick
directly since `V u`'s fixing is derived block-by-block via `Reaches` instead.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- If `A'` fixes every point reachable via `g` from an already-fixed point, and `hmixed` gives
every point of `V u` a witness reaching some block outside `V u`, then fixing all of `ι∖{u}`
pointwise extends to fixing `V u` pointwise too. -/
theorem fixes_Vu_of_fixes_all_blocks {V : ι → Finset Ω} {g : Equiv.Perm Ω} {u : ι}
    {A' : Subgroup (Equiv.Perm Ω)} (hcent' : ∀ φ ∈ A', Commute φ g)
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y)
    (hpart : IsPartition V)
    (hfixblocks : ∀ i ≠ u, ∀ x ∈ V i, ∀ φ ∈ A', φ x = x) :
    ∀ x ∈ V u, ∀ φ ∈ A', φ x = x := by
  intro x hx φ hφ
  obtain ⟨y, hyu, hxy⟩ := hmixed x hx
  obtain ⟨i0, hi0, -⟩ := hpart y
  have hi0u : i0 ≠ u := by intro h; subst h; exact hyu hi0
  have hfixy : φ y = y := hfixblocks i0 hi0u y hi0 φ hφ
  exact (Perm.fixed_of_commute_of_fixed_point (hcent' φ hφ) hfixy hxy.symm)

/-- **The base case**: if `A'` fixes every block of `ι∖{u}` pointwise, `A'` is trivial (given
`hmixed`, which also forces `V u` to be fixed pointwise via the lemma above, so `A'` fixes all of
`Ω`). -/
theorem card_le_one_of_fixes_all_blocks {V : ι → Finset Ω} {g : Equiv.Perm Ω} {u : ι}
    {A' : Subgroup (Equiv.Perm Ω)} (hcent' : ∀ φ ∈ A', Commute φ g)
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y) (hpart : IsPartition V)
    (hfixblocks : ∀ i ≠ u, ∀ x ∈ V i, ∀ φ ∈ A', φ x = x) :
    Nat.card A' ≤ 1 := by
  have hfixVu := fixes_Vu_of_fixes_all_blocks hcent' hmixed hpart hfixblocks
  have hAtriv : ∀ φ ∈ A', φ = 1 := by
    intro φ hφ
    apply Equiv.Perm.ext
    intro x
    by_cases hxu : x ∈ V u
    · simpa using hfixVu x hxu φ hφ
    · obtain ⟨i, hi, -⟩ := hpart x
      have hiu : i ≠ u := by intro h; subst h; exact hxu hi
      simpa using hfixblocks i hiu x hi φ hφ
  haveI : Subsingleton A' := ⟨fun a b => Subtype.ext ((hAtriv a a.2).trans (hAtriv b b.2).symm)⟩
  calc Nat.card A' ≤ Nat.card Unit := Nat.card_le_card_of_injective (fun _ => ())
        (fun a b _ => Subsingleton.elim a b)
    _ = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨()⟩⟩
