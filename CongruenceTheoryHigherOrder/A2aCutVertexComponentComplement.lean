import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexComponentHom
import CongruenceTheoryHigherOrder.A2aCutVertexBranchOrbitStab
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**A permutation fixing a Finset pointwise maps the complement to itself setwise.** Needed for the
outer induction across (A2a)'s cut-vertex case's remaining components: if `A'` fixes every
already-processed component pointwise (on its whole island, hence certainly as a point of
`componentHom`'s permutation action), it maps the *complement* Finset of still-unprocessed
components to itself setwise — so the induction's shrinking measure (`M.card`) is preserved by the
group action at each step.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- A permutation of a fintype fixing a Finset `N` pointwise maps the complement to itself. -/
theorem Equiv.Perm.mapsTo_compl_of_fixes {α : Type*} [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) {N : Finset α} (hN : ∀ x ∈ N, π x = x) {x : α} (hx : x ∉ N) :
    π x ∉ N := by
  intro hπx
  apply hx
  have hNimg : N.image π = N := by
    apply Finset.ext
    intro y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩; rwa [hN z hz]
    · intro hy; exact ⟨y, hy, hN y hy⟩
  rw [← hNimg] at hπx
  obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hπx
  rwa [← π.injective hzeq]

theorem componentMulAction_mapsTo_compl {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) {N : Finset (BlockComponent V g u)}
    (φ : ↥A')
    (hfix : ∀ c ∈ N,
      letI := componentMulAction hpart hne hcent' hperm' hblock_u'
      φ • c = c) :
    letI := componentMulAction hpart hne hcent' hperm' hblock_u'
    ∀ c ∉ N, φ • c ∉ N := by
  letI := componentMulAction hpart hne hcent' hperm' hblock_u'
  intro c hc hφc
  apply hc
  have hNimg : N.image (fun c => φ • c) = N := by
    apply Finset.ext
    intro y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩; rwa [hfix z hz]
    · intro hy; exact ⟨y, hy, hfix y hy⟩
  rw [← hNimg] at hφc
  obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hφc
  have hinj : Function.Injective (fun c : BlockComponent V g u => φ • c) :=
    MulAction.injective φ
  rwa [← hinj hzeq]
