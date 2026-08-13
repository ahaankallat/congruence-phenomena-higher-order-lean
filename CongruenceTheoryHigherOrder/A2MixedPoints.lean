import Mathlib
import CongruenceTheoryHigherOrder.A2aBlockPermutation

/-!
**`thm:atomic-connected-content`'s (A2): the "mixed points" restriction.** The manuscript's proof
of (A2) (the second divisor beyond (A2a)) restricts a centralizer `C_{\widetilde H}(\sigma)` to
the "mixed part" — the points whose `\sigma`-cycle reaches outside their own block — and shows the
kernel of this restriction embeds in a product of symmetric groups on the *non*-mixed points,
while the image satisfies (A2a) on the mixed points alone. This file builds the "mixed points"
notion itself and the basic facts a centralizing, block-permuting subgroup needs: mixedness is
preserved (`isMixed_apply_of_commute_of_permBlocks`), and two points on the same `\sigma`-cycle
are mixed together (`isMixedPt_of_sameCycle`).
-/

namespace CongruenceTheory

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- **A point `x` is mixed** (relative to a block partition `V` and a permutation `\sigma`) if
its own block contains it but its `\sigma`-cycle reaches a point outside that block. -/
def IsMixedPt (V : ι → Finset Ω) (σ : Equiv.Perm Ω) (x : Ω) : Prop :=
  ∃ i, x ∈ V i ∧ ∃ y ∉ V i, σ.SameCycle x y

/-- **Two points on the same `\sigma`-cycle are mixed together.** -/
theorem isMixedPt_of_sameCycle {V : ι → Finset Ω} (hpart : IsPartition V) {σ : Equiv.Perm Ω}
    {x y : Ω} (hsame : σ.SameCycle x y) (hx : IsMixedPt V σ x) : IsMixedPt V σ y := by
  obtain ⟨i, hxi, z, hznoti, hxz⟩ := hx
  obtain ⟨j, hyj, -⟩ := hpart y
  by_cases hij : i = j
  · subst hij
    exact ⟨i, hyj, z, hznoti, hsame.symm.trans hxz⟩
  · refine ⟨j, hyj, x, ?_, hsame.symm⟩
    intro hxj
    obtain ⟨i0, hi0, huniqx⟩ := hpart x
    exact hij ((huniqx i hxi).trans (huniqx j hxj).symm)

/-- **A commuting, block-permuting element sends mixed points to mixed points.** -/
theorem isMixed_apply_of_commute_of_permBlocks {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)}
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {σ : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ σ)
    {φ : Equiv.Perm Ω} (hφ : φ ∈ A) {x : Ω} (hx : IsMixedPt V σ x) :
    IsMixedPt V σ (φ x) := by
  obtain ⟨i, hxi, y, hynoti, hsame⟩ := hx
  set π := blockPermOfMem hpart hne hperm φ hφ with hπdef
  refine ⟨π i, ?_, φ y, ?_, ?_⟩
  · rw [show π i = blockOfElt hpart hperm φ hφ i from rfl, ← blockOfElt_spec hpart hperm φ hφ i]
    exact Finset.mem_image_of_mem φ hxi
  · rw [show π i = blockOfElt hpart hperm φ hφ i from rfl, ← blockOfElt_spec hpart hperm φ hφ i]
    intro hmem
    obtain ⟨y', hy'mem, hy'eq⟩ := Finset.mem_image.mp hmem
    exact hynoti ((φ.injective hy'eq) ▸ hy'mem)
  · obtain ⟨n, hn⟩ := hsame
    refine ⟨n, ?_⟩
    have hcommn : φ * σ ^ n = σ ^ n * φ := (hcent φ hφ).zpow_right n
    have heq : φ ((σ ^ n) x) = (σ ^ n) (φ x) := by
      have hc := congrArg (fun e : Equiv.Perm Ω => e x) hcommn
      simpa using hc
    rw [hn] at heq
    exact heq.symm

#print axioms isMixedPt_of_sameCycle
#print axioms isMixed_apply_of_commute_of_permBlocks

end CongruenceTheory
