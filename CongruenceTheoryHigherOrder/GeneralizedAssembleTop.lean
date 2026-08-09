import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.GeneralizedConnectivity
import CongruenceTheoryHigherOrder.GeneralizedConnectivityTransport
import CongruenceTheoryHigherOrder.GeneralizedConnectivityTop
import CongruenceTheoryHigherOrder.GeneralizedPartitionGluing
import CongruenceTheoryHigherOrder.A3Final

/-!
**The crux of (A4)**: `genAssemble p`'s global connectivity partition is exactly `τ` iff each
block `B`'s own permutation `p B`, relabeled to `↥B × Fin q`, is *locally* fully connected.
-/

namespace CongruenceTheory

open Equiv

open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

theorem genBlockTypeEquiv_fst {B : Finset ι} (x : genBlockType (q := q) B) :
    ((genBlockTypeEquiv B x).1 : ι) = x.1.1 := rfl

theorem genBlockTypeEquiv_snd {B : Finset ι} (x : genBlockType (q := q) B) :
    (genBlockTypeEquiv B x).2 = x.1.2 := rfl

theorem genBlockTypeEquiv_symm_fst {B : Finset ι} (x' : ↥B × Fin q) :
    ((genBlockTypeEquiv B).symm x').1.1 = (x'.1 : ι) := rfl

/-- **Local/global touches compatibility**: for `i,j` in one block `B`, `genAssemble p`'s
global touches relation matches `p B`'s own local touches relation (transported to `↥B × Fin q`).
-/
theorem genTouches_assemble_iff {τ : GenPartLat ι} (p : GenPartitionPerm (q := q) τ)
    (B : τ.parts) (i j : ↥(B : Finset ι)) :
    genTouches (genAssemble p) (i : ι) (j : ι) ↔
      genTouches ((genBlockTypeEquiv (B : Finset ι)).permCongr (p B)) i j := by
  unfold genTouches
  constructor
  · rintro ⟨x, hx1, hx2⟩
    have hxB : x.1 ∈ (B : Finset ι) := hx1 ▸ i.2
    set x' : genBlockType (q := q) (B : Finset ι) := ⟨x, hxB⟩ with hx'_def
    refine ⟨genBlockTypeEquiv (B : Finset ι) x', ?_, ?_⟩
    · apply Subtype.ext
      show ((genBlockTypeEquiv (B : Finset ι) x').1 : ι) = (i : ι)
      rw [genBlockTypeEquiv_fst]
      exact hx1
    · show ((genBlockTypeEquiv (B : Finset ι)).permCongr (p B)
        (genBlockTypeEquiv (B : Finset ι) x')).1 = j
      show (genBlockTypeEquiv (B : Finset ι)
        ((p B) ((genBlockTypeEquiv (B : Finset ι)).symm (genBlockTypeEquiv (B : Finset ι) x')))).1 = j
      rw [Equiv.symm_apply_apply]
      apply Subtype.ext
      rw [genBlockTypeEquiv_fst]
      have hpBx' : ((p B) x').1 = genAssemble p x := by
        rw [genAssemble_apply p x]
        have hBeq : (⟨τ.part x.1, τ.part_mem.mpr (Finset.mem_univ x.1)⟩ : τ.parts) = B := by
          apply Subtype.ext
          exact τ.part_eq_of_mem B.2 hxB
        rw [show genExtendB p (⟨τ.part x.1, τ.part_mem.mpr (Finset.mem_univ x.1)⟩ : τ.parts) x =
          genExtendB p B x from by rw [hBeq]]
        unfold genExtendB
        rw [Equiv.Perm.extendDomain_apply_subtype (p B)
          (Equiv.refl (genBlockType (q := q) (B : Finset ι))) hxB]
        simp only [Equiv.refl_apply, Equiv.refl_symm]
        rfl
      rw [hpBx', hx2]
  · rintro ⟨x', hx1, hx2⟩
    set x : genBlockType (q := q) (B : Finset ι) := (genBlockTypeEquiv (B : Finset ι)).symm x'
      with hx_def
    refine ⟨x.1, ?_, ?_⟩
    · show x.1.1 = (i : ι)
      rw [hx_def, genBlockTypeEquiv_symm_fst]
      exact congrArg Subtype.val hx1
    · have hxB : x.1.1 ∈ (B : Finset ι) := x.2
      have hBeq : (⟨τ.part x.1.1, τ.part_mem.mpr (Finset.mem_univ x.1.1)⟩ : τ.parts) = B := by
        apply Subtype.ext
        exact τ.part_eq_of_mem B.2 hxB
      have hx2' : (genBlockTypeEquiv (B : Finset ι) ((p B) x)).1 = j := by
        have heq : (genBlockTypeEquiv (B : Finset ι)) ((p B) x) =
            (genBlockTypeEquiv (B : Finset ι)).permCongr (p B) x' := by
          show (genBlockTypeEquiv (B : Finset ι)) ((p B) x) =
            genBlockTypeEquiv (B : Finset ι)
              ((p B) ((genBlockTypeEquiv (B : Finset ι)).symm x'))
          rw [← hx_def]
        rw [heq]
        exact hx2
      rw [genAssemble_apply p x.1, hBeq]
      unfold genExtendB
      rw [Equiv.Perm.extendDomain_apply_subtype (p B)
        (Equiv.refl (genBlockType (q := q) (B : Finset ι))) hxB]
      simp only [Equiv.refl_apply, Equiv.refl_symm]
      show (((p B) x) : ι × Fin q).1 = (j : ι)
      rw [← genBlockTypeEquiv_fst ((p B) x)]
      exact congrArg Subtype.val hx2'

end CongruenceTheory
