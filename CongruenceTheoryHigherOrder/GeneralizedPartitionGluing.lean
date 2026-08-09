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
import CongruenceTheoryHigherOrder.A3Final

/-!
**Generalizes `PartitionGluing.lean` and `PartitionRespects.lean` from `Fin r` to an arbitrary
finite macroblock index type `ι`.** Mechanical generalization, mirroring `GeneralizedConnectivity.
lean`'s treatment of `ConnectedCount.lean`: same definitions and proofs, `Fin r` replaced by `ι`
throughout. Needed for (A4)'s two-level microblock refinement, at both the macroblock level
(`ι := Fin r`) and, recursively, within each block of a coarser partition (`ι := ↥B`).
-/

namespace CongruenceTheory

open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- The label subtype for a macroblock `B ⊆ ι`. -/
abbrev genBlockType (B : Finset ι) := {x : ι × Fin q // x.1 ∈ B}

noncomputable instance instFintypeGenBlockType (B : Finset ι) :
    Fintype (genBlockType (q := q) B) := by unfold genBlockType; infer_instance

/-- `genBlockType B ≃ ↥B × Fin q`. -/
def genBlockTypeEquiv (B : Finset ι) : genBlockType (q := q) B ≃ (↥B × Fin q) :=
  Equiv.prodSubtypeFstEquivSubtypeProd (p := fun i : ι => i ∈ B)

theorem card_genBlockType (B : Finset ι) :
    Fintype.card (genBlockType (q := q) B) = B.card * q := by
  rw [Fintype.card_congr (genBlockTypeEquiv (q := q) B), Fintype.card_prod, Fintype.card_coe,
    Fintype.card_fin]

/-- A tuple of permutations `(p_B)_{B∈τ.parts}`, one per macroblock of `τ`. -/
def GenPartitionPerm (τ : GenPartLat ι) :=
  ∀ B : τ.parts, Equiv.Perm (genBlockType (q := q) (B : Finset ι))

noncomputable instance (τ : GenPartLat ι) : Fintype (GenPartitionPerm (q := q) τ) := by
  unfold GenPartitionPerm; infer_instance

noncomputable def GenPartitionPerm.ciProd {τ : GenPartLat ι} (p : GenPartitionPerm (q := q) τ) :
    MvPolynomial ℕ ℤ :=
  ∏ B : τ.parts, ci (p B)

theorem gen_prod_C_eq_sum_ciProd (τ : GenPartLat ι) :
    ∏ B ∈ τ.parts, C (B.card * q) = ∑ p : GenPartitionPerm (q := q) τ, p.ciProd := by
  have hstep : ∀ B : τ.parts, C ((B : Finset ι).card * q) =
      ∑ g : Equiv.Perm (genBlockType (q := q) (B : Finset ι)), ci g := by
    intro B
    rw [← Cperm_eq_C]
    exact Cperm_eq_sum_of_card_eq (card_genBlockType (B : Finset ι))
  rw [show (∏ B ∈ τ.parts, C (B.card * q)) = ∏ B : τ.parts, C ((B : Finset ι).card * q) from
    (Finset.prod_attach τ.parts (fun B => C (B.card * q))).symm]
  rw [Finset.prod_congr rfl (fun B _ => hstep B)]
  exact Fintype.prod_sum _

noncomputable def genExtendB {τ : GenPartLat ι} (p : GenPartitionPerm (q := q) τ) (B : τ.parts) :
    Equiv.Perm (ι × Fin q) :=
  Equiv.Perm.extendDomain (p B) (Equiv.refl (genBlockType (q := q) (B : Finset ι)))

theorem genExtendB_disjoint {τ : GenPartLat ι} (p : GenPartitionPerm (q := q) τ) {B1 B2 : τ.parts}
    (h : B1 ≠ B2) : Equiv.Perm.Disjoint (genExtendB p B1) (genExtendB p B2) := by
  intro x
  by_cases hx1 : x.1 ∈ (B1 : Finset ι)
  · right
    have hx2 : x.1 ∉ (B2 : Finset ι) := by
      intro hx2
      exact h (Subtype.ext (τ.eq_of_mem_parts B1.2 B2.2 hx1 hx2))
    exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hx2
  · left
    exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hx1

noncomputable def genAssemble {τ : GenPartLat ι} (p : GenPartitionPerm (q := q) τ) :
    Equiv.Perm (ι × Fin q) :=
  τ.parts.attach.noncommProd (fun B => genExtendB p B)
    (fun B1 _ B2 _ hne => (genExtendB_disjoint p hne).commute)

theorem genCycleType_assemble {τ : GenPartLat ι} (p : GenPartitionPerm (q := q) τ) :
    (genAssemble p).cycleType = ∑ B : τ.parts, (p B).cycleType := by
  unfold genAssemble
  rw [Equiv.Perm.Disjoint.cycleType_noncommProd]
  · exact Finset.sum_congr rfl (fun B _ => Equiv.Perm.cycleType_extendDomain _)
  · exact fun B1 _ B2 _ hne => genExtendB_disjoint p hne

theorem gen_card_eq_sum_card_blockType (τ : GenPartLat ι) :
    Fintype.card (ι × Fin q) =
      ∑ B : τ.parts, Fintype.card (genBlockType (q := q) (B : Finset ι)) := by
  simp_rw [card_genBlockType]
  rw [Finset.sum_coe_sort τ.parts (fun B => B.card * q), ← Finset.sum_mul, τ.sum_card_parts]
  simp

theorem gen_ci_assemble {τ : GenPartLat ι} (p : GenPartitionPerm (q := q) τ) :
    ci (genAssemble p) = p.ciProd := by
  unfold ci GenPartitionPerm.ciProd
  rw [genCycleType_assemble, gen_card_eq_sum_card_blockType (q := q) τ]
  have hle : ∀ B : τ.parts,
      (p B).cycleType.sum ≤ Fintype.card (genBlockType (q := q) (B : Finset ι)) :=
    fun B => Equiv.Perm.sum_cycleType_le (p B)
  rw [show (∑ B : τ.parts, Fintype.card (genBlockType (q := q) (B : Finset ι))) -
      (∑ B : τ.parts, (p B).cycleType).sum =
      ∑ B : τ.parts,
        (Fintype.card (genBlockType (q := q) (B : Finset ι)) - (p B).cycleType.sum) by
    rw [multiset_sum_sum, Finset.sum_tsub_distrib _ (fun B _ => hle B)]]
  rw [← Finset.prod_pow_eq_pow_sum, multiset_prod_map_sum, ← Finset.prod_mul_distrib]
  rfl

/-- `g` respects `τ`'s block structure. -/
def GenRespects (τ : GenPartLat ι) (g : Equiv.Perm (ι × Fin q)) : Prop :=
  ∀ x : ι × Fin q, (g x).1 ∈ (τ.part x.1 : Finset ι)

theorem genAssemble_apply {τ : GenPartLat ι} (p : GenPartitionPerm (q := q) τ) (x : ι × Fin q) :
    genAssemble p x = genExtendB p ⟨τ.part x.1, τ.part_mem.mpr (Finset.mem_univ x.1)⟩ x := by
  unfold genAssemble
  exact noncommProd_apply_of_forall_others_fix (fun B => genExtendB p B) τ.parts.attach
    (fun B1 _ B2 _ hne => genExtendB_disjoint p hne)
    ⟨τ.part x.1, τ.part_mem.mpr (Finset.mem_univ x.1)⟩ (Finset.mem_attach _ _) x
    (fun B _ hne => Equiv.Perm.extendDomain_apply_not_subtype _ _
      (fun hxB => hne (Subtype.ext (τ.part_eq_of_mem B.2 hxB).symm)))

theorem genRespects_assemble {τ : GenPartLat ι} (p : GenPartitionPerm (q := q) τ) :
    GenRespects τ (genAssemble p) := by
  intro x
  rw [genAssemble_apply p x]
  unfold genExtendB
  set B : τ.parts := ⟨τ.part x.1, τ.part_mem.mpr (Finset.mem_univ x.1)⟩
  by_cases hxB : x.1 ∈ (B : Finset ι)
  · rw [Equiv.Perm.extendDomain_apply_subtype (p B)
      (Equiv.refl (genBlockType (q := q) (B : Finset ι))) hxB]
    exact ((p B) ⟨x, hxB⟩).2
  · exact absurd (τ.mem_part_self.mpr (Finset.mem_univ x.1)) hxB

noncomputable def genRestrictP {τ : GenPartLat ι} (g : Equiv.Perm (ι × Fin q))
    (hg : GenRespects τ g) (B : τ.parts) : Equiv.Perm (genBlockType (q := q) (B : Finset ι)) :=
  g.subtypePerm (p := fun x : ι × Fin q => x.1 ∈ (B : Finset ι)) (fun x => by
    constructor
    · intro hgx
      rw [τ.eq_of_mem_parts B.2 (τ.part_mem.mpr (Finset.mem_univ x.1)) hgx (hg x)]
      exact τ.mem_part_self.mpr (Finset.mem_univ x.1)
    · intro hx
      rw [← τ.part_eq_of_mem B.2 hx]
      exact hg x)

theorem genAssemble_restrictP {τ : GenPartLat ι} (g : Equiv.Perm (ι × Fin q))
    (hg : GenRespects τ g) : genAssemble (fun B => genRestrictP g hg B) = g := by
  apply Equiv.ext
  intro x
  rw [genAssemble_apply (fun B => genRestrictP g hg B) x]
  set B : τ.parts := ⟨τ.part x.1, τ.part_mem.mpr (Finset.mem_univ x.1)⟩
  have hx1B : x.1 ∈ (B : Finset ι) := τ.mem_part_self.mpr (Finset.mem_univ x.1)
  unfold genExtendB genBlockType
  rw [Equiv.Perm.extendDomain_apply_subtype (genRestrictP g hg B)
    (Equiv.refl (genBlockType (q := q) (B : Finset ι))) hx1B]
  simp only [Equiv.refl_apply, Equiv.refl_symm]
  unfold genRestrictP
  rw [Equiv.Perm.subtypePerm_apply]

theorem genRestrictP_assemble {τ : GenPartLat ι} (p : GenPartitionPerm (q := q) τ) :
    (fun B => genRestrictP (genAssemble p) (genRespects_assemble p) B) = p := by
  funext B
  apply Equiv.ext
  intro y
  obtain ⟨x, hx⟩ := y
  unfold genRestrictP
  rw [Equiv.Perm.subtypePerm_apply]
  apply Subtype.ext
  show genAssemble p x = ((p B) ⟨x, hx⟩ : genBlockType (q := q) (B : Finset ι)).1
  rw [genAssemble_apply p x]
  have hBeq : (⟨τ.part x.1, τ.part_mem.mpr (Finset.mem_univ x.1)⟩ : τ.parts) = B :=
    Subtype.ext (τ.part_eq_of_mem B.2 hx)
  rw [hBeq]
  unfold genExtendB genBlockType
  rw [Equiv.Perm.extendDomain_apply_subtype (p B)
    (Equiv.refl (genBlockType (q := q) (B : Finset ι))) hx]
  simp only [Equiv.refl_apply, Equiv.refl_symm]

/-- **`genAssemble` is a bijection** between `GenPartitionPerm τ` and the permutations respecting
`τ`'s block structure. -/
noncomputable def genAssembleEquiv (τ : GenPartLat ι) :
    GenPartitionPerm (q := q) τ ≃ {g : Equiv.Perm (ι × Fin q) // GenRespects τ g} where
  toFun p := ⟨genAssemble p, genRespects_assemble p⟩
  invFun g := fun B => genRestrictP g.1 g.2 B
  left_inv p := genRestrictP_assemble p
  right_inv g := Subtype.ext (genAssemble_restrictP g.1 g.2)

theorem gen_sum_ci_respects_eq_prod_C (τ : GenPartLat ι) :
    (∑ g : {g : Equiv.Perm (ι × Fin q) // GenRespects τ g}, ci g.1) =
      ∏ B ∈ τ.parts, C (B.card * q) := by
  rw [gen_prod_C_eq_sum_ciProd τ, ← Equiv.sum_comp (genAssembleEquiv τ) (fun g => ci g.1)]
  exact Finset.sum_congr rfl (fun p _ => gen_ci_assemble p)

end CongruenceTheory
