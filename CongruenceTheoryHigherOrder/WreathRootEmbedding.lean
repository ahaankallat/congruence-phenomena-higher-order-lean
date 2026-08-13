import Mathlib
import CongruenceTheoryHigherOrder.WreathFullProduct

/-!
**Embedding `S_q ≀ S_{r-2}` into `\operatorname{Perm}(\operatorname{Fin} r \times
\operatorname{Fin} q)` as the subgroup fixing two designated "root" blocks pointwise.** This is
`thm:atomic-connected-content`'s `(A2)`'s `\widetilde H = S_q\wr S_{r-2}` (after the manuscript
removes two root blocks from `r` total blocks), built by extending `WreathFullProduct.lean`'s
`WreathFull (r-2) q`-action on the *complement* of the two root blocks to the identity on the
root blocks themselves, via Mathlib's `Equiv.Perm.extendDomainHom`.
-/

namespace CongruenceTheory

open scoped Classical

variable {r q : ℕ}

/-- The predicate carving out the non-root blocks. -/
def NotRoot (u1 u2 : Fin r) (i : Fin r) : Prop := i ≠ u1 ∧ i ≠ u2

theorem card_notRoot (u1 u2 : Fin r) (h : u1 ≠ u2) :
    Fintype.card {i : Fin r // NotRoot u1 u2 i} = r - 2 := by
  have hcompl : Fintype.card {i : Fin r // ¬ (i = u1 ∨ i = u2)} =
      Fintype.card (Fin r) - Fintype.card {i : Fin r // i = u1 ∨ i = u2} :=
    Fintype.card_subtype_compl _
  have heq2 : Fintype.card {i : Fin r // i = u1 ∨ i = u2} = 2 := by
    have : {i : Fin r // i = u1 ∨ i = u2} ≃ ({u1, u2} : Finset (Fin r)) := by
      apply Equiv.subtypeEquivRight
      intro i
      simp [Finset.mem_insert, Finset.mem_singleton]
    rw [Fintype.card_congr this, Fintype.card_coe, Finset.card_insert_of_notMem
      (by simp [h]), Finset.card_singleton]
  have hiff : ∀ i : Fin r, NotRoot u1 u2 i ↔ ¬ (i = u1 ∨ i = u2) := by
    intro i; unfold NotRoot; tauto
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hiff), hcompl, heq2, Fintype.card_fin]

/-- **`\operatorname{Fin}(r-2)` is equivalent to the non-root blocks** (given two distinct root
blocks). -/
noncomputable def rootComplementEquiv (u1 u2 : Fin r) (h : u1 ≠ u2) :
    Fin (r - 2) ≃ {i : Fin r // NotRoot u1 u2 i} :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, card_notRoot u1 u2 h])

/-- **`\operatorname{Fin}(r-2)\times\operatorname{Fin} q` is equivalent to the non-root points.**
-/
noncomputable def rootComplementProdEquiv (u1 u2 : Fin r) (h : u1 ≠ u2) :
    Fin (r - 2) × Fin q ≃ {s : Fin r × Fin q // NotRoot u1 u2 s.1} :=
  (rootComplementEquiv u1 u2 h).prodCongr (Equiv.refl (Fin q)) |>.trans
    Equiv.prodSubtypeFstEquivSubtypeProd.symm

/-- **`S_q ≀ S_{r-2}` embeds into `\operatorname{Perm}(\operatorname{Fin} r \times
\operatorname{Fin} q)`, fixing the two root blocks `u1,u2` pointwise.** -/
noncomputable def wreathRootHom (u1 u2 : Fin r) (h : u1 ≠ u2) :
    WreathFull (r - 2) q →* Equiv.Perm (Fin r × Fin q) :=
  (Equiv.Perm.extendDomainHom (rootComplementProdEquiv u1 u2 h)).comp
    (wreathFullToPerm (r - 2) q)

theorem wreathRootHom_injective (u1 : Fin r) (u2 : Fin r) (h : u1 ≠ u2) (q : ℕ) [NeZero q] :
    Function.Injective (wreathRootHom (q := q) u1 u2 h) := by
  unfold wreathRootHom
  rw [MonoidHom.coe_comp]
  exact (Equiv.Perm.extendDomainHom_injective (rootComplementProdEquiv u1 u2 h)).comp
    (wreathFullToPerm_injective (r - 2) q)

/-- **Elements of the range fix the root blocks pointwise.** -/
theorem wreathRootHom_fixes_root (u1 u2 : Fin r) (h : u1 ≠ u2) (w : WreathFull (r - 2) q)
    (i : Fin r) (hi : i = u1 ∨ i = u2) (k : Fin q) :
    wreathRootHom u1 u2 h w (i, k) = (i, k) := by
  show (Equiv.Perm.extendDomain (wreathFullToPerm (r - 2) q w) (rootComplementProdEquiv u1 u2 h))
    (i, k) = (i, k)
  apply Equiv.Perm.extendDomain_apply_not_subtype
  simp only [NotRoot]
  tauto

#print axioms card_notRoot
#print axioms rootComplementEquiv
#print axioms rootComplementProdEquiv
#print axioms wreathRootHom
#print axioms wreathRootHom_injective
#print axioms wreathRootHom_fixes_root

end CongruenceTheory
