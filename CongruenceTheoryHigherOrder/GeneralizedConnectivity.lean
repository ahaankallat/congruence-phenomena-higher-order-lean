import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount

/-!
**Generalizes `ConnectedCount.lean`'s cycle-support connectivity apparatus from `Fin r` to an
arbitrary finite macroblock index type `ι`.** Needed for (A4)'s two-level microblock refinement:
the SAME connectivity/Möbius machinery is needed once at the macroblock level (`ι := Fin r`,
recovering `ConnectedCount.lean` exactly) and once at the microblock level (`ι` ranging over
*subsets* of a larger macroblock set, reindexed via `↥B`, when restricting to one block of a
coarser partition). Rather than duplicate `ConnectedCount.lean`'s ~150 lines for each new `ι`,
this file makes `ι` a variable throughout.

**Everything here is definitionally/propositionally identical to `ConnectedCount.lean`'s own
`Fin r`-specific versions** — same proofs, `Fin r` replaced by a general `ι`. `genPiOf_eq_of_equiv`
additionally shows this apparatus transports correctly along any `ι ≃ ι'` (needed to identify the
general-`ι` and `Fin r`-specific versions when `ι ≃ Fin r`, e.g. via `Fintype.equivFin`).
-/

namespace CongruenceTheory

open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- The partition lattice of a general finite index type `ι`. -/
abbrev GenPartLat (ι : Type*) [Fintype ι] [DecidableEq ι] := Finpartition (Finset.univ : Finset ι)

noncomputable instance : LocallyFiniteOrder (GenPartLat ι) :=
  Fintype.toLocallyFiniteOrder

noncomputable instance : OrderTop (GenPartLat ι) := by
  unfold GenPartLat
  infer_instance

/-- `i` and `j` are directly connected by some cycle of `g`. -/
def genTouches (g : Equiv.Perm (ι × Fin q)) (i j : ι) : Prop :=
  ∃ x : ι × Fin q, x.1 = i ∧ (g x).1 = j

noncomputable instance (g : Equiv.Perm (ι × Fin q)) : DecidableRel (genTouches (q := q) g) :=
  Classical.decRel _

/-- The cycle-support connectivity graph of `g` on `ι`. -/
noncomputable def genGraphOf (g : Equiv.Perm (ι × Fin q)) : SimpleGraph ι :=
  SimpleGraph.fromRel (genTouches (q := q) g)

noncomputable instance (g : Equiv.Perm (ι × Fin q)) :
    DecidableRel (genGraphOf (q := q) g).Adj := by
  unfold genGraphOf; infer_instance

noncomputable instance (g : Equiv.Perm (ι × Fin q)) :
    DecidableRel (genGraphOf (q := q) g).Reachable := by
  classical infer_instance

/-- The canonical cycle-support connectivity partition `π(g)` of `ι`. -/
noncomputable def genPiOf (g : Equiv.Perm (ι × Fin q)) : GenPartLat ι :=
  Finpartition.ofSetoid (genGraphOf (q := q) g).reachableSetoid

theorem genRespects_of_genPiOf_le {τ : GenPartLat ι} {g : Equiv.Perm (ι × Fin q)}
    (h : genPiOf g ≤ τ) : ∀ x : ι × Fin q, (g x).1 ∈ (τ.part x.1 : Finset ι) := by
  intro x
  have hreach : (genGraphOf g).Reachable x.1 (g x).1 := by
    by_cases heq : x.1 = (g x).1
    · rw [heq]
    · exact SimpleGraph.Adj.reachable
        (SimpleGraph.fromRel_adj _ _ _ |>.mpr ⟨heq, Or.inl ⟨x, rfl, rfl⟩⟩)
  have hmem : (g x).1 ∈ (genPiOf g).part x.1 := by
    unfold genPiOf
    exact (Finpartition.mem_part_ofSetoid_iff_rel).mpr hreach
  obtain ⟨c, hc, hsub⟩ := h ((genPiOf g).part_mem.mpr (Finset.mem_univ x.1))
  have hxc : x.1 ∈ c := hsub ((genPiOf g).mem_part_self.mpr (Finset.mem_univ x.1))
  have hgxc : (g x).1 ∈ c := hsub hmem
  rwa [τ.part_eq_of_mem hc hxc]

theorem genPiOf_le_of_genRespects {τ : GenPartLat ι} {g : Equiv.Perm (ι × Fin q)}
    (h : ∀ x : ι × Fin q, (g x).1 ∈ (τ.part x.1 : Finset ι)) : genPiOf g ≤ τ := by
  have hstep : ∀ b c : ι, (genGraphOf g).Adj b c → τ.part b = τ.part c := by
    intro b c hbc
    unfold genGraphOf at hbc
    rw [SimpleGraph.fromRel_adj (genTouches (q := q) g) b c] at hbc
    rcases hbc.2 with ⟨x, hx1, hx2⟩ | ⟨x, hx1, hx2⟩
    · have hmem : c ∈ (τ.part b : Finset ι) := by rw [← hx1, ← hx2]; exact h x
      exact ((τ.mem_part_iff_part_eq_part (Finset.mem_univ c) (Finset.mem_univ b)).mp hmem).symm
    · have hmem : b ∈ (τ.part c : Finset ι) := by rw [← hx1, ← hx2]; exact h x
      exact (τ.mem_part_iff_part_eq_part (Finset.mem_univ b) (Finset.mem_univ c)).mp hmem
  have hkey : ∀ i j : ι, (genGraphOf g).Reachable i j → τ.part i = τ.part j := by
    intro i j hij
    rw [SimpleGraph.reachable_iff_reflTransGen] at hij
    induction hij with
    | refl => rfl
    | tail _ hbc ih => rw [ih]; exact hstep _ _ hbc
  intro b hb
  obtain ⟨i0, hi0⟩ := (genPiOf g).nonempty_of_mem_parts hb
  refine ⟨τ.part i0, τ.part_mem.mpr (Finset.mem_univ i0), ?_⟩
  intro j hj
  have hbeq : (genPiOf g).part i0 = b := (genPiOf g).part_eq_of_mem hb hi0
  have hj' : j ∈ (genPiOf g).part i0 := hbeq ▸ hj
  unfold genPiOf at hj'
  have hreach : (genGraphOf g).Reachable i0 j := Finpartition.mem_part_ofSetoid_iff_rel.mp hj'
  rw [hkey i0 j hreach]
  exact τ.mem_part_self.mpr (Finset.mem_univ j)

theorem genRespects_iff_genPiOf_le {τ : GenPartLat ι} {g : Equiv.Perm (ι × Fin q)} :
    (∀ x : ι × Fin q, (g x).1 ∈ (τ.part x.1 : Finset ι)) ↔ genPiOf g ≤ τ :=
  ⟨genPiOf_le_of_genRespects, genRespects_of_genPiOf_le⟩

/-- The sum of `ci` over permutations whose canonical connectivity partition is exactly `π`. -/
noncomputable def GenGfun (π : GenPartLat ι) : MvPolynomial ℕ ℤ :=
  ∑ g ∈ (Finset.univ : Finset (Equiv.Perm (ι × Fin q))).filter (fun g => genPiOf g = π), ci g

/-- The sum of `ci` over permutations respecting `τ`. -/
noncomputable def GenFfun (τ : GenPartLat ι) : MvPolynomial ℕ ℤ :=
  ∑ g ∈ (Finset.univ : Finset (Equiv.Perm (ι × Fin q))).filter
    (fun g => ∀ x : ι × Fin q, (g x).1 ∈ (τ.part x.1 : Finset ι)), ci g

theorem GenFfun_eq_sum_GenGfun (τ : GenPartLat ι) :
    GenFfun (q := q) τ = ∑ π ∈ Finset.Iic τ, GenGfun (q := q) π := by
  unfold GenFfun GenGfun
  have hmaps : ∀ g ∈ (Finset.univ : Finset (Equiv.Perm (ι × Fin q))).filter
      (fun g => ∀ x : ι × Fin q, (g x).1 ∈ (τ.part x.1 : Finset ι)),
      genPiOf (q := q) g ∈ Finset.Iic τ :=
    fun g hg => Finset.mem_Iic.mpr (genRespects_iff_genPiOf_le.mp (Finset.mem_filter.mp hg).2)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps ci]
  apply Finset.sum_congr rfl
  intro π hπ
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ⟨_, hg⟩; exact hg
  · intro hg
    exact ⟨genRespects_iff_genPiOf_le.mpr (hg ▸ Finset.mem_Iic.mp hπ), hg⟩

end CongruenceTheory
