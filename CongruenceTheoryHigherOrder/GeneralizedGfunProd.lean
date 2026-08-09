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
import CongruenceTheoryHigherOrder.GeneralizedAssembleTop
import CongruenceTheoryHigherOrder.GeneralizedPiOfAssemble
import CongruenceTheoryHigherOrder.GeneralizedGfunTopK
import CongruenceTheoryHigherOrder.A3Final

/-!
**The central (A4) factoring theorem**: `GenGfun τ = ∏_{B∈τ.parts} K B.card q`.
-/

namespace CongruenceTheory

open Equiv

open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

theorem genGfun_eq_prod_K (τ : GenPartLat ι) :
    GenGfun (q := q) τ = ∏ B ∈ τ.parts, K B.card q := by
  have hstep1 : GenGfun (q := q) τ =
      ∑ p : GenPartitionPerm (q := q) τ,
        (if (∀ B : τ.parts, genPiOf ((genBlockTypeEquiv (B : Finset ι)).permCongr (p B)) = ⊤)
          then p.ciProd else 0) := by
    unfold GenGfun
    rw [Finset.sum_filter]
    rw [show (∑ g : Equiv.Perm (ι × Fin q), if genPiOf g = τ then ci g else 0) =
        ∑ g ∈ (Finset.univ : Finset (Equiv.Perm (ι × Fin q))).filter (GenRespects τ),
          (if genPiOf g = τ then ci g else 0) from by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro g _ hgnot
      rw [Finset.mem_filter] at hgnot
      push Not at hgnot
      rw [if_neg (fun hg => hgnot (Finset.mem_univ g) (genRespects_of_genPiOf_le (le_of_eq hg)))]]
    rw [Finset.sum_subtype (p := GenRespects τ)
      ((Finset.univ : Finset (Equiv.Perm (ι × Fin q))).filter (GenRespects τ)) (fun g => by simp)
      (fun g => if genPiOf g = τ then ci g else 0)]
    rw [← Equiv.sum_comp (genAssembleEquiv τ)
      (fun g : {g : Equiv.Perm (ι × Fin q) // GenRespects τ g} =>
        if genPiOf g.1 = τ then ci g.1 else 0)]
    apply Finset.sum_congr rfl
    intro p _
    show (if genPiOf (genAssembleEquiv τ p).1 = τ then ci (genAssembleEquiv τ p).1 else 0) = _
    rw [show (genAssembleEquiv τ p).1 = genAssemble p from rfl]
    rw [gen_ci_assemble]
    by_cases hcond : (∀ B : τ.parts, genPiOf ((genBlockTypeEquiv (B : Finset ι)).permCongr (p B)) = ⊤)
    · rw [if_pos ((genPiOf_assemble_eq_tau_iff p).mpr hcond), if_pos hcond]
    · rw [if_neg (fun hc => hcond ((genPiOf_assemble_eq_tau_iff p).mp hc)), if_neg hcond]
  have hstep2 : ∀ p : GenPartitionPerm (q := q) τ,
      (if (∀ B : τ.parts, genPiOf ((genBlockTypeEquiv (B : Finset ι)).permCongr (p B)) = ⊤)
          then p.ciProd else 0) =
        ∏ B : τ.parts, (if genPiOf ((genBlockTypeEquiv (B : Finset ι)).permCongr (p B)) = ⊤
          then ci (p B) else 0) := by
    intro p
    unfold GenPartitionPerm.ciProd
    by_cases hcond : (∀ B : τ.parts, genPiOf ((genBlockTypeEquiv (B : Finset ι)).permCongr (p B)) = ⊤)
    · rw [if_pos hcond]
      exact Finset.prod_congr rfl (fun B _ => by rw [if_pos (hcond B)])
    · rw [if_neg hcond]
      push Not at hcond
      obtain ⟨B0, hB0⟩ := hcond
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ B0)
      rw [if_neg hB0]
  rw [hstep1, Finset.sum_congr rfl (fun p _ => hstep2 p)]
  rw [show (∏ B ∈ τ.parts, K B.card q) = ∏ B : τ.parts, K (B : Finset ι).card q from
    (Finset.prod_attach τ.parts (fun B => K B.card q)).symm]
  refine Eq.trans (Fintype.prod_sum
    (fun (B : τ.parts) (h : Equiv.Perm (genBlockType (q := q) (B : Finset ι))) =>
      if genPiOf ((genBlockTypeEquiv (B : Finset ι)).permCongr h) = ⊤ then ci h else 0)).symm
    (Finset.prod_congr rfl (fun B _ => ?_))
  have hsum_eq : (∑ h : Equiv.Perm (genBlockType (q := q) (B : Finset ι)),
      if genPiOf ((genBlockTypeEquiv (B : Finset ι)).permCongr h) = ⊤ then ci h else 0) =
      GenGfun (q := q) (⊤ : GenPartLat (B : Finset ι)) := by
    unfold GenGfun
    rw [Finset.sum_filter]
    rw [← Equiv.sum_comp (genBlockTypeEquiv (B : Finset ι)).permCongr
      (fun h' : Equiv.Perm (↥(B : Finset ι) × Fin q) => if genPiOf h' = ⊤ then ci h' else 0)]
    exact Finset.sum_congr rfl (fun h _ => by rw [ci_permCongr])
  rw [hsum_eq, genGfun_top_eq_K]
  congr 1
  exact Fintype.card_coe (B : Finset ι)

end CongruenceTheory
