import Mathlib
import CongruenceTheory.Perm
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC

/-!
**The count of full cycles**: `Fintype.card {g : Equiv.Perm (Fin (m+1)) // g.IsCycle ∧
g.support = Finset.univ} = m!` — the classical "number of cyclic permutations of `n` points is
`(n-1)!`" fact, needed (combined with `FullCycleConnected.lean`/`CiFullCycle.lean`) to complete
(A3)'s combinatorial claim ("the coefficient of `X_{jp}` in `K_j(p)` is `(jp-1)!`"). Built
entirely from `CpermEqC.lean`'s existing `CycleTuple`/`cyc`/`cyc_injective`/`card_CycleTuple`/
`exists_decomp_pos` machinery (built there for an unrelated purpose, `Cperm_eq_C`) — no new
combinatorial infrastructure, purely permutation/`Finset` reasoning (deliberately avoiding
`MvPolynomial`, which proved pathologically slow to elaborate for a related lemma attempted
earlier).
-/

namespace CongruenceTheory

open Equiv Equiv.Perm

open scoped Classical

variable (m : ℕ)

theorem cycleCompl_self_false (t : CycleTuple m m) (x : Fin (m + 1)) : ¬ CycleCompl m m t x := by
  rw [not_CycleCompl_iff]
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · right
    have hcard : Fintype.card (Fin m) = Fintype.card (NZ m) := by
      rw [Fintype.card_fin, card_NZ]
    have hbij : Function.Bijective (t : Fin m → NZ m) :=
      (Fintype.bijective_iff_injective_and_card (t : Fin m → NZ m)).mpr ⟨t.injective, hcard⟩
    obtain ⟨i, hi⟩ := hbij.surjective ⟨x, hx0⟩
    exact ⟨i, congrArg Subtype.val hi⟩

theorem ofSubtype_eq_one_of_isEmpty {α : Type*} [DecidableEq α] {p : α → Prop} [DecidablePred p]
    (hp : ∀ x, ¬ p x) (h : Equiv.Perm {x // p x}) : Equiv.Perm.ofSubtype h = 1 := by
  ext x
  rw [Equiv.Perm.ofSubtype_apply_of_not_mem h (hp x)]
  rfl

theorem cyc_support_eq_univ (t : CycleTuple m m) (hm : 1 ≤ m) :
    (cyc m m t).support = Finset.univ := by
  rw [cyc_support_eq m m t hm]
  apply Finset.eq_univ_of_card
  rw [List.toFinset_card_of_nodup (cycleList_nodup m m t), cycleList_length, Fintype.card_fin]

theorem cyc_surjective_of_full_cycle (hm : 1 ≤ m) (g : Equiv.Perm (Fin (m + 1)))
    (hcyc : g.IsCycle) (hsupp : g.support = Finset.univ) :
    ∃ t : CycleTuple m m, cyc m m t = g := by
  have h0 : (0 : Fin (m + 1)) ∈ g.support := hsupp ▸ Finset.mem_univ 0
  have hcycOf : g.cycleOf 0 = g := hcyc.cycleOf_eq (Equiv.Perm.mem_support.mp h0)
  have hcard : (g.cycleOf 0).support.card = m + 1 := by
    rw [hcycOf, hsupp]; simp
  obtain ⟨t, h, hgassemble⟩ := exists_decomp_pos m m g hm hcard
  refine ⟨t, ?_⟩
  have heq1 : Equiv.Perm.ofSubtype h = 1 :=
    ofSubtype_eq_one_of_isEmpty (cycleCompl_self_false m t) h
  rw [← hgassemble]
  unfold gAssemble
  rw [heq1, mul_one]

/-- **The number of full `(m+1)`-cycles is `m!`.** -/
theorem card_fullCycle (hm : 1 ≤ m) :
    Fintype.card {g : Equiv.Perm (Fin (m + 1)) // g.IsCycle ∧ g.support = Finset.univ} =
      Nat.factorial m := by
  set F : CycleTuple m m → {g : Equiv.Perm (Fin (m + 1)) // g.IsCycle ∧ g.support = Finset.univ} :=
    fun t => ⟨cyc m m t, cyc_isCycle_of_pos m m t hm, cyc_support_eq_univ m t hm⟩ with hF_def
  have hFinj : Function.Injective F := by
    intro t1 t2 heq
    exact cyc_injective m m hm t1 t2 (congrArg Subtype.val heq)
  have hFsurj : Function.Surjective F := by
    intro g
    obtain ⟨t, ht⟩ := cyc_surjective_of_full_cycle m hm g.1 g.2.1 g.2.2
    exact ⟨t, Subtype.ext ht⟩
  have hbij : Function.Bijective F := ⟨hFinj, hFsurj⟩
  rw [← Fintype.card_congr (Equiv.ofBijective F hbij), card_CycleTuple, Nat.descFactorial_self]

#print axioms card_fullCycle

end CongruenceTheory
