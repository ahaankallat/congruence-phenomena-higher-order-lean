import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheory.ContentBounds
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.CompletePrimeLocalDefect
import CongruenceTheoryHigherOrder.PUnitConjugacyClassResidual
import CongruenceTheoryHigherOrder.ProdCoeffSupport
import CongruenceTheoryHigherOrder.DefectWeightedHomogeneous

/-!
**`thm:complete-prime-local`(iii), the "no-carry" (residual-cycle) case** (`\sum_i(n_i\bmod p)<p`,
`|U_p(\mathbf n)|\ge2`). The defect `\Delta_{\mathbf n}` has a coefficient not divisible by `p`,
hence `v_p(\operatorname{cont}\Delta_{\mathbf n})=0`. At the monomial for cycle type "`h` disjoint
`p`-cycles plus one `s`-cycle" (`N=hp+s`), a block-respecting permutation would need *every*
element allocated to a `p`-cycle or the single `s`-cycle (no fixed points at all, since the
monomial has no weight at position `1`), forcing all but *one* block to have `p`-divisible size —
impossible when `\ge2` blocks have `p\nmid n_i`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`\Delta_{\mathbf n}` has a coefficient not divisible by `p`** whenever `N=hp+s`
(`2\le s<p`) and at least two indices have `p\nmid n_i`. -/
theorem exists_coeff_not_dvd_of_no_carry {r : ℕ} (n : Fin r → ℕ) {p : ℕ} (hp : p.Prime)
    {h s : ℕ} (hs2 : 2 ≤ s) (hslt : s < p) (hN : (∑ i, n i) = h * p + s)
    (hU2 : ∃ i0 i1 : Fin r, i0 ≠ i1 ∧ ¬ p ∣ n i0 ∧ ¬ p ∣ n i1) :
    ∃ d, ¬ (p : ℤ) ∣ coeff d (Delta n) := by
  set N := ∑ i, n i with hNdef
  obtain ⟨g, hg⟩ := exists_perm_replicate_add_singleton_cycleType (N := N) hp hs2 hN
  set d0 : ℕ →₀ ℕ := ciExp 0 (Multiset.replicate h p + {s}) with hd0def
  refine ⟨d0, ?_⟩
  have hCNcoeff : coeff d0 (C N) =
      ((Finset.univ.filter (fun x : Equiv.Perm (Fin N) => x.cycleType =
        Multiset.replicate h p + {s})).card : ℤ) := by
    rw [← Cperm_eq_C]
    have hcc := coeff_sum_ci_eq_card_cycleType (α := Fin N) (Multiset.replicate h p + {s})
      (fun x hx => by
        rw [Multiset.mem_add] at hx
        rcases hx with hx | hx
        · rw [Multiset.eq_of_mem_replicate hx]; exact hp.two_le
        · rw [Multiset.mem_singleton.mp hx]; exact hs2)
    have hcard : Fintype.card (Fin N) = N := Fintype.card_fin N
    have hsum0 : (Multiset.replicate h p + ({s} : Multiset ℕ)).sum = N := by
      rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, Multiset.sum_singleton]
      exact hN.symm
    rw [hcard, hsum0, Nat.sub_self] at hcc
    rw [hd0def]
    exact hcc
  have hfiltereq : (Finset.univ.filter (fun x : Equiv.Perm (Fin N) => x.cycleType =
      Multiset.replicate h p + {s})) = (Finset.univ.filter (fun x : Equiv.Perm (Fin N) =>
        IsConj g x)) := by
    apply Finset.filter_congr
    intro x _
    rw [← hg, Equiv.Perm.isConj_iff_cycleType_eq]
    constructor <;> (intro heq; exact heq.symm)
  have hcardeq : (Finset.univ.filter (fun x : Equiv.Perm (Fin N) => x.cycleType =
      Multiset.replicate h p + {s})).card = Nat.card {x : Equiv.Perm (Fin N) | IsConj g x} := by
    rw [hfiltereq, Nat.card_eq_fintype_card]
    simp [Fintype.card_subtype]
  have hnotdvdcard : ¬ p ∣ (Finset.univ.filter (fun x : Equiv.Perm (Fin N) => x.cycleType =
      Multiset.replicate h p + {s})).card := by
    rw [hcardeq]
    exact not_dvd_card_isConj_replicate_add_singleton_cycleType hp hs2 hslt hN hg
  have hprodcoeff : coeff d0 (∏ i, C (n i)) = 0 := by
    apply coeff_finset_prod_eq_zero_of_forall_ne
    rintro ⟨e, hemem, hesum⟩
    obtain ⟨i0, i1, hi01, hni0, hni1⟩ := hU2
    have hspos : ∀ i, ∀ k, k ≠ p → k ≠ s → (e i) k = 0 := by
      intro i k hkp hks
      by_contra hne
      have hsum_apply : (∑ i, e i) k = ∑ i, (e i) k := by
        have hms := map_sum (Finsupp.applyAddHom k) e Finset.univ
        simp only [Finsupp.applyAddHom_apply] at hms
        exact hms
      rw [hesum] at hsum_apply
      have hd0k : d0 k = 0 := by
        rw [hd0def, ciExp_apply, Multiset.count_add, Multiset.count_replicate]
        simp [hkp, hks, Ne.symm hkp, Ne.symm hks]
      rw [hd0k] at hsum_apply
      have hall0 : ∀ j, (e j) k = 0 := by
        intro j
        by_contra hjne
        have hpos : 0 < (e j) k := Nat.pos_of_ne_zero hjne
        have hle : (e j) k ≤ ∑ i, (e i) k :=
          Finset.single_le_sum (f := fun i => (e i) k) (fun i _ => Nat.zero_le _)
            (Finset.mem_univ j)
        omega
      exact hne (hall0 i)
    have hweight : ∀ i, (e i) p * p + (e i) s * s = n i := by
      intro i
      have hw := isWeightedHomogeneous_C (n i)
        (mem_support_iff.mp (hemem i (Finset.mem_univ i)))
      rw [Finsupp.weight_apply, Finsupp.sum] at hw
      have hsupp1 : (e i).support ⊆ {p, s} := by
        intro k hk
        by_contra hkmem
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hkmem
        exact (Finsupp.mem_support_iff.mp hk) (hspos i k hkmem.1 hkmem.2)
      rw [Finset.sum_subset hsupp1 (fun k _ hk =>
          by simp [Finsupp.notMem_support_iff.mp hk])] at hw
      have hpsne : p ≠ s := hslt.ne'
      rw [Finset.sum_pair hpsne] at hw
      simpa [smul_eq_mul] using hw
    have hsumsval : ∑ i, (e i) s = 1 := by
      have hsum_apply : (∑ i, e i) s = ∑ i, (e i) s := by
        have hms := map_sum (Finsupp.applyAddHom s) e Finset.univ
        simp only [Finsupp.applyAddHom_apply] at hms
        exact hms
      rw [hesum] at hsum_apply
      rw [hd0def, ciExp_apply, Multiset.count_add, Multiset.count_replicate,
        Multiset.count_singleton_self] at hsum_apply
      have hpsne' : ¬ (p : ℕ) = s := hslt.ne'
      simp [hpsne'] at hsum_apply
      omega
    have hblockdvd : ∀ i, (e i) s = 0 → p ∣ n i := by
      intro i hei0
      have hwi := hweight i
      rw [hei0, zero_mul, add_zero] at hwi
      exact ⟨(e i) p, by rw [mul_comm]; exact hwi.symm⟩
    have hor : (e i0) s = 0 ∨ (e i1) s = 0 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨hc0, hc1⟩ := hcon
      have hp0 : 1 ≤ (e i0) s := Nat.one_le_iff_ne_zero.mpr hc0
      have hp1 : 1 ≤ (e i1) s := Nat.one_le_iff_ne_zero.mpr hc1
      have hle : (e i0) s + (e i1) s ≤ ∑ k, (e k) s := by
        have hsub : ({i0, i1} : Finset (Fin r)) ⊆ Finset.univ := Finset.subset_univ _
        have hss := Finset.sum_le_sum_of_subset (f := fun k => (e k) s) hsub
        rw [Finset.sum_pair hi01] at hss
        exact hss
      omega
    rcases hor with h0 | h1
    · exact hni0 (hblockdvd i0 h0)
    · exact hni1 (hblockdvd i1 h1)
  have hDeltacoeff : coeff d0 (Delta n) = coeff d0 (C N) - coeff d0 (∏ i, C (n i)) := by
    unfold Delta
    rw [coeff_sub, hNdef]
  rw [hDeltacoeff, hCNcoeff, hprodcoeff, sub_zero]
  intro hcon
  apply hnotdvdcard
  have h2 := Int.natCast_dvd_natCast.mp (by exact_mod_cast hcon)
  exact h2

#print axioms exists_coeff_not_dvd_of_no_carry

end CongruenceTheory
