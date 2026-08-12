import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheory.ContentBounds
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.CompletePrimeLocalDefect
import CongruenceTheoryHigherOrder.PUnitConjugacyClass
import CongruenceTheoryHigherOrder.FloorSubadditivity
import CongruenceTheoryHigherOrder.ProdCoeffSupport
import CongruenceTheoryHigherOrder.DefectWeightedHomogeneous

/-!
**`thm:complete-prime-local`(iii), the "carry" case (`\sum_i(n_i\bmod p)\ge p`).** The defect
`\Delta_{\mathbf n}` has a coefficient not divisible by `p`, hence `v_p(\operatorname{cont}
\Delta_{\mathbf n})=0`. Assembled from `not_dvd_card_isConj_replicate_cycleType` (the Sylow-witness
conjugacy class is a `p`-unit), `sum_div_lt_div_sum_iff` (floor subadditivity forces no
block-respecting permutation to match the witness's cycle type), and
`coeff_finset_prod_eq_zero_of_forall_ne` (turning that into an exact vanishing of `\prod_iC(n_i)`'s
matching coefficient).
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`\Delta_{\mathbf n}` has a coefficient not divisible by `p`** whenever the residues
`n_i\bmod p` accumulate to at least `p` in total. -/
theorem exists_coeff_not_dvd_of_carry {r : ℕ} (n : Fin r → ℕ) (hn : ∀ i, 0 < n i) {p : ℕ}
    (hp : p.Prime) (hcarry : p ≤ ∑ i, (n i % p)) :
    ∃ d, ¬ (p : ℤ) ∣ coeff d (Delta n) := by
  set N := ∑ i, n i with hNdef
  set h := N / p with hhdef
  set s := N % p with hsdef
  have hpN : p ≤ N := by
    have hle : ∑ i, (n i % p) ≤ N := by
      rw [hNdef]
      exact Finset.sum_le_sum (fun i _ => Nat.mod_le (n i) p)
    omega
  obtain ⟨g, hg⟩ := exists_perm_replicate_cycleType hp hpN
  set d0 : ℕ →₀ ℕ := ciExp s (Multiset.replicate h p) with hd0def
  refine ⟨d0, ?_⟩
  have hCNcoeff : coeff d0 (C N) =
      ((Finset.univ.filter (fun x : Equiv.Perm (Fin N) => x.cycleType =
        Multiset.replicate h p)).card : ℤ) := by
    rw [← Cperm_eq_C]
    have hcc := coeff_sum_ci_eq_card_cycleType (α := Fin N) (Multiset.replicate h p)
      (fun x hx => by rw [Multiset.eq_of_mem_replicate hx]; exact hp.two_le)
    have hcard : Fintype.card (Fin N) = N := Fintype.card_fin N
    have hsum : (Multiset.replicate h p).sum = h * p := by
      rw [Multiset.sum_replicate, smul_eq_mul]
    rw [hcard, hsum] at hcc
    have hdm := Nat.div_add_mod N p
    have hNs0 : N - N / p * p = N % p := by rw [mul_comm]; omega
    rw [← hhdef, ← hsdef] at hNs0
    have hNs : N - h * p = s := hNs0
    rw [hNs] at hcc
    rw [hd0def]
    exact hcc
  have hfiltereq : (Finset.univ.filter (fun x : Equiv.Perm (Fin N) => x.cycleType =
      Multiset.replicate h p)) = (Finset.univ.filter (fun x : Equiv.Perm (Fin N) =>
        IsConj g x)) := by
    apply Finset.filter_congr
    intro x _
    rw [← hg, Equiv.Perm.isConj_iff_cycleType_eq]
    constructor <;> (intro heq; exact heq.symm)
  have hcardeq : (Finset.univ.filter (fun x : Equiv.Perm (Fin N) => x.cycleType =
      Multiset.replicate h p)).card = Nat.card {x : Equiv.Perm (Fin N) | IsConj g x} := by
    rw [hfiltereq, Nat.card_eq_fintype_card]
    simp [Fintype.card_subtype]
  have hnotdvdcard : ¬ p ∣ (Finset.univ.filter (fun x : Equiv.Perm (Fin N) => x.cycleType =
      Multiset.replicate h p)).card := by
    rw [hcardeq]
    exact not_dvd_card_isConj_replicate_cycleType hp hpN hg
  have hprodcoeff : coeff d0 (∏ i, C (n i)) = 0 := by
    apply coeff_finset_prod_eq_zero_of_forall_ne
    rintro ⟨e, hemem, hesum⟩
    have hspos : ∀ i, ∀ k, k ≠ 1 → k ≠ p → (e i) k = 0 := by
      intro i k hk1 hkp
      by_contra hne
      have hsum_apply : (∑ i, e i) k = ∑ i, (e i) k := by
        have hms := map_sum (Finsupp.applyAddHom k) e Finset.univ
        simp only [Finsupp.applyAddHom_apply] at hms
        exact hms
      rw [hesum] at hsum_apply
      have hd0k : d0 k = 0 := by
        rw [hd0def, ciExp_apply, Multiset.count_replicate]
        simp [hk1, Ne.symm hkp]
      rw [hd0k] at hsum_apply
      have hall0 : ∀ j, (e j) k = 0 := by
        intro j
        by_contra hjne
        have hpos : 0 < (e j) k := Nat.pos_of_ne_zero hjne
        have : (e j) k ≤ ∑ i, (e i) k :=
          Finset.single_le_sum (f := fun i => (e i) k) (fun i _ => Nat.zero_le _)
            (Finset.mem_univ j)
        omega
      exact hne (hall0 i)
    have hweight : ∀ i, (e i) 1 + (e i) p * p = n i := by
      intro i
      have hw := isWeightedHomogeneous_C (n i)
        (mem_support_iff.mp (hemem i (Finset.mem_univ i)))
      rw [Finsupp.weight_apply, Finsupp.sum] at hw
      have hsupp1 : (e i).support ⊆ {1, p} := by
        intro k hk
        by_contra hkmem
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hkmem
        exact (Finsupp.mem_support_iff.mp hk) (hspos i k hkmem.1 hkmem.2)
      rw [Finset.sum_subset hsupp1 (fun k _ hk =>
          by simp [Finsupp.notMem_support_iff.mp hk])] at hw
      by_cases hp1 : (1 : ℕ) = p
      · exact absurd hp1.symm hp.ne_one
      · rw [Finset.sum_pair hp1] at hw
        simpa [smul_eq_mul] using hw
    have hsumhi : ∑ i, (e i) p = h := by
      have hsum_apply : (∑ i, e i) p = ∑ i, (e i) p := by
        have hms := map_sum (Finsupp.applyAddHom p) e Finset.univ
        simp only [Finsupp.applyAddHom_apply] at hms
        exact hms
      rw [hesum] at hsum_apply
      rw [hd0def, ciExp_apply] at hsum_apply
      simp only [Multiset.count_replicate] at hsum_apply
      have hpne1 : ¬ (p : ℕ) = 1 := hp.ne_one
      simp [hpne1] at hsum_apply
      omega
    have hhile : ∀ i, (e i) p ≤ n i / p := by
      intro i
      have hwi := hweight i
      have hle : (e i) p * p ≤ n i := by
        have hle0 : (e i) p * p ≤ (e i) 1 + (e i) p * p := Nat.le_add_left _ _
        rw [hwi] at hle0
        exact hle0
      exact (Nat.le_div_iff_mul_le hp.pos).mpr hle
    have hlesum : ∑ i, (e i) p ≤ ∑ i, (n i / p) := Finset.sum_le_sum (fun i _ => hhile i)
    have hltdiv : ∑ i, (n i / p) < N / p := (sum_div_lt_div_sum_iff n p hp.pos).mpr hcarry
    rw [hsumhi] at hlesum
    rw [hhdef] at hlesum
    omega
  have hDeltacoeff : coeff d0 (Delta n) = coeff d0 (C N) - coeff d0 (∏ i, C (n i)) := by
    unfold Delta
    rw [coeff_sub, hNdef]
  rw [hDeltacoeff, hCNcoeff, hprodcoeff, sub_zero]
  intro hcon
  apply hnotdvdcard
  have h2 := Int.natCast_dvd_natCast.mp (by exact_mod_cast hcon)
  exact h2

#print axioms exists_coeff_not_dvd_of_carry

end CongruenceTheory
