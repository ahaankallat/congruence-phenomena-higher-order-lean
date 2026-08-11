import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.DefectValuationExactWeight
import CongruenceTheoryHigherOrder.CycleDepthHierarchy
import CongruenceTheoryHigherOrder.CommonPrimeClassificationDepthLowerBound
import CongruenceTheoryHigherOrder.CommonPrimeClassificationDepthSharpness
import CongruenceTheoryHigherOrder.MicroblockPartition

/-!
**`thm:common-prime-classification`'s witness-depth formula, fully assembled.** Writing
`E:=\min W_p(\lambda;\mathbf u)` (as in `common_prime_classification_valuation`) and
`k_{\min}:=\min\{k(\lambda): A_\lambda(\mathbf u)>0, W_p(\lambda;\mathbf u)=E\}`: `k_{\min}\ge1`
(every non-refining shape has a part `\ge2`, since it merges at least two distinct macroblocks),
`p^{E+1}\mid D_s(\Delta_{p\mathbf u})` for every `1\le s<k_{\min}`
(`dvd_Dgcd_of_kmin_gt`), and `p^{E+1}\nmid D_{k_{\min}}(\Delta_{p\mathbf u})`
(`exists_coeff_nontrivialPartCount_eq_not_dvd_pow_succ`) -- together with `p^E` always dividing
`D_s` (`dvd_coeff_defect_Wp`), this pins `v_p(D_{k_{\min}})=E` exactly and `v_p(D_s)>E` for
`s<k_{\min}`, matching `def:prime-cycle-depth`'s `\delta_p(p\mathbf u)=k_{\min}`.
-/

namespace CongruenceTheory

open MvPolynomial
open scoped Classical

/-- **A non-refining partition has a part spanning `\ge2` macroblocks.** -/
theorem exists_ge_two_of_not_le_macroPartition {r : ℕ} (u : Fin r → ℕ)
    {π : GenPartLat (MicroIdx u)} (hπ : ¬ π ≤ macroPartition u) :
    ∃ B ∈ π.parts, 2 ≤ B.card := by
  by_contra hcon
  push_neg at hcon
  apply hπ
  intro b hb
  have hbcard : b.card ≤ 1 := by have := hcon b hb; omega
  obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts hb
  have hbsingle : b = {x} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hx, fun y hy => ((Finset.card_le_one.mp hbcard) x hx y hy).symm⟩
  refine ⟨(macroPartition u).part x, (macroPartition u).part_mem.mpr (Finset.mem_univ x), ?_⟩
  rw [hbsingle]
  intro z hz
  rw [Finset.mem_singleton] at hz
  rw [hz]
  exact (macroPartition u).mem_part_self.mpr (Finset.mem_univ x)

/-- **Every shape achieved by a non-refining partition has at least one part `\ge2`.** -/
theorem one_le_card_filter_of_mem_image {r : ℕ} (u : Fin r → ℕ) {lam : Multiset ℕ}
    (hlam : lam ∈ (nonRefiningPartitions u).image GenPartLatShape) :
    1 ≤ (lam.filter (2 ≤ ·)).card := by
  obtain ⟨π, hπmem, hπeq⟩ := Finset.mem_image.mp hlam
  unfold nonRefiningPartitions at hπmem
  rw [Finset.mem_filter] at hπmem
  obtain ⟨B, hBmem, hBcard⟩ := exists_ge_two_of_not_le_macroPartition u hπmem.2
  have hmem : B.card ∈ lam.filter (2 ≤ ·) := by
    rw [← hπeq]
    unfold GenPartLatShape
    rw [Multiset.mem_filter]
    exact ⟨Multiset.mem_map.mpr ⟨B, hBmem, rfl⟩, hBcard⟩
  have hne : lam.filter (2 ≤ ·) ≠ 0 := fun h0 => by
    rw [h0] at hmem; exact absurd hmem (Multiset.notMem_zero _)
  have hpos : 0 < (lam.filter (2 ≤ ·)).card := Multiset.card_pos.mpr hne
  omega

/-- **Every `j\ge2` layer exponent is `\ge1`.** -/
theorem card_le_sum_firstPrimeLayerExponent (p : ℕ) (lam : Multiset ℕ) :
    (lam.filter (2 ≤ ·)).card ≤ (lam.map (firstPrimeLayerExponent p)).sum := by
  induction lam using Multiset.induction with
  | empty => simp
  | cons j s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons]
    by_cases hj2 : 2 ≤ j
    · rw [Multiset.filter_cons_of_pos (p := fun x => 2 ≤ x) s hj2, Multiset.card_cons]
      have : 1 ≤ firstPrimeLayerExponent p j := by unfold firstPrimeLayerExponent; omega
      omega
    · rw [Multiset.filter_cons_of_neg (p := fun x => 2 ≤ x) s hj2]
      omega

/-- **`W_p(\lambda;\mathbf u)\ge1`** for every achieved shape `\lambda`. -/
theorem one_le_Wp_of_mem_image {r : ℕ} (u : Fin r → ℕ) {p : ℕ} {lam : Multiset ℕ}
    (hlam : lam ∈ (nonRefiningPartitions u).image GenPartLatShape) : 1 ≤ Wp u p lam := by
  have h1 := one_le_card_filter_of_mem_image u hlam
  have h2 := card_le_sum_firstPrimeLayerExponent p lam
  unfold Wp
  omega

/-- **`thm:common-prime-classification`'s witness-depth formula, fully assembled.** For `E`
the minimum `W_p`-weight among achieved shapes, `k_{\min}` is `\ge1` and is the least `s\ge1`
with `v_p(D_s(\Delta_{p\mathbf u}))=E`. -/
theorem common_prime_classification_depth {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ)
    (hu : ∀ i, 0 < u i) {p : ℕ} [Fact (Nat.Prime p)] (E : ℕ)
    (hE : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape, E ≤ Wp u p lam)
    (lamE : Multiset ℕ) (hlamEmem : lamE ∈ (nonRefiningPartitions u).image GenPartLatShape)
    (hlamEeq : Wp u p lamE = E) :
    ∃ kmin : ℕ, 1 ≤ kmin ∧
      IsLeast {s : ℕ | 1 ≤ s ∧
          (Dgcd (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) s).factorization p = E} kmin := by
  have hp : p.Prime := Fact.out
  set Simg := (nonRefiningPartitions u).image GenPartLatShape with hSimg
  set SE := Simg.filter (fun lam => Wp u p lam = E) with hSE
  have hlamESE : lamE ∈ SE := by rw [hSE, Finset.mem_filter]; exact ⟨hlamEmem, hlamEeq⟩
  set K := SE.image (fun lam => (lam.filter (2 ≤ ·)).card) with hK
  have hKne : K.Nonempty := ⟨_, Finset.mem_image_of_mem _ hlamESE⟩
  set kmin := K.min' hKne with hkmindef
  have hkminmem : kmin ∈ K := Finset.min'_mem K hKne
  obtain ⟨lam0, hlam0SE, hlam0k⟩ := Finset.mem_image.mp hkminmem
  have hkmin_le : ∀ lam ∈ SE, kmin ≤ (lam.filter (2 ≤ ·)).card := by
    intro lam hlam
    rw [hkmindef]
    exact Finset.min'_le K _ (Finset.mem_image_of_mem _ hlam)
  rw [Finset.mem_filter] at hlam0SE
  obtain ⟨hlam0mem, hlam0E⟩ := hlam0SE
  have hkmin1 : 1 ≤ kmin := by rw [← hlam0k]; exact one_le_card_filter_of_mem_image u hlam0mem
  set Smin := SE.filter (fun lam => (lam.filter (2 ≤ ·)).card = kmin) with hSmin
  have hlam0Smin : lam0 ∈ Smin := by
    rw [hSmin, Finset.mem_filter]
    exact ⟨Finset.mem_filter.mpr ⟨hlam0mem, hlam0E⟩, hlam0k⟩
  have hSminne : Smin.Nonempty := ⟨lam0, hlam0Smin⟩
  obtain ⟨lamMin, hlamMinSmin, hlamMinmin⟩ :=
    Smin.exists_min_image (fun lam => Multiset.count 1 lam) hSminne
  rw [hSmin, Finset.mem_filter, hSE, Finset.mem_filter] at hlamMinSmin
  obtain ⟨⟨hlamMinmem, hlamMinE⟩, hlamMink⟩ := hlamMinSmin
  have hlamMinm1 : ∀ lam ∈ Simg, Wp u p lam = E → (lam.filter (2 ≤ ·)).card = kmin →
      Multiset.count 1 lamMin ≤ Multiset.count 1 lam := by
    intro lam hlammem hlamE hlamk
    exact hlamMinmin lam (by
      rw [hSmin, Finset.mem_filter, hSE, Finset.mem_filter]
      exact ⟨⟨hlammem, hlamE⟩, hlamk⟩)
  have hkmin_le' : ∀ lam ∈ Simg, Wp u p lam = E → kmin ≤ (lam.filter (2 ≤ ·)).card := by
    intro lam hlammem hlamE
    exact hkmin_le lam (Finset.mem_filter.mpr ⟨hlammem, hlamE⟩)
  refine ⟨kmin, hkmin1, ⟨⟨hkmin1, ?_⟩, ?_⟩⟩
  · -- v_p(D_kmin) = E
    obtain ⟨d, hdcount, hdndvd⟩ :=
      exists_coeff_nontrivialPartCount_eq_not_dvd_pow_succ hr u hu E kmin hE hkmin_le' lamMin
        hlamMinmem hlamMinE hlamMink hlamMinm1
    have hnatEdvd : p ^ E ∣ Dgcd (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) kmin := by
      unfold Dgcd
      apply Finset.dvd_gcd
      intro d' hd'
      rw [Finset.mem_filter] at hd'
      have hbound := dvd_coeff_defect_Wp hr u hu hp E hE d'
      have h1 := Int.natAbs_dvd_natAbs.mpr hbound
      rwa [Int.natAbs_pow, Int.natAbs_natCast] at h1
    have hdz : coeff d (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) ≠ 0 := by
      intro h0
      apply hdndvd
      rw [h0]
      exact dvd_zero _
    have hddvd_gcd : Dgcd (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) kmin ∣
        (coeff d (C ((∑ i, u i) * p) - ∏ i, C (u i * p))).natAbs := by
      unfold Dgcd
      apply Finset.gcd_dvd
      rw [Finset.mem_filter]
      exact ⟨mem_support_iff.mpr hdz, le_of_eq hdcount⟩
    have hnatE1ndvd : ¬ p ^ (E + 1) ∣ Dgcd (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) kmin := by
      intro hcon
      apply hdndvd
      have h1 : p ^ (E + 1) ∣ (coeff d (C ((∑ i, u i) * p) - ∏ i, C (u i * p))).natAbs :=
        dvd_trans hcon hddvd_gcd
      have h2 : ((p ^ (E + 1) : ℕ) : ℤ) ∣
          ((coeff d (C ((∑ i, u i) * p) - ∏ i, C (u i * p))).natAbs : ℤ) :=
        Int.natCast_dvd_natCast.mpr h1
      rw [Int.dvd_natAbs] at h2
      push_cast at h2
      exact h2
    have hDkminne : Dgcd (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) kmin ≠ 0 := by
      intro h0
      apply hnatE1ndvd
      rw [h0]
      exact dvd_zero _
    have hge := (Nat.Prime.pow_dvd_iff_le_factorization hp hDkminne).mp hnatEdvd
    have hle : (Dgcd (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) kmin).factorization p ≤ E := by
      by_contra hcon
      push_neg at hcon
      exact hnatE1ndvd ((Nat.Prime.pow_dvd_iff_le_factorization hp hDkminne).mpr hcon)
    omega
  · -- kmin is a lower bound: any s with v_p(D_s)=E has s ≥ kmin
    rintro s ⟨hs1, hsE⟩
    by_contra hlt
    push_neg at hlt
    have hs : ∀ lam ∈ Simg, (lam.filter (2 ≤ ·)).card ≤ s → E + 1 ≤ Wp u p lam := by
      intro lam hlammem hlamcard
      by_cases hlamE : Wp u p lam = E
      · exfalso
        have := hkmin_le' lam hlammem hlamE
        omega
      · have := hE lam hlammem
        omega
    have hE1dvd : (p : ℕ) ^ (E + 1) ∣ Dgcd (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) s :=
      dvd_Dgcd_of_kmin_gt hr u hu hp E s hs
    by_cases hDsz : Dgcd (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) s = 0
    · rw [hDsz] at hsE
      simp only [Nat.factorization_zero, Finsupp.coe_zero, Pi.zero_apply] at hsE
      have hE1 := one_le_Wp_of_mem_image (p := p) u hlamEmem
      omega
    · have := (Nat.Prime.pow_dvd_iff_le_factorization hp hDsz).mp hE1dvd
      omega

#print axioms exists_ge_two_of_not_le_macroPartition
#print axioms one_le_card_filter_of_mem_image
#print axioms card_le_sum_firstPrimeLayerExponent
#print axioms one_le_Wp_of_mem_image
#print axioms common_prime_classification_depth

end CongruenceTheory
