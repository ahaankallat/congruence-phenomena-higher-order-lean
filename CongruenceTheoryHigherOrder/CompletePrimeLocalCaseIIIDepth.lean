import Mathlib
import CongruenceTheoryHigherOrder.DeltaOrderAssembly
import CongruenceTheoryHigherOrder.DeltaZeroFree
import CongruenceTheoryHigherOrder.WeightedOrder
import CongruenceTheoryHigherOrder.CycleDepthHierarchy
import CongruenceTheoryHigherOrder.GaussLemmaModP

/-!
**`thm:complete-prime-local`(iii)'s depth theorem, fully assembled (the `R\ge2` case).**
Connects `DeltaOrderAssembly.lean`'s `WOrder nontrivialWeight (\Delta_{\mathbf
n}.\text{map}(\Z/p)) p^\kappa` back to the concrete `Dgcd`/depth characterization used
throughout this project (`CycleDepthHierarchy.lean`, matching
`common_prime_classification_depth`'s own `IsLeast` style): `p^\kappa` is the *least* `s\ge1`
with `Dgcd(\Delta_{\mathbf n},s)` nonzero and not a multiple of `p`.

The `\text{Dgcd}\ne0` qualifier is unavoidable and mathematically correct: `\text{Dgcd}(\varphi,
s)` is `0` exactly when no monomial of `\varphi` has `\text{nontrivialPartCount}\le s` (an empty
gcd), in which case "depth `s`" is not a meaningful witness at all (its factorization is
vacuously `0` for every prime, which is not evidence of anything). Restricting the least-depth
search to genuine (nonzero) witnesses is the honest reading of "depth" and is exactly what is
needed for the least element to be well-defined.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`d` lies in `(\varphi.\text{map}(\Z/p)).\text{support}` iff `p\nmid\text{coeff}_d\varphi`.**
-/
theorem mem_support_map_iff {φ : MvPolynomial ℕ ℤ} {p : ℕ} [Fact p.Prime] (d : ℕ →₀ ℕ) :
    d ∈ (MvPolynomial.map (Int.castRingHom (ZMod p)) φ).support ↔
      ¬ ((p : ℤ) ∣ MvPolynomial.coeff d φ) := by
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map, Int.coe_castRingHom]
  exact not_congr (ZMod.intCast_zmod_eq_zero_iff_dvd _ _)

/-- **The full `thm:complete-prime-local`(iii) depth theorem, `R\ge2` case.** `p^\kappa` is the
least `s\ge1` at which `\text{Dgcd}(\Delta_{\mathbf n},s)` is both nonzero and not divisible by
`p`. -/
theorem complete_prime_local_case_iii_depth {r : ℕ} (n : Fin r → ℕ) {p : ℕ} (hp : p.Prime)
    (hR2 : 2 ≤ RTot n p) (hRp : RTot n p ≤ p - 1)
    (hDcne : Dc p (RTot n p) (HTot n p) (cCount n p) ≠ 0) :
    ∃ κ : ℕ, IsLeast {s : ℕ | 1 ≤ s ∧ Dgcd (Delta n) s ≠ 0 ∧
        (Dgcd (Delta n) s).factorization p = 0} (p ^ κ) := by
  haveI := Fact.mk hp
  obtain ⟨κ, hWOrder⟩ := WOrder_Delta_map n hp hR2 hRp hDcne
  refine ⟨κ, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero κ hp.pos.ne')
  · -- Dgcd (Delta n) (p^κ) ≠ 0
    obtain ⟨d₀, hd₀mem, hd₀deg⟩ := hWOrder.2
    have hd₀memΔ : d₀ ∈ (Delta n).support :=
      Finset.mem_of_subset
        (MvPolynomial.support_map_subset (Int.castRingHom (ZMod p)) (Delta n)) hd₀mem
    have hd₀0 : d₀ 0 = 0 := apply_zero_eq_zero_of_mem_support_Delta n d₀ hd₀memΔ
    have hd₀npc : nontrivialPartCount d₀ = p ^ κ := by
      rw [← wDeg_nontrivialWeight_eq d₀ hd₀0]
      exact hd₀deg
    have hd₀filt : d₀ ∈ (Delta n).support.filter (fun d => nontrivialPartCount d ≤ p ^ κ) :=
      Finset.mem_filter.mpr ⟨hd₀memΔ, le_of_eq hd₀npc⟩
    intro h0
    unfold Dgcd at h0
    have hdvd : (Finset.gcd ((Delta n).support.filter
        (fun d => nontrivialPartCount d ≤ p ^ κ)) (fun d => (coeff d (Delta n)).natAbs)) ∣
        (coeff d₀ (Delta n)).natAbs := Finset.gcd_dvd hd₀filt
    rw [h0] at hdvd
    have : coeff d₀ (Delta n) = 0 := by
      have := Nat.eq_zero_of_zero_dvd hdvd
      exact Int.natAbs_eq_zero.mp this
    exact (MvPolynomial.mem_support_iff.mp hd₀memΔ) this
  · -- factorization p = 0
    obtain ⟨d₀, hd₀mem, hd₀deg⟩ := hWOrder.2
    have hd₀memΔ : d₀ ∈ (Delta n).support :=
      Finset.mem_of_subset
        (MvPolynomial.support_map_subset (Int.castRingHom (ZMod p)) (Delta n)) hd₀mem
    have hd₀0 : d₀ 0 = 0 := apply_zero_eq_zero_of_mem_support_Delta n d₀ hd₀memΔ
    have hd₀npc : nontrivialPartCount d₀ = p ^ κ := by
      rw [← wDeg_nontrivialWeight_eq d₀ hd₀0]
      exact hd₀deg
    have hd₀filt : d₀ ∈ (Delta n).support.filter (fun d => nontrivialPartCount d ≤ p ^ κ) :=
      Finset.mem_filter.mpr ⟨hd₀memΔ, le_of_eq hd₀npc⟩
    have hdvd : Dgcd (Delta n) (p ^ κ) ∣ (coeff d₀ (Delta n)).natAbs := by
      unfold Dgcd
      exact Finset.gcd_dvd hd₀filt
    have hndvd : ¬ (p : ℤ) ∣ coeff d₀ (Delta n) := (mem_support_map_iff d₀).mp hd₀mem
    have hDgne : Dgcd (Delta n) (p ^ κ) ≠ 0 := by
      obtain ⟨d₀', hd₀'mem, hd₀'deg⟩ := hWOrder.2
      have hd₀'memΔ : d₀' ∈ (Delta n).support :=
        Finset.mem_of_subset
          (MvPolynomial.support_map_subset (Int.castRingHom (ZMod p)) (Delta n)) hd₀'mem
      have hd₀'0 : d₀' 0 = 0 := apply_zero_eq_zero_of_mem_support_Delta n d₀' hd₀'memΔ
      have hd₀'npc : nontrivialPartCount d₀' = p ^ κ := by
        rw [← wDeg_nontrivialWeight_eq d₀' hd₀'0]; exact hd₀'deg
      have hd₀'filt : d₀' ∈ (Delta n).support.filter
          (fun d => nontrivialPartCount d ≤ p ^ κ) :=
        Finset.mem_filter.mpr ⟨hd₀'memΔ, le_of_eq hd₀'npc⟩
      intro h0
      unfold Dgcd at h0
      have hdvd' : (Finset.gcd ((Delta n).support.filter
          (fun d => nontrivialPartCount d ≤ p ^ κ)) (fun d => (coeff d (Delta n)).natAbs)) ∣
          (coeff d₀' (Delta n)).natAbs := Finset.gcd_dvd hd₀'filt
      rw [h0] at hdvd'
      have : coeff d₀' (Delta n) = 0 := by
        have := Nat.eq_zero_of_zero_dvd hdvd'
        exact Int.natAbs_eq_zero.mp this
      exact (MvPolynomial.mem_support_iff.mp hd₀'memΔ) this
    by_contra hcon
    have h1le : 1 ≤ (Dgcd (Delta n) (p ^ κ)).factorization p := Nat.one_le_iff_ne_zero.mpr hcon
    have hpdvd : p ∣ Dgcd (Delta n) (p ^ κ) :=
      (Nat.Prime.dvd_iff_one_le_factorization hp hDgne).mpr h1le
    have hpdvdz : (p : ℤ) ∣ coeff d₀ (Delta n) := by
      have h1 : p ∣ (coeff d₀ (Delta n)).natAbs := hpdvd.trans hdvd
      have h2 := Int.natCast_dvd_natCast.mpr h1
      rwa [Int.dvd_natAbs] at h2
    exact hndvd hpdvdz
  · -- lower bound
    rintro s ⟨hs1, hDsne, hsfact⟩
    by_contra hlt
    push_neg at hlt
    have hall : ∀ d ∈ (Delta n).support, nontrivialPartCount d ≤ s →
        (p : ℤ) ∣ coeff d (Delta n) := by
      intro d hdmem hdcount
      by_contra hndvd
      have hd0 : d 0 = 0 := apply_zero_eq_zero_of_mem_support_Delta n d hdmem
      have hdmap : d ∈ (MvPolynomial.map (Int.castRingHom (ZMod p)) (Delta n)).support :=
        (mem_support_map_iff d).mpr hndvd
      have hge := hWOrder.1 d hdmap
      rw [wDeg_nontrivialWeight_eq d hd0] at hge
      omega
    have hpdvd : (p : ℕ) ∣ Dgcd (Delta n) s := by
      unfold Dgcd
      apply Finset.dvd_gcd
      intro d hd
      rw [Finset.mem_filter] at hd
      have h1 := hall d hd.1 hd.2
      have h2 := Int.natAbs_dvd_natAbs.mpr h1
      rwa [Int.natAbs_natCast] at h2
    have h1le : 1 ≤ (Dgcd (Delta n) s).factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hp hDsne).mp hpdvd
    omega

#print axioms mem_support_map_iff
#print axioms complete_prime_local_case_iii_depth

end CongruenceTheory
