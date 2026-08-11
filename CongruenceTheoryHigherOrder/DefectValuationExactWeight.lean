import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.GeneralizedConnectivity
import CongruenceTheoryHigherOrder.PartitionShape
import CongruenceTheoryHigherOrder.MicroblockPartition
import CongruenceTheoryHigherOrder.MomentCumulantExpansion
import CongruenceTheoryHigherOrder.FirstPrimeLayer
import CongruenceTheoryHigherOrder.ProductValuation
import CongruenceTheoryHigherOrder.DefectValuationLowerBound

/-!
**The manuscript's own weight `W_p(\lambda;\mathbf u)=v_p(A_\lambda(\mathbf u))+\sum_{j\ge2}
m_je_p(j)`**, and the correspondingly strengthened lower bound on `v_p(\operatorname{cont}
\Delta_{p\mathbf u})`. `DefectValuationLowerBound.lean`'s `dvd_coeff_defect` only uses each
individual partition's own `shapeWeight`; grouping partitions of the same shape `\lambda` together
(`sum_prod_K_eq_sum_shapeCount`) reveals the *sum* of the `A_\lambda(\mathbf u)`-many identical
block-products is divisible by the *extra* `p^{v_p(A_\lambda(\mathbf u))}` as well, matching the
manuscript's tighter bound exactly.
-/

namespace CongruenceTheory

open MvPolynomial
open scoped Classical

variable {r : ℕ} (u : Fin r → ℕ)

/-- The Finset of partitions of the microblocks that do **not** refine the macroblock partition —
the domain (A7) sums over. -/
noncomputable def nonRefiningPartitions : Finset (GenPartLat (MicroIdx u)) :=
  (Finset.univ : Finset (GenPartLat (MicroIdx u))).filter (fun π => ¬ π ≤ macroPartition u)

/-- `A_\lambda(\mathbf u)`: the number of non-refining partitions of shape `\lambda`. -/
noncomputable def Alam (u : Fin r → ℕ) (lam : Multiset ℕ) : ℕ :=
  shapeCount (nonRefiningPartitions u) lam

/-- `W_p(\lambda;\mathbf u) = v_p(A_\lambda(\mathbf u)) + \sum_{j\in\lambda}e_p(j)` (the `j=1`
terms contribute `0`, matching the manuscript's `\sum_{j\ge2}`). -/
noncomputable def Wp (u : Fin r → ℕ) (p : ℕ) (lam : Multiset ℕ) : ℕ :=
  (Alam u lam).factorization p + (lam.map (firstPrimeLayerExponent p)).sum

/-- **(A7), regrouped by shape.** -/
theorem defect_eq_sum_Alam_smul {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ) (hu : ∀ i, 0 < u i)
    (p : ℕ) :
    C ((∑ i, u i) * p) - ∏ i, C (u i * p) =
      ∑ lam ∈ (nonRefiningPartitions u).image GenPartLatShape,
        (Alam u lam) • ((lam.map (fun j => K j p)).prod) := by
  rw [defect_eq_sum_prod_K hr u hu p]
  exact sum_prod_K_eq_sum_shapeCount (nonRefiningPartitions u) p

/-- **Every coefficient of the shape-`\lambda` term `A_\lambda(\mathbf u)\bullet\prod K` is
divisible by `p^{W_p(\lambda;\mathbf u)}`.** -/
theorem dvd_coeff_Alam_smul {p : ℕ} (hp : p.Prime) (lam : Multiset ℕ) (hlam : ∀ j ∈ lam, 1 ≤ j)
    (hn2 : ∀ j ∈ lam, 2 ≤ j * p) :
    ∀ d, (p : ℤ) ^ (Wp u p lam) ∣ coeff d ((Alam u lam) • ((lam.map (fun j => K j p)).prod)) := by
  intro d
  rw [coeff_smul, nsmul_eq_mul, Wp, pow_add]
  apply mul_dvd_mul
  · exact_mod_cast Nat.ordProj_dvd (Alam u lam) p
  · exact dvd_coeff_prod_K_of_multiset hp lam hlam hn2 d

/-- **The strengthened lower-bound half of `thm:common-prime-classification`'s valuation
formula**, matching the manuscript's own `W_p` exactly (incorporating `v_p(A_\lambda(\mathbf
u))`, not merely the per-partition `shapeWeight`). -/
theorem dvd_coeff_defect_Wp {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ) (hu : ∀ i, 0 < u i) {p : ℕ}
    (hp : p.Prime) (E : ℕ)
    (hE : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape, E ≤ Wp u p lam) :
    ∀ d, (p : ℤ) ^ E ∣ coeff d (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) := by
  intro d
  rw [defect_eq_sum_Alam_smul hr u hu p, coeff_sum]
  apply Finset.dvd_sum
  intro lam hlam
  have hshape1 : ∀ j ∈ lam, 1 ≤ j := by
    intro j hj
    obtain ⟨π, -, hπ⟩ := Finset.mem_image.mp hlam
    rw [← hπ] at hj
    obtain ⟨B, hB, hBj⟩ := Multiset.mem_map.mp hj
    have hBmem : B ∈ π.parts := hB
    have := Finset.card_pos.mpr (π.nonempty_of_mem_parts hBmem)
    omega
  have hn2 : ∀ j ∈ lam, 2 ≤ j * p := by
    intro j hj
    have h1 := hshape1 j hj
    have h2 : 2 ≤ p := hp.two_le
    nlinarith
  exact dvd_trans (pow_dvd_pow (p : ℤ) (hE lam hlam)) (dvd_coeff_Alam_smul u hp lam hshape1 hn2 d)

#print axioms defect_eq_sum_Alam_smul
#print axioms dvd_coeff_defect_Wp

end CongruenceTheory
