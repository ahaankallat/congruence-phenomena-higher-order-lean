import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.GeneralizedConnectivity
import CongruenceTheoryHigherOrder.PartitionShape
import CongruenceTheoryHigherOrder.MicroblockPartition
import CongruenceTheoryHigherOrder.MomentCumulantExpansion
import CongruenceTheoryHigherOrder.FirstPrimeLayer
import CongruenceTheoryHigherOrder.ProductValuation

/-!
**The lower-bound half of `thm:common-prime-classification`'s valuation formula.** Combines
(A7) (`defect_eq_sum_prod_K`) with the per-shape `p`-power divisibility
(`dvd_coeff_prod_K_of_multiset`) to show every coefficient of `\Delta_{p\mathbf u}` is divisible by
`p^E`, where `E` is the minimum, over partitions not refining the macroblock structure, of the
weighted sum `\sum_j e_p(j)` of the partition's own shape.
-/

namespace CongruenceTheory

open MvPolynomial
open scoped Classical

variable {r : ℕ} (u : Fin r → ℕ)

/-- `W_p(\pi)`, the weight of a partition's shape: `\sum_{j\in\mathrm{shape}(\pi)}e_p(j)`
(with multiplicity), matching the manuscript's `\sum_{j\ge2}m_je_p(j)` (the `j=1`/`m_1` term
contributes `0`, since `e_p(1)=0`). -/
noncomputable def shapeWeight (p : ℕ) (π : GenPartLat (MicroIdx u)) : ℕ :=
  ((GenPartLatShape π).map (firstPrimeLayerExponent p)).sum

/-- **Every coefficient of the block-product `\prod_{B\in\pi.parts}K(|B|,p)` is divisible by
`p^{W_p(\pi)}`.** -/
theorem dvd_coeff_prod_K_parts {p : ℕ} (hp : p.Prime) (π : GenPartLat (MicroIdx u)) :
    ∀ d, (p : ℤ) ^ (shapeWeight u p π) ∣ coeff d (∏ B ∈ π.parts, K B.card p) := by
  intro d
  rw [prod_K_eq_shape_prod]
  have hshape1 : ∀ j ∈ GenPartLatShape π, 1 ≤ j := by
    intro j hj
    obtain ⟨B, hB, hBj⟩ := Multiset.mem_map.mp hj
    have hBmem : B ∈ π.parts := hB
    have := Finset.card_pos.mpr (π.nonempty_of_mem_parts hBmem)
    omega
  apply dvd_coeff_prod_K_of_multiset hp (GenPartLatShape π) hshape1
  intro j hj
  have h1 := hshape1 j hj
  have h2 : 2 ≤ p := hp.two_le
  nlinarith

/-- **The lower-bound half of `thm:common-prime-classification`'s valuation formula.** For any
`E` bounding every relevant partition's shape weight from below, `p^E` divides every coefficient
of the defect. -/
theorem dvd_coeff_defect {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ) (hu : ∀ i, 0 < u i) {p : ℕ}
    (hp : p.Prime) (E : ℕ)
    (hE : ∀ π ∈ (Finset.univ : Finset (GenPartLat (MicroIdx u))).filter
        (fun π => ¬ π ≤ macroPartition u), E ≤ shapeWeight u p π) :
    ∀ d, (p : ℤ) ^ E ∣ coeff d (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) := by
  intro d
  rw [defect_eq_sum_prod_K hr u hu p, coeff_sum]
  apply Finset.dvd_sum
  intro π hπ
  exact dvd_trans (pow_dvd_pow (p : ℤ) (hE π hπ)) (dvd_coeff_prod_K_parts u hp π d)

#print axioms dvd_coeff_defect

end CongruenceTheory
