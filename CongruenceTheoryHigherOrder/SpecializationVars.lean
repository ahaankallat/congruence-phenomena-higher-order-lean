import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.Perm
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.FullCycleConnected
import CongruenceTheoryHigherOrder.CiFullCycle
import CongruenceTheoryHigherOrder.CiConverse
import CongruenceTheoryHigherOrder.FullCycleCount
import CongruenceTheoryHigherOrder.A3Final
import CongruenceTheoryHigherOrder.KWeightedHomogeneous

/-!
**The degree bound behind "`z_m` cannot occur in `L_j` when `m>j`"**
(`cor:triangular-independence`).
Builds the specialization `X_1\mapsto1`, `X_{mp}\mapsto z_m`, `X_k\mapsto0` otherwise, as a single
ring hom `specialize p : MvPolynomial ℕ ℤ →+* MvPolynomial ℕ (ZMod p)` (for prime `p`), and shows:
for any `r`, no variable `z_m` with `m>r` occurs in `specialize p (K r p)`. This is the
manuscript's own reason ("since `K_j(p)` is a sum over partitions of only `j` blocks"), now
derived cleanly from `isWeightedHomogeneous_K` (`KWeightedHomogeneous.lean`) rather than
re-examined case by case.

**Honest scope note**: this closes the vars-bound half of `cor:triangular-independence`'s
"triangular" property. The other half — the unit-coefficient computation at each `z_j` — needs
the coefficientwise-division construction of `L_j := p^{-e_p(j)}K_j(p)` and is not attempted in
this file.
-/

namespace CongruenceTheory

open MvPolynomial

/-- If `i ∈ φ.vars` and `φ` is weighted homogeneous (weight `= id`) of degree `n`, then `i ≤ n`. -/
theorem le_of_mem_vars_isWeightedHomogeneous {φ : MvPolynomial ℕ ℤ} {n : ℕ}
    (hφ : IsWeightedHomogeneous (fun k : ℕ => k) φ n) {i : ℕ} (hi : i ∈ φ.vars) : i ≤ n := by
  obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support i).mp hi
  have hcoeff : coeff d φ ≠ 0 := mem_support_iff.mp hd
  have hweight : Finsupp.weight (fun k : ℕ => k) d = n := hφ hcoeff
  rw [Finsupp.weight_apply, Finsupp.sum] at hweight
  have hdi : d i ≠ 0 := Finsupp.mem_support_iff.mp hid
  have hsingle : d i * i ≤ ∑ a ∈ d.support, d a * a :=
    Finset.single_le_sum (fun a _ => Nat.zero_le (d a * a)) hid
  have hdi1 : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr hdi
  calc i = 1 * i := (one_mul i).symm
    _ ≤ d i * i := Nat.mul_le_mul_right i hdi1
    _ ≤ ∑ a ∈ d.support, d a * a := hsingle
    _ = n := hweight

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The specialization `X_1\mapsto1`, `X_{mp}\mapsto z_m` (i.e. the target's own variable `m`),
`X_k\mapsto0` otherwise. -/
noncomputable def specSubst : ℕ → MvPolynomial ℕ (ZMod p) :=
  fun k => if k = 1 then 1 else if p ∣ k then X (k / p) else 0

/-- The full specialization ring hom, changing coefficients `ℤ\to\mathrm{ZMod}\,p` and
variables via `specSubst p` simultaneously. -/
noncomputable def specialize : MvPolynomial ℕ ℤ →+* MvPolynomial ℕ (ZMod p) :=
  (bind₁ (specSubst p)).toRingHom.comp (MvPolynomial.map (Int.castRingHom (ZMod p)))

theorem specialize_apply (φ : MvPolynomial ℕ ℤ) :
    specialize p φ = bind₁ (specSubst p) (MvPolynomial.map (Int.castRingHom (ZMod p)) φ) := rfl

theorem specSubst_vars_subset (k : ℕ) : (specSubst p k).vars ⊆ {k / p} := by
  unfold specSubst
  split_ifs with h1 h2
  · simp
  · intro i hi
    rw [vars_X] at hi
    simpa using hi
  · simp

/-- Every variable occurring in `specialize p φ` comes from a variable of `φ` via `specSubst`. -/
theorem vars_specialize_subset (φ : MvPolynomial ℕ ℤ) :
    (specialize p φ).vars ⊆ φ.vars.biUnion fun i => (specSubst p i).vars := by
  rw [specialize_apply]
  intro m hm
  obtain ⟨i, hi, hmi⟩ := mem_vars_bind₁ (specSubst p) _ hm
  exact Finset.mem_biUnion.mpr
    ⟨i, vars_map (f := Int.castRingHom (ZMod p)) (p := φ) hi, hmi⟩

/-- **The vars bound behind `cor:triangular-independence`'s triangularity.** No variable `m>r`
occurs in `specialize p (K r p)`. -/
theorem specialize_K_vars_subset (r : ℕ) : ∀ m ∈ (specialize p (K r p)).vars, m ≤ r := by
  intro m hm
  obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.mp (vars_specialize_subset p (K r p) hm)
  have hile : i ≤ r * p :=
    le_of_mem_vars_isWeightedHomogeneous (isWeightedHomogeneous_K r p) hi
  have hmeq : m = i / p := Finset.mem_singleton.mp (specSubst_vars_subset p i hmi)
  have hppos : 0 < p := (Fact.out (p := Nat.Prime p)).pos
  rw [hmeq]
  calc i / p ≤ (r * p) / p := Nat.div_le_div_right hile
    _ = r := Nat.mul_div_cancel r hppos

#print axioms specialize_K_vars_subset

end CongruenceTheory
