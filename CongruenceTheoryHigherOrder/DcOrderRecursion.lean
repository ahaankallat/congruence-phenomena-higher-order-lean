import Mathlib
import CongruenceTheoryHigherOrder.DcDef
import CongruenceTheoryHigherOrder.DcOrderOne
import CongruenceTheoryHigherOrder.DcFrobenius
import CongruenceTheoryHigherOrder.DcPowOrder
import CongruenceTheoryHigherOrder.DigitDecomposition
import CongruenceTheoryHigherOrder.DcOrderStep
import CongruenceTheoryHigherOrder.DcResidualStep

/-!
**`thm:complete-prime-local`(iii)'s `(A11)`/`(A12)`, fully assembled:
`\operatorname{ord}_J(D_{\mathbf c})=p^\kappa`.** Combines `DcOrderStep.lean`'s single general
step (peeling off the initial
`F_r` factor) with `DcResidualStep.lean`'s residual (`r=1`) steps, iterated by strong induction
on the total multiplicity `h+\sum_{s=2}^{p-1}c_s` (which strictly decreases at each successful
division, exactly as the manuscript's own termination argument: "a valid division strictly
decreases the total multiplicity"), terminating in `\operatorname{ord}=1` the moment (A8)
first fails. The only side condition needed is `D_{\mathbf c}\ne0`, which is preserved down the
recursion (each factor of a nonzero product is itself nonzero) and rules out exactly the
degenerate all-zero vector, where `D_{\mathbf c}` is identically the zero polynomial.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`D_{1,h,\mathbf c}` does not depend on `c_1`**: since `F_1=1` identically, only `c_s` for
`2\le s\le p-1` affects the polynomial's value. -/
theorem Dc_r1_congr (p h : ℕ) (hp : p.Prime) (c1 c2 : ℕ → ℕ)
    (hagree : ∀ s ∈ Finset.Icc 2 (p - 1), c1 s = c2 s) :
    Dc p 1 h c1 = Dc p 1 h c2 := by
  unfold Dc
  congr 1
  have hicceq : Finset.Icc 1 (p - 1) = insert 1 (Finset.Icc 2 (p - 1)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    have := hp.two_le
    omega
  rw [hicceq, Finset.prod_insert (by simp only [Finset.mem_Icc]; omega),
    Finset.prod_insert (by simp only [Finset.mem_Icc]; omega), FmZ_one, one_pow, one_pow,
    one_mul, one_mul]
  exact Finset.prod_congr rfl (fun s hs => by rw [hagree s hs])

/-- **The residual (`r=1`) order recursion, in full**: for `D_{1,h,\mathbf c}\ne0`, the order
`\operatorname{ord}_J(D_{1,h,\mathbf c})=p^\kappa` exists, obtained by iterating
`MinDeg_Dc_step_r1` for as long as the residual digit conditions hold, terminating via
`MinDeg_one_Dc_of_not_digit_conditions_r1` the moment they first fail. Proved by strong
induction on the total multiplicity `h+\sum_{s=2}^{p-1}c_s`. -/
theorem exists_MinDeg_Dc_r1 (p : ℕ) (hp : p.Prime) :
    ∀ M h : ℕ, ∀ c : ℕ → ℕ, h + ∑ s ∈ Finset.Icc 2 (p - 1), c s = M → Dc p 1 h c ≠ 0 →
      ∃ κ : ℕ, MinDeg (Dc p 1 h c) (p ^ κ) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M IH =>
    intro h c hM hDcne
    by_cases hdig : (∀ s, 2 ≤ s → s ≤ p - 1 → (c s : ZMod p) = 0) ∧ (h : ZMod p) = 0
    · obtain ⟨h', hh'⟩ := exists_decomp_of_dvd hdig.2
      have hcex : ∀ s ∈ Finset.Icc 2 (p - 1), ∃ c'0 : ℕ, c s = p * c'0 := by
        intro s hs
        have hsmem : s ∈ Finset.Icc 2 (p - 1) := hs
        simp only [Finset.mem_Icc] at hsmem
        have hcs : (c s : ZMod p) = 0 := hdig.1 s hsmem.1 hsmem.2
        obtain ⟨c'0, hc'0⟩ := exists_decomp_of_modEq (ε := 0) hp.pos (by simpa using hcs)
        exact ⟨c'0, by simpa using hc'0⟩
      choose c'fun hc'fun using hcex
      set c' : ℕ → ℕ := fun s => if hs : s ∈ Finset.Icc 2 (p - 1) then c'fun s hs else 0
        with hc'def
      have hc'spec : ∀ s ∈ Finset.Icc 2 (p - 1), c s = p * c' s := by
        intro s hs
        simp only [hc'def, dif_pos hs]
        exact hc'fun s hs
      have hMeq : M = p * (h' + ∑ s ∈ Finset.Icc 2 (p - 1), c' s) := by
        have hsumeq : ∑ s ∈ Finset.Icc 2 (p - 1), c s =
            p * ∑ s ∈ Finset.Icc 2 (p - 1), c' s := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl hc'spec
        rw [← hM, hh', hsumeq]
        ring
      have hp0 : p ≠ 0 := hp.pos.ne'
      have hMpos : 0 < M := by
        rcases Nat.eq_zero_or_pos M with hM0 | hMpos
        · exfalso
          have hzero : p * (h' + ∑ s ∈ Finset.Icc 2 (p - 1), c' s) = 0 := by
            rw [← hMeq]; exact hM0
          have hsum0 : h' + ∑ s ∈ Finset.Icc 2 (p - 1), c' s = 0 :=
            (Nat.mul_eq_zero.mp hzero).resolve_left hp0
          have hh0 : h = 0 := by rw [hh']; omega
          have hc0 : ∀ s ∈ Finset.Icc 2 (p - 1), c s = 0 := by
            intro s hs
            have hc's0 : c' s = 0 := by
              have hle : c' s ≤ ∑ s' ∈ Finset.Icc 2 (p - 1), c' s' :=
                Finset.single_le_sum (fun s' _ => Nat.zero_le (c' s')) hs
              omega
            rw [hc'spec s hs, hc's0, mul_zero]
          apply hDcne
          rw [Dc_r1_congr p h hp c (fun _ => 0) (fun s hs => hc0 s hs), hh0]
          unfold Dc
          simp [FmZ_one]
        · exact hMpos
      have hM'lt : h' + ∑ s ∈ Finset.Icc 2 (p - 1), c' s < M := by
        have hp2 : 2 ≤ p := hp.two_le
        nlinarith [hMeq, hMpos]
      have hDc'ne : Dc p 1 h' c' ≠ 0 := by
        intro hcon
        apply hDcne
        have hfrob := Dc_frobenius_factorization_r1 p h h' hp c c' hh' hc'spec
        rw [hfrob, hcon]
        exact zero_pow hp.pos.ne'
      obtain ⟨κ', hκ'⟩ := IH _ hM'lt h' c' rfl hDc'ne
      refine ⟨κ' + 1, ?_⟩
      have hpow : p ^ (κ' + 1) = p * p ^ κ' := by ring
      rw [hpow]
      exact MinDeg_Dc_step_r1 p h hp c hdig
        (fun h'' hh'' c'' hc''s => by
          have hh''eq : h'' = h' := by
            have hp0 : p ≠ 0 := hp.pos.ne'
            have : p * h'' = p * h' := by rw [← hh'', ← hh']
            exact Nat.eq_of_mul_eq_mul_left hp.pos this
          have hDceq : Dc p 1 h'' c'' = Dc p 1 h' c' := by
            rw [hh''eq]
            apply Dc_r1_congr p h' hp c'' c'
            intro s hs
            have hp0 : p ≠ 0 := hp.pos.ne'
            have : p * c'' s = p * c' s := by rw [← hc''s s hs, ← hc'spec s hs]
            exact Nat.eq_of_mul_eq_mul_left hp.pos this
          rw [hDceq]
          exact hκ')
    · exact ⟨0, by simpa using MinDeg_one_Dc_of_not_digit_conditions_r1 p h hp c hdig⟩

/-- **The full order recursion (A11)/(A12): `\operatorname{ord}_J(D_{\mathbf c})=p^\kappa`
exists**, for any nonzero `D_{\mathbf c}` (`2\le r\le p-1`). Combines one general step
(`MinDeg_Dc_step_of_digit_conditions`) with the residual recursion
(`exists_MinDeg_Dc_r1`). -/
theorem exists_MinDeg_Dc (p r h : ℕ) (hp : p.Prime) (c : ℕ → ℕ)
    (hr2 : 2 ≤ r) (hrp : r ≤ p - 1) (hDcne : Dc p r h c ≠ 0) :
    ∃ κ : ℕ, MinDeg (Dc p r h c) (p ^ κ) := by
  haveI := Fact.mk hp
  by_cases hdig : (∀ s, 2 ≤ s → s ≤ p - 1 → (c s : ZMod p) = if s = r then 1 else 0) ∧
      (h : ZMod p) = 0
  · obtain ⟨h', hh'⟩ := exists_decomp_of_dvd hdig.2
    have hcex : ∀ s ∈ Finset.Icc 2 (p - 1),
        ∃ c'0 : ℕ, c s = p * c'0 + (if s = r then 1 else 0) := by
      intro s hs
      have hsmem : s ∈ Finset.Icc 2 (p - 1) := hs
      simp only [Finset.mem_Icc] at hsmem
      by_cases hsr : s = r
      · subst hsr
        have hcs : (c s : ZMod p) = 1 := by rw [hdig.1 s hsmem.1 hsmem.2]; simp
        obtain ⟨c'0, hc'0⟩ := exists_decomp_of_modEq (ε := 1) hp.one_lt (by simpa using hcs)
        exact ⟨c'0, by simpa using hc'0⟩
      · have hcs : (c s : ZMod p) = 0 := by rw [hdig.1 s hsmem.1 hsmem.2]; simp [hsr]
        obtain ⟨c'0, hc'0⟩ := exists_decomp_of_modEq (ε := 0) hp.pos (by simpa using hcs)
        refine ⟨c'0, ?_⟩
        simpa [hsr] using hc'0
    choose c'fun hc'fun using hcex
    set c' : ℕ → ℕ := fun s => if hs : s ∈ Finset.Icc 2 (p - 1) then c'fun s hs else 0
      with hc'def
    have hc'spec : ∀ s ∈ Finset.Icc 2 (p - 1), c s = p * c' s + (if s = r then 1 else 0) := by
      intro s hs
      simp only [hc'def, dif_pos hs]
      exact hc'fun s hs
    have hfrob := Dc_frobenius_factorization p r h h' hp c c' hr2 hrp hh' hc'spec
    have hDc'ne : Dc p 1 h' c' ≠ 0 := by
      intro hcon
      apply hDcne
      rw [hfrob, hcon]
      rw [zero_pow hp.pos.ne', mul_zero]
    obtain ⟨κ', hκ'⟩ := exists_MinDeg_Dc_r1 p hp _ h' c' rfl hDc'ne
    refine ⟨κ' + 1, ?_⟩
    have hpow : p ^ (κ' + 1) = p * p ^ κ' := by ring
    rw [hpow, hfrob]
    exact MinDeg_unit_mul hp (FmZ_coeff_zero_ne_zero p r hp) (MinDeg_pow_p hp hκ')
  · exact ⟨0, by simpa using MinDeg_one_Dc_of_not_digit_conditions p r h hp c hr2 hrp hdig⟩

#print axioms Dc_r1_congr
#print axioms exists_MinDeg_Dc_r1
#print axioms exists_MinDeg_Dc

end CongruenceTheory
