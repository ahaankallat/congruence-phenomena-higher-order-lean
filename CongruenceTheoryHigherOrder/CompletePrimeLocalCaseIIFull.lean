import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.CompletePrimeLocalCaseIIValuationBLeE
import CongruenceTheoryHigherOrder.CompletePrimeLocalCaseIIDepthBLeE
import CongruenceTheoryHigherOrder.CompletePrimeLocalCaseIIDepthELtB

/-!
**`thm:complete-prime-local`, case (ii), fully assembled.** For `U_p(\mathbf n)=\{1\}$, writing
`\mathbf n=(a,\mathbf m)$ with `p\nmid a`, `p\mid m_i`, `B=\sum_im_i`, `b:=v_p(B)`,
`E:=v_p(\operatorname{cont}\Delta_{\mathbf m})`, `d:=\delta_p(\mathbf m)`: both the content
valuation `v_p(\operatorname{cont}\Delta_{a,\mathbf m})=\min\{b,E\}` and the witness depth
`\delta_p(a,\mathbf m)=1$ (if `b\le E`) or `d` (if `E<b`) hold *unconditionally*, assembled from
the two valuation branches (`complete_prime_local_case_ii_valuation_b_le_E`,
`complete_prime_local_case_ii_valuation_b_lt_E`) and the two depth branches
(`complete_prime_local_case_ii_depth_b_le_E`, `complete_prime_local_case_ii_depth_E_lt_b`) via a
single case split on `b` vs `E`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`thm:complete-prime-local`(ii), fully assembled.** For `p\nmid a`, `\mathbf m=(pu_1,\ldots,
pu_t)`, `E:=v_p(\operatorname{cont}\Delta_{\mathbf m})\ge1` (always true for an achieved shape),
with `d` the least witness depth of `\mathbf m` itself: writing `b:=v_p(B)`,
`v_p(\operatorname{cont}\Delta_{a,\mathbf m})=\min\{b,E\}`, and `\delta_p(a,\mathbf m)=1` if
`b\le E`, `d` if `E<b`. -/
theorem complete_prime_local_case_ii {t : ℕ} {a : ℕ} (u : Fin t → ℕ) (hu : ∀ i, 0 < u i)
    {p : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (ha1 : 1 ≤ a)
    {E : ℕ} (hE1 : 1 ≤ E) (hE : (cont (Delta (fun i => p * u i))).factorization p = E)
    (hmne : Delta (fun i => p * u i) ≠ 0)
    {d : ℕ} (hleast : IsLeast
      {s : ℕ | 1 ≤ s ∧ (Dgcd (Delta (fun i => p * u i)) s).factorization p = E} d) :
    (cont (Delta (Fin.cons a (fun i => p * u i) : Fin (t + 1) → ℕ))).factorization p =
        min (padicValNat p (∑ i, p * u i)) E ∧
      IsLeast {s : ℕ | 1 ≤ s ∧
          (Dgcd (Delta (Fin.cons a (fun i => p * u i) : Fin (t + 1) → ℕ)) s).factorization p =
            min (padicValNat p (∑ i, p * u i)) E}
        (if padicValNat p (∑ i, p * u i) ≤ E then 1 else d) := by
  by_cases hb : padicValNat p (∑ i, p * u i) ≤ E
  · rw [min_eq_left hb, if_pos hb]
    exact ⟨complete_prime_local_case_ii_valuation_b_le_E u hu hp hpa ha1 hE hmne hb,
      complete_prime_local_case_ii_depth_b_le_E u hu hp hpa ha1 hE hmne hb⟩
  · push_neg at hb
    rw [min_eq_right hb.le, if_neg (not_le.mpr hb)]
    have ht2 := two_le_of_Delta_ne_zero (fun i => p * u i) hmne
    have hB1 : 1 ≤ ∑ i, p * u i := by
      obtain ⟨i0⟩ : Nonempty (Fin t) := ⟨⟨0, by omega⟩⟩
      have hpos : 0 < p * u i0 := Nat.mul_pos hp.pos (hu i0)
      calc 1 ≤ p * u i0 := hpos
        _ ≤ ∑ i, p * u i :=
          Finset.single_le_sum (f := fun i => p * u i) (fun i _ => Nat.zero_le _)
            (Finset.mem_univ i0)
    exact ⟨complete_prime_local_case_ii_valuation_E_lt_b (fun i => p * u i) hp hpa ha1 hB1 hE
        hmne hb,
      complete_prime_local_case_ii_depth_E_lt_b u hu hp hpa ha1 hE1 hE hmne hleast hb⟩

#print axioms complete_prime_local_case_ii

end CongruenceTheory
