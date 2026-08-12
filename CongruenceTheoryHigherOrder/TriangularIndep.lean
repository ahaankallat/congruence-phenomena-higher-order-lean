import Mathlib

/-!
**`thm:complete-prime-local`(iii)'s `(A11)`: triangular nullspace / linear independence.**
A general fact: if `v_s` (for `s` ranging over `[a,b]`) satisfies `v_s(t)=0` for `t>s` (in
range) and `v_s(s)\ne0` (a "lower-triangular, nonzero-diagonal" family), then the only linear
relation `\sum_s x_s v_s = 0` (checked at every `t\in[a,b]`) is the trivial one. This is the
manuscript's reason `\log F_2,\ldots,\log F_{p-1}` (and, degree-one-wise, `F_2,\ldots,F_{p-1}`
themselves) are linearly independent.
-/

namespace CongruenceTheory

variable {p : ℕ}

theorem triangular_indep (hp : p.Prime) (a b : ℕ) (v : ℕ → ℕ → ZMod p)
    (hzero : ∀ s t, a ≤ s → s ≤ b → a ≤ t → t ≤ b → s < t → v s t = 0)
    (hdiag : ∀ s, a ≤ s → s ≤ b → v s s ≠ 0)
    (x : ℕ → ZMod p)
    (hsum : ∀ t, a ≤ t → t ≤ b → ∑ s ∈ Finset.Icc a b, x s * v s t = 0) :
    ∀ s, a ≤ s → s ≤ b → x s = 0 := by
  haveI := Fact.mk hp
  by_contra hcon
  push_neg at hcon
  obtain ⟨s0, hs0a, hs0b, hs0ne⟩ := hcon
  set S := (Finset.Icc a b).filter (fun s => x s ≠ 0) with hSdef
  have hSne : S.Nonempty := ⟨s0, by
    simp only [hSdef, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hs0a, hs0b⟩, hs0ne⟩⟩
  obtain ⟨smax, hsmaxS, hsmaxmax⟩ := S.exists_max_image id hSne
  have hsmaxa : a ≤ smax := (Finset.mem_Icc.mp (Finset.mem_of_mem_filter smax hsmaxS)).1
  have hsmaxb : smax ≤ b := (Finset.mem_Icc.mp (Finset.mem_of_mem_filter smax hsmaxS)).2
  have hsmaxne : x smax ≠ 0 := (Finset.mem_filter.mp hsmaxS).2
  have heq := hsum smax hsmaxa hsmaxb
  have hterm : ∀ s ∈ Finset.Icc a b, s ≠ smax → x s * v s smax = 0 := by
    intro s hs hsne
    have hsa : a ≤ s := (Finset.mem_Icc.mp hs).1
    have hsb : s ≤ b := (Finset.mem_Icc.mp hs).2
    rcases lt_or_gt_of_ne hsne with hlt | hgt
    · rw [hzero s smax hsa hsb hsmaxa hsmaxb hlt, mul_zero]
    · by_cases hxs : x s = 0
      · rw [hxs, zero_mul]
      · exfalso
        have hsS : s ∈ S := by
          simp only [hSdef, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hsa, hsb⟩, hxs⟩
        have := hsmaxmax s hsS
        simp only [id] at this
        omega
  rw [Finset.sum_eq_single smax hterm (fun h => absurd (Finset.mem_Icc.mpr ⟨hsmaxa, hsmaxb⟩) h)]
    at heq
  exact (mul_ne_zero hsmaxne (hdiag smax hsmaxa hsmaxb)) heq

#print axioms triangular_indep

end CongruenceTheory
