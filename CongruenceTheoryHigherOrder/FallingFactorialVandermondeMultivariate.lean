import Mathlib
import CongruenceTheoryHigherOrder.FallingFactorialVandermonde

/-!
**The multivariate (`r`-ary) falling-factorial Vandermonde identity**, generalizing
`descFactorial_add_eq` — the manuscript's own named ingredient for (A6)'s Prüfer-enumerator
evaluation, now in full generality: for a finite index set `s` and `y : ι → ℕ`,
`(∑_{i∈s} y_i)_n = ∑_{c ∈ s.piAntidiag n} multinomial(s,c) · ∏_{i∈s} (y_i)_{c_i}`. Proved by
induction on `s`, peeling one index at a time via `Finset.piAntidiag_insert` (Mathlib's own
insert-recursion for "functions summing to `n`") and `Nat.multinomial_insert`, reducing each
inductive step to exactly the binary case already proved in `FallingFactorialVandermonde.lean`.
-/

open Finset Classical

theorem descFactorial_sum_eq {ι : Type*} [DecidableEq ι] (s : Finset ι) (y : ι → ℕ) :
    ∀ n : ℕ, (∑ i ∈ s, y i).descFactorial n =
      ∑ c ∈ s.piAntidiag n, Nat.multinomial s c * ∏ i ∈ s, (y i).descFactorial (c i) := by
  induction s using Finset.induction_on with
  | empty =>
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rw [Finset.piAntidiag_empty_of_ne_zero hn.ne']
      simp [Nat.descFactorial_eq_zero_iff_lt.mpr hn]
  | @insert i s hi ih =>
    intro n
    rw [Finset.sum_insert hi, Finset.piAntidiag_insert hi n]
    have hdisj : Set.PairwiseDisjoint (↑(Finset.antidiagonal n) : Set (ℕ × ℕ)) (fun p : ℕ × ℕ =>
        (s.piAntidiag p.2).image (fun f j => f j + if j = i then p.1 else 0)) := by
      intro p _ q _ hpq
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
      rintro h ⟨f, hf, rfl⟩ ⟨g, hg, hgeq⟩
      obtain ⟨hfsum, hfsupp⟩ := Finset.mem_piAntidiag.mp hf
      obtain ⟨hgsum, hgsupp⟩ := Finset.mem_piAntidiag.mp hg
      have hfi : f i = 0 := by by_contra hne; exact hi (hfsupp i hne)
      have hgi : g i = 0 := by by_contra hne; exact hi (hgsupp i hne)
      have heqi : f i + (if i = i then p.1 else 0) = g i + (if i = i then q.1 else 0) :=
        (congrFun hgeq i).symm
      rw [if_pos rfl, if_pos rfl, hfi, hgi] at heqi
      simp only [Nat.zero_add] at heqi
      have heqs : ∀ j ∈ s, f j = g j := by
        intro j hj
        have hne : j ≠ i := fun h' => hi (h' ▸ hj)
        have hcong := congrFun hgeq j
        rw [if_neg hne, if_neg hne] at hcong
        simpa using hcong.symm
      have hsumeq : p.2 = q.2 := by
        rw [← hfsum, ← hgsum]; exact Finset.sum_congr rfl heqs
      exact hpq (Prod.ext heqi hsumeq)
    rw [Finset.sum_biUnion hdisj]
    have hstep : ∀ p ∈ Finset.antidiagonal n,
        ∑ c ∈ (s.piAntidiag p.2).image (fun f j => f j + if j = i then p.1 else 0),
          Nat.multinomial (insert i s) c * ∏ j ∈ insert i s, (y j).descFactorial (c j) =
        n.choose p.1 * (y i).descFactorial p.1 * (∑ j ∈ s, y j).descFactorial p.2 := by
      intro p hp
      have hpn : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
      have hinj : ∀ f ∈ s.piAntidiag p.2, ∀ g ∈ s.piAntidiag p.2,
          (fun j => f j + if j = i then p.1 else 0) = (fun j => g j + if j = i then p.1 else 0) →
          f = g := by
        intro f _ g _ heq
        funext j
        have := congrFun heq j
        omega
      rw [Finset.sum_image hinj]
      have hpointwise : ∀ f ∈ s.piAntidiag p.2,
          (Nat.multinomial (insert i s) fun j' => f j' + if j' = i then p.1 else 0) *
            ∏ j ∈ insert i s, (y j).descFactorial
              ((fun j' => f j' + if j' = i then p.1 else 0) j) =
          n.choose p.1 * (y i).descFactorial p.1 *
            (Nat.multinomial s f * ∏ j ∈ s, (y j).descFactorial (f j)) := by
        intro f hf
        obtain ⟨hfsum, hfsupp⟩ := Finset.mem_piAntidiag.mp hf
        have hfi : f i = 0 := by by_contra hne; exact hi (hfsupp i hne)
        set shift : ι → ℕ := fun j' => f j' + if j' = i then p.1 else 0 with hshift_def
        have hshifti : shift i = p.1 := by simp [hshift_def, hfi]
        have hshifts : ∀ j ∈ s, shift j = f j := by
          intro j hj
          have hne : j ≠ i := fun h' => hi (h' ▸ hj)
          simp [hshift_def, hne]
        have hsumcongr : ∑ j ∈ s, shift j = ∑ j ∈ s, f j := Finset.sum_congr rfl hshifts
        have hcongr : Nat.multinomial s shift = Nat.multinomial s f :=
          Nat.multinomial_congr hshifts
        have hprod : ∏ j ∈ insert i s, (y j).descFactorial (shift j) =
            (y i).descFactorial p.1 * ∏ j ∈ s, (y j).descFactorial (f j) := by
          rw [Finset.prod_insert hi, hshifti]
          congr 1
          exact Finset.prod_congr rfl (fun j hj => by rw [hshifts j hj])
        have hmulti : Nat.multinomial (insert i s) shift = n.choose p.1 * Nat.multinomial s f := by
          rw [Nat.multinomial_insert hi shift, hshifti, hsumcongr, hfsum, hcongr, hpn]
        rw [hprod, hmulti]
        ring
      rw [Finset.sum_congr rfl hpointwise, ← Finset.mul_sum, ← ih p.2]
    rw [Finset.sum_congr rfl hstep]
    rw [descFactorial_add_eq (y i) (∑ j ∈ s, y j) n]

#print axioms descFactorial_sum_eq
