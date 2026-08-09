import Mathlib
import CongruenceTheory.StrongWeighted
import CongruenceTheoryHigherOrder.PrimeWitness
import CongruenceTheory.OrbitSum

/-!
**Proposition `prop:prime`**: for every prime `p`, `A_w(p) ≡ w_1^p + (p-1)!·w_p ≡ w_1 - w_p
(mod p)`. The manuscript's own proof: every conjugacy class in `S_p` other than `{1}` and
the `p`-cycles has size divisible by `p`; Fermat and Wilson close the rest. This is a
*different* orbit argument from `thm:strong`'s (full-group conjugation, not the `H`-subgroup
case), so it uses Mathlib's own `Equiv.Perm.card_isConj_mul_eq` directly rather than the
custom `Conj.lean`/`Centralizer.lean` machinery.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm Nat MvPolynomial

/-- `p` does not divide `n!` when `n < p`. -/
theorem not_dvd_factorial_of_lt (p n : ℕ) (hp : p.Prime) (h : n < p) : ¬ p ∣ n ! := by
  induction n with
  | zero => simp [hp.one_lt.ne']
  | succ n ih =>
    rw [Nat.factorial_succ]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h2
    · have := Nat.le_of_dvd (by omega) h1; omega
    · exact ih (by omega) h2

theorem replicate_count_le (m : Multiset ℕ) (n : ℕ) : Multiset.replicate (m.count n) n ≤ m := by
  rw [Multiset.le_iff_count]
  intro a
  rw [Multiset.count_replicate]
  by_cases h : a = n
  · subst h; simp
  · rw [if_neg (Ne.symm h)]; exact Nat.zero_le _

theorem multiset_sum_le_of_le (m1 m2 : Multiset ℕ) (h : m1 ≤ m2) : m1.sum ≤ m2.sum := by
  obtain ⟨c, rfl⟩ := Multiset.le_iff_exists_add.mp h
  simp [Multiset.sum_add]

/-- **The centralizer-size formula `z_λ` is `p`-free** for every conjugacy class other than
the identity and the `p`-cycles: the manuscript's key structural fact behind `prop:prime`. -/
theorem not_dvd_centralizer_size (p : ℕ) (hp : p.Prime) (g : Equiv.Perm (Fin p)) (hg1 : g ≠ 1)
    (hgp : g.cycleType ≠ {p}) :
    ¬ p ∣ ((p - g.cycleType.sum)! * g.cycleType.prod *
      (∏ n ∈ g.cycleType.toFinset, (g.cycleType.count n)!)) := by
  have hppos : 0 < p := hp.pos
  have hne : g.cycleType ≠ 0 := fun h0 => hg1 (Equiv.Perm.cycleType_eq_zero.mp h0)
  have hsum_le : g.cycleType.sum ≤ p := by
    have := Equiv.Perm.sum_cycleType_le g; simpa using this
  have hallt : ∀ x ∈ g.cycleType, 2 ≤ x ∧ x < p := by
    intro x hx
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hx
    have hxle : x ≤ g.cycleType.sum := Multiset.single_le_sum (fun y _ => Nat.zero_le y) x hx
    refine ⟨h2, ?_⟩
    by_contra hge
    push Not at hge
    have hxp : x = p := le_antisymm (hxle.trans hsum_le) hge
    apply hgp
    have hcons : g.cycleType = x ::ₘ g.cycleType.erase x := (Multiset.cons_erase hx).symm
    have herasesum : (g.cycleType.erase x).sum = 0 := by
      have hsum_eq : g.cycleType.sum = x + (g.cycleType.erase x).sum := by
        conv_lhs => rw [hcons]
        rw [Multiset.sum_cons]
      omega
    have herase0 : g.cycleType.erase x = 0 := by
      by_contra hne0
      obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hne0
      have := Multiset.single_le_sum (fun z _ => Nat.zero_le z) y hy
      have hy2 : 2 ≤ y := Equiv.Perm.two_le_of_mem_cycleType (Multiset.mem_of_mem_erase hy)
      omega
    rw [hcons, herase0, hxp]
    rfl
  obtain ⟨x0, hx0⟩ := Multiset.exists_mem_of_ne_zero hne
  have hS2 : 2 ≤ g.cycleType.sum :=
    le_trans (hallt x0 hx0).1 (Multiset.single_le_sum (fun y _ => Nat.zero_le y) x0 hx0)
  have hlt1 : p - g.cycleType.sum < p := by omega
  have h1 : ¬ p ∣ (p - g.cycleType.sum)! := not_dvd_factorial_of_lt p (p - g.cycleType.sum) hp hlt1
  have h2 : ¬ p ∣ g.cycleType.prod := by
    intro hdvd
    obtain ⟨x, hx, hxdvd⟩ := (Nat.Prime.prime hp).exists_mem_multiset_dvd hdvd
    have hx2 := (hallt x hx).1
    have hxp := (hallt x hx).2
    have hxle := Nat.le_of_dvd (by omega : 0 < x) hxdvd
    omega
  have h3 : ¬ p ∣ ∏ n ∈ g.cycleType.toFinset, (g.cycleType.count n)! := by
    intro hdvd
    obtain ⟨n, hnmem, hndvd⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd hdvd
    have hn2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType (Multiset.mem_toFinset.mp hnmem)
    have hcnt_le : g.cycleType.count n * n ≤ g.cycleType.sum := by
      have hle := replicate_count_le g.cycleType n
      have hsm := multiset_sum_le_of_le _ _ hle
      rwa [Multiset.sum_replicate, smul_eq_mul] at hsm
    have hcnt_lt : g.cycleType.count n < p := by nlinarith
    exact not_dvd_factorial_of_lt p (g.cycleType.count n) hp hcnt_lt hndvd
  intro hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with hdvd12 | hdvd3
  · rcases (Nat.Prime.dvd_mul hp).mp hdvd12 with hd1 | hd2
    · exact h1 hd1
    · exact h2 hd2
  · exact h3 hdvd3

/-- Every conjugacy class other than the identity's and the `p`-cycles' has size divisible
by `p`, via Mathlib's own `Equiv.Perm.card_isConj_mul_eq`. -/
theorem prime_dvd_isConj_card (p : ℕ) (hp : p.Prime) (g : Equiv.Perm (Fin p)) (hg1 : g ≠ 1)
    (hgp : g.cycleType ≠ {p}) :
    p ∣ Nat.card {h : Equiv.Perm (Fin p) | IsConj g h} := by
  have heq := Equiv.Perm.card_isConj_mul_eq g
  have hz := not_dvd_centralizer_size p hp g hg1 hgp
  have hpdvd : p ∣ Nat.card {h : Equiv.Perm (Fin p) | IsConj g h} *
      ((Fintype.card (Fin p) - g.cycleType.sum)! * g.cycleType.prod *
        (∏ n ∈ g.cycleType.toFinset, (g.cycleType.count n)!)) := by
    rw [heq, Fintype.card_fin]
    exact Nat.dvd_factorial hp.pos (le_refl p)
  rw [Fintype.card_fin] at hpdvd
  rcases (Nat.Prime.dvd_mul hp).mp hpdvd with h1 | h2
  · exact h1
  · exact absurd h2 hz

open scoped Classical in
/-- **The exceptional-class decomposition of `Cperm p`**: `Cperm p = X_1^p + (p-1)!·X_p +
p·Q` for some `Q`, for every prime `p`. -/
theorem Cperm_prime_decomp (p : ℕ) (hp : p.Prime) :
    ∃ Q : MvPolynomial ℕ ℤ,
      Cperm p = (MvPolynomial.X 1 : MvPolynomial ℕ ℤ) ^ p +
        ((p - 1)! : MvPolynomial ℕ ℤ) * MvPolynomial.X p + (p : MvPolynomial ℕ ℤ) * Q := by
  set s := Finset.univ.filter (fun g : Equiv.Perm (Fin p) => g ≠ 1 ∧ g.cycleType ≠ {p}) with hs
  have key : ∀ x ∈ s, (p : ℤ) ∣ ((s.filter (IsConj x)).card : ℤ) := by
    intro x hx
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hclass_eq : s.filter (IsConj x) = Finset.univ.filter (IsConj x) := by
      ext y
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro hy
        refine ⟨?_, hy⟩
        obtain ⟨c, hc⟩ := isConj_iff.mp hy
        constructor
        · intro hy1
          apply hx.1
          have hxeq : x = c⁻¹ * y * c := by rw [← hc]; group
          rw [hy1] at hxeq
          simpa using hxeq
        · intro hycyc
          apply hx.2
          have hcyc_eq : y.cycleType = x.cycleType := by rw [← hc, Equiv.Perm.cycleType_conj]
          rw [hcyc_eq] at hycyc
          exact hycyc
    rw [hclass_eq]
    have hcardeq : Nat.card {h : Equiv.Perm (Fin p) | IsConj x h} =
        (Finset.univ.filter (IsConj x)).card := by
      rw [Nat.card_eq_card_toFinset]
      congr 1
      ext y
      simp
    have hpf := prime_dvd_isConj_card p hp x hx.1 hx.2
    rw [hcardeq] at hpf
    exact_mod_cast hpf
  obtain ⟨Q, hQ⟩ := dvd_sum_of_const_on_classes IsConj
    (fun x => IsConj.refl x) (fun x y h => h.symm) (fun x y z h1 h2 => h1.trans h2)
    ci (fun x y hxy => by obtain ⟨c, hc⟩ := isConj_iff.mp hxy; rw [← hc, ci_conj])
    p s key
  refine ⟨Q, ?_⟩
  have hsplit : (Cperm p : MvPolynomial ℕ ℤ) =
      ci (1 : Equiv.Perm (Fin p)) +
        ∑ g ∈ Finset.univ.filter (fun g : Equiv.Perm (Fin p) => g.cycleType = ({p} : Multiset ℕ)),
          ci g + ∑ g ∈ s, ci g := by
    rw [Cperm]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = (1 : Equiv.Perm (Fin p)))]
    rw [show (Finset.univ.filter (· = (1 : Equiv.Perm (Fin p)))) = {1} from by ext g; simp]
    rw [Finset.sum_singleton]
    rw [show (Finset.univ.filter (fun g : Equiv.Perm (Fin p) => ¬ g = 1)) =
        (Finset.univ.filter
          (fun g : Equiv.Perm (Fin p) => g.cycleType = ({p} : Multiset ℕ))) ∪ s
        from by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hs]
      constructor
      · intro hg1
        by_cases hgp : g.cycleType = {p}
        · exact Or.inl hgp
        · exact Or.inr ⟨hg1, hgp⟩
      · rintro (h | h)
        · intro hcontra
          rw [hcontra] at h
          simp at h
        · exact h.1]
    rw [Finset.sum_union]
    · ring
    · rw [Finset.disjoint_left]
      intro g hg1 hg2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs] at hg1 hg2
      exact hg2.2 hg1
  rw [hsplit, hQ]
  have hci1 : ci (1 : Equiv.Perm (Fin p)) = (MvPolynomial.X 1 : MvPolynomial ℕ ℤ) ^ p := by
    simp [ci, Equiv.Perm.cycleType_one]
  have hcip : ∑ g ∈ Finset.univ.filter (fun g : Equiv.Perm (Fin p) => g.cycleType = ({p} :
      Multiset ℕ)), ci g = ((p - 1)! : MvPolynomial ℕ ℤ) * MvPolynomial.X p := by
    have hciform : ∀ g : Equiv.Perm (Fin p), g.cycleType = ({p} : Multiset ℕ) →
        ci g = MvPolynomial.X p := by
      intro g hg
      simp only [ci, hg, Fintype.card_fin, Multiset.sum_singleton, Multiset.map_singleton,
        Multiset.prod_singleton]
      have : p - p = 0 := by omega
      rw [this, pow_zero, one_mul]
    rw [Finset.sum_congr rfl (fun g hg => hciform g (Finset.mem_filter.mp hg).2)]
    rw [Finset.sum_const]
    have hcard := card_singleCycle_eq_choose_mul (α := Fin p) p hp.two_le
    rw [Fintype.card_fin, Nat.choose_self, one_mul] at hcard
    rw [hcard]
    ring
  rw [hci1, hcip]

/-- **Proposition `prop:prime`**: for every prime `p`, `A_w(p) ≡ w_1 - w_p (mod p)`. -/
theorem AwPerm_prime_cong (w : ℕ → ℤ) (p : ℕ) (hp : p.Prime) :
    (p : ℤ) ∣ (AwPerm w p - (w 1 - w p)) := by
  haveI := Fact.mk hp
  obtain ⟨Q, hQ⟩ := Cperm_prime_decomp p hp
  have hAw : AwPerm w p = w 1 ^ p + ((p - 1)! : ℤ) * w p + (p : ℤ) * MvPolynomial.eval w Q := by
    rw [AwPerm, hQ]
    simp only [map_add, map_mul, map_pow, MvPolynomial.eval_X, map_natCast]
  rw [hAw]
  have hfermat : (p : ℤ) ∣ (w 1 ^ p - w 1) := by
    have := ZMod.pow_card (w 1 : ZMod p)
    have hcast : ((w 1 ^ p - w 1 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [this]
      ring
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  have hwilson : (p : ℤ) ∣ (((p - 1)! : ℤ) + 1) := by
    have hw := ZMod.wilsons_lemma p
    have hcast : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by
      push_cast
      rw [hw]
      ring
    have h2 : p ∣ ((p - 1)! + 1) := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    exact_mod_cast h2
  have key : w 1 ^ p + ((p - 1)! : ℤ) * w p + (p : ℤ) * MvPolynomial.eval w Q - (w 1 - w p) =
      (w 1 ^ p - w 1) + (((p - 1)! : ℤ) + 1) * w p + (p : ℤ) * MvPolynomial.eval w Q := by
    ring
  rw [key]
  exact dvd_add (dvd_add hfermat (Dvd.dvd.mul_right hwilson (w p)))
    (Dvd.intro (MvPolynomial.eval w Q) rfl)

end CongruenceTheory
