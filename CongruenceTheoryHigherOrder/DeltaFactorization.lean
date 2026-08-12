import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.CompletePrimeLocalDefect
import CongruenceTheoryHigherOrder.CShiftCongruence

/-!
**`thm:complete-prime-local`(iii)'s proof: `\Delta_{\mathbf n}\equiv C_p^{\sum q_i}\cdot[\text{
bracket}]\pmod p`.** Writing `n_i=pq_i+s_i` (`s_i=n_i\bmod p`), `\sum s_i=pH+R`
(`0\le R<p`), applies `(A10)` (`map_C_shift_cong`) to `N=\sum n_i` and to each `n_i` separately,
then regroups `\prod_iC(s_i)` by residue value (`Finset.prod_fiberwise_of_maps_to'`) into
`\prod_{s=1}^{p-1}C(s)^{c_s}` (`c_s:=\#\{i:s_i=s\}`, matching the manuscript's own `c_s`), to
extract the common factor `C_p^{\sum q_i}`.
-/

namespace CongruenceTheory

open MvPolynomial

variable {r : ℕ} (n : Fin r → ℕ) (p : ℕ)

/-- **`c_s:=\#\{i:n_i\equiv s\pmod p\}`**, the manuscript's own residue-count function. -/
noncomputable def cCount (s : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => n i % p = s)).card

/-- **`Q:=\sum_iq_i`**, the total quotient. -/
noncomputable def QTot : ℕ := ∑ i, n i / p

/-- **`H`, `R`**: `\sum_i(n_i\bmod p)=pH+R`, `0\le R<p`. -/
noncomputable def HTot : ℕ := (∑ i, n i % p) / p

noncomputable def RTot : ℕ := (∑ i, n i % p) % p

variable {p}

theorem sum_mod_eq (hp : 0 < p) : ∑ i, n i % p = p * HTot n p + RTot n p := by
  unfold HTot RTot
  exact (Nat.div_add_mod (∑ i, n i % p) p).symm

theorem sum_n_eq (hp : 0 < p) : ∑ i, n i = p * (QTot n p + HTot n p) + RTot n p := by
  have h1 : ∑ i, n i = p * (∑ i, n i / p) + ∑ i, n i % p := by
    have hde : ∀ i, n i = p * (n i / p) + n i % p := fun i => (Nat.div_add_mod (n i) p).symm
    rw [Finset.sum_congr rfl (fun i _ => hde i), Finset.sum_add_distrib, Finset.mul_sum]
  rw [h1, sum_mod_eq n hp]
  unfold QTot
  ring

/-- **Regrouping `\prod_iC(n_i\bmod p)` by residue value.** -/
theorem prod_C_mod_eq_prod_cCount (hp : 0 < p) :
    ∏ i, MvPolynomial.map (Int.castRingHom (ZMod p)) (C (n i % p)) =
      ∏ s ∈ Finset.range p,
        (MvPolynomial.map (Int.castRingHom (ZMod p)) (C s)) ^ (cCount n p s) := by
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin r)), n i % p ∈ Finset.range p :=
    fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ hp)
  rw [← Finset.prod_fiberwise_of_maps_to' hmaps
    (fun s => MvPolynomial.map (Int.castRingHom (ZMod p)) (C s))]
  apply Finset.prod_congr rfl
  intro s _
  unfold cCount
  exact Finset.prod_const _

/-- **`\prod_iC(n_i\bmod p)=\prod_{s=1}^{p-1}C(s)^{c_s}`**: the `s=0` term drops out since
`C(0)=1`. -/
theorem prod_C_mod_eq_prod_cCount_Icc (hp : 0 < p) (hp2 : 2 ≤ p) :
    ∏ i, MvPolynomial.map (Int.castRingHom (ZMod p)) (C (n i % p)) =
      ∏ s ∈ Finset.Icc 1 (p - 1),
        (MvPolynomial.map (Int.castRingHom (ZMod p)) (C s)) ^ (cCount n p s) := by
  rw [prod_C_mod_eq_prod_cCount n hp]
  have hrangeeq : Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hrangeeq, Finset.prod_insert (by simp only [Finset.mem_Icc]; omega)]
  rw [C_zero]
  simp

/-- **`\Delta_{\mathbf n}\equiv C_p^Q\cdot\bigl[C_R\cdot C_p^{H}-\prod_{s=1}^{p-1}C(s)^{c_s}
\bigr]\pmod p`.** The manuscript's factorization, before identifying `C_p\equiv X_1^p-X_p`. -/
theorem map_Delta_eq {p : ℕ} (hpp : p.Prime) (n : Fin r → ℕ) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (Delta n) =
      MvPolynomial.map (Int.castRingHom (ZMod p)) (C p) ^ (QTot n p) *
        (MvPolynomial.map (Int.castRingHom (ZMod p)) (C (RTot n p)) *
            MvPolynomial.map (Int.castRingHom (ZMod p)) (C p) ^ (HTot n p) -
          ∏ s ∈ Finset.Icc 1 (p - 1),
            (MvPolynomial.map (Int.castRingHom (ZMod p)) (C s)) ^ (cCount n p s)) := by
  have hp0 : 0 < p := hpp.pos
  have hp2 : 2 ≤ p := hpp.two_le
  unfold Delta
  rw [map_sub, map_prod]
  have hstep1 : MvPolynomial.map (Int.castRingHom (ZMod p)) (C (∑ i, n i)) =
      MvPolynomial.map (Int.castRingHom (ZMod p)) (C (RTot n p)) *
        MvPolynomial.map (Int.castRingHom (ZMod p)) (C p) ^ (QTot n p + HTot n p) := by
    rw [sum_n_eq n hp0]
    exact map_C_shift_cong hpp (QTot n p + HTot n p) (RTot n p)
  have hstep2 : ∀ i, MvPolynomial.map (Int.castRingHom (ZMod p)) (C (n i)) =
      MvPolynomial.map (Int.castRingHom (ZMod p)) (C (n i % p)) *
        MvPolynomial.map (Int.castRingHom (ZMod p)) (C p) ^ (n i / p) := by
    intro i
    have hdecomp : n i = p * (n i / p) + n i % p := (Nat.div_add_mod (n i) p).symm
    conv_lhs => rw [hdecomp]
    exact map_C_shift_cong hpp (n i / p) (n i % p)
  rw [hstep1, Finset.prod_congr rfl (fun i _ => hstep2 i), Finset.prod_mul_distrib]
  have hpoweq : ∏ i : Fin r, MvPolynomial.map (Int.castRingHom (ZMod p)) (C p) ^ (n i / p) =
      MvPolynomial.map (Int.castRingHom (ZMod p)) (C p) ^ (QTot n p) := by
    unfold QTot
    rw [Finset.prod_pow_eq_pow_sum]
  rw [hpoweq, prod_C_mod_eq_prod_cCount_Icc n hp0 hp2, pow_add]
  ring

#print axioms sum_n_eq
#print axioms sum_mod_eq
#print axioms prod_C_mod_eq_prod_cCount
#print axioms prod_C_mod_eq_prod_cCount_Icc
#print axioms map_Delta_eq

end CongruenceTheory
