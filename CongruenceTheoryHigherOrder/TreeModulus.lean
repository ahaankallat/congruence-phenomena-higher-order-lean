import Mathlib
import CongruenceTheory.OptimalDivisorC

/-!
**Theorem `thm:tree-modulus`** ("Binary-decomposition divisibility"), the `r ≥ 2` generalization
of `thm:optimal-divisor` (`OptimalDivisorC.lean`) to tuples via labeled binary trees.

For a tuple `n = (n_1,...,n_r)` of positive integers, a full binary tree `T` whose leaves are
labelled `n_1,...,n_r` (in order) determines, at every internal vertex `v`, two child sums
`a_v, b_v`; `μ(T) = gcd_v a_v b_v/rad(gcd(a_v,b_v))`. The manuscript's theorem:
`Δ_n = C_{N(n)} - ∏_i C_{n_i} ∈ M(n)ℤ[X]`, where `M(n) = lcm_T μ(T)` over all such trees.

**What's formalized**: `TreeFor ns` — a full binary tree whose *in-order leaf sequence* is
exactly `ns : List ℕ` (`TreeFor.leaf`/`TreeFor.node`, indexed directly by the leaf list rather
than by a separate length + assignment, so no dependent-list bookkeeping is needed). `TreeFor.mu`
mirrors `μ(T)`'s own recursive definition exactly: `0` at a leaf (no internal vertices), and at
an internal node combining `treeM` (the exact `r=2` two-term modulus from `OptimalDivisorC.lean`)
at that vertex with the `gcd` of both subtrees' own `μ`. `TreeFor.mu_dvd_defect` is the theorem
itself: for *every* tree witness `T : TreeFor ns` with all leaves positive, `μ(T)` divides every
coefficient of `Δ_ns = C_{sum ns} - ∏_i C_{n_i}`. This is the mathematical content of
`thm:tree-modulus` and, applied with `r = 2`, is *stronger* than the packaged
`M(n) = lcm_T μ(T)` statement (which would need an additional `Fintype`/enumeration of "all
trees with a given leaf sequence" — a separate combinatorial-enumeration exercise, not attempted
here, and not needed for the mathematical content: `M(n) ∣ Δ_n` is an immediate corollary of
`∀T, μ(T) ∣ Δ_n` once such an enumeration exists). `cor:tree-recursion`'s content — that `M(n)`
is computable by a finite recursion over binary tree shapes without ever expanding a cycle-index
polynomial — is exactly `TreeFor.mu`'s own recursive *definition*, so is not restated separately.

**Proof**: by induction on `T`, via the manuscript's own telescoping identity
`C_{a+b} - ∏ns = (C_{a+b}-C_aC_b) + C_b(C_a-∏l_1) + (∏l_1)(C_b-∏l_2)` (`telescope`, a pure ring
identity given `listProdC`'s distributivity over `++`) — the first summand is handled by
`treeM_dvd_defect` and the other two by the induction hypotheses via a coefficient-convolution
argument (`dvd_coeff_mul_of_dvd_coeff_right`).
-/

namespace CongruenceTheory

open MvPolynomial

/-- A full binary tree whose in-order leaf sequence is exactly `ns` — the manuscript's
"rooted full binary tree whose leaves are labelled by `n_1,...,n_r`", with the labelling
fixed to the given list's order. -/
inductive TreeFor : List ℕ → Type
  | leaf (n : ℕ) : TreeFor [n]
  | node {l1 l2 : List ℕ} (t1 : TreeFor l1) (t2 : TreeFor l2) : TreeFor (l1 ++ l2)

/-- The sum of leaf labels under a tree — the child sum at the root of a bigger tree. -/
def TreeFor.sum {ns : List ℕ} : TreeFor ns → ℕ
  | .leaf n => n
  | .node t1 t2 => t1.sum + t2.sum

/-- `μ(T)`: the gcd, over all internal vertices, of `a_v b_v / rad(gcd(a_v,b_v))`. -/
noncomputable def TreeFor.mu {ns : List ℕ} : TreeFor ns → ℕ
  | .leaf _ => 0
  | .node t1 t2 => Nat.gcd (treeM t1.sum t2.sum) (Nat.gcd t1.mu t2.mu)

/-- The product `∏_{n ∈ ns} C_n`. -/
noncomputable def listProdC (ns : List ℕ) : MvPolynomial ℕ ℤ := (ns.map C).prod

theorem listProdC_append (l1 l2 : List ℕ) :
    listProdC (l1 ++ l2) = listProdC l1 * listProdC l2 := by
  unfold listProdC
  rw [List.map_append, List.prod_append]

theorem TreeFor.sum_eq_sum_list {ns : List ℕ} (T : TreeFor ns) : T.sum = ns.sum := by
  induction T with
  | leaf n => simp [TreeFor.sum]
  | node t1 t2 ih1 ih2 => simp [TreeFor.sum, ih1, ih2, List.sum_append]

theorem TreeFor.ne_nil {ns : List ℕ} (T : TreeFor ns) : ns ≠ [] := by
  induction T with
  | leaf n => simp
  | node t1 t2 ih1 ih2 => simp [ih1]

/-- The manuscript's own telescoping identity, splitting the defect at the root's two
children — a pure ring identity given `listProdC_append`. -/
theorem telescope (a b : ℕ) (l1 l2 : List ℕ) :
    C (a + b) - listProdC (l1 ++ l2) =
      (C (a + b) - C a * C b) + C b * (C a - listProdC l1) +
        listProdC l1 * (C b - listProdC l2) := by
  rw [listProdC_append]
  ring

theorem dvd_coeff_mul_of_dvd_coeff_right {D : ℤ} {P Q : MvPolynomial ℕ ℤ}
    (h : ∀ e, D ∣ coeff e Q) (d : ℕ →₀ ℕ) : D ∣ coeff d (P * Q) := by
  rw [MvPolynomial.coeff_mul]
  apply Finset.dvd_sum
  intro x _
  exact Dvd.dvd.mul_left (h x.2) _

theorem TreeFor.sum_pos {ns : List ℕ} (T : TreeFor ns) (hpos : ∀ n ∈ ns, 1 ≤ n) :
    1 ≤ T.sum := by
  induction T with
  | leaf n => exact hpos n (by simp)
  | node t1 t2 ih1 ih2 =>
    simp only [TreeFor.sum]
    have h1 : 1 ≤ t1.sum := ih1 (fun n hn => hpos n (by simp [hn]))
    omega

/-- **`thm:tree-modulus`**: for every binary tree `T` witnessing a labelling of the positive
tuple `ns`, `μ(T)` divides every coefficient of `Δ_ns = C_{sum ns} - ∏_i C_{n_i}`. -/
theorem TreeFor.mu_dvd_defect {ns : List ℕ} (T : TreeFor ns) (hpos : ∀ n ∈ ns, 1 ≤ n) :
    ∀ d : ℕ →₀ ℕ, (T.mu : ℤ) ∣ coeff d (C T.sum - listProdC ns) := by
  induction T with
  | leaf n => intro d; simp [TreeFor.mu, TreeFor.sum, listProdC]
  | @node l1 l2 t1 t2 ih1 ih2 =>
    intro d
    have hpos1 : ∀ n ∈ l1, 1 ≤ n := fun n hn => hpos n (by simp [hn])
    have hpos2 : ∀ n ∈ l2, 1 ≤ n := fun n hn => hpos n (by simp [hn])
    have h1 : 1 ≤ t1.sum := t1.sum_pos hpos1
    have h2 : 1 ≤ t2.sum := t2.sum_pos hpos2
    have ih1' := ih1 hpos1
    have ih2' := ih2 hpos2
    have htel : C (t1.sum + t2.sum) - listProdC (l1 ++ l2) =
        (C (t1.sum + t2.sum) - C t1.sum * C t2.sum) +
          C t2.sum * (C t1.sum - listProdC l1) +
          listProdC l1 * (C t2.sum - listProdC l2) := telescope t1.sum t2.sum l1 l2
    show (Nat.gcd (treeM t1.sum t2.sum) (Nat.gcd t1.mu t2.mu) : ℤ) ∣
      coeff d (C (t1.sum + t2.sum) - listProdC (l1 ++ l2))
    rw [htel, coeff_add, coeff_add]
    have hg1 : (Nat.gcd (treeM t1.sum t2.sum) (Nat.gcd t1.mu t2.mu) : ℤ) ∣
        (treeM t1.sum t2.sum : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left _ _
    have hg2 : (Nat.gcd (treeM t1.sum t2.sum) (Nat.gcd t1.mu t2.mu) : ℤ) ∣ (t1.mu : ℤ) := by
      exact_mod_cast (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
    have hg3 : (Nat.gcd (treeM t1.sum t2.sum) (Nat.gcd t1.mu t2.mu) : ℤ) ∣ (t2.mu : ℤ) := by
      exact_mod_cast (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
    apply dvd_add
    apply dvd_add
    · exact hg1.trans (treeM_dvd_defect t1.sum t2.sum h1 h2 d)
    · exact hg2.trans (dvd_coeff_mul_of_dvd_coeff_right ih1' d)
    · exact hg3.trans (dvd_coeff_mul_of_dvd_coeff_right ih2' d)

end CongruenceTheory
