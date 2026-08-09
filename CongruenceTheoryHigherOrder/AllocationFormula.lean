import Mathlib
import CongruenceTheory.ContentBounds
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.TreeModulus

/-!
**Theorem `thm:allocation-formula`** ("Exact allocation formula"): for a tuple
`n=(n_1,...,n_r)`, `N=∑n_i`, and a partition `λ=(1^{m_1}2^{m_2}⋯)⊢N`, the manuscript gives a
closed form `[X_λ]∏_i C_{n_i} = ∑_Q W(Q)`, summing over matrices `Q=(q_{ij})` of nonnegative
integers with `∑_i q_{ij}=m_j` and `∑_j j q_{ij}=n_i`, where
`W(Q)=∏_i n_i!/∏_i∏_j j^{q_{ij}}q_{ij}!`.

**What's formalized**: the coefficient-*counting* form of the same identity —
`coeff_listProdC_eq_card` — which is the same mathematical content one step before its closed
evaluation: `[X_λ]∏_i C_{n_i}` equals the number of tuples `(g_1,...,g_r)` (one permutation
`g_i : Equiv.Perm (Fin n_i)` per entry) whose *combined* cycle type sums to `λ`'s non-trivial
part. This is proved via `PermTuple ns` (a heterogeneous list of permutations indexed directly
by the list `ns=[n_1,...,n_r]`, mirroring `TreeModulus.lean`'s `TreeFor` pattern) and its
`Fintype` instance, `PermTuple.ciProd` (the combined cycle-indicator monomial `∏ᵢci(g_i)`, shown
in `PermTuple.ciProd_eq_monomial` to literally equal a single `ciExp`-monomial via
`ciExp_add`/`ci_eq_monomial`), and `listProdC_eq_sum_ciProd` (identifying `∏_iC_{n_i}` — via the
`Cperm=C` bridge — with the sum of these monomials over all tuples). Extracting the coefficient
at `λ` then counts exactly the tuples whose combined cycle type matches, via `ciExp`'s
injectivity (`ciExp_eq_iff`).

Reaching the manuscript's literal `∑_Q W(Q)` closed form from here needs one further step —
partitioning `PermTuple`s by each individual `g_i`'s own cycle type `μ_i` (with `∑μ_i=λ` as
multisets, the same data as a matrix `Q`) and applying the closed-form class-size count to each
`g_i` separately (`coeff_Cperm_closed_form` below does exactly this for a *single* factor, via
Mathlib's `Equiv.Perm.card_of_cycleType`) — a further combinatorial bijection not carried out
here, matching this codebase's standing practice of stating the honest mathematical content
reached rather than glossing a further, separate combinatorial-enumeration step.
-/

namespace CongruenceTheory

open MvPolynomial

/-- The class-size formula for a *single* cycle-index factor: `[X_μ]C_n = n!/z_μ`, connecting
`coeff_sum_ci_eq_card_cycleType`'s counting form to Mathlib's closed-form
`Equiv.Perm.card_of_cycleType`. The per-factor building block for the manuscript's `W(Q)`. -/
theorem coeff_Cperm_closed_form (n : ℕ) (m : Multiset ℕ) (hm2 : ∀ x ∈ m, 2 ≤ x)
    (hmsum : m.sum ≤ n) :
    coeff (ciExp (n - m.sum) m) (Cperm n) =
      ((Nat.factorial n / (Nat.factorial (n - m.sum) * m.prod *
        ∏ x ∈ m.toFinset, Nat.factorial (m.count x)) : ℕ) : ℤ) := by
  have hcount : coeff (ciExp (n - m.sum) m) (Cperm n) =
      ((Finset.univ.filter (fun g : Equiv.Perm (Fin n) => g.cycleType = m)).card : ℤ) := by
    unfold Cperm
    rw [show n - m.sum = Fintype.card (Fin n) - m.sum by rw [Fintype.card_fin]]
    exact coeff_sum_ci_eq_card_cycleType (α := Fin n) m hm2
  rw [hcount]
  have hcard := Equiv.Perm.card_of_cycleType (α := Fin n) m
  rw [show (Finset.univ.filter (fun g : Equiv.Perm (Fin n) => g.cycleType = m)) =
      ({g | g.cycleType = m} : Finset (Equiv.Perm (Fin n))) from rfl]
  rw [hcard]
  rw [if_pos ⟨by simpa using hmsum, hm2⟩]
  simp

/-- A tuple of permutations `(g_1,...,g_r)` with `g_i : Equiv.Perm (Fin n_i)`, indexed
directly by the list `ns = [n_1,...,n_r]` (a "heterogeneous list" avoiding dependent-length
bookkeeping, matching `TreeModulus.lean`'s `TreeFor` pattern). -/
inductive PermTuple : List ℕ → Type
  | nil : PermTuple []
  | cons {n : ℕ} (g : Equiv.Perm (Fin n)) {ns : List ℕ} (rest : PermTuple ns) :
      PermTuple (n :: ns)

noncomputable instance : Fintype (PermTuple []) where
  elems := {PermTuple.nil}
  complete := by intro f; cases f; simp

/-- The natural equivalence `Perm(Fin n) × PermTuple ns ≃ PermTuple (n :: ns)`. -/
def permTupleConsEquiv (n : ℕ) (ns : List ℕ) :
    Equiv.Perm (Fin n) × PermTuple ns ≃ PermTuple (n :: ns) where
  toFun := fun p => PermTuple.cons p.1 p.2
  invFun := fun f => by
    cases f with
    | cons g rest => exact (g, rest)
  left_inv := fun p => rfl
  right_inv := fun f => by cases f with | cons g rest => rfl

noncomputable instance instFintypePermTupleCons (n : ℕ) (ns : List ℕ) [Fintype (PermTuple ns)] :
    Fintype (PermTuple (n :: ns)) :=
  Fintype.ofEquiv (Equiv.Perm (Fin n) × PermTuple ns) (permTupleConsEquiv n ns)

noncomputable instance instFintypePermTuple : ∀ ns : List ℕ, Fintype (PermTuple ns)
  | [] => inferInstance
  | n :: ns => @instFintypePermTupleCons n ns (instFintypePermTuple ns)

/-- The combined cycle-indicator monomial `∏ᵢ ci(g_i)` of a permutation tuple. -/
noncomputable def PermTuple.ciProd : {ns : List ℕ} → PermTuple ns → MvPolynomial ℕ ℤ
  | _, .nil => 1
  | _, .cons g rest => ci g * rest.ciProd

theorem listProdC_eq_sum_ciProd : ∀ ns : List ℕ,
    listProdC ns = ∑ f : PermTuple ns, f.ciProd
  | [] => by
      simp [listProdC]
      rw [show (Finset.univ : Finset (PermTuple [])) = {PermTuple.nil} from rfl]
      simp [PermTuple.ciProd]
  | n :: ns => by
      have hstep : listProdC (n :: ns) = Cperm n * listProdC ns := by
        unfold listProdC
        rw [List.map_cons, List.prod_cons, ← Cperm_eq_C]
      rw [hstep, listProdC_eq_sum_ciProd ns]
      unfold Cperm
      rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
      rw [← Equiv.sum_comp (permTupleConsEquiv n ns) (fun f => f.ciProd)]
      apply Finset.sum_congr rfl
      intro p _
      rfl

/-- The combined cycle type `⊎ᵢ cycleType(g_i)` of a permutation tuple — the multiset sum,
matching `λ`'s non-trivial part in the manuscript's statement. -/
noncomputable def PermTuple.combinedCycleType : {ns : List ℕ} → PermTuple ns → Multiset ℕ
  | _, .nil => 0
  | _, .cons g rest => g.cycleType + rest.combinedCycleType

theorem PermTuple.combinedCycleType_no_ones {ns : List ℕ} (f : PermTuple ns) :
    ∀ x ∈ f.combinedCycleType, x ≠ 1 := by
  induction f with
  | nil => simp [PermTuple.combinedCycleType]
  | cons g rest ih =>
    intro x hx
    simp only [PermTuple.combinedCycleType, Multiset.mem_add] at hx
    rcases hx with hx | hx
    · have := Equiv.Perm.two_le_of_mem_cycleType hx; omega
    · exact ih x hx

theorem PermTuple.combinedCycleType_sum_le {ns : List ℕ} (f : PermTuple ns) :
    f.combinedCycleType.sum ≤ ns.sum := by
  induction f with
  | nil => simp [PermTuple.combinedCycleType]
  | cons g rest ih =>
    simp only [PermTuple.combinedCycleType, List.sum_cons, Multiset.sum_add]
    have hg := Equiv.Perm.sum_cycleType_le g
    simp only [Fintype.card_fin] at hg
    omega

/-- The combined cycle-indicator monomial of a tuple is a single `ciExp`-monomial, with
exponent `(ns.sum - combinedCycleType.sum, combinedCycleType)` — the r-ary generalization of
`ci_eq_monomial`. -/
theorem PermTuple.ciProd_eq_monomial {ns : List ℕ} (f : PermTuple ns) :
    f.ciProd = MvPolynomial.monomial (ciExp (ns.sum - f.combinedCycleType.sum)
      f.combinedCycleType) (1 : ℤ) := by
  induction f with
  | nil => simp [PermTuple.ciProd, PermTuple.combinedCycleType, ciExp]
  | @cons n g ns' rest ih =>
    simp only [PermTuple.ciProd, PermTuple.combinedCycleType]
    rw [ih, ci_eq_monomial, MvPolynomial.monomial_mul, one_mul, ciExp_add]
    rw [show n - g.cycleType.sum + (ns'.sum - rest.combinedCycleType.sum) =
        (n :: ns').sum - (g.cycleType + rest.combinedCycleType).sum by
      have h1 : g.cycleType.sum ≤ n := by simpa using Equiv.Perm.sum_cycleType_le g
      have h2 : rest.combinedCycleType.sum ≤ ns'.sum := rest.combinedCycleType_sum_le
      simp only [List.sum_cons, Multiset.sum_add]
      omega]

/-- **`thm:allocation-formula`, coefficient-counting form**: `[X_λ]∏_iC_{n_i}` equals the
number of permutation tuples `(g_1,...,g_r)` whose combined cycle type is exactly `λ`. -/
theorem coeff_listProdC_eq_card (ns : List ℕ) (m : Multiset ℕ) (hm : ∀ x ∈ m, x ≠ 1) :
    coeff (ciExp (ns.sum - m.sum) m) (listProdC ns) =
      ((Finset.univ.filter (fun f : PermTuple ns => f.combinedCycleType = m)).card : ℤ) := by
  rw [listProdC_eq_sum_ciProd, MvPolynomial.coeff_sum]
  have hstep : ∀ f : PermTuple ns,
      coeff (ciExp (ns.sum - m.sum) m) f.ciProd = if f.combinedCycleType = m then 1 else 0 := by
    intro f
    rw [f.ciProd_eq_monomial, MvPolynomial.coeff_monomial]
    simp only [ciExp_eq_iff f.combinedCycleType_no_ones hm]
    by_cases hfm : f.combinedCycleType = m
    · simp [hfm]
    · simp [hfm]
  simp_rw [hstep]
  rw [show (∑ f : PermTuple ns, if f.combinedCycleType = m then (1 : ℤ) else 0) =
      (((Finset.univ.filter (fun f : PermTuple ns => f.combinedCycleType = m)).card : ℕ) : ℤ) by
    rw [Finset.card_filter]
    push_cast
    rfl]

end CongruenceTheory
