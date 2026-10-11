# Higher-Order Defects of Cycle-Index Polynomials: Lean formalization

A Lean 4 / Mathlib formalization of parts of the paper *Higher-Order Defects of
Cycle-Index Polynomials: Connected Cumulants and a Prime-Local Classification*
(A. Kallat), together with two further results from the main paper
*Universal Shift Congruences for Weighted Permutation Sequences*: the lifting theorem at
every prime and a Lagrange-type theorem.

The library has 219 files (218 modules in `CongruenceTheoryHigherOrder/` and the root file
`CongruenceTheoryHigherOrder.lean`). It contains no `sorry` and declares no `axiom` or
`opaque`. The headline theorems depend only on `propext`, `Classical.choice` and
`Quot.sound` (checked with `#print axioms`).

## The paper in one paragraph

For a tuple `n = (n_1,...,n_r)` the defect is `Delta_n = C_N - prod C_{n_i}` with `N = sum n_i`,
where `C_n` is the cycle-index polynomial. The paper determines, for every prime `p`, the exact
power of `p` dividing all coefficients of `Delta_n` (the content) and the least number of
nontrivial cycles one must look at to see it (the witness depth).

## Paper theorems and Lean statements

Names are Lean declarations in the namespace `CongruenceTheory` (file in
`CongruenceTheoryHigherOrder/`).

| Paper | Lean | File |
|---|---|---|
| Lemma `semiregular-divisor` (inequality A1) | `coeff_K_dvd` | `InequalityA1` |
| Two-root bound (A2a), non-cut-vertex case | `card_A_factorization_le` | `A2FullBound` |
| Two-root bound (A2a), cut-vertex case | `factorization_card_le_cutVertex_unconditional` | `A2aCutVertexUnconditional` |
| Coefficient identity `(jp-1)!` (A3) | `A3_coeff_eq_factorial` | `A3Final` |
| Moment-cumulant factorization (A4) | `genGfun_eq_prod_K` | `GeneralizedGfunProd` |
| Proposition `first-prime-layer` | `firstPrimeLayer` | `FirstPrimeLayer` |
| Corollary `triangular-independence` | `triangular_independence` | `TriangularIndependenceFinal` |
| Corollary `cycle-depth-hierarchy`, Definition `prime-cycle-depth` | `cont_dvd_Dgcd`, `Dgcd_succ_dvd`, `Dgcd_half_eq_cont` (`Dgcd` is `D_s`) | `CycleDepthHierarchy` |
| Theorem `common-prime-classification`, valuation | `common_prime_classification_valuation` | `CommonPrimeClassificationValuation` |
| Theorem `common-prime-classification`, depth | `common_prime_classification_depth` | `CommonPrimeClassificationDepth` |
| Theorem `complete-prime-local`, case (i) | `complete_prime_local_case_i_general` (valuation), `complete_prime_local_case_i_depth` (depth, file `CompletePrimeLocalDefect`) | `CompletePrimeLocalCaseIDispatch` |
| Theorem `complete-prime-local`, case (ii) | `complete_prime_local_case_ii_general` | `CompletePrimeLocalCaseIIGeneral` |
| Theorem `complete-prime-local`, case (iii), valuation | `complete_prime_local_case_iii_valuation` | `CompletePrimeLocalCaseIIIValuation` |
| Theorem `complete-prime-local`, case (iii), depth | `complete_prime_local_case_iii_depth_full` | `CompletePrimeLocalCaseIIIDepthFull` |
| Theorem `tree-modulus` (per tree) | `TreeFor.mu_dvd_defect` | `TreeModulus` |
| Theorem `allocation-formula` (counting form) | `coeff_listProdC_eq_card` | `AllocationFormula` |
| Lemma `uniform-hypertree-enumerator` (generating-function identity) | `hypertree_enumerator` | `HypertreeEnumerator` |
| Lifting theorem at every prime (main paper, Theorem 39) | `lift_all_primes` | `LiftAllPrimes` |
| Lagrange-type theorem (main paper) | `lagrange_type`, `lagrange_type_shift` | `LagrangeFamily` |

Precise forms of the classification statements:

* Common-prime case: the valuation is exactly `min W_p` over the achieved non-refining shapes
  whenever that set is nonempty (at least two blocks). The depth statement asserts that there is
  a least `k_min >= 1` with `v_p(D_s) = nu`; `k_min` is built in the proof as the minimum of `k(lambda)`
  over the minimizing shapes.
* Case (ii): an exceptional block at any position, a remaining subtuple `m` of at least two blocks,
  with `nu` and `d = delta_p(m)` as inputs. Conclusion: valuation `min{b, nu}` and depth `1` if `b <= nu`, `d` otherwise.
* Case (iii): the valuation `0` is unconditional for at least two blocks of nonzero residue. The depth
  statement is formalized under the hypothesis that `Phi_c` (`Dc p R H c`) is nonzero, and gives the existence of
  `kappa` such that `p^kappa` is the least `s >= 1` with `D_s` nonzero and prime to `p`. The identification of
  `kappa` with the number of divisions in (A8) is carried by the `Dc` recursion lemmas
  (`DcOrderStep`, `DcOrderRecursion`, `DcFrobenius`), not by a single tuple-level statement.

Nearby forms: `tree-modulus` is proved as divisibility by `mu(T)` for each tree `T`, not as the
least common multiple `M(n)`; `allocation-formula` is proved as a count of tuples of permutations,
not as the closed sum over matrices; the hypertree enumerator is the generating-function identity
for the Pruefer data, without the bijection with hypertrees.

## Not formalized

Theorem `atomic-connected-content` is not assembled into a single Lean theorem: the group-action-to-coefficient
bridge for the second divisor, the root and connectivity witness for the group `H~`, and the link between the
hypertree enumerator and the coefficients of `K_r(q)` are missing. Also not formalized: the explicit witness
bounds (Corollaries `one-cycle-witness` and `two-cycle-witness`), the closed formulas of the two subsections
on singleton blocks (Theorem `two-singleton-collapse` through Theorem `one-singleton-repeated`), and Theorem
`scope-completeness`.

## Building

```
lake exe cache get      # Mathlib binaries
lake build
```

Toolchain: `leanprover/lean4:v4.31.0` (see `lean-toolchain`), Mathlib `v4.31.0`. To check axioms for
a theorem, add `#print axioms CongruenceTheory.firstPrimeLayer` (or any name above) to a scratch file that
imports `CongruenceTheoryHigherOrder`, and run `lake env lean scratch.lean`.

## Dependency

The library depends on the repository
[`congruence-phenomena-lean`](https://github.com/ahaankallat/congruence-phenomena-lean) (the Lean
library of the main paper) as a Lake dependency, for the shared definitions (`Basic`, `Perm`, `OrbitSum`,
`CpermEqC`, `ContentBounds`, `OptimalDivisorC`, `StrongWeighted`, `WeightedSpecialization`).

## Two additional results

* `LiftAllPrimes.lean`: for a prime `p` dividing `k > 0`, every coefficient of `C_{pk} - C_k^p` is divisible
  by `p^(2 v_p(k))` for odd `p` and `p^(2 v_p(k) - 1)` for `p = 2` (`lift_all_primes`). The proof uses
  the connected cumulants of this library.
* `LagrangeFamily.lean`: for integer series `F, G` the sequence `n! [x^n] exp(xG(x)) F(x)^n` is of the form
  `A_w(n)` with integral weights `w`, and `A_w(k) = (F(0)G(0))^k (mod k)` (`lagrange_type`); the file contains
  its own proof of Lagrange inversion.

## History

`docs/PROGRESS_LOG.md` is the original development log, kept for reference. It is out of date.
