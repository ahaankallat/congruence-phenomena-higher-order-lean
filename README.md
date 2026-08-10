# A General Theory of Congruence Phenomena, Part II — Lean

A Lean 4 / Mathlib formalization of `A_General_Theory_of_Congruence_Phenomena_II.tex`
("Connected Cumulants and the Complete Prime-Local Classification of
Higher-Order Defects"), Part II of a two-part manuscript. Depends on
[`congruence-phenomena-lean`](https://github.com/ahaankallat/congruence-phenomena-lean)
(Part I) as a Lake library dependency for the shared cycle-index and
orbit-counting foundations (`Basic`, `Perm`, `OrbitSum`, `CpermEqC`,
`ContentBounds`, `OptimalDivisorC`, `StrongWeighted`).

## Status: substantial partial coverage; the headline theorem is not yet closed

Unlike Part I, **this repository does not fully verify Part II's headline
result.** All of Part II's proofs are ordinary written mathematical proofs,
checked in the usual way; what follows is an honest report of how far this
independent Lean formalization has gotten, not a claim that the paper's
results are unverified in the traditional sense.

The tree-divisor and exact-allocation machinery (`thm:tree-modulus`,
`thm:allocation-formula`) is formalized up to two documented packaging gaps:
proved in a per-witness-tree form and a coefficient-counting form
respectively, rather than evaluated into the paper's closed lcm/sum form.
Neither gap affects either theorem's mathematical content, only how
literally the Lean statement matches the paper's closed-form packaging.

The connected-cumulant chapter (`thm:atomic-connected-content` through
`thm:one-singleton-repeated`, roughly fifteen results) is where the
manuscript underlying this two-part work previously contained a real proof
gap, later found and repaired (a false two-root faithfulness assertion,
replaced by the two-root constellation-automorphism bound used in the
current proof). This chapter has received the most formalization effort of
any part of the project, and substantial pieces are complete — including
`coeff_K_dvd` (inequality (A1), the semiregular wreath-product divisor,
proved at the level of every coefficient), both cases of the two-root bound
(A2a), the opening coefficient identity of the sharpness argument (A3,
`A3_coeff_eq_factorial`), and the abstract moment-cumulant factorization
mechanism (A4, `genGfun_eq_prod_K`) — each independently `#print axioms`
checked to depend only on Lean/Mathlib's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

**External review of an earlier version of this README caught a genuine,
previously undocumented gap**, since closed: the non-cut-vertex case of
(A2a) obtained the cardinality bound `|A|≤R_u∏_{i≠u}(R_i-1)!`
(`card_le_root_bound`, `A2aRootBound.lean`) and inferred the valuation bound
`v_p(|A|)≤1+Σv_p((R_i-1)!)` from it via "since `v_p(R_u)≤1+v_p((R_u-1)!)`" —
an invalid step, since `a≤b` does not imply `v_p(a)≤v_p(b)` in general
(`8<10` but `v_2(8)=3>1=v_2(10)`). This is now fully closed:
`card_le_root_bound_valuation` (`A2aValuationBound.lean`) proves the actual
valuation-level statement via a genuine orbit-stabilizer argument — the
orbit of the root incidence satisfies only `p^k≤R_u`, not a divisibility
relation to `R_u`, supporting the weaker (but sufficient) bound
`v_p(orbit)≤⌊log_pR_u⌋≤1+v_p((R_u-1)!)` (`A2aLogFactorialBound.lean`); the
stabilizer term is bounded via genuine group-theoretic divisibility
(`card_dvd_prod_factorial_mul_card_fixBlocks`, `key_induction_dvd`,
`key_induction_rooted_dvd` — divisibility upgrades of the existing
cardinality-only machinery, which already contained an exact
`|A|=|range|·|ker|` factorization via the first isomorphism theorem, just
not previously exposed as a divisibility fact). All five new theorems are
independently `#print axioms`-checked to depend only on
`propext`/`Classical.choice`/`Quot.sound`, zero `sorry`.

**One gap remains open, and `thm:atomic-connected-content` as a whole is not
closed:** the cut-vertex case of (A2a) has both the same kind of
cardinality-to-valuation gap just closed for the non-cut-vertex case and,
separately, its formalized bound groups branches by two numeric invariants
(attachment count and block size) as a proxy for the paper's
rooted-isomorphism type. This proxy is necessary but not sufficient, so the
formalized bound can, in principle, be looser than the paper's exact claim
whenever two non-isomorphic branches happen to share both invariants.

**Substantial progress on the valuation half — all four pieces the outer
bound needs are now individually proved:**

1. `A2aCutVertexC0Valuation.lean`: `factorization_card_le_cutVertex_c0_bound`
   closes the valuation gap for the distinguished-component (`C0`) branch,
   `v_p(|A|) ≤ 1+v_p((a_0-1)!)+Σ_{i∈c0}v_p((R_i-1)!)+v_p(|ker(islandHom)|)`,
   via exact orbit-stabilizer factorization, the log-factorial lemma for
   the one genuinely value-only step, and genuine Lagrange-style
   divisibility (a new `card_dvd_island_tight_bound`) for the rest.
2. `A2aCutVertexFiberPermHom.lean`: the `m_τ!` factor is closed by a
   single-shot Lagrange argument, not iterative orbit-peeling (which would
   telescope to something strictly weaker than `v_p(m_τ!)` — the same
   `≤`-does-not-imply-`v_p`-`≤` issue in a new guise: bounding each peeled
   orbit by the shrinking fiber and applying the log-factorial lemma at
   every step loses a full unit of `p`-adic budget per component whenever
   `p` does not divide that component's attachment count).
   `card_dvd_fiberHom_range_factorial` restricts the component-permutation
   action to a single `compType`-fiber via a genuine `MonoidHom`
   (`fiberHom`) and applies Lagrange once: `Nat.card(range) ∣ fiber.card!`.
3. `A2aCutVertexFiberAttachmentHom.lean`: the `(a_τ!)^{m_τ}` factor is
   closed the same way, one level in. Inside `fiberHom`'s kernel, every
   component of the fiber is fixed setwise, hence its attachment set is
   too; `attachmentFiberHom` bundles all of them into one `MonoidHom` into
   `∏_{c∈fiber} Equiv.Perm(AmbientC0Attach c)`, and
   `card_dvd_attachmentFiberHom_range_prod` gets
   `Nat.card(range) ∣ ∏_{c∈fiber}(AmbientC0Attach(c).card)!` by Lagrange —
   again no orbit, no log-factorial, no telescoping loss, replacing an
   earlier plan (chaining the single-component valuation bound across a
   fiber one at a time) that turned out to be *valid but too weak*: each
   peel would pay `1+v_p((a-1)!)` for a component of attachment count `a`,
   a full unit looser than the needed `v_p(a!)` whenever `p∤a`.
4. `A2aCutVertexIslandFiberInduction.lean`: the remaining `B_τ^{m_τ}`
   factor (island contents). Inside `attachmentFiberHom`'s kernel, every
   attachment point of every component in the fiber is already fixed
   *pointwise*, so peeling one component's island at a time here is
   lossless (`Nat.card K = Nat.card(PtStab K p₀)` outright, no
   orbit-stabilizer factor, since `p₀` is already fixed) —
   `key_induction_island_dvd` chains the already-proved
   `card_dvd_island_tight_bound` across the fiber via pure divisibility,
   using a new `FixIslands` subgroup (mirroring the existing `FixBlocks`
   pattern) to track what's left.

All new theorems zero `sorry`, standard axioms only
(`[propext, Classical.choice, Quot.sound]`), verified via `#print axioms`.

**What remains to assemble the full outer bound**: chain these four
per-fiber pieces into one theorem, then iterate across every `compType` in
`compTypeSet`, then combine with the `C0` branch into the final
valuation-level cut-vertex bound — wiring, not new mathematics.
`DisjointTupleSymmetry.lean`'s `factorial_dvd_card_disjointTuple` (an
independent, self-contained proof of the `m_τ!` divisibility principle) is
superseded for this purpose by `fiberHom`'s direct construction, but is
left in place as a standalone fact.

**A second gap, previously listed here, is now resolved:** the point-level
hypothesis `hmixed` (that the relevant mixed points, not just blocks, are
connected — used in both the cut-vertex and non-cut-vertex cases) does not
in fact need deriving from block-level connectivity at all. Tracing the
manuscript's only actual use of (A2a) shows it is never applied to the
original blocks directly, only to each block restricted to its own mixed
points. For that restriction, `hmixed` holds automatically: if `y`
witnesses that a point is mixed relative to the original block, the same
`y` (being outside a superset) is automatically outside the smaller
restricted block too. `HmixedResolution.lean` proves this
(`mixed_restricted_still_mixed`, `hmixed_of_restriction`), along with the
companion fact the connectivity hypothesis (A2a) also needs: a cross-block
`hconn`-style witness for the original blocks (`x ∈ V i`, `y ∈ V j`, `i ≠ j`,
`g.SameCycle x y`) already witnesses the same fact for the mixed-point
restrictions, since a cycle only ever contributed such a witness when it was
already mixed, so it survives the restriction unchanged. This is proved as
its own theorem, `hconn_witness_transfers`, using the file's `IsPartition`
hypothesis to get block disjointness. Zero `sorry`, standard axioms only.

Consequently `thm:atomic-connected-content`'s fully general statement, for
arbitrary block size `q`, is not yet closed by machine, but only for the
one remaining cut-vertex reason above.

**This does not, however, block `thm:complete-prime-local` or the
scope-completeness corollary.** Tracing the manuscript's own proofs shows
neither actually depends on the general statement: both use only its
single-prime specialization (the "first prime layer" step), whose two
ingredients are each already, separately, proved here with zero `sorry`,
depending only on standard axioms: the semiregular wreath-product bound for
arbitrary `r,q` (`coeff_K_dvd`, `InequalityA1.lean`) and the coefficient
identity together with Legendre's formula
(`A3_coeff_eq_factorial`/`factorization_factorial_mul_sub_one`,
`A3Final.lean`/`LegendreA3.lean`). Combining these two facts into the single
valuation statement `v_p(cont K_j(p))=e_p(j)` that
`thm:common-prime-classification` needs is elementary (the coefficient
identity gives an upper bound on the content's valuation via Legendre's
formula, the wreath-product bound gives a matching lower bound directly)
but has not yet been assembled as its own theorem here — unlike the
cut-vertex gap, this is a mechanical gap, not an open mathematical
question. The repeated-block, triple, and other structurally distinguished
closed-form theorems use their own direct arguments, whose dependence on
the general statement of `thm:atomic-connected-content` was not separately
re-examined here.


## File-by-file breakdown and progress notes

The bullets below are per-file; the longer discussion afterward walks
through the connected-cumulant chapter's progress in more narrative detail,
preserved from the formalization's own working notes.

- **`CongruenceTheoryHigherOrder/TreeModulus.lean`** — **`thm:tree-modulus`**
  ("Binary-decomposition divisibility"), the `r≥2` generalization of
  `thm:optimal-divisor` to tuples via labeled binary trees. `TreeFor ns` is
  a full binary tree whose *in-order leaf sequence* is exactly
  `ns : List ℕ` (indexed directly by the leaf list, avoiding
  dependent-length bookkeeping). `TreeFor.mu` mirrors the manuscript's
  `μ(T)` exactly: `0` at a leaf, and at an internal node `treeM` (the exact
  `r=2` modulus) at that vertex combined via `gcd` with both subtrees' own
  `μ`. **`TreeFor.mu_dvd_defect`** is the theorem: for *every* tree witness
  `T : TreeFor ns` with all leaves positive, `μ(T)` divides every
  coefficient of `Δ_ns = C_{sum ns} - ∏_i C_{n_i}`. Proved by induction on
  `T` via the manuscript's own telescoping identity
  `C_{a+b}-∏ns = (C_{a+b}-C_aC_b) + C_b(C_a-∏l_1) + (∏l_1)(C_b-∏l_2)`
  (`telescope`, pure ring algebra given `listProdC`'s distributivity over
  `++`) — the first summand via `treeM_dvd_defect`, the other two via the
  induction hypotheses through a coefficient-convolution argument
  (`dvd_coeff_mul_of_dvd_coeff_right`). This is the mathematical content of
  `thm:tree-modulus` and is honestly *stronger*, per-witness, than the
  manuscript's packaged `M(n)=lcm_T μ(T)` statement — packaging it as that
  single lcm would need a further `Fintype`/enumeration of "all trees with
  a given leaf sequence" (Catalan-many shapes), a separate combinatorial
  exercise not attempted here since `M(n)∣Δ_n` is an immediate corollary of
  `∀T,μ(T)∣Δ_n` once such an enumeration exists. `cor:tree-recursion`'s
  content — `M(n)` computable by finite recursion over tree shapes without
  expanding any cycle-index polynomial — is exactly `TreeFor.mu`'s own
  recursive *definition*, so isn't restated as a separate theorem.
- **`CongruenceTheoryHigherOrder/AllocationFormula.lean`** — **`thm:allocation-formula`,
  coefficient-counting form.** The manuscript's closed form
  `[X_λ]∏_iC_{n_i}=∑_QW(Q)` (summed over matrices `Q` with row/column-sum
  constraints) is reached here one step short of its closed evaluation:
  `coeff_listProdC_eq_card` shows `[X_λ]∏_iC_{n_i}` equals the number of
  permutation tuples `(g_1,...,g_r)` (`g_i:Equiv.Perm(Fin n_i)`) whose
  *combined* cycle type is exactly `λ`. Built from `PermTuple ns` (a
  heterogeneous list of permutations indexed directly by `ns=[n_1,...,n_r]`,
  mirroring `TreeFor`'s pattern) and its recursive `Fintype` instance;
  `PermTuple.ciProd_eq_monomial` shows the combined cycle-indicator monomial
  `∏ᵢci(g_i)` is literally a single `ciExp`-monomial (via `ciExp_add` and
  `ci_eq_monomial`); `listProdC_eq_sum_ciProd` identifies `∏_iC_{n_i}` (via
  the `Cperm=C` bridge) with the sum of these monomials over all tuples;
  extracting the coefficient at `λ` then counts matching tuples via `ciExp`'s
  injectivity. `coeff_Cperm_closed_form` supplies the per-factor closed form
  `[X_μ]C_n=n!/z_μ` (via Mathlib's `Equiv.Perm.card_of_cycleType`) that the
  manuscript's own `W(Q)` is built from. Reaching the literal `∑_QW(Q)` sum
  from here needs one further combinatorial bijection (partitioning tuples
  by each `g_i`'s individual cycle type, the same data as a matrix `Q`) —
  not carried out, matching this codebase's practice of stating the honest
  mathematical content reached rather than a further enumeration step.
- **`CongruenceTheoryHigherOrder/ConnectedCumulant.lean`** — foundational setup for
  the atomic connected-cumulant chapter's own starting definition
  `K_r(q)=∑_{π∈Π_r}μ(π,1̂)∏_{B∈π}C_{|B|q}`. `PartLat r` is the partition
  lattice `Π_r`, built directly from Mathlib's `Finpartition` (which already
  supplies the `PartialOrder`/`OrderTop`/`Fintype` instances needed); `K`
  combines this with `IncidenceAlgebra.mu` (the Möbius function of any
  locally finite order), which Mathlib already supplies generically.
  `K_one : K 1 q = C q` checks the manuscript's own stated base case. A
  direct `K_2(q)` sanity check against `IncidenceAlgebra.mu` reducing by
  `decide` at that small scale was attempted and abandoned (`decide` doesn't
  reduce `IncidenceAlgebra.mu` through `Finpartition`'s definitions at
  useful speed); not needed for `K_one`, so left undone. This file supplies
  no theorem beyond `K_one` — the actual content (`thm:atomic-connected-content`)
  needs `HypertreeEnumerator.lean`, below, plus further work not yet started.
- **`CongruenceTheoryHigherOrder/HypertreeEnumerator.lean`** — **`lem:uniform-hypertree-enumerator`**
  ("Uniform-hypertree Prüfer enumerator"), the key combinatorial tool
  `thm:atomic-connected-content` needs to evaluate `K_r(q)` in closed form,
  and the single hardest piece of new combinatorics attempted in this
  project — Mathlib has no hypertree, tree-enumeration, or Prüfer-sequence
  support of any kind, not even for ordinary (non-hyper) labeled trees.
  Formalized via the same honest-reformulation pattern used for `TreeFor`
  and `PermTuple`: `HyperTreeData r h d root` is the Prüfer-recipe data
  itself for a labelled `h`-uniform hypertree on `[r]` rooted at `root` — an
  *ordered* sequence of `d` disjoint `(h-1)`-element blocks partitioning the
  non-root points (`OrderedBlocks`, a new recursive type built by peeling
  one block at a time, mirroring `CycleTuple`'s technique) together with a
  word of `d-1` petiole values — defined directly via the recipe the
  manuscript's own bijective proof constructs (root, strip a leaf hyperedge
  at a time), rather than independently via general hypergraph
  connectivity/acyclicity axioms. `card_orderedBlocks_mul` counts
  `OrderedBlocks` exactly, in multiplied form to avoid ℕ-division
  (`(count)·k!^d=(dk)!`, via `Nat.choose_mul_factorial_mul_factorial`
  combined with the inductive count of the remainder — the *ordered* count,
  so no `/d!` is needed). **`hypertree_enumerator`** is the full
  degree-generating-function identity,
  `(∑_T∏_ix_i^{deg_T(i)-1})·(h-1)!^d=(dk)!·(∑_ix_i)^{d-1}`
  (multiplied form, `k=h-1`): the degree is read directly off the petiole
  word, and the identity follows by splitting the sum over `HyperTreeData`
  into block-choice × word (`Fintype.sum_prod_type'`) and expanding the word
  sum via `Fintype.sum_pow`. **Honest scope note**: what remains for
  `thm:atomic-connected-content` itself is the further, separate argument
  relating this identity to `K_r(q)`'s actual cycle-index coefficients —
  the manuscript's own claim that `K_r(q)` counts permutations whose
  cycle-support hypergraph on `r` prescribed blocks is connected — not
  attempted here.
- **`CongruenceTheoryHigherOrder/PartitionGluing.lean`** — the first step toward the manuscript's own
  supporting claim (stated right after `K_r(q)`'s definition, not itself a separately labeled
  result) that "coefficientwise, `K_r(q)` counts permutations whose cycle-support hypergraph on
  `r` prescribed blocks of size `q` is connected": a permutation-native realization of `K_r(q)`'s
  own defining product `∏_{B∈π}C_{|B|q}`. Labeling the `rq` points as `Fin r×Fin q`, `blockType B`
  (for a macroblock `B⊆Fin r`) is the merged label subtype of size `|B|q`; `PartitionPerm τ` is a
  tuple of independent permutations, one per macroblock of a partition `τ`, with combined
  cycle-indicator monomial `ciProd:=∏_Bci(p_B)`. `prod_C_eq_sum_ciProd` shows
  `∏_{B∈τ.parts}C(|B|q)=∑_pp.ciProd` purely algebraically ("a product of sums is a sum of
  products", `Fintype.prod_sum`) — no gluing needed for this half. `assemble` then glues a
  `PartitionPerm τ` into one actual permutation of `Fin r×Fin q` (extending each block's
  permutation to fix everything outside it, via Mathlib's `Equiv.Perm.extendDomain`, then
  combining the pairwise-disjoint — hence commuting — results via `Finset.noncommProd`).
  **`ci_assemble`** is the main theorem: `ci(assemble p)=p.ciProd`, i.e. `ci` is multiplicative
  over this gluing — a genuine generalization of the `Cperm=C` bridge's `ci_sumCongr`
  (`CpermEqC.lean`, binary gluing over `m⊕n`) to gluing over an arbitrary finite partition, via
  Mathlib's `Equiv.Perm.Disjoint.cycleType_noncommProd` and `Equiv.Perm.cycleType_extendDomain`
  plus two small helper lemmas distributing `Multiset.sum`/`.map _|>.prod` over a `Finset`-indexed
  sum of multisets. **Honest scope note**: this does not yet reach the "counts connected
  permutations" claim — that needs `assemble` shown to biject `PartitionPerm τ` with exactly the
  τ-respecting permutations, a canonical connectivity partition `π(g)` per permutation, and a
  Möbius-inversion argument over `PartLat r` — none of which is attempted here, nor is any part of
  `thm:atomic-connected-content` itself.
- **`CongruenceTheoryHigherOrder/PartitionRespects.lean`** — completes the previous file's identification:
  `assemble` is exactly a **bijection** between `PartitionPerm τ` and the permutations *respecting*
  `τ`'s block structure (`Respects τ g`: every macroblock maps into itself). `assemble_apply`
  computes `assemble p` pointwise via a general fact about `Finset.noncommProd` of
  pairwise-disjoint permutations (`noncommProd_apply_of_forall_others_fix`: if only one factor can
  move a point, `noncommProd` at that point reduces to that factor's action, proved by induction
  on the underlying `Finset` using a short direct argument that a permutation disjoint from another
  fixes every point the other moves to, `Equiv.Perm.Disjoint.apply_eq_self_of_ne`). `restrictP` is
  the inverse direction (restricting a `Respects τ g` permutation to each block via Mathlib's
  `Equiv.Perm.subtypePerm`); `assemble_restrictP`/`restrictP_assemble` show these are mutually
  inverse, packaged as `assembleEquiv`. **`sum_ci_respects_eq_prod_C`**:
  `∑_{g:Respects τ g}ci(g)=∏_{B∈τ.parts}C(|B|q)` — the permutation-native form of `K_r(q)`'s own
  defining product, one Möbius-inversion step short of the "counts connected permutations" claim
  itself. **Honest scope note**: still needed to reach `K_r(q)` (the Möbius-alternating sum over
  *all* `τ∈PartLat r`) itself: a canonical cycle-support connectivity partition `π(g)` per
  permutation (showing `Respects τ g ↔ π(g)≤τ`) and the Möbius-inversion argument identifying
  `K_r(q)` with `∑_{π(g)=⊤}ci(g)` — not attempted here, nor is any part of
  `thm:atomic-connected-content` itself.
- **`CongruenceTheoryHigherOrder/ConnectedCount.lean`** — **completes the manuscript's own supporting
  remark**, right after `K_r(q)`'s definition: "coefficientwise, `K_r(q)` counts permutations
  whose cycle-support hypergraph on `r` prescribed blocks of size `q` is connected." Supplies a
  canonical cycle-support connectivity partition `π(g)` for every permutation `g` — `touches g i j`
  (some point of macroblock `i` sent by `g` into macroblock `j`), `graphOf g` (the resulting graph
  on `[r]`, via Mathlib's `SimpleGraph.fromRel`), and `piOf g := Finpartition.ofSetoid (graphOf
  g).reachableSetoid` (macroblocks grouped by graph-reachability, via Mathlib's generic
  "a setoid on a finite type induces a partition" and "reachability is an equivalence relation").
  **`respects_iff_piOf_le`**: `Respects τ g ↔ π(g)≤τ` — one direction chases a single reachability
  witness through partition-refinement; the other propagates block-preservation along a
  `Relation.ReflTransGen` induction (via `SimpleGraph.reachable_iff_reflTransGen`), since "same
  `τ`-block" is already an equivalence relation. Combined with `PartitionRespects.lean`'s
  `sum_ci_respects_eq_prod_C`, grouping permutations by their own `π(g)` value gives
  `Ffun τ = ∑_{π≤τ}Gfun π` (`Ffun_eq_sum_Gfun`, via Mathlib's `Finset.sum_fiberwise_of_maps_to`,
  where `Ffun τ = ∏_{B∈τ.parts}C_{|B|q}` and `Gfun π := ∑_{g:π(g)=π}ci(g)`). A genuine
  **Möbius-inversion** argument — Mathlib's `IncidenceAlgebra.moebius_inversion_bot`, applied
  *coefficientwise* (extracting each monomial coefficient to stay inside `ℤ` throughout, avoiding
  casting `IncidenceAlgebra.mu`'s value across rings, then recombining via `MvPolynomial.ext`) —
  concludes **`K_eq_Gfun_top`**: `K_r(q) = ∑_{g:π(g)=⊤}ci(g)`, exactly the manuscript's remark, now
  a proved theorem. **Honest scope note**: this closes out the supporting remark completely, but
  `thm:atomic-connected-content` itself — the wreath-product stabilizer bounds, the bipartite
  incidence-graph automorphism induction, the moment-cumulant expansion, the mod-`p`
  algebraic-independence argument, the falling-factorial Vandermonde identity combined with
  `HypertreeEnumerator.lean`, and Lucas' theorem — remains entirely open and is genuinely
  research-scale work beyond what's attempted here.
- **`CongruenceTheoryHigherOrder/WreathProduct.lean`** — foundational scaffolding for inequality (A1) of
  `thm:atomic-connected-content`'s proof (the lower bound `(r-1)!q^{r-1}∣K_r(q)`), which the
  manuscript establishes via "the group `C_q^r⋊S_r`" acting by conjugation on connected
  permutations. Mathlib's only wreath product (`RegularWreathProduct`) uses the wrong action
  (`Q` on itself, not `S_r`'s natural action on `r` labelled blocks), so this builds the needed
  group **from scratch** as a genuine subgroup of `Equiv.Perm(Fin r×Fin q)`, via Mathlib's general
  external `SemidirectProduct` (needing only an arbitrary `φ:G→*MulAut N`) combined with the
  block-gluing style from `PartitionGluing.lean`. `Wreath r q := WreathN r q⋊[wreathPhi r q]
  Equiv.Perm(Fin r)` (with `WreathN r q:=Fin r→Multiplicative(ZMod q)` and `wreathPhi` permuting
  coordinates) has order `q^r·r!` (**`card_wreath`**, via Mathlib's `SemidirectProduct.card`).
  **`wreathToPerm`** is the actual action homomorphism into `Equiv.Perm(Fin r×Fin q)` (assembled
  via Mathlib's `SemidirectProduct.lift` from `wreathFn`/`wreathFg`, with `cPowHom`/`blockAction`
  supplying the per-block cyclic-power and block-permutation pieces respectively), and
  **`wreathToPerm_injective`** shows it's faithful whenever the chosen generator `c` has order
  exactly `q` — concretely instantiated as `wreathToPermRotate` via Mathlib's standard rotation
  `finRotate q` (`orderOf_finRotate`, `q≥2`, via Mathlib's `IsCycle.orderOf`). **Honest scope
  note**: this is *only* the group-and-action scaffolding — it doesn't yet touch (A1)'s actual
  mathematical content: the conjugation action on *connected* permutations of a fixed cycle type
  (needing conjugation-invariance of `ConnectedCount.lean`'s `π(g)`), and the semiregularity
  argument itself ("a stabilizer fixing one point is the identity on that block, and
  connectedness propagates this to every block") — genuinely novel group-theoretic reasoning
  specific to this manuscript, with no Mathlib precedent, not attempted here. Nor is any of (A2)
  through (A6) or Lucas' theorem.
- **`CongruenceTheoryHigherOrder/Semiregularity.lean`** — **the mathematical core of (A1)**, proving the
  manuscript's own semiregularity claim exactly: "if an element fixes one point, it is the
  identity on that block; commutation fixes every mixed cycle meeting the block pointwise, and
  connectedness propagates this to every block." **`wreathToPermRotate_eq_one_of_fixes`**: if `g`
  is connected (`piOf g=⊤`) and `w:Wreath r q` centralizes `g`'s image under the wreath action,
  then `w`'s image fixing *any* point forces it to be the identity everywhere — the stabilizer of
  a connected permutation acts freely on the `rq` labels. Proved via the manuscript's own three
  steps: `wreathToPermRotate_fixes_block` (fixing one point of a block forces the local cyclic
  power to vanish, using Mathlib's `IsCycle.pow_eq_one_iff'` — a nontrivial power of a full
  `q`-cycle has no fixed points — hence the *whole* block is fixed); a closure step inside the main
  proof (if a stabilizer element fixes a whole block `j` and some cycle of `g` connects `j` to `j'`,
  commuting `w`'s image past `g` along that cycle shows it fixes a point of `j'` too, hence the
  whole block `j'`); and `reachable_of_piOf_top` combined with a `Relation.ReflTransGen` induction
  propagating "whole block fixed" along `g`'s connectivity to *every* block. **Honest scope note**:
  this is the semiregularity claim itself; assembling the full `(r-1)!q^{r-1}∣K_r(q)` still needs
  orbit-stabilizer applied to the conjugation action on connected permutations of a fixed cycle
  type, the "free action ⟹ order divides set size" packaging, and combining across `K_r(q)`'s
  coefficients — not attempted here, nor is any of (A2) through (A6) or Lucas' theorem.
- **`CongruenceTheoryHigherOrder/ConjugationInvariance.lean`** — the missing piece needed to make "the wreath
  product acts by conjugation on connected permutations" well-defined: **`piOf_conj_eq_top`**,
  conjugating a connected permutation by a wreath element stays connected. Conjugating by
  `h:=wreathToPermRotate w` relabels macroblock `i` to `w.right i` while preserving within-block
  connectivity structure; `touches_conj` makes this precise by tracking a witness point through
  the conjugation directly (via `wreathToPerm_apply`), lifting to `graphOf`'s adjacency
  (`graphOf_conj_adj`, via Mathlib's `SimpleGraph.fromRel_adj`) and then, by induction along
  `SimpleGraph.reachable_iff_reflTransGen`, to full reachability (`graphOf_conj_reachable`). Since
  `g` connected means every macroblock pair is reachable (`reachable_of_piOf_top`,
  `Semiregularity.lean`) and `w.right` is a bijection, every pair is reachable in the conjugate's
  graph too, hence (via the converse `piOf_eq_top_of_forall_reachable`, built directly from
  `Finpartition`'s refinement order) the conjugate is connected too. **Honest scope note**: this
  closes one more piece for (A1) but doesn't assemble the inequality itself — the orbit-counting
  packaging and coefficient-combining remain, as does all of (A2) through (A6) and Lucas' theorem.
- **`CongruenceTheoryHigherOrder/StabilizerBound.lean`** — completes the manuscript's own stated conclusion
  for (A1): "Hence the stabilizer order divides `rq`." **`card_wreathStab_dvd`** proves exactly
  this: for `g` connected, the subgroup of `Wreath r q` centralizing `g`'s image under the wreath
  action has order dividing `rq`. Built from a general, reusable group-theory lemma
  (**`card_dvd_of_free_action`**: a finite group acting freely on a finite type has order dividing
  the type's size, via Mathlib's class-equation decomposition
  `MulAction.selfEquivSigmaOrbitsQuotientStabilizer`) applied to `wreathStab hq g` (the actual
  centralizer subgroup, inheriting a `MulAction` on `Fin r×Fin q` via `MulAction.compHom`), whose
  freeness is exactly `Semiregularity.lean`'s `wreathToPermRotate_eq_one_of_fixes` combined with
  the action's faithfulness. This finishes every sentence of the manuscript's own proof of (A1) as
  formalized statements. **Honest scope note**: what remains to reach the final boxed inequality
  `(r-1)!q^{r-1}∣K_r(q)` is orbit-stabilizer on the *full* wreath group's conjugation action (not
  just this centralizer subgroup) to convert "stabilizer divides `rq`" into "orbit size is a
  multiple of `q^{r-1}(r-1)!`", and relating that orbit size to an actual `MvPolynomial.coeff`
  of `K_r(q)` via `ConnectedCount.lean`'s `K_eq_Gfun_top` — bookkeeping rather than new
  mathematical content, but not attempted here. Nor is any of (A2) through (A6) or Lucas' theorem.
- **`CongruenceTheoryHigherOrder/OrbitCounting.lean`** — the numeric core of (A1)'s stated conclusion:
  "`(r-1)!q^{r-1}∣K_r(q)`." **`index_wreathStab_dvd_mul`**: for `g` connected, the index of its
  wreath-centralizer subgroup (the number of distinct wreath-conjugates of `g`, i.e. its orbit
  size) is a multiple of `q^{r-1}(r-1)!`. Purely arithmetic given what's already built: Mathlib's
  `Subgroup.index_mul_card` gives `index(wreathStab g)·|wreathStab g|=|Wreath r q|=q^r·r!`
  (`card_wreath`); `StabilizerBound.lean`'s `card_wreathStab_dvd` gives `|wreathStab g|∣rq`; since
  `q^r·r!=(rq)·(q^{r-1}(r-1)!)` (elementary), substituting and cancelling the positive stabilizer
  order gives the result. **Honest scope note**: this is the numeric heart of (A1)'s conclusion,
  but doesn't yet identify the index with a literal `MvPolynomial.coeff` of `K_r(q)` — that needs
  a genuine bijection between cosets and an explicit orbit `Finset`, showing the orbit sits inside
  `{h:π(h)=⊤∧cycleType h=cycleType g}` (via `piOf_conj_eq_top` and Mathlib's
  `Equiv.Perm.cycleType_conj`), a coefficient-extraction lemma for `Gfun ⊤` analogous to the
  existing `coeff_sum_ci_eq_card_cycleType` (`ContentBounds.lean`), and a union-of-orbits argument
  summing divisibility across every orbit in that set — not attempted here, nor is any of (A2)
  through (A6) or Lucas' theorem.
- **`CongruenceTheoryHigherOrder/InequalityA1.lean`** — **inequality (A1) fully assembled**:
  `(r-1)!q^{r-1}∣K_r(q)`, at the level of a single coefficient, closing out every piece flagged as
  open in `OrbitCounting.lean`. `wreathOrbit hq g` is the actual `Finset` of wreath-conjugates of
  `g` inside `Equiv.Perm(Fin r×Fin q)` (not just an abstract subgroup index); `card_wreathOrbit_mul`
  shows `|wreathOrbit g|·|wreathStab g|=|Wreath r q|` via a from-scratch fiber-counting argument
  (`card_conj_fiber`: every fiber of the conjugation map has the same size `|wreathStab g|`, via
  the general group identity `conj_eq_conj_iff_commute`, `a·x·a⁻¹=b·x·b⁻¹↔Commute (b⁻¹a) x`).
  Combined with `OrbitCounting.lean`'s `index_wreathStab_dvd_mul`, this gives
  **`card_wreathOrbit_dvd_mul`**: `|wreathOrbit g|` is a literal multiple of `q^{r-1}(r-1)!`.
  `wreathOrbit_subset` shows conjugates of a connected `g` stay connected and same-cycle-type;
  `connSameTypeFinset g:={h:π(h)=⊤∧cycleType h=cycleType g}` is the actual coefficient-counting
  set, whose cardinality equals `K_r(q)`'s coefficient at `g`'s cycle-type monomial via
  **`coeff_sum_ci_eq_card_cycleType_filter`** (generalizing `ContentBounds.lean`'s own coefficient
  lemma from `Finset.univ` to an arbitrary `Finset`, applied to `K_eq_Gfun_top`). A union-of-orbits
  argument — `wreathRel`/`wreathSetoid` (wreath-conjugacy is an equivalence relation) decomposes
  `connSameTypeFinset g` into wreath-orbits via Mathlib's `Finpartition.ofSetSetoid`
  (`wreathOrbit_eq_part`: each part *is* literally a `wreathOrbit`), applies
  `card_wreathOrbit_dvd_mul` to *every* part (every representative is itself connected), and sums
  (`Finpartition.sum_card_parts`+`Finset.dvd_sum`) — gives **`card_connSameTypeFinset_dvd`**, then
  **`coeff_K_dvd`**: the fully assembled inequality. **Honest scope note**: this completes (A1)
  itself at the coefficient level (equivalent to `cont K_r(q)` divisibility, since content is the
  gcd of all coefficients and this holds for every connected `g`). What remains for
  `thm:atomic-connected-content` as a whole (written when none of the below had been attempted;
  see the `A2a*.lean`/`LucasApplication.lean` entries further down for what's since been done):
  (A2)'s stabilizer bound via the bipartite incidence-graph automorphism induction with cut-vertex
  case splits (A2a) — the "`u` not a cut vertex" case is now fully formalized; the cut-vertex case's
  per-component mathematics (both the distinguished component and every other branch) is now also
  fully proved, with only the outer well-founded recursion across all components and the final
  grouped-multinomial numeric assembly remaining (see the `A2aCutVertex*.lean` entries further down)
  — the moment-cumulant expansion (A4), the mod-`p` algebraic-independence argument via
  triangular Jacobians (A5), the falling-factorial Vandermonde identity combined with
  `HypertreeEnumerator.lean` (A6), and Lucas' theorem for sharpness — the Lucas' theorem step is
  now also fully formalized — each its own substantial, research-scale undertaking.
- **`CongruenceTheoryHigherOrder/SpanningTreeLeaf.lean`** — general-purpose `SimpleGraph` infrastructure
  toward (A2a)'s bipartite incidence-graph automorphism induction, specifically the
  "`u` not a cut vertex" case's "attach a leaf" step. Two new, reusable facts not present in
  Mathlib: **`SimpleGraph.IsAcyclic.map`** — acyclicity is preserved *forward* under an injective
  graph map `f:V↪W` (`G.IsAcyclic→(G.map f).IsAcyclic`; Mathlib only has the reverse
  `IsAcyclic.of_map`), proved by pulling a hypothetical cycle in `G.map f` back along `f`'s range
  via `Walk.induce`/`Embedding.induce`/`Embedding.map f G`'s induced-range isomorphism, and
  **`SimpleGraph.exists_spanningTree_leaf`** — if `u` is not a cut vertex
  (`¬(G.induce{v≠u}).Connected` fails to hold, i.e. `IsCutVertex` is false) of a connected `G` on
  `≥2` vertices, `G` has a spanning tree with `u` as a leaf (`T≤G∧T.IsTree∧T.degree u=1`). Built by
  taking a spanning tree `T'` of `G.induce{v≠u}` (Mathlib's
  `exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic`), re-embedding it into `V` via
  `IsAcyclic.map`, and attaching `u` by a single edge to a `G`-neighbour `w` of `u`
  (`IsAcyclic.sup_edge_of_not_reachable`). **Honest scope note**: this is exactly the "attach a
  leaf" lemma needed for the tree-rooted counting injection giving `|A|≤R_u∏_{i≠u}(R_i-1)!` in the
  `u`-not-a-cut-vertex case of (A2a) — but the bipartite incidence-multigraph formalization
  (blocks/cycles as a bipartite graph with cyclic-order decorations), the automorphism-faithfulness
  claim, the counting injection itself, the "`u` is a cut vertex" case (component-type grouping),
  and all of (A2) beyond (A2a) remain fully open, as does (A4) through (A6) and Lucas' theorem.

- **`CongruenceTheoryHigherOrder/CentralizerCycleFaithful.lean`** — the group-theoretic core of (A2a)'s
  "faithfulness" claim. The manuscript asserts "the automorphism action on this decorated
  incidence graph is faithful" for the bipartite black-vertices-are-blocks/white-vertices-are-
  cycles multigraph, decorated at each white vertex with `g`'s induced cyclic order. Unpacked: an
  element `φ` of the centralizer of `g` induces the *trivial* automorphism of this decorated graph
  exactly when it fixes every block, every cycle, and — since `φ` commutes with `g`, so acts on
  any cycle it stabilizes as some power of `g` restricted to that cycle — doesn't rotate the
  induced cyclic order at any cycle, i.e. fixes a point on every cycle of `g`. So the claim reduces
  to a clean, self-contained fact independent of the blocks or tree structure, built from a
  granular reusable primitive, **`Perm.fixed_of_commute_of_fixed_point`**: if `φ` commutes with `g`
  and `φ p=p`, then `φ q=q` for every `q` on `p`'s `g`-cycle (for `q=g^i p`, commuting gives
  `φ(g^i p)=g^i(φ p)=g^i p=q`). Applying this at one point per cycle gives
  **`eq_one_of_commute_of_fixed_point_on_every_cycle`** — if `φ` commutes with `g` and fixes a
  point on every cycle of `g` (`g.SameCycle`), then `φ=1`. **Honest scope note**: as with
  `Semiregularity.lean`'s analogous treatment of (A1), the literal incidence-multigraph formalism
  (an explicit `SimpleGraph`/multigraph type with an `Aut` group) is not separately built, since it
  carries no further mathematical content beyond this fact.
- **`CongruenceTheoryHigherOrder/A2aOrbitBound.lean`** — the reusable pieces toward (A2a)'s tree-rooted
  counting bound `|A|≤R_u∏_{i≠u}(R_i-1)!`. **`fixed_block_of_fixed_point`** and
  **`card_le_card_block_mul_card_stabilizer`** are stated for an **arbitrary acting group**
  `[Group G][MulAction G Ω]` (not just a subgroup of `Equiv.Perm Ω` directly): if every element of
  `G` maps each block of a partition `V` (`IsPartition V:=∀x,∃!i,x∈V i`) onto some block and `g:G`
  fixes a point of block `i`, then `g` fixes block `i` setwise; and orbit-stabilizer instantiated
  at a block gives `|G|≤|V_i|·|Stab_G(p)|` for `p∈V_i` (via the general
  **`nat_card_orbit_mul_stabilizer`**, from Mathlib's `orbitEquivQuotientStabilizer` plus
  `Subgroup.index_mul_card`, in `Nat.card` form to match this project's convention elsewhere, e.g.
  `OrbitCounting.lean`). **`card_stabilizer_le_of_sameCycle`** demonstrates these compose across a
  shared cycle (`|Stab_A(p₀)|≤|V_j|·|Stab_{Stab_A(p₀)}(q)|`) — valuable as a proof that the
  propagation genuinely typechecks in Lean, but **not** the shape the final bound needs (it adds a
  full `|V_j|` factor per block, not `(R_j-1)!`). Working out the correct final shape surfaced a
  real gap: the manuscript's bound has a bare `R_u` for the root with **no** factor for `u`'s own
  remaining `R_u-1` points, which seemed to break injectivity until cross-checking
  `proofs/ATOMIC_TWO_ROOT_REPAIR.md` (a repair note included in this package for exactly this
  lemma) confirmed the resolution: "an automorphism is determined by the image of the decorated
  spanning tree." **`eq_on_block_of_eq_off_block_of_commute`** proves the underlying fact: if
  `φ,ψ` commute with `g` and agree everywhere outside block `V_u`, and every point of `V_u` lies on
  a `g`-cycle also meeting some point outside `V_u` (the manuscript's "only mixed cycles"
  hypothesis), then `φ,ψ` agree on `V_u` too — so `u`'s residual points are pinned for free by
  propagation from whichever other block their own cycle happens to reach, with no separate factor
  needed. This unlocks **`card_le_prod_factorial_of_fixed_points`**, the second half of (A2a)'s
  bound, **fully proved**: given a specific point `q i` in every block `i≠u`, uniformly fixed by
  every element of `A` (`hfixq`), `A` embeds into `∀i∈Finset.univ.erase u, Equiv.Perm↥(V_i∖{q_i})`
  — built via `Equiv.Perm.subtypePerm` restricting each `φ∈A` to a permutation of `V_i∖{q_i}`
  (well-defined since `hfixq`+`fixed_block_of_fixed_point` pin `q_i` and `V_i` setwise), injective
  since agreement at every `i≠u` gives agreement off `V_u` (as each block is covered) and hence,
  via `eq_on_block_of_eq_off_block_of_commute`, agreement on `V_u` too — giving
  `|A|≤∏_{i≠u}(R_i-1)!` directly (`Nat.card_pi`+`Fintype.card_perm`+`Finset.card_erase_of_mem`,
  with **no separate factor for `u`**, matching the manuscript's own bound exactly). Combined with
  `card_le_card_block_mul_card_stabilizer` (giving the `R_u` factor, applied first to reduce to
  `A=Stab(p₀)` for a chosen `p₀∈V_u`), `card_le_prod_factorial_of_fixed_points` directly gives
  `|A|≤R_u∏_{i≠u}(R_i-1)!` **whenever every non-root block is touched directly by `p₀`'s own
  cycle** (tree depth 1) — `hfixq`'s uniform fixed point `q_i` is exactly `p₀`'s cycle meeting
  block `i`, and *every* `φ∈Stab_A(p₀)` shares it, since they all share `φ(p₀)=p₀`.
  **Honest scope note, corrected from an earlier overstatement in this file**: for trees of
  depth ≥2 — a block `i` with `R_i≥3` reached from the root, itself connecting to a further block
  `k` through one of `i`'s *other* points — `hfixq` genuinely fails to hold for `k` relative to the
  *whole* `Stab_A(p₀)`, because which of `i`'s remaining `(R_i-1)!` arrangements a given `φ`
  realizes determines which point of `i` lands on `k`'s connecting cycle, so different `φ` connect
  to `k` differently. `card_le_prod_factorial_of_fixed_points` is not one missing induction away
  from the general case; it's the correct *per-layer* step of a BFS-style induction over the
  spanning tree built in `SpanningTreeLeaf.lean` — apply it once to bound the layer of blocks the
  current stabilizer's known fixed points reach uniformly, then recurse into the (smaller)
  stabilizer that produces for the next layer out. **`eq_on_blocks_of_eq_off_blocks_of_commute`**
  and **`card_le_prod_factorial_of_fixed_points_layer`** generalize the single fixed block `u` to
  an arbitrary *set* `S` (agreement outside `⋃i∈S,Vi`, with every point of `S`'s blocks
  propagating outward, forces agreement on `S` too), but still need `hfixq` to hold *uniformly for
  every block outside `S` at once* — usable once `S` is "everything but the outermost layer", not
  as a genuine step-by-step recursion on its own.
- **`CongruenceTheoryHigherOrder/A2aLayerInduction.lean`** — the piece that actually closes this gap,
  **fully proved**: a version of the layer step built from a genuine `MonoidHom`, giving a real
  *subgroup* to recurse into rather than only a cardinality bound. **`FixBlocks A V L`**: the
  subgroup of `A` fixing every block in a Finset `L` pointwise (as a subgroup of the ambient
  `Equiv.Perm Ω`, avoiding subgroup-of-subgroup nesting). **`card_le_prod_factorial_mul_card_
  fixBlocks`**: given `A` fixes a designated point in every block of `L` (only `L` — not "every
  remaining block"), the restriction map `A →* ∀i∈L,Equiv.Perm↥(Vi∖{qi})` (built from
  `Equiv.Perm.subtypePerm`, verified as an actual `MonoidHom`) has kernel exactly `FixBlocks A V
  L`, giving `|A|≤(∏i∈L,(Ri-1)!)·|FixBlocks A V L|` via Noether's first isomorphism theorem
  (`QuotientGroup.quotientKerEquivRange`) and Lagrange
  (`Subgroup.card_eq_card_quotient_mul_card_subgroup`). **`FixBlocks_fixes_of_sameCycle`**:
  elements of `FixBlocks A V L` fix every point reachable via a `g`-cycle from an already-fixed
  block in `L`, so the *next* layer's designated points are uniformly fixed by `FixBlocks A V L`
  — exactly the hypothesis needed to call `card_le_prod_factorial_mul_card_fixBlocks` again, one
  layer further out. Together these two theorems supply every ingredient the general-depth
  recursion needs, with a real, composable subgroup at each step. The well-founded recursion
  itself, assembling these into one theorem, is now built — see `A2aFullInduction.lean` next.
- **`CongruenceTheoryHigherOrder/A2aFullInduction.lean`** — **`key_induction`**, **fully proved**: the actual
  assembly of `A2aLayerInduction.lean`'s pieces into a complete, general-depth well-founded
  induction, not tied to a specific root `u`. Given a partition `V`, a permutation `g`, and
  connectivity (`hconn`: every proper nonempty "processed" set `L` of blocks has an edge leaving
  it — some `i∈L`, `j∉L` linked by a shared `g`-cycle), if a subgroup `A` (permuting blocks,
  commuting with `g`) fixes every point of every block already in a nonempty `L`, then
  `|A|≤∏_{i∉L}(R_i-1)!`. Proved by strong induction on `(Finset.univ∖L).card`: the base case
  `L=Finset.univ` makes `A` fix every point of `Ω`, hence (`Equiv.Perm.ext`) trivial, and the empty
  product is `1`; the inductive step uses `hconn` to find a boundary edge `(i,j,x,y)` with `i∈L`,
  `j∉L`, `g.SameCycle x y`, propagates `A`'s fixed point at `x` to `y` via
  `Perm.fixed_of_commute_of_fixed_point`, applies `card_le_prod_factorial_mul_card_fixBlocks` with
  the singleton layer `{j}` to get `|A|≤(R_j-1)!·|FixBlocks A V {j}|`, and recurses into
  `FixBlocks A V {j}` (which still fixes everything `L` fixed, plus all of `V j`, by
  `FixBlocks_fixes_of_sameCycle`/construction) with `L∪{j}` — one block closer to
  `Finset.univ` — with the telescoping product `(R_j-1)!·∏_{i∈(L∪{j})ᶜ}(R_i-1)!=∏_{i∈Lᶜ}(R_i-1)!`
  closing the step. `key_induction`'s invariant requires `A` to fix *every* point of the seed
  block(s) in `L`, not just one — instantiating with `L={u}` therefore needs `A` to already fix all
  of `V_u` pointwise, which the natural starting group `Stab_A(p₀)` (only fixing the single point
  `p₀∈V_u`) doesn't provide on its own. This gap is now closed — see `A2aRootBound.lean` next. Not
  attempted: the "`u` is a cut vertex" case of (A2a) (component-type grouping), or any of
  (A3) sharpness, (A4)'s moment-cumulant identity, (A5)'s algebraic-independence-via-triangular-
  Jacobians-mod-`p` argument, or (A6)'s falling-factorial Vandermonde identity — each a further
  substantial, research-scale undertaking. (A6)'s closing Lucas'-theorem application, however, *is*
  now complete — see `LucasApplication.lean` below.
- **`CongruenceTheoryHigherOrder/A2aHconnFromReachable.lean`** — closes the "establishing `hconn` from the
  manuscript's connected block-support hypergraph hypothesis" gap just flagged above, **fully
  proved**: **`blockTouches V g i j := ∃x∈V i,∃y∈V j,g.SameCycle x y`** and **`blockGraphOf V g :=
  SimpleGraph.fromRel (blockTouches V g)`** build the block-support graph on the block index type
  `ι` (mirroring `ConnectedCount.lean`/`GeneralizedConnectivity.lean`'s own `touches`/`graphOf`
  recipe from the (A4) work above, adapted to an arbitrary partition `V:ι→Finset Ω` in place of
  the canonical product structure). **`hconn_of_forall_reachable`**: ordinary graph reachability
  between every pair of blocks implies `hconn` — the standard graph-theory fact that a connected
  graph has no nonempty proper "closed" vertex subset. Proof: given a proper nonempty `L` and a
  point `j₀∉L`, induct along the `ReflTransGen`-path from any `i₀∈L` to `j₀`; at each step, either
  the path so far stays inside `L` (propagate) or a boundary edge has already been found
  (propagate that instead) — since the path ends at `j₀∉L`, staying inside `L` the whole way is
  impossible, so a boundary edge must have been produced; unpack the `SimpleGraph.fromRel`
  adjacency (symmetrized) back into the `∃x∈V i,y∈V j,SameCycle x y` witness `hconn` needs,
  using `SameCycle`'s own symmetry when the edge is found in the reversed orientation.
  **`key_induction_of_reachable`** repackages `key_induction` to take block-graph connectivity
  directly. `#print axioms`-checked standard for both.
- **`CongruenceTheoryHigherOrder/A2aHreachAll.lean`** — closes the cut-vertex case's analogous gap,
  **fully proved**: `card_le_cutVertex_full_bound''`'s `hreach_all` ("every component of the
  `ι∖{u}` block-adjacency structure has some point of `V u` reaching it") is the cut-vertex
  version of `hconn`, using the different `BlockComponent`-indexed (`Quot`-based) reachability
  notion from `A2aCutVertexComponents.lean`/`A2aCutVertexAttachment.lean`. **`hreach_all_of_forall_reachable`**
  derives it from the same `blockGraphOf` connectivity as above — the standard fact that if a
  graph is connected, every component left over after deleting a vertex `u` must have an edge
  back to `u` (otherwise, having no edge to `u` and none to any other component either by
  definition of "component of `G∖u`", it would be an isolated piece of the original graph,
  contradicting connectivity). Proof: take any representative `x₀` of the target component `c`;
  since the full graph is connected, `x₀` reaches `u`; induct along that `ReflTransGen` path,
  tracking the invariant "the current vertex is still in component `c`, or a witness has already
  been found" — the first step that lands on `u` produces the witness directly (via the shared
  edge, symmetrized as needed), and every step is confirmed to preserve the invariant since an
  edge between two non-`u` vertices staying in `ι∖{u}` is exactly a `BlockAdjSub` step,
  extending the `BlockReach`/`Quot` equivalence via `Quot.sound`. `#print axioms`-checked
  standard. **Honest scope note**: this closes exactly `hreach_all`, and `A2aHconnFromReachable.lean`
  above closes `hconn` — together, both of `key_induction`'s and `card_le_cutVertex_full_bound''`'s
  named connectivity-flavored hypotheses that *are* pure block-level connectivity facts are now
  derived from ordinary graph connectivity. `hmixed` (`∀p∈V u,∃y∉V u,g.SameCycle p y`) remains
  open: unlike `hconn`/`hreach_all`, it is a *point*-level claim (every individual point of `V u`
  reaches outside), not implied by block-level connectivity alone (some points of `V u` could in
  principle have their whole cycle confined to `V u` even while other points of `V u` connect
  outward) — not attempted here.
- **`CongruenceTheoryHigherOrder/A2aRootBound.lean`** — closes the gap left open above, giving
  **`card_le_root_bound`**, **fully proved**: the manuscript's exact literal bound
  `|A|≤R_u∏_{i≠u}(R_i-1)!` for (A2a)'s "`u` not a cut vertex" case. The fix is to never seed
  `key_induction`-style machinery at `u` at all. **`key_induction_rooted`**: a variant of
  `key_induction` whose domain of blocks is `Finset.univ.erase u` (never including `u`), whose base
  case (`L=Finset.univ.erase u`, i.e. every block *except* `u` fully pinned) is closed via
  `eq_on_block_of_eq_off_block_of_commute`'s mixed-cycle trick — comparing any `φ∈A` against the
  identity, both commute with `g`, both agree off `V_u` (since every other block is pinned), so the
  mixed-cycle hypothesis forces agreement on `V_u` too, making `A` trivial — instead of the direct
  pointwise argument `key_induction` uses for its `L=Finset.univ` base case. **`PtStab A p`**
  (`A⊓Stab_{Perm Ω}(p)`, ambient-subgroup pattern again avoiding nesting) and
  **`card_le_card_block_mul_card_ptStab`** re-derive the `R_u` orbit-stabilizer factor in this
  ambient-subgroup form (bridging `MulAction.stabilizer A p₀`, nested inside `A`, to `PtStab A p₀`,
  a genuine subgroup of `Equiv.Perm Ω`, via a direct `Equiv`). **`card_le_root_bound`** assembles
  everything: orbit-stabilizer gives `|A|≤R_u·|PtStab A p₀|`; one bootstrap application of
  `card_le_prod_factorial_mul_card_fixBlocks` (using `Perm.fixed_of_commute_of_fixed_point` to
  propagate `p₀`'s fixedness to a chosen point `y₀` of a first block `j₀` reachable via a shared
  `g`-cycle) reaches `FixBlocks (PtStab A p₀) V {j₀}` — a subgroup that fixes *all* of `V j₀`
  pointwise by construction, exactly the seed `key_induction_rooted` needs; that theorem then
  finishes the job for every remaining block, and the telescoping factorial products close the
  bound. **Honest scope note**: the connectivity hypothesis `hconn` and the initial edge from `p₀`
  are still taken as hypotheses here rather than derived from the manuscript's "connected
  block-support hypergraph"/spanning-tree structure (a translation step, not a new mathematical
  difficulty) — but the group-theoretic counting argument itself, the actual substance of (A2a)'s
  "`u` not a cut vertex" case, is now **completely formalized** end to end.
- **`CongruenceTheoryHigherOrder/A2aCutVertexValuation.lean`** — two self-contained `p`-adic valuation facts
  extracted from (A2a)'s remaining "`u` *is* a cut vertex" case, both **fully proved**:
  **`factorization_le_factorization_factorial`**, `v_p(n)≤v_p(n!)` (immediate from
  `Nat.mul_factorial_pred`, `n!=n·(n-1)!`) — the manuscript's "`v_p(a_τ)≤v_p(a_τ!)`" step; and
  **`factorization_le_one_add_factorization_factorial_pred`**, `v_p(n)≤1+v_p((n-1)!)` for `n≥1` —
  the manuscript's "`v_p(a_0)≤1+v_p((a_0-1)!)`" step (the same shape as the non-cut-vertex case's
  own `v_p(R_u)≤1+v_p((R_u-1)!)` remark, which `card_le_root_bound` above bypasses entirely by
  working with the literal `Nat` inequality rather than valuations — here, for the cut-vertex case,
  the manuscript's own argument stays at the valuation level, so the fact is proved directly).
  Proof of the second, writing `k=v_p(n)`: `p^k∣n` gives `n≥p^k`, so the single `i=1` term of
  Legendre's formula (`Nat.factorization_factorial`) gives `v_p((n-1)!)≥(n-1)/p≥(p^k-1)/p=p^{k-1}-1`
  (via a small division identity, `aux_div_pred`, `(p·m-1)/p=m-1` for `m≥1`), and `p^{k-1}≥k`
  (`Nat.lt_pow_self`) closes it: `k≤p^{k-1}≤1+(p^{k-1}-1)≤1+v_p((n-1)!)`. **Honest scope note**:
  these are the only two purely-arithmetic sub-facts of the cut-vertex case; the surrounding
  combinatorial machinery it needs — components of the incidence graph minus `u`, classifying them
  into rooted-isomorphism types `τ` with attachment numbers `a_τ` and multiplicities `m_τ`, and the
  multinomial-type divisibility `(R_u-1)!/((a_0-1)!∏_τ(a_τ!)^{m_τ}m_τ!)∈ℕ` this needs — is a further
  substantial undertaking, comparable in scope to the wreath-product argument for (A1); the `m_τ!`
  divisor's own underlying principle is now fully established (`FreeActionDivides.lean`,
  `DisjointTupleSymmetry.lean`, next), though the surrounding graph-component classification is not.
- **(A2a)'s cut-vertex "island/restriction-image" machinery** (`A2aBlockPermutation.lean`,
  `A2aCutVertexComponents.lean`, `A2aCutVertexAction.lean`, `A2aCutVertexComponentAction.lean`,
  `A2aCutVertexAttachment.lean`, `A2aCutVertexFixesC0.lean`, `A2aCutVertexInvariance.lean`,
  `A2aCutVertexIslandMap.lean`, `A2aCutVertexIslandPerm.lean`, `A2aCutVertexIslandPermMul.lean`,
  `A2aCutVertexIslandInstance.lean`, `A2aCutVertexIslandG.lean`, `A2aCutVertexIslandHperm.lean`,
  `A2aCutVertexIslandHom.lean`, `A2aCutVertexIslandFactor.lean`, `A2aCutVertexBoundaryEdge.lean`,
  `A2aCutVertexIslandSameCycle.lean`, `A2aCutVertexIslandNone.lean`, `A2aCutVertexIslandMixed.lean`,
  `A2aCutVertexIslandConn.lean`, `A2aCutVertexIslandInitEdge.lean`) — the foundational
  infrastructure for the "`u` *is* a cut vertex" case, going well beyond the two arithmetic facts
  above: builds `BlockComponent` (connected components of the block-adjacency graph on `ι∖{u}`,
  via `Relation.EqvGen`/raw `Quot`), `Reaches` (which component a point of `V u` connects to via a
  shared `g`-cycle), and — the key architectural device — the **island**
  (`InComponentPlus`: one component `c`'s own blocks *plus* the points of `V u` reaching it,
  proved `g`-invariant), together with `islandHom : ↥(PtStab A p₀) →* Equiv.Perm(island)` (a
  genuine `MonoidHom` built from `subtypePerm`) and every hypothesis `card_le_root_bound` needs to
  apply *within* the island as a smaller, self-contained instance (`IsPartition`, block
  nonemptiness, the mixed-cycle fact, an initial edge, and `hconn` — this last one proved as a
  general "no separating cut" graph fact, `exists_boundary_edge_of_blockReach`, by induction on the
  `EqvGen` witnessing two blocks' connectivity).
- **(A2a)'s cut-vertex per-component bound** (`PtStabProdBound.lean`, `IslandTightBound.lean`,
  `A2aCutVertexDistinguished.lean`, `A2aCutVertexC0Bound.lean`, `A2aCutVertexComponentHom.lean`,
  `A2aCutVertexKerAmbient.lean`, `A2aCutVertexBranchConfinement.lean`,
  `A2aCutVertexBranchOrbitStab.lean`, `A2aCutVertexBranchBound.lean`) — assembles the island
  machinery above into the manuscript's *actual* cut-vertex strategy (re-read directly from the
  LaTeX source, correcting an earlier, subtly wrong naive approach): "adjoin `u` back to a
  component, so it is no longer a cut vertex, and the non-cut-vertex bound applies to the core and
  every branch." Two fully-proved theorems now match this exactly:
  - **`card_le_cutVertex_c0_bound`** — for the manuscript's *distinguished* component `C_0`
    (containing a second fixed root block `V_{j2}`, per (A2a)'s own hypothesis that `A` fixes both
    `V_1,V_2` setwise): `A`'s induced component-permutation fixes `C_0` setwise
    (`componentPermOfMem_fixes_of_block_fixed`), confining the orbit of any `p₀` reaching `C_0` to
    `C_0`'s own `a_0`-sized attachment set rather than all of `V u`
    (`card_le_ambientAttach_mul_card_ptStab`) — avoiding a double-counting bug in an earlier
    attempt that naively re-applied `card_le_root_bound` to the island (which redundantly
    re-orbit-stabilizes a point the group already fixes). The fix,
    **`card_le_ptStab_prod_bound`**, extracts `card_le_root_bound`'s own internal block-product
    step *without* its outer `(V u).card`-factor wrapper, applied directly to `range(islandHom)`
    (which already fixes the island's seed point outright, since `PtStab(range(islandHom),p₀) =
    range(islandHom)`) via **`card_le_island_tight_bound`**. Result:
    `Nat.card A ≤ a_0·∏_{i∈C_0}(R_i-1)!·Nat.card(ker(islandHom))`, with the kernel left over.
  - **`card_le_branch_bound`** — the *same* mechanism, generalized to any other component `c1`, this
    time deriving "the component-permutation fixes `c1`" not from a hypothesis-supplied second root
    block but from being in the *stabilizer* of `c1` under a new `componentHom : A →*
    Equiv.Perm(BlockComponent)` action — so orbit-stabilizer at the component level
    (`card_eq_orbit_mul_stabAmbient`) first splits off the orbit size (the manuscript's `m_τ`
    multiplicity, for components isomorphic to `c1` that get permuted among themselves) before the
    same confinement + kernel-factorization + tight-island-bound chain applies to the stabilizer.
    This step is composable — its own leftover kernel re-embeds via `KerAmbient` (built generically,
    not hardcoded to any specific subgroup) exactly as needed to invoke `card_le_branch_bound` again
    for a further component.
  **The outer well-founded recursion is now also assembled** (`A2aCutVertexComponentComplement.lean`,
  `A2aCutVertexBaseCase.lean`, `A2aCutVertexComponentInv.lean`, `A2aCutVertexOrbitEqual.lean`,
  `A2aCutVertexOuterInduction.lean`, `A2aCutVertexFullBound.lean`), giving
  **`card_le_cutVertex_full_bound`** — a complete, fully proved, literal `Nat` bound on `|A|` for
  the whole cut-vertex case, `#print axioms`-checked to depend only on the standard
  `[propext, Classical.choice, Quot.sound]`. Getting there needed one genuine correction, recorded
  honestly in `A2aCutVertexOuterInduction.lean`'s docstring: the first design tried to remove a
  whole `A'`-orbit of components per step (to match the manuscript's `m_τ` grouping exactly), but
  the kernel obtained from peeling one component is only *guaranteed* to fix that one component's
  island pointwise, not the rest of its orbit — so the accumulating invariant the recursion's base
  case needs cannot be carried past a single component per step this way. Re-examining the
  manuscript's own target (`v_p(a_0)+Σv_p((R_i-1)!)+Σ_τ(m_τv_p(a_τ)+v_p(m_τ!))`) shows the
  `v_p(m_τ!)` term is *supposed* to be there — a per-component (not per-orbit) recursion that
  simply accumulates one orbit-size factor per component peeled, exactly like
  `key_induction_rooted`'s own "one designated point/block at a time" strategy, is the right
  mechanism to produce it. Two forms are proved: **`key_induction_cutVertex_components`**
  (`card_le_cutVertex_full_bound`) bounds every per-step orbit factor by the crude global constant
  `Fintype.card(BlockComponent V g u)`; **`key_induction_cutVertex_components'`**
  (`card_le_cutVertex_full_bound'`), a genuine sharpening, observes that `A'` already fixes every
  component outside the remaining pool `M` pointwise (hence setwise) — so an injective map can
  never send a still-unprocessed `c1∈M` to a fixed point outside `M`, confining the orbit to `M`
  itself and tightening the accumulation from `Fintype.card(BlockComponent)^{|M|}` down to
  `|M|!`, strictly smaller whenever `|M|` is less than the total component count.
  **A further sharpening is now also complete** (`A2aCutVertexComponentType.lean`,
  `A2aCutVertexOuterInductionSharp.lean`, `A2aCutVertexFullBoundSharp.lean`), giving
  **`card_le_cutVertex_full_bound''`**, `#print axioms`-checked standard. The idea: classify each
  component by `compType c := ((AmbientC0Attach c).card, ∏_{i∈c}(R_i-1)!)` — exactly the two
  numeric invariants `card_ambientAttach_eq_of_moved`/`prod_blockSet_eq_of_moved` already show are
  preserved along an `A'`-orbit, so an orbit is confined not just to `M` but to `M`'s same-`compType`
  fiber. `classFactorialProd g u M := ∏_{types τ} (fiber_τ(M)).card!`, indexed over the *fixed*
  `compTypeSet` (all types occurring anywhere) so it telescopes uniformly under `M.erase c1`
  (`classFactorialProd_erase`: erasing one component of type `τ1` divides the product by exactly
  `fiber_τ1(M).card`, proved directly — no auxiliary arithmetic lemma needed, since the accumulator
  is defined type-fiberwise from the start rather than bounded after the fact). This replaces the
  `|M|!` accumulator with `∏_τ(fiber_τ.card)!`, matching the *shape* of the manuscript's
  `∏_τ m_τ!` grouping. **Honest scope note**: `compType` is a *numeric* classifier (attachment
  count, block-size product) — a necessary but not sufficient condition for two components to be
  the manuscript's same *rooted-isomorphism* type, so it can conflate genuinely non-isomorphic
  components that happen to share both numbers. Since merging fiber classes only inflates the
  product (`(n₁+n₂)!≥n₁!·n₂!`), `classFactorialProd` is always `≤ |M|!` but may still exceed the
  manuscript's exact `∏_τ m_τ!` (computed over the finer true-isomorphism-type partition) whenever
  such a numeric coincidence occurs; the two agree whenever the numeric invariant happens to already
  separate all non-isomorphic types present. Reaching the manuscript's literal statement in full
  generality would need the finer classifier (an actual rooted-tree/hypergraph isomorphism
  invariant on each component, not just two integers derived from it) — a further undertaking, not
  attempted here. `hmixed`/`hreach_all` remain supplied as hypotheses rather than derived from the
  manuscript's own block-support-hypergraph connectivity assumption, the same translation gap noted
  for the non-cut-vertex case.
- **`CongruenceTheoryHigherOrder/FreeActionDivides.lean`** — **`card_dvd_of_free`**, **fully proved**: a
  general, reusable fact extracted while investigating the cut-vertex case's multinomial
  divisibility above — if a finite group `G` acts on a finite type `X` *freely*
  (`∀g≠1,∀x,g•x≠x`), then `Fintype.card G ∣ Fintype.card X`. Proof: freeness makes every
  stabilizer trivial, so orbit-stabilizer (`Subgroup.index_mul_card`) gives every orbit exactly
  `Nat.card G` elements; `MulAction.selfEquivSigmaOrbits'` partitions `X` into its orbits, so
  `Fintype.card X` is a sum of terms each equal to `Fintype.card G`, giving the divisibility via
  `Finset.dvd_sum`. This is exactly the principle behind the cut-vertex case's `m_τ!` divisor
  (`∏_τ Equiv.Perm(Fin m_τ)` acts freely on labeled block-assignments, permuting which slot within
  a size-class `τ` holds which content, by permuting disjoint nonempty sets) — the same idea also
  underlies the *unaddressed* "there are `(r-1)!/(d!(h-1)!^d)` possible block partitions" remark in
  `HypertreeEnumerator.lean`'s own manuscript source, which that file sidesteps by staying in
  multiplied-out form. Applying it to `HypertreeEnumerator.lean`'s `OrderedBlocks` (defined
  recursively, not as a flat tuple) would still need an explicit intermediate equivalence to a
  flat-tuple representation — not attempted — but the cut-vertex application below needed no such
  detour, since its own natural representation already *is* a flat tuple.
- **`CongruenceTheoryHigherOrder/DisjointTupleSymmetry.lean`** — **`factorial_dvd_card_disjointTuple`**,
  **fully proved**: the cut-vertex case's `m_τ!` divisibility, as a direct application of
  `card_dvd_of_free`. `DisjointTuple β m a`, the type of `m`-tuples of pairwise-disjoint
  `a`-element subsets of `β`, carries a natural `Equiv.Perm (Fin m)` action (permuting which
  labeled slot holds which block); for `a≥1` this action is **free** — if `σ≠1` then some
  `σ⁻¹ i₀≠i₀`, and since `f (σ⁻¹ i₀)` and `f i₀` are disjoint (by the tuple's own defining
  property) yet `σ•f=f` would force them equal, contradicting nonemptiness (`a≥1`) — so
  `card_dvd_of_free` gives `m!∣Fintype.card(DisjointTuple β m a)` directly. Combined with
  `Nat.multinomial_spec` (an off-the-shelf Mathlib identity handling the
  `(a_0-1)!∏_τ(a_τ!)^{m_τ}` factor exactly, for the labeled-partition count itself), this supplies
  *every* purely-arithmetic ingredient the cut-vertex multinomial fact needs. **Honest scope
  note**: assembling these into the manuscript's literal identity — instantiating `β,m,a` once per
  rooted-isomorphism type `τ` and combining across all `τ` simultaneously (not just one class at a
  time) — plus the graph-component/rooted-isomorphism-type classification that `a_0`, `a_τ`, `m_τ`
  are themselves defined in terms of (components of the incidence graph minus `u`, grouped by
  rooted isomorphism), remains a further substantial undertaking, not attempted here.
- **`CongruenceTheoryHigherOrder/LucasApplication.lean`** — the Lucas'-theorem step that closes (A6)'s
  sharpness argument, **fully proved**, independent of everything else in the manuscript (the
  hypertree enumeration, the moment-cumulant identity, the algebraic-independence argument):
  "since `d∣Q` and `r≡1 (mod d)`, Lucas' theorem gives `p∤C(r(Q-1),d-1)`" for `d=p^s`.
  **`not_dvd_choose_pow_sub_one_of_mod_eq`**: the general shape — if `n≡p^s-1(mod p^s)` then
  `p∤C(n,p^s-1)`, since `k=p^s-1`'s base-`p` digits are all maxed at `p-1`, `n`'s matching bottom
  `s` digits are too, and Lucas' theorem's digit-wise product is then `C(p-1,p-1)=1` throughout
  (proved by induction on `s`, peeling one digit at a time via Mathlib's
  `Choose.choose_modEq_choose_mod_mul_choose_div_nat` from `Mathlib.Data.Nat.Choose.Lucas`).
  **`not_dvd_choose_of_dvd_and_modEq`**: the manuscript's exact statement, reducing to the above
  via `r(Q-1)=(p^s-1)+p^s·(m(Q-1)+(Q'-1))` where `r=p^s·m+1`, `Q=p^s·Q'` (i.e. `r≡1,Q≡0 (mod p^s)`
  force `r(Q-1)=rQ-r≡0-1≡p^s-1 (mod p^s)`).
- **`CongruenceTheoryHigherOrder/FallingFactorialVandermonde.lean`** — **`descFactorial_add_eq`**, **fully
  proved**: the binary case of (A6)'s own named ingredient, "the multivariate falling-factorial
  Vandermonde identity" (used together with `hypertree_enumerator`'s Prüfer sum to evaluate
  `A_h` in closed form) — `(m+n)_k=Σ_{i+j=k}C(k,i)·(m)_i·(n)_j` for `Nat.descFactorial`. Derived
  directly from Mathlib's ordinary-binomial Vandermonde identity (`Nat.add_choose_eq`) one level
  up the descFactorial/choose correspondence (`Nat.descFactorial_eq_factorial_mul_choose`,
  `n.descFactorial k=k!·n.choose k`): multiply `Nat.add_choose_eq` through by `k!`, then split
  `k!` back into `C(k,i)·i!·j!` per term via `Nat.choose_mul_factorial_mul_factorial`.
- **`CongruenceTheoryHigherOrder/FallingFactorialVandermondeMultivariate.lean`** — **`descFactorial_sum_eq`**,
  **fully proved**: the full `r`-ary (multinomial-weighted) generalization —
  `(Σ_{i∈s}y_i)_n = Σ_{c∈s.piAntidiag n} multinomial(s,c)·∏_{i∈s}(y_i)_{c_i}` — matching the
  manuscript's own "multivariate falling-factorial Vandermonde identity" exactly, for an arbitrary
  finite index set `s`. Proved by induction on `s`, peeling one index at a time via Mathlib's
  `Finset.piAntidiag_insert` (the insert-recursion for "functions summing to `n`", found after
  `Finset.Nat.antidiagonalTuple`'s own `Fin`-indexed API turned out to have no ready-made
  insert/cons recursion lemma) and `Nat.multinomial_insert`, reducing each inductive step to
  exactly the binary case above via a `calc`-free rewrite chain (pairwise-disjointness of the
  `piAntidiag_insert` decomposition's pieces proved directly by a short pointwise argument, rather
  than reusing Mathlib's internal `addRightEmbedding`-based disjointness fact, whose exact
  definition site could not be located). **Honest scope note**: this closes the identity itself in
  full generality, but the manuscript's actual application to `hypertree_enumerator`'s *power*-sum
  identity is not a direct substitution — the manuscript's step reinterprets the same Prüfer-recipe
  combinatorics under an added distinctness constraint (choosing microblocks *without* repetition)
  rather than substituting into the existing polynomial identity — so connecting the two to
  complete (A6)'s closed-form evaluation of `A_h` remains a further undertaking, not attempted
  here.
- **`CongruenceTheoryHigherOrder/FullCycleConnected.lean`** — **`piOf_eq_top_of_isCycle_of_support_eq_univ`**,
  **fully proved**: a full-support cycle's macroblock connectivity partition is automatically `⊤`
  — the first building block toward (A3)'s combinatorial claim ("the coefficient of `X_{jp}` in
  `K_j(p)` is `(jp-1)!`," needed to connect the already-proven Legendre's-formula identity
  `LegendreA3.lean` to the actual `K` polynomial via `K_eq_Gfun_top`/`Gfun`/`ci`
  from `ConnectedCount.lean`, since `ci g` is always a single monomial, so the coefficient of
  `X_{jp}` in `Gfun ⊤` counts exactly the `g` with `piOf g = ⊤` *and* `ci g = X_{jp}`, i.e. a full
  `jp`-cycle — and this file shows the `piOf g = ⊤` half of that conjunction is automatic, so it
  drops out). Proved via `IsCycle.exists_pow_eq` (every two moved points are reachable by some
  natural-number power) combined with a step-by-step `graphOf g`-reachability induction on that
  power, then converted into `piOf g = ⊤` through the refinement order `Finpartition.≤` directly
  (`⊤ ≤ piOf g` since *any* part of `⊤` is `⊆ Finset.univ = (piOf g).part x₀` for a fixed moved
  point `x₀`), avoiding needing to characterize `⊤`'s own `.parts`/`.part` explicitly.
- **`CongruenceTheoryHigherOrder/CiFullCycle.lean`** — **`ci_eq_X_of_isCycle_of_support_eq_univ`**, **fully
  proved**: the companion fact — a full-support cycle's cycle-indicator monomial `ci g` is exactly
  the bare `X_{rq}` (no `X_1` factor, since `IsCycle.cycleType` gives `g.cycleType={r*q}` directly
  from `g.support=univ`, so `ci`'s `X_1`-exponent `card-cycleType.sum` vanishes and the cycle-length
  product collapses to the single factor `X (r*q)`). Combined with `FullCycleConnected.lean`, every
  full `rq`-cycle contributes to `Gfun ⊤`'s defining sum with exactly the monomial `X (r*q)` and
  satisfies the `piOf g=⊤` membership condition, matching two of the three ingredients (A3)'s
  combinatorial claim needs.
- **`CongruenceTheoryHigherOrder/CiConverse.lean`** — **`isCycle_and_support_eq_univ_of_ci_eq_X`**, **fully
  proved**: the converse — `ci g = X n` (`n≥2`) forces `g` to be a full `n`-cycle. Built on
  **`multiset_map_X_prod_eq_monomial`** (also here): `(m.map X).prod = monomial m.toFinsupp 1` for
  any multiset `m`, proved by `Multiset.induction_on` via `Multiset.toFinsupp_add`/
  `_singleton` and `X n = monomial (single n 1) 1` (`X`'s own definition). Applied to `ci g`'s own
  `X_1^e * (cycleType.map X).prod` form, `ci g = X n` becomes a single `Finsupp` equation
  (`monomial_eq_monomial_iff`); evaluating it at index `1` (using `1∉cycleType`, since cycle
  lengths are `≥2`) forces `e=0`, then `Multiset.toFinsupp`'s injectivity (an `AddEquiv`) forces
  `g.cycleType={n}` outright, giving `IsCycle` (`card_cycleType_eq_one`) and `support=univ` (via
  `sum_cycleType`/`sum_cycleType_le` pinning `Fintype.card=n`) together. **Honest note on this
  file's own history**: the *identical* proof failed to compile for over 30 minutes on a first
  attempt earlier in this effort — traced to transient system load (confirmed by a plain
  `import Mathlib` file with no proof content taking comparably long at the time), not a defect in
  the mathematics; a session restart resolved it and the exact same proof compiled in under a
  minute.
- **`CongruenceTheoryHigherOrder/FullCycleCount.lean`** — **`card_fullCycle`**, **fully proved**: the count of
  full `(m+1)`-cycles is `m!` — the classical "cyclic permutations of `n` points number `(n-1)!`"
  fact, built entirely from `CpermEqC.lean`'s existing `CycleTuple`/`cyc_injective`/
  `card_CycleTuple`/`exists_decomp_pos` machinery (constructed there for the unrelated `Cperm_eq_C`
  bridge). The bijection `CycleTuple m m ≃ {full (m+1)-cycles}`: injectivity is `cyc_injective`
  directly; surjectivity uses `exists_decomp_pos` at `r=m` (the "cycle through `0`" already covers
  the whole domain when `r=m`, forcing the complement `CycleCompl m m t` to be empty for every `t`
  — provable via `Fintype.bijective_iff_injective_and_card`, since `t:Fin m↪NZ m` is an embedding
  between equal-cardinality types — so `Equiv.Perm.ofSubtype` of the (unique, trivial) complement
  permutation is `1`, collapsing `gAssemble` to `cyc` exactly).
- **(A3), fully closed** — **`CongruenceTheoryHigherOrder/A3Final.lean`**, **`A3_coeff_eq_factorial`**,
  **fully proved**, `#print axioms`-checked standard: "the coefficient of `X_{jp}` in `K_j(p)` is
  `(jp-1)!`," the manuscript's own literal claim, assembled from every ingredient above.
  `ci_eq_monomial_toFinsupp`/`coeff_X_ci_eq_ite` show `ci g`'s coefficient at `X n` is the
  indicator of `ci g = X n` exactly (not just `≤1`), turning `Gfun ⊤`'s coefficient into a literal
  `Finset.sum_boole` count via `Finset.sum_congr` + the forward/converse pair above; the
  `piOf g=⊤` filter is shown to drop out entirely (any full cycle already satisfies it, via
  `FullCycleConnected.lean`). The remaining gap — `card_fullCycle` being stated for `Fin (m+1)`
  while `Gfun`'s sum runs over `Equiv.Perm (Fin r × Fin q)` — is closed by a genuine
  `Fin r × Fin q ≃ Fin (r*q)` transport (`finProdFinEquiv`) proved from scratch:
  `support_permCongr`, `permCongr_zpow`/`permCongr_zpow_apply` (via the bundled `MulEquiv`
  `Equiv.permCongrHom`, giving `map_zpow` for free), `sameCycle_permCongr_iff`,
  `isCycle_permCongr_iff`, and `permCongr_symm_permCongr` (round-trip cancellation, via
  `permCongrHom.symm = symm.permCongrHom` combined with generic `MulEquiv.symm_apply_apply` —
  avoiding ever unfolding `finProdFinEquiv`'s own div/mod definition) — none of which existed
  ready-made in Mathlib for cross-type permutation conjugation. **Precise scope note**: this
  proves the manuscript's own sentence *verbatim* — "the coefficient of `X_{jp}` in `K_j(p)` is
  `(jp-1)!`" — as a literal, `#print axioms`-checked-standard `Nat.factorial` equation, not a
  corollary weaker than what's stated. It is the first result in this codebase proved to exactly
  match a manuscript sentence end-to-end rather than a supporting lemma or a weaker bound. It is
  *not*, however, the tagged equation `(A3)` itself (`v_p(\operatorname{cont}K_j(p))=e_p(j)`,
  combining this coefficient fact with `LegendreA3.lean`'s Legendre's-formula identity): that
  needs the further fact that *no other coefficient* of `K_j(p)` has smaller `p`-adic valuation
  (the manuscript's "no term belonging to a proper partition... can contain a cycle meeting all
  `jp` labels"), i.e. that this one coefficient realizes `K_j(p)`'s content — a claim about every
  *other* term of the polynomial, not attempted here.
- **(A4) infrastructure — nine files, `GeneralizedConnectivity.lean` through
  `GeneralizedGfunProd.lean`** — the moment-cumulant microblock-refinement identity
  `K_r(q)=Σ_λ A^{\rm conn}_λ(Q;r)C_p^{m_1}∏_{j≥2}K_j(p)^{m_j}`. **The abstract mechanism is now
  fully proved**: **`genGfun_eq_prod_K`** — for *any* finite macroblock index type `ι` (not just
  `Fin r`) and *any* partition `τ` of `ι` (not just `⊤`), the sum of `ci g` over permutations
  whose connectivity partition is exactly `τ` factors as `∏_{B∈τ.parts} K |B| q` — i.e. "connected
  structures on a union of blocks factor as a product of one connected structure per block," the
  precise two-level generalization `K_eq_Gfun_top`'s single-level Möbius inversion needs.
  `#print axioms`-checked standard throughout. Built by:
  **`GeneralizedConnectivity.lean`** (`GenPartLat`/`genTouches`/`genPiOf`/`GenGfun`/`GenFfun`,
  a near-verbatim generalization of `ConnectedCount.lean` from `Fin r` to arbitrary `ι`) and
  **`GeneralizedPartitionGluing.lean`** (likewise generalizing `PartitionGluing.lean`/
  `PartitionRespects.lean`'s `assemble`/`restrictP`/`assembleEquiv` bijection) — both mechanical,
  compiling clean on the first attempt. On top of these, four genuinely new pieces, none of which
  had a ready-made Mathlib analogue: **`GeneralizedConnectivityTransport.lean`**
  (`genTouches_permCongr`/`genGraphOf_reachable_permCongr_iff`: connectivity transports along any
  index-relabeling `Equiv`, via the bundled `MulEquiv` `Equiv.permCongrHom`) and
  **`GeneralizedConnectivityTop.lean`** (`genPiOf_eq_top_iff`: `π(g)=⊤` iff `g`'s graph is fully
  reachable, proved via `Finpartition.parts_top_subset` rather than characterizing `⊤`'s own
  `.part` directly, which has no simp-normal form under the library's `Decidable(s=⊥)`-conditional
  `⊤` instance). The crux, **`GeneralizedAssembleTop.lean`**
  (`genTouches_assemble_iff`: for a permutation respecting a partition `τ`, *global* touches
  restricted to one block matches that block's *own* local touches exactly — via
  `genBlockTypeEquiv`'s explicit component formulas, since `Equiv.prodSubtypeFstEquivSubtypeProd`
  carries no `@[simps]` lemmas) and **`GeneralizedPiOfAssemble.lean`**
  (`genPiOf_assemble_eq_tau_iff`: the assembled permutation's connectivity is *exactly* `τ` iff
  *every* block is individually fully connected — the reverse direction needed proving reachable
  points never leave their own block, via an auxiliary lemma with a genuinely free endpoint
  variable, to sidestep Lean's "index in target's type is not a variable" restriction on inducting
  over a `ReflTransGen` whose target is already a fixed `Subtype`-coerced term). Finally
  **`GeneralizedGfunTopK.lean`** identifies `GenGfun(⊤)` at any `ι` with `K (Fintype.card ι) q`
  (transporting to `Fin (card ι)` via `Fintype.equivFin`, where `GenGfun`/`Gfun` are *definitionally*
  identical, `rfl`), and **`GeneralizedGfunProd.lean`** assembles everything into
  `genGfun_eq_prod_K` itself. **Honest scope note**: this is the *abstract* mechanism — applying it
  concretely to the manuscript's own setup (relabeling `Fin r × Fin q` as macroblocks/microblocks
  with `q=Qp`, invoking `genGfun_eq_prod_K` at the microblock level `ι:=Fin r × Fin Q` block size
  `p`, adding the side constraint that the induced *macroblock* connectivity is `⊤` via a further
  partition-projection argument relating microblock partitions to their coarsening, and finally
  regrouping the resulting sum over microblock partitions by partition *shape* into the
  manuscript's `A^{\rm conn}_λ(Q;r)` form, reusing the `compType`/`classFactorialProd`-style
  type-classifier construction from the (A2a) cut-vertex work) — remains a further, substantial
  assembly step. **`CongruenceTheoryHigherOrder/MacroMicroRelabel.lean`** takes the first step, **fully
  proved**: `macroMicroEquiv r Q p : Fin r × Fin (Q*p) ≃ (Fin r × Fin Q) × Fin p` (the `q=Qp`
  relabeling, macroblock component held fixed — `macroMicroEquiv_fst` is `rfl`) and
  **`genTouches_macro_iff_micro`**: a macroblock permutation's touches relation is exactly the
  microblock-relabeled permutation's touches relation, coarsened by macroblock-projection —
  `genTouches g i j ↔ ∃y:(Fin r×Fin Q)×Fin p, y.1.1=i ∧ ((macroMicroEquiv r Q p).permCongr g
  y).1.1=j`. **Honest scope note**: reaching macroblock `⊤`-connectivity as a condition on the
  *microblock partition* `τ' := π'(g')` itself is more subtle than it first looks. It is *not*
  "some fixed lift pair of `i,j` is micro-reachable (same `τ'`-part)" — two macro-adjacent steps
  in a macro walk from `i` to `j` may be witnessed by *different* microblocks of the same
  intermediate macroblock, so no single `τ'`-part need touch both `i` and `j`. The correct
  condition (matching the manuscript's own "induced support hypergraph on the macroblocks is
  connected") is: build a graph `H` on `Fin r` with `i ∼ j` iff *some* part of `τ'` contains a
  microblock of `i` and a microblock of `j` (a hyperedge touching both), then check `H` is
  connected — exactly `ConnectedCount.lean`'s own `touches`/`graphOf`/`piOf` recipe, but applied
  to a *partition*'s parts rather than a permutation's cycles directly. **`MacroMicroReach.lean`**
  proves the *easier* half needed to connect this to `genPiOf`: **`genTouches_macro_iff_micro'`**
  restates the touches correspondence at microblock-*index* level (`∃mb1 mb2:Fin r×Fin Q,
  mb1.1=i∧mb2.1=j∧` microblock-touches), and **`genGraphOf_reachable_macro_of_micro_adj`** lifts
  it to reachability: microblock reachability implies macroblock reachability of the projected
  endpoints (a microblock walk projects to a macroblock walk, collapsing steps that stay within
  one macroblock) — proved by induction on `ReflTransGen`, case-splitting on whether consecutive
  microblock endpoints share a macroblock. **`CongruenceTheoryHigherOrder/PartGraph.lean`** closes the
  hypergraph characterization itself, **fully proved, zero `sorry`**: **`partTouches τ' i j`**
  (`∃C∈τ'.parts, (∃mb∈C,mb.1=i)∧(∃mb∈C,mb.1=j)`, i.e. some `τ'`-part contains a microblock of
  each) and **`partGraphOf τ' := SimpleGraph.fromRel (partTouches τ')`** — the induced hypergraph
  `H` on macroblocks `Fin r`. The *easier* direction, **`genGraphOf_reachable_of_partTouches`**:
  a `τ'`-part touching `i` and `j` forces macroblock reachability (via same-part membership giving
  micro-reachability, then `genGraphOf_reachable_macro_of_micro_adj`). The *harder* converse
  direction, **`partGraphOf_reachable_of_genGraphOf_reachable`**: a macro-adjacent step is
  witnessed by a micro-*adjacent* — hence a fortiori micro-*reachable* — lift pair, which
  therefore lies in a common `τ'`-part; the key internal lemma `hmk` handles the case where the
  two microblock lifts coincide (trivial, via `mem_part_self`) separately from the case where they
  differ (via an explicit `Adj` witness), since the *outer* induction's endpoint-inequality fact
  cannot be reused inside the *generically*-quantified helper — an early draft conflated the two
  and was caught and corrected before formalizing further. Both directions combine, by induction on
  `ReflTransGen` in each direction, into the headline
  **`genPiOf_macro_eq_top_iff_partGraphOf_connected`**:
  `genPiOf g = ⊤ ↔ ∀i j:Fin r, (partGraphOf (genPiOf ((macroMicroEquiv r Q p).permCongr
  g))).Reachable i j` — macroblock `⊤`-connectivity of `g` matches `H`'s connectivity exactly,
  confirmed via `#print axioms` to depend only on `[propext, Classical.choice, Quot.sound]`. This
  is precisely the manuscript's own "induced support hypergraph on the macroblocks is connected"
  condition. **`CongruenceTheoryHigherOrder/GeneralizedGfunFilter.lean`** provides the generic regrouping
  step this needs, **fully proved**: for any decidable predicate `C` on `GenPartLat ι`,
  **`sum_ci_filter_genPiOf_eq_sum_filter_genGfun`** shows filtering a `ci`-sum over
  `Perm(ι×Fin q)` by `C∘genPiOf` regroups into a sum of `GenGfun τ'` over the (finitely many)
  `τ'` satisfying `C` — a `Finset.sum_fiberwise_of_maps_to` application, the fiber for each `τ'`
  matching `GenGfun`'s own filter-sum definition exactly once `C τ'` is known to hold. Combined
  with `genGfun_eq_prod_K`, **`sum_ci_filter_genPiOf_eq_sum_filter_prod_K`** rewrites each fiber
  as a block-product of `K`'s. **`CongruenceTheoryHigherOrder/MacroMicroSum.lean`** assembles this with
  `PartGraph.lean`'s hypergraph characterization and `MacroMicroRelabel.lean`'s `q=Qp` relabeling
  into **the core content of (A4)'s manuscript equation**,
  **`K_eq_sum_filter_partGraphOf_connected_prod_K`**:
  `K r (Q*p) = ∑_{τ'∈univ.filter(fun τ'⇒∀i j,(partGraphOf τ').Reachable i j)} ∏_{B∈τ'.parts}
  K(|B|,p)` — `#print axioms`-checked standard. Proof: `K r (Q*p) = GenGfun(⊤:GenPartLat(Fin r))`
  (via `genGfun_top_eq_K`, `Fintype.card_fin`), unfolded to a `ci`-sum over
  `Perm(Fin r×Fin(Qp))`, reindexed along `(macroMicroEquiv r Q p).permCongr` (an `Equiv.sum_comp`
  application, with `ci_permCongr` carrying the summand and
  `genPiOf_macro_eq_top_iff_partGraphOf_connected` carrying the filtering condition across the
  relabeling pointwise), landing exactly on
  `sum_ci_filter_genPiOf_eq_sum_filter_prod_K`'s hypotheses. **`CongruenceTheoryHigherOrder/PartitionShape.lean`**
  supplies the generic final regrouping mechanism, **fully proved**: **`GenPartLatShape τ' :=
  τ'.parts.val.map Finset.card`** (the multiset of block sizes), **`prod_K_eq_shape_prod`**
  observes `∏_{B∈τ'.parts} K(|B|,q)` depends on `τ'` only through this shape (`Multiset.map_map`
  unfolding `Finset.prod`), **`shapeCount S lam := (S.filter (GenPartLatShape·=lam)).card`**, and
  **`sum_prod_K_eq_sum_shapeCount`** regroups any `Finset`-filtered sum of block-products by shape
  (the same `Finset.sum_fiberwise_of_maps_to` recipe as `GeneralizedGfunFilter.lean`, applied to
  the shape map instead of `genPiOf`). **`CongruenceTheoryHigherOrder/MacroMicroShape.lean`** combines this
  with `K_eq_sum_filter_partGraphOf_connected_prod_K`, defining **`connSet r Q`** (the
  macro-connected microblock partitions) and proving the headline
  **`K_eq_sum_shapeCount_prod_K`**:
  `K r (Qp) = ∑_{λ∈(connSet r Q).image GenPartLatShape} (shapeCount (connSet r Q) λ) •
  (λ.map (K·p)).prod` — `#print axioms`-checked standard, and the closest this project comes to
  the manuscript's literal `K_r(Qp)=Σ_λ A^{\rm conn}_λ(Q;r)C_p^{m_1}∏_{j≥2}K_j(p)^{m_j}`.
  **`CongruenceTheoryHigherOrder/ShapeCpSplit.lean`** makes the manuscript's `C_p^{m_1}` split an actual
  proven corollary rather than a prose observation, **fully proved**: `ConnectedCumulant.lean`'s
  `K_one : K 1 q = C q` means wherever `λ` contains a `1`, the shape-product's corresponding
  factor already *is* `C p` literally — **`shape_prod_eq_Cp_pow_mul_prod`** makes this explicit
  by induction on `λ` (`Multiset.count_cons`/`filter_cons` case-splitting on whether the head is
  `1`), giving `(λ.map (K·p)).prod = (C p)^{λ.count 1} · ((λ.filter (·≠1)).map (K·p)).prod`.
  Composed with `K_eq_sum_shapeCount_prod_K`, **`K_eq_sum_shapeCount_Cp_pow_mul_prod`** is the
  manuscript's written form verbatim, `#print axioms`-checked standard. **Honest scope note**:
  `shapeCount (connSet r Q) λ` — "the number of macro-connected microblock partitions with
  block-size multiset `λ`" — is the natural reading of the manuscript's `A^{\rm conn}_λ(Q;r)`,
  but this project does not independently verify the correspondence against the manuscript's own
  definition of that enumerator (not directly accessible in this session); what genuinely remains
  unverified is only whether `shapeCount`'s *counting* convention (raw cardinality of
  macro-connected microblock partitions of a given shape) matches how the manuscript itself
  defines/normalizes `A^{\rm conn}_λ(Q;r)` —
  not attempted here.
- **`CongruenceTheoryHigherOrder/PochhammerValuation.lean`** — the numeric ingredient (A2) needs beyond
  (A2a), **fully proved**: closing `(r-2)!q^r/\mathrm{rad}(q)∣K_r(q)` reduces (via (A2a)'s
  two-root lemma applied to the kernel/image of a centralizer restricted to the mixed part) to
  "using `v_p((q)_R)≥t+v_p((R-1)!)` gives `v_p(|H̃:C_H̃(σ)|)≥rt-1+v_p((r-2)!)`" — and the
  falling-factorial valuation bound itself, **`factorization_descFactorial_ge`**:
  `v_p(q)+v_p((R-1)!)≤v_p((q)_R)` for `1≤R≤q` (`(q)_R=q.descFactorial R`), is a self-contained
  number-theoretic fact independent of everything else in the argument. Proof: `q.descFactorial R
  = q·(q-1).descFactorial(R-1)` (Mathlib's `Nat.succ_descFactorial_succ`), and `(R-1)!∣
  (q-1).descFactorial(R-1)` (any descending factorial is a multiple of the matching ordinary
  factorial, via `Nat.descFactorial_eq_factorial_mul_choose`), so `q·(R-1)!` divides `(q)_R`,
  giving the valuation inequality directly via `Nat.factorization_le_factorization_of_dvd_right`.
  **`A2_valuation_bound`** completes the arithmetic, **also fully proved**: given `r` blocks with
  `1≤R_i≤q`, `v_p(H)=r·v_p(q!)+v_p((r-2)!)` (for `H=S_q^r⋊S_{r-2}`), and the manuscript's own
  group-theoretic embedding fact `v_p(C)≤Σ_i v_p((q-R_i)!)+1+Σ_i v_p((R_i-1)!)` taken as a
  hypothesis (not re-derived), it derives `v_p(H)+1≥r·v_p(q)+v_p((r-2)!)+v_p(C)` — the
  manuscript's `v_p(|H:C|)≥rt-1+v_p((r-2)!)` exactly, in addition form to avoid `Nat` subtraction.
  Proof: `factorization_descFactorial_ge` plus `Nat.factorial_mul_descFactorial` give, per block,
  `v_p(q)+v_p((R_i-1)!)+v_p((q-R_i)!)≤v_p(q!)`; summing over all `r` blocks and combining with the
  hypothesis on `v_p(C)` telescopes the `v_p((R_i-1)!)` and `v_p((q-R_i)!)` sums away entirely,
  leaving exactly the stated bound. **Honest scope note**: the group-theoretic embedding fact
  itself (`hCbound`) — let alone the surrounding centralizer-restriction argument that produces
  it — is not derived here, only used; what's proved is that the numeric bookkeeping from there
  to the final valuation bound is correct.

- **`CongruenceTheoryHigherOrder/LegendreA3.lean`** — the Legendre's-formula identity from (A3)'s sharpness
  argument, **fully proved**: `v_p((jp-1)!)=(j-1)+v_p((j-1)!)`, i.e. `e_p(j)=v_p((jp-1)!)` for
  `e_p(j):=j-1+v_p((j-1)!)` as the manuscript defines it. A self-contained number-theoretic fact,
  independent of the combinatorial claim about `K_j(p)`'s coefficient of `X_{jp}` that (A3) also
  needs (which would need this project's `K_r(q)` machinery from `ConnectedCumulant.lean` and is
  not addressed here). Proof (**`factorization_factorial_mul_sub_one`**): Mathlib's
  `Nat.Choose.Factorization.factorization_factorial_mul` gives `v_p((jp)!)=v_p(j!)+j`; splitting
  `(jp)!=(jp)·(jp-1)!` and `j!=j·(j-1)!` via `Nat.factorial_succ`, and using
  `v_p(jp)=v_p(j)+v_p(p)=v_p(j)+1` (`p` prime), the `v_p(j)` terms cancel, leaving exactly the
  stated identity. **Honest scope note**: the numeric identity only, not the rest of (A3)'s
  argument.

- **`CongruenceTheoryHigherOrder/LcmCombination.lean`** — the `(A1)`/`(A2)`-combination step closing the
  lower-bound half of `thm:atomic-connected-content`, **fully proved**: "the least common multiple
  of (A1) and (A2) has the exponent stated in the theorem." A self-contained arithmetic fact,
  independent of `K_r(q)`, `(A1)`, and `(A2)` themselves. **`atomic_connected_content_lower_bound`**:
  for `r≥2`, `t≥1`, and `F1=c+F2` (the case of interest: `c=v_p(r-1)`, `F1=v_p((r-1)!)`,
  `F2=v_p((r-2)!)`), `max((r-1)t+F1,rt-1+F2)=rt-1+F1-min(t-1,c)` — exactly the theorem's boxed
  `v_p(\mathrm{cont}K_r(q))=rt-1+v_p((r-1)!)-\min\{t-1,v_p(r-1)\}` as a lower bound (matching it
  with the upper bound from sharpness, (A3)–(A6), is not addressed here). Proof: case on
  `t-1≤c` vs. `c<t-1`; in each case `r*t=(r-1)*t+t` identifies which side is the max, and `omega`
  closes the resulting linear arithmetic. Depends only on `[propext, Quot.sound]` — no
  `Classical.choice` needed, being pure constructive `Nat` arithmetic.

Run `lake build` (`.lake/packages` here is a copy-on-write clone of
`../../vibemath/lean-verify/.lake`, same toolchain `v4.31.0` and Mathlib
pin, so no re-fetch is needed) to typecheck everything — 15442 lines across
125 files, zero `sorry` (figures as of `A2aHreachAll.lean`; grows as work continues).


## Remaining scope (not attempted)

The manuscript has roughly 50 labeled theorems/corollaries total.
**`prop:content-bounds`** and **`thm:optimal-divisor`** are now complete,
single, unified theorems for the abstract `C` (`OptimalDivisorC.lean`,
above) — no longer split across two representations. **`thm:tree-modulus`**
is also done, in the per-witness-tree form described above
(`TreeModulus.lean`), and **`thm:allocation-formula`** in the
coefficient-counting form described above (`AllocationFormula.lean`).

Also complete: **`prop:support`** and **`prop:finitewidth`**
(`SupportTheorem.lean`, `FiniteWidth.lean`, above) — this closes out
essentially everything reasonably reachable from the manuscript's
"Specializations and sequence applications" section (`sec:sequences`).

Beyond that, three tiers remain, in increasing order of difficulty. Note
**`thm:BO`** (Bellagh–Oulebsir, specialized) is explicitly *literature-derived*
in the manuscript itself ("not claimed here as new") — it specializes an
external paper's Proposition 1.1(3), which isn't proved in this manuscript
either, so formalizing it here would mean either reproving that external
result from scratch or taking it as an axiom; neither fits this project's
zero-paper-specific-axiom standard, so it's excluded from scope entirely
rather than "remaining."

The entire Euler/Gauss chapter (`sec:euler`) is now complete: `thm:gauss`
(`GaussCongruence.lean`), **`thm:euler-product`** (`EulerProductTheorem.lean`),
and **`thm:euler-integrality`**, all three clauses (`EulerIntegrality.lean`).

The canonical-coordinates chapter (`sec:principle`) is now also complete.
`log(AB)=log A+log B` and the full `log`/`exp` bijection
(`PowerSeriesLog.lean`: `logOf_mul`, `logOf_exp`, `exp_logOf`) cover
`thm:canonical-classification`'s bijection itself.
`thm:multiplicative-functoriality` (all three clauses: `u_m(AB)=u_m(A)+u_m(B)`,
`u_m(A^{-1})=-u_m(A)`, `u_m(A^q)=q\,u_m(A)`), **`thm:base-change`** (all
three clauses, `BaseChange.lean`), **`thm:general-defect`** (main identity
plus both parts (i) and (ii), `EGFCoordinates.lean`), **`thm:local-locus`**
(clauses (i)/(ii) unified via a single `IsKLocal` definition,
`LocalLocus.lean`), **`prop:no-all-egf-shift`** (`NoAllEgfShift.lean`), and
**`cor:general-twoadic-defect`** (`GeneralTwoAdicDefect.lean`, in the
`Cperm`/`CpermSum` form `thm:strong` actually proves here, not restated for
the abstract `C` the manuscript states it for — the `Cperm=C` bridge
(`CpermEqC.lean`) now exists and could be used to transfer this to `C`
directly, but that transfer hasn't been done, so this remains the
permutation-native analogue rather than a literal transcription of the
manuscript's statement) are all done.
- **Hard**: the higher-order/hypertree chapter (`thm:tree-modulus`,
  `thm:allocation-formula`) is now done, up to two matching, honestly
  documented gaps (both above): `thm:tree-modulus` in the per-witness-tree
  form (`TreeFor.mu_dvd_defect`, `TreeModulus.lean`) rather than packaged as
  the single lcm `M(n)`, and `thm:allocation-formula` in the
  coefficient-counting form (`coeff_listProdC_eq_card`,
  `AllocationFormula.lean`) rather than evaluated into the closed
  `∑_QW(Q)` sum. Both remaining gaps are the *same kind* of step — a
  `Fintype`/enumeration of a further combinatorial index (tree shapes with a
  given leaf sequence; matrices `Q`/individual cycle-type partitions of
  `λ`) — not carried out since it isn't needed for either theorem's
  mathematical content, only for matching the manuscript's literal
  closed-form packaging.
- **Hardest, and highest assurance value**: the atomic connected-cumulant
  chapter (`thm:atomic-connected-content` through
  `thm:one-singleton-repeated`, ~15 results) — this is where the
  manuscript's one *actual, previously-found-and-repaired* proof gap lived.
  Needs wreath-product and hypertree (Prüfer-bijection) combinatorics with
  essentially no existing Mathlib support for the deep content; comparable
  in scope to the entire `thm:strong` effort above, for one theorem cluster.
  **Foundational setup is done** (`CongruenceTheoryHigherOrder/ConnectedCumulant.lean`,
  above): the chapter's own starting definition
  `K_r(q)=∑_{π∈Π_r}μ(π,1̂)∏_{B∈π}C_{|B|q}` turned out to need *no new
  infrastructure* — Mathlib's `Finpartition` already gives the partition
  lattice `Π_r` (as `PartLat r`, with the `PartialOrder`/`OrderTop`/`Fintype`
  instances the definition needs) and `IncidenceAlgebra.mu` already gives the
  Möbius function of any locally finite order, so `K` combines the two
  directly. `K_one : K 1 q = C q` checks the manuscript's own stated base
  case. **`lem:uniform-hypertree-enumerator` is now also done**
  (`CongruenceTheoryHigherOrder/HypertreeEnumerator.lean`, above) — the
  "Uniform-hypertree Prüfer enumerator", built from scratch with no
  existing Mathlib scaffolding (not even for ordinary, non-hyper tree
  enumeration), via the same honest-reformulation pattern as `TreeFor` and
  `PermTuple`: hypertrees are defined directly by their own Prüfer-recipe
  data (`HyperTreeData`, `OrderedBlocks`) rather than through general
  hypergraph connectivity/acyclicity axioms. What's *still not* done is the
  actual remaining content beyond that: relating this enumerator identity to
  `K_r(q)`'s own cycle-index coefficients, and the wreath-product
  centralizer computations further into the chapter — the genuinely hard,
  novel combinatorics this tier was always expected to need.
  **The manuscript's own supporting remark is now fully proved**
  (`CongruenceTheoryHigherOrder/PartitionGluing.lean`, `PartitionRespects.lean`,
  `ConnectedCount.lean`, below): "coefficientwise, `K_r(q)` counts
  permutations whose cycle-support hypergraph on `r` prescribed blocks of
  size `q` is connected" is now the theorem `K_eq_Gfun_top`,
  `K_r(q)=∑_{g:π(g)=⊤}ci(g)`, built via a permutation-native realization of
  `K_r(q)`'s defining product (`assemble`/`ci_assemble`, generalizing the
  `Cperm=C` bridge's `ci_sumCongr` from binary gluing to an arbitrary
  partition), a bijection onto exactly the `τ`-respecting permutations
  (`assembleEquiv`), a canonical cycle-support connectivity partition
  `π(g)` for every permutation (`piOf`, via Mathlib's
  `SimpleGraph`/`Finpartition.ofSetoid`) with `Respects τ g↔π(g)≤τ`
  (`respects_iff_piOf_le`), and a genuine coefficientwise Möbius-inversion
  argument (Mathlib's `IncidenceAlgebra.moebius_inversion_bot`). What
  remains entirely open is `thm:atomic-connected-content` as a whole, but **inequality (A1) is
  now fully proved** (`CongruenceTheoryHigherOrder/WreathProduct.lean`, `Semiregularity.lean`,
  `ConjugationInvariance.lean`, `StabilizerBound.lean`, `OrbitCounting.lean`,
  `InequalityA1.lean`, below): the wreath product `(ℤ/q)^r⋊S_r`, built from scratch as a genuine
  subgroup of `Equiv.Perm(Fin r×Fin q)` since Mathlib's only wreath product uses the wrong action
  for this purpose; conjugation by a wreath element preserving connectedness; the manuscript's own
  semiregularity argument, proved exactly as stated; the stabilizer-order and orbit-size
  divisibility this implies; and, finally, identifying the orbit with a literal
  `MvPolynomial.coeff` of `K_r(q)` via a from-scratch fiber-counting orbit-stabilizer argument, a
  generalized coefficient-extraction lemma, and a union-of-orbits summation — giving
  `coeff_K_dvd`, the manuscript's own `(r-1)!q^{r-1}∣K_r(q)` as a fully verified theorem, at the
  level of every coefficient (inequality (A1), fully proved). `thm:atomic-connected-content` as a
  whole remains open, though substantial further pieces are now done too: **(A2a)'s "`u` not a cut
  vertex" case is now completely formalized** (`SpanningTreeLeaf.lean`,
  `CentralizerCycleFaithful.lean`, `A2aOrbitBound.lean`, `A2aLayerInduction.lean`,
  `A2aFullInduction.lean`, `A2aRootBound.lean`), giving the manuscript's exact literal
  `|A|≤R_u∏_{i≠u}(R_i-1)!` (`card_le_root_bound`) via a general-depth well-founded induction
  (`key_induction`/`key_induction_rooted`), given a connectivity hypothesis on the block-support
  hypergraph and an initial edge from the chosen root point. **The "`u` is a cut vertex" case now
  has a complete, fully proved, end-to-end bound** (`A2aCutVertexComponents.lean` through
  `A2aCutVertexFullBound.lean`, ~26 files — see the dedicated entries above), culminating in
  **`card_le_cutVertex_full_bound`**: the island/restriction-image architecture, the distinguished
  component `C_0`'s bound, a fully composable single-branch bound usable for *any* other component
  via orbit-stabilizer at the component-permutation level (matching the manuscript's actual "adjoin
  `u` back to a component" strategy — an earlier attempt at naively re-applying `card_le_root_bound`
  to the island was caught and fixed for double-counting the root factor), and an outer
  well-founded recursion chaining that step across every remaining component down to a trivial
  base case. Two further sharpenings are also proved: `card_le_cutVertex_full_bound'` confines
  each step's orbit to the remaining pool `M` (giving `|M|!` instead of the crude
  `Fintype.card(BlockComponent)^{|M|}`), and **`card_le_cutVertex_full_bound''`**
  (`A2aCutVertexComponentType.lean`, `A2aCutVertexOuterInductionSharp.lean`,
  `A2aCutVertexFullBoundSharp.lean`) confines it further to `M`'s same-`compType` fiber (attachment
  count + block-size product), giving `∏_τ(fiber_τ.card)!` — matching the *shape* of the
  manuscript's `∏_τ m_τ!` grouping by rooted-isomorphism type. **Honest scope note**: all three are
  fully proved, literal `Nat` inequalities, but even the sharpest, `card_le_cutVertex_full_bound''`,
  remains a corollary of the manuscript's exact claim rather than the claim itself, for two reasons.
  First, `compType`'s two numeric invariants are a *necessary* condition for two components to be
  the manuscript's same rooted-isomorphism type but not a *sufficient* one, so it can (in principle)
  conflate non-isomorphic components that happen to share both numbers, making
  `classFactorialProd` potentially larger than the manuscript's exact `∏_τ m_τ!` in such cases (the
  two coincide whenever the numeric invariant already separates all types present, and
  `classFactorialProd` is always `≤|M|!` regardless). Reaching the literal statement in full
  generality would need a true rooted-tree/hypergraph isomorphism classifier in place of the two
  numeric proxies — the arithmetic ingredients such a classifier's grouping would still need beyond
  that (the two valuation facts and the `m_τ!` divisibility) are already fully proved,
  `A2aCutVertexValuation.lean`/`DisjointTupleSymmetry.lean`. Second, `hconn` and `hreach_all` are
  now both derived from ordinary block-graph connectivity (`A2aHconnFromReachable.lean`,
  `A2aHreachAll.lean`) rather than supplied as hypotheses; `hmixed` — a point-level claim, not
  implied by block-level connectivity alone — remains open.
  **The manuscript's own sentence "the coefficient of `X_{jp}` in `K_j(p)` is `(jp-1)!`" — the
  first step of (A3)'s sharpness argument — is now fully proved verbatim**
  (`FullCycleConnected.lean`, `CiFullCycle.lean`, `CiConverse.lean`, `FullCycleCount.lean`,
  `A3Final.lean`: **`A3_coeff_eq_factorial`**), `#print axioms`-checked standard — the first result
  in this codebase to exactly match a manuscript sentence end-to-end rather than a supporting
  lemma or a weaker bound. The tagged equation `(A3)` itself (`v_p(cont K_j(p))=e_p(j)`) needs one
  further fact beyond this — that no *other* coefficient of `K_j(p)` has smaller `p`-adic
  valuation, so this one coefficient realizes the whole polynomial's content — not attempted here.
  **The moment-cumulant expansion (A4)'s abstract mechanism is now also fully proved**
  (`GeneralizedConnectivity.lean` through `GeneralizedGfunProd.lean`, nine files: culminating in
  **`genGfun_eq_prod_K`**, `#print axioms`-checked standard — "connected structures on a union of
  blocks factor as a product of one connected structure per block," the two-level Möbius-inversion
  generalization `K_eq_Gfun_top` needs). The concrete manuscript instantiation is now partway
  built: `MacroMicroRelabel.lean`/`MacroMicroReach.lean` give the `q=Qp` relabeling and touches
  correspondence, and **`PartGraph.lean`** now proves the macroblock-connectivity side constraint
  itself in exactly the manuscript's own terms — **`genPiOf_macro_eq_top_iff_partGraphOf_connected`**:
  macroblock `⊤`-connectivity matches connectivity of the induced "touches-via-partition"
  hypergraph `H` on macroblocks, `#print axioms`-checked standard. **`GeneralizedGfunFilter.lean`**
  and **`MacroMicroSum.lean`** close the core content:
  **`K_eq_sum_filter_partGraphOf_connected_prod_K`** expresses `K_r(Qp)` exactly as the sum, over
  microblock partitions `τ'` whose induced macroblock hypergraph is connected, of `∏_{B∈τ'.parts}
  K(|B|,p)`. **`PartitionShape.lean`** and **`MacroMicroShape.lean`** take the final regrouping
  step, **`K_eq_sum_shapeCount_prod_K`**: `K_r(Qp)` as a sum over distinct block-size multisets
  `λ`, weighted by `shapeCount`(the count of macro-connected microblock partitions of shape `λ`),
  of `∏_{j∈λ} K(j,p)`. **`ShapeCpSplit.lean`** makes the manuscript's `C_p^{m_1}` split an actual
  proof rather than an observation — `K_one:K 1 q=C q` gives
  **`K_eq_sum_shapeCount_Cp_pow_mul_prod`**, `K_r(Qp)` as a `shapeCount`-weighted sum of
  `C_p^{m_1}·∏_{j≠1}K_j(p)` verbatim, `#print axioms`-checked standard — the manuscript's literal
  `K_r(q)=Σ_λ A^{\rm conn}_λ(Q;r)C_p^{m_1}∏_{j≥2}K_j(p)^{m_j}`, short of independently verifying
  `shapeCount`'s counting convention matches the manuscript's own `A^{\rm conn}_λ(Q;r)`
  normalization — not attempted here. The mod-`p` algebraic-independence
  argument via triangular Jacobians (A5) remains entirely open; the falling-factorial Vandermonde
  identity combined with the hypertree enumerator (A6) remains open as a whole, though its closing
  Lucas'-theorem step is fully proved (`LucasApplication.lean`) and the Vandermonde identity itself
  is now also fully proved, in full `r`-ary generality (`FallingFactorialVandermonde.lean`,
  `FallingFactorialVandermondeMultivariate.lean`) — genuinely research-scale group theory and
  extremal combinatorics, most of it not attempted here, but no longer entirely untouched.

## Build

```bash
lake build
```

This package requires `congruence-phenomena-lean` as a sibling checkout
(`../congruence-phenomena-lean`, matching the `path` requirement in
`lakefile.toml`) or, once both repositories are public, via the git
requirement form. `.lake/packages` can reuse a `congruence-phenomena-lean`
build pinned to the same toolchain (`v4.31.0`) and Mathlib revision to avoid
rebuilding Mathlib from scratch.

## Scope

This repository covers Part II of the two-part manuscript: higher-order
multiplicative defects, the connected-cumulant hierarchy, the atomic
equal-block content formula, and the complete prime-local classification.
See Part I's repository, `congruence-phenomena-lean`, for the universal
shift congruence and strong two-adic lift, which are fully verified there.
