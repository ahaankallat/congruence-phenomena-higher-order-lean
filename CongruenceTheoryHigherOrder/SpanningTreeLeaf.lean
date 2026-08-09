import Mathlib

/-!
**Graph-theoretic infrastructure toward inequality (A2a) of `thm:atomic-connected-content`.**

This file develops two general, reusable facts about `SimpleGraph` that are not present in
Mathlib and are needed for the "`u` is not a cut vertex" case of (A2a):

- **`SimpleGraph.IsAcyclic.map`**: acyclicity is preserved *forward* under an injective graph
  map `G.map f` (Mathlib only has the reverse direction, `IsAcyclic.of_map`). Proved by pulling
  a hypothetical cycle in `G.map f` back to a cycle in `G` via `Walk.induce` along the range of
  `f`, using `SimpleGraph.Embedding.map f G : G ↪g G.map f` and its induced-range isomorphism.
- **`SimpleGraph.exists_spanningTree_leaf`**: if `u` is not a cut vertex of a connected graph `G`
  on at least 2 vertices, `G` has a spanning tree in which `u` is a leaf (degree exactly `1`).
  Proved by taking a spanning tree `T'` of `G.induce {v | v ≠ u}` (via Mathlib's
  `exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic`), re-embedding it into `V` via
  `IsAcyclic.map`, and attaching `u` by a single edge to some neighbour `w` of `u` in `G`
  (via `IsAcyclic.sup_edge_of_not_reachable`).

This is the "attach a leaf" step of the manuscript's tree-rooted counting argument for
`|A| ≤ R_u ∏_{i≠u} (R_i - 1)!` in the `u`-not-a-cut-vertex case; the bipartite incidence-multigraph
formalization and the counting injection itself remain open.
-/

open scoped Classical

namespace SimpleGraph

variable {V W : Type*} (f : V ↪ W) (G : SimpleGraph V)

theorem Walk.support_subset_range {a b : W} (p : (G.map f).Walk a b) (ha : a ∈ Set.range f) :
    ∀ x ∈ p.support, x ∈ Set.range f := by
  induction p with
  | nil => intro x hx; simp only [Walk.support_nil, List.mem_singleton] at hx; subst hx; exact ha
  | cons hadj p' ih =>
    rename_i a b c
    rw [G.map_adj] at hadj
    obtain ⟨a', b', -, hfa, hfb⟩ := hadj
    have hb : b ∈ Set.range f := ⟨b', hfb⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact ha
    · exact ih hb x hmem

/-- Acyclicity is preserved forward under an injective graph map. The reverse direction
(`IsAcyclic.of_map`) is already in Mathlib; this direction is not. -/
theorem IsAcyclic.map (h : G.IsAcyclic) : (G.map f).IsAcyclic := by
  intro v q hq
  have hv : v ∈ Set.range f := by
    cases q with
    | nil => exact absurd rfl hq.ne_nil
    | cons hadj q' =>
      rw [G.map_adj] at hadj
      obtain ⟨a', -, -, hfa, -⟩ := hadj
      exact ⟨a', hfa⟩
  have hconf : ∀ x ∈ q.support, x ∈ Set.range f := Walk.support_subset_range f G q hv
  set q' := q.induce (Set.range f) hconf with hq'def
  have hmapback : q'.map (Embedding.induce (G := G.map f) (Set.range f)).toHom = q :=
    Walk.map_induce q hconf
  have hedgeseq : q.edges =
      q'.edges.map (Sym2.map (Embedding.induce (G := G.map f) (Set.range f)).toHom) := by
    conv_lhs => rw [← hmapback]
    exact Walk.edges_map ..
  have hsupeq : q.support =
      q'.support.map (Embedding.induce (G := G.map f) (Set.range f)).toHom := by
    conv_lhs => rw [← hmapback]
    exact Walk.support_map ..
  have hq'cycle : q'.IsCycle := by
    refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
    · have hn := hq.edges_nodup
      rw [hedgeseq] at hn
      exact List.Nodup.of_map _ hn
    · intro hnil
      apply hq.ne_nil
      have hqnil : q = Walk.nil := by rw [← hmapback, hnil]; rfl
      exact hqnil
    · have hsn := hq.support_nodup
      rw [hsupeq] at hsn
      have htail : (q'.support.map (Embedding.induce (G := G.map f) (Set.range f)).toHom).tail =
          q'.support.tail.map (Embedding.induce (G := G.map f) (Set.range f)).toHom := by
        cases q'.support with
        | nil => rfl
        | cons a l => rfl
      rw [htail] at hsn
      exact List.Nodup.of_map _ hsn
  have hiso := (Embedding.map f G).isoInduceRange
  have hinjsymm : Function.Injective hiso.symm.toHom := hiso.symm.toEquiv.injective
  exact h (q'.map hiso.symm.toHom) (Walk.IsCycle.map hinjsymm hq'cycle)

/-- `u` is a cut vertex of `G` if removing it disconnects the graph. -/
def IsCutVertex (G : SimpleGraph V) (u : V) : Prop :=
  ¬ (G.induce {v | v ≠ u}).Connected

/-- If `u` is not a cut vertex of a connected graph `G` with at least 2 vertices, there is a
spanning tree of `G` in which `u` is a leaf (degree exactly 1). -/
theorem exists_spanningTree_leaf [Fintype V] (hG : G.Connected) (u : V)
    (hu : ¬ G.IsCutVertex u) (hcard : 2 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ T.degree u = 1 := by
  unfold IsCutVertex at hu
  rw [not_not] at hu
  obtain ⟨T', -, hT'le, hT'acyc, hT'reach⟩ :=
    (G.induce {v | v ≠ u}).exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic
      (H := ⊥) bot_le isAcyclic_bot
  have hne : Nonempty ↥({v : V | v ≠ u}) := hu.nonempty
  have hT'conn : T'.Connected := by
    refine ⟨?_⟩
    rw [T'.preconnected_iff_reachable_eq_top, hT'reach,
      ← (G.induce {v | v ≠ u}).preconnected_iff_reachable_eq_top]
    exact hu.preconnected
  set ι : ↥({v : V | v ≠ u}) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩ with hιdef
  set T'' : SimpleGraph V := T'.map ι with hT''def
  have hT''acyc : T''.IsAcyclic := IsAcyclic.map ι T' hT'acyc
  have hT''isolated : T''.IsIsolated u := by
    intro w hadj
    rw [hT''def, T'.map_adj] at hadj
    obtain ⟨a, -, -, ha, -⟩ := hadj
    exact a.2 ha
  have hune : ∃ w : V, w ≠ u := by
    by_contra hcon
    push_neg at hcon
    have hle1 : Fintype.card V ≤ 1 := by
      rw [Fintype.card_le_one_iff]
      intro a b
      rw [hcon a, hcon b]
    omega
  obtain ⟨w0, hw0⟩ := hune
  have hexnb : ∃ w, G.Adj u w := by
    have hreach := hG.preconnected u w0
    rw [reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨y, hy, -⟩
    · exact absurd heq.symm hw0
    · exact ⟨y, hy⟩
  obtain ⟨w, hw⟩ := hexnb
  have hwneu : w ≠ u := hw.ne'
  set T : SimpleGraph V := T'' ⊔ edge u w with hTdef
  have hTle : T ≤ G := by
    apply sup_le
    · intro a b hab
      rw [hT''def, T'.map_adj] at hab
      obtain ⟨a', b', hadj', hfa, hfb⟩ := hab
      rw [← hfa, ← hfb]
      exact hT'le hadj'
    · intro a b hab
      rw [edge_adj] at hab
      rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hw
      · exact hw.symm
  have hnotreach : ¬ T''.Reachable u w := by
    intro hreach
    obtain ⟨p⟩ := hreach
    cases p with
    | nil => exact hw.ne rfl
    | cons hadj p' => exact hT''isolated _ hadj
  have hTacyc : T.IsAcyclic := hT''acyc.sup_edge_of_not_reachable hnotreach
  have hlift : ∀ x y : ↥({v : V | v ≠ u}), T'.Reachable x y → T.Reachable (ι x) (ι y) := by
    intro x y hxy
    obtain ⟨p⟩ := hxy
    have hp' : T''.Walk (ι x) (ι y) := p.map (Embedding.map ι T').toHom
    exact hp'.reachable.mono le_sup_left
  have huw : T.Adj u w := by
    rw [hTdef, sup_adj]
    right
    rw [edge_adj]
    exact ⟨Or.inl ⟨rfl, rfl⟩, hw.ne⟩
  have hTconn : T.Preconnected := by
    intro a b
    by_cases ha : a = u <;> by_cases hb : b = u
    · rw [ha, hb]
    · have h2 : T.Reachable (ι ⟨w, hwneu⟩) (ι ⟨b, hb⟩) := hlift _ _ (hT'conn.preconnected _ _)
      rw [ha]
      exact huw.reachable.trans h2
    · have h2 : T.Reachable (ι ⟨w, hwneu⟩) (ι ⟨a, ha⟩) := hlift _ _ (hT'conn.preconnected _ _)
      rw [hb]
      exact (huw.reachable.trans h2).symm
    · exact hlift ⟨a, ha⟩ ⟨b, hb⟩ (hT'conn.preconnected _ _)
  clear_value T
  have hdeg1 : T.degree u = 1 := by
    have hnf : T.neighborFinset u = {w} := by
      apply Finset.ext
      intro x
      rw [mem_neighborFinset, Finset.mem_singleton]
      constructor
      · intro hadj
        rw [hTdef, sup_adj] at hadj
        rcases hadj with hadj | hadj
        · exact absurd hadj (hT''isolated x)
        · rw [edge_adj] at hadj
          rcases hadj.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact h2
          · exact absurd h1 hw.ne
      · intro hx
        rw [hx]
        exact huw
    rw [← card_neighborFinset_eq_degree, hnf, Finset.card_singleton]
  have hVne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact ⟨T, hTle, ⟨⟨hTconn⟩, hTacyc⟩, hdeg1⟩

end SimpleGraph
