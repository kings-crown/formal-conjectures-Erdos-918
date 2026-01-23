/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports
import Mathlib
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Order.ConditionallyCompleteLattice.Basic



set_option linter.style.ams_attribute false
set_option linter.unusedTactic false
/-!
# Erdős Problem 918

*References:*
- [erdosproblems.com/918](https://www.erdosproblems.com/918)
- [ErHa68b] Erdős, P. and Hajnal, A., On chromatic number of infinite graphs. (1968), 83--98.
- [Er69b] Erdős, P., Problems and results in chromatic graph theory. Proof Techniques in Graph Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
-/

universe u

open scoped Cardinal

namespace Erdos918

/-- Is there a graph with $\aleph_2$ vertices and chromatic number $\aleph_2$ such that every
subgraph on $\aleph_1$ vertices has chromatic number $\leq\aleph_0$? -/
-- Formalisation note: source material [ErHa68b] uses only induced subgraphs
@[category research open, AMS 5]
theorem erdos_918.parts.i :
    answer(sorry) ↔ ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  sorry

/-- Is there a graph with $\aleph_{\omega+1}$ vertices and chromatic number $\aleph_1$ such that
every subgraph on $\aleph_\omega$ vertices has chromatic number $\leq\aleph_0$? -/
@[category research open, AMS 5]
theorem erdos_918.parts.ii (ω : Ordinal) :
    answer(sorry) ↔ ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W = ℵ_ ω), (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  sorry

/-- Is there a graph with $\aleph_2$ vertices and chromatic number $\aleph_2$ such that every
subgraph on $\aleph_1$ vertices has chromatic number $\leq\aleph_0$? -/
-- Formalisation note: It is not clear whether this question for general subgraphs is open or not
@[category research open, AMS 5]
theorem erdos_918.variants.all_subgraphs.parts.i :
    answer(sorry) ↔ ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ₁), H.coe.chromaticCardinal ≤ ℵ₀ := by
  sorry

/-- Is there a graph with $\aleph_{\omega+1}$ vertices and chromatic number $\aleph_1$ such that
every subgraph on $\aleph_\omega$ vertices has chromatic number $\leq\aleph_0$? -/
@[category research open, AMS 5]
theorem erdos_918.variants.all_subgraphs.parts.ii (ω : Ordinal) :
    answer(sorry) ↔ ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ_ ω), H.coe.chromaticCardinal ≤ ℵ₀ := by
  sorry

/-- A question of Erd\H{o}s and Hajnal [ErHa68b], who proved that for every finite $k$
there is a graph with chromatic number $\aleph_1$ and $\aleph_k$ vertices where each subgraph on
less than $\aleph_k$ vertices has chromatic number $\leq \aleph_0$. -/
-- Formalisation note: the source is missing the assumption that the graph have ℵₖ vertices
-- which can be found in [ErHa68b]
@[category research solved, AMS 5]
theorem erdos_918.variants.erdos_hajnal (k : ℕ) : ∃ (V : Type u) (G : SimpleGraph V),
    #V = ℵ_ k ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W < ℵ_ k), (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  sorry

/-- In [ErHa69] the questions are stated with $= \aleph_0$ rather than $\leq\aleph_0$. This is
a likely typo since it can be shown that no such graph exists in this case.

This is the first question with induced subgraphs. -/
@[category undergraduate, AMS 5]
theorem erdos_918.variants.eq_aleph_0.parts.i :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal = ℵ₀ := by
  sorry

/-- In [ErHa69] the questions are stated with $= \aleph_0$ rather than $\leq\aleph_0$. This is
a likely typo since it can be shown that no such graph exists in this case.

This is the first question with all subgraphs. -/
@[category high_school, AMS 5]
theorem erdos_918.variants.eq_aleph_0_all_subgraphs.parts.i :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ₁), H.coe.chromaticCardinal = ℵ₀ := by
  sorry

/-- In [ErHa69] the questions are stated with $= \aleph_0$ rather than $\leq\aleph_0$. This is
a likely typo since it can be shown that no such graph exists in this case.

This is the second question with induced subgraphs. -/
@[category undergraduate, AMS 5]
theorem erdos_918.variants.eq_aleph_0.parts.ii (ω : Ordinal) :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W = ℵ_ ω), (G.induce W).chromaticCardinal = ℵ₀ := by
  sorry

/-- In [ErHa69] the questions are stated with $= \aleph_0$ rather than $\leq\aleph_0$. This is
a likely typo since it can be shown that no such graph exists in this case.

This is the second question with all subgraphs. -/
@[category high_school, AMS 5]
theorem erdos_918.variants.eq_aleph_0_all_subgraphs.parts.ii (ω : Ordinal) :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ_ ω), H.coe.chromaticCardinal = ℵ₀ := by
  sorry

end Erdos918


noncomputable section
open Classical


set_option linter.style.category_attribute false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false

lemma chromaticCardinal_le_one_of_no_edges {V : Type u} (G : SimpleGraph V)
    (hno : ∀ ⦃v w : V⦄, ¬ G.Adj v w) :
    G.chromaticCardinal ≤ (1 : Cardinal.{u}) := by
  classical
  -- one-color type living in Type u
  let C : Type u := ULift.{u} (Fin 1)

  have hcol : Nonempty (G.Coloring C) := by
    refine ⟨{ toFun := fun _ => (⟨⟨0, by decide⟩⟩ : C)
              map_rel' := ?_ }⟩
    intro v w hvw
    -- adjacency is impossible, so the "different colors" obligation is vacuous
    exact (hno hvw).elim

  -- use the definition: chromaticCardinal = sInf {κ | ∃ C, #C = κ ∧ Nonempty (G.Coloring C)}
  unfold SimpleGraph.chromaticCardinal
   -- Let S be the set whose infimum defines χ
  let S : Set (Cardinal.{u}) :=
    { κ | ∃ C : Type u, ∃ (_ : (#C : Cardinal.{u}) = κ), Nonempty (G.Coloring C) }

  change sInf S ≤ (#C : Cardinal.{u})
  have hBdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro κ hκ
    exact bot_le

  refine csInf_le hBdd ?_
  exact ⟨C, rfl, hcol⟩


@[category high_school, AMS 5]
theorem erdos_918.variants.eq_aleph_0_all_subgraphs.parts.i :
    ¬∃ (V : Type u) (G : SimpleGraph V),
        #V = ℵ_ 2 ∧
        G.chromaticCardinal = ℵ_ 2 ∧
        ∀ (H : G.Subgraph) (_ : #H.verts = ℵ₁), H.coe.chromaticCardinal = ℵ₀ := by
  classical
  intro h
  rcases h with ⟨V, G, hV, hχ, hsub⟩

  --------------------------------------------------------------------
  -- 1) Pick W : Set V with #W = ℵ₁
  --------------------------------------------------------------------
  have hle : (ℵ₁ : Cardinal.{u}) ≤ #V := by
    simpa [hV] using
      (Cardinal.aleph_le_aleph.2 (by decide : (1 : Ordinal) ≤ 2))

  rcases (Cardinal.le_mk_iff_exists_set (α := V)).1 hle with ⟨W, hW⟩

  --------------------------------------------------------------------
  -- 2) Induce a subgraph on W, then delete ALL edges
  --------------------------------------------------------------------
  let H0 : G.Subgraph := (⊤ : G.Subgraph).induce W
  let H  : G.Subgraph := H0.deleteEdges Set.univ

  -- verts are unchanged by deleteEdges, and induce has verts = W
  have hHverts : #H.verts = (ℵ₁ : Cardinal.{u}) := by
    -- Often simp proves H.verts = W; then this is immediate from hW
    -- If simp doesn’t close, see debugging notes below.
    have : H.verts = W := by
      simp [H, H0]
    simpa [this] using hW

  --------------------------------------------------------------------
  -- 3) Hypothesis forces χ(H) = ℵ₀
  --------------------------------------------------------------------
  have hHchi : H.coe.chromaticCardinal = (ℵ₀ : Cardinal.{u}) :=
    hsub H hHverts

  --------------------------------------------------------------------
  -- 4) But H has no edges, so χ(H) ≤ 1
  --    IMPORTANT: H.coe is on ↑H.verts, not V
  --------------------------------------------------------------------
  have hno : ∀ ⦃v w : ↑H.verts⦄, ¬ (H.coe).Adj v w := by
    intro v w hvw

    -- Convert adjacency in H.coe (subtype vertices) to adjacency in H on V
    have hvwH : H.Adj (v : V) (w : V) := by
      simpa [SimpleGraph.Subgraph.coe_adj] using hvw

    -- Rewrite H = H0.deleteEdges Set.univ
    have hvwDel : (H0.deleteEdges Set.univ).Adj (v : V) (w : V) := by
      simpa [H] using hvwH

    -- Unpack deleteEdges adjacency
    have hpair :=
      (SimpleGraph.Subgraph.deleteEdges_adj (G' := H0) (s := Set.univ)
        (v := (v : V)) (w := (w : V))).1 hvwDel
    -- hpair : H0.Adj (v:V) (w:V) ∧ (Set.univ …) ∉ Set.univ

    -- The second conjunct is impossible because everything is in Set.univ
    have : False := by
      simpa using hpair.2
    exact this.elim


  have hle1 : H.coe.chromaticCardinal ≤ (1 : Cardinal.{u}) :=
    chromaticCardinal_le_one_of_no_edges (G := H.coe) hno

  --------------------------------------------------------------------
  -- 5) Contradiction: χ(H)=ℵ₀ but χ(H)≤1
  --------------------------------------------------------------------
  have : (ℵ₀ : Cardinal.{u}) ≤ (1 : Cardinal.{u}) := by
    simpa [hHchi] using hle1

  exact (not_le_of_gt (Cardinal.one_lt_aleph0 :
    (1 : Cardinal.{u}) < (ℵ₀ : Cardinal.{u}))) this
