import PEqualNP.Defs

/-!
Support counting adapted from the public project files
PEqualNP/MetaComplexity/Helpers/Support.lean and PermInputs.lean.
The small degree-sum proof below is adapted from pinned Mathlib
Combinatorics/SimpleGraph/DegreeSum.lean, copyright 2020 Kyle Miller,
released under the Apache 2.0 license.

This module is a parameterized bounded-maximum-degree result. It does not
establish a uniform constant for the unrestricted L-meta-1710 statement.
-/

namespace PEqualNP.Outside.L_meta_1710.BoundedDegree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n : ℕ}

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- The support of a gate: the union of the supports of the wires it reads. -/
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

/-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
`y` agree on. -/
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- Any set `W` of wires has a joint support of size at most `t + |W|`. -/
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

/-- Any collection of semantically essential inputs has at most one more
member than the number of gates. Only the fan-in condition is needed. -/
theorem dependent_inputs_card_le (n : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool,
      circuitFun n C (Function.update x i (!x i)) ≠ circuitFun n C x) :
    T.card ≤ C.size + 1 := by
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    exact (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) hfan cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  exact (Finset.card_le_card hall).trans hc

def edgeFun (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : Bool :=
  decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)

/-- Every endpoint of an edge is an essential variable of the edge function. -/
theorem edge_dep (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w : Fin n) (hvw : G.Adj v w) :
    ∃ x : Fin n → Bool,
      edgeFun G (Function.update x v (!x v)) ≠ edgeFun G x := by
  let x : Fin n → Bool := fun z => decide (z = w)
  refine ⟨x, ?_⟩
  have hzero : edgeFun G x = false := by
    simp only [edgeFun, x, decide_eq_true_eq, decide_eq_false_iff_not]
    rintro ⟨a, b, hab, ha, hb⟩
    subst a
    subst b
    exact G.loopless.irrefl w hab
  have hone : edgeFun G (Function.update x v (!x v)) = true := by
    rw [edgeFun, decide_eq_true_eq]
    refine ⟨v, w, hvw, ?_, ?_⟩
    · simp [x, hvw.ne]
    · simp [Function.update_of_ne hvw.ne.symm, x]
  rw [hone, hzero]
  decide

/-- Isolated vertices make no contribution to this count. -/
theorem nonisolated_card_le (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (heval : circuitFun n C = edgeFun G) :
    (Finset.univ.filter fun v => G.degree v ≠ 0).card ≤ C.size + 1 := by
  apply dependent_inputs_card_le n C hfan
  intro v hv
  have hv' : G.degree v ≠ 0 := (Finset.mem_filter.mp hv).2
  obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero hv')
  simpa only [heval] using edge_dep G v w hvw

section DegreeSum

open Finset

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

private theorem dart_fst_fiber (v : Fin n) :
    ({d : G.Dart | d.fst = v} : Finset _) = univ.image (G.dartOfNeighborSet v) := by
  ext d
  simp only [mem_image, true_and, mem_filter, SetCoe.exists, mem_univ]
  constructor
  · rintro rfl
    exact ⟨_, d.adj, by ext <;> rfl⟩
  · rintro ⟨e, he, rfl⟩
    rfl

private theorem dart_fst_fiber_card (v : Fin n) :
    ({d : G.Dart | d.fst = v} : Finset _).card = G.degree v := by
  simpa only [dart_fst_fiber, Finset.card_univ, SimpleGraph.card_neighborSet_eq_degree] using
    card_image_of_injective univ (G.dartOfNeighborSet_injective v)

private theorem dart_card_eq_sum_degrees : Fintype.card G.Dart = ∑ v, G.degree v := by
  simp only [← card_univ, ← dart_fst_fiber_card]
  exact card_eq_sum_card_fiberwise (by simp)

private theorem dart_edge_fiber (d : G.Dart) :
    ({d' : G.Dart | d'.edge = d.edge} : Finset _) = {d, d.symm} :=
  Finset.ext fun d' => by simpa using SimpleGraph.dart_edge_eq_iff d' d

private theorem dart_edge_fiber_card (e : Sym2 (Fin n)) (h : e ∈ G.edgeSet) :
    ({d : G.Dart | d.edge = e} : Finset _).card = 2 := by
  obtain ⟨v, w⟩ := e
  let d : G.Dart := ⟨(v, w), h⟩
  convert! congrArg Finset.card (dart_edge_fiber G d)
  rw [card_insert_of_notMem, card_singleton]
  rw [mem_singleton]
  exact d.symm_ne.symm

private theorem dart_card_eq_twice_edges : Fintype.card G.Dart = 2 * G.edgeFinset.card := by
  classical
  rw [← card_univ]
  rw [@card_eq_sum_card_fiberwise _ _ _ SimpleGraph.Dart.edge _ G.edgeFinset fun d _h =>
      by rw [mem_coe, SimpleGraph.mem_edgeFinset]; apply SimpleGraph.Dart.edge_mem]
  rw [← mul_comm, sum_const_nat]
  intro e h
  apply dart_edge_fiber_card G e
  rwa [← SimpleGraph.mem_edgeFinset]

private theorem sum_degrees_eq_twice_edges : ∑ v, G.degree v = 2 * G.edgeFinset.card :=
  (dart_card_eq_sum_degrees G).symm.trans (dart_card_eq_twice_edges G)

end DegreeSum

/-- A maximum degree bound gives a linear edge-count bound, for every graph.
The conclusion uses no girth or minimum-degree hypothesis. -/
theorem bounded_degree_edges (D : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hD : ∀ v, G.degree v ≤ D) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (heval : circuitFun n C = edgeFun G) :
    2 * G.edgeFinset.card ≤ D * (C.size + 1) := by
  let T := Finset.univ.filter fun v => G.degree v ≠ 0
  have hcard : T.card ≤ C.size + 1 := nonisolated_card_le G C hfan heval
  have hsum : (∑ v, G.degree v) = ∑ v ∈ T, G.degree v := by
    symm
    apply Finset.sum_subset (Finset.subset_univ T)
    intro v _ hv
    by_contra h
    exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
  calc
    2 * G.edgeFinset.card = ∑ v, G.degree v := (sum_degrees_eq_twice_edges G).symm
    _ = ∑ v ∈ T, G.degree v := hsum
    _ ≤ ∑ _v ∈ T, D := Finset.sum_le_sum fun v _ => hD v
    _ = D * T.card := by simp [Nat.mul_comm]
    _ ≤ D * (C.size + 1) := Nat.mul_le_mul_left D hcard

/-- The specialization to the task's public monotone circuit class. -/
theorem monotone_bounded_degree_edges (D : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hD : ∀ v, G.degree v ≤ D) (C : Circuit)
    (hmono : Monotone2 C)
    (heval : circuitFun n C = fun x => decide
      (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) :
    2 * G.edgeFinset.card ≤ D * (C.size + 1) :=
  bounded_degree_edges D G hD C (fun g hg => (hmono g hg).2) heval

end PEqualNP.Outside.L_meta_1710.BoundedDegree
