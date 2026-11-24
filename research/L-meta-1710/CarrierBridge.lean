import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1710.CarrierBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CarriedProduct PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]


def F (n : ℕ) (C : Circuit) (vals : List Bool) (m : ℕ) (L : List ℕ) : List ℕ :=
  ((List.range m).reverse).foldl (liveStep n C vals) L

lemma F_zero (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) :
    F n C vals 0 L = L := by
  simp [F]

lemma F_succ (n : ℕ) (C : Circuit) (vals : List Bool) (m : ℕ) (L : List ℕ) :
    F n C vals (m + 1) L = F n C vals m (liveStep n C vals L m) := by
  simp [F, List.range_succ]

lemma step_sub (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) (j w : ℕ) (hw : w ∈ L) :
    w ∈ liveStep n C vals L j := by
  unfold liveStep
  split_ifs
  · exact List.mem_append_left _ hw
  · exact hw

lemma step_mem (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) (j w : ℕ)
    (h : w ∈ liveStep n C vals L j) :
    w ∈ L ∨ (n + j ∈ L ∧ w ∈ (gateAt C j).inputs ∧ w < n + j ∧ vals.getD w false = true) := by
  unfold liveStep at h
  split_ifs at h with hj
  · rcases List.mem_append.1 h with h | h
    · exact Or.inl h
    · simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
      exact Or.inr ⟨hj, h.1, h.2.1, h.2.2⟩
  · exact Or.inl h

lemma F_sub (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ) (w : ℕ), w ∈ L → w ∈ F n C vals m L := by
  intro m
  induction m with
  | zero => intro L w hw; rw [F_zero]; exact hw
  | succ m ih => intro L w hw; rw [F_succ]; exact ih _ w (step_sub n C vals L m w hw)

lemma F_mem (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ) (w : ℕ), w ∈ F n C vals m L → w ∈ L ∨ w < n + m := by
  intro m
  induction m with
  | zero => intro L w hw; rw [F_zero] at hw; exact Or.inl hw
  | succ m ih =>
    intro L w hw
    rw [F_succ] at hw
    rcases ih _ w hw with h | h
    · rcases step_mem n C vals L m w h with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    · exact Or.inr (by omega)

lemma F_true (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ), (∀ w ∈ L, vals.getD w false = true) →
      ∀ w ∈ F n C vals m L, vals.getD w false = true := by
  intro m
  induction m with
  | zero => intro L hL w hw; rw [F_zero] at hw; exact hL w hw
  | succ m ih =>
    intro L hL w hw
    rw [F_succ] at hw
    refine ih _ ?_ w hw
    intro w2 hw2
    rcases step_mem n C vals L m w2 hw2 with h | h
    · exact hL w2 h
    · exact h.2.2.2

lemma F_back (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ) (j : ℕ), j < m → n + j ∈ F n C vals m L →
      ∀ a ∈ (gateAt C j).inputs, a < n + j → vals.getD a false = true →
        a ∈ F n C vals m L := by
  intro m
  induction m with
  | zero => intro L j hj; omega
  | succ m ih =>
    intro L j hj hmem a ha hlt hv
    rw [F_succ] at hmem ⊢
    by_cases hjm : j < m
    · exact ih _ j hjm hmem a ha hlt hv
    · have hjeq : j = m := by omega
      subst hjeq
      have h1 : n + j ∈ liveStep n C vals L j := by
        rcases F_mem n C vals j _ _ hmem with h | h
        · exact h
        · omega
      have h2 : n + j ∈ L := by
        rcases step_mem n C vals L j _ h1 with h | h
        · exact h
        · exact h.1
      apply F_sub
      unfold liveStep
      rw [ite_eq_left h2]
      refine List.mem_append_right _ ?_
      simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨ha, hlt, hv⟩

lemma liveWires_eq (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    liveWires n C x = F n C (C.wires (List.ofFn x)) C.gates.length
      (if (C.wires (List.ofFn x)).getD C.output false then [C.output] else []) := rfl

lemma live_true (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (h : IsLive n C x w) :
    W n C x w = true := by
  unfold IsLive at h
  rw [liveWires_eq] at h
  refine F_true n C _ _ _ ?_ w h
  intro w2 hw2
  split_ifs at hw2 with hc
  · simp only [List.mem_singleton] at hw2
    rw [hw2]; exact hc
  · simp at hw2

lemma live_back (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (h : IsLive n C x (n + j)) (a : ℕ) (ha : a ∈ (gateAt C j).inputs) (hlt : a < n + j)
    (hv : W n C x a = true) : IsLive n C x a := by
  unfold IsLive at h ⊢
  rw [liveWires_eq] at h ⊢
  exact F_back n C _ _ _ j hj h a ha hlt hv

lemma live_out (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : W n C x C.output = true) :
    IsLive n C x C.output := by
  unfold IsLive
  rw [liveWires_eq]
  apply F_sub
  unfold W at h
  rw [ite_eq_left h]
  simp

theorem closure (n : ℕ) (C : Circuit) (hM : Monotone2 C) (u v : Fin n) (B : ℕ)
    (hno : ∀ i, n + i < B → (gateAt C i).op = GateOp.and →
      ¬ IsLive n C (pairInput u v) (n + i)) :
    ∀ w, w < B → IsLive n C (pairInput u v) w →
      W n C (pairInput u u) w = true ∨ W n C (pairInput v v) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwB hlive
    have hw := live_true n C _ w hlive
    by_cases hwn : w < n
    · rw [W_input n C _ w hwn] at hw
      simp only [pairInput, decide_eq_true_eq] at hw
      rcases hw with h | h
      · left; rw [W_input n C _ w hwn]; simp [pairInput, h]
      · right; rw [W_input n C _ w hwn]; simp [pairInput, h]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k < C.gates.length
      · have hmem : gateAt C k ∈ C.gates := by
          rw [gateAt_eq C k hk]
          exact List.getElem_mem hk
        have hops := (hM _ hmem).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hops
        rcases hops with hop | hop
        · exact absurd hlive (hno k hwB hop)
        · rw [W_gate n C _ k hk, hop] at hw
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at hw
          obtain ⟨i, hi, hv⟩ := hw
          have hlt : i < n + k := by
            by_contra hc
            simp [hc] at hv
          simp only [hlt, ite_true] at hv
          have hli := live_back n C _ k hk hlive i hi hlt hv
          have key : ∀ y : Fin n → Bool, W n C y i = true → W n C y (n + k) = true := by
            intro y hy
            rw [W_gate n C _ k hk, hop]
            simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
            exact ⟨i, hi, by simp only [hlt, ite_true]; exact hy⟩
          rcases ih i hlt (by omega) hli with h | h
          · exact Or.inl (key _ h)
          · exact Or.inr (key _ h)
      · exfalso
        have : W n C (pairInput u v) (n + k) = false := by
          simp only [W]
          exact getD_ge_length _ _ (by rw [wires_length]; omega)
        rw [this] at hw
        exact Bool.false_ne_true hw

lemma exists_min (P : ℕ → Prop) (h : ∃ t, P t) : ∃ t, P t ∧ ∀ i < t, ¬ P i := by
  by_contra hno
  have hall : ∀ t, ¬ P t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro hp
      exact hno ⟨t, hp, ih⟩
  obtain ⟨t, ht⟩ := h
  exact hall t ht

lemma card_pair (n : ℕ) (u v : Fin n) :
    (Finset.univ.filter (fun k : Fin n => pairInput u v k = true)).card ≤ 2 := by
  have hsub : Finset.univ.filter (fun k : Fin n => pairInput u v k = true) ⊆ {u, v} := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairInput, decide_eq_true_eq] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hk
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

lemma graph_single (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) :
    graphFun G ∅ (pairInput i i) = false := by
  rw [Bool.eq_false_iff]
  intro h
  unfold graphFun at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨a, ha, _⟩ | ⟨a, b, hab, ha, hb⟩
  · simp at ha
  · simp only [pairInput, or_self, decide_eq_true_eq] at ha hb
    rw [ha, hb] at hab
    exact G.irrefl hab

lemma graph_pair (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n)
    (huv : G.Adj u v) : graphFun G ∅ (pairInput u v) = true := by
  unfold graphFun
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  right
  exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩


/- Wire and live-trace infrastructure above is adapted from the checked L-meta-1603. -/

open PEqualNP.TopForm PEqualNP.CleanedNonEdge

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k


lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩


lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩


/- OR-closure infrastructure above is adapted from the checked L-meta-1490. -/

lemma ao2_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : Monotone2 C := by
  intro g hg
  refine ⟨?_, le_of_eq (hAO.2.2 g hg)⟩
  rcases hAO.1 g hg with h | h
  · simp [h]
  · simp [h]

lemma carrier_unique {n : ℕ} {C : Circuit} {u v : Fin n} {i j : ℕ}
    (hi : IsCarrier n C u v i) (hj : IsCarrier n C u v j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact (hj.2.2.2 i h hi.2.1 hi.2.2.1).elim
  · exact h
  · exact (hi.2.2.2 j h hj.2.1 hj.2.2.1).elim

/-- Carrier existence requires correctness on pairs and singletons, but does not require
    individual AND gates to reject singleton inputs. -/
theorem carrier_exists (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hM : Monotone2 C) (hfun : circuitFun n C = graphFun G ∅)
    (u v : Fin n) (huv : G.Adj u v) : ∃ j, IsCarrier n C u v j := by
  have hW : ∀ y, circuitFun n C y = W n C y C.output := fun _ => rfl
  have hsingle : ∀ i : Fin n, W n C (pairInput i i) C.output = false := by
    intro i
    rw [← hW, hfun]
    exact graph_single n G i
  have hout : IsLive n C (pairInput u v) C.output := by
    apply live_out
    rw [← hW, hfun]
    exact graph_pair n G u v huv
  have hex : ∃ t, (gateAt C t).op = GateOp.and ∧ IsLive n C (pairInput u v) (n + t) := by
    by_contra hno
    have hno2 : ∀ i, n + i < C.output + 1 → (gateAt C i).op = GateOp.and →
        ¬ IsLive n C (pairInput u v) (n + i) := fun i _ hop hl => hno ⟨i, hop, hl⟩
    rcases closure n C hM u v (C.output + 1) hno2 C.output (by omega) hout with h | h
    · rw [hsingle u] at h; exact Bool.false_ne_true h
    · rw [hsingle v] at h; exact Bool.false_ne_true h
  have hlen : ∀ t, (gateAt C t).op = GateOp.and → t < C.gates.length := by
    intro t hop
    by_contra hc
    have hd : gateAt C t = ⟨GateOp.or, []⟩ := by
      simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 hc)]
    rw [hd] at hop
    cases hop
  obtain ⟨t, ⟨hop, hl⟩, hmin⟩ := exists_min _ hex
  exact ⟨t, hlen t hop, hop, hl, fun i hi hopi hli => hmin i hi ⟨hopi, hli⟩⟩

/-- Before the first live AND, every live wire has a true OR-only path to one of the
    two inputs. This is stronger than the singleton-value disjunction in L-meta-1603. -/
lemma live_or_trace (n : ℕ) (C : Circuit) (hM : Monotone2 C) (u v : Fin n) (B : ℕ)
    (hno : ∀ i, n + i < B → (gateAt C i).op = GateOp.and →
      ¬ IsLive n C (pairInput u v) (n + i)) :
    ∀ w, w < B → IsLive n C (pairInput u v) w →
      ∃ t : Fin n, (t = u ∨ t = v) ∧
        Relation.ReflTransGen (OrStep n C) w t.val := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwB hlive
    have hw := live_true n C _ w hlive
    by_cases hwn : w < n
    · refine ⟨⟨w, hwn⟩, ?_, Relation.ReflTransGen.refl⟩
      rw [W_input n C _ w hwn] at hw
      simpa only [pairInput, decide_eq_true_eq] using hw
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k < C.gates.length
      · have hmem : gateAt C k ∈ C.gates := by
          rw [gateAt_eq C k hk]
          exact List.getElem_mem hk
        have hops := (hM _ hmem).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hops
        rcases hops with hop | hop
        · exact absurd hlive (hno k hwB hop)
        · rw [W_gate n C _ k hk, hop] at hw
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at hw
          obtain ⟨i, hi, hv⟩ := hw
          have hlt : i < n + k := by
            by_contra hc
            simp [hc] at hv
          simp only [hlt, ite_true] at hv
          have hli := live_back n C _ k hk hlive i hi hlt hv
          obtain ⟨t, ht, hr⟩ := ih i hlt (by omega) hli
          exact ⟨t, ht, Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr⟩
      · exfalso
        have : W n C (pairInput u v) (n + k) = false := by
          simp only [W]
          exact getD_ge_length _ _ (by rw [wires_length]; omega)
        rw [this] at hw
        exact Bool.false_ne_true hw

lemma or_path_true {n : ℕ} {C : Circuit} (x : Fin n → Bool) {w w' : ℕ}
    (hr : Relation.ReflTransGen (OrStep n C) w w') (hv : W n C x w' = true) :
    W n C x w = true := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    rw [W_gate n C _ k hk, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    exact ⟨_, hin, by simpa [hlt] using ih⟩

/-- A clean earliest-live AND can carry only a star edge. No minimality, girth,
    TopForm, or correctness assumption is used in this local implication. -/
theorem carrier_below_star (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (u v : Fin n) (j : ℕ)
    (hc : IsCarrier n C u v j) (hbelow : BelowF G C j) :
    s(u, v) ∈ starEdges G C := by
  have hj := hc.1
  have hop := hc.2.1
  have hl := hc.2.2.1
  have hmin := hc.2.2.2
  have hmem : gateAt C j ∈ C.gates := by
    rw [gateAt_eq C j hj]
    exact List.getElem_mem hj
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ hmem)
  have hgate : ∀ x : Fin n → Bool, W n C x (n + j) =
      ((gateAt C j).inputs.map fun i => if i < n + j then W n C x i else false).all id := by
    intro x
    rw [W_gate n C _ j hj, hop]
    rfl
  have hv := live_true n C _ _ hl
  rw [hgate] at hv
  simp only [List.all_map, List.all_eq_true, Function.comp_apply, id] at hv
  have hinput : ∀ z ∈ (gateAt C j).inputs, z < n + j ∧ W n C (pairInput u v) z = true := by
    intro z hz
    have h := hv z hz
    by_cases hz' : z < n + j
    · exact ⟨hz', by simpa [hz'] using h⟩
    · simp [hz'] at h
  have ha := hinput a (by rw [hin]; simp)
  have hb := hinput b (by rw [hin]; simp)
  have hno : ∀ i, n + i < n + j → (gateAt C i).op = GateOp.and →
      ¬ IsLive n C (pairInput u v) (n + i) := fun i hi => hmin i (by omega)
  obtain ⟨r, hr, hrt⟩ := live_or_trace n C (ao2_mono hAO) u v (n + j) hno a ha.1
    (live_back n C _ j hj hl a (by rw [hin]; simp) ha.1 ha.2)
  obtain ⟨s, hs, hst⟩ := live_or_trace n C (ao2_mono hAO) u v (n + j) hno b hb.1
    (live_back n C _ j hj hl b (by rw [hin]; simp) hb.1 hb.2)
  have hsingle_path : ∀ (t : Fin n) (w : ℕ),
      Relation.ReflTransGen (OrStep n C) w t.val → W n C (pairInput t t) w = true := by
    intro t w ht
    apply or_path_true (pairInput t t) ht
    rw [W_input n C _ t.val t.isLt]
    simp [pairInput]
  have hrs : r ≠ s := by
    intro heq
    subst s
    have har := hsingle_path r a hrt
    have hbr := hsingle_path r b hst
    have hc1 : W n C (pairInput r r) (n + j) = true := by
      rw [hgate, hin]
      simp [ha.1, hb.1, har, hbr]
    have hgr := hbelow (pairInput r r) hc1
    rw [graph_single n G r] at hgr
    exact Bool.false_ne_true hgr
  have hed : s(r, s) = s(u, v) := by
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
    · exact (hrs rfl).elim
    · rfl
    · exact Sym2.eq_swap
    · exact (hrs rfl).elim
  have htop : j ∈ tops G C := by
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, hop, hbelow⟩
  rw [← hed]
  simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
  refine ⟨j, htop, (r, s), ⟨?_, ?_⟩, rfl⟩
  · have hri := reach_mem_orIn r hrt
    simpa [side, opnd, hin] using hri
  · have hsi := reach_mem_orIn s hst
    simpa [side, opnd, hin] using hsi

theorem residual_carrier_junk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (u v : Fin n) (j : ℕ)
    (he : s(u, v) ∈ Ustar G C) (hc : IsCarrier n C u v j) : j ∈ junk G C := by
  have hnstar : s(u, v) ∉ starEdges G C := (Finset.mem_sdiff.mp he).2
  have hn : ¬ BelowF G C j := fun h => hnstar (carrier_below_star n G C hAO u v j hc h)
  have hex : ∃ x : Fin n → Bool, gateVal n C j x = true ∧ graphFun G ∅ x = false := by
    unfold BelowF at hn
    push Not at hn
    obtain ⟨x, hxt, hxf⟩ := hn
    exact ⟨x, hxt, Bool.eq_false_iff.mpr hxf⟩
  change j ∈ (Finset.range C.gates.length).filter (fun k => IsDirtyAnd n G C k)
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr hc.1, hc.2.1, hc.1, hex⟩

/-- The structural carrier bridge. In fact TopForm and leastness are unnecessary. -/
theorem residual_unique_carrier (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (u v : Fin n) (he : s(u, v) ∈ Ustar G C) :
    ∃! j : ℕ, IsCarrier n C u v j ∧ j ∈ junk G C := by
  have huv : G.Adj u v := by
    have heG := (Finset.mem_sdiff.mp he).1
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heG
  obtain ⟨j, hj⟩ := carrier_exists n G C (ao2_mono hAO) hfun u v huv
  refine ⟨j, ⟨hj, residual_carrier_junk n G C hAO u v j he hj⟩, ?_⟩
  intro k hk
  exact carrier_unique hk.1 hj

theorem residual_carried_cover (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) :
    Ustar G C ⊆ (junk G C).biUnion
      (fun j => (carried n G C j).image (fun p => s(p.1, p.2))) := by
  intro e he
  have hrepr : ∃ u v : Fin n, u < v ∧ e = s(u, v) := by
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := by
        have h := (Finset.mem_sdiff.mp he).1
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using h
      rcases lt_or_gt_of_ne (G.ne_of_adj huv) with h | h
      · exact ⟨u, v, h, rfl⟩
      · exact ⟨v, u, h, Sym2.eq_swap⟩
  obtain ⟨u, v, hlt, rfl⟩ := hrepr
  obtain ⟨j, ⟨hj, hjunk⟩, _⟩ := residual_unique_carrier n G C hAO hfun u v he
  have huv : G.Adj u v := by
    have h := (Finset.mem_sdiff.mp he).1
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using h
  have hcarried : (u, v) ∈ carried n G C j := by
    change (u, v) ∈ Finset.univ.filter
      (fun p : Fin n × Fin n => p.1 < p.2 ∧ Carries n G C j p.1 p.2)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, huv, hj⟩
  exact Finset.mem_biUnion.mpr ⟨j, hjunk,
    Finset.mem_image.mpr ⟨(u, v), hcarried, rfl⟩⟩

/-- A counting consequence of the new structural bridge. The reverse task, bounding
    the total number of junk-carried edges by circuit size, remains open. -/
theorem residual_card_le_sum_carried (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) :
    (Ustar G C).card ≤ ∑ j ∈ junk G C, (carried n G C j).card := by
  calc
    (Ustar G C).card ≤ ((junk G C).biUnion
        (fun j => (carried n G C j).image (fun p => s(p.1, p.2)))).card :=
      Finset.card_le_card (residual_carried_cover n G C hAO hfun)
    _ ≤ ∑ j ∈ junk G C, ((carried n G C j).image (fun p => s(p.1, p.2))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ j ∈ junk G C, (carried n G C j).card := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.card_image_le

lemma mem_carried_iff (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (p : Fin n × Fin n) :
    p ∈ carried n G C j ↔
      p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ IsCarrier n C p.1 p.2 j := by
  change p ∈ Finset.univ.filter (fun q : Fin n × Fin n =>
    q.1 < q.2 ∧ Carries n G C j q.1 q.2) ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Carries]

/-- Unique earliest-live carriers give disjoint edge sets for different gates.
    This uses no gate-basis or correctness assumption. -/
theorem carried_disjoint (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (i j : ℕ) (hij : i ≠ j) :
    Disjoint (carried n G C i) (carried n G C j) := by
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  have hi := (mem_carried_iff n G C i p).mp hpi
  have hj := (mem_carried_iff n G C j p).mp hpj
  exact hij (carrier_unique hi.2.2 hj.2.2)

lemma ordered_pair_sym2_injective {n : ℕ} (p q : Fin n × Fin n)
    (hp : p.1 < p.2) (hq : q.1 < q.2) (heq : s(p.1, p.2) = s(q.1, q.2)) : p = q := by
  rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · exfalso
    rw [h1, h2] at hp
    exact (lt_asymm hp hq)

/-- Any chosen finite family of carriers counts each graph edge at most once.
    In particular this holds for junk gates even without circuit correctness. -/
theorem sum_carried_le_edges (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (J : Finset ℕ) :
    (∑ j ∈ J, (carried n G C j).card) ≤ G.edgeFinset.card := by
  let U := J.biUnion (carried n G C)
  have hdisj : (J : Set ℕ).PairwiseDisjoint (carried n G C) := by
    intro i _ j _ hij
    exact carried_disjoint n G C i j hij
  have hcard : U.card = ∑ j ∈ J, (carried n G C j).card :=
    Finset.card_biUnion hdisj
  have hordered : ∀ p ∈ U, p.1 < p.2 := by
    intro p hp
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
    exact ((mem_carried_iff n G C j p).mp hj).1
  have hinj : Set.InjOn (fun p : Fin n × Fin n => s(p.1, p.2)) (U : Set _) := by
    intro p hp q hq heq
    exact ordered_pair_sym2_injective p q (hordered p hp) (hordered q hq) heq
  have hsub : U.image (fun p => s(p.1, p.2)) ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
    have hadj := ((mem_carried_iff n G C j p).mp hj).2.1
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hadj
  calc
    (∑ j ∈ J, (carried n G C j).card) = U.card := hcard.symm
    _ = (U.image (fun p => s(p.1, p.2))).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ G.edgeFinset.card := Finset.card_le_card hsub

theorem sum_junk_carried_le_edges (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) :
    (∑ j ∈ junk G C, (carried n G C j).card) ≤ G.edgeFinset.card :=
  sum_carried_le_edges n G C (junk G C)

end PEqualNP.Outside.L_meta_1710.CarrierBridge

