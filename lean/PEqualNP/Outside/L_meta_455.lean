import PEqualNP.Defs

-- Offline candidate prepared without a task lease.
-- This candidate has not been submitted to the project.

theorem PEqualNP.Outside.L_meta_455 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)) →
    (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
    ∀ u v : Fin n, G.Adj u v →
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w), ¬ G.Adj a b) ∧
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj u w),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj u w), ¬ G.Adj a b) ∧
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
              Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
              Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v), ¬ G.Adj a b) := by
  intro n G _ htri hfour u v huv
  have hneighbour (w a b : Fin n) (hwa : G.Adj w a) (hwb : G.Adj w b) :
      ¬ G.Adj a b := by
    intro hab
    exact htri w a b ⟨hwa, hab, hwb.symm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    exact hneighbour v a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  · intro a ha b hb
    exact hneighbour u a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  · intro a ha b hb hab
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases Finset.mem_union.mp hb with hb | hb
      · exact hneighbour v a b (Finset.mem_filter.mp ha).2.1
          (Finset.mem_filter.mp hb).2.1 hab
      · rcases (Finset.mem_filter.mp ha).2 with ⟨hva, hau⟩
        rcases (Finset.mem_filter.mp hb).2 with ⟨hub, hbv⟩
        exact hfour u v a b (Ne.symm hau) (Ne.symm hbv)
          ⟨huv, hva, hab, hub.symm⟩
    · rcases Finset.mem_union.mp hb with hb | hb
      · rcases (Finset.mem_filter.mp ha).2 with ⟨hua, hav⟩
        rcases (Finset.mem_filter.mp hb).2 with ⟨hvb, hbu⟩
        exact hfour u v b a (Ne.symm hbu) (Ne.symm hav)
          ⟨huv, hvb, hab.symm, hua.symm⟩
      · exact hneighbour u a b (Finset.mem_filter.mp ha).2.1
          (Finset.mem_filter.mp hb).2.1 hab
