import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

theorem PEqualNP.Outside.L_meta_765 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔ 5 ≤ s := by
  intro s
  let g : (Fin 4 → Bool) → Bool :=
    fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0)
  have hnc : ∃ y y' : Fin 4 → Bool, g y ≠ g y' := by
    refine ⟨(fun _ => false), (fun _ => true), ?_⟩
    decide
  have hshift : ∀ t : ℕ,
      PEqualNP.MetaComplexity.HasCircuitSize 6
        (fun x : Fin 6 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2))
        (t + 2) ↔ 3 ≤ t := by
    intro t
    have h := (PEqualNP.MetaComplexity.L153 4 t g hnc).trans
      (PEqualNP.MetaComplexity.L112 t)
    simpa [g, Fin.castAdd, Fin.castLE, Fin.natAdd, Bool.or_assoc] using h
  by_cases hs : 2 ≤ s
  · have he : s - 2 + 2 = s := by omega
    have ht := hshift (s - 2)
    rw [he] at ht
    exact ht.trans (by constructor <;> intro h <;> omega)
  · constructor
    · intro h
      have htwo : PEqualNP.MetaComplexity.HasCircuitSize 6
          (fun x : Fin 6 → Bool =>
            (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) 2 := by
        rcases h with ⟨C, hfan, hsize, heval⟩
        exact ⟨C, hfan, le_trans hsize (by omega), heval⟩
      have hz : 3 ≤ 0 := (hshift 0).mp htwo
      omega
    · intro h
      omega
