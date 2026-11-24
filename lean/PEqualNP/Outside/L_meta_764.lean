import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

theorem PEqualNP.Outside.L_meta_764 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s := by
  intro s
  let g : (Fin 3 → Bool) → Bool :=
    fun x => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)
  have hnc : ∃ y y' : Fin 3 → Bool, g y ≠ g y' := by
    refine ⟨(fun _ => false), (fun _ => true), ?_⟩
    decide
  have hshift : ∀ t : ℕ,
      PEqualNP.MetaComplexity.HasCircuitSize 5
        (fun x : Fin 5 → Bool =>
          (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4))
        (t + 2) ↔ 4 ≤ t := by
    intro t
    have h := (PEqualNP.MetaComplexity.L153 3 t g hnc).trans
      (PEqualNP.MetaComplexity.L100 t)
    simpa [g, Fin.castAdd, Fin.castLE, Fin.natAdd, Bool.or_assoc] using h
  by_cases hs : 2 ≤ s
  · have he : s - 2 + 2 = s := by omega
    have ht := hshift (s - 2)
    rw [he] at ht
    exact ht.trans (by constructor <;> intro h <;> omega)
  · constructor
    · intro h
      have htwo : PEqualNP.MetaComplexity.HasCircuitSize 5
          (fun x : Fin 5 → Bool =>
            (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) 2 := by
        rcases h with ⟨C, hfan, hsize, heval⟩
        exact ⟨C, hfan, le_trans hsize (by omega), heval⟩
      have hz : 4 ≤ 0 := (hshift 0).mp htwo
      omega
    · intro h
      omega
