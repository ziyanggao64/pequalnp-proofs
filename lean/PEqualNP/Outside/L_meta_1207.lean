import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1207

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨.or, [1, 2]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.and, [3, 10]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.and, [4, 12]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [15, 13]⟩,
    ⟨.or, [16, 14]⟩]
  output := 17

end PEqualNP.Outside.L_meta_1207

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_1207 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1207.circuit, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1207.circuit]
  · intro x
    simp [PEqualNP.Outside.L_meta_1207.circuit,
      PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires,
      PEqualNP.CircuitLowerBounds.GateOp.eval,
      List.ofFn_succ, Bool.and_or_distrib_left]
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
      cases h3 : x 3 <;> cases h4 : x 4 <;> cases h5 : x 5 <;>
      cases h6 : x 6 <;> cases h7 : x 7 <;> simp_all
