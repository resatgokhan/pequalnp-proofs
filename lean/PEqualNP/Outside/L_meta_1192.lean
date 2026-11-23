import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1192

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨.or, [0, 4]⟩,
    ⟨.or, [8, 5]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.and, [2, 11]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [3, 13]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [15, 14]⟩]
  output := 16

lemma monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro gate hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma computesEdges : ∀ a b c d e f g h : Bool,
    circuit.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (a && d) || (b && e) ||
       (b && f) || (c && g) || (d && h)) := by
  decide

end PEqualNP.Outside.L_meta_1192

open PEqualNP.Outside.L_meta_1192

theorem PEqualNP.Outside.L_meta_1192 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) x := by
  refine ⟨circuit, monotone, by decide, ?_⟩
  intro x
  have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    simp [List.ofFn_succ]
  rw [inputs]
  exact computesEdges (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
