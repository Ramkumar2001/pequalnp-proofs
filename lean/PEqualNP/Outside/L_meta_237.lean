import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_237

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def conv (g : Gate) : BinaryGate :=
  match g.op, g.inputs with
  | GateOp.and, [] => ⟨fun _ _ => true, 0, 0⟩
  | GateOp.and, [i] => ⟨fun a _ => a, i, i⟩
  | GateOp.and, i :: j :: _ => ⟨fun a b => a && b, i, j⟩
  | GateOp.or, [] => ⟨fun _ _ => false, 0, 0⟩
  | GateOp.or, [i] => ⟨fun a _ => a, i, i⟩
  | GateOp.or, i :: j :: _ => ⟨fun a b => a || b, i, j⟩
  | GateOp.not, [] => ⟨fun _ _ => true, 0, 0⟩
  | GateOp.not, i :: _ => ⟨fun a _ => !a, i, i⟩
  | _, _ => ⟨fun _ _ => false, 0, 0⟩

lemma conv_eval (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List Bool) :
    (conv g).op (w.getD (conv g).left false) (w.getD (conv g).right false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hl
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
  all_goals first
    | (exfalso; simp only [List.length_cons, List.length_nil] at hl; omega)
    | (rcases hop with rfl | rfl | rfl <;> simp [conv, GateOp.eval])

lemma wires_eq (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List Bool) :
    (gs.map conv).foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) w =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [conv_eval g (hg g (by simp)) w]
    exact ih (fun z hz => hg z (by simp [hz])) _

end PEqualNP.Outside.L_meta_237

theorem PEqualNP.Outside.L_meta_237 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), PEqualNP.MetaComplexity.HasCircuitSize n f s → PEqualNP.MetaComplexity.HasBinarySize n f s := by
  intro n f s ⟨C, hC, hs, he⟩
  refine ⟨⟨C.gates.map PEqualNP.Outside.L_meta_237.conv, C.output⟩, ?_, ?_⟩
  · simpa [PEqualNP.MetaComplexity.BinaryCircuit.size, PEqualNP.CircuitLowerBounds.Circuit.size] using hs
  · intro x
    rw [← he x]
    simp only [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires, PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
    rw [PEqualNP.Outside.L_meta_237.wires_eq C.gates hC]
