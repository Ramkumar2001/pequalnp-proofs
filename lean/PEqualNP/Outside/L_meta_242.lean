import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_242

open PEqualNP.MetaComplexity

lemma getD_append_false (W : List Bool) (o : ℕ) :
    (W ++ [false]).getD o false = W.getD o false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases lt_trichotomy o W.length with h | h | h
  · rw [List.getElem?_append_left h]
  · subst h
    simp
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

end PEqualNP.Outside.L_meta_242

theorem PEqualNP.Outside.L_meta_242 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), PEqualNP.MetaComplexity.HasBinarySize n f s → PEqualNP.MetaComplexity.HasBinarySize n f (s + 1) := by
  intro n f s ⟨C, hs, he⟩
  refine ⟨⟨C.gates ++ [⟨fun _ _ => false, 0, 0⟩], C.output⟩, ?_, ?_⟩
  · simp only [PEqualNP.MetaComplexity.BinaryCircuit.size, List.length_append, List.length_singleton] at hs ⊢
    omega
  · intro x
    rw [← he x]
    simp only [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact PEqualNP.Outside.L_meta_242.getD_append_false _ _
