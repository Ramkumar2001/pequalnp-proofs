import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_240

open PEqualNP.MetaComplexity

lemma zero_gates_false (n : ℕ) (o : ℕ) :
    (BinaryCircuit.mk [] o).eval (List.ofFn (fun _ : Fin n => false)) = false := by
  simp only [BinaryCircuit.eval, BinaryCircuit.wires, List.foldl_nil]
  rw [List.getD_eq_getElem?_getD]
  by_cases h : o < n
  · simp [h]
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

end PEqualNP.Outside.L_meta_240

theorem PEqualNP.Outside.L_meta_240 : ∀ n s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => true) s ↔ 1 ≤ s := by
  intro n s
  constructor
  · rintro ⟨⟨gs, o⟩, hs, he⟩
    by_contra h
    have h0 : gs = [] := by
      simp only [PEqualNP.MetaComplexity.BinaryCircuit.size] at hs
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst h0
    have := he (fun _ => false)
    rw [PEqualNP.Outside.L_meta_240.zero_gates_false] at this
    exact Bool.false_ne_true this
  · intro h
    refine ⟨⟨[⟨fun _ _ => true, 0, 0⟩], n⟩, by simpa [PEqualNP.MetaComplexity.BinaryCircuit.size] using h, ?_⟩
    intro x
    simp [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires]
