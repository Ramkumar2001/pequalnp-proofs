import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_238

open PEqualNP.MetaComplexity

lemma no_gates (o : ℕ) (x : Fin 2 → Bool) :
    (BinaryCircuit.mk [] o).eval (List.ofFn x) = [x 0, x 1].getD o false := by
  simp [BinaryCircuit.eval, BinaryCircuit.wires, List.ofFn_succ]

end PEqualNP.Outside.L_meta_238

theorem PEqualNP.Outside.L_meta_238 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasBinarySize 2 (fun x : Fin 2 → Bool => xor (x 0) (x 1)) s ↔ 1 ≤ s := by
  intro s
  constructor
  · rintro ⟨⟨gs, o⟩, hs, he⟩
    by_contra h
    have h0 : gs = [] := by
      simp only [PEqualNP.MetaComplexity.BinaryCircuit.size] at hs
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst h0
    have h1 := he (fun _ => true)
    have h2 := he (fun i => decide (i = 0))
    have h3 := he (fun i => decide (i = 1))
    rw [PEqualNP.Outside.L_meta_238.no_gates] at h1 h2 h3
    rcases o with _ | _ | o <;> simp_all
  · intro h
    refine ⟨⟨[⟨fun a b => xor a b, 0, 1⟩], 2⟩, by simpa [PEqualNP.MetaComplexity.BinaryCircuit.size] using h, ?_⟩
    intro x
    simp [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires, List.ofFn_succ]
