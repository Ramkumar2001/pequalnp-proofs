import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2533

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def mapG (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

lemma getD_step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  unfold step
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_step_eq (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold step
  rw [List.getD_eq_getElem?_getD]
  simp

lemma getD_step_gt (w : List Bool) (g : Gate) (i : ℕ) (h : w.length + 1 ≤ i) :
    (step w g).getD i false = false := by
  unfold step
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
  rfl

lemma getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma len_step (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih, len_step]; simp; omega

lemma foldl_getD (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by rw [len_step]; omega), getD_step_lt w g i h]

-- one stage of rewiring: a fixed index map r turns the old run into the new run
lemma sim (r : ℕ → ℕ) : ∀ (gs : List Gate) (W V : List Bool),
    (∀ i, W.getD i false = V.getD (r i) false) →
    (∀ k < gs.length, r (W.length + k) = V.length + k) →
    (∀ k ≤ gs.length, ∀ i, W.length + k ≤ i → V.length + k ≤ r i) →
    (∀ i < W.length, r i < V.length ∨ V.length + gs.length ≤ r i) →
    ∀ i, (gs.foldl step W).getD i false = ((gs.map (mapG r)).foldl step V).getD (r i) false := by
  intro gs
  induction gs with
  | nil => intro W V hinv _ _ _ i; exact hinv i
  | cons g gs ih =>
    intro W V hinv hcur hfut hpast
    simp only [List.foldl_cons, List.map_cons]
    have hval : g.op.eval (g.inputs.map fun i => W.getD i false) =
        (mapG r g).op.eval ((mapG r g).inputs.map fun i => V.getD i false) := by
      simp only [mapG, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact hinv j
    have hr0 : r W.length = V.length := by simpa using hcur 0 (by simp)
    apply ih
    · intro i
      rcases lt_trichotomy i W.length with h | h | h
      · rw [getD_step_lt W g i h, hinv i]
        rcases hpast i h with h' | h'
        · rw [getD_step_lt V _ _ h']
        · rw [getD_ge V _ (by simp at h'; omega), getD_step_gt V _ _ (by simp at h'; omega)]
      · subst h
        rw [getD_step_eq, hr0, getD_step_eq, hval]
      · rw [getD_step_gt W g i (by omega)]
        have := hfut 1 (by simp) i (by omega)
        rw [getD_step_gt V _ _ (by omega)]
    · intro k hk
      rw [len_step, len_step]
      have := hcur (k + 1) (by simp; omega)
      rw [show W.length + 1 + k = W.length + (k + 1) by omega, this]; omega
    · intro k hk i hi
      rw [len_step] at hi ⊢
      have := hfut (k + 1) (by simp; omega) i (by omega)
      omega
    · intro i hi
      rw [len_step] at hi ⊢
      rcases Nat.lt_or_ge i W.length with h | h
      · rcases hpast i h with h' | h'
        · left; omega
        · right; simp at h'; omega
      · left; have : i = W.length := by omega
        subst this; omega

end PEqualNP.Outside.L_meta_2533

theorem PEqualNP.Outside.L_meta_2533 : ∀ (x1 : ℕ) (x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 : List ℕ) (x5 : ℕ),   x1 ∈ x4 →     have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x4 : PEqualNP.CircuitLowerBounds.Gate } :: x3, output := x5 : PEqualNP.CircuitLowerBounds.Circuit };     PEqualNP.MetaComplexity.FanInTwo x7 → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x9 : Fin x1 → Bool) => x7.eval (List.ofFn x9 ++ [Bool.false])) (x2.length + x3.length) := by
  intro n A B ins o hmem
  simp only []
  intro hfan
  classical
  let big := n + A.length + B.length
  let rA : ℕ → ℕ := fun i => if i < n then i else if i = n then big else
    if i < n + 1 + A.length then i - 1 else big
  let orT : ℕ := match ins.find? (fun j => decide (j ≠ n)) with
    | some y => rA y
    | none => big
  let rB : ℕ → ℕ := fun i => if i < n + 1 + A.length then rA i else
    if i = n + 1 + A.length then orT else i - 2
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨A.map (PEqualNP.Outside.L_meta_2533.mapG rA) ++ B.map (PEqualNP.Outside.L_meta_2533.mapG rB), rB o⟩
  have hgmem : ∀ g ∈ A ++ ⟨PEqualNP.CircuitLowerBounds.GateOp.or, ins⟩ :: B,
      g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2 := hfan
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    simp only [D, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩ | ⟨g0, hg0, rfl⟩
    · have := hgmem g0 (by simp [hg0])
      exact ⟨this.1, by simpa [PEqualNP.Outside.L_meta_2533.mapG] using this.2⟩
    · have := hgmem g0 (by simp [hg0])
      exact ⟨this.1, by simpa [PEqualNP.Outside.L_meta_2533.mapG] using this.2⟩
  · simp [D, PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x
    let W0 : List Bool := List.ofFn x ++ [false]
    let V0 : List Bool := List.ofFn x
    have hW0 : W0.length = n + 1 := by simp [W0]
    have hV0 : V0.length = n := by simp [V0]
    -- stage A
    have invA0 : ∀ i, W0.getD i false = V0.getD (rA i) false := by
      intro i
      by_cases h1 : i < n
      · simp only [rA, if_pos h1, W0, V0]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h1)]
      · by_cases h2 : i = n
        · subst h2
          simp only [rA, lt_irrefl, if_false, if_true]
          rw [PEqualNP.Outside.L_meta_2533.getD_ge V0 _ (by simp [V0, big]; omega)]
          simp [W0, List.getD_eq_getElem?_getD]
        · rw [PEqualNP.Outside.L_meta_2533.getD_ge W0 _ (by omega)]
          simp only [rA, if_neg h1, if_neg h2]
          split_ifs
          · rw [PEqualNP.Outside.L_meta_2533.getD_ge V0 _ (by omega)]
          · rw [PEqualNP.Outside.L_meta_2533.getD_ge V0 _ (by simp [V0, big]; omega)]
    have simA := PEqualNP.Outside.L_meta_2533.sim rA A W0 V0 invA0
      (by intro k hk; simp only [rA, hW0, hV0]; split_ifs <;> omega)
      (by intro k hk i hi; simp only [rA, hW0, hV0] at hi ⊢; split_ifs <;> simp [big] at * <;> omega)
      (by intro i hi; simp only [rA, hW0, hV0] at hi ⊢; split_ifs <;> simp [big] at * <;> omega)
    let WA := A.foldl PEqualNP.Outside.L_meta_2533.step W0
    let VA := (A.map (PEqualNP.Outside.L_meta_2533.mapG rA)).foldl PEqualNP.Outside.L_meta_2533.step V0
    have hWA : WA.length = n + 1 + A.length := by simp [WA, PEqualNP.Outside.L_meta_2533.foldl_len, hW0]
    have hVA : VA.length = n + A.length := by simp [VA, PEqualNP.Outside.L_meta_2533.foldl_len, hV0]
    have hWAn : WA.getD n false = false := by
      rw [PEqualNP.Outside.L_meta_2533.foldl_getD A W0 n (by omega)]
      simp [W0, List.getD_eq_getElem?_getD]
    -- the OR gate's value is the value of its other input
    have hor : (⟨PEqualNP.CircuitLowerBounds.GateOp.or, ins⟩ : PEqualNP.CircuitLowerBounds.Gate).op.eval
        (ins.map fun i => WA.getD i false) = VA.getD orT false := by
      have hl : ins.length ≤ 2 := (hgmem ⟨PEqualNP.CircuitLowerBounds.GateOp.or, ins⟩ (by simp)).2
      have hcase : ins = [n] ∨ ins = [n, n] ∨ (∃ b, b ≠ n ∧ ins = [n, b]) ∨ (∃ a, a ≠ n ∧ ins = [a, n]) := by
        rcases hins : ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · rw [hins] at hmem; simp at hmem
        · rw [hins] at hmem; simp at hmem; subst hmem; left; rfl
        · rw [hins] at hmem; simp at hmem
          by_cases ha : a = n
          · subst ha
            by_cases hb : b = a
            · subst hb; right; left; rfl
            · right; right; left; exact ⟨b, hb, rfl⟩
          · have hb : b = n := by tauto
            subst hb; right; right; right; exact ⟨a, ha, rfl⟩
        · rw [hins] at hl; simp at hl
      have hbig : VA[big]? = none := List.getElem?_eq_none (by rw [hVA]; simp [big])
      have hWAn' : WA[n]?.getD false = false := by simpa [List.getD_eq_getElem?_getD] using hWAn
      simp only [orT]
      rcases hcase with h | h | ⟨b, hb, h⟩ | ⟨a, ha, h⟩ <;> rw [h]
      · simp [PEqualNP.CircuitLowerBounds.GateOp.eval, List.getD_eq_getElem?_getD, hWAn', hbig]
      · simp [PEqualNP.CircuitLowerBounds.GateOp.eval, List.getD_eq_getElem?_getD, hWAn', hbig]
      · have := simA b
        simp only [List.getD_eq_getElem?_getD] at this
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval, List.getD_eq_getElem?_getD, hWAn', hb]
        exact this
      · have := simA a
        simp only [List.getD_eq_getElem?_getD] at this
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval, List.getD_eq_getElem?_getD, hWAn', ha]
        exact this
    -- stage B
    let W1 := PEqualNP.Outside.L_meta_2533.step WA ⟨PEqualNP.CircuitLowerBounds.GateOp.or, ins⟩
    have hW1 : W1.length = n + 2 + A.length := by simp [W1, PEqualNP.Outside.L_meta_2533.len_step, hWA]; omega
    have invB : ∀ i, W1.getD i false = VA.getD (rB i) false := by
      intro i
      rcases lt_trichotomy i (n + 1 + A.length) with h | h | h
      · rw [PEqualNP.Outside.L_meta_2533.getD_step_lt WA _ i (by omega)]
        simp only [rB, if_pos h]
        exact simA i
      · subst h
        have := PEqualNP.Outside.L_meta_2533.getD_step_eq WA ⟨PEqualNP.CircuitLowerBounds.GateOp.or, ins⟩
        rw [hWA] at this
        simp only [W1, this, rB, lt_irrefl, if_false, if_true]
        exact hor
      · rw [PEqualNP.Outside.L_meta_2533.getD_step_gt WA _ i (by omega)]
        simp only [rB, if_neg (show ¬ i < n + 1 + A.length by omega), if_neg (show i ≠ n + 1 + A.length by omega)]
        rw [PEqualNP.Outside.L_meta_2533.getD_ge VA _ (by omega)]
    have horT : orT < n + A.length ∨ n + A.length + B.length ≤ orT := by
      simp only [orT]
      split
      · simp only [rA]; split_ifs <;> simp [big] at * <;> omega
      · right; simp [big]
    have simB := PEqualNP.Outside.L_meta_2533.sim rB B W1 VA invB
      (by intro k hk; simp only [rB, hW1, hVA]; split_ifs <;> omega)
      (by intro k hk i hi; simp only [rB, hW1, hVA] at hi ⊢; split_ifs <;> omega)
      (by
        intro i hi
        rw [hW1] at hi
        rw [hVA]
        simp only [rB]
        split_ifs with h1 h2
        · simp only [rA]; split_ifs <;> simp [big] at * <;> omega
        · exact horT
        · omega)
    have e1 : PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨A ++ ⟨PEqualNP.CircuitLowerBounds.GateOp.or, ins⟩ :: B, o⟩ (List.ofFn x ++ [false]) =
        (B.foldl PEqualNP.Outside.L_meta_2533.step W1).getD o false := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
        List.foldl_append, List.foldl_cons]
      rfl
    have e2 : D.eval (List.ofFn x) =
        ((B.map (PEqualNP.Outside.L_meta_2533.mapG rB)).foldl PEqualNP.Outside.L_meta_2533.step VA).getD (rB o) false := by
      simp only [D, PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
        List.foldl_append]
      rfl
    show D.eval (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval
      ⟨A ++ ⟨PEqualNP.CircuitLowerBounds.GateOp.or, ins⟩ :: B, o⟩ (List.ofFn x ++ [false])
    rw [e2, e1]
    exact (simB o).symm
