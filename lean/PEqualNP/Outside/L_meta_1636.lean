import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1636

open PEqualNP.CircuitLowerBounds

def Le (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

lemma op_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : List Bool)
    (h : ∀ i, a.getD i false = true → b.getD i false = true) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] <;> simp only [GateOp.eval]
  · simp only [List.all_map, List.all_eq_true, Function.comp, id]
    exact fun ha j hj => h j (ha j hj)
  · simp only [List.any_map, List.any_eq_true, Function.comp, id]
    rintro ⟨j, hj, ha⟩
    exact ⟨j, hj, h j ha⟩

lemma step_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : List Bool)
    (h : Le a b) :
    Le (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
      (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]) := by
  obtain ⟨hlen, hle⟩ := h
  refine ⟨by simp [hlen], ?_⟩
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  rcases lt_trichotomy i a.length with hlt | heq | hgt
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (hlen ▸ hlt)]
    have := hle i (by rw [List.getD_eq_getElem?_getD]; exact hi)
    rwa [List.getD_eq_getElem?_getD] at this
  · subst heq
    rw [List.getElem?_append_right (le_refl _)] at hi
    rw [hlen, List.getElem?_append_right (le_refl _)]
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
    exact op_mono g hg a b hle hi
  · rw [List.getElem?_eq_none (by simp; omega)] at hi
    simp at hi

lemma foldl_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, Le a b →
      Le (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b) := by
  induction gs with
  | nil => intro a b h; exact h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons]
    exact ih (fun z hz => hgs z (by simp [hz])) _ _ (step_le g (hgs g (by simp)) a b h)

lemma eval_mono {N : ℕ} (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) :
    Circuit.eval ⟨gs, w⟩ (List.ofFn x) = true → Circuit.eval ⟨gs, w⟩ (List.ofFn y) = true := by
  have base : Le (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases h : i < N
    · rw [List.getD_eq_getElem _ _ (by simpa using h)] at hi ⊢
      simp only [List.getElem_ofFn] at hi ⊢
      exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      exact absurd hi (by simp)
  intro hx
  exact (foldl_le gs hgs _ _ base).2 w hx

lemma two_points {N : ℕ} (L : Fin N → Finset (Fin N))
    (hinter : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) (i j : Fin N) (hij : i ≠ j)
    (a b : Fin N) (ha : a ∈ L i) (ha' : a ∈ L j) (hb : b ∈ L i) (hb' : b ∈ L j) : a = b := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hinter i j hij)
  have h1 : a ∈ L i ∩ L j := Finset.mem_inter.mpr ⟨ha, ha'⟩
  have h2 : b ∈ L i ∩ L j := Finset.mem_inter.mpr ⟨hb, hb'⟩
  rw [hc, Finset.mem_singleton] at h1 h2
  rw [h1, h2]

end PEqualNP.Outside.L_meta_1636

theorem PEqualNP.Outside.L_meta_1636 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ w : ℕ,
    (∀ m l : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → (p0 ∈ L l ∧ p1 ∉ L l) → ev w (fun v : Fin N => decide (v ∉ L m)) = false → (∃ p ∈ L l, ev w (T l p) = true) →
      ∀ l' : Fin N, (p0 ∈ L l' ∧ p1 ∉ L l') → l' ≠ l → ev w (fun v : Fin N => decide (v ∉ L l')) = true) ∧
    (∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) → ev w (fun v : Fin N => decide (v ∉ L l)) = false → (∃ p ∈ L m, ev w (T m p) = true) →
      ∀ m' : Fin N, (p1 ∈ L m' ∧ p0 ∉ L m') → m' ≠ m → ev w (fun v : Fin N => decide (v ∉ L m')) = true) ∧
    (∀ m M : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → ev w (fun v : Fin N => decide (v ∉ L m)) = false → (p0 ∉ L M ∧ p1 ∉ L M) → ((L M).filter (fun p => ev w (T M p) = true)).card ≤ 1) := by
  intro q N L i0 p0 p1 _ _ _ hinter _ hp01 _ _ T hT gates hg _ _ ev hev w
  have mono : ∀ x y : Fin N → Bool, (∀ v, x v = true → y v = true) →
      ev w x = true → ev w y = true := by
    intro x y hxy hx
    rw [hev] at hx ⊢
    exact PEqualNP.Outside.L_meta_1636.eval_mono gates (fun g hgm => (hg g hgm).1) w x y hxy hx
  have two := PEqualNP.Outside.L_meta_1636.two_points L hinter
  refine ⟨?_, ?_, ?_⟩
  · intro m l hm hl hcm hex l' hl' hll'
    obtain ⟨p, hpl, hpT⟩ := hex
    by_cases hpp : p = p0
    · exfalso
      have hc : ev w (fun v : Fin N => decide (v ∉ L m)) = true := by
        refine mono _ _ (fun v hv => ?_) hpT
        rw [hT] at hv
        have hv0 : v = p0 := by
          rcases hv with h | h | h | h
          · exact h.trans hpp
          · exact absurd hl.1 h.1
          · exact absurd hpp h.2.2.1
          · exact absurd h.2.1 hl.2
        rw [hv0]
        simpa using hm.2
      rw [hcm] at hc
      exact Bool.false_ne_true hc
    · refine mono _ _ (fun v hv => ?_) hpT
      rw [hT] at hv
      have hv' : v = p ∨ v = p1 := by
        rcases hv with h | h | h | h
        · exact Or.inl h
        · exact absurd hl.1 h.1
        · exact Or.inr h.2.2.2
        · exact absurd h.2.1 hl.2
      rcases hv' with rfl | rfl
      · have : v ∉ L l' := fun hvl' =>
          hpp (two l l' (Ne.symm hll') v p0 hpl hvl' hl.1 hl'.1)
        simpa using this
      · simpa using hl'.2
  · intro l m hl hm hcl hex m' hm' hmm'
    obtain ⟨p, hpm, hpT⟩ := hex
    by_cases hpp : p = p1
    · exfalso
      have hc : ev w (fun v : Fin N => decide (v ∉ L l)) = true := by
        refine mono _ _ (fun v hv => ?_) hpT
        rw [hT] at hv
        have hv1 : v = p1 := by
          rcases hv with h | h | h | h
          · exact h.trans hpp
          · exact absurd hpp h.2.1
          · exact absurd h.1 hm.2
          · exact absurd h.1 hm.2
        rw [hv1]
        simpa using hl.2
      rw [hcl] at hc
      exact Bool.false_ne_true hc
    · refine mono _ _ (fun v hv => ?_) hpT
      rw [hT] at hv
      have hv' : v = p ∨ v = p0 := by
        rcases hv with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h.2.2
        · exact absurd h.1 hm.2
        · exact absurd h.1 hm.2
      rcases hv' with rfl | rfl
      · have : v ∉ L m' := fun hvm' =>
          hpp (two m m' (Ne.symm hmm') v p1 hpm hvm' hm.1 hm'.1)
        simpa using this
      · simpa using hm'.2
  · intro m M hm hcm hM
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    have hMm : M ≠ m := fun e => hM.2 (e ▸ hm.1)
    have hsupp : ∀ p v : Fin N, T M p v = true → v = p ∨ v = p0 := by
      intro p v hv
      rw [hT] at hv
      rcases hv with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h.2.2
      · exact absurd h.1 hM.1
      · exact absurd h.1 hM.1
    have inm : ∀ p : Fin N, ev w (T M p) = true → p ∈ L m := by
      intro p hp
      by_contra hpm
      have hc : ev w (fun v : Fin N => decide (v ∉ L m)) = true := by
        refine mono _ _ (fun v hv => ?_) hp
        rcases hsupp p v hv with rfl | rfl
        · simpa using hpm
        · simpa using hm.2
      rw [hcm] at hc
      exact Bool.false_ne_true hc
    exact two M m hMm a b ha.1 (inm a ha.2) hb.1 (inm b hb.2)
