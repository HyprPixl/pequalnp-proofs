import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1376

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (h : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by rw [fold_length]; simp; omega)]
  rfl

theorem val_append_lt {n : ℕ} (gs hs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (h : i < n + gs.length) : val (gs ++ hs) x i = val gs x i := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, val_snoc, if_neg (by simp; omega), ih]

theorem val_gate {n : ℕ} (gs : List Gate) (k : ℕ) (g : Gate) (hk : gs[k]? = some g)
    (x : Fin n → Bool) :
    val gs x (n + k) = g.op.eval (g.inputs.map fun a =>
      if a < n + k then val gs x a else false) := by
  have hlt : k < gs.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hk
    exact absurd hk (by simp)
  have hsplit : gs = gs.take k ++ [g] ++ gs.drop (k + 1) := by
    have h1 : gs[k] = g := by
      rw [List.getElem?_eq_getElem hlt] at hk
      exact Option.some.inj hk
    conv_lhs => rw [← List.take_append_drop k gs]
    rw [List.drop_eq_getElem_cons hlt, h1]
    simp
  have htl : (gs.take k).length = k := by simp; omega
  have hL : val gs x (n + k) = g.op.eval (g.inputs.map fun j => val (gs.take k) x j) := by
    conv_lhs => rw [hsplit]
    rw [val_append_lt _ _ _ _ (by simp; omega), val_snoc, if_pos (by rw [htl])]
  rw [hL]
  congr 1
  apply List.map_congr_left
  intro a _
  split_ifs with ha
  · conv_rhs => rw [hsplit]
    rw [List.append_assoc, val_append_lt _ _ _ _ (by rw [htl]; omega)]
  · apply val_ge
    rw [htl]; omega

theorem val_snoc_lt {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ)
    (h : i < n + gs.length) : val (gs ++ [g]) x i = val gs x i :=
  val_append_lt gs [g] x i h

theorem lt_of_val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (h : val gs x i = true) : i < n + gs.length := by
  by_contra hc
  rw [val_ge gs x i (by omega)] at h
  exact absurd h (by simp)

theorem gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro _
        exact ⟨h, h, fun y hy => Or.inl hy.1⟩
      · refine ⟨b, b, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        exact ⟨hb, hb, fun y hy => Or.inl hy.2⟩
    · right
      refine ⟨a, b, ?_⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff]
      intro hz
      exact ⟨hz.1, hz.2, fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

def Zof {n : ℕ} (T : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ T)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Inv {n : ℕ} (T X : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, u ∈ X → v ∈ X → val gs (Zof T) i = false → val gs (eof u) i = true →
    val gs (eof v) i = true → u ∈ T ∧ l u = l v

def Good {n : ℕ} (T X : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  ∃ k a b, i = n + k ∧ gs[k]? = some ⟨GateOp.or, [a, b]⟩ ∧ a < i ∧ b < i ∧
    val gs (Zof T) a = false ∧ val gs (Zof T) b = false ∧
    ∃ u ∈ X, ∃ v ∈ X, u ≠ v ∧ val gs (eof u) a = true ∧ val gs (eof v) b = true

theorem Good_snoc {n : ℕ} (T X : Finset (Fin n)) (gs : List Gate) (g : Gate) (i : ℕ)
    (h : Good T X gs i) : Good T X (gs ++ [g]) i := by
  obtain ⟨k, a, b, hi, hk, ha, hb, hza, hzb, u, hu, v, hv, huv, hua, hvb⟩ := h
  have hlt : k < gs.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hk
    exact absurd hk (by simp)
  refine ⟨k, a, b, hi, ?_, ha, hb, ?_, ?_, u, hu, v, hv, huv, ?_, ?_⟩
  · rw [List.getElem?_append_left hlt]; exact hk
  · rw [val_snoc_lt _ _ _ _ (by omega)]; exact hza
  · rw [val_snoc_lt _ _ _ _ (by omega)]; exact hzb
  · rw [val_snoc_lt _ _ _ _ (by omega)]; exact hua
  · rw [val_snoc_lt _ _ _ _ (by omega)]; exact hvb

theorem good_of {n : ℕ} (T X : Finset (Fin n)) (gs : List Gate) (a b : ℕ)
    (hza : val gs (Zof T) a = false) (hzb : val gs (Zof T) b = false)
    (u v : Fin n) (hu : u ∈ X) (hv : v ∈ X) (huv : u ≠ v)
    (hua : val gs (eof u) a = true) (hvb : val gs (eof v) b = true) :
    Good T X (gs ++ [⟨GateOp.or, [a, b]⟩]) (n + gs.length) := by
  have ha := lt_of_val _ _ _ hua
  have hb := lt_of_val _ _ _ hvb
  refine ⟨gs.length, a, b, rfl, by simp, ha, hb, ?_, ?_, u, hu, v, hv, huv, ?_, ?_⟩
  · rw [val_snoc_lt _ _ _ _ ha]; exact hza
  · rw [val_snoc_lt _ _ _ _ hb]; exact hzb
  · rw [val_snoc_lt _ _ _ _ ha]; exact hua
  · rw [val_snoc_lt _ _ _ _ hb]; exact hvb

theorem merge_good {n : ℕ} (T X : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n)
    (g : Gate) (hinv : Inv T X gs l) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2)
    (hz : g.op.eval (g.inputs.map fun j => val gs (Zof T) j) = false)
    (u0 v0 : Fin n) (hu0 : u0 ∈ X) (hv0 : v0 ∈ X)
    (hu : g.op.eval (g.inputs.map fun j => val gs (eof u0) j) = true)
    (hv : g.op.eval (g.inputs.map fun j => val gs (eof v0) j) = true)
    (hne : l u0 ≠ l v0) :
    Good T X (gs ++ [g]) (n + gs.length) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen hz hu hv ⊢
  have huv : u0 ≠ v0 := fun h => hne (by rw [h])
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · simp [GateOp.eval] at hz
    · simp [GateOp.eval] at hu
  | [a], _ =>
    exfalso
    rcases hop with rfl | rfl <;> simp [GateOp.eval] at hz hu hv <;>
      exact hne (hinv a u0 v0 hu0 hv0 hz hu hv).2
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · exfalso
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        Bool.and_true, id_eq, Bool.and_eq_true, Bool.and_eq_false_iff] at hz hu hv
      rcases hz with hz | hz
      · exact hne (hinv a u0 v0 hu0 hv0 hz hu.1 hv.1).2
      · exact hne (hinv b u0 v0 hu0 hv0 hz hu.2 hv.2).2
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff] at hz hu hv
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact absurd (hinv a u0 v0 hu0 hv0 hz.1 hu hv).2 hne
      · exact good_of T X gs a b hz.1 hz.2 u0 v0 hu0 hv0 huv hu hv
      · exact good_of T X gs a b hz.1 hz.2 v0 u0 hv0 hu0 (Ne.symm huv) hv hu
      · exact absurd (hinv b u0 v0 hu0 hv0 hz.2 hu hv).2 hne
  | _ :: _ :: _ :: _, h => simp at h

theorem main_inv {n : ℕ} (T X : Finset (Fin n)) (gs : List Gate)
    (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hop : ∀ k g, gs[k]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∨
      val gs (Zof T) (n + k) = true) :
    ∃ (l : Fin n → Fin n) (M : Finset ℕ), Inv T X gs l ∧
      (T ∩ X).card ≤ ((T ∩ X).image l).card + M.card ∧ ∀ i ∈ M, Good T X gs i := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ∅, ?_, by simp, by simp⟩
    intro i u v _ _ hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      exact ⟨hz, rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    have hlen' : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' hg' => hlen g' (by simp [hg'])
    have hop' : ∀ k g', gs[k]? = some g' → (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∨
        val gs (Zof T) (n + k) = true := by
      intro k g' hk
      have hlt : k < gs.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hk
        exact absurd hk (by simp)
      rcases hop k g' (by rw [List.getElem?_append_left hlt]; exact hk) with h | h
      · exact Or.inl h
      · right
        rw [val_snoc_lt _ _ _ _ (by omega)] at h
        exact h
    obtain ⟨l, M, hinv, hcard, hgood⟩ := ih hlen' hop'
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, if_pos hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, if_neg hi]
    have hgood' : ∀ i ∈ M, Good T X (gs ++ [g]) i := fun i hi => Good_snoc T X gs g i (hgood i hi)
    rcases hop gs.length g (by simp) with hop | hnot
    swap
    · refine ⟨l, M, ?_, hcard, hgood'⟩
      intro i u v hu hv hiz hiu hiv
      by_cases hi : i = N
      · subst hi
        rw [hiz] at hnot
        exact absurd hnot (by simp)
      · rw [hold _ _ hi] at hiz hiu hiv
        exact hinv i u v hu hv hiz hiu hiv
    have hlg := hlen g (by simp)
    have key : P (Zof T) = false → ∀ u, u ∈ X → P (eof u) = true →
        u ∈ T ∧ ∃ A B : Fin n → Prop, (∀ w, P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', w ∈ X → w' ∈ X → A w → A w' → l w = l w') ∧
          (∀ w w', w ∈ X → w' ∈ X → B w → B w' → l w = l w') := by
      intro hz u huX hu
      rcases gate_cases g hop hlg (fun x j => val gs x j) (Zof T) with hall | ⟨a, b, hab⟩
      · have := hall (eof u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hz
        refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
          fun w hw => hy (eof w) hw, fun w w' hw hw' h h' => (hinv a w w' hw hw' ha h h').2,
          fun w w' hw hw' h h' => (hinv b w w' hw hw' hb h h').2⟩
        rcases hy (eof u) hu with h | h
        · exact (hinv a u u huX huX ha h h).1
        · exact (hinv b u u huX huX hb h h).1
    by_cases hm : P (Zof T) = false ∧ ∃ u v, u ∈ X ∧ v ∈ X ∧ P (eof u) = true ∧
        P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, hu0X, hv0X, hu0, hv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, insert N M, ?_, ?_, ?_⟩
      · intro i u v huX hvX hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, A, B, hAB, hA, hB⟩ := key hiz u huX hiu
          refine ⟨huS, ?_⟩
          have two : ∀ w, w ∈ X → P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hwX hw
            rcases hAB w hw with h | h <;> rcases hAB u0 hu0 with h0 | h0 <;>
              rcases hAB v0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 hwX hu0X h h0)
            · exact Or.inl (hA w u0 hwX hu0X h h0)
            · exact Or.inr (hA w v0 hwX hv0X h h1)
            · exact absurd (hB u0 v0 hu0X hv0X h0 h1) hne
            · exact absurd (hA u0 v0 hu0X hv0X h0 h1) hne
            · exact Or.inr (hB w v0 hwX hv0X h h1)
            · exact Or.inl (hB w u0 hwX hu0X h h0)
            · exact Or.inl (hB w u0 hwX hu0X h h0)
          have red : ∀ w, w ∈ X → P (eof w) = true →
              (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hwX hw
            rcases two w hwX hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [if_pos h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u huX hiu, red v hvX hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huS, hl⟩ := hinv i u v huX hvX hiz hiu hiv
          refine ⟨huS, ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : (T ∩ X).image l ⊆
            insert (l v0) ((T ∩ X).image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [if_neg h]
        have h1 : ((T ∩ X).image l).card ≤
            ((T ∩ X).image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNnot : N ∉ M := by
          intro h
          obtain ⟨k, a, b, hk, hget, -⟩ := hgood N h
          have hlt : k < gs.length := by
            by_contra hc
            rw [List.getElem?_eq_none (by omega)] at hget
            exact absurd hget (by simp)
          omega
        rw [Finset.card_insert_of_notMem hNnot]
        omega
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact merge_good T X gs l g hinv hop hlg hz u0 v0 hu0X hv0X hu0 hv0 hne
        · exact hgood' i hi
    · refine ⟨l, M, ?_, hcard, hgood'⟩
      intro i u v huX hvX hiz hiu hiv
      by_cases hi : i = N
      · subst hi
        rw [hnew] at hiz hiu hiv
        obtain ⟨huS, -⟩ := key hiz u huX hiu
        refine ⟨huS, ?_⟩
        by_contra hne
        exact hm ⟨hiz, u, v, huX, hvX, hiu, hiv, hne⟩
      · rw [hold _ _ hi] at hiz hiu hiv
        exact hinv i u v huX hvX hiz hiu hiv

theorem val_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val gs x i = x ⟨i, h⟩ := by
  have := val_append_lt [] gs x i (by simpa using h)
  simp only [List.nil_append] at this
  rw [this, val_nil, dif_pos h]

theorem lt_of_some {α : Type} (l : List α) (k : ℕ) (a : α) (h : l[k]? = some a) :
    k < l.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  exact absurd h (by simp)

theorem or_val {n : ℕ} (gs : List Gate) (k a b : ℕ)
    (hk : gs[k]? = some ⟨GateOp.or, [a, b]⟩) (ha : a < n + k) (hb : b < n + k)
    (x : Fin n → Bool) : val gs x (n + k) = (val gs x a || val gs x b) := by
  rw [val_gate gs k _ hk]
  simp [GateOp.eval, ha, hb]

theorem good_disj {n : ℕ} (T1 T2 X1 X2 : Finset (Fin n)) (gs : List Gate)
    (l1 l2 : Fin n → Fin n) (hinv1 : Inv T1 X1 gs l1) (hinv2 : Inv T2 X2 gs l2) (i : ℕ)
    (h1 : Good T1 X1 gs i) (h2 : Good T2 X2 gs i) :
    ∃ u v, u ≠ v ∧ u ∈ X1 ∧ v ∈ X1 ∧ u ∈ T1 ∧ v ∈ T1 ∧ (u ∈ X2 → u ∈ T2) ∧
      (v ∈ X2 → v ∈ T2) := by
  obtain ⟨k, a, b, hi, hk, -, -, hza, hzb, u, hu, v, hv, huv, hua, hvb⟩ := h1
  obtain ⟨k', a', b', hi', hk', -, -, hza', hzb', -⟩ := h2
  have hkk : k' = k := by omega
  subst hkk
  rw [hk] at hk'
  simp only [Option.some.injEq, Gate.mk.injEq, List.cons.injEq, and_true, true_and] at hk'
  obtain ⟨rfl, rfl⟩ := hk'
  exact ⟨u, v, huv, hu, hv, (hinv1 a u u hu hu hza hua hua).1, (hinv1 b v v hv hv hzb hvb hvb).1,
    fun h => (hinv2 a u u h h hza' hua hua).1, fun h => (hinv2 b v v h h hzb' hvb hvb).1⟩

theorem good_input {n : ℕ} (T X : Finset (Fin n)) (gs : List Gate) (i r c : ℕ) (g : Gate)
    (h : Good T X gs i) (hg : gs[r]? = some g) (hi : i = n + r) (hc : c ∈ g.inputs) :
    val gs (Zof T) c = false := by
  obtain ⟨k, a, b, hik, hk, -, -, hza, hzb, -⟩ := h
  have : k = r := by omega
  subst this
  rw [hk] at hg
  have hg' := Option.some.inj hg
  subst hg'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact hza
  · exact hzb

theorem good_op {n : ℕ} (T X : Finset (Fin n)) (gs : List Gate) (i r : ℕ) (g : Gate)
    (h : Good T X gs i) (hg : gs[r]? = some g) (hi : i = n + r) : g.op = GateOp.or := by
  obtain ⟨k, a, b, hik, hk, -⟩ := h
  have : k = r := by omega
  subst this
  rw [hk] at hg
  have hg' := Option.some.inj hg
  subst hg'
  rfl

theorem good_range {n : ℕ} (T X : Finset (Fin n)) (gs : List Gate) (i : ℕ)
    (h : Good T X gs i) : ∃ k, k < gs.length ∧ i = n + k := by
  obtain ⟨k, a, b, hik, hk, -⟩ := h
  exact ⟨k, lt_of_some _ _ _ hk, hik⟩

def Qp {n : ℕ} (gs : List Gate) (S R : Finset (Fin n)) (i : ℕ) : Prop :=
  val gs (Zof (S ∪ R)) i = false ∧ (∃ u ∈ S, u ∉ R ∧ val gs (eof u) i = true) ∧
    (∃ p ∈ S, p ∈ R ∧ val gs (eof p) i = true) ∧ ∀ v, val gs (eof v) i = true → v ∈ S

theorem Q_range {n : ℕ} (gs : List Gate) (S R : Finset (Fin n)) (i : ℕ) (hQ : Qp gs S R i) :
    n ≤ i ∧ i < n + gs.length := by
  obtain ⟨-, ⟨u, -, huR, hu⟩, ⟨p, -, hpR, hp⟩, -⟩ := hQ
  refine ⟨?_, lt_of_val _ _ _ hu⟩
  by_contra hc0
  have hc : i < n := Nat.lt_of_not_le hc0
  rw [val_input _ _ _ hc] at hu hp
  simp only [eof, decide_eq_true_eq] at hu hp
  rw [← hu, hp] at huR
  exact huR hpR

theorem Q_two {n : ℕ} (gs : List Gate) (S S' R : Finset (Fin n)) (i : ℕ)
    (hQ : Qp gs S R i) (hQ' : Qp gs S' R i) : 2 ≤ (S ∩ S').card := by
  obtain ⟨-, ⟨u, huS, huR, hu⟩, ⟨p, hpS, hpR, hp⟩, -⟩ := hQ
  obtain ⟨-, -, -, hall⟩ := hQ'
  have hup : u ≠ p := fun h => huR (h ▸ hpR)
  have hsub : ({u, p} : Finset (Fin n)) ⊆ S ∩ S' := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨huS, hall _ hu⟩
    · exact Finset.mem_inter.mpr ⟨hpS, hall _ hp⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hup] at this
  exact this

theorem Q_not_good {n : ℕ} (gs : List Gate) (S S' R : Finset (Fin n)) (i : ℕ)
    (hQ : Qp gs S R i) (hmin : ∀ i' < i, ¬ Qp gs S R i') (hg : Good (S' ∪ R) Rᶜ gs i) :
    False := by
  obtain ⟨k, a, b, hi, hk, ha, hb, -, -, u', hu', v', hv', -, hua, hvb⟩ := hg
  subst hi
  have hval := or_val gs k a b hk ha hb
  obtain ⟨hz, -, ⟨p, hpS, hpR, hp⟩, hall⟩ := hQ
  rw [hval, Bool.or_eq_false_iff] at hz
  rw [hval, Bool.or_eq_true] at hp
  have hallA : ∀ v, val gs (eof v) a = true → v ∈ S := fun v h => hall v (by rw [hval, h]; simp)
  have hallB : ∀ v, val gs (eof v) b = true → v ∈ S := fun v h => hall v (by rw [hval, h]; simp)
  rw [Finset.mem_compl] at hu' hv'
  rcases hp with h | h
  · exact hmin a ha ⟨hz.1, ⟨u', hallA u' hua, hu', hua⟩, ⟨p, hpS, hpR, h⟩, hallA⟩
  · exact hmin b hb ⟨hz.2, ⟨v', hallB v' hvb, hv', hvb⟩, ⟨p, hpS, hpR, h⟩, hallB⟩

theorem Q_not_good0 {n : ℕ} (gs : List Gate) (S R : Finset (Fin n)) (i : ℕ)
    (l : Fin n → Fin n) (hinv : Inv R Finset.univ gs l)
    (hQ : Qp gs S R i) (hg : Good R Finset.univ gs i) : False := by
  obtain ⟨k, a, b, hi, hk, ha, hb, hza, hzb, -⟩ := hg
  subst hi
  have hval := or_val gs k a b hk ha hb
  obtain ⟨-, ⟨u, -, huR, hu⟩, -⟩ := hQ
  have hz : val gs (Zof R) (n + k) = false := by rw [hval, hza, hzb]; rfl
  exact huR (hinv _ u u (Finset.mem_univ _) (Finset.mem_univ _) hz hu hu).1

theorem Q_transfer {n : ℕ} (gs : List Gate) (S R : Finset (Fin n)) (i d : ℕ)
    (h : ∀ x : Fin n → Bool, (x = Zof (S ∪ R) ∨ ∃ v, x = eof v) → val gs x i = val gs x d)
    (hQ : Qp gs S R i) : Qp gs S R d := by
  obtain ⟨hz, ⟨u, huS, huR, hu⟩, ⟨p, hpS, hpR, hp⟩, hall⟩ := hQ
  refine ⟨?_, ⟨u, huS, huR, ?_⟩, ⟨p, hpS, hpR, ?_⟩, ?_⟩
  · rw [← h _ (Or.inl rfl)]; exact hz
  · rw [← h _ (Or.inr ⟨u, rfl⟩)]; exact hu
  · rw [← h _ (Or.inr ⟨p, rfl⟩)]; exact hp
  · intro v hv
    exact hall v (by rw [h _ (Or.inr ⟨v, rfl⟩)]; exact hv)

theorem Q_not_reader {n : ℕ} (gs : List Gate) (S R : Finset (Fin n)) (r jj : ℕ) (g : Gate)
    (hQ : Qp gs S R (n + r)) (hmin : ∀ i' < n + r, ¬ Qp gs S R i')
    (hg : gs[r]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (hjr : jj < n + r) (hc : jj ∈ g.inputs)
    (htrue : ∀ x : Fin n → Bool, (x = Zof (S ∪ R) ∨ ∃ v, x = eof v) → val gs x jj = true) :
    False := by
  have hval := @val_gate n gs r g hg
  have hf : ∀ x : Fin n → Bool, (x = Zof (S ∪ R) ∨ ∃ v, x = eof v) →
      (if jj < n + r then val gs x jj else false) = true := by
    intro x hx
    rw [if_pos hjr]; exact htrue x hx
  have hZ := hf _ (Or.inl rfl)
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen hc hval
  -- an AND gate whose other input is the wire d
  have and_case : ∀ d : ℕ, op = GateOp.and →
      (∀ x : Fin n → Bool, (x = Zof (S ∪ R) ∨ ∃ v, x = eof v) →
        val gs x (n + r) = if d < n + r then val gs x d else false) → False := by
    intro d _ hd
    by_cases hdl : d < n + r
    · apply hmin d hdl
      apply Q_transfer gs S R (n + r) d _ hQ
      intro x hx
      rw [hd x hx, if_pos hdl]
    · obtain ⟨-, ⟨u, -, -, hu⟩, -⟩ := hQ
      rw [hd _ (Or.inr ⟨u, rfl⟩), if_neg hdl] at hu
      exact absurd hu (by simp)
  have hZQ := hQ.1
  match ins, hlen with
  | [], _ => simp at hc
  | [c], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    rw [hval] at hZQ
    rcases hop with rfl | rfl <;> simp [GateOp.eval, hjr, htrue _ (Or.inl rfl)] at hZQ
  | [c, d], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hop with rfl | rfl
    · rcases hc with rfl | rfl
      · apply and_case d rfl
        intro x hx
        rw [hval]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq]
        rw [hf x hx, Bool.true_and]
      · apply and_case c rfl
        intro x hx
        rw [hval]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq]
        rw [hf x hx, Bool.and_true]
    · rw [hval] at hZQ
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq] at hZQ
      rcases hc with rfl | rfl
      · rw [hZ] at hZQ; simp at hZQ
      · rw [hZ] at hZQ; simp at hZQ
  | _ :: _ :: _ :: _, h => simp at h

theorem main (q n m : ℕ) (S : Fin m → Finset (Fin n)) (R : Finset (Fin n))
    (hS : ∀ i : Fin m, (S i).card = q + 1)
    (hint : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hj : (gates.get j).op = GateOp.not)
    (huniq : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hout : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hN : ∀ x : Fin n → Bool,
      ((∀ v ∈ R, x v = false) ∨ (∃ p ∈ R, ∀ v : Fin n, x v = decide (v = p))) →
      val gates x (n + (j : ℕ)) = true) :
    m * q + (Finset.univ.filter (fun i : Fin gates.length =>
        j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 1 ≤
      gates.length +
        (if ∃ i0 : Fin m, R = S i0 then 0 else ∑ i : Fin m, ((S i ∩ R).card - 1)) := by
  classical
  have hNZ : ∀ T : Finset (Fin n), R ⊆ T → val gates (Zof T) (n + j) = true := by
    intro T hT
    apply hN
    left
    intro v hv
    simp [Zof, hT hv]
  have hNE : ∀ v : Fin n, val gates (eof v) (n + j) = true := by
    intro v
    apply hN
    by_cases hv : v ∈ R
    · right
      exact ⟨v, hv, fun u => rfl⟩
    · left
      intro u hu
      simp only [eof, decide_eq_false_iff_not]
      rintro rfl
      exact hv hu
  have hlen : ∀ g ∈ gates, g.inputs.length ≤ 2 := fun g h => (hg g h).2
  have hgetr : ∀ r : Fin gates.length, gates[r.val]? = some (gates.get r) := by
    intro r
    simp
  have hnotk : ∀ k g, gates[k]? = some g → g.op = GateOp.not → k = j.val := by
    intro k g hk hop
    have hlt := lt_of_some _ _ _ hk
    have h1 : gates.get ⟨k, hlt⟩ = g := by
      rw [hgetr ⟨k, hlt⟩] at hk
      exact Option.some.inj hk
    have := huniq ⟨k, hlt⟩ (by rw [h1]; exact hop)
    rw [← this]
  have hopT : ∀ T : Finset (Fin n), R ⊆ T → ∀ k g, gates[k]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∨ val gates (Zof T) (n + k) = true := by
    intro T hT k g hk
    have hmem : g ∈ gates := List.mem_of_getElem? hk
    rcases (hg g hmem).1 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · right
      rw [hnotk k g hk h]
      exact hNZ T hT
  have hline : ∀ w : Fin m, ∃ (l : Fin n → Fin n) (M : Finset ℕ),
      Inv (S w ∪ R) Rᶜ gates l ∧
      ((S w ∪ R) ∩ Rᶜ).card ≤ (((S w ∪ R) ∩ Rᶜ).image l).card + M.card ∧
      ∀ i ∈ M, Good (S w ∪ R) Rᶜ gates i :=
    fun w => main_inv _ _ gates hlen (hopT _ Finset.subset_union_right)
  choose l M hinv hcard hgood using hline
  obtain ⟨l0, M0, hinv0, hcard0, hgood0⟩ :=
    main_inv R Finset.univ gates hlen (hopT R (Finset.Subset.refl R))
  have hZout : ∀ w : Fin m, ∀ T : Finset (Fin n), S w ⊆ T → val gates (Zof T) (out w) = false := by
    intro w T hT
    rw [hout, decide_eq_false_iff_not]
    rintro ⟨v, hv, hz⟩
    simp [Zof, hT hv] at hz
  have hEout : ∀ w : Fin m, ∀ u ∈ S w, val gates (eof u) (out w) = true := by
    intro w u hu
    rw [hout, decide_eq_true_eq]
    exact ⟨u, hu, by simp [eof]⟩
  have hMw : ∀ w, (S w \ R).card ≤ 1 + (M w).card := by
    intro w
    have heq : (S w ∪ R) ∩ Rᶜ = S w \ R := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl, Finset.mem_sdiff]
      tauto
    have h1 : ((S w \ R).image (l w)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      rw [Finset.mem_sdiff] at hu hv
      exact (hinv w (out w) u v (Finset.mem_compl.mpr hu.2) (Finset.mem_compl.mpr hv.2)
        (hZout w _ Finset.subset_union_left) (hEout w u hu.1) (hEout w v hv.1)).2
    have := hcard w
    rw [heq] at this
    omega
  -- the first gates joining a line inside and outside R
  set K := Finset.univ.filter (fun w : Fin m => 1 ≤ (S w \ R).card ∧ 1 ≤ (S w ∩ R).card)
    with hK
  have hQout : ∀ w ∈ K, Qp gates (S w) R (out w) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hw.2.1
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hw.2.2
    rw [Finset.mem_sdiff] at hu
    rw [Finset.mem_inter] at hp
    refine ⟨hZout w _ Finset.subset_union_left, ⟨u, hu.1, hu.2, hEout w u hu.1⟩,
      ⟨p, hp.1, hp.2, hEout w p hp.1⟩, ?_⟩
    intro v hv
    rw [hout, decide_eq_true_eq] at hv
    obtain ⟨v', hv', he⟩ := hv
    simp only [eof, decide_eq_true_eq] at he
    rw [← he]
    exact hv'
  have hYex : ∀ w, ∃ i, w ∈ K → Qp gates (S w) R i ∧ ∀ i' < i, ¬ Qp gates (S w) R i' := by
    intro w
    by_cases hw : w ∈ K
    · have hex : ∃ i, Qp gates (S w) R i := ⟨out w, hQout w hw⟩
      exact ⟨Nat.find hex, fun _ => ⟨Nat.find_spec hex, fun i' hi' => Nat.find_min hex hi'⟩⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose Y hY using hYex
  have htest : ∀ w : Fin m, ∀ x : Fin n → Bool, (x = Zof (S w ∪ R) ∨ ∃ v, x = eof v) →
      val gates x (n + j) = true := by
    intro w x hx
    rcases hx with rfl | ⟨v, rfl⟩
    · exact hNZ _ Finset.subset_union_right
    · exact hNE v
  -- the readers of the NOT wire, as wires
  set F := Finset.univ.filter (fun i : Fin gates.length =>
    j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs) with hF
  set Rd := F.image (fun r : Fin gates.length => n + r.val) with hRd
  set B := Finset.univ.biUnion M with hB
  set Ys := K.image Y with hYs
  have hRdcard : Rd.card = F.card := by
    apply Finset.card_image_of_injective
    intro a b h
    exact Fin.ext (by simpa using h)
  have hBcard : B.card = ∑ w, (M w).card := by
    apply Finset.card_biUnion
    intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro i ha hb
    obtain ⟨u, v, huv, hu, hv, hua, hva, hub, hvb⟩ :=
      good_disj _ _ _ _ gates _ _ (hinv a) (hinv b) i (hgood a i ha) (hgood b i hb)
    rw [Finset.mem_compl] at hu hv
    have hua' : u ∈ S a := by simpa [hu] using hua
    have hva' : v ∈ S a := by simpa [hv] using hva
    have hub' : u ∈ S b := by simpa [hu] using hub (Finset.mem_compl.mpr hu)
    have hvb' : v ∈ S b := by simpa [hv] using hvb (Finset.mem_compl.mpr hv)
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hua', hub'⟩
      · exact Finset.mem_inter.mpr ⟨hva', hvb'⟩
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair huv] at h2
    have := hint a b hab
    omega
  have hYcard : Ys.card = K.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    by_contra hne
    have h2 := Q_two gates (S a) (S b) R (Y a) (hY a ha).1 (hab ▸ (hY b hb).1)
    have := hint a b hne
    omega
  -- disjointness
  have d4 : Disjoint M0 Ys := by
    rw [Finset.disjoint_left]
    intro i h0 hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    exact Q_not_good0 gates (S w) R _ l0 hinv0 (hY w hw).1 (hgood0 _ h0)
  have d3 : Disjoint B (M0 ∪ Ys) := by
    rw [Finset.disjoint_left]
    intro i hb h2
    obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hb
    rcases Finset.mem_union.mp h2 with h0 | hy
    · obtain ⟨u, v, -, hu, -, -, -, hu2, -⟩ :=
        good_disj _ _ _ _ gates _ _ (hinv w) hinv0 i (hgood w i hw) (hgood0 i h0)
      exact (Finset.mem_compl.mp hu) (hu2 (Finset.mem_univ _))
    · obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hy
      exact Q_not_good gates (S w') (S w) R _ (hY w' hw').1 (hY w' hw').2 (hgood w _ hw)
  have hreader : ∀ r : Fin gates.length, r ∈ F →
      (gates.get r).op = GateOp.and ∨ (gates.get r).op = GateOp.or := by
    intro r hr
    rw [Finset.mem_filter] at hr
    rcases (hg (gates.get r) (List.get_mem _ _)).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have := huniq r h
      rw [this] at hr
      exact absurd hr.2.1 (lt_irrefl _)
  have d2 : Disjoint Rd (B ∪ (M0 ∪ Ys)) := by
    rw [Finset.disjoint_left]
    intro i hr h2
    obtain ⟨r, hrF, rfl⟩ := Finset.mem_image.mp hr
    have hrF' := hrF
    rw [Finset.mem_filter] at hrF'
    obtain ⟨-, hjr, hc⟩ := hrF'
    have hjr' : n + (j : ℕ) < n + r.val := by
      have : (j : ℕ) < r.val := hjr
      omega
    rcases Finset.mem_union.mp h2 with hb | h3
    · obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hb
      have := good_input _ _ gates _ r.val _ _ (hgood w _ hw) (hgetr r) rfl hc
      rw [hNZ _ Finset.subset_union_right] at this
      exact absurd this (by simp)
    rcases Finset.mem_union.mp h3 with h0 | hy
    · have := good_input _ _ gates _ r.val _ _ (hgood0 _ h0) (hgetr r) rfl hc
      rw [hNZ _ (Finset.Subset.refl R)] at this
      exact absurd this (by simp)
    · obtain ⟨w, hw, hYw⟩ := Finset.mem_image.mp hy
      have hQ := (hY w hw).1
      have hmin := (hY w hw).2
      rw [hYw] at hQ hmin
      exact Q_not_reader gates (S w) R r.val (n + j) (gates.get r) hQ hmin (hgetr r)
        (hreader r hrF) (hlen _ (List.get_mem _ _)) hjr' hc (htest w)
  have d1 : Disjoint ({n + (j : ℕ)} : Finset ℕ) (Rd ∪ (B ∪ (M0 ∪ Ys))) := by
    rw [Finset.disjoint_singleton_left]
    intro h
    rcases Finset.mem_union.mp h with hr | h
    · obtain ⟨r, hrF, he⟩ := Finset.mem_image.mp hr
      rw [Finset.mem_filter] at hrF
      have : (j : ℕ) < r.val := hrF.2.1
      omega
    rcases Finset.mem_union.mp h with hb | h
    · obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hb
      have := good_op _ _ gates _ j.val _ (hgood w _ hw) (hgetr j) rfl
      rw [hj] at this
      cases this
    rcases Finset.mem_union.mp h with h0 | hy
    · have := good_op _ _ gates _ j.val _ (hgood0 _ h0) (hgetr j) rfl
      rw [hj] at this
      cases this
    · obtain ⟨w, hw, hYw⟩ := Finset.mem_image.mp hy
      have hQ := (hY w hw).1
      rw [hYw] at hQ
      have := hQ.1
      rw [hNZ _ Finset.subset_union_right] at this
      exact absurd this (by simp)
  set U := ({n + (j : ℕ)} : Finset ℕ) ∪ (Rd ∪ (B ∪ (M0 ∪ Ys))) with hU
  have hUcard : U.card = 1 + (F.card + ((∑ w, (M w).card) + (M0.card + K.card))) := by
    rw [hU, Finset.card_union_of_disjoint d1, Finset.card_union_of_disjoint d2,
      Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d4,
      Finset.card_singleton, hRdcard, hBcard, hYcard]
  have hUsub : U ⊆ Finset.Ico n (n + gates.length) := by
    intro i hi
    rw [Finset.mem_Ico]
    rcases Finset.mem_union.mp hi with h | h
    · rw [Finset.mem_singleton] at h
      have := j.isLt
      omega
    rcases Finset.mem_union.mp h with hr | h
    · obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hr
      have := r.isLt
      omega
    rcases Finset.mem_union.mp h with hb | h
    · obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hb
      obtain ⟨k, hk, rfl⟩ := good_range _ _ gates _ (hgood w _ hw)
      omega
    rcases Finset.mem_union.mp h with h0 | hy
    · obtain ⟨k, hk, rfl⟩ := good_range _ _ gates _ (hgood0 _ h0)
      omega
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      exact Q_range gates (S w) R _ (hY w hw).1
  have hbig : 1 + (F.card + ((∑ w, (M w).card) + (M0.card + K.card))) ≤ gates.length := by
    rw [← hUcard]
    have := Finset.card_le_card hUsub
    simpa using this
  have hKsum : (∑ w : Fin m, if (1 ≤ (S w \ R).card ∧ 1 ≤ (S w ∩ R).card) then 1 else 0) =
      K.card := by
    rw [hK, Finset.card_filter]
  have hsplit : ∀ w, (S w \ R).card + (S w ∩ R).card = q + 1 := by
    intro w
    rw [Finset.card_sdiff_add_card_inter, hS w]
  have hmq : ∑ _w : Fin m, q = m * q := by simp
  by_cases hl : ∃ i0 : Fin m, R = S i0
  · rw [if_pos hl]
    obtain ⟨i0, hR⟩ := hl
    have hM0 : q ≤ M0.card := by
      have h1 : ((R ∩ Finset.univ).image l0).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
        rw [Finset.inter_univ] at hu hv
        rw [hR] at hu hv
        exact (hinv0 (out i0) u v (Finset.mem_univ _) (Finset.mem_univ _)
          (hZout i0 R (hR ▸ Finset.Subset.refl R)) (hEout i0 u hu) (hEout i0 v hv)).2
      have h2 := hcard0
      rw [Finset.inter_univ] at h2 h1
      have h3 : R.card = q + 1 := by rw [hR]; exact hS i0
      omega
    have hper : ∀ w, q ≤ (M w).card +
        (if (1 ≤ (S w \ R).card ∧ 1 ≤ (S w ∩ R).card) then 1 else 0) +
        (if w = i0 then q else 0) := by
      intro w
      by_cases hw : w = i0
      · rw [if_pos hw]
        omega
      · rw [if_neg hw]
        have h1 : (S w ∩ R).card ≤ 1 := by rw [hR]; exact hint w i0 hw
        have h2 := hsplit w
        have h3 := hMw w
        split_ifs with h4
        · omega
        · omega
    have hsum := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => hper w)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hKsum, hmq] at hsum
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
    omega
  · rw [if_neg hl]
    have hper : ∀ w, q ≤ (M w).card +
        (if (1 ≤ (S w \ R).card ∧ 1 ≤ (S w ∩ R).card) then 1 else 0) +
        ((S w ∩ R).card - 1) := by
      intro w
      have h2 := hsplit w
      have h3 := hMw w
      split_ifs with h4
      · omega
      · omega
    have hsum := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => hper w)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hKsum, hmq] at hsum
    omega

end PEqualNP.Outside.L_meta_1376

theorem PEqualNP.Outside.L_meta_1376 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (R : Finset (Fin n)),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool,
      ((∀ v ∈ R, x v = false) ∨ (∃ p ∈ R, ∀ v : Fin n, x v = decide (v = p))) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = true) →
    m * q + (Finset.univ.filter (fun i : Fin gates.length =>
        j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 1 ≤
      gates.length + (if ∃ i0 : Fin m, R = S i0 then 0 else ∑ i : Fin m, ((S i ∩ R).card - 1)) := by
  intro q n m S R _ hS hint gates out j hg hj huniq hout hN
  exact PEqualNP.Outside.L_meta_1376.main q n m S R hS hint gates out j hg hj huniq
    (fun w x => hout w x) (fun x hx => hN x hx)
