import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3529_aux

def adjMasks : List ℕ :=
  [1408, 8832, 12544, 6272, 11264, 5632, 2816]

def rowList : List ℕ :=
  [129, 130, 136, 257, 260, 320, 514, 544, 576, 1025, 1040, 1056, 2056, 2064,
   2112, 4100, 4104, 4128, 8194, 8196, 8208,
   127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565,
   3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713,
   9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]

def edgeAdj (i j : Fin 14) : Bool :=
  (adjMasks.getD i.val 0).testBit j.val

def P (x : Fin 14 → Bool) : Prop :=
  ∃ i j : Fin 14, edgeAdj i j = true ∧ x i = true ∧ x j = true

def rowFn (k : Fin 58) (i : Fin 14) : Bool :=
  (rowList.getD k.val 0).testBit i.val

lemma edgeAdj_bipartite : ∀ i j : Fin 14, edgeAdj i j = true → i.val < 7 ∧ 7 ≤ j.val := by
  decide

lemma edge_in_rows : ∀ i j : Fin 14, edgeAdj i j = true →
    ∃ k : Fin 58, k.val < 21 ∧ ∀ t : Fin 14, decide (t = i ∨ t = j) = rowFn k t := by
  decide

def pack7 (b0 b1 b2 b3 b4 b5 b6 : Bool) : ℕ :=
  (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
  (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0) +
  (if b6 then 64 else 0)

lemma pack7_lt (b0 b1 b2 b3 b4 b5 b6 : Bool) : pack7 b0 b1 b2 b3 b4 b5 b6 < 128 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> decide

lemma pack7_testBit (b0 b1 b2 b3 b4 b5 b6 : Bool) (i : Fin 7) :
    (pack7 b0 b1 b2 b3 b4 b5 b6).testBit i.val =
      match i.val with
      | 0 => b0
      | 1 => b1
      | 2 => b2
      | 3 => b3
      | 4 => b4
      | 5 => b5
      | _ => b6 := by
  fin_cases i <;>
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> rfl

def leftBits (x : Fin 14 → Bool) : Fin 128 :=
  ⟨pack7 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6), pack7_lt _ _ _ _ _ _ _⟩

lemma leftBits_testBit (x : Fin 14 → Bool) (i : Fin 7) :
    (leftBits x).val.testBit i.val = x ⟨i.val, by omega⟩ := by
  unfold leftBits
  rw [pack7_testBit]
  fin_cases i <;> rfl

def rightOf (a : Fin 128) (j : Fin 14) : Bool :=
  decide (∀ i : Fin 7, edgeAdj ⟨i.val, by omega⟩ j = true → a.val.testBit i.val = false)

def isMaxLeft (a : Fin 128) : Bool :=
  decide (∀ i : Fin 7,
    a.val.testBit i.val =
      decide (∀ j : Fin 14, edgeAdj ⟨i.val, by omega⟩ j = true → rightOf a j = false))

def fullOf (a : Fin 128) (t : Fin 14) : Bool :=
  if t.val < 7 then a.val.testBit t.val else rightOf a t

def fullMask (a : Fin 128) : ℕ :=
  a.val +
  (if rightOf a 7 then 128 else 0) +
  (if rightOf a 8 then 256 else 0) +
  (if rightOf a 9 then 512 else 0) +
  (if rightOf a 10 then 1024 else 0) +
  (if rightOf a 11 then 2048 else 0) +
  (if rightOf a 12 then 4096 else 0) +
  (if rightOf a 13 then 8192 else 0)

def misIdx (a : Fin 128) : ℕ :=
  rowList.idxOf (fullMask a)

set_option maxRecDepth 20000 in
lemma mis_idx_ok : ∀ a : Fin 128, isMaxLeft a = true →
    21 ≤ misIdx a ∧ misIdx a < 58 ∧ ∀ t : Fin 14, fullOf a t = (rowList.getD (misIdx a) 0).testBit t.val := by
  decide

lemma mis_in_rows (a : Fin 128) (h : isMaxLeft a = true) :
    ∃ k : Fin 58, 21 ≤ k.val ∧ ∀ t : Fin 14, fullOf a t = rowFn k t := by
  obtain ⟨h1, h2, h3⟩ := mis_idx_ok a h
  exact ⟨⟨misIdx a, h2⟩, h1, h3⟩

lemma part_minimal (x : Fin 14 → Bool) (hmin : Minimal P x) :
    ∃ k : Fin 58, k.val < 21 ∧ x = rowFn k := by
  obtain ⟨i, j, hij, hxi, hxj⟩ := hmin.1
  let e : Fin 14 → Bool := fun t => decide (t = i ∨ t = j)
  have hPe : P e := ⟨i, j, hij, by simp [e], by simp [e]⟩
  have hex : e ≤ x := by
    intro t
    by_cases h : t = i ∨ t = j
    · rcases h with rfl | rfl <;> simp [e, hxi, hxj]
    · have h1 : t ≠ i := fun hi => h (Or.inl hi)
      have h2 : t ≠ j := fun hj => h (Or.inr hj)
      simp [e, h1, h2]
  have hxe : x ≤ e := hmin.2 hPe hex
  have hxeq : x = e := le_antisymm hxe hex
  obtain ⟨k, hk, hkf⟩ := edge_in_rows i j hij
  exact ⟨k, hk, hxeq.trans (funext hkf)⟩

lemma max_right (x : Fin 14 → Bool) (hmax : Maximal (fun y => ¬ P y) x)
    (j : Fin 14) (hj : 7 ≤ j.val) :
    x j = decide (∀ i : Fin 14, edgeAdj i j = true → x i = false) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hxj i hij
    cases hxi : x i
    · rfl
    · exact False.elim (hmax.1 ⟨i, j, hij, hxi, hxj⟩)
  · intro hall
    let y : Fin 14 → Bool := fun t => if t = j then true else x t
    have hxy : x ≤ y := by
      intro t
      by_cases ht : t = j
      · simp [y, ht]
      · simp [y, ht]
    have hny : ¬ P y := by
      rintro ⟨u, v, huv, hyu, hyv⟩
      have hbip := edgeAdj_bipartite u v huv
      have huj : u ≠ j := by
        intro h; subst h; omega
      have hxu : x u = true := by simpa [y, huj] using hyu
      by_cases hvj : v = j
      · subst hvj
        have hfalse := hall u huv
        rw [hfalse] at hxu
        exact Bool.noConfusion hxu
      · have hxv : x v = true := by simpa [y, hvj] using hyv
        exact hmax.1 ⟨u, v, huv, hxu, hxv⟩
    have hyx : y ≤ x := hmax.2 hny hxy
    have hle : true ≤ x j := by simpa [y] using hyx j
    cases hxj : x j
    · rw [hxj] at hle; exact absurd hle (by decide)
    · rfl

lemma max_left (x : Fin 14 → Bool) (hmax : Maximal (fun y => ¬ P y) x)
    (i : Fin 14) (hi : i.val < 7) :
    x i = decide (∀ j : Fin 14, edgeAdj i j = true → x j = false) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hxi j hij
    cases hxj : x j
    · rfl
    · exact False.elim (hmax.1 ⟨i, j, hij, hxi, hxj⟩)
  · intro hall
    let y : Fin 14 → Bool := fun t => if t = i then true else x t
    have hxy : x ≤ y := by
      intro t
      by_cases ht : t = i
      · simp [y, ht]
      · simp [y, ht]
    have hny : ¬ P y := by
      rintro ⟨u, v, huv, hyu, hyv⟩
      have hbip := edgeAdj_bipartite u v huv
      have hvi : v ≠ i := by
        intro h; subst h; omega
      have hxv : x v = true := by simpa [y, hvi] using hyv
      by_cases hui : u = i
      · subst hui
        have hfalse := hall v huv
        rw [hfalse] at hxv
        exact Bool.noConfusion hxv
      · have hxu : x u = true := by simpa [y, hui] using hyu
        exact hmax.1 ⟨u, v, huv, hxu, hxv⟩
    have hyx : y ≤ x := hmax.2 hny hxy
    have hle : true ≤ x i := by simpa [y] using hyx i
    cases hxi : x i
    · rw [hxi] at hle; exact absurd hle (by decide)
    · rfl

lemma part_maximal (x : Fin 14 → Bool) (hmax : Maximal (fun y => ¬ P y) x) :
    ∃ k : Fin 58, 21 ≤ k.val ∧ x = rowFn k := by
  let a := leftBits x
  have hright : ∀ j : Fin 14, 7 ≤ j.val → x j = rightOf a j := by
    intro j hj
    rw [max_right x hmax j hj]
    unfold rightOf
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h i hij
      rw [leftBits_testBit x i]
      exact h ⟨i.val, by omega⟩ hij
    · intro h i hij
      have hi7 : i.val < 7 := (edgeAdj_bipartite i j hij).1
      have hbit := h ⟨i.val, hi7⟩ hij
      rw [leftBits_testBit x ⟨i.val, hi7⟩] at hbit
      exact hbit
  have hfull : x = fullOf a := by
    funext t
    unfold fullOf
    by_cases ht : t.val < 7
    · simp only [ht, ite_true]
      exact (leftBits_testBit x ⟨t.val, ht⟩).symm
    · simp only [ht, ite_false]
      exact hright t (by omega)
  have hml : isMaxLeft a = true := by
    unfold isMaxLeft
    apply decide_eq_true
    intro i
    rw [leftBits_testBit x i, max_left x hmax ⟨i.val, by omega⟩ i.isLt]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h j hij
      have hj7 : 7 ≤ j.val := (edgeAdj_bipartite ⟨i.val, by omega⟩ j hij).2
      rw [← hright j hj7]
      exact h j hij
    · intro h j hij
      have hj7 : 7 ≤ j.val := (edgeAdj_bipartite ⟨i.val, by omega⟩ j hij).2
      rw [hright j hj7]
      exact h j hij
  obtain ⟨k, hk, hkf⟩ := mis_in_rows a hml
  exact ⟨k, hk, hfull.trans (funext hkf)⟩

end PEqualNP.Outside.L_meta_3529_aux

open PEqualNP.Outside.L_meta_3529_aux in
theorem PEqualNP.Outside.L_meta_3529 : have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), ([(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)].getD ↑x2 (0 : ℕ)).testBit ↑x3 = Bool.true ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; have x2 : Fin (58 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : Fin (58 : ℕ)) (x3 : Fin (14 : ℕ)) =>   ((have x4 : List ℕ :=             have x4 : List ℕ :=               have x4 : List ℕ :=                 have x4 : List ℕ := [(12353 : ℕ), (13504 : ℕ), (14849 : ℕ), (16256 : ℕ)];                 (9288 : ℕ) :: (9992 : ℕ) :: (10273 : ℕ) :: (10656 : ℕ) :: x4;               (5186 : ℕ) :: (6147 : ℕ) :: (7426 : ℕ) :: (8297 : ℕ) :: (8416 : ℕ) :: (8488 : ℕ) :: (8713 : ℕ) :: x4;             have x5 : List ℕ := (3078 : ℕ) :: (3716 : ℕ) :: (4179 : ℕ) :: (4304 : ℕ) :: (4370 : ℕ) :: (4625 : ℕ) :: (5008 : ℕ) :: x4;             (1220 : ℕ) :: (1290 : ℕ) :: (1548 : ℕ) :: (2087 : ℕ) :: (2212 : ℕ) :: (2338 : ℕ) :: (2565 : ℕ) :: x5;           have x5 : List ℕ :=             have x5 : List ℕ :=               have x5 : List ℕ := (541 : ℕ) :: (660 : ℕ) :: (792 : ℕ) :: (1102 : ℕ) :: x4;               (127 : ℕ) :: (244 : ℕ) :: (314 : ℕ) :: (432 : ℕ) :: x5;             (2112 : ℕ) :: (4100 : ℕ) :: (4104 : ℕ) :: (4128 : ℕ) :: (8194 : ℕ) :: (8196 : ℕ) :: (8208 : ℕ) :: x5;           have x6 : List ℕ := (544 : ℕ) :: (576 : ℕ) :: (1025 : ℕ) :: (1040 : ℕ) :: (1056 : ℕ) :: (2056 : ℕ) :: (2064 : ℕ) :: x5;           (129 : ℕ) :: (130 : ℕ) :: (136 : ℕ) :: (257 : ℕ) :: (260 : ℕ) :: (320 : ℕ) :: (514 : ℕ) :: x6).getD         ↑x2 (0 : ℕ)).testBit     ↑x3; ∀ (x3 : Fin (14 : ℕ) → Bool), (Minimal x1 x3 → ∃ (x5 : Fin (58 : ℕ)), ↑x5 < (21 : ℕ) ∧ x3 = x2 x5) ∧ (Maximal (fun (x4 : Fin (14 : ℕ) → Bool) => ¬x1 x4) x3 → ∃ (x5 : Fin (58 : ℕ)), (21 : ℕ) ≤ ↑x5 ∧ x3 = x2 x5) := by
  dsimp only
  intro x3
  exact ⟨part_minimal x3, part_maximal x3⟩


