import DoubleHall.SemibiplaneHall

/-!
# Counting in the homology semibiplane

* every point and block has exactly `q = |F|` incidences;
* the incidence is symmetric;
* block classes are images of point classes under the rotation `v ↦ (-v₂, v₁)`, and a point
  class and its rotated block class span no incidence;
* every block meets each point class at most once, and vice versa.
-/

set_option linter.unusedSectionVars false

open Finset

namespace DoubleHall

namespace Semibiplane

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### Affine lines have `q` points -/

theorem card_dot_eq (a : F × F) (ha : a ≠ 0) (s : F) :
    (univ.filter (fun v : F × F => dot F a v = s)).card = Fintype.card F := by
  classical
  by_cases h1 : a.1 = 0
  · have h2 : a.2 ≠ 0 := by
      intro h2; apply ha; ext <;> simp [h1, h2]
    have : univ.filter (fun v : F × F => dot F a v = s) =
        univ.image (fun t : F => (t, (s - a.1 * t) / a.2)) := by
      ext v
      simp only [mem_filter, mem_univ, true_and, mem_image]
      constructor
      · intro hv
        refine ⟨v.1, Prod.ext rfl ?_⟩
        simp only
        rw [← hv]; unfold dot; field_simp; ring
      · rintro ⟨t, rfl⟩
        unfold dot; field_simp; ring
    rw [this, card_image_of_injective, card_univ]
    intro t t' h; exact congrArg Prod.fst h
  · have : univ.filter (fun v : F × F => dot F a v = s) =
        univ.image (fun t : F => ((s - a.2 * t) / a.1, t)) := by
      ext v
      simp only [mem_filter, mem_univ, true_and, mem_image]
      constructor
      · intro hv
        refine ⟨v.2, Prod.ext ?_ rfl⟩
        simp only
        rw [← hv]; unfold dot; field_simp; ring
      · rintro ⟨t, rfl⟩
        unfold dot; field_simp; ring
    rw [this, card_image_of_injective, card_univ]
    intro t t' h; exact congrArg Prod.snd h

theorem incRep_comm (u v : F × F) : incRep u v ↔ incRep v u := by
  unfold incRep; rw [dot_comm]

theorem inc_comm (x y : Pt F) : Inc x y ↔ Inc y x := by
  rw [inc_iff_out, inc_iff_out, incRep_comm]

theorem not_incRep_zero (a : F × F) : ¬ incRep a 0 := by
  unfold incRep dot
  simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero]
  rintro (h | h)
  · exact zero_ne_one h
  · exact zero_ne_one (by rw [eq_neg_iff_add_eq_zero, zero_add] at h; exact h.symm)

/-- Every point has exactly `q` incident blocks. -/
theorem degL_inc (hF : (2 : F) ≠ 0) (x : Pt F) : degL Inc x = Fintype.card F := by
  classical
  set a := x.out.1
  have ha : a ≠ 0 := x.out.2
  let f : F × F → ℝ := fun v => if incRep a v then 1 else 0
  have heven : ∀ v, f (-v) = f v := by
    intro v; simp only [f, incRep_neg_right]
  have h2 := sum_NZ_eq_two_mul hF f heven
  have h0 := sum_NZ_eq_sum f (by simp [f, not_incRep_zero])
  -- the class sum counts incident blocks
  have hcls : ∑ c : Pt F, f c.out.1 = (degL Inc x : ℝ) := by
    unfold degL
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    refine sum_congr rfl (fun c _ => ?_)
    simp only [f, inc_iff_out x c, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rfl
  -- the vector sum counts two affine lines
  have hvec : ∑ v : F × F, f v = 2 * (Fintype.card F : ℝ) := by
    have hne := one_ne_neg_one hF
    have e1 : ∑ v : F × F, f v = ∑ v : F × F, ((if dot F a v = 1 then (1 : ℝ) else 0) +
        (if dot F a v = -1 then (1 : ℝ) else 0)) := by
      refine sum_congr rfl (fun v _ => ?_)
      by_cases h1 : dot F a v = 1
      · have h2 : dot F a v ≠ -1 := fun h => hne (h1.symm.trans h)
        rw [show f v = 1 from if_pos (Or.inl h1), if_pos h1, if_neg h2]; ring
      · by_cases h2 : dot F a v = -1
        · rw [show f v = 1 from if_pos (Or.inr h2), if_neg h1, if_pos h2]; ring
        · rw [show f v = 0 from if_neg (by rintro (h | h) <;> contradiction), if_neg h1,
            if_neg h2]; ring
    rw [e1, sum_add_distrib, sum_boole, sum_boole, card_dot_eq a ha, card_dot_eq a ha]
    ring
  have : (2 : ℝ) * (degL Inc x : ℝ) = 2 * (Fintype.card F : ℝ) := by
    rw [← hcls, ← h2, h0, hvec]
  have := mul_left_cancel₀ (two_ne_zero) this
  exact_mod_cast this

theorem degR_inc (hF : (2 : F) ≠ 0) (y : Pt F) : degR Inc y = Fintype.card F := by
  have h := degL_inc hF y
  unfold degL at h; unfold degR
  rw [← h]; congr 1; ext x; simp [inc_comm x y]

/-! ### Rotation and block classes -/

/-- Rotation by a quarter turn. -/
def rot (v : F × F) : F × F := (-v.2, v.1)

theorem rot_neg (v : F × F) : rot (-v) = -rot v := by
  unfold rot; simp

theorem rot_ne_zero {v : F × F} (hv : v ≠ 0) : rot v ≠ 0 := by
  intro h; apply hv
  unfold rot at h
  simp only [Prod.mk_eq_zero, neg_eq_zero] at h
  exact Prod.ext h.2 h.1

theorem det_rot (a v : F × F) : det F a (rot v) = dot F a v := by
  unfold det rot dot; ring

theorem det_rot_rot (u w : F × F) : det F (rot u) (rot w) = det F u w := by
  unfold det rot; ring

/-- Rotation on sign classes. -/
def rotPt : Pt F → Pt F :=
  Quotient.map (fun v : NZ F => (⟨rot v.1, rot_ne_zero v.2⟩ : NZ F)) (by
    intro u v h
    rcases h with h | h
    · exact Or.inl (by simp only; rw [h])
    · exact Or.inr (by simp only; rw [h, rot_neg]))

/-- Block classes: the parallel class of the rotated block. -/
def clsY (y : Pt F) : Line F := cls (rotPt y)

theorem det_out_mk (x : Pt F) (v : NZ F) :
    det F x.out.1 (⟦v⟧ : Pt F).out.1 = 0 ↔ det F x.out.1 v.1 = 0 := by
  have h : (signSetoid F).r (⟦v⟧ : Pt F).out v := Quotient.mk_out (s := signSetoid F) v
  rcases h with h | h
  · rw [h]
  · have : (⟦v⟧ : Pt F).out.1 = -v.1 := by rw [h, neg_neg]
    rw [this]; unfold det; simp only [Prod.fst_neg, Prod.snd_neg]; constructor <;> intro h' <;> linear_combination -h'

/-- A point is in the class rotated from a block exactly when their dot product vanishes. -/
theorem cls_eq_clsY_iff (x y : Pt F) : cls x = clsY y ↔ dot F x.out.1 y.out.1 = 0 := by
  unfold clsY
  rw [cls_eq_iff]
  have hy : rotPt y = ⟦⟨rot y.out.1, rot_ne_zero y.out.2⟩⟧ := by
    conv_lhs => rw [← Quotient.out_eq y]
    rfl
  rw [hy, det_out_mk, det_rot]

/-- No incidence inside a paired class rectangle. -/
theorem not_inc_of_cls_eq_clsY (x y : Pt F) (h : cls x = clsY y) : ¬ Inc x y := by
  rw [cls_eq_clsY_iff] at h
  rw [inc_iff_out]
  unfold incRep
  rw [h]
  rintro (h1 | h1)
  · exact zero_ne_one h1
  · exact zero_ne_one (by rw [eq_neg_iff_add_eq_zero, zero_add] at h1; exact h1.symm)

/-- A block meets every point class at most once. -/
theorem inc_cls_unique (hF : (2 : F) ≠ 0) {x x' y : Pt F} (hcls : cls x = cls x')
    (hx : Inc x y) (hx' : Inc x' y) : x = x' := by
  rw [cls_eq_iff] at hcls
  rw [inc_iff_out] at hx hx'
  rcases eq_or_eq_neg_of_det_zero hF _ _ _ hcls hx hx' with h | h
  · rw [← Quotient.out_eq x, ← Quotient.out_eq x']
    exact Quotient.sound (Or.inl h)
  · rw [← Quotient.out_eq x, ← Quotient.out_eq x']
    exact Quotient.sound (Or.inr h)

theorem clsY_eq_iff (y y' : Pt F) : clsY y = clsY y' ↔ det F y.out.1 y'.out.1 = 0 := by
  unfold clsY
  rw [cls_eq_iff]
  have hy : ∀ z : Pt F, rotPt z = ⟦⟨rot z.out.1, rot_ne_zero z.out.2⟩⟧ := by
    intro z
    conv_lhs => rw [← Quotient.out_eq z]
    rfl
  rw [hy y, hy y']
  -- representatives of the rotated classes are ± the rotated representatives
  have key : ∀ (u w : NZ F), det F (⟦u⟧ : Pt F).out.1 (⟦w⟧ : Pt F).out.1 = 0 ↔
      det F u.1 w.1 = 0 := by
    intro u w
    have hu : (signSetoid F).r (⟦u⟧ : Pt F).out u := Quotient.mk_out (s := signSetoid F) u
    have hw : (signSetoid F).r (⟦w⟧ : Pt F).out w := Quotient.mk_out (s := signSetoid F) w
    rcases hu with hu | hu <;> rcases hw with hw | hw
    · rw [hu, hw]
    · have h2 : (⟦w⟧ : Pt F).out.1 = -w.1 := by rw [hw, neg_neg]
      rw [hu, h2]; unfold det; simp only [Prod.fst_neg, Prod.snd_neg]; constructor <;> intro h' <;> linear_combination -h'
    · have h1 : (⟦u⟧ : Pt F).out.1 = -u.1 := by rw [hu, neg_neg]
      rw [h1, hw]; unfold det; simp only [Prod.fst_neg, Prod.snd_neg]; constructor <;> intro h' <;> linear_combination -h'
    · have h1 : (⟦u⟧ : Pt F).out.1 = -u.1 := by rw [hu, neg_neg]
      have h2 : (⟦w⟧ : Pt F).out.1 = -w.1 := by rw [hw, neg_neg]
      rw [h1, h2]; unfold det; simp only [Prod.fst_neg, Prod.snd_neg]; constructor <;> intro h' <;> linear_combination h'
  rw [key]
  simp only [det_rot_rot]

/-- A point meets every block class at most once. -/
theorem inc_clsY_unique (hF : (2 : F) ≠ 0) {x y y' : Pt F} (hcls : clsY y = clsY y')
    (hy : Inc x y) (hy' : Inc x y') : y = y' := by
  rw [clsY_eq_iff] at hcls
  rw [inc_comm] at hy hy'
  rw [inc_iff_out] at hy hy'
  rcases eq_or_eq_neg_of_det_zero hF _ _ _ hcls hy hy' with h | h
  · rw [← Quotient.out_eq y, ← Quotient.out_eq y']
    exact Quotient.sound (Or.inl h)
  · rw [← Quotient.out_eq y, ← Quotient.out_eq y']
    exact Quotient.sound (Or.inr h)

end Semibiplane

end DoubleHall
