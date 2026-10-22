import DoubleHall.SemibiplaneCount

/-!
# Sizes in the homology semibiplane

With `q = |F|` odd: there are `(q² - 1)/2` points, and every point class and every block
class has `(q - 1)/2` elements.
-/

set_option linter.unusedSectionVars false

open Finset

namespace DoubleHall

namespace Semibiplane

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Sum over nonzero vectors, for a function that need not vanish at zero. -/
theorem sum_NZ_add (f : F × F → ℝ) :
    ∑ v : NZ F, f v.1 + f 0 = ∑ v : F × F, f v := by
  classical
  rw [← sum_erase_add _ _ (mem_univ (0 : F × F))]
  congr 1
  exact (sum_subtype (univ.erase (0 : F × F)) (p := fun v => v ≠ 0) (fun x => by simp) f).symm

theorem two_mul_card_Pt (hF : (2 : F) ≠ 0) :
    2 * Fintype.card (Pt F) = Fintype.card F ^ 2 - 1 := by
  classical
  have h2 := sum_NZ_eq_two_mul hF (fun _ => (1 : ℝ)) (fun _ => rfl)
  have h0 := sum_NZ_add (F := F) (fun _ => (1 : ℝ))
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at h2 h0
  have hsq : Fintype.card (F × F) = Fintype.card F ^ 2 := by
    rw [Fintype.card_prod, sq]
  have hq : 1 ≤ Fintype.card F ^ 2 := Nat.one_le_pow _ _ Fintype.card_pos
  have : (2 * Fintype.card (Pt F) : ℝ) = (Fintype.card F ^ 2 : ℕ) - 1 := by
    rw [← hsq]; push_cast; linarith
  have : ((2 * Fintype.card (Pt F) : ℕ) : ℝ) = ((Fintype.card F ^ 2 - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hq]; push_cast at this ⊢; linarith
  exact_mod_cast this

/-- Every point class has `(q - 1)/2` elements. -/
theorem two_mul_card_cls (hF : (2 : F) ≠ 0) (L : Line F) :
    2 * (univ.filter (fun c : Pt F => cls c = L)).card = Fintype.card F - 1 := by
  classical
  set o := L.out.1 with ho
  have ho0 : o ≠ 0 := L.out.2
  let f : F × F → ℝ := fun v => if det F o v = 0 then 1 else 0
  have heven : ∀ v, f (-v) = f v := by
    intro v
    have hiff : det F o (-v) = 0 ↔ det F o v = 0 := by
      unfold det; simp only [Prod.fst_neg, Prod.snd_neg]
      constructor <;> intro h <;> linear_combination -h
    simp only [f, hiff]
  have h2 := sum_NZ_eq_two_mul hF f heven
  have h0 := sum_NZ_add f
  have hf0 : f 0 = 1 := by simp [f, det]
  -- the class sum counts the points of L
  have hcls : ∑ c : Pt F, f c.out.1 = ((univ.filter (fun c : Pt F => cls c = L)).card : ℝ) := by
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    refine sum_congr rfl (fun c _ => ?_)
    have : cls c = L ↔ det F o c.out.1 = 0 := by
      have h1 : cls c = (⟦c.out⟧ : Line F) := by
        conv_lhs => rw [← Quotient.out_eq c]
        rfl
      rw [h1]
      conv_lhs => rw [← Quotient.out_eq L]
      rw [Quotient.eq]
      show det F c.out.1 L.out.1 = 0 ↔ _
      unfold det; constructor <;> intro h <;> linear_combination -h
    simp only [f, this]; split_ifs <;> simp
  -- the vector sum counts the line through o
  have hvec : ∑ v : F × F, f v = (Fintype.card F : ℝ) := by
    have hrot : rot o ≠ 0 := rot_ne_zero ho0
    have : ∑ v : F × F, f v = ((univ.filter (fun v : F × F => dot F (rot o) v = 0)).card : ℝ) := by
      rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
      refine sum_congr rfl (fun v _ => ?_)
      have : det F o v = 0 ↔ dot F (rot o) v = 0 := by
        unfold det dot rot; constructor <;> intro h <;> linear_combination h
      simp only [f, this]; split_ifs <;> simp
    rw [this, card_dot_eq _ hrot]
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have : (2 * (univ.filter (fun c : Pt F => cls c = L)).card : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [← hcls, ← h2]; linarith
  have : ((2 * (univ.filter (fun c : Pt F => cls c = L)).card : ℕ) : ℝ) =
      ((Fintype.card F - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hq]; push_cast at this ⊢; linarith
  exact_mod_cast this

theorem rot_rot (v : F × F) : rot (rot v) = -v := by
  unfold rot; ext <;> simp

theorem rotPt_rotPt (y : Pt F) : rotPt (rotPt y) = y := by
  induction y using Quotient.inductionOn with
  | h v =>
    show (⟦⟨rot (rot v.1), _⟩⟧ : Pt F) = ⟦v⟧
    apply Quotient.sound
    show v.1 = rot (rot v.1) ∨ v.1 = -rot (rot v.1)
    right; rw [rot_rot, neg_neg]

theorem rotPt_bijective : Function.Bijective (rotPt (F := F)) :=
  Function.Involutive.bijective rotPt_rotPt

/-- Every block class has `(q - 1)/2` elements. -/
theorem two_mul_card_clsY (hF : (2 : F) ≠ 0) (L : Line F) :
    2 * (univ.filter (fun c : Pt F => clsY c = L)).card = Fintype.card F - 1 := by
  classical
  have : (univ.filter (fun c : Pt F => clsY c = L)) =
      (univ.filter (fun c : Pt F => cls c = L)).image rotPt := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_image, clsY]
    constructor
    · intro h; exact ⟨rotPt c, h, rotPt_rotPt c⟩
    · rintro ⟨d, hd, rfl⟩; rw [rotPt_rotPt]; exact hd
  rw [this, card_image_of_injective _ rotPt_bijective.1]
  exact two_mul_card_cls hF L

end Semibiplane

end DoubleHall
