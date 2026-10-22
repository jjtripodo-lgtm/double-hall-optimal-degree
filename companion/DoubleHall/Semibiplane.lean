import DoubleHall.Orthogonal
import DoubleHall.Repair

/-!
# The Desarguesian homology semibiplane

Let `F` be a finite field of odd order `q`. Points and blocks are the nonzero vectors of `F²`
modulo `u ~ -u`, so there are `(q² - 1)/2` of each. A point `[u]` is joined to a block `[v]`
when `u · v = ±1`.

Classical facts (Moorhouse 1990, §§1–2) formalized here:
* the incidence is well defined and `q`-regular;
* its signed incidence matrix has pairwise orthogonal rows;
* every set of points meeting two parallel classes (one-dimensional subspaces) has at least
  as many super-neighbors as points (strong quadrangularity);
* a point class and its perpendicular block class span no incidence.
-/

set_option linter.unusedSectionVars false

open Finset

namespace DoubleHall

namespace Semibiplane

noncomputable section

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- The dot product on `F × F`. -/
def dot (u v : F × F) : F := u.1 * v.1 + u.2 * v.2

/-- The determinant of two vectors in `F × F`. -/
def det (u v : F × F) : F := u.1 * v.2 - u.2 * v.1

/-- Nonzero vectors. -/
abbrev NZ := {u : F × F // u ≠ 0}

/-- The sign relation `u ~ ±u`. -/
def signSetoid : Setoid (NZ F) where
  r u v := v.1 = u.1 ∨ v.1 = -u.1
  iseqv := by
    refine ⟨fun u => Or.inl rfl, ?_, ?_⟩
    · intro u v h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, neg_neg])
    · intro u v w h₁ h₂
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · exact Or.inl (h₂.trans h₁)
      · exact Or.inr (by rw [h₂, h₁])
      · exact Or.inr (by rw [h₂, h₁])
      · exact Or.inl (by rw [h₂, h₁, neg_neg])

/-- Points (and blocks): sign classes of nonzero vectors. -/
abbrev Pt := Quotient (signSetoid F)

instance : DecidableEq (Pt F) := by
  classical exact inferInstance

noncomputable instance : Fintype (Pt F) := by
  classical exact Quotient.fintype _

variable {F}

theorem dot_comm (u v : F × F) : dot F u v = dot F v u := by
  unfold dot; ring

theorem dot_neg_left (u v : F × F) : dot F (-u) v = -dot F u v := by
  unfold dot; simp; ring

theorem dot_neg_right (u v : F × F) : dot F u (-v) = -dot F u v := by
  unfold dot; simp; ring

/-- The incidence predicate on representatives. -/
def incRep (u v : F × F) : Prop := dot F u v = 1 ∨ dot F u v = -1

theorem incRep_neg_left (u v : F × F) : incRep (-u) v ↔ incRep u v := by
  unfold incRep; rw [dot_neg_left]
  constructor
  · rintro (h | h)
    · exact Or.inr (by rw [← neg_neg (dot F u v), h])
    · exact Or.inl (by rw [← neg_neg (dot F u v), h, neg_neg])
  · rintro (h | h)
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h, neg_neg])

theorem incRep_neg_right (u v : F × F) : incRep u (-v) ↔ incRep u v := by
  unfold incRep; rw [dot_neg_right]
  constructor
  · rintro (h | h)
    · exact Or.inr (by rw [← neg_neg (dot F u v), h])
    · exact Or.inl (by rw [← neg_neg (dot F u v), h, neg_neg])
  · rintro (h | h)
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h, neg_neg])

/-- Incidence of the semibiplane on sign classes. -/
def Inc : Pt F → Pt F → Prop :=
  Quotient.lift₂ (fun u v : NZ F => incRep u.1 v.1) (by
    intro a₁ b₁ a₂ b₂ ha hb
    apply propext
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      simp only [ha, hb, incRep_neg_left, incRep_neg_right])

theorem inc_mk (u v : NZ F) : Inc ⟦u⟧ ⟦v⟧ ↔ incRep u.1 v.1 := Iff.rfl

instance : ∀ x y : Pt F, Decidable (Inc x y) := by
  classical exact fun _ _ => inferInstance

theorem inc_iff_out (x y : Pt F) : Inc x y ↔ incRep x.out.1 y.out.1 := by
  conv_lhs => rw [← Quotient.out_eq x, ← Quotient.out_eq y]
  rfl

/-! ### The signed incidence matrix -/

/-- `+1` at `1`, `-1` at `-1`, zero elsewhere (when `1 ≠ -1`). -/
noncomputable def sgnF (t : F) : ℝ := (if t = 1 then 1 else 0) - (if t = -1 then 1 else 0)

theorem sgnF_neg (t : F) : sgnF (-t) = -sgnF t := by
  unfold sgnF
  have h1 : (-t = 1) ↔ (t = -1) := by
    constructor
    · intro h; rw [← h, neg_neg]
    · intro h; rw [h, neg_neg]
  have h2 : (-t = -1) ↔ (t = 1) := by
    constructor
    · intro h; exact neg_inj.1 h
    · intro h; rw [h]
  simp only [h1, h2]; ring

theorem one_ne_neg_one (hF : (2 : F) ≠ 0) : (1 : F) ≠ -1 := by
  intro h
  apply hF
  linear_combination h

theorem sgnF_ne_zero_iff (hF : (2 : F) ≠ 0) (t : F) : sgnF t ≠ 0 ↔ (t = 1 ∨ t = -1) := by
  have hne := one_ne_neg_one hF
  unfold sgnF
  by_cases h1 : t = 1
  · subst h1; simp [hne]
  · by_cases h2 : t = -1
    · subst h2; simp [hne.symm]
    · simp [h1, h2]

theorem sum_sgnF (hF : (2 : F) ≠ 0) : ∑ t : F, sgnF t = 0 := by
  unfold sgnF
  rw [sum_sub_distrib]
  simp

/-- Signed incidence matrix, using chosen representatives. -/
noncomputable def W (x y : Pt F) : ℝ := sgnF (dot F x.out.1 y.out.1)

theorem W_ne_zero_iff (hF : (2 : F) ≠ 0) (x y : Pt F) : W x y ≠ 0 ↔ Inc x y := by
  rw [W, sgnF_ne_zero_iff hF, inc_iff_out]; rfl

/-! ### Summing over sign classes -/

theorem neg_ne_self (hF : (2 : F) ≠ 0) (u : NZ F) : (-u.1) ≠ u.1 := by
  intro h
  apply u.2
  have h2 : (2 : F) • u.1 = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h]; exact neg_add_cancel u.1
  exact (smul_eq_zero.1 h2).resolve_left hF

/-- The negation of a nonzero vector, as a nonzero vector. -/
def negNZ (u : NZ F) : NZ F := ⟨-u.1, neg_ne_zero.2 u.2⟩

theorem fiber_eq (hF : (2 : F) ≠ 0) (c : Pt F) :
    (univ.filter (fun v : NZ F => (⟦v⟧ : Pt F) = c)) = {c.out, negNZ c.out} := by
  ext v
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · intro h
    have h' : (⟦v⟧ : Pt F) = ⟦c.out⟧ := by rw [h, Quotient.out_eq]
    rcases Quotient.exact h' with h'' | h''
    · left; exact Subtype.ext h''.symm
    · right; apply Subtype.ext; simp only [negNZ]; rw [h'', neg_neg]
  · rintro (rfl | rfl)
    · exact Quotient.out_eq c
    · conv_rhs => rw [← Quotient.out_eq c]
      apply Quotient.sound
      exact Or.inr (by simp [negNZ])

/-- An even function summed over nonzero vectors is twice its sum over sign classes. -/
theorem sum_NZ_eq_two_mul (hF : (2 : F) ≠ 0) (f : F × F → ℝ) (hf : ∀ v, f (-v) = f v) :
    ∑ v : NZ F, f v.1 = 2 * ∑ c : Pt F, f c.out.1 := by
  classical
  rw [← sum_fiberwise univ (fun v : NZ F => (⟦v⟧ : Pt F)) (fun v => f v.1), mul_sum]
  refine sum_congr rfl ?_
  intro c _
  rw [fiber_eq hF c, sum_pair]
  · simp only [negNZ, hf]; ring
  · intro h
    exact neg_ne_self hF c.out (congrArg Subtype.val h).symm

/-- Sum over nonzero vectors equals sum over all vectors for functions vanishing at zero. -/
theorem sum_NZ_eq_sum (f : F × F → ℝ) (hf : f 0 = 0) :
    ∑ v : NZ F, f v.1 = ∑ v : F × F, f v := by
  classical
  rw [← sum_subtype (univ.filter (fun v : F × F => v ≠ 0)) (p := fun v => v ≠ 0)
    (by intro v; simp)]
  rw [sum_filter]
  refine sum_congr rfl (fun v _ => ?_)
  by_cases hv : v = 0
  · simp [hv, hf]
  · simp [hv]

/-! ### Two-by-two linear algebra -/

theorem dot_eq_zero_of_det (a b v : F × F) (hdet : det F a b ≠ 0)
    (ha : dot F a v = 0) (hb : dot F b v = 0) : v = 0 := by
  unfold det at hdet; unfold dot at ha hb
  have h1 : (a.1 * b.2 - a.2 * b.1) * v.1 = 0 := by linear_combination b.2 * ha - a.2 * hb
  have h2 : (a.1 * b.2 - a.2 * b.1) * v.2 = 0 := by linear_combination a.1 * hb - b.1 * ha
  ext
  · exact (mul_eq_zero.1 h1).resolve_left hdet
  · exact (mul_eq_zero.1 h2).resolve_left hdet

/-- For independent `a, b`, the map `v ↦ (a·v, b·v)` is a bijection of `F × F`. -/
theorem dotPair_bijective (a b : F × F) (hdet : det F a b ≠ 0) :
    Function.Bijective (fun v : F × F => (dot F a v, dot F b v)) := by
  rw [← Finite.injective_iff_bijective]
  intro v w h
  simp only [Prod.mk.injEq] at h
  have : v - w = 0 := dot_eq_zero_of_det a b (v - w) hdet
    (by unfold dot at *; simp only [Prod.fst_sub, Prod.snd_sub]; linear_combination h.1)
    (by unfold dot at *; simp only [Prod.fst_sub, Prod.snd_sub]; linear_combination h.2)
  exact sub_eq_zero.1 this

/-- For independent `a, b`, some vector has `a·v = 1` and `b·v = 1`. -/
theorem exists_dot_one_one (a b : F × F) (hdet : det F a b ≠ 0) :
    ∃ v : F × F, dot F a v = 1 ∧ dot F b v = 1 := by
  refine ⟨((b.2 - a.2) / det F a b, (a.1 - b.1) / det F a b), ?_, ?_⟩
  · unfold dot
    simp only
    rw [mul_div_assoc', mul_div_assoc', ← add_div, div_eq_one_iff_eq hdet]
    unfold det; ring
  · unfold dot
    simp only
    rw [mul_div_assoc', mul_div_assoc', ← add_div, div_eq_one_iff_eq hdet]
    unfold det; ring

/-- If `det a b = 0`, `a·v = ±1` and `b·v = ±1`, then `b = ±a`. -/
theorem eq_or_eq_neg_of_det_zero (hF : (2 : F) ≠ 0) (a b v : F × F) (hdet : det F a b = 0)
    (ha : incRep a v) (hb : incRep b v) : b = a ∨ b = -a := by
  unfold det at hdet; unfold incRep at ha hb
  have key1 : dot F a v * b.1 = dot F b v * a.1 := by
    unfold dot; linear_combination (-v.2) * hdet
  have key2 : dot F a v * b.2 = dot F b v * a.2 := by
    unfold dot; linear_combination v.1 * hdet
  rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;> rw [h1, h2] at key1 key2
  · left
    exact Prod.ext (by linear_combination key1) (by linear_combination key2)
  · right
    exact Prod.ext (by simp only [Prod.fst_neg]; linear_combination key1)
      (by simp only [Prod.snd_neg]; linear_combination key2)
  · right
    exact Prod.ext (by simp only [Prod.fst_neg]; linear_combination -key1)
      (by simp only [Prod.snd_neg]; linear_combination -key2)
  · left
    exact Prod.ext (by linear_combination -key1) (by linear_combination -key2)

end

end Semibiplane

end DoubleHall
