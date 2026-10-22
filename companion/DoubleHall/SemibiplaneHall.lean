import DoubleHall.Semibiplane

/-!
# Strong quadrangularity of the homology semibiplane

Rows of the signed incidence matrix are pairwise orthogonal, and two points in different
parallel classes share an incident block. Hence every point set meeting two parallel classes
has at least as many super-neighbors as points.
-/

set_option linter.unusedSectionVars false

open Finset

namespace DoubleHall

namespace Semibiplane

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem sgnF_mul_even (a b : F × F) (v : F × F) :
    sgnF (dot F a (-v)) * sgnF (dot F b (-v)) = sgnF (dot F a v) * sgnF (dot F b v) := by
  rw [dot_neg_right, dot_neg_right, sgnF_neg, sgnF_neg]; ring

theorem sgnF_dot_zero (a : F × F) : sgnF (dot F a 0) = 0 := by
  have : dot F a 0 = 0 := by unfold dot; simp
  rw [this]; unfold sgnF
  have h1 : (0 : F) ≠ 1 := zero_ne_one
  have h2 : (0 : F) ≠ -1 := by rw [ne_eq, eq_comm, neg_eq_zero]; exact one_ne_zero
  simp [h1, h2]

/-- Rows indexed by distinct points are orthogonal. -/
theorem W_orthogonal (hF : (2 : F) ≠ 0) {x y : Pt F} (hxy : x ≠ y) :
    ∑ c : Pt F, W x c * W y c = 0 := by
  classical
  set a := x.out.1
  set b := y.out.1
  by_cases hdet : det F a b = 0
  · -- dependent representatives: no common incident block
    refine sum_eq_zero (fun c _ => ?_)
    by_contra hne
    have hx : W x c ≠ 0 := left_ne_zero_of_mul hne
    have hy : W y c ≠ 0 := right_ne_zero_of_mul hne
    rw [W, sgnF_ne_zero_iff hF] at hx hy
    rcases eq_or_eq_neg_of_det_zero hF a b c.out.1 hdet hx hy with h | h
    · apply hxy
      rw [← Quotient.out_eq x, ← Quotient.out_eq y]
      exact Quotient.sound (Or.inl h)
    · apply hxy
      rw [← Quotient.out_eq x, ← Quotient.out_eq y]
      exact Quotient.sound (Or.inr h)
  · -- independent representatives: change variables v ↦ (a·v, b·v)
    have h2 := sum_NZ_eq_two_mul hF (fun v => sgnF (dot F a v) * sgnF (dot F b v))
      (fun v => sgnF_mul_even a b v)
    have h0 := sum_NZ_eq_sum (fun v => sgnF (dot F a v) * sgnF (dot F b v))
      (by simp [sgnF_dot_zero])
    have hbij := dotPair_bijective a b hdet
    have hfull : ∑ v : F × F, sgnF (dot F a v) * sgnF (dot F b v) = 0 := by
      have hc := Function.Bijective.sum_comp hbij (fun p : F × F => sgnF p.1 * sgnF p.2)
      simp only at hc
      rw [hc, Fintype.sum_prod_type]
      simp_rw [← mul_sum]
      rw [← sum_mul, sum_sgnF hF, zero_mul]
    have : (2 : ℝ) * ∑ c : Pt F, sgnF (dot F a c.out.1) * sgnF (dot F b c.out.1) = 0 := by
      rw [← h2, h0, hfull]
    have h2ne : (2 : ℝ) ≠ 0 := two_ne_zero
    exact (mul_eq_zero.1 this).resolve_left h2ne

/-! ### Parallel classes -/

/-- Two nonzero vectors are parallel. -/
def lineSetoid : Setoid (NZ F) where
  r u v := det F u.1 v.1 = 0
  iseqv := by
    refine ⟨fun u => by unfold det; ring, fun {u v} h => by unfold det at *; linear_combination -h,
      fun {u v w} h₁ h₂ => ?_⟩
    unfold det at *
    have hv := v.2
    have e1 : (u.1.1 * w.1.2 - u.1.2 * w.1.1) * v.1.1 = 0 := by
      linear_combination w.1.1 * h₁ + u.1.1 * h₂
    have e2 : (u.1.1 * w.1.2 - u.1.2 * w.1.1) * v.1.2 = 0 := by
      linear_combination w.1.2 * h₁ + u.1.2 * h₂
    by_contra hne
    apply hv
    ext
    · exact (mul_eq_zero.1 e1).resolve_left hne
    · exact (mul_eq_zero.1 e2).resolve_left hne

instance : DecidableRel (lineSetoid (F := F)).r := fun u v => by
  unfold lineSetoid; infer_instance

/-- Parallel classes (projective points). -/
abbrev Line (F : Type*) [Field F] [Fintype F] [DecidableEq F] := Quotient (lineSetoid (F := F))

instance : DecidableEq (Line F) := by classical exact inferInstance

noncomputable instance : Fintype (Line F) := by classical exact Quotient.fintype _

/-- The parallel class of a point. -/
def cls : Pt F → Line F :=
  Quotient.lift (fun u : NZ F => (⟦u⟧ : Line F)) (by
    intro u v h
    apply Quotient.sound
    show det F u.1 v.1 = 0
    rcases h with h | h <;> rw [h] <;> unfold det <;> simp <;> ring)

theorem cls_eq_iff (x y : Pt F) : cls x = cls y ↔ det F x.out.1 y.out.1 = 0 := by
  conv_lhs => rw [← Quotient.out_eq x, ← Quotient.out_eq y]
  exact Quotient.eq

/-- Two points in different parallel classes share an incident block. -/
theorem exists_common_block (hF : (2 : F) ≠ 0) {x y : Pt F} (hxy : cls x ≠ cls y) :
    ∃ c : Pt F, W x c ≠ 0 ∧ W y c ≠ 0 := by
  have hdet : det F x.out.1 y.out.1 ≠ 0 := fun h => hxy ((cls_eq_iff x y).2 h)
  obtain ⟨v, hv1, hv2⟩ := exists_dot_one_one _ _ hdet
  have hv0 : v ≠ 0 := by
    rintro rfl; unfold dot at hv1; simp at hv1
  refine ⟨⟦⟨v, hv0⟩⟧, ?_, ?_⟩
  · rw [W_ne_zero_iff hF]
    have h := (inc_mk x.out ⟨v, hv0⟩).2 (Or.inl hv1)
    rwa [Quotient.out_eq] at h
  · rw [W_ne_zero_iff hF]
    have h := (inc_mk y.out ⟨v, hv0⟩).2 (Or.inl hv2)
    rwa [Quotient.out_eq] at h

/-- Strong quadrangularity: a point set meeting two parallel classes has at least as many
super-neighbors as points. -/
theorem card_le_superNbrs_of_not_inOneClass (hF : (2 : F) ≠ 0) (A : Finset (Pt F))
    (hA : ¬ InOneClass cls A) : A.card ≤ (superNbrs Inc A).card := by
  classical
  have hshare : ∀ u ∈ A, ∃ w ∈ A, w ≠ u ∧ ∃ c, W u c ≠ 0 ∧ W w c ≠ 0 := by
    intro u hu
    simp only [InOneClass, not_forall] at hA
    obtain ⟨a, ha, b, hb, hab⟩ := hA
    by_cases hua : cls u = cls a
    · have hub : cls u ≠ cls b := fun h => hab (hua.symm.trans h)
      obtain ⟨c, hc1, hc2⟩ := exists_common_block hF hub
      exact ⟨b, hb, fun h => hub (by rw [h]), c, hc1, hc2⟩
    · obtain ⟨c, hc1, hc2⟩ := exists_common_block hF hua
      exact ⟨a, ha, fun h => hua (by rw [h]), c, hc1, hc2⟩
  have h := card_le_card_multiCols W A (fun u _ w _ huw => W_orthogonal hF huw) hshare
  have heq : multiCols W A = superNbrs Inc A := by
    ext c
    simp only [multiCols, superNbrs, nbrsIn, mem_filter, mem_univ, true_and]
    have : (A.filter fun x => W x c ≠ 0) = A.filter fun x => Inc x c := by
      ext x; simp [W_ne_zero_iff hF]
    rw [this]
  rwa [heq] at h

end Semibiplane

end DoubleHall
