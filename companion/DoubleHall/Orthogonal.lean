import DoubleHall.Basic

/-!
# Orthogonal supports force many multi-hit columns

Classical strong-quadrangularity necessity (Severini; Severini–Szöllősi 2008, p. 378):
if the rows of a real matrix indexed by `A` are pairwise orthogonal and every row shares a
nonzero column with another row of `A`, then at least `|A|` columns contain two or more
nonzero entries in the rows of `A`.

Proof: restricting the rows to those columns changes no off-diagonal inner product and keeps
every row nonzero, so the restricted rows are linearly independent.
-/

set_option linter.unusedSectionVars false

open Finset

namespace DoubleHall

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Columns with at least two nonzero entries in the rows `A`. -/
noncomputable def multiCols (W : X → Y → ℝ) (A : Finset X) : Finset Y :=
  univ.filter (fun y => 2 ≤ (A.filter (fun x => W x y ≠ 0)).card)

/-- Outside the multi-hit columns, distinct rows of `A` have disjoint support. -/
theorem mul_eq_zero_of_not_mem_multiCols (W : X → Y → ℝ) (A : Finset X)
    {u w : X} (hu : u ∈ A) (hw : w ∈ A) (huw : u ≠ w) {y : Y}
    (hy : y ∉ multiCols W A) : W u y * W w y = 0 := by
  by_contra hne
  have hu0 : W u y ≠ 0 := left_ne_zero_of_mul hne
  have hw0 : W w y ≠ 0 := right_ne_zero_of_mul hne
  apply hy
  simp only [multiCols, mem_filter, mem_univ, true_and]
  have hsub : ({u, w} : Finset X) ⊆ A.filter (fun x => W x y ≠ 0) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_filter.2 ⟨hu, hu0⟩
    · exact mem_filter.2 ⟨hw, hw0⟩
  calc 2 = ({u, w} : Finset X).card := (card_pair huw).symm
    _ ≤ _ := card_le_card hsub

/-- Strong quadrangularity: orthogonal rows that pairwise overlap force `|A|` multi-hit
columns. -/
theorem card_le_card_multiCols (W : X → Y → ℝ) (A : Finset X)
    (horth : ∀ u ∈ A, ∀ w ∈ A, u ≠ w → ∑ y, W u y * W w y = 0)
    (hshare : ∀ u ∈ A, ∃ w ∈ A, w ≠ u ∧ ∃ y, W u y ≠ 0 ∧ W w y ≠ 0) :
    A.card ≤ (multiCols W A).card := by
  classical
  set C := multiCols W A with hC
  -- restricted row vectors
  let v : A → (C → ℝ) := fun u y => W u y
  -- restricted inner products agree with full ones for distinct rows
  have hrestr : ∀ u ∈ A, ∀ w ∈ A, u ≠ w → ∑ y : C, W u y * W w y = 0 := by
    intro u hu w hw huw
    have h := horth u hu w hw huw
    rw [← sum_add_sum_compl C] at h
    have hzero : ∑ y ∈ Cᶜ, W u y * W w y = 0 := by
      refine sum_eq_zero ?_
      intro y hy
      exact mul_eq_zero_of_not_mem_multiCols W A hu hw huw (by simpa using hy)
    rw [hzero, add_zero] at h
    rw [← h]
    exact (sum_coe_sort C (fun y => W u y * W w y))
  -- each restricted row has positive squared norm
  have hpos : ∀ w ∈ A, 0 < ∑ y : C, W w y * W w y := by
    intro w hw
    obtain ⟨w', hw', hne, y, hy1, hy2⟩ := hshare w hw
    have hyC : y ∈ C := by
      by_contra hyC
      exact (mul_ne_zero hy1 hy2) (by
        have := mul_eq_zero_of_not_mem_multiCols W A hw hw' hne.symm hyC
        exact this)
    have hterm : 0 < W w y * W w y := mul_self_pos.2 hy1
    calc 0 < W w y * W w y := hterm
      _ = W w (⟨y, hyC⟩ : C) * W w (⟨y, hyC⟩ : C) := rfl
      _ ≤ ∑ z : C, W w z * W w z :=
        single_le_sum (f := fun z : C => W w z * W w z)
          (fun z _ => mul_self_nonneg _) (mem_univ _)
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg w
    -- pair the vanishing combination with row w
    have hdot : ∑ y : C, (∑ i : A, g i • v i) y * W w y = 0 := by
      rw [hg]; simp
    have hexpand : ∑ y : C, (∑ i : A, g i • v i) y * W w y
        = ∑ i : A, g i * ∑ y : C, W i y * W w y := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v, Finset.sum_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      refine sum_congr rfl (fun i _ => sum_congr rfl (fun y _ => by ring))
    rw [hexpand] at hdot
    have hsingle : ∑ i : A, g i * ∑ y : C, W i y * W w y
        = g w * ∑ y : C, W w y * W w y := by
      rw [Finset.sum_eq_single w]
      · intro i _ hiw
        rw [hrestr i i.2 w w.2 (fun h => hiw (Subtype.ext h)), mul_zero]
      · intro h; exact absurd (mem_univ w) h
    rw [hsingle] at hdot
    exact (mul_eq_zero.1 hdot).resolve_right (hpos w w.2).ne'
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe] at hcard
  exact hcard

end DoubleHall
