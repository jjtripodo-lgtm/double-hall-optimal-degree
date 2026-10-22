import DoubleHall.Basic

/-!
# Two-sided double Hall, transposes and relabelling
-/

set_option linter.unusedSectionVars false

open Finset

namespace DoubleHall

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Double Hall on the right side. -/
def DoubleHallRight (R : X → Y → Prop) [∀ x y, Decidable (R x y)] : Prop :=
  DoubleHallLeft (fun y x => R x y)

/-- Double Hall on both sides. -/
def DoubleHallBoth (R : X → Y → Prop) [∀ x y, Decidable (R x y)] : Prop :=
  DoubleHallLeft R ∧ DoubleHallRight R

theorem DoubleHallBoth.mono {R R' : X → Y → Prop} [∀ x y, Decidable (R x y)]
    [∀ x y, Decidable (R' x y)] (hR : DoubleHallBoth R) (h : ∀ x y, R x y → R' x y) :
    DoubleHallBoth R' :=
  ⟨hR.1.mono h, DoubleHallLeft.mono (R := fun y x => R x y) hR.2 (fun y x hxy => h x y hxy)⟩

theorem degL_transpose (R : X → Y → Prop) [∀ x y, Decidable (R x y)] (y : Y) :
    degL (fun y x => R x y) y = degR R y := rfl

theorem degR_transpose (R : X → Y → Prop) [∀ x y, Decidable (R x y)] (x : X) :
    degR (fun y x => R x y) x = degL R x := rfl

section Relabel

variable {X' Y' : Type*} [Fintype X'] [Fintype Y'] [DecidableEq X'] [DecidableEq Y']

/-- Relabel both sides along equivalences. -/
def relabel (eX : X ≃ X') (eY : Y ≃ Y') (R : X → Y → Prop) (x' : X') (y' : Y') : Prop :=
  R (eX.symm x') (eY.symm y')

instance (eX : X ≃ X') (eY : Y ≃ Y') (R : X → Y → Prop) [∀ x y, Decidable (R x y)] :
    ∀ x' y', Decidable (relabel eX eY R x' y') := fun _ _ => by
  unfold relabel; infer_instance

variable (eX : X ≃ X') (eY : Y ≃ Y') (R : X → Y → Prop) [∀ x y, Decidable (R x y)]

theorem relabel_doubleHallLeft (hR : DoubleHallLeft R) :
    DoubleHallLeft (relabel eX eY R) := by
  classical
  intro A hA
  set B := A.map eX.symm.toEmbedding with hB
  have hBcard : B.card = A.card := card_map _
  have h := hR B (by rw [hBcard]; exact hA)
  rw [hBcard] at h
  refine h.trans (le_of_eq_of_le (card_map eY.toEmbedding).symm (card_le_card ?_))
  intro y' hy'
  obtain ⟨y, hy, rfl⟩ := mem_map.1 hy'
  simp only [superNbrs, mem_filter, mem_univ, true_and] at hy ⊢
  refine hy.trans (le_of_eq_of_le (card_map eX.toEmbedding).symm (card_le_card ?_))
  intro x' hx'
  obtain ⟨x, hx, rfl⟩ := mem_map.1 hx'
  simp only [nbrsIn, mem_filter, hB, mem_map] at hx ⊢
  obtain ⟨⟨a, ha, rfl⟩, hxa⟩ := hx
  refine ⟨by simpa using ha, ?_⟩
  simpa [relabel] using hxa

theorem relabel_doubleHallBoth (hR : DoubleHallBoth R) :
    DoubleHallBoth (relabel eX eY R) :=
  ⟨relabel_doubleHallLeft eX eY R hR.1,
   relabel_doubleHallLeft (R := fun y x => R x y) eY eX hR.2⟩

theorem degL_relabel (x' : X') : degL (relabel eX eY R) x' = degL R (eX.symm x') := by
  classical
  unfold degL relabel
  rw [← card_map eY.symm.toEmbedding]
  congr 1
  ext y
  simp only [mem_map, mem_filter, mem_univ, true_and, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨y', h, rfl⟩; exact h
  · intro h; exact ⟨eY y, by simpa using h, by simp⟩

theorem degR_relabel (y' : Y') : degR (relabel eX eY R) y' = degR R (eY.symm y') :=
  degL_relabel (R := fun y x => R x y) eY eX y'

end Relabel

end DoubleHall
