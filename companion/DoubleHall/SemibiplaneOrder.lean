import DoubleHall.SemibiplaneFibers
import DoubleHall.RookInterp

/-!
# Regular two-sided double-Hall graphs at semibiplane orders

Repair every empty class rectangle of the homology semibiplane with a fixed balanced regular
two-sided double-Hall graph on `g = (q - 1)/2` vertices per side.
-/

set_option linter.unusedSectionVars false

open Finset

namespace DoubleHall

section Labels

variable {Z J : Type*} [Fintype Z] [DecidableEq Z] [DecidableEq J]

/-- If every fiber of `κ` has `g` elements, there is a labelling `Z → Fin g` that is a
bijection on every fiber. -/
theorem exists_fiber_labels (κ : Z → J) (g : ℕ)
    (hcard : ∀ j, (univ.filter (fun z => κ z = j)).card = g) :
    ∃ e : Z → Fin g, (∀ z z', κ z = κ z' → e z = e z' → z = z') ∧
      (∀ j (w : Fin g), ∃ z, κ z = j ∧ e z = w) := by
  classical
  have hc : ∀ j, Fintype.card {z // κ z = j} = g := by
    intro j; rw [Fintype.card_subtype]; exact hcard j
  let eqv : ∀ j, {z // κ z = j} ≃ Fin g := fun j => Fintype.equivFinOfCardEq (hc j)
  let e : Z → Fin g := fun z => eqv (κ z) ⟨z, rfl⟩
  have he : ∀ z j (hz : κ z = j), e z = eqv j ⟨z, hz⟩ := by
    intro z j hz; subst hz; rfl
  refine ⟨e, ?_, ?_⟩
  · intro z z' hzz h
    rw [he z (κ z) rfl, he z' (κ z) hzz.symm] at h
    exact congrArg Subtype.val ((eqv (κ z)).injective h)
  · intro j w
    refine ⟨((eqv j).symm w).1, ((eqv j).symm w).2, ?_⟩
    rw [he _ j ((eqv j).symm w).2]
    simp

end Labels

namespace Semibiplane

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem clsY_eq_iff_cls_eq (y y' : Pt F) : clsY y = clsY y' ↔ cls y = cls y' := by
  rw [clsY_eq_iff, cls_eq_iff]

theorem card_cls_fiber (hF : (2 : F) ≠ 0) {g : ℕ} (hg : 2 * g = Fintype.card F - 1) (L : Line F) :
    (univ.filter (fun c : Pt F => cls c = L)).card = g := by
  have := two_mul_card_cls hF L; omega

theorem card_clsY_fiber (hF : (2 : F) ≠ 0) {g : ℕ} (hg : 2 * g = Fintype.card F - 1) (L : Line F) :
    (univ.filter (fun c : Pt F => clsY c = L)).card = g := by
  have := two_mul_card_clsY hF L; omega

/-- The repaired semibiplane: incidence plus a local graph in every paired class rectangle. -/
def repaired {g : ℕ} (eX eY : Pt F → Fin g) (Loc : Fin g → Fin g → Prop) (x y : Pt F) : Prop :=
  Inc x y ∨ localRel cls clsY eX eY Loc x y

open scoped Classical in
/-- The repaired semibiplane is `(q + h)`-regular with double Hall on both sides, for any
fiber labellings. -/
theorem repaired_props (hF : (2 : F) ≠ 0) {g h : ℕ} (Loc : Fin g → Fin g → Prop)
    (hLoc : DoubleHallBoth Loc) (hLreg : IsRegular Loc h) {eX eY : Pt F → Fin g}
    (heXinj : ∀ z z', cls z = cls z' → eX z = eX z' → z = z')
    (heXsurj : ∀ (j : Line F) (w : Fin g), ∃ z, cls z = j ∧ eX z = w)
    (heYinj : ∀ z z', clsY z = clsY z' → eY z = eY z' → z = z')
    (heYsurj : ∀ (j : Line F) (w : Fin g), ∃ z, clsY z = j ∧ eY z = w) :
    DoubleHallBoth (repaired eX eY Loc) ∧ IsRegular (repaired eX eY Loc) (Fintype.card F + h) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- left side
    have := doubleHallLeft_union_of_classes cls Inc (localRel cls clsY eX eY Loc)
      (fun A hA hone => card_le_superNbrs_of_not_inOneClass hF A hone)
      (fun A hA hone => localRel_hall heXinj heYsurj hLoc.1 A hA hone)
    convert this using 2
    rfl
  · -- right side
    unfold DoubleHallRight
    have hB : ∀ A : Finset (Pt F), 2 ≤ A.card → ¬ InOneClass clsY A →
        A.card ≤ (superNbrs (fun y x => Inc x y) A).card := by
      intro A hA hone
      have hone' : ¬ InOneClass cls A := by
        intro h; apply hone
        intro a ha b hb; exact (clsY_eq_iff_cls_eq a b).2 (h a ha b hb)
      have := card_le_superNbrs_of_not_inOneClass hF A hone'
      convert this using 3
      ext x; simp [inc_comm]
    have hL : ∀ A : Finset (Pt F), 2 ≤ A.card → InOneClass clsY A →
        A.card ≤ (superNbrs (fun y x => localRel cls clsY eX eY Loc x y) A).card := by
      intro A hA hone
      have := localRel_hall (κX := clsY) (κY := cls) (eX := eY) (eY := eX)
        (Loc := fun a b => Loc b a) heYinj heXsurj hLoc.2 A hA hone
      convert this using 3
      ext y; simp [localRel, eq_comm]
    have := doubleHallLeft_union_of_classes clsY (fun y x => Inc x y)
      (fun y x => localRel cls clsY eX eY Loc x y) hB hL
    convert this using 2
    rfl
  · -- regularity
    have hdisj : ∀ x y, Inc x y → ¬ localRel cls clsY eX eY Loc x y := by
      intro x y hinc hl
      exact not_inc_of_cls_eq_clsY x y hl.1 hinc
    have hIreg : IsRegular (Inc (F := F)) (Fintype.card F) :=
      ⟨fun x => degL_inc hF x, fun y => degR_inc hF y⟩
    have hLreg' : IsRegular (localRel cls clsY eX eY Loc) h :=
      ⟨fun x => by rw [degL_localRel heYsurj heYinj]; exact hLreg.1 _,
       fun y => by rw [degR_localRel heXsurj heXinj]; exact hLreg.2 _⟩
    have := isRegular_union_of_disjoint _ _ hdisj hIreg hLreg'
    unfold IsRegular at this ⊢
    obtain ⟨h1, h2⟩ := this
    refine ⟨fun x => ?_, fun y => ?_⟩
    · rw [← h1 x]; unfold degL; congr 1; ext; simp [repaired]
    · rw [← h2 y]; unfold degR; congr 1; ext; simp [repaired]

open scoped Classical in
/-- **Semibiplane-order theorem.** If `|F| = q` is odd, `2g = q - 1`, and `Loc` is a balanced
`h`-regular graph on `Fin g` with double Hall on both sides, then the homology semibiplane
repaired by `Loc` is `(q + h)`-regular with double Hall on both sides. -/
theorem repaired_doubleHallBoth_regular (hF : (2 : F) ≠ 0) {g h : ℕ}
    (hg : 2 * g = Fintype.card F - 1) (Loc : Fin g → Fin g → Prop)
    (hLoc : DoubleHallBoth Loc) (hLreg : IsRegular Loc h) :
    ∃ eX eY : Pt F → Fin g,
      DoubleHallBoth (repaired eX eY Loc) ∧ IsRegular (repaired eX eY Loc) (Fintype.card F + h) := by
  obtain ⟨eX, heXinj, heXsurj⟩ := exists_fiber_labels cls g (card_cls_fiber hF hg)
  obtain ⟨eY, heYinj, heYsurj⟩ := exists_fiber_labels clsY g (card_clsY_fiber hF hg)
  exact ⟨eX, eY, repaired_props hF Loc hLoc hLreg heXinj heXsurj heYinj heYsurj⟩

end Semibiplane

end DoubleHall
