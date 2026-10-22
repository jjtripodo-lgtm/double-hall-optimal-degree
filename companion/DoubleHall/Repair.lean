import DoubleHall.Basic

/-!
# Class repair

Suppose the left side is partitioned into classes by `κ : X → I`. If a base graph `B` handles
every subset that meets two classes, and a local graph `L` handles every subset inside one
class, then `B ∪ L` has the double Hall property. If `B` and `L` share no edge, degrees add.
-/

set_option linter.unusedSectionVars false

open Finset

namespace DoubleHall

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {I : Type*} (κ : X → I)

/-- `A` lies inside a single class. -/
def InOneClass (A : Finset X) : Prop := ∀ a ∈ A, ∀ b ∈ A, κ a = κ b

variable (B L : X → Y → Prop) [∀ x y, Decidable (B x y)] [∀ x y, Decidable (L x y)]

theorem doubleHallLeft_union_of_classes
    (hB : ∀ A : Finset X, 2 ≤ A.card → ¬ InOneClass κ A → A.card ≤ (superNbrs B A).card)
    (hL : ∀ A : Finset X, 2 ≤ A.card → InOneClass κ A → A.card ≤ (superNbrs L A).card) :
    DoubleHallLeft (fun x y => B x y ∨ L x y) := by
  intro A hA
  by_cases hone : InOneClass κ A
  · exact (hL A hA hone).trans
      (card_le_card (superNbrs_mono (fun x y h => Or.inr h) A))
  · exact (hB A hA hone).trans
      (card_le_card (superNbrs_mono (fun x y h => Or.inl h) A))

theorem degL_union_of_disjoint (hdisj : ∀ x y, B x y → ¬ L x y) (x : X) :
    degL (fun x y => B x y ∨ L x y) x = degL B x + degL L x := by
  unfold degL
  rw [← card_union_of_disjoint]
  · congr 1; ext y; simp
  · rw [disjoint_filter]; intro y _ hb hl; exact hdisj x y hb hl

theorem degR_union_of_disjoint (hdisj : ∀ x y, B x y → ¬ L x y) (y : Y) :
    degR (fun x y => B x y ∨ L x y) y = degR B y + degR L y := by
  unfold degR
  rw [← card_union_of_disjoint]
  · congr 1; ext x; simp
  · rw [disjoint_filter]; intro x _ hb hl; exact hdisj x y hb hl

theorem isRegular_union_of_disjoint {d h : ℕ} (hdisj : ∀ x y, B x y → ¬ L x y)
    (hBreg : IsRegular B d) (hLreg : IsRegular L h) :
    IsRegular (fun x y => B x y ∨ L x y) (d + h) :=
  ⟨fun x => by rw [degL_union_of_disjoint B L hdisj, hBreg.1, hLreg.1],
   fun y => by rw [degR_union_of_disjoint B L hdisj, hBreg.2, hLreg.2]⟩

section Localize

variable {J : Type*} [DecidableEq J] (κX : X → J) (κY : Y → J) {g : ℕ}
  (eX : X → Fin g) (eY : Y → Fin g) (Loc : Fin g → Fin g → Prop)
  [∀ a b, Decidable (Loc a b)]

/-- Insert a copy of `Loc` into every class rectangle `κX⁻¹(i) × κY⁻¹(i)`. -/
def localRel (x : X) (y : Y) : Prop := κX x = κY y ∧ Loc (eX x) (eY y)

instance : ∀ x y, Decidable (localRel κX κY eX eY Loc x y) := fun _ _ => by
  unfold localRel; infer_instance

variable {κX κY eX eY Loc}

theorem localRel_hall
    (heX : ∀ x x', κX x = κX x' → eX x = eX x' → x = x')
    (heY : ∀ i (z : Fin g), ∃ y, κY y = i ∧ eY y = z)
    (hLoc : DoubleHallLeft Loc) (A : Finset X) (hA : 2 ≤ A.card) (hone : InOneClass κX A) :
    A.card ≤ (superNbrs (localRel κX κY eX eY Loc) A).card := by
  classical
  obtain ⟨x₀, hx₀⟩ : A.Nonempty := card_pos.1 (by omega)
  set i := κX x₀
  have hinj : Set.InjOn eX A := fun x hx x' hx' h => heX x x' (hone x hx x' hx') h
  set A' := A.image eX with hA'
  have hA'card : A'.card = A.card := card_image_of_injOn hinj
  have hSN := hLoc A' (by rw [hA'card]; exact hA)
  choose yOf hyOfκ hyOfe using heY i
  have hyinj : Function.Injective yOf := by
    intro z z' h; rw [← hyOfe z, ← hyOfe z', h]
  have hsub : (superNbrs Loc A').image yOf ⊆ superNbrs (localRel κX κY eX eY Loc) A := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hy
    simp only [superNbrs, mem_filter, mem_univ, true_and] at hz ⊢
    refine hz.trans ?_
    have : nbrsIn Loc A' z ⊆ (nbrsIn (localRel κX κY eX eY Loc) A (yOf z)).image eX := by
      intro w hw
      simp only [nbrsIn, mem_filter, hA', mem_image] at hw
      obtain ⟨⟨x, hx, rfl⟩, hl⟩ := hw
      refine mem_image.2 ⟨x, ?_, rfl⟩
      simp only [nbrsIn, mem_filter, localRel]
      refine ⟨hx, ?_, ?_⟩
      · rw [hyOfκ]; exact hone x hx x₀ hx₀
      · rw [hyOfe]; exact hl
    exact (card_le_card this).trans card_image_le
  calc A.card = A'.card := hA'card.symm
    _ ≤ (superNbrs Loc A').card := hSN
    _ = ((superNbrs Loc A').image yOf).card := (card_image_of_injective _ hyinj).symm
    _ ≤ _ := card_le_card hsub

theorem degL_localRel
    (heY : ∀ i (z : Fin g), ∃ y, κY y = i ∧ eY y = z)
    (heY' : ∀ y y', κY y = κY y' → eY y = eY y' → y = y') (x : X) :
    degL (localRel κX κY eX eY Loc) x = degL Loc (eX x) := by
  classical
  unfold degL
  choose yOf hyOfκ hyOfe using heY (κX x)
  have : univ.filter (fun y => localRel κX κY eX eY Loc x y) =
      (univ.filter (fun z => Loc (eX x) z)).image yOf := by
    ext y
    simp only [mem_filter, mem_univ, true_and, localRel, mem_image]
    constructor
    · rintro ⟨hk, hl⟩
      refine ⟨eY y, hl, heY' _ _ (by rw [hyOfκ, hk]) (hyOfe _)⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(hyOfκ z).symm, by rw [hyOfe]; exact hz⟩
  rw [this, card_image_of_injective]
  intro z z' h; rw [← hyOfe z, ← hyOfe z', h]

theorem degR_localRel
    (heX : ∀ i (z : Fin g), ∃ x, κX x = i ∧ eX x = z)
    (heX' : ∀ x x', κX x = κX x' → eX x = eX x' → x = x') (y : Y) :
    degR (localRel κX κY eX eY Loc) y = degR Loc (eY y) := by
  classical
  unfold degR
  choose xOf hxOfκ hxOfe using heX (κY y)
  have : univ.filter (fun x => localRel κX κY eX eY Loc x y) =
      (univ.filter (fun z => Loc z (eY y))).image xOf := by
    ext x
    simp only [mem_filter, mem_univ, true_and, localRel, mem_image]
    constructor
    · rintro ⟨hk, hl⟩
      exact ⟨eX x, hl, heX' _ _ (by rw [hxOfκ, hk]) (hxOfe _)⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hxOfκ z, by rw [hxOfe]; exact hz⟩
  rw [this, card_image_of_injective]
  intro z z' h; rw [← hxOfe z, ← hxOfe z', h]

end Localize

end DoubleHall
