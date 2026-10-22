import DoubleHall.Basic

/-!
# The rook-cross graph

On the `m × m` grid, join cell `(a, b)` on the left to cell `(i, j)` on the right when
`a = i` or `b = j`. This graph is `(2m - 1)`-regular, contains the diagonal matching, and has
the double Hall property on both sides.
-/

set_option linter.unusedSectionVars false

open Finset

namespace DoubleHall

namespace Rook

variable {m : ℕ}

/-- Rook-cross adjacency on the grid. -/
def adj (c d : Fin m × Fin m) : Prop := c.1 = d.1 ∨ c.2 = d.2

instance : ∀ c d : Fin m × Fin m, Decidable (adj c d) := fun _ _ => by
  unfold adj; infer_instance

theorem adj_comm (c d : Fin m × Fin m) : adj c d ↔ adj d c := by
  unfold adj; constructor <;> rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm;
    exact Or.inl h.symm; exact Or.inr h.symm]

theorem adj_self (c : Fin m × Fin m) : adj c c := Or.inl rfl

/-- A cell of `A` is isolated when it is alone in its row and alone in its column. -/
def Isolated (A : Finset (Fin m × Fin m)) (c : Fin m × Fin m) : Prop :=
  ∀ d ∈ A, adj d c → d = c

instance (A : Finset (Fin m × Fin m)) (c : Fin m × Fin m) : Decidable (Isolated A c) := by
  unfold Isolated; infer_instance

/-- A non-isolated cell of `A` is a super-neighbor of `A`. -/
theorem mem_superNbrs_of_not_isolated {A : Finset (Fin m × Fin m)} {c : Fin m × Fin m}
    (hc : c ∈ A) (hni : ¬ Isolated A c) : c ∈ superNbrs adj A := by
  simp only [Isolated, not_forall] at hni
  obtain ⟨d, hd, hdc, hne⟩ := hni
  simp only [superNbrs, mem_filter, mem_univ, true_and]
  have hsub : ({c, d} : Finset _) ⊆ nbrsIn adj A c := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    simp only [nbrsIn, mem_filter]
    rcases hz with rfl | rfl
    · exact ⟨hc, adj_self _⟩
    · exact ⟨hd, hdc⟩
  calc 2 = ({c, d} : Finset _).card := (card_pair (Ne.symm hne)).symm
    _ ≤ _ := card_le_card hsub

/-- Two distinct isolated cells lie in different rows and different columns. -/
theorem isolated_row_col {A : Finset (Fin m × Fin m)} {c d : Fin m × Fin m}
    (hc : c ∈ A) (hd : d ∈ A) (hci : Isolated A c) (hcd : c ≠ d) :
    c.1 ≠ d.1 ∧ c.2 ≠ d.2 := by
  constructor
  · intro h; exact hcd (hci d hd (Or.inl h.symm)).symm
  · intro h; exact hcd (hci d hd (Or.inr h.symm)).symm

theorem finRotate_ne_self {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : finRotate k i ≠ i := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have h1 : (1 : Fin (n + 2)) = 0 := by
    have := congrArg (fun z => z - i) h
    simpa using this
  exact absurd h1 (by simp)

/-- The rook-cross graph has the double Hall property. -/
theorem doubleHallLeft : DoubleHallLeft (adj (m := m)) := by
  classical
  intro A hA
  set I := A.filter (fun c => Isolated A c) with hI
  set N := A.filter (fun c => ¬ Isolated A c) with hN
  have hcardA : I.card + N.card = A.card := card_filter_add_card_filter_not _
  have hNsub : N ⊆ superNbrs adj A := by
    intro c hc
    simp only [hN, mem_filter] at hc
    exact mem_superNbrs_of_not_isolated hc.1 hc.2
  have hIA : I ⊆ A := filter_subset _ _
  -- cells of A that are not super-neighbors are exactly the isolated ones
  rcases Nat.lt_or_ge I.card 2 with hk | hk
  · rcases (show I.card = 0 ∨ I.card = 1 by omega) with hIc | hIc
    · -- no isolated cells
      calc A.card = N.card := by omega
        _ ≤ _ := card_le_card hNsub
    · -- one isolated cell
      obtain ⟨c, hcI⟩ := card_eq_one.1 hIc
      have hc : c ∈ I := by rw [hcI]; exact mem_singleton_self c
      have hcA : c ∈ A := hIA hc
      have hciso : Isolated A c := (mem_filter.1 hc).2
      obtain ⟨d, hdA, hdc⟩ : ∃ d ∈ A, d ≠ c := by
        by_contra h
        push_neg at h
        have : A ⊆ {c} := fun z hz => mem_singleton.2 (h z hz)
        have := card_le_card this
        simp at this; omega
      set w : Fin m × Fin m := (c.1, d.2) with hw
      have hwSN : w ∈ superNbrs adj A := by
        simp only [superNbrs, mem_filter, mem_univ, true_and]
        have hsub : ({c, d} : Finset _) ⊆ nbrsIn adj A w := by
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          simp only [nbrsIn, mem_filter]
          rcases hz with rfl | rfl
          · exact ⟨hcA, Or.inl rfl⟩
          · exact ⟨hdA, Or.inr rfl⟩
        calc 2 = ({c, d} : Finset _).card := (card_pair hdc.symm).symm
          _ ≤ _ := card_le_card hsub
      have hwN : w ∉ N := by
        intro hwN
        have hwA : w ∈ A := (mem_filter.1 hwN).1
        have hwc : w = c := hciso w hwA (Or.inl rfl)
        have hd2 : d.2 = c.2 := by have := congrArg Prod.snd hwc; simpa [hw] using this
        exact hdc (hciso d hdA (Or.inr hd2))
      calc A.card = N.card + 1 := by omega
        _ = (insert w N).card := (card_insert_of_notMem hwN).symm
        _ ≤ _ := card_le_card (insert_subset hwSN hNsub)
  · -- at least two isolated cells: use the cyclic cross cells
    set k := I.card with hkdef
    let e : {c // c ∈ I} ≃ Fin k := I.equivFin
    let σ : {c // c ∈ I} → {c // c ∈ I} := fun c => e.symm (finRotate k (e c))
    have hσne : ∀ c, σ c ≠ c := by
      intro c h
      apply finRotate_ne_self hk (e c)
      have := congrArg e h
      simpa [σ] using this
    let cross : {c // c ∈ I} → Fin m × Fin m := fun c => (c.1.1, (σ c).1.2)
    have hcrossinj : Function.Injective cross := by
      intro c c' h
      have h1 : c.1.1 = c'.1.1 := by have := congrArg Prod.fst h; simpa [cross] using this
      by_contra hne
      have hne' : c.1 ≠ c'.1 := fun h => hne (Subtype.ext h)
      exact (isolated_row_col (hIA c.2) (hIA c'.2) (mem_filter.1 c.2).2 hne').1 h1
    set Cr : Finset (Fin m × Fin m) := univ.image cross with hCr
    have hCrcard : Cr.card = k := by
      rw [hCr, card_image_of_injective _ hcrossinj, card_univ, Fintype.card_coe]
    have hCrSN : Cr ⊆ superNbrs adj A := by
      intro w hw
      obtain ⟨c, _, rfl⟩ := mem_image.1 hw
      simp only [superNbrs, mem_filter, mem_univ, true_and]
      have hne : c.1 ≠ (σ c).1 := fun h => hσne c (Subtype.ext h.symm)
      have hsub : ({c.1, (σ c).1} : Finset _) ⊆ nbrsIn adj A (cross c) := by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        simp only [nbrsIn, mem_filter]
        rcases hz with rfl | rfl
        · exact ⟨hIA c.2, Or.inl rfl⟩
        · exact ⟨hIA (σ c).2, Or.inr rfl⟩
      calc 2 = ({c.1, (σ c).1} : Finset _).card := (card_pair hne).symm
        _ ≤ _ := card_le_card hsub
    have hdisj : Disjoint N Cr := by
      rw [disjoint_left]
      intro w hwN hwCr
      obtain ⟨c, _, rfl⟩ := mem_image.1 hwCr
      have hwA : cross c ∈ A := (mem_filter.1 hwN).1
      have hciso : Isolated A c.1 := (mem_filter.1 c.2).2
      have hwc : cross c = c.1 := hciso _ hwA (Or.inl rfl)
      have h2 : (σ c).1.2 = c.1.2 := by have := congrArg Prod.snd hwc; simpa [cross] using this
      have hne : c.1 ≠ (σ c).1 := fun h => hσne c (Subtype.ext h.symm)
      exact (isolated_row_col (hIA c.2) (hIA (σ c).2) hciso hne).2 h2.symm
    calc A.card = N.card + Cr.card := by omega
      _ = (N ∪ Cr).card := (card_union_of_disjoint hdisj).symm
      _ ≤ _ := card_le_card (union_subset hNsub hCrSN)

/-- Degrees in the rook-cross graph. -/
theorem degL_eq (c : Fin m × Fin m) : degL (adj (m := m)) c = 2 * m - 1 := by
  classical
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; exact c.1.elim0
    · exact h
  have hrow : (univ.filter (fun d : Fin m × Fin m => c.1 = d.1)).card = m := by
    have : univ.filter (fun d : Fin m × Fin m => c.1 = d.1) = ({c.1} : Finset (Fin m)) ×ˢ univ := by
      ext d; simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]; constructor <;> intro h <;> simp_all [eq_comm]
    rw [this, card_product]; simp
  have hcol : (univ.filter (fun d : Fin m × Fin m => c.2 = d.2)).card = m := by
    have : univ.filter (fun d : Fin m × Fin m => c.2 = d.2) = (univ : Finset (Fin m)) ×ˢ {c.2} := by
      ext d; simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]; constructor <;> intro h <;> simp_all [eq_comm]
    rw [this, card_product]; simp
  have hint : (univ.filter (fun d : Fin m × Fin m => c.1 = d.1)) ∩
      (univ.filter (fun d : Fin m × Fin m => c.2 = d.2)) = {c} := by
    ext d; simp only [mem_inter, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact Prod.ext h1.symm h2.symm
    · rintro rfl; exact ⟨rfl, rfl⟩
  have hunion : univ.filter (fun d => adj c d) =
      (univ.filter (fun d : Fin m × Fin m => c.1 = d.1)) ∪
        (univ.filter (fun d : Fin m × Fin m => c.2 = d.2)) := by
    ext d; simp [adj]
  have := card_union_add_card_inter (univ.filter (fun d : Fin m × Fin m => c.1 = d.1))
    (univ.filter (fun d : Fin m × Fin m => c.2 = d.2))
  rw [hint, hrow, hcol, card_singleton] at this
  unfold degL
  rw [hunion]
  omega

theorem degR_eq (d : Fin m × Fin m) : degR (adj (m := m)) d = 2 * m - 1 := by
  have h := degL_eq (m := m) d
  unfold degL at h; unfold degR
  rw [← h]
  congr 1
  ext c; simp [adj_comm]

end Rook

end DoubleHall
