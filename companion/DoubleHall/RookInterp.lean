import DoubleHall.Rook
import DoubleHall.Duplicate
import DoubleHall.Completion
import DoubleHall.Transport

/-!
# Regular two-sided double-Hall graphs of degree `2⌊√g⌋ + 4` at every order `g ≥ 576`

Duplicate `t = g - m²` cells of the two cyclic diagonals of the rook-cross graph on the
`m × m` grid (`m = ⌊√g⌋`), then complete to a regular graph of degree `2m + 4`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace DoubleHall

namespace RookInterp

/-- The two cyclic diagonals of the grid. -/
def diagCells (m : ℕ) : Finset (Fin m × Fin m) :=
  univ.image (fun i : Fin m => (i, i)) ∪ univ.image (fun i : Fin m => (i, finRotate m i))

theorem card_diagCells {m : ℕ} (hm : 2 ≤ m) : (diagCells m).card = 2 * m := by
  unfold diagCells
  rw [card_union_of_disjoint]
  · rw [card_image_of_injective, card_image_of_injective, card_univ, Fintype.card_fin]
    · ring
    · intro i j h; exact congrArg Prod.fst h
    · intro i j h; exact congrArg Prod.fst h
  · rw [disjoint_left]
    intro c h1 h2
    obtain ⟨i, _, rfl⟩ := mem_image.1 h1
    obtain ⟨j, _, h⟩ := mem_image.1 h2
    have hij : j = i := congrArg Prod.fst h
    subst hij
    have : finRotate m j = j := congrArg Prod.snd h
    exact Rook.finRotate_ne_self hm j this

/-- Diagonal cells in a fixed row. -/
theorem card_diag_row_le (m : ℕ) (a : Fin m) :
    ((diagCells m).filter (fun c => c.1 = a)).card ≤ 2 := by
  have : (diagCells m).filter (fun c => c.1 = a) ⊆ {(a, a), (a, finRotate m a)} := by
    intro c hc
    simp only [diagCells, mem_filter, mem_union, mem_image, mem_univ, true_and] at hc
    obtain ⟨⟨i, rfl⟩ | ⟨i, rfl⟩, hca⟩ := hc
    · simp only at hca; subst hca; simp
    · simp only at hca; subst hca; simp
  exact (card_le_card this).trans (card_insert_le _ _)

/-- Diagonal cells in a fixed column. -/
theorem card_diag_col_le (m : ℕ) (b : Fin m) :
    ((diagCells m).filter (fun c => c.2 = b)).card ≤ 2 := by
  have : (diagCells m).filter (fun c => c.2 = b) ⊆ {(b, b), ((finRotate m).symm b, b)} := by
    intro c hc
    simp only [diagCells, mem_filter, mem_union, mem_image, mem_univ, true_and] at hc
    obtain ⟨⟨i, rfl⟩ | ⟨i, rfl⟩, hcb⟩ := hc
    · simp only at hcb; subst hcb; simp
    · simp only at hcb; subst hcb
      apply mem_insert_of_mem
      rw [mem_singleton, Equiv.symm_apply_apply]
  exact (card_le_card this).trans (card_insert_le _ _)

/-- Every rook neighborhood contains at most four selected diagonal cells. -/
theorem load_le_four {m : ℕ} {T : Finset (Fin m × Fin m)} (hT : T ⊆ diagCells m)
    (c : Fin m × Fin m) : (univ.filter (fun d => Rook.adj c d) ∩ T).card ≤ 4 := by
  have hsub : univ.filter (fun d => Rook.adj c d) ∩ T ⊆
      (diagCells m).filter (fun d => d.1 = c.1) ∪ (diagCells m).filter (fun d => d.2 = c.2) := by
    intro d hd
    simp only [mem_inter, mem_filter, mem_univ, true_and, Rook.adj] at hd
    obtain ⟨h | h, hdT⟩ := hd
    · exact mem_union_left _ (mem_filter.2 ⟨hT hdT, h.symm⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨hT hdT, h.symm⟩)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ 2 + 2 := add_le_add (card_diag_row_le m c.1) (card_diag_col_le m c.2)

theorem sum_mult {ι : Type*} [DecidableEq ι] (T S : Finset ι) :
    ∑ j ∈ S, Dup.mult T j = S.card + (S ∩ T).card := by
  have : ∀ j ∈ S, Dup.mult T j = 1 + (if j ∈ T then 1 else 0) := by
    intro j _; unfold Dup.mult; split_ifs <;> rfl
  rw [sum_congr rfl this, sum_add_distrib, sum_const, smul_eq_mul, mul_one, sum_boole,
    filter_mem_eq_inter, Nat.cast_id]

/-- Degree of a vertex of the duplicated rook graph. -/
theorem deg_dup {m : ℕ} (hm : 1 ≤ m) (T : Finset (Fin m × Fin m)) (p : Dup.V T) :
    degL (Dup.dupRel Rook.adj T) p =
      (2 * m - 1) + (univ.filter (fun d => Rook.adj p.1 d) ∩ T).card := by
  rw [Dup.degL_dup, sum_mult]
  congr 1
  exact Rook.degL_eq p.1

theorem dupRel_symm {m : ℕ} (T : Finset (Fin m × Fin m)) (p q : Dup.V T) :
    Dup.dupRel Rook.adj T p q ↔ Dup.dupRel Rook.adj T q p := by
  unfold Dup.dupRel; exact Rook.adj_comm _ _

theorem degR_dup_eq_degL {m : ℕ} (T : Finset (Fin m × Fin m)) (p : Dup.V T) :
    degR (Dup.dupRel Rook.adj T) p = degL (Dup.dupRel Rook.adj T) p := by
  unfold degR degL
  congr 1; ext q; simp [dupRel_symm T q p]

theorem dup_doubleHallBoth {m : ℕ} (T : Finset (Fin m × Fin m)) :
    DoubleHallBoth (Dup.dupRel Rook.adj T) := by
  refine ⟨Dup.doubleHallLeft Rook.adj Rook.adj_self Rook.doubleHallLeft T, ?_⟩
  have h := Dup.doubleHallLeft Rook.adj Rook.adj_self Rook.doubleHallLeft T
  unfold DoubleHallRight
  have heq : (fun q p : Dup.V T => Dup.dupRel Rook.adj T p q) = Dup.dupRel Rook.adj T := by
    funext q p; exact propext (dupRel_symm T p q)
  intro A hA
  have := h A hA
  convert this using 3

theorem card_V {m : ℕ} (T : Finset (Fin m × Fin m)) :
    Fintype.card (Dup.V T) = m * m + T.card := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [sum_mult, card_univ, univ_inter, Fintype.card_prod, Fintype.card_fin]

open scoped Classical in
/-- For every `g ≥ 576` there is a balanced `(2⌊√g⌋ + 4)`-regular bipartite graph on
`Fin g` with double Hall on both sides and every diagonal edge. -/
theorem exists_local (g : ℕ) (hg : 576 ≤ g) :
    ∃ L : Fin g → Fin g → Prop,
      DoubleHallBoth L ∧ IsRegular L (2 * Nat.sqrt g + 4) ∧ ∀ i, L i i := by
  set m := Nat.sqrt g with hmdef
  have hm24 : 24 ≤ m := Nat.le_sqrt.2 (by omega)
  have hmsq : m * m ≤ g := Nat.sqrt_le g
  have hlt : g < (m + 1) * (m + 1) := Nat.lt_succ_sqrt g
  set t := g - m * m with htdef
  have ht : t ≤ 2 * m := by
    have : g ≤ m * m + 2 * m := by nlinarith
    omega
  obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card_eq
    (show t ≤ (diagCells m).card by rw [card_diagCells (by omega)]; exact ht)
  have hcardV : Fintype.card (Dup.V T) = g := by rw [card_V, hTcard]; omega
  have hdeg : ∀ p : Dup.V T, 2 * m - 1 ≤ degL (Dup.dupRel Rook.adj T) p ∧ degL (Dup.dupRel Rook.adj T) p ≤ 2 * m + 3 := by
    intro p
    rw [deg_dup (by omega) T p]
    have := load_le_four hTsub p.1
    omega
  have hdegR : ∀ p : Dup.V T, 2 * m - 1 ≤ degR (Dup.dupRel Rook.adj T) p ∧ degR (Dup.dupRel Rook.adj T) p ≤ 2 * m + 3 := by
    intro p; rw [degR_dup_eq_degL]; exact hdeg p
  obtain ⟨G, hHG, hGx, hGy⟩ := exists_regular_supergraph (H := Dup.dupRel Rook.adj T) (D := 2 * m + 4) (a := 5)
    (b := 5) (r := 2 * m + 3) (c := 2 * m + 3)
    (fun x => by have := hdeg x; omega) (fun y => by have := hdegR y; omega)
    (fun x => by have := hdeg x; omega) (fun y => by have := hdegR y; omega)
    (fun x => (hdeg x).2) (fun y => (hdegR y).2) rfl
    (by
      have hsum : (Fintype.card (Dup.V T)) ≤ ∑ y : Dup.V T, (2 * m + 4 - degR (Dup.dupRel Rook.adj T) y) := by
        calc Fintype.card (Dup.V T) = ∑ _y : Dup.V T, 1 := by simp
          _ ≤ _ := sum_le_sum (fun y _ => by have := hdegR y; omega)
      rw [hcardV] at hsum
      nlinarith)
  -- relabel to `Fin g`
  let e : Dup.V T ≃ Fin g := Fintype.equivFinOfCardEq hcardV
  refine ⟨relabel e e G, ?_, ⟨fun i => ?_, fun i => ?_⟩, fun i => ?_⟩
  · have hGboth : DoubleHallBoth G := (dup_doubleHallBoth T).mono hHG
    exact relabel_doubleHallBoth e e G hGboth
  · calc degL (relabel e e G) i = degL G (e.symm i) := by convert degL_relabel e e G i
      _ = 2 * m + 4 := by unfold degL; convert hGx (e.symm i) using 2
  · calc degR (relabel e e G) i = degR G (e.symm i) := by convert degR_relabel e e G i
      _ = 2 * m + 4 := by unfold degR; convert hGy (e.symm i) using 2
  · exact hHG _ _ (Rook.adj_self _)

end RookInterp

end DoubleHall
