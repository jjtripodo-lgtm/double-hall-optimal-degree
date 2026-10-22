import DoubleHall.Basic

/-!
# Matched duplication

Let `H` be a balanced bipartite graph on index set `ι` (left vertex `i`, right vertex `i`)
with every diagonal edge `H i i`. Duplicating the left and right vertex of every index in `T`
(copying all incidences) preserves the double Hall property.

We model the duplicated graph on `Σ i, Fin (mult T i)` with `mult T i = 2` for `i ∈ T` and
`1` otherwise; copies are adjacent exactly when their indices are adjacent in `H`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace DoubleHall

namespace Dup

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multiplicity of an index after duplication. -/
def mult (T : Finset ι) (i : ι) : ℕ := if i ∈ T then 2 else 1

theorem one_le_mult (T : Finset ι) (i : ι) : 1 ≤ mult T i := by
  unfold mult; split_ifs <;> omega

theorem mult_le_two (T : Finset ι) (i : ι) : mult T i ≤ 2 := by
  unfold mult; split_ifs <;> omega

/-- Vertices after duplication. -/
abbrev V (T : Finset ι) := Σ i : ι, Fin (mult T i)

/-- The duplicated graph. -/
def dupRel (H : ι → ι → Prop) (T : Finset ι) (p q : V T) : Prop := H p.1 q.1

instance (H : ι → ι → Prop) [∀ i j, Decidable (H i j)] (T : Finset ι) :
    ∀ p q : V T, Decidable (dupRel H T p q) := fun _ _ => by
  unfold dupRel; infer_instance

/-- The first copy of an index. -/
def c0 (T : Finset ι) (i : ι) : V T := ⟨i, ⟨0, one_le_mult T i⟩⟩

variable (H : ι → ι → Prop) [∀ i j, Decidable (H i j)]

/-- Matched duplication preserves the double Hall property. -/
theorem doubleHallLeft (hdiag : ∀ i, H i i) (hH : DoubleHallLeft H) (T : Finset ι) :
    DoubleHallLeft (dupRel H T) := by
  classical
  intro A hA
  set B : Finset ι := A.image Sigma.fst with hB
  -- indices with both copies in A
  set D : Finset ι := B.filter (fun i => 2 ≤ (A.filter (fun p => p.1 = i)).card) with hD
  -- |A| = |B| + |D|
  have hfiber : ∀ i ∈ B, (A.filter (fun p => p.1 = i)).card ≤ 2 := by
    intro i _
    calc (A.filter (fun p => p.1 = i)).card
        ≤ ((univ : Finset (Fin (mult T i))).image (fun j => (⟨i, j⟩ : V T))).card := by
          apply card_le_card
          intro p hp
          simp only [mem_filter] at hp
          obtain ⟨j, k⟩ := p
          simp only at hp
          obtain rfl := hp.2
          exact mem_image.2 ⟨k, mem_univ _, rfl⟩
      _ ≤ (univ : Finset (Fin (mult T i))).card := card_image_le
      _ = mult T i := by simp
      _ ≤ 2 := mult_le_two T i
  have hfiber_le_mult : ∀ i, (A.filter (fun p => p.1 = i)).card ≤ mult T i := by
    intro i
    calc (A.filter (fun p => p.1 = i)).card
        ≤ ((univ : Finset (Fin (mult T i))).image (fun j => (⟨i, j⟩ : V T))).card := by
          apply card_le_card
          intro p hp
          simp only [mem_filter] at hp
          obtain ⟨j, k⟩ := p
          simp only at hp
          obtain rfl := hp.2
          exact mem_image.2 ⟨k, mem_univ _, rfl⟩
      _ ≤ (univ : Finset (Fin (mult T i))).card := card_image_le
      _ = mult T i := by simp
  have hcardA : A.card = B.card + D.card := by
    rw [card_eq_sum_card_image Sigma.fst A]
    rw [← hB]
    have : ∀ i ∈ B, (A.filter (fun p => p.1 = i)).card
        = 1 + (if 2 ≤ (A.filter (fun p => p.1 = i)).card then 1 else 0) := by
      intro i hi
      have hpos : 0 < (A.filter (fun p => p.1 = i)).card := by
        obtain ⟨p, hp, rfl⟩ := mem_image.1 hi
        exact card_pos.2 ⟨p, mem_filter.2 ⟨hp, rfl⟩⟩
      have := hfiber i hi
      split_ifs <;> omega
    rw [sum_congr rfl this, sum_add_distrib, sum_const, smul_eq_mul, mul_one, ← sum_filter,
      sum_const, smul_eq_mul, mul_one]
  -- the second copies of doubled indices are super-neighbors
  have hmultD : ∀ i ∈ D, 1 < mult T i := by
    intro i hi
    have h2 := (mem_filter.1 hi).2
    have := hfiber_le_mult i
    omega
  let c1 : {i // i ∈ D} → V T := fun i => ⟨i.1, ⟨1, hmultD i.1 i.2⟩⟩
  have hc1inj : Function.Injective c1 := by
    intro i j h
    exact Subtype.ext (congrArg Sigma.fst h)
  have hc1SN : ∀ i : {i // i ∈ D}, c1 i ∈ superNbrs (dupRel H T) A := by
    intro i
    simp only [superNbrs, mem_filter, mem_univ, true_and]
    have h2 := (mem_filter.1 i.2).2
    refine h2.trans (card_le_card ?_)
    intro p hp
    simp only [mem_filter] at hp
    simp only [nbrsIn, mem_filter, dupRel]
    exact ⟨hp.1, by rw [hp.2]; exact hdiag _⟩
  set S1 : Finset (V T) := univ.image c1 with hS1
  have hS1card : S1.card = D.card := by
    rw [hS1, card_image_of_injective _ hc1inj, card_univ, Fintype.card_coe]
  have hS1sub : S1 ⊆ superNbrs (dupRel H T) A := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := mem_image.1 hw
    exact hc1SN i
  -- first copies are never second copies
  have hdisj : ∀ S0 : Finset ι, Disjoint (S0.image (c0 T)) S1 := by
    intro S0
    rw [disjoint_left]
    intro w h0 h1
    obtain ⟨j, _, rfl⟩ := mem_image.1 h0
    obtain ⟨i, _, h⟩ := mem_image.1 h1
    have := congrArg (fun p : V T => (p.2 : ℕ)) h
    simp [c0, c1] at this
  have hc0inj : Function.Injective (c0 T) := by
    intro i j h; exact congrArg Sigma.fst h
  rcases Nat.lt_or_ge B.card 2 with hB2 | hB2
  · -- one index, doubled
    have hBpos : 0 < B.card := by
      rw [hB, card_pos]
      obtain ⟨p, hp⟩ : A.Nonempty := card_pos.1 (by omega)
      exact ⟨p.1, mem_image.2 ⟨p, hp, rfl⟩⟩
    have hB1 : B.card = 1 := by omega
    obtain ⟨i, hBi⟩ := card_eq_one.1 hB1
    have hiB : i ∈ B := by rw [hBi]; exact mem_singleton_self i
    have hS0sub : ({i} : Finset ι).image (c0 T) ⊆ superNbrs (dupRel H T) A := by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hw
      rw [mem_singleton] at hj; subst hj
      simp only [superNbrs, mem_filter, mem_univ, true_and]
      have hfib : A.filter (fun p => p.1 = j) = A := by
        ext p
        simp only [mem_filter, and_iff_left_iff_imp]
        intro hp
        have : p.1 ∈ B := mem_image.2 ⟨p, hp, rfl⟩
        rw [hBi, mem_singleton] at this
        exact this
      calc 2 ≤ A.card := hA
        _ = (A.filter (fun p => p.1 = j)).card := by rw [hfib]
        _ ≤ _ := by
          apply card_le_card
          intro p hp
          simp only [mem_filter] at hp
          simp only [nbrsIn, mem_filter, dupRel, c0]
          exact ⟨hp.1, by rw [hp.2]; exact hdiag _⟩
    calc A.card = B.card + D.card := hcardA
      _ = (({i} : Finset ι).image (c0 T)).card + S1.card := by
          rw [card_image_of_injective _ hc0inj, card_singleton, hB1, hS1card]
      _ = ((({i} : Finset ι).image (c0 T)) ∪ S1).card := (card_union_of_disjoint (hdisj _)).symm
      _ ≤ _ := card_le_card (union_subset hS0sub hS1sub)
  · -- at least two indices: use super-neighbors of B in H
    have hSNB := hH B hB2
    have hS0sub : (superNbrs H B).image (c0 T) ⊆ superNbrs (dupRel H T) A := by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hw
      simp only [superNbrs, mem_filter, mem_univ, true_and] at hj ⊢
      -- choose a copy in A of every index of B adjacent to j
      have hpick : ∀ i ∈ nbrsIn H B j, ∃ p ∈ A, p.1 = i := by
        intro i hi
        have : i ∈ B := (mem_filter.1 hi).1
        obtain ⟨p, hp, rfl⟩ := mem_image.1 this
        exact ⟨p, hp, rfl⟩
      calc 2 ≤ (nbrsIn H B j).card := hj
        _ ≤ (nbrsIn (dupRel H T) A (c0 T j)).card := by
          -- the map p ↦ p.1 sends nbrsIn A onto nbrsIn B
          have hsurj : nbrsIn H B j ⊆ (nbrsIn (dupRel H T) A (c0 T j)).image Sigma.fst := by
            intro i hi
            obtain ⟨p, hp, hpi⟩ := hpick i hi
            refine mem_image.2 ⟨p, ?_, hpi⟩
            simp only [nbrsIn, mem_filter, dupRel, c0]
            exact ⟨hp, by rw [hpi]; exact (mem_filter.1 hi).2⟩
          exact (card_le_card hsurj).trans card_image_le
    calc A.card = B.card + D.card := hcardA
      _ ≤ ((superNbrs H B).image (c0 T)).card + S1.card := by
          rw [card_image_of_injective _ hc0inj, hS1card]; omega
      _ = (((superNbrs H B).image (c0 T)) ∪ S1).card :=
          (card_union_of_disjoint (hdisj _)).symm
      _ ≤ _ := card_le_card (union_subset hS0sub hS1sub)

/-- Degrees after duplication: a copy of `i` has degree `∑_{j adjacent to i} mult T j`. -/
theorem degL_dup (T : Finset ι) (p : V T) :
    degL (dupRel H T) p = ∑ j ∈ univ.filter (fun j => H p.1 j), mult T j := by
  classical
  unfold degL
  rw [card_eq_sum_ones, sum_filter]
  rw [Fintype.sum_sigma]
  rw [sum_filter]
  refine sum_congr rfl (fun j _ => ?_)
  by_cases h : H p.1 j <;> simp [dupRel, h]

end Dup

end DoubleHall
