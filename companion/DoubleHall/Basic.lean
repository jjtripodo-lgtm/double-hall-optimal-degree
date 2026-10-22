import Mathlib.Combinatorics.Hall.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# The double Hall property for bipartite graphs

A bipartite graph between finite types `X` (the designated left side) and `Y` is a decidable
relation `R : X → Y → Prop`. For `A : Finset X`, a *super-neighbor* of `A` is a vertex `y : Y`
with at least two neighbors in `A`. `R` has the (left) double Hall property when every `A` with
`|A| ≥ 2` has at least `|A|` super-neighbors.

This file contains the definitions, monotonicity under adding edges, and the classical
pair-counting lower bound `2 (n - 1) ≤ Δ (Δ - 1)` (Chen, Lavrov, Ma, Su and Vandenbussche,
Theorem 1.10).
-/

set_option linter.unusedSectionVars false

open Finset

namespace DoubleHall

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

section Defs

variable (R : X → Y → Prop) [∀ x y, Decidable (R x y)]

/-- The neighbors of `y` that lie in `A`. -/
def nbrsIn (A : Finset X) (y : Y) : Finset X := A.filter (fun x => R x y)

/-- Super-neighbors of `A`: right vertices with at least two neighbors in `A`. -/
def superNbrs (A : Finset X) : Finset Y :=
  univ.filter (fun y => 2 ≤ (nbrsIn R A y).card)

/-- The designated-left-side double Hall property. -/
def DoubleHallLeft : Prop :=
  ∀ A : Finset X, 2 ≤ A.card → A.card ≤ (superNbrs R A).card

/-- Degree of a left vertex. -/
def degL (x : X) : ℕ := (univ.filter (fun y => R x y)).card

/-- Degree of a right vertex. -/
def degR (y : Y) : ℕ := (univ.filter (fun x => R x y)).card

/-- `R` is `d`-regular on both sides. -/
def IsRegular (d : ℕ) : Prop := (∀ x, degL R x = d) ∧ ∀ y, degR R y = d

end Defs

section Mono

variable {R R' : X → Y → Prop} [∀ x y, Decidable (R x y)] [∀ x y, Decidable (R' x y)]

theorem superNbrs_mono (h : ∀ x y, R x y → R' x y) (A : Finset X) :
    superNbrs R A ⊆ superNbrs R' A := by
  intro y hy
  simp only [superNbrs, mem_filter, mem_univ, true_and] at hy ⊢
  refine hy.trans (card_le_card ?_)
  intro x hx
  simp only [nbrsIn, mem_filter] at hx ⊢
  exact ⟨hx.1, h _ _ hx.2⟩

/-- Adding edges preserves the double Hall property. -/
theorem DoubleHallLeft.mono (hR : DoubleHallLeft R) (h : ∀ x y, R x y → R' x y) :
    DoubleHallLeft R' := fun A hA =>
  (hR A hA).trans (card_le_card (superNbrs_mono h A))

end Mono

section LowerBound

variable {R : X → Y → Prop} [∀ x y, Decidable (R x y)]

/-- In a double-Hall graph, any two distinct left vertices have at least two common
neighbors. -/
theorem two_le_common (hR : DoubleHallLeft R) {a b : X} (hab : a ≠ b) :
    2 ≤ (univ.filter (fun y => R a y ∧ R b y)).card := by
  have hA : ({a, b} : Finset X).card = 2 := card_pair hab
  have h := hR {a, b} hA.ge
  rw [hA] at h
  refine h.trans (card_le_card ?_)
  intro y hy
  simp only [superNbrs, mem_filter, mem_univ, true_and] at hy ⊢
  have hsub : nbrsIn R {a, b} y ⊆ {a, b} := filter_subset _ _
  have heq : nbrsIn R {a, b} y = {a, b} :=
    eq_of_subset_of_card_le hsub (by rw [hA]; exact hy)
  have ha : a ∈ nbrsIn R {a, b} y := by rw [heq]; simp
  have hb : b ∈ nbrsIn R {a, b} y := by rw [heq]; simp
  simp only [nbrsIn, mem_filter] at ha hb
  exact ⟨ha.2, hb.2⟩

/-- The classical pair-counting lower bound: if every vertex has degree at most `Δ`,
then `2 (|X| - 1) ≤ Δ (Δ - 1)`. -/
theorem pair_count_lower_bound (hR : DoubleHallLeft R) (Δ : ℕ)
    (hX : ∀ x, degL R x ≤ Δ) (hY : ∀ y, degR R y ≤ Δ) (x₀ : X) :
    2 * (Fintype.card X - 1) ≤ Δ * (Δ - 1) := by
  classical
  set S : Finset X := univ.erase x₀ with hS
  set N₀ : Finset Y := univ.filter (fun y => R x₀ y) with hN₀
  -- double count the pairs (x, y) with x ∈ S, y a common neighbor of x₀ and x
  have hcount :
      ∑ x ∈ S, (univ.filter (fun y => R x₀ y ∧ R x y)).card
        = ∑ y ∈ N₀, (S.filter (fun x => R x y)).card := by
    rw [hN₀, sum_filter]
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl (fun y _ => ?_)
    by_cases hy : R x₀ y <;> simp [hy]
  have hlow : ∑ x ∈ S, 2 ≤ ∑ x ∈ S, (univ.filter (fun y => R x₀ y ∧ R x y)).card := by
    refine sum_le_sum ?_
    intro x hx
    have hne : x₀ ≠ x := fun h => by simp [hS, h] at hx
    exact two_le_common hR hne
  have hup : ∀ y ∈ N₀, (S.filter (fun x => R x y)).card ≤ Δ - 1 := by
    intro y hy
    have hy0 : R x₀ y := by simpa [hN₀] using hy
    have hsplit : (univ.filter (fun x => R x y)) =
        insert x₀ (S.filter (fun x => R x y)) := by
      ext x
      by_cases hx : x = x₀
      · subst hx; simp [hS, hy0]
      · simp [hS, hx]
    have hnot : x₀ ∉ S.filter (fun x => R x y) := by simp [hS]
    have h1 := hY y
    rw [degR, hsplit, card_insert_of_notMem hnot] at h1
    omega
  have hsumup : ∑ y ∈ N₀, (S.filter (fun x => R x y)).card ≤ N₀.card * (Δ - 1) := by
    simpa using sum_le_sum hup
  have hN₀le : N₀.card ≤ Δ := hX x₀
  have hScard : S.card = Fintype.card X - 1 := by
    rw [hS, card_erase_of_mem (mem_univ _), card_univ]
  calc 2 * (Fintype.card X - 1) = ∑ x ∈ S, 2 := by rw [sum_const, smul_eq_mul, hScard, mul_comm]
    _ ≤ _ := hlow
    _ = _ := hcount
    _ ≤ N₀.card * (Δ - 1) := hsumup
    _ ≤ Δ * (Δ - 1) := Nat.mul_le_mul_right _ hN₀le

end LowerBound

end DoubleHall
