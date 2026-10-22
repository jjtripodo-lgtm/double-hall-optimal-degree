import DoubleHall.Basic

/-!
# Sparse regular completion via Hall's theorem

Given a bipartite graph `H` and prescribed deficits `α : X → ℕ`, `β : Y → ℕ` with equal
totals, we find a subgraph `F` of the bipartite complement of `H` with these degrees,
provided the cut condition

  `α(U) + β(V) ≤ T₀ + e_{H̄}(U, V)`  for all `U ⊆ X`, `V ⊆ Y`

holds. The proof uses Tutte's gadget and Mathlib's Hall marriage theorem. We then derive the
explicit sufficient condition `T₀ ≥ a c + b r + 2 a b` and the regular completion theorem.
-/

set_option linter.unusedSectionVars false

open Finset

namespace DoubleHall

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

section Gadget

variable (H : X → Y → Prop) [∀ x y, Decidable (H x y)] (α : X → ℕ) (β : Y → ℕ)

/-- Edges of the bipartite complement. -/
abbrev CEdge := {p : X × Y // ¬ H p.1 p.2}

/-- Left vertices of the gadget: copies of left vertices, and one node per complement edge. -/
abbrev GL := (Σ x : X, Fin (α x)) ⊕ CEdge H

/-- Right vertices of the gadget: copies of right vertices, and one node per complement edge. -/
abbrev GR := (Σ y : Y, Fin (β y)) ⊕ CEdge H

/-- Gadget adjacency. -/
def gadgetNbrs : GL H α → Finset (GR H β)
  | Sum.inl ⟨x, _⟩ => (univ.filter (fun e : CEdge H => e.1.1 = x)).image Sum.inr
  | Sum.inr e => insert (Sum.inr e) ((univ : Finset (Fin (β e.1.2))).image
      (fun j => Sum.inl ⟨e.1.2, j⟩))

/-- Complement edges between `U` and `V`. -/
def eComp (U : Finset X) (V : Finset Y) : ℕ :=
  (univ.filter (fun e : CEdge H => e.1.1 ∈ U ∧ e.1.2 ∈ V)).card

/-- The cut condition. -/
def CutCondition : Prop :=
  ∀ (U : Finset X) (V : Finset Y),
    ∑ x ∈ U, α x + ∑ y ∈ V, β y ≤ ∑ y, β y + eComp H U V

variable {H α β}

theorem card_sigma_fin {Z : Type*} [Fintype Z] (γ : Z → ℕ) :
    Fintype.card (Σ z : Z, Fin (γ z)) = ∑ z, γ z := by
  simp [Fintype.card_sigma]

/-- Hall's condition for the gadget follows from the cut condition. -/
theorem gadget_hall (hcut : CutCondition H α β) (s : Finset (GL H α)) :
    s.card ≤ (s.biUnion (gadgetNbrs H α β)).card := by
  classical
  set s1 : Finset (Σ x : X, Fin (α x)) := s.preimage Sum.inl Sum.inl_injective.injOn with hs1
  set s2 : Finset (CEdge H) := s.preimage Sum.inr Sum.inr_injective.injOn with hs2
  have hscard : s.card ≤ s1.card + s2.card := by
    have hsub : s ⊆ s1.image Sum.inl ∪ s2.image Sum.inr := by
      intro l hl
      cases l with
      | inl p => exact mem_union_left _ (mem_image.2 ⟨p, by simpa [hs1] using hl, rfl⟩)
      | inr e => exact mem_union_right _ (mem_image.2 ⟨e, by simpa [hs2] using hl, rfl⟩)
    calc s.card ≤ (s1.image Sum.inl ∪ s2.image Sum.inr).card := card_le_card hsub
      _ ≤ (s1.image Sum.inl).card + (s2.image Sum.inr).card := card_union_le _ _
      _ ≤ s1.card + s2.card := add_le_add card_image_le card_image_le
  set U : Finset X := s1.image Sigma.fst with hU
  set V : Finset Y := s2.image (fun e => e.1.2) with hV
  set Vc : Finset Y := univ \ V with hVc
  have hs1le : s1.card ≤ ∑ x ∈ U, α x := by
    calc s1.card ≤ (U.sigma (fun x => (univ : Finset (Fin (α x))))).card := by
          apply card_le_card
          intro p hp
          simp only [mem_sigma, mem_univ, and_true, hU, mem_image]
          exact ⟨p, hp, rfl⟩
      _ = ∑ x ∈ U, α x := by simp [card_sigma]
  set E1 : Finset (CEdge H) := univ.filter (fun e : CEdge H => e.1.1 ∈ U ∧ e.1.2 ∈ Vc) with hE1
  set C2 : Finset (Σ y : Y, Fin (β y)) := V.sigma (fun y => (univ : Finset (Fin (β y))))
    with hC2
  have hdisjE : Disjoint s2 E1 := by
    rw [disjoint_left]
    intro e he1 he2
    simp only [hE1, mem_filter, mem_univ, true_and, hVc, mem_sdiff] at he2
    exact he2.2 (mem_image.2 ⟨e, he1, rfl⟩)
  have hsupset : (s2 ∪ E1).image Sum.inr ∪ C2.image Sum.inl ⊆
      s.biUnion (gadgetNbrs H α β) := by
    intro r hr
    rw [mem_biUnion]
    rcases mem_union.1 hr with hr | hr
    · obtain ⟨e, he, rfl⟩ := mem_image.1 hr
      rcases mem_union.1 he with he | he
      · refine ⟨Sum.inr e, by simpa [hs2] using he, ?_⟩
        simp [gadgetNbrs]
      · simp only [hE1, mem_filter, mem_univ, true_and, hU, mem_image] at he
        obtain ⟨⟨p, hp, hpx⟩, _⟩ := he
        refine ⟨Sum.inl p, by simpa [hs1] using hp, ?_⟩
        obtain ⟨x, i⟩ := p
        simp only [gadgetNbrs, mem_image, mem_filter, mem_univ, true_and]
        exact ⟨e, hpx.symm ▸ rfl, rfl⟩
    · obtain ⟨⟨y, j⟩, hyj, rfl⟩ := mem_image.1 hr
      simp only [hC2, mem_sigma, mem_univ, and_true, hV, mem_image] at hyj
      obtain ⟨e, he, rfl⟩ := hyj
      refine ⟨Sum.inr e, by simpa [hs2] using he, ?_⟩
      simp [gadgetNbrs]
  have hcardsup : ((s2 ∪ E1).image Sum.inr ∪ C2.image Sum.inl).card
      = s2.card + E1.card + ∑ y ∈ V, β y := by
    rw [card_union_of_disjoint]
    · rw [card_image_of_injective _ Sum.inr_injective, card_image_of_injective _ Sum.inl_injective,
        card_union_of_disjoint hdisjE, hC2]
      simp [card_sigma]
    · rw [disjoint_left]
      intro r h1 h2
      obtain ⟨_, _, rfl⟩ := mem_image.1 h1
      obtain ⟨_, _, h⟩ := mem_image.1 h2
      cases h
  -- the cut condition at (U, Vc)
  have hc := hcut U Vc
  have heComp : eComp H U Vc = E1.card := rfl
  have hsplit : ∑ y, β y = ∑ y ∈ V, β y + ∑ y ∈ Vc, β y := by
    rw [hVc, ← sum_add_sum_compl V]
    congr 1
  have hfinal : s.card ≤ s2.card + E1.card + ∑ y ∈ V, β y := by omega
  calc s.card ≤ s2.card + E1.card + ∑ y ∈ V, β y := hfinal
    _ = _ := hcardsup.symm
    _ ≤ _ := card_le_card hsupset

open scoped Classical in
/-- Existence of a degree-prescribed subgraph of the complement under the cut condition. -/
theorem exists_factor (hcut : CutCondition H α β) (hsum : ∑ x, α x = ∑ y, β y) :
    ∃ F : X → Y → Prop, (∀ x y, F x y → ¬ H x y) ∧
      (∀ x, (univ.filter (fun y => F x y)).card = α x) ∧
      (∀ y, (univ.filter (fun x => F x y)).card = β y) := by
  classical
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (gadgetNbrs H α β)).1
      (gadget_hall hcut)
  have hcard : Fintype.card (GL H α) = Fintype.card (GR H β) := by
    simp only [GL, GR, Fintype.card_sum, card_sigma_fin, hsum]
  have hfbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, hcard⟩
  -- an edge is used when its right gadget node is matched from a left copy
  let used : CEdge H → Prop := fun e => f (Sum.inr e) ≠ Sum.inr e
  let F : X → Y → Prop := fun x y => ∃ h : ¬ H x y, used ⟨(x, y), h⟩
  refine ⟨F, fun x y ⟨h, _⟩ => h, ?_, ?_⟩
  · -- left degrees
    intro x
    -- copies of x are matched to right edge nodes at x
    have hcopy : ∀ i : Fin (α x), ∃ e : CEdge H, e.1.1 = x ∧ f (Sum.inl ⟨x, i⟩) = Sum.inr e := by
      intro i
      have := hfmem (Sum.inl ⟨x, i⟩)
      simp only [gadgetNbrs, mem_image, mem_filter, mem_univ, true_and] at this
      obtain ⟨e, he, h⟩ := this
      exact ⟨e, he, h.symm⟩
    choose g hgx hgf using hcopy
    have hginj : Function.Injective g := by
      intro i j h
      have : f (Sum.inl ⟨x, i⟩) = f (Sum.inl ⟨x, j⟩) := by rw [hgf, hgf, h]
      have := hfinj this
      simp only [Sum.inl.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at this
      exact this
    -- used edges at x are exactly the g i
    have hused : ∀ e : CEdge H, e.1.1 = x → (used e ↔ ∃ i, g i = e) := by
      intro e hex
      constructor
      · intro hu
        obtain ⟨l, hl⟩ := hfbij.2 (Sum.inr e)
        cases l with
        | inr e' =>
          have hm := hfmem (Sum.inr e')
          rw [hl] at hm
          simp only [gadgetNbrs, mem_insert, Sum.inr.injEq, mem_image, mem_univ, true_and,
            reduceCtorEq, exists_false, or_false] at hm
          subst hm
          exact absurd hl hu
        | inl p =>
          obtain ⟨x', i⟩ := p
          have hm := hfmem (Sum.inl ⟨x', i⟩)
          rw [hl] at hm
          simp only [gadgetNbrs, mem_image, mem_filter, mem_univ, true_and, Sum.inr.injEq,
            exists_eq_right] at hm
          have hx' : x' = x := hm.symm.trans hex
          subst hx'
          refine ⟨i, ?_⟩
          have := hgf i
          rw [hl] at this
          exact (Sum.inr_injective this).symm
      · rintro ⟨i, rfl⟩ hfix
        have h1 := hgf i
        rw [← hfix] at h1
        exact absurd (hfinj h1) (by simp)
    -- count
    have hset : univ.filter (fun y => F x y) = univ.image (fun i => (g i).1.2) := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_image]
      constructor
      · rintro ⟨h, hu⟩
        obtain ⟨i, hi⟩ := (hused ⟨(x, y), h⟩ rfl).1 hu
        exact ⟨i, by rw [hi]⟩
      · rintro ⟨i, rfl⟩
        have hx := hgx i
        refine ⟨by rw [← hx]; exact (g i).2, ?_⟩
        have key := (hused (g i) hx).2 ⟨i, rfl⟩
        have hgi : g i = ⟨(x, (g i).1.2), by rw [← hx]; exact (g i).2⟩ :=
          Subtype.ext (Prod.ext hx rfl)
        rw [hgi] at key
        exact key
    have hc : (univ.image (fun i => (g i).1.2)).card = α x := by
      rw [card_image_of_injective, card_univ, Fintype.card_fin]
      intro i j h
      apply hginj
      exact Subtype.ext (Prod.ext ((hgx i).trans (hgx j).symm) h)
    convert (congrArg Finset.card hset).trans hc
  · -- right degrees
    intro y
    -- copies of y come from edge nodes at y; each such edge is used
    have hpre : ∀ j : Fin (β y), ∃ e : CEdge H, e.1.2 = y ∧ f (Sum.inr e) = Sum.inl ⟨y, j⟩ := by
      intro j
      obtain ⟨l, hl⟩ := hfbij.2 (Sum.inl ⟨y, j⟩)
      cases l with
      | inl p =>
        have hm := hfmem (Sum.inl p)
        rw [hl] at hm
        obtain ⟨x', i⟩ := p
        simp [gadgetNbrs] at hm
      | inr e =>
        have hm := hfmem (Sum.inr e)
        rw [hl] at hm
        simp only [gadgetNbrs, mem_insert, reduceCtorEq, mem_image, mem_univ, true_and,
          false_or] at hm
        obtain ⟨k, hk⟩ := hm
        simp only [Sum.inl.injEq, Sigma.mk.inj_iff] at hk
        exact ⟨e, hk.1, hl⟩
    choose g hgy hgf using hpre
    have hginj : Function.Injective g := by
      intro i j h
      have : (Sum.inl ⟨y, i⟩ : GR H β) = Sum.inl ⟨y, j⟩ := by rw [← hgf, ← hgf, h]
      simpa using this
    have hused : ∀ e : CEdge H, e.1.2 = y → (used e ↔ ∃ j, g j = e) := by
      intro e hey
      constructor
      · intro hu
        have hm := hfmem (Sum.inr e)
        simp only [gadgetNbrs, mem_insert, mem_image, mem_univ, true_and] at hm
        rcases hm with hm | ⟨k, hk⟩
        · exact absurd hm hu
        · subst hey
          refine ⟨k, Sum.inr_injective (hfinj ?_)⟩
          rw [hgf]
          first | exact hk | exact hk.symm
      · rintro ⟨j, rfl⟩ hfix
        have := hgf j
        rw [hfix] at this
        simp at this
    have hset : univ.filter (fun x => F x y) = univ.image (fun j => (g j).1.1) := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_image]
      constructor
      · rintro ⟨h, hu⟩
        obtain ⟨j, hj⟩ := (hused ⟨(x, y), h⟩ rfl).1 hu
        exact ⟨j, by rw [hj]⟩
      · rintro ⟨j, rfl⟩
        have hy := hgy j
        refine ⟨by rw [← hy]; exact (g j).2, ?_⟩
        have key := (hused (g j) hy).2 ⟨j, rfl⟩
        have hgj : g j = ⟨((g j).1.1, y), by rw [← hy]; exact (g j).2⟩ :=
          Subtype.ext (Prod.ext rfl hy)
        rw [hgj] at key
        exact key
    have hc : (univ.image (fun j => (g j).1.1)).card = β y := by
      rw [card_image_of_injective, card_univ, Fintype.card_fin]
      intro i j h
      apply hginj
      exact Subtype.ext (Prod.ext h ((hgy i).trans (hgy j).symm))
    convert (congrArg Finset.card hset).trans hc

end Gadget

section Sparse

variable {H : X → Y → Prop} [∀ x y, Decidable (H x y)]

theorem eComp_eq_sum (U : Finset X) (V : Finset Y) :
    eComp H U V = ∑ x ∈ U, (V.filter (fun y => ¬ H x y)).card := by
  classical
  unfold eComp
  have hmap : (univ.filter (fun e : CEdge H => e.1.1 ∈ U ∧ e.1.2 ∈ V)).map
      (Function.Embedding.subtype _) = (U ×ˢ V).filter (fun p => ¬ H p.1 p.2) := by
    ext p
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype,
      mem_product]
    constructor
    · rintro ⟨e, ⟨h1, h2⟩, rfl⟩; exact ⟨⟨h1, h2⟩, e.2⟩
    · rintro ⟨⟨h1, h2⟩, h⟩; exact ⟨⟨p, h⟩, ⟨h1, h2⟩, rfl⟩
  rw [← card_map, hmap, card_filter, sum_product]
  refine sum_congr rfl (fun x _ => ?_)
  rw [card_filter]

theorem card_filter_not_ge (x : X) (V : Finset Y) :
    V.card ≤ (V.filter (fun y => ¬ H x y)).card + degL H x := by
  classical
  have h1 := card_filter_add_card_filter_not (s := V) (fun y => H x y)
  have h2 : (V.filter (fun y => H x y)).card ≤ degL H x :=
    card_le_card (fun y hy => by simp only [mem_filter] at hy; simp [hy.2])
  omega

theorem card_filter_not_ge' (y : Y) (U : Finset X) :
    U.card ≤ (U.filter (fun x => ¬ H x y)).card + degR H y := by
  classical
  have h1 := card_filter_add_card_filter_not (s := U) (fun x => H x y)
  have h2 : (U.filter (fun x => H x y)).card ≤ degR H y :=
    card_le_card (fun x hx => by simp only [mem_filter] at hx; simp [hx.2])
  omega

theorem eComp_eq_sum' (U : Finset X) (V : Finset Y) :
    eComp H U V = ∑ y ∈ V, (U.filter (fun x => ¬ H x y)).card := by
  classical
  rw [eComp_eq_sum]
  simp only [card_eq_sum_ones, sum_filter]
  exact sum_comm

/-- The explicit sparse sufficient condition implies the cut condition. -/
theorem cutCondition_of_sparse (α : X → ℕ) (β : Y → ℕ) {a b r c : ℕ}
    (hα : ∀ x, α x ≤ a) (hβ : ∀ y, β y ≤ b)
    (hr : ∀ x, degL H x ≤ r) (hc : ∀ y, degR H y ≤ c)
    (hsum : ∑ x, α x = ∑ y, β y)
    (hC : a * c + b * r + 2 * a * b ≤ ∑ y, β y) :
    CutCondition H α β := by
  classical
  intro U V
  have hαU : ∑ x ∈ U, α x ≤ a * U.card := by
    calc ∑ x ∈ U, α x ≤ ∑ x ∈ U, a := sum_le_sum (fun x _ => hα x)
      _ = a * U.card := by rw [sum_const, smul_eq_mul, mul_comm]
  have hβV : ∑ y ∈ V, β y ≤ b * V.card := by
    calc ∑ y ∈ V, β y ≤ ∑ y ∈ V, b := sum_le_sum (fun y _ => hβ y)
      _ = b * V.card := by rw [sum_const, smul_eq_mul, mul_comm]
  have hβVle : ∑ y ∈ V, β y ≤ ∑ y, β y := sum_le_sum_of_subset (subset_univ _)
  have hαUle : ∑ x ∈ U, α x ≤ ∑ x, α x := sum_le_sum_of_subset (subset_univ _)
  by_cases hV : r + a ≤ V.card
  · have hE : a * U.card ≤ eComp H U V := by
      rw [eComp_eq_sum]
      calc a * U.card = ∑ x ∈ U, a := by rw [sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ x ∈ U, (V.filter (fun y => ¬ H x y)).card := by
          refine sum_le_sum (fun x _ => ?_)
          have := card_filter_not_ge (H := H) x V
          have := hr x
          omega
    omega
  · by_cases hU : c + b ≤ U.card
    · have hE : b * V.card ≤ eComp H U V := by
        rw [eComp_eq_sum']
        calc b * V.card = ∑ y ∈ V, b := by rw [sum_const, smul_eq_mul, mul_comm]
          _ ≤ ∑ y ∈ V, (U.filter (fun x => ¬ H x y)).card := by
            refine sum_le_sum (fun y _ => ?_)
            have := card_filter_not_ge' (H := H) y U
            have := hc y
            omega
      omega
    · push Not at hV hU
      have h1 : a * U.card ≤ a * (c + b) := Nat.mul_le_mul_left _ hU.le
      have h2 : b * V.card ≤ b * (r + a) := Nat.mul_le_mul_left _ hV.le
      have h3 : a * (c + b) + b * (r + a) = a * c + b * r + 2 * a * b := by ring
      omega

/-- Handshake: left and right degree sums agree. -/
theorem sum_degL_eq_sum_degR (R : X → Y → Prop) [∀ x y, Decidable (R x y)] :
    ∑ x, degL R x = ∑ y, degR R y := by
  classical
  unfold degL degR
  simp only [card_eq_sum_ones, sum_filter]
  exact sum_comm

open scoped Classical in
/-- Sparse regular completion: a balanced graph with small deficits extends to a regular
graph of degree `D` on the same parts. -/
theorem exists_regular_supergraph {D a b r c : ℕ}
    (hdX : ∀ x, degL H x ≤ D) (hdY : ∀ y, degR H y ≤ D)
    (hα : ∀ x, D - degL H x ≤ a) (hβ : ∀ y, D - degR H y ≤ b)
    (hr : ∀ x, degL H x ≤ r) (hc : ∀ y, degR H y ≤ c)
    (hn : Fintype.card X = Fintype.card Y)
    (hC : a * c + b * r + 2 * a * b ≤ ∑ y, (D - degR H y)) :
    ∃ G : X → Y → Prop, (∀ x y, H x y → G x y) ∧
      (∀ x, (univ.filter (fun y => G x y)).card = D) ∧
      (∀ y, (univ.filter (fun x => G x y)).card = D) := by
  classical
  have hsum : ∑ x, (D - degL H x) = ∑ y, (D - degR H y) := by
    have h1 : ∑ x, (D - degL H x) + ∑ x, degL H x = Fintype.card X * D := by
      rw [← sum_add_distrib]
      rw [show (Fintype.card X * D) = ∑ _x : X, D by simp [mul_comm]]
      exact sum_congr rfl (fun x _ => Nat.sub_add_cancel (hdX x))
    have h2 : ∑ y, (D - degR H y) + ∑ y, degR H y = Fintype.card Y * D := by
      rw [← sum_add_distrib]
      rw [show (Fintype.card Y * D) = ∑ _y : Y, D by simp [mul_comm]]
      exact sum_congr rfl (fun y _ => Nat.sub_add_cancel (hdY y))
    have h3 := sum_degL_eq_sum_degR H
    rw [hn] at h1
    omega
  have hcut := cutCondition_of_sparse (H := H) (fun x => D - degL H x) (fun y => D - degR H y)
    hα hβ hr hc hsum hC
  obtain ⟨F, hFH, hFx, hFy⟩ := exists_factor hcut hsum
  refine ⟨fun x y => H x y ∨ F x y, fun x y h => Or.inl h, ?_, ?_⟩
  · intro x
    have hdisj : Disjoint (univ.filter (fun y => H x y)) (univ.filter (fun y => F x y)) := by
      rw [disjoint_filter]; intro y _ h hf; exact hFH x y hf h
    have hcx : (univ.filter (fun y => H x y) ∪ univ.filter (fun y => F x y)).card = D := by
      rw [card_union_of_disjoint hdisj]
      have h1 := hFx x
      have h2 := hdX x
      unfold degL at h2
      have h3 : (univ.filter (fun y => F x y)).card = D - (univ.filter (fun y => H x y)).card := by
        convert h1 using 2
        all_goals first | rfl | simp [degL, degR]
      omega
    convert hcx using 2
    ext y; simp
  · intro y
    have hdisj : Disjoint (univ.filter (fun x => H x y)) (univ.filter (fun x => F x y)) := by
      rw [disjoint_filter]; intro x _ h hf; exact hFH x y hf h
    have hcy : (univ.filter (fun x => H x y) ∪ univ.filter (fun x => F x y)).card = D := by
      rw [card_union_of_disjoint hdisj]
      have h1 := hFy y
      have h2 := hdY y
      unfold degR at h2
      have h3 : (univ.filter (fun x => F x y)).card = D - (univ.filter (fun x => H x y)).card := by
        convert h1 using 2
        all_goals first | rfl | simp [degL, degR]
      omega
    convert hcy using 2
    ext x; simp

end Sparse

end DoubleHall
