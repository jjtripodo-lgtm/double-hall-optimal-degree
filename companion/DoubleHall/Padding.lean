import DoubleHall.Main

/-!
# Class-block padding: every order above a semibiplane order

Let `G` be the repaired semibiplane on `N = (q² - 1)/2` vertices per side, of degree
`d = q + h`. Match each point `x` with the block `π x` in its paired class carrying the same
local label. For `N ≤ n`, put `t = n - N`, `k = t / g`, and duplicate (matched) `t` points
inside `k + 1` parallel classes. Every row and column load is at most `R = k + 1 + h`; complete
to degree `d + R + 1`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace DoubleHall

namespace Semibiplane

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

section Matching

variable {g : ℕ}

/-- The matched partner block: same class pairing, same local label. -/
noncomputable def partner (eX eY : Pt F → Fin g)
    (heYsurj : ∀ (j : Line F) (w : Fin g), ∃ z, clsY z = j ∧ eY z = w) (x : Pt F) : Pt F :=
  Classical.choose (heYsurj (cls x) (eX x))

theorem partner_spec (eX eY : Pt F → Fin g)
    (heYsurj : ∀ (j : Line F) (w : Fin g), ∃ z, clsY z = j ∧ eY z = w) (x : Pt F) :
    clsY (partner eX eY heYsurj x) = cls x ∧ eY (partner eX eY heYsurj x) = eX x :=
  Classical.choose_spec (heYsurj (cls x) (eX x))

theorem partner_injective (eX eY : Pt F → Fin g)
    (heXinj : ∀ z z', cls z = cls z' → eX z = eX z' → z = z')
    (heYsurj : ∀ (j : Line F) (w : Fin g), ∃ z, clsY z = j ∧ eY z = w) :
    Function.Injective (partner eX eY heYsurj) := by
  intro x x' h
  have h1 := partner_spec eX eY heYsurj x
  have h2 := partner_spec eX eY heYsurj x'
  apply heXinj
  · rw [← h1.1, ← h2.1, h]
  · rw [← h1.2, ← h2.2, h]

end Matching

section Pad

open scoped Classical

/-- The number of parallel classes is `q + 1`. -/
theorem card_line (hF : (2 : F) ≠ 0) {g : ℕ} (hg : 2 * g = Fintype.card F - 1)
    (hg0 : 0 < g) : Fintype.card (Line F) = Fintype.card F + 1 := by
  have h1 : Fintype.card (Pt F) = ∑ L : Line F, (univ.filter (fun c : Pt F => cls c = L)).card :=
    card_eq_sum_card_fiberwise (fun c _ => mem_univ (cls c))
  simp only [card_cls_fiber hF hg, sum_const, card_univ, smul_eq_mul] at h1
  have h2 := two_mul_card_Pt hF
  -- 2 |Pt| = q² - 1 = (q - 1)(q + 1) = 2 g (q + 1)
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  have h3 : Fintype.card F ^ 2 - 1 = (Fintype.card F - 1) * (Fintype.card F + 1) := by
    obtain ⟨r, hr⟩ : ∃ r, Fintype.card F = r + 1 := ⟨Fintype.card F - 1, by omega⟩
    rw [hr]; simp only [Nat.add_sub_cancel]; ring_nf; omega
  rw [h3, ← hg, h1] at h2
  have : Fintype.card (Line F) * g = (Fintype.card F + 1) * g := by nlinarith
  exact Nat.eq_of_mul_eq_mul_right hg0 this

/-- Columns re-indexed so that the matched partner sits on the diagonal. -/
def matchedRel {g : ℕ} (eX eY : Pt F → Fin g) (Loc : Fin g → Fin g → Prop)
    (π : Pt F → Pt F) (i j : Pt F) : Prop :=
  repaired eX eY Loc i (π j)

variable (hF : (2 : F) ≠ 0) {g h : ℕ} (Loc : Fin g → Fin g → Prop)
  (hLoc : DoubleHallBoth Loc) (hLreg : IsRegular Loc h) (hdiag : ∀ i, Loc i i)
  {eX eY : Pt F → Fin g}
  (heXinj : ∀ z z', cls z = cls z' → eX z = eX z' → z = z')
  (heXsurj : ∀ (j : Line F) (w : Fin g), ∃ z, cls z = j ∧ eX z = w)
  (heYinj : ∀ z z', clsY z = clsY z' → eY z = eY z' → z = z')
  (heYsurj : ∀ (j : Line F) (w : Fin g), ∃ z, clsY z = j ∧ eY z = w)

include hF heXinj in
/-- Row load: a point sees at most `|S| + h` duplicated indices when every duplicated index
lies in a class of `S`. -/
theorem row_load_le (S : Finset (Line F)) (T : Finset (Pt F)) (hT : ∀ j ∈ T, cls j ∈ S)
    (i : Pt F) :
    (univ.filter (fun j => matchedRel eX eY Loc (partner eX eY heYsurj) i j) ∩ T).card
      ≤ S.card + degL Loc (eX i) := by
  set π := partner eX eY heYsurj
  have hπ := partner_spec eX eY heYsurj
  set A := T.filter (fun j => Inc i (π j))
  set B := univ.filter (fun j => localRel cls clsY eX eY Loc i (π j))
  have hsub : univ.filter (fun j => matchedRel eX eY Loc π i j) ∩ T ⊆ A ∪ B := by
    intro j hj
    simp only [mem_inter, mem_filter, mem_univ, true_and, matchedRel, repaired] at hj
    rcases hj.1 with h1 | h1
    · exact mem_union_left _ (mem_filter.2 ⟨hj.2, h1⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, h1⟩)
  have hA : A.card ≤ S.card := by
    have hinj : Set.InjOn cls (↑A : Set (Pt F)) := by
      intro j hj j' hj' hjj
      simp only [A, coe_filter, Set.mem_setOf_eq] at hj hj'
      have hc : clsY (π j) = clsY (π j') := by rw [(hπ j).1, (hπ j').1, hjj]
      have := inc_clsY_unique hF hc hj.2 hj'.2
      exact partner_injective eX eY heXinj heYsurj this
    calc A.card = (A.image cls).card := (card_image_of_injOn hinj).symm
      _ ≤ S.card := card_le_card (fun L hL => by
          obtain ⟨j, hj, rfl⟩ := mem_image.1 hL
          exact hT j (mem_filter.1 hj).1)
  have hB : B.card ≤ degL Loc (eX i) := by
    have hcls : ∀ j ∈ B, cls j = cls i := by
      intro j hj
      have := (mem_filter.1 hj).2.1
      rw [(hπ j).1] at this; exact this.symm
    have hinj : Set.InjOn eX (↑B : Set (Pt F)) := by
      intro j hj j' hj' hjj
      exact heXinj j j' ((hcls j hj).trans (hcls j' hj').symm) hjj
    calc B.card = (B.image eX).card := (card_image_of_injOn hinj).symm
      _ ≤ degL Loc (eX i) := card_le_card (fun w hw => by
          obtain ⟨j, hj, rfl⟩ := mem_image.1 hw
          have := (mem_filter.1 hj).2.2
          rw [(hπ j).2] at this
          simpa using this)
  calc _ ≤ (A ∪ B).card := card_le_card hsub
    _ ≤ A.card + B.card := card_union_le _ _
    _ ≤ _ := add_le_add hA hB

include hF heXinj in
/-- Column load. -/
theorem col_load_le (S : Finset (Line F)) (T : Finset (Pt F)) (hT : ∀ j ∈ T, cls j ∈ S)
    (j : Pt F) :
    (univ.filter (fun i => matchedRel eX eY Loc (partner eX eY heYsurj) i j) ∩ T).card
      ≤ S.card + degR Loc (eX j) := by
  set π := partner eX eY heYsurj
  have hπ := partner_spec eX eY heYsurj
  set A := T.filter (fun i => Inc i (π j))
  set B := univ.filter (fun i => localRel cls clsY eX eY Loc i (π j))
  have hsub : univ.filter (fun i => matchedRel eX eY Loc π i j) ∩ T ⊆ A ∪ B := by
    intro i hi
    simp only [mem_inter, mem_filter, mem_univ, true_and, matchedRel, repaired] at hi
    rcases hi.1 with h1 | h1
    · exact mem_union_left _ (mem_filter.2 ⟨hi.2, h1⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, h1⟩)
  have hA : A.card ≤ S.card := by
    have hinj : Set.InjOn cls (↑A : Set (Pt F)) := by
      intro i hi i' hi' hii
      simp only [A, coe_filter, Set.mem_setOf_eq] at hi hi'
      exact inc_cls_unique hF hii hi.2 hi'.2
    calc A.card = (A.image cls).card := (card_image_of_injOn hinj).symm
      _ ≤ S.card := card_le_card (fun L hL => by
          obtain ⟨i, hi, rfl⟩ := mem_image.1 hL
          exact hT i (mem_filter.1 hi).1)
  have hB : B.card ≤ degR Loc (eX j) := by
    have hcls : ∀ i ∈ B, cls i = cls j := by
      intro i hi
      have := (mem_filter.1 hi).2.1
      rw [(hπ j).1] at this; exact this
    have hinj : Set.InjOn eX (↑B : Set (Pt F)) := by
      intro i hi i' hi' hii
      exact heXinj i i' ((hcls i hi).trans (hcls i' hi').symm) hii
    calc B.card = (B.image eX).card := (card_image_of_injOn hinj).symm
      _ ≤ degR Loc (eX j) := card_le_card (fun w hw => by
          obtain ⟨i, hi, rfl⟩ := mem_image.1 hw
          have := (mem_filter.1 hi).2.2
          rw [(hπ j).2] at this
          simpa using this)
  calc _ ≤ (A ∪ B).card := card_le_card hsub
    _ ≤ A.card + B.card := card_union_le _ _
    _ ≤ _ := add_le_add hA hB

theorem card_odd (hF : (2 : F) ≠ 0) : Fintype.card F % 2 = 1 := by
  have hP := two_mul_card_Pt hF
  rcases Nat.even_or_odd (Fintype.card F) with he | ho
  · exfalso
    obtain ⟨r, hr⟩ := he
    have hsq : Fintype.card F ^ 2 = 4 * (r * r) := by rw [hr]; ring
    rw [hsq] at hP
    have hr1 : 1 ≤ r := by have := Fintype.card_pos (α := F); omega
    have : 1 ≤ r * r := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    omega
  · exact Nat.odd_iff.1 ho

open scoped Classical in
/-- **Padding theorem** (exact finite form of the all-order construction). -/
theorem padding_theorem (hF : (2 : F) ≠ 0) {n q g h d N t k R : ℕ}
    (hqF : Fintype.card F = q) (hq : 1153 ≤ q) (hg : g = (q - 1) / 2)
    (hh : h = 2 * Nat.sqrt g + 4) (hd : d = q + h) (hNdef : N = (q ^ 2 - 1) / 2)
    (hNn : N ≤ n) (ht : t = n - N) (hkdef : k = t / g) (hR : R = k + 1 + h)
    (hkq : k ≤ q) (hn : 2 * (R + 1) * (d + R) + 2 * (R + 1) * (R + 1) ≤ n) :
    HasRegularBoth n (d + R + 1) := by
  have hodd := card_odd hF
  rw [hqF] at hodd
  have hg2 : 2 * g = Fintype.card F - 1 := by omega
  have hg576 : 576 ≤ g := by omega
  have hg0 : 0 < g := by omega
  obtain ⟨Loc, hLoc, hLreg, hdiag⟩ := RookInterp.exists_local g hg576
  rw [← hh] at hLreg
  obtain ⟨eX, heXinj, heXsurj⟩ := exists_fiber_labels cls g (card_cls_fiber hF hg2)
  obtain ⟨eY, heYinj, heYsurj⟩ := exists_fiber_labels clsY g (card_clsY_fiber hF hg2)
  obtain ⟨hGboth, hGreg⟩ := repaired_props hF Loc hLoc hLreg heXinj heXsurj heYinj heYsurj
  set π := partner eX eY heYsurj with hπdef
  have hπ := partner_spec eX eY heYsurj
  have hπbij : Function.Bijective π :=
    Finite.injective_iff_bijective.1 (partner_injective eX eY heXinj heYsurj)
  set πE : Pt F ≃ Pt F := Equiv.ofBijective π hπbij
  set H' := matchedRel eX eY Loc π with hH'
  -- H' is the repaired graph with relabelled columns
  have hH'eq : ∀ i j, H' i j ↔ relabel (Equiv.refl _) πE.symm (repaired eX eY Loc) i j := by
    intro i j; simp [hH', matchedRel, relabel, πE]
  have hH'both : DoubleHallBoth H' := by
    have := relabel_doubleHallBoth (Equiv.refl _) πE.symm _ hGboth
    have hfun : H' = relabel (Equiv.refl _) πE.symm (repaired eX eY Loc) := by
      funext i j; exact propext (hH'eq i j)
    rw [hfun]; convert this
  have hH'degL : ∀ i, degL H' i = d := by
    intro i
    have h1 : (univ.filter (fun j => H' i j)).image π =
        univ.filter (fun y => repaired eX eY Loc i y) := by
      ext y
      simp only [mem_image, mem_filter, mem_univ, true_and, hH', matchedRel]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact hj
      · intro hy
        obtain ⟨j, rfl⟩ := hπbij.2 y
        exact ⟨j, hy, rfl⟩
    calc degL H' i = ((univ.filter (fun j => H' i j)).image π).card :=
          (card_image_of_injective _ hπbij.1).symm
      _ = (univ.filter (fun y => repaired eX eY Loc i y)).card := by rw [h1]
      _ = degL (repaired eX eY Loc) i := by unfold degL; congr 1
      _ = d := by rw [hGreg.1 i, hd, hqF]
  have hH'degR : ∀ j, degR H' j = d := by
    intro j
    have h1 : degR H' j = degR (repaired eX eY Loc) (π j) := by
      unfold degR; congr 1
    rw [h1, hGreg.2, hd, hqF]
  have hdiag' : ∀ i, H' i i := by
    intro i
    simp only [hH', matchedRel, repaired, localRel]
    right
    exact ⟨((hπ i).1).symm, by rw [(hπ i).2]; exact hdiag _⟩
  -- choose k+1 classes and t indices inside them
  have hline := card_line hF hg2 hg0
  obtain ⟨S, -, hScard⟩ := exists_subset_card_eq
    (show k + 1 ≤ (univ : Finset (Line F)).card by rw [card_univ, hline, hqF]; omega)
  set U := univ.filter (fun c : Pt F => cls c ∈ S) with hU
  have hUcard : U.card = (k + 1) * g := by
    have := card_eq_sum_card_fiberwise (s := U) (t := S) (f := cls)
      (fun c hc => (mem_filter.1 hc).2)
    rw [this]
    have : ∀ L ∈ S, (U.filter (fun c => cls c = L)).card = g := by
      intro L hL
      rw [← card_cls_fiber hF hg2 L]; congr 1; ext c
      simp only [hU, mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hL, h⟩
    rw [sum_congr rfl this, sum_const, smul_eq_mul, hScard]
  have htU : t ≤ U.card := by
    rw [hUcard, hkdef]
    have := Nat.div_add_mod t g
    have := Nat.mod_lt t hg0
    nlinarith
  obtain ⟨T, hTU, hTcard⟩ := exists_subset_card_eq htU
  have hT : ∀ j ∈ T, cls j ∈ S := fun j hj => (mem_filter.1 (hTU hj)).2
  -- duplicate
  have hcardV : Fintype.card (Dup.V T) = n := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [RookInterp.sum_mult, card_univ, univ_inter, hTcard]
    have := two_mul_card_Pt hF
    rw [hqF] at this
    omega
  have hboth : DoubleHallBoth (Dup.dupRel H' T) := by
    refine ⟨Dup.doubleHallLeft H' hdiag' hH'both.1 T, ?_⟩
    have := Dup.doubleHallLeft (fun j i => H' i j) hdiag' hH'both.2 T
    unfold DoubleHallRight
    exact this
  have hdegL : ∀ p : Dup.V T, d ≤ degL (Dup.dupRel H' T) p ∧ degL (Dup.dupRel H' T) p ≤ d + R := by
    intro p
    have h1 := Dup.degL_dup H' T p
    rw [RookInterp.sum_mult] at h1
    have hl := row_load_le hF Loc heXinj heYsurj S T hT p.1
    rw [hScard, hLreg.1] at hl
    have h2 : (univ.filter (fun j => H' p.1 j)).card = d := hH'degL p.1
    constructor
    · rw [h1, h2]; exact Nat.le_add_right d _
    · rw [h1, h2, hR]
      have : (univ.filter (fun j => H' p.1 j) ∩ T).card ≤ k + 1 + h := hl
      omega
  have hdegR : ∀ p : Dup.V T, d ≤ degR (Dup.dupRel H' T) p ∧ degR (Dup.dupRel H' T) p ≤ d + R := by
    intro p
    have h1 := Dup.degL_dup (fun j i => H' i j) T p
    rw [RookInterp.sum_mult] at h1
    have hl := col_load_le hF Loc heXinj heYsurj S T hT p.1
    rw [hScard, hLreg.2] at hl
    have h2 : (univ.filter (fun i => H' i p.1)).card = d := hH'degR p.1
    have hR' : degR (Dup.dupRel H' T) p = degL (Dup.dupRel (fun j i => H' i j) T) p := rfl
    constructor
    · rw [hR', h1, h2]; exact Nat.le_add_right d _
    · rw [hR', h1, h2, hR]
      have : (univ.filter (fun i => H' i p.1) ∩ T).card ≤ k + 1 + h := hl
      omega
  obtain ⟨G2, hDG, hG2x, hG2y⟩ := exists_regular_supergraph (H := (Dup.dupRel H' T)) (D := d + R + 1)
    (a := R + 1) (b := R + 1) (r := d + R) (c := d + R)
    (fun x => by have := hdegL x; omega) (fun y => by have := hdegR y; omega)
    (fun x => by have := hdegL x; omega) (fun y => by have := hdegR y; omega)
    (fun x => (hdegL x).2) (fun y => (hdegR y).2) rfl
    (by
      have hsum : Fintype.card (Dup.V T) ≤ ∑ y : Dup.V T, (d + R + 1 - degR (Dup.dupRel H' T) y) := by
        calc Fintype.card (Dup.V T) = ∑ _y : Dup.V T, 1 := by simp
          _ ≤ _ := sum_le_sum (fun y _ => by have := hdegR y; omega)
      rw [hcardV] at hsum
      nlinarith)
  refine hasRegularBoth_of_equiv hcardV G2 (hboth.mono hDG) ⟨fun x => ?_, fun y => ?_⟩
  · unfold degL; convert hG2x x using 2
  · unfold degR; convert hG2y y using 2

end Pad

end Semibiplane

end DoubleHall
