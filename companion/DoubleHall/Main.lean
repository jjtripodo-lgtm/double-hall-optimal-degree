import DoubleHall.SemibiplaneOrder

/-!
# Main theorems

* `pair_count_lower_bound`: the counting lower bound `2(n-1) ≤ Δ(Δ-1)` (in `Basic`).
* `semibiplane_order_theorem`: for every finite field of odd order `q ≥ 1153` there is a
  balanced regular bipartite graph on `N = (q² - 1)/2` vertices per side, with the double Hall
  property on both sides, of degree `q + 2⌊√((q - 1)/2)⌋ + 4`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace DoubleHall

open scoped Classical in
/-- A balanced `D`-regular bipartite graph on `n + n` vertices with double Hall on both
sides exists. -/
def HasRegularBoth (n D : ℕ) : Prop :=
  ∃ G : Fin n → Fin n → Prop, DoubleHallBoth G ∧ IsRegular G D

open scoped Classical in
theorem hasRegularBoth_of_equiv {V : Type*} [Fintype V] [DecidableEq V] {n D : ℕ}
    (hV : Fintype.card V = n) (G : V → V → Prop) (hG : DoubleHallBoth G) (hreg : IsRegular G D) :
    HasRegularBoth n D := by
  let e : V ≃ Fin n := Fintype.equivFinOfCardEq hV
  refine ⟨relabel e e G, ?_, ⟨fun i => ?_, fun i => ?_⟩⟩
  · convert relabel_doubleHallBoth e e G hG
  · calc degL (relabel e e G) i = degL G (e.symm i) := by convert degL_relabel e e G i
      _ = D := hreg.1 _
  · calc degR (relabel e e G) i = degR G (e.symm i) := by convert degR_relabel e e G i
      _ = D := hreg.2 _

open scoped Classical in
/-- **Semibiplane-order theorem** (Theorem 3 of the manuscript). -/
theorem semibiplane_order_theorem (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : (2 : F) ≠ 0) (hq : 1153 ≤ Fintype.card F) :
    HasRegularBoth ((Fintype.card F ^ 2 - 1) / 2)
      (Fintype.card F + (2 * Nat.sqrt ((Fintype.card F - 1) / 2) + 4)) := by
  set q := Fintype.card F with hqdef
  set g := (q - 1) / 2 with hgdef
  -- q is odd
  have hodd : q % 2 = 1 := by
    have hP := Semibiplane.two_mul_card_Pt hF
    rcases Nat.even_or_odd q with he | ho
    · exfalso
      obtain ⟨r, hr⟩ := he
      have hsq : Fintype.card F ^ 2 = 4 * (r * r) := by rw [← hqdef, hr]; ring
      rw [hsq] at hP
      have : 1 ≤ r * r := by
        have : 1 ≤ r := by omega
        exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      omega
    · exact Nat.odd_iff.1 ho
  have hg : 2 * g = q - 1 := by omega
  obtain ⟨Loc, hLoc, hLreg, _⟩ := RookInterp.exists_local g (by omega)
  obtain ⟨eX, eY, hboth, hreg⟩ :=
    Semibiplane.repaired_doubleHallBoth_regular hF hg Loc hLoc hLreg
  refine hasRegularBoth_of_equiv ?_ _ hboth hreg
  have := Semibiplane.two_mul_card_Pt hF
  rw [← hqdef] at this
  omega

end DoubleHall
