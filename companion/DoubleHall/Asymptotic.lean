import DoubleHall.Padding
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Field.ZMod

/-!
# The all-order asymptotic theorem (prime-interval transfer)

`PrimeIntervalHyp θ`: for all sufficiently large real `x` there is a prime in `[x - x^θ, x]`.
Baker–Harman–Pintz proved it for `θ = 21/40`; it is not formalized here and enters only as an
explicit hypothesis.

`transfer_theorem`: if `1/2 ≤ θ < 1` and `PrimeIntervalHyp θ`, then for every sufficiently
large `n` there is a balanced regular bipartite graph on `n + n` vertices with double Hall on
both sides, of degree at most `√(2n) + 33 n^(θ/2)`.
-/

set_option linter.unusedSectionVars false

open Finset Real

namespace DoubleHall

/-- Short-interval prime hypothesis with exponent `θ`. -/
def PrimeIntervalHyp (θ : ℝ) : Prop :=
  ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x - x ^ θ ≤ (p : ℝ) ∧ (p : ℝ) ≤ x

/-- Large `Q` makes `Q^θ` a small fraction of `Q`. -/
theorem rpow_le_div_of_large {θ M Q : ℝ} (hθ : θ < 1) (hM : 1 ≤ M)
    (hQ : M ^ (1 / (1 - θ)) ≤ Q) (hQ1 : 1 ≤ Q) : M * Q ^ θ ≤ Q := by
  have h1θ : 0 < 1 - θ := by linarith
  have hQpos : 0 < Q := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hpow : M ≤ Q ^ (1 - θ) := by
    calc M = (M ^ (1 / (1 - θ))) ^ (1 - θ) := by
          rw [← rpow_mul hM0, one_div_mul_cancel h1θ.ne', rpow_one]
      _ ≤ Q ^ (1 - θ) := rpow_le_rpow (rpow_nonneg hM0 _) hQ h1θ.le
  calc M * Q ^ θ ≤ Q ^ (1 - θ) * Q ^ θ := by
        exact mul_le_mul_of_nonneg_right hpow (rpow_nonneg hQpos.le _)
    _ = Q := by rw [← rpow_add hQpos]; simp

theorem sqrt_le_rpow {θ Q : ℝ} (hθ : 1 / 2 ≤ θ) (hQ : 1 ≤ Q) : Real.sqrt Q ≤ Q ^ θ := by
  rw [Real.sqrt_eq_rpow]
  exact rpow_le_rpow_of_exponent_le hQ hθ

theorem sqrt_rpow_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2) {n : ℝ} (hn : 1 ≤ n) :
    (Real.sqrt (2 * n + 1)) ^ θ ≤ 3 * n ^ (θ / 2) := by
  have h0 : (0 : ℝ) ≤ 2 * n + 1 := by linarith
  rw [Real.sqrt_eq_rpow, ← rpow_mul h0]
  have hle : 2 * n + 1 ≤ 3 * n := by linarith
  calc (2 * n + 1) ^ (1 / 2 * θ) ≤ (3 * n) ^ (1 / 2 * θ) :=
        rpow_le_rpow h0 hle (by positivity)
    _ = 3 ^ (1 / 2 * θ) * n ^ (1 / 2 * θ) := mul_rpow (by norm_num) (by linarith)
    _ ≤ 3 * n ^ (θ / 2) := by
        have h3 : (3 : ℝ) ^ (1 / 2 * θ) ≤ 3 ^ (1 : ℝ) :=
          rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        rw [rpow_one] at h3
        rw [show 1 / 2 * θ = θ / 2 by ring] at h3 ⊢
        exact mul_le_mul_of_nonneg_right h3 (rpow_nonneg (by linarith) _)

/-- Nat square root is at most the real square root. -/
theorem natSqrt_le_sqrt (g : ℕ) : (Nat.sqrt g : ℝ) ≤ Real.sqrt g := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  exact_mod_cast Nat.sqrt_le' g

set_option maxHeartbeats 800000 in
/-- **Transfer theorem.** A prime-interval exponent `θ ∈ [1/2, 1)` gives degree
`√(2n) + O(n^(θ/2))` at every sufficiently large order. -/
theorem transfer_theorem {θ : ℝ} (hθ1 : 1 / 2 ≤ θ) (hθ2 : θ < 1) (hP : PrimeIntervalHyp θ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ D : ℕ, HasRegularBoth n D ∧
      (D : ℝ) ≤ Real.sqrt (2 * n) + 33 * (n : ℝ) ^ (θ / 2) := by
  obtain ⟨X₀, hX₀⟩ := hP
  set M : ℝ := 10000 with hM
  set Q₀ : ℝ := max (max X₀ 10000) (M ^ (1 / (1 - θ))) with hQ₀
  refine ⟨⌈Q₀ ^ 2⌉₊ + 1, fun n hn => ?_⟩
  -- the real parameter Q = √(2n+1)
  have hn1 : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  set Q : ℝ := Real.sqrt (2 * n + 1) with hQ
  have hQsq : Q ^ 2 = 2 * n + 1 := by rw [hQ, sq_sqrt (by positivity)]
  have hQ0le : Q₀ ≤ Q := by
    have hceil : Q₀ ^ 2 ≤ (n : ℝ) := by
      have h1 : Q₀ ^ 2 ≤ (⌈Q₀ ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈Q₀ ^ 2⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈Q₀ ^ 2⌉₊ ≤ n)
      linarith
    have hQ0pos : 0 ≤ Q₀ := le_trans (by norm_num) (le_trans (le_max_right X₀ 10000) (le_max_left _ _))
    rw [hQ]
    apply Real.le_sqrt_of_sq_le
    linarith
  have hQbig : 10000 ≤ Q := le_trans (le_trans (le_max_right X₀ 10000) (le_max_left _ _)) hQ0le
  have hQX : X₀ ≤ Q := le_trans (le_trans (le_max_left X₀ 10000) (le_max_left _ _)) hQ0le
  have hQM : M ^ (1 / (1 - θ)) ≤ Q := le_trans (le_max_right _ _) hQ0le
  set u : ℝ := Q ^ θ with hu
  have huM : M * u ≤ Q := rpow_le_div_of_large hθ2 (by norm_num [hM]) hQM (by linarith)
  have hsqrtQ : Real.sqrt Q ≤ u := sqrt_le_rpow hθ1 (by linarith)
  have hu1 : 100 ≤ u := by
    have : (100 : ℝ) ≤ Real.sqrt Q := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]; norm_num; linarith
    linarith
  -- the prime
  obtain ⟨p, hp, hplow, hphigh⟩ := hX₀ Q hQX
  have hM' : 10000 * u ≤ Q := by rw [hM] at huM; exact huM
  have hpQ2 : (p : ℝ) ≥ Q / 2 + 2 := by linarith
  have hp1153 : 1153 ≤ p := by
    have : (1153 : ℝ) ≤ p := by linarith
    exact_mod_cast this
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  -- the field
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hF : (2 : ZMod p) ≠ 0 := by
    intro h2
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  -- natural parameters
  set g := (p - 1) / 2 with hgdef
  set h := 2 * Nat.sqrt g + 4 with hhdef
  set d := p + h with hddef
  set N := (p ^ 2 - 1) / 2 with hNdef
  set t := n - N with htdef
  set k := t / g with hkdef
  set R := k + 1 + h with hRdef
  have hg2 : 2 * g = p - 1 := by omega
  have hpsq : p ^ 2 ≤ 2 * n + 1 := by
    have : (p : ℝ) ^ 2 ≤ 2 * n + 1 := by
      rw [← hQsq]; exact pow_le_pow_left₀ (Nat.cast_nonneg p) hphigh 2
    exact_mod_cast this
  have hp2odd : p ^ 2 % 2 = 1 := by
    rw [Nat.pow_mod, hpodd]
  have h2N : 2 * N = p ^ 2 - 1 := by omega
  have hNn : N ≤ n := by omega
  have h2t : 2 * t = 2 * n + 1 - p ^ 2 := by omega
  -- real bounds
  have hp_le : (p : ℝ) ≤ Q := hphigh
  have htR : (t : ℝ) ≤ Q * u := by
    have h1 : (2 * t : ℝ) = Q ^ 2 - (p : ℝ) ^ 2 := by
      rw [hQsq]
      have : ((2 * t : ℕ) : ℝ) = ((2 * n + 1 - p ^ 2 : ℕ) : ℝ) := by rw [h2t]
      push_cast [Nat.cast_sub hpsq] at this
      linarith
    have e1 : Q ^ 2 - (p : ℝ) ^ 2 = (Q - p) * (Q + p) := by ring
    have e2 : (Q - p) * (Q + p) ≤ u * (2 * Q) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  have hgR : Q / 4 ≤ (g : ℝ) := by
    have : ((2 * g : ℕ) : ℝ) = ((p - 1 : ℕ) : ℝ) := by rw [hg2]
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)] at this
    linarith
  have hgQ : (g : ℝ) ≤ Q := by
    have : ((2 * g : ℕ) : ℝ) ≤ p := by exact_mod_cast (by omega : 2 * g ≤ p)
    push_cast at this; linarith
  have hkR : (k : ℝ) ≤ 4 * u := by
    have hkg : (k : ℝ) * g ≤ t := by exact_mod_cast Nat.div_mul_le_self t g
    have hQpos : 0 < Q := by linarith
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have e1 : (k : ℝ) * (Q / 4) ≤ (k : ℝ) * g := mul_le_mul_of_nonneg_left hgR hk0
    have e2 : (k : ℝ) * Q ≤ (4 * u) * Q := by linarith
    exact le_of_mul_le_mul_right e2 hQpos
  have hhR : (h : ℝ) ≤ 2 * u + 4 := by
    have h1 := natSqrt_le_sqrt g
    have h2 : Real.sqrt g ≤ Real.sqrt Q := Real.sqrt_le_sqrt hgQ
    have : (h : ℝ) = 2 * (Nat.sqrt g : ℝ) + 4 := by rw [hhdef]; push_cast; ring
    linarith
  have hRR : (R : ℝ) ≤ 7 * u := by
    have : (R : ℝ) = k + 1 + h := by rw [hRdef]; push_cast; ring
    linarith
  have hdR : (d : ℝ) ≤ Q + 2 * u + 4 := by
    have : (d : ℝ) = p + h := by rw [hddef]; push_cast; ring
    linarith
  -- padding hypotheses
  have hkq : k ≤ p := by
    have : (k : ℝ) ≤ p := by linarith
    exact_mod_cast this
  have hnR : (2 * (R + 1) * (d + R) + 2 * (R + 1) * (R + 1) : ℝ) ≤ n := by
    have hQn : Q * Q ≤ 3 * n := by nlinarith [hQsq]
    have hR0 : (0 : ℝ) ≤ R := by positivity
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have h1 : (R : ℝ) + 1 ≤ 8 * u := by linarith
    have h2 : (d : ℝ) + R ≤ 2 * Q := by linarith
    have h3 : ((R : ℝ) + 1) * (d + R) ≤ (8 * u) * (2 * Q) :=
      mul_le_mul h1 h2 (by linarith) (by linarith)
    have h4 : ((R : ℝ) + 1) * (R + 1) ≤ (8 * u) * (8 * u) :=
      mul_le_mul h1 h1 (by linarith) (by linarith)
    have hu_le : u ≤ Q / 10000 := by linarith
    have h6 : u * u ≤ (Q / 10000) * u := mul_le_mul_of_nonneg_right hu_le (by linarith)
    have h7 : Q * u ≤ Q * (Q / 10000) := mul_le_mul_of_nonneg_left hu_le (by linarith)
    have e : (2 * (R + 1) * (d + R) + 2 * (R + 1) * (R + 1) : ℝ)
        = 2 * (((R : ℝ) + 1) * (d + R)) + 2 * (((R : ℝ) + 1) * (R + 1)) := by ring
    rw [e]
    nlinarith
  have hn' : 2 * (R + 1) * (d + R) + 2 * (R + 1) * (R + 1) ≤ n := by exact_mod_cast hnR
  have hreg := Semibiplane.padding_theorem (F := ZMod p) hF (n := n) hcard hp1153 rfl rfl rfl rfl
    hNn rfl rfl rfl hkq hn'
  refine ⟨d + R + 1, hreg, ?_⟩
  -- the degree bound
  have hD : ((d + R + 1 : ℕ) : ℝ) ≤ Q + 10 * u := by push_cast; linarith
  have hQs : Q ≤ Real.sqrt (2 * n) + 1 := by
    rw [hQ, Real.sqrt_le_left (by positivity)]
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * n by positivity)
    have hs0 := Real.sqrt_nonneg (2 * (n : ℝ))
    nlinarith
  have hu3 : u ≤ 3 * (n : ℝ) ^ (θ / 2) := by
    rw [hu, hQ]; exact sqrt_rpow_le (by linarith) (by linarith) hn1
  linarith

open scoped Classical in
/-- The counting lower bound for the regular two-sided problem: `2(n - 1) ≤ D(D - 1)`. -/
theorem hasRegularBoth_lower {n D : ℕ} (hn : 1 ≤ n) (h : HasRegularBoth n D) :
    2 * (n - 1) ≤ D * (D - 1) := by
  obtain ⟨G, hG, hreg⟩ := h
  have := pair_count_lower_bound hG.1 D (fun x => (hreg.1 x).le) (fun y => (hreg.2 y).le)
    ⟨0, by omega⟩
  simpa using this

end DoubleHall
