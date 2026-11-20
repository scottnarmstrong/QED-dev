/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# (R-Π₄) step L7: from comparable photon pairs to all light pairs

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L7. The class sum at
a photon pair is additive (`QED.GradedProof.RPi4.qPair_add`). A bound for *comparable* pairs
`a ≤ b ≤ 2a`, where both photon masses are of the size `b` and no photon collapse is needed,
gives a bound for every light pair `0 < a ≤ b` by halving `b` until it is comparable with `a`:

* `norm_le_of_comparable`: for `Q` additive on `(0, r₀]`, `‖Q a b‖ ≤ g b` on comparable pairs and
  `g (b / 2) ≤ ρ g b` (`0 ≤ ρ < 1`), `‖Q a b‖ ≤ g b / (1 - ρ)` for all `0 < a ≤ b ≤ r₀`;
* `norm_le_of_comparable_rpow`: the case `g b = C b ^ p`, `p > 0`.

No model enters.
-/

@[expose] public section

namespace QED.GradedProof.RPi4

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **Comparable pairs control all light pairs.** -/
theorem norm_le_of_comparable {Q : ℝ → ℝ → E} {g : ℝ → ℝ} {r₀ ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hg0 : ∀ b, 0 < b → b ≤ r₀ → 0 ≤ g b)
    (hg : ∀ b, 0 < b → b ≤ r₀ → g (b / 2) ≤ ρ * g b)
    (hadd : ∀ a b d, 0 < a → a ≤ b → b ≤ d → d ≤ r₀ → Q a d = Q a b + Q b d)
    (hcomp : ∀ a b, 0 < a → a ≤ b → b ≤ 2 * a → b ≤ r₀ → ‖Q a b‖ ≤ g b) :
    ∀ a b, 0 < a → a ≤ b → b ≤ r₀ → ‖Q a b‖ ≤ g b / (1 - ρ) := by
  have h1ρ : 0 < 1 - ρ := by linarith
  have key : ∀ n : ℕ, ∀ a b, 0 < a → a ≤ b → b ≤ r₀ → b ≤ 2 ^ n * a →
      ‖Q a b‖ ≤ g b / (1 - ρ) := by
    intro n
    induction n with
    | zero =>
      intro a b ha hab hb hn
      have hgb := hg0 b (ha.trans_le hab) hb
      calc ‖Q a b‖ ≤ g b := hcomp a b ha hab (by linarith) hb
        _ ≤ g b / (1 - ρ) := by
          rw [le_div_iff₀ h1ρ]
          nlinarith
    | succ n ih =>
      intro a b ha hab hb hn
      have hb0 : 0 < b := ha.trans_le hab
      have hgb := hg0 b hb0 hb
      rcases le_or_gt b (2 * a) with h2 | h2
      · calc ‖Q a b‖ ≤ g b := hcomp a b ha hab h2 hb
          _ ≤ g b / (1 - ρ) := by
            rw [le_div_iff₀ h1ρ]
            nlinarith
      · have ham : a ≤ b / 2 := by linarith
        have hmb : b / 2 ≤ b := by linarith
        have hm : b / 2 ≤ 2 ^ n * a := by
          rw [pow_succ] at hn
          linarith
        have e := hadd a (b / 2) b ha ham hmb hb
        have i1 := ih a (b / 2) ha ham (hmb.trans hb) hm
        have i2 := hcomp (b / 2) b (by linarith) hmb (by linarith) hb
        have i3 := hg b hb0 hb
        rw [e]
        calc ‖Q a (b / 2) + Q (b / 2) b‖ ≤ ‖Q a (b / 2)‖ + ‖Q (b / 2) b‖ := norm_add_le _ _
          _ ≤ g (b / 2) / (1 - ρ) + g b := add_le_add i1 i2
          _ ≤ ρ * g b / (1 - ρ) + g b := by gcongr
          _ = g b / (1 - ρ) := by field_simp; ring
  intro a b ha hab hb
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (b / a) (by norm_num : (1 : ℝ) < 2)
  refine key n a b ha hab hb ?_
  rw [div_lt_iff₀ ha] at hn
  exact hn.le

/-- **Comparable pairs control all light pairs**, power form: a bound `C b ^ p` on comparable
pairs gives `C b ^ p / (1 - 2⁻ᵖ)` on all light pairs. -/
theorem norm_le_of_comparable_rpow {Q : ℝ → ℝ → E} {r₀ C p : ℝ} (hC : 0 ≤ C) (hp : 0 < p)
    (hadd : ∀ a b d, 0 < a → a ≤ b → b ≤ d → d ≤ r₀ → Q a d = Q a b + Q b d)
    (hcomp : ∀ a b, 0 < a → a ≤ b → b ≤ 2 * a → b ≤ r₀ → ‖Q a b‖ ≤ C * b ^ p) :
    ∀ a b, 0 < a → a ≤ b → b ≤ r₀ → ‖Q a b‖ ≤ C * b ^ p / (1 - (2 : ℝ) ^ (-p)) := by
  have hρ1 : (2 : ℝ) ^ (-p) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine norm_le_of_comparable (Real.rpow_nonneg (by norm_num) _) hρ1
    (fun b hb _ => mul_nonneg hC (Real.rpow_nonneg hb.le _)) (fun b hb _ => ?_) hadd hcomp
  rw [Real.div_rpow hb.le (by norm_num), Real.rpow_neg (by norm_num)]
  have h2 : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  rw [div_eq_mul_inv]
  nlinarith [Real.rpow_nonneg hb.le p]

end QED.GradedProof.RPi4

end
