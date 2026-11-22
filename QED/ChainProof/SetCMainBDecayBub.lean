/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBClosed
import QED.Integration.LoopBounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Set (c), the bubble classes: a sharper bound on the bubble energy integral

Helper level for set (c), the bubble classes `QED.ChainProof.SetCLink.repB i`, at fixed
`ε > 0`. The Fubini condition of `QED.ChainProof.SetCMainB.jointEnergyFirstIntegral_nestB` asks
the outer factor, times `(1 + ‖K‖)^{17/2}`, to be integrable in the outer energies. For two of
the twelve orbits (one open line between the bubble's photon endpoints) the outer factor decays
only like `|K⁰|⁻⁹` and that fails. Here the exponent is lowered to `6`:

* `abs_numer_le_quad`, `norm_bracketA_le_ball`: inside the ball `‖v‖ < 4‖k‖ + 2` the bracket of
  the closed form is quadratic in `1 + ‖k‖` (the bound `constA (1 + ‖v‖)²` with `constA` cubic in
  `k` gives `(1 + ‖k‖)⁵` there);
* **`exists_norm_timeSum_le_six`**, **`exists_norm_spatialG_le_six`**:
  `‖spatialG P ε k μ ν v‖ ≤ C (1 + ‖k‖)⁶ (1 + ‖v‖)^{-7/2}`;
* `OuterDecay'`: the decay condition with the exponent `6`;
* **`integrable_bubbleT_nestB'`**, **`jointEnergyFirstIntegral_nestB'`**: the Fubini condition
  and nested equals joint under `OuterDecay'`.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.ChainProof.SetCMainB

open QED.WickModel QED.WickModel.VacuumPolarizationLimit QED.OneLoop
open QED.TwoLoop.NestedVPFubiniBound (constAPoly constAPoly_nonneg constA_le constS₂_nonneg
  constS₁_nonneg continuous_timeSum_joint)

/-! ### The bracket inside the ball -/

/-- The numerator is quadratic in the momenta. -/
theorem abs_numer_le_quad (M : ℝ) (k ℓ : Fin 4 → ℝ) (μ ν : Fin 4) :
    |numer M k ℓ μ ν| ≤ 4 * (6 * ((‖ℓ‖ + ‖k‖) * ‖ℓ‖) + M ^ 2) := by
  have hlk : ‖ℓ + k‖ ≤ ‖ℓ‖ + ‖k‖ := norm_add_le _ _
  have e1 : |(ℓ + k) μ * ℓ ν| ≤ (‖ℓ‖ + ‖k‖) * ‖ℓ‖ := by
    rw [abs_mul]
    exact mul_le_mul ((abs_apply_le _ μ).trans hlk) (abs_apply_le ℓ ν) (abs_nonneg _)
      (by positivity)
  have e2 : |(ℓ + k) ν * ℓ μ| ≤ (‖ℓ‖ + ‖k‖) * ‖ℓ‖ := by
    rw [abs_mul]
    exact mul_le_mul ((abs_apply_le _ ν).trans hlk) (abs_apply_le ℓ μ) (abs_nonneg _)
      (by positivity)
  have e3 : |Minkowski.dot (ℓ + k) ℓ| ≤ 4 * ((‖ℓ‖ + ‖k‖) * ‖ℓ‖) :=
    (abs_dot_le _ _).trans (by gcongr)
  have e5 : |(Minkowski.dot (ℓ + k) ℓ + M ^ 2) * Minkowski.metric μ ν|
      ≤ 4 * ((‖ℓ‖ + ‖k‖) * ‖ℓ‖) + M ^ 2 := by
    rw [abs_mul]
    calc |Minkowski.dot (ℓ + k) ℓ + M ^ 2| * |Minkowski.metric μ ν|
        ≤ (4 * ((‖ℓ‖ + ‖k‖) * ‖ℓ‖) + M ^ 2) * 1 := by
          gcongr
          · refine (abs_add_le _ _).trans ?_
            rw [abs_of_nonneg (sq_nonneg M)]
            linarith
          · exact abs_metric_le μ ν
      _ = _ := by ring
  have hsum : |(ℓ + k) μ * ℓ ν + (ℓ + k) ν * ℓ μ
      - (Minkowski.dot (ℓ + k) ℓ + M ^ 2) * Minkowski.metric μ ν|
      ≤ 6 * ((‖ℓ‖ + ‖k‖) * ‖ℓ‖) + M ^ 2 := by
    refine (abs_sub _ _).trans ?_
    have := abs_add_le ((ℓ + k) μ * ℓ ν) ((ℓ + k) ν * ℓ μ)
    linarith
  unfold numer
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  exact mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- The constant of the bracket inside the ball. -/
noncomputable def constBall (P : Params) (μ ν : Fin 4) : ℝ :=
  |alpha μ ν| * (77 + P.mass 0 ^ 2) + 4 * (180 + P.mass 0 ^ 2)

theorem constBall_nonneg (P : Params) (μ ν : Fin 4) : 0 ≤ constBall P μ ν := by
  unfold constBall; positivity

/-- **Inside the ball `‖v‖ < 4‖k‖ + 2`** the flavour-independent bracket is quadratic in
`1 + ‖k‖`. -/
theorem norm_bracketA_le_ball (P : Params) {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (μ ν : Fin 4)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) {v : Fin 3 → ℝ} (hv : ‖v‖ < 4 * ‖k‖ + 2) :
    ‖bracketA P ε k μ ν x v‖ ≤ constBall P μ ν * (1 + ε) * (1 + ‖k‖) ^ 2 := by
  set s := 1 + ‖k‖ with hs
  set M := P.mass 0
  have hK := norm_nonneg k
  have hs1 : 1 ≤ s := by linarith
  have hs2 : 1 ≤ s ^ 2 := one_le_pow₀ hs1
  have hvs : ‖v‖ ≤ 4 * s := by linarith
  -- the Feynman mass term
  have hi : ∀ i : Fin 3, (v i + x * k i.succ) ^ 2 ≤ 25 * s ^ 2 := by
    intro i
    have h1 : |v i| ≤ ‖v‖ := by
      have := norm_le_pi_norm v i
      rwa [Real.norm_eq_abs] at this
    have h2 : |x * k i.succ| ≤ ‖k‖ := by
      rw [abs_mul, abs_of_nonneg hx.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hx.2).trans (abs_apply_le k _)
    have h3 : |v i + x * k i.succ| ≤ 5 * s := (abs_add_le _ _).trans (by linarith)
    calc (v i + x * k i.succ) ^ 2 = |v i + x * k i.succ| ^ 2 := (sq_abs _).symm
      _ ≤ (5 * s) ^ 2 := by gcongr
      _ = 25 * s ^ 2 := by ring
  have hD : |x * (1 - x) * Minkowski.dot k k| ≤ s ^ 2 := by
    have hx1 : 0 ≤ x * (1 - x) := by nlinarith [hx.1, hx.2]
    have hx2 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
    have hd := abs_dot_le k k
    rw [abs_mul, abs_of_nonneg hx1]
    have hk2 : ‖k‖ * ‖k‖ ≤ s ^ 2 := by nlinarith
    calc x * (1 - x) * |Minkowski.dot k k| ≤ 1 / 4 * (4 * (‖k‖ * ‖k‖)) := by
          gcongr
      _ ≤ s ^ 2 := by linarith
  have hW : |SelfEnergyLimit.massW M M k x v| ≤ (76 + M ^ 2) * s ^ 2 := by
    have e : SelfEnergyLimit.massW M M k x v = ∑ i : Fin 3, (v i + x * k i.succ) ^ 2 +
        (M ^ 2 + x * (1 - x) * Minkowski.dot k k) := by
      simp only [SelfEnergyLimit.massW, selfEnergyFeynmanMass]
      ring
    rw [e]
    have hS : 0 ≤ ∑ i : Fin 3, (v i + x * k i.succ) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hS' : ∑ i : Fin 3, (v i + x * k i.succ) ^ 2 ≤ 75 * s ^ 2 := by
      rw [Fin.sum_univ_three]
      linarith [hi 0, hi 1, hi 2]
    have hM : M ^ 2 ≤ M ^ 2 * s ^ 2 := le_mul_of_one_le_right (sq_nonneg M) hs2
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg hS]
    have := (abs_add_le (M ^ 2) (x * (1 - x) * Minkowski.dot k k))
    rw [abs_of_nonneg (sq_nonneg M)] at this
    nlinarith
  -- the numerator
  have hl : ‖(Fin.cons (-(x * k 0)) v : Fin 4 → ℝ)‖ ≤ 5 * s := by
    refine (QED.Integration.norm_finCons_le _ _).trans ?_
    have h1 := abs_apply_le k 0
    have : |-(x * k 0)| ≤ |k 0| := by
      rw [abs_neg, abs_mul, abs_of_nonneg hx.1]
      exact mul_le_of_le_one_left (abs_nonneg _) hx.2
    linarith
  have hN : |numer M k (Fin.cons (-(x * k 0)) v) μ ν| ≤ 4 * (180 + M ^ 2) * s ^ 2 := by
    refine (abs_numer_le_quad M k _ μ ν).trans ?_
    set L := ‖(Fin.cons (-(x * k 0)) v : Fin 4 → ℝ)‖
    have hL0 : 0 ≤ L := norm_nonneg _
    have hq : (L + ‖k‖) * L ≤ 30 * s ^ 2 := by
      have h1 : L + ‖k‖ ≤ 6 * s := by linarith
      calc (L + ‖k‖) * L ≤ (6 * s) * (5 * s) := by gcongr
        _ = 30 * s ^ 2 := by ring
    have hM : M ^ 2 ≤ M ^ 2 * s ^ 2 := le_mul_of_one_le_right (sq_nonneg M) hs2
    nlinarith
  -- assembling
  have hz : ‖-(SelfEnergyLimit.massW M M k x v : ℂ) + ε * I‖
      ≤ |SelfEnergyLimit.massW M M k x v| + ε := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, norm_I,
      mul_one, Real.norm_eq_abs, abs_of_pos hε]
  have hα : 0 ≤ |alpha μ ν| := abs_nonneg _
  simp only [bracketA]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : |alpha μ ν| * ‖-(SelfEnergyLimit.massW M M k x v : ℂ) + ε * I‖
      ≤ |alpha μ ν| * ((77 + M ^ 2) * (1 + ε) * s ^ 2) := by
    refine mul_le_mul_of_nonneg_left (hz.trans ?_) hα
    have hεs : ε ≤ ε * s ^ 2 := le_mul_of_one_le_right hε.le hs2
    nlinarith [sq_nonneg M, mul_nonneg hε.le (sq_nonneg M), mul_nonneg hε.le (sq_nonneg s)]
  have h2 : 4 * (180 + M ^ 2) * s ^ 2 ≤ 4 * (180 + M ^ 2) * (1 + ε) * s ^ 2 := by
    have : 0 ≤ 4 * (180 + M ^ 2) * s ^ 2 := by positivity
    nlinarith
  have e : constBall P μ ν * (1 + ε) * s ^ 2 =
      |alpha μ ν| * ((77 + M ^ 2) * (1 + ε) * s ^ 2) + 4 * (180 + M ^ 2) * (1 + ε) * s ^ 2 := by
    simp only [constBall, M]
    ring
  rw [e]
  linarith

/-! ### The closed forms and the energy integral -/

variable {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
  (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)

theorem rpow_seven_halves_le {u s : ℝ} (hu : 1 ≤ u) (hus : u ≤ 4 * s) :
    u ^ (7 / 2 : ℝ) ≤ 256 * s ^ 4 := by
  have h1 : u ^ (7 / 2 : ℝ) ≤ u ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
  have h2 : u ^ (4 : ℝ) = u ^ 4 := by rw [← Real.rpow_natCast]; norm_num
  have h3 : u ^ 4 ≤ (4 * s) ^ 4 := by gcongr
  rw [h2] at h1
  nlinarith

include hm hM₁ hM₂ hPV₁ hPV₂ in
/-- **The closed forms are bounded by `C (1 + ‖k‖)⁶ (1 + ‖v‖)^{-7/2}`**, for `ε > 0`, the
Pauli–Villars conditions and `x ∈ [0, 1]`. -/
theorem exists_norm_timeSum_le_six {ε : ℝ} (hε : 0 < ε) (μ ν : Fin 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin 4 → ℝ) (x : ℝ), x ∈ Icc (0 : ℝ) 1 → ∀ v : Fin 3 → ℝ,
      ‖timeSum P ε k μ ν x v‖ ≤ C * (1 + ‖k‖) ^ 6 * (1 + ‖v‖) ^ (-(7 / 2 : ℝ)) := by
  have hS₂ := constS₂_nonneg P
  have hS₁ := constS₁_nonneg hm hM₁ hM₂ μ ν
  have hCA := constAPoly_nonneg P μ ν
  have hCB := constBall_nonneg P μ ν
  set X := 3 / 2 * (3 / 2 + 1) * constS₂ P * (2 / 9 : ℝ) ^ (-(3 / 2 + 2 : ℝ)) with hX
  set Y := 3 / 2 * constS₁ P μ ν * (2 / 9 : ℝ) ^ (-(3 / 2 + 1 : ℝ)) with hY
  set Z₂c := 3 / 2 * (3 / 2 + 1) * constS₂ P * ε ^ (-(3 / 2 + 2 : ℝ)) with hZ₂c
  set Z₁c := 3 / 2 * constS₁ P μ ν * ε ^ (-(3 / 2 + 1 : ℝ)) with hZ₁c
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hZ₂0 : 0 ≤ Z₂c := by positivity
  have hZ₁0 : 0 ≤ Z₁c := by positivity
  set C₁ := 256 * (π / 2 * (constBall P μ ν * (1 + ε) * Z₂c + Z₁c))
  set C₂ := π / 2 * (constAPoly P μ ν * X + Y) * (1 + ε)
  have hC₁ : 0 ≤ C₁ := by positivity
  have hC₂ : 0 ≤ C₂ := by positivity
  refine ⟨C₁ + C₂, by positivity, fun k x hx v => ?_⟩
  set s := 1 + ‖k‖ with hs
  set u := 1 + ‖v‖ with hu
  have hs1 : 1 ≤ s := by linarith [norm_nonneg k]
  have hu1 : 1 ≤ u := by linarith [norm_nonneg v]
  have hu0 : 0 < u := by linarith
  have hu72 : 0 < u ^ (-(7 / 2 : ℝ)) := Real.rpow_pos_of_pos hu0 _
  have hs6 : 0 ≤ s ^ 6 := by positivity
  rcases le_or_gt (4 * ‖k‖ + 2) ‖v‖ with hv | hv
  · -- outside the ball
    have hlow : 2 / 9 * (1 + ‖v‖) ^ 2
        ≤ max ε (SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v) :=
      (QED.TwoLoop.NestedVPFubiniBound.massW_ge_of_large _ k hx hv).trans (le_max_right _ _)
    have h := norm_timeSum_le hm hM₁ hM₂ hPV₁ hPV₂ k μ ν (by norm_num : (0 : ℝ) < 2 / 9) hε hx v
      hlow
    have hK : constK P k μ ν (2 / 9) ≤ π / 2 * (constAPoly P μ ν * X + Y) * s ^ 3 := by
      have hA := constA_le P k μ ν
      have hs3 : 1 ≤ s ^ 3 := one_le_pow₀ hs1
      unfold constK
      rw [← hX, ← hY]
      have : constA P k μ ν * X + Y ≤ (constAPoly P μ ν * X + Y) * s ^ 3 := by
        have e1 : constA P k μ ν * X ≤ constAPoly P μ ν * s ^ 3 * X :=
          mul_le_mul_of_nonneg_right hA hX0
        have e2 : Y ≤ Y * s ^ 3 := le_mul_of_one_le_right hY0 hs3
        nlinarith
      calc π / 2 * (constA P k μ ν * X + Y) ≤ π / 2 * ((constAPoly P μ ν * X + Y) * s ^ 3) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have hu5 : u ^ (-(5 : ℝ)) ≤ u ^ (-(7 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
    have hs36 : s ^ 3 ≤ s ^ 6 := pow_le_pow_right₀ hs1 (by norm_num)
    refine h.trans ?_
    calc constK P k μ ν (2 / 9) * (1 + ε) * u ^ (-(5 : ℝ))
        ≤ π / 2 * (constAPoly P μ ν * X + Y) * s ^ 3 * (1 + ε) * u ^ (-(7 / 2 : ℝ)) := by
          gcongr
      _ = C₂ * s ^ 3 * u ^ (-(7 / 2 : ℝ)) := by ring
      _ ≤ C₂ * s ^ 6 * u ^ (-(7 / 2 : ℝ)) := by gcongr
      _ ≤ (C₁ + C₂) * s ^ 6 * u ^ (-(7 / 2 : ℝ)) := by
          gcongr
          linarith
  · -- inside the ball
    set lam := max ε (SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v)
    have hlam : ε ≤ lam := le_max_left _ _
    have hA := norm_bracketA_le_ball P hε k μ ν hx hv
    have b2 := norm_sum_loopCoeff_cpow_le hm hM₁ hM₂ hPV₁ hPV₂ hε k x v
    have b1 := norm_sum_loopCoeff_bracketB_cpow_le hm hM₁ hM₂ hPV₁ hPV₂ hε k μ ν x v
    have r2 : lam ^ (-(3 / 2 + 2 : ℝ)) ≤ ε ^ (-(3 / 2 + 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hε hlam (by norm_num)
    have r1 : lam ^ (-(3 / 2 + 1 : ℝ)) ≤ ε ^ (-(3 / 2 + 1 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hε hlam (by norm_num)
    rw [timeSum_eq, norm_mul, SelfEnergyLimit.norm_ofReal_div_two_pi]
    set Z₂ := ∑ f, (P.loopCoeff f : ℂ) *
      (-(SelfEnergyLimit.massW (P.mass f) (P.mass f) k x v : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))
    set Z₁ := ∑ f, ((P.loopCoeff f * bracketB P μ ν f : ℝ) : ℂ) *
      (-(SelfEnergyLimit.massW (P.mass f) (P.mass f) k x v : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))
    have hZ₂ : ‖Z₂‖ ≤ Z₂c := b2.trans (by rw [hZ₂c]; gcongr)
    have hZ₁ : ‖Z₁‖ ≤ Z₁c := b1.trans (by rw [hZ₁c]; gcongr)
    rw [← hs] at hA
    have hs2 : 1 ≤ s ^ 2 := one_le_pow₀ hs1
    have hAZ : ‖bracketA P ε k μ ν x v * Z₂ + Z₁‖
        ≤ (constBall P μ ν * (1 + ε) * Z₂c + Z₁c) * s ^ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have e1 : ‖bracketA P ε k μ ν x v‖ * ‖Z₂‖ ≤ constBall P μ ν * (1 + ε) * s ^ 2 * Z₂c :=
        mul_le_mul hA hZ₂ (norm_nonneg _) (by positivity)
      have e2 : Z₁c ≤ Z₁c * s ^ 2 := le_mul_of_one_le_right hZ₁0 hs2
      calc ‖bracketA P ε k μ ν x v‖ * ‖Z₂‖ + ‖Z₁‖
          ≤ constBall P μ ν * (1 + ε) * s ^ 2 * Z₂c + Z₁c * s ^ 2 :=
            add_le_add e1 (hZ₁.trans e2)
        _ = _ := by ring
    -- `s² ≤ 256 s⁶ u^{-7/2}` inside the ball
    have hus : u ≤ 4 * s := by rw [hu, hs]; linarith
    have hs2u : s ^ 2 ≤ 256 * s ^ 6 * u ^ (-(7 / 2 : ℝ)) := by
      have h7 := rpow_seven_halves_le hu1 hus
      have hinv : u ^ (-(7 / 2 : ℝ)) * u ^ (7 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add hu0]; norm_num
      have hp : 0 < u ^ (7 / 2 : ℝ) := Real.rpow_pos_of_pos hu0 _
      have : s ^ 2 * u ^ (7 / 2 : ℝ) ≤ 256 * s ^ 6 := by
        calc s ^ 2 * u ^ (7 / 2 : ℝ) ≤ s ^ 2 * (256 * s ^ 4) := by gcongr
          _ = 256 * s ^ 6 := by ring
      calc s ^ 2 = s ^ 2 * u ^ (7 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ)) := by
            rw [mul_assoc, mul_comm (u ^ (7 / 2 : ℝ)), hinv, mul_one]
        _ ≤ 256 * s ^ 6 * u ^ (-(7 / 2 : ℝ)) := by gcongr
    have hB0 : 0 ≤ constBall P μ ν * (1 + ε) * Z₂c + Z₁c := by positivity
    calc π / 2 * ‖bracketA P ε k μ ν x v * Z₂ + Z₁‖
        ≤ π / 2 * ((constBall P μ ν * (1 + ε) * Z₂c + Z₁c) * s ^ 2) :=
          mul_le_mul_of_nonneg_left hAZ (by positivity)
      _ ≤ π / 2 * ((constBall P μ ν * (1 + ε) * Z₂c + Z₁c) *
            (256 * s ^ 6 * u ^ (-(7 / 2 : ℝ)))) := by gcongr
      _ = C₁ * s ^ 6 * u ^ (-(7 / 2 : ℝ)) := by ring
      _ ≤ (C₁ + C₂) * s ^ 6 * u ^ (-(7 / 2 : ℝ)) := by
          gcongr
          linarith

include hm hM₁ hM₂ hPV₁ hPV₂ in
/-- **The energy integral is bounded by `C (1 + ‖k‖)⁶ (1 + ‖v‖)^{-7/2}`**, for `ε > 0` and the
Pauli–Villars conditions, with `C` depending only on the parameters, `ε`, `μ` and `ν`. -/
theorem exists_norm_spatialG_le_six {ε : ℝ} (hε : 0 < ε) (μ ν : Fin 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin 4 → ℝ) (v : Fin 3 → ℝ),
      ‖spatialG P ε k μ ν v‖ ≤ C * (1 + ‖k‖) ^ 6 * (1 + ‖v‖) ^ (-(7 / 2 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_timeSum_le_six hm hM₁ hM₂ hPV₁ hPV₂ hε μ ν
  set V := (volume.restrict (Ioc (0 : ℝ) 1)).real univ
  have hV : 0 ≤ V := measureReal_nonneg
  refine ⟨‖kappa P.e‖ * C * V, by positivity, fun k v => ?_⟩
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun x => kappa P.e * timeSum P ε k μ ν x v)
    (C := ‖kappa P.e‖ * (C * (1 + ‖k‖) ^ 6 * (1 + ‖v‖) ^ (-(7 / 2 : ℝ))))
    ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC k x (Ioc_subset_Icc_self hx) v) (norm_nonneg _))
  refine (show ‖spatialG P ε k μ ν v‖ ≤ _ from h).trans (le_of_eq ?_)
  ring

/-! ### Nested equals joint under the weaker decay -/

/-- **The decay of the outer factor, exponent `6`**: at every outer spatial momentum `v'`, each
entry of `O`, times `(1 + ‖K‖)⁶`, is dominated by an integrable function of the outer
energies. -/
def OuterDecay' (O : (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (K : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ) : Prop :=
  ∀ (v' : Fin 2 → Fin 3 → ℝ) (ρ σ : Fin 4), ∃ h : (Fin 2 → ℝ) → ℝ, Integrable h ∧
    ∀ t' : Fin 2 → ℝ, ‖O (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) ρ σ‖ *
      (1 + ‖K fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)‖) ^ 6 ≤ h t'

variable (hε : 0 < P.ε)

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- **The Fubini condition for `nestB`** under `OuterDecay'`, at every outer spatial
momentum. -/
theorem integrable_bubbleT_nestB' {O : (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    {K : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ} (hO : ∀ ρ σ, Continuous fun ℓ' => O ℓ' ρ σ)
    (hK : Continuous K) (hd : OuterDecay' O K) (v' : Fin 2 → Fin 3 → ℝ) :
    Integrable fun p : (Fin 2 → ℝ) × (Fin 3 → ℝ) => bubbleT (nestB P O K) p.1 v' p.2 := by
  simp only [bubbleT_nestB hε]
  refine integrable_finsetSum _ fun ρ _ => integrable_finsetSum _ fun σ _ => ?_
  obtain ⟨h, hh, hb⟩ := hd v' ρ σ
  obtain ⟨Ci, hCi0, hCi⟩ := exists_norm_spatialG_le_six hm hM₁ hM₂ hPV₁ hPV₂ hε ρ σ
  have hint : Integrable (fun p : (Fin 2 → ℝ) × (Fin 3 → ℝ) =>
      Ci * (h p.1 * (1 + ‖p.2‖) ^ (-(7 / 2 : ℝ)))) :=
    (hh.mul_prod (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 7 / 2)
      (by simp; norm_num))).const_mul Ci
  have hc := continuous_consFam v'
  refine hint.mono' (((hO ρ σ).comp (hc.comp continuous_fst)).aestronglyMeasurable.mul
    (aestronglyMeasurable_spatialG_comp hε (hK.comp hc) ρ σ))
    (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨t', w⟩ := p
  simp only
  rw [norm_mul]
  set k := K fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)
  have h1 := hb t'
  have h2 := hCi k w
  have hO0 := norm_nonneg (O (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) ρ σ)
  calc ‖O (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) ρ σ‖ * ‖spatialG P P.ε k ρ σ w‖
      ≤ ‖O (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) ρ σ‖ *
          (Ci * (1 + ‖k‖) ^ 6 * (1 + ‖w‖) ^ (-(7 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 hO0
    _ = Ci * ((‖O (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) ρ σ‖ *
          (1 + ‖k‖) ^ 6) * (1 + ‖w‖) ^ (-(7 / 2 : ℝ))) := by ring
    _ ≤ Ci * (h t' * (1 + ‖w‖) ^ (-(7 / 2 : ℝ))) := by gcongr

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- **Nested equals joint for a bubble in a two-loop outer factor**, under `OuterDecay'`: given
both stages of (T₉) at three loops for `nestB`, continuity of the outer factor and of the photon
momentum, the value at three loops is the joint energy-first integral at two loops of
`outerBub`, which is integrable in both stages. -/
theorem jointEnergyFirstIntegral_nestB' {O : (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    {K : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ} (hO : ∀ ρ σ, Continuous fun ℓ' => O ℓ' ρ σ)
    (hK : Continuous K) (hd : OuterDecay' O K)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 3 (nestB P O K)) :
    QED.TwoLoop.jointEnergyFirstIntegral 3 (nestB P O K) =
        QED.TwoLoop.jointEnergyFirstIntegral 2 (outerBub P O K) ∧
      QED.TwoLoop.jointEnergyFirstIntegrable 2 (outerBub P O K) := by
  have hB := integrable_bubbleT_nestB' hm hM₁ hM₂ hPV₁ hPV₂ hε hO hK hd
  rw [← bubbleJ_nestB hm hM₁ hM₂ hPV₁ hPV₂ hε]
  exact ⟨jointEnergyFirstIntegral_three_eq_inner _ hF (Filter.Eventually.of_forall hB),
    jointEnergyFirstIntegrable_inner _ hF hB⟩

end QED.ChainProof.SetCMainB

end
