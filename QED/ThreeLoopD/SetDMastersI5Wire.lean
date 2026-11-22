/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5Def
public import QED.ThreeLoopD.SetDMastersI13Wire
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (d), master `I₅`: the input from the expansion of the subtracted integral

`I₅ C⁻¹ = (i5Tail + i5Rem) / (ε (1 - ε) Γ(1 + ε) Γ(1 - ε))`
(`QED.ThreeLoopD.setDMasterI5_eq`), and the tail is
`(G² B₂ + G B₁) / (ε² D)` with `B₂ = -2(1 - 2ε)`, `B₁ = 3`, `D = 6(1 - 2ε)²` and
`G = Γ(1 - ε)² / Γ(1 - 2ε)` (`QED.ThreeLoopD.i5Tail_eq`). With the truncations of `G` and of
`(Γ(1 + ε) Γ(1 - ε))⁻¹` from `QED.ThreeLoopD.SetDMastersI13Wire`, the expansion

  `Rem = (3 - π²/3) + (25 - 5ζ₃ - 5π²/3 - 4π⁴/45) ε
    + (143 + 4π² ln 2 - 36ζ₃ + 25/6 π²ζ₃ - 49/2 ζ₅ - 29π⁴/40 - 37π²/6) ε² + O(ε³)`
  (`QED.ThreeLoopD.i5RemLaurent`)

gives `HasTruncLaurent setDMasterI5 setDLaurentI5 2`
(`QED.ThreeLoopD.hasTruncLaurent_setDMasterI5_of_Rem`). The orders `ε⁰` to `ε⁴` of
`ε³ I₅ C⁻¹` match by the polynomial identity `QED.ThreeLoopD.i5Wire_key`, checked by `ring`.
The expansion of `Rem` is the one implied by the LR96 table with Laporta's `2 C₁`; numerically
the integral reproduces it. Its proof is the hypothesis that remains.

## Main results

* `QED.ThreeLoopD.setDMasterI5_eq`, `QED.ThreeLoopD.i5Tail_eq`.
* `QED.ThreeLoopD.hasTruncLaurent_setDMasterI5_of_Rem`.
-/

@[expose] public section

open Complex Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-- **The target expansion of `i5Rem`** through `ε²`. -/
noncomputable def i5RemLaurent (ε : ℂ) : ℂ :=
  (- 1 / 3 * (π : ℂ) ^ 2 + 3) + (- 4 / 45 * (π : ℂ) ^ 4 - 5 / 3 * (π : ℂ) ^ 2 - 5 * (zeta3 : ℂ)
    + 25) * ε + (- 29 / 40 * (π : ℂ) ^ 4 + 25 / 6 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    + 4 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 37 / 6 * (π : ℂ) ^ 2 - 36 * (zeta3 : ℂ)
    - 49 / 2 * (zeta5 : ℂ) + 143) * ε ^ 2

/-! ### The master and the tail -/

/-- The numerator coefficient of `G²` in `ε² · i5Tail`. -/
noncomputable def i5B2 (ε : ℂ) : ℂ := -2 * (1 - 2 * ε)

/-- The numerator coefficient of `G` in `ε² · i5Tail`. -/
noncomputable def i5B1 : ℂ := 3

/-- The denominator of `ε² · i5Tail`. -/
noncomputable def i5D (ε : ℂ) : ℂ := 6 * (1 - 2 * ε) ^ 2

theorem i5D_ne_zero {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : i5D ε ≠ 0 := by
  have h := setDGamma_lin_ne_zero hε 1 (-2) (by norm_num) (by norm_num) (x := 1 - 2 * ε) (by ring)
  simp only [i5D]
  simp [h]

/-- **The tail as a rational function of `ε` and `G`.** -/
theorem i5Tail_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    i5Tail ε = (i13G ε ^ 2 * i5B2 ε + i13G ε * i5B1) / (ε ^ 2 * i5D ε) := by
  have h := setDGamma_lin_ne_zero hε 1 (-2) (by norm_num) (by norm_num) (x := 1 - 2 * ε) (by ring)
  have h' : 1 - ε * 2 ≠ 0 := by rwa [mul_comm]
  simp only [i5Tail, i13Al0, i5B2, i5B1, i5D]
  generalize i13G ε = G
  field_simp
  ring

/-- `I₅ C⁻¹ = T / (ε (1 - ε) Γ(1 + ε) Γ(1 - ε))`. -/
theorem setDMasterI5_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    setDMasterI5 ε =
      i5T ε / (ε * (1 - ε) * (Gamma (1 + 1 * ε) * Gamma (1 + (-1) * ε))) := by
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have h1 := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 + (-1) * ε) (by ring)
  have h1' := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 - ε) (by ring)
  have hG1 := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε 1 (by norm_num))
  have hGm := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε (-1) (by norm_num))
  have hpi : (π : ℂ) ^ ε ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr pi_ne_zero))
  simp only [setDMasterI5, lr96I5, lr96C, QED.DimReg.lr96LoopFactor_four_sub]
  rw [show (1 : ℂ) + ε = 1 + 1 * ε by ring,
    Gamma_eq_div_one (s := ε) (t := 1 + 1 * ε) (p := ε) h0 (by ring) rfl,
    show (2 : ℂ) - ε = 1 + (-1) * ε + 1 by ring, Gamma_add_one _ h1]
  rw [show (1 : ℂ) * ε = ε by ring] at hG1 ⊢
  rw [show (1 : ℂ) + (-1) * ε = 1 - ε by ring] at hGm ⊢
  generalize Gamma (1 + ε) = A at *
  generalize Gamma (1 - ε) = B at *
  generalize (π : ℂ) ^ ε = P at *
  field_simp

/-! ### The polynomial identity -/

/-- `ε³` times the Laurent polynomial of `I₅ C⁻¹`. -/
noncomputable def i5L5e (ε : ℂ) : ℂ :=
  1 / 6 + 3 / 2 * ε + (- 1 / 3 * (π : ℂ) ^ 2 + 55 / 6) * ε ^ 2 + (- 4 / 45 * (π : ℂ) ^ 4
    - 7 / 3 * (π : ℂ) ^ 2 - 14 / 3 * (zeta3 : ℂ) + 95 / 2) * ε ^ 3 + (- 23 / 30 * (π : ℂ) ^ 4
    + 25 / 6 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 4 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 31 / 3 * (π : ℂ) ^ 2
    - 42 * (zeta3 : ℂ) - 49 / 2 * (zeta5 : ℂ) + 1351 / 6) * ε ^ 4

/-- The coefficient of `ε ^ 0` in `QED.ThreeLoopD.i5WireP`. -/
noncomputable def i5WP0 : ℂ :=
  ((4 / 45 * (π : ℂ) ^ 6 - 89 / 30 * (π : ℂ) ^ 4 + 28 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    + 24 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 111 * (π : ℂ) ^ 2 - 292 * (zeta3 : ℂ)
    - 141 * (zeta5 : ℂ) + 1863))

/-- The coefficient of `ε ^ 1` in `QED.ThreeLoopD.i5WireP`. -/
noncomputable def i5WP1 : ℂ :=
  ((37 / 108 * (π : ℂ) ^ 6 - 25 / 6 * (π : ℂ) ^ 4 * (zeta3 : ℂ) - 4 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ)
    + 73 / 4 * (π : ℂ) ^ 4 - 76 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 49 / 2 * (π : ℂ) ^ 2 * (zeta5 : ℂ)
    - 96 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) + 237 * (π : ℂ) ^ 2 - 8 * (zeta3 : ℂ) ^ 2
    + 1040 * (zeta3 : ℂ) + 540 * (zeta5 : ℂ) - 6236))

/-- The coefficient of `ε ^ 2` in `QED.ThreeLoopD.i5WireP`. -/
noncomputable def i5WP2 : ℂ :=
  ((- 1 / 225 * (π : ℂ) ^ 8 - 1363 / 540 * (π : ℂ) ^ 6 + 251 / 15 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
    + 16 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) - 143 / 4 * (π : ℂ) ^ 4 - 24 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    - 103 * (π : ℂ) ^ 2 * (zeta5 : ℂ) + 96 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) + 224 * (π : ℂ) ^ 2
    + 16 * (zeta3 : ℂ) ^ 2 - 1008 * (zeta3 : ℂ) - 588 * (zeta5 : ℂ) + 5404))

/-- The coefficient of `ε ^ 3` in `QED.ThreeLoopD.i5WireP`. -/
noncomputable def i5WP3 : ℂ :=
  ((- 743 / 43200 * (π : ℂ) ^ 8 + 5 / 24 * (π : ℂ) ^ 6 * (zeta3 : ℂ)
    + 1 / 5 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) + 343 / 120 * (π : ℂ) ^ 6
    - 278 / 15 * (π : ℂ) ^ 4 * (zeta3 : ℂ) - 49 / 40 * (π : ℂ) ^ 4 * (zeta5 : ℂ)
    - 16 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) + 329 / 12 * (π : ℂ) ^ 4
    + 4 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2 + 144 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    + 114 * (π : ℂ) ^ 2 * (zeta5 : ℂ) - 572 * (π : ℂ) ^ 2 - 48 * (zeta3 : ℂ) * (zeta5 : ℂ)))

/-- The coefficient of `ε ^ 4` in `QED.ThreeLoopD.i5WireP`. -/
noncomputable def i5WP4 : ℂ :=
  ((1333 / 10800 * (π : ℂ) ^ 8 - 883 / 1080 * (π : ℂ) ^ 6 * (zeta3 : ℂ)
    - 4 / 5 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) + 9 / 10 * (π : ℂ) ^ 6
    + 31 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ) + 301 / 60 * (π : ℂ) ^ 4 * (zeta5 : ℂ)
    - 118 / 5 * (π : ℂ) ^ 4 - 8 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2 + 96 * (zeta3 : ℂ) * (zeta5 : ℂ)))

/-- The coefficient of `ε ^ 5` in `QED.ThreeLoopD.i5WireP`. -/
noncomputable def i5WP5 : ℂ :=
  ((1 / 14400 * (π : ℂ) ^ 10 - 29 / 200 * (π : ℂ) ^ 8 + 221 / 270 * (π : ℂ) ^ 6 * (zeta3 : ℂ)
    + 4 / 5 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) - 37 / 30 * (π : ℂ) ^ 6
    - 11 / 15 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2 - 36 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
    - 163 / 30 * (π : ℂ) ^ 4 * (zeta5 : ℂ) + 143 / 5 * (π : ℂ) ^ 4
    + 16 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (zeta5 : ℂ) - 72 * (zeta5 : ℂ) ^ 2))

/-- The coefficient of `ε ^ 6` in `QED.ThreeLoopD.i5WireP`. -/
noncomputable def i5WP6 : ℂ :=
  ((- 1 / 7200 * (π : ℂ) ^ 10 - 29 / 5400 * (π : ℂ) ^ 8 * (zeta3 : ℂ)
    + 1 / 15 * (π : ℂ) ^ 6 * (zeta5 : ℂ) + 22 / 15 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2
    - 32 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (zeta5 : ℂ) + 144 * (zeta5 : ℂ) ^ 2))

/-- The coefficient of `ε ^ 7` in `QED.ThreeLoopD.i5WireP`. -/
noncomputable def i5WP7 : ℂ :=
  ((- 1 / 96000 * (π : ℂ) ^ 12 + 29 / 2700 * (π : ℂ) ^ 8 * (zeta3 : ℂ)
    + 8 / 135 * (π : ℂ) ^ 6 * (zeta3 : ℂ) ^ 2 - 2 / 15 * (π : ℂ) ^ 6 * (zeta5 : ℂ)
    - 26 / 15 * (π : ℂ) ^ 4 * (zeta3 : ℂ) * (zeta5 : ℂ) + 12 * (π : ℂ) ^ 2 * (zeta5 : ℂ) ^ 2))

/-- The coefficient of `ε ^ 8` in `QED.ThreeLoopD.i5WireP`. -/
noncomputable def i5WP8 : ℂ :=
  ((1 / 48000 * (π : ℂ) ^ 12 + 1 / 3600 * (π : ℂ) ^ 10 * (zeta3 : ℂ)
    - 1 / 200 * (π : ℂ) ^ 8 * (zeta5 : ℂ) - 16 / 135 * (π : ℂ) ^ 6 * (zeta3 : ℂ) ^ 2
    + 52 / 15 * (π : ℂ) ^ 4 * (zeta3 : ℂ) * (zeta5 : ℂ) - 24 * (π : ℂ) ^ 2 * (zeta5 : ℂ) ^ 2))

/-- The coefficient of `ε ^ 9` in `QED.ThreeLoopD.i5WireP`. -/
noncomputable def i5WP9 : ℂ :=
  ((- 1 / 1800 * (π : ℂ) ^ 10 * (zeta3 : ℂ) - 1 / 540 * (π : ℂ) ^ 8 * (zeta3 : ℂ) ^ 2
    + 1 / 100 * (π : ℂ) ^ 8 * (zeta5 : ℂ) + 1 / 15 * (π : ℂ) ^ 6 * (zeta3 : ℂ) * (zeta5 : ℂ)
    - 3 / 5 * (π : ℂ) ^ 4 * (zeta5 : ℂ) ^ 2))

/-- The coefficient of `ε ^ 10` in `QED.ThreeLoopD.i5WireP`. -/
noncomputable def i5WP10 : ℂ :=
  ((1 / 270 * (π : ℂ) ^ 8 * (zeta3 : ℂ) ^ 2 - 2 / 15 * (π : ℂ) ^ 6 * (zeta3 : ℂ) * (zeta5 : ℂ)
    + 6 / 5 * (π : ℂ) ^ 4 * (zeta5 : ℂ) ^ 2))

/-- The polynomial `(K S_p - ε³ L₅ D (1 - ε)) / ε⁵`. -/
noncomputable def i5WireP (ε : ℂ) : ℂ :=
  i5WP0 + i5WP1 * ε + i5WP2 * ε ^ 2 + i5WP3 * ε ^ 3 + i5WP4 * ε ^ 4 + i5WP5 * ε ^ 5 + i5WP6 * ε ^ 6
    + i5WP7 * ε ^ 7 + i5WP8 * ε ^ 8 + i5WP9 * ε ^ 9 + i5WP10 * ε ^ 10

/-- The truncated numerator `G_p² B₂ + G_p B₁ + ε² D Rem_L`. -/
noncomputable def i5K (ε : ℂ) : ℂ :=
  i13Gp ε ^ 2 * i5B2 ε + i13Gp ε * i5B1 + ε ^ 2 * i5D ε * i5RemLaurent ε

/-- **The polynomial identity behind the expansion of `I₅`**: the orders `ε⁰` to `ε⁴` of
`K S_p` are those of `ε³ L₅ D (1 - ε)`. -/
theorem i5Wire_key (ε : ℂ) :
    i5K ε * i13Sp ε - i5L5e ε * i5D ε * (1 - ε) = ε ^ 5 * i5WireP ε := by
  simp only [i5K, i13Gp, i5B2, i5B1, i5D, i5RemLaurent, i13Sp, i5L5e, i5WireP,
    i5WP0, i5WP1, i5WP2, i5WP3, i5WP4, i5WP5, i5WP6, i5WP7, i5WP8, i5WP9, i5WP10]
  ring

/-! ### The expansion -/

/-- `H = ε ((2 G_p ΔG + ε⁶ ΔG²) B₂ + ΔG B₁) + D R`. -/
noncomputable def i5H (ε R : ℂ) : ℂ :=
  ε * ((2 * i13Gp ε * i13dG ε + ε ^ 6 * i13dG ε ^ 2) * i5B2 ε + i13dG ε * i5B1) + i5D ε * R

/-- The remainder `R₅` with `I₅ C⁻¹ = L₅ + ε² R₅`, given `Rem = Rem_L + ε³ R`. -/
noncomputable def i5R (ε R : ℂ) : ℂ :=
  (i5WireP ε + ε * i5K ε * i13dS ε + i5H ε R * i13S ε) / (i5D ε * (1 - ε))

theorem analyticAt_i5R {R : ℂ → ℂ} (hR : AnalyticAt ℂ R 0) :
    AnalyticAt ℂ (fun ε => i5R ε (R ε)) 0 := by
  have hV : AnalyticAt ℂ i13V 0 := by
    have h1 := analyticAt_logGammaRem_mul (-1)
    have h2 := analyticAt_logGammaRem_mul (-2)
    unfold i13V
    fun_prop
  have hW : AnalyticAt ℂ i13W 0 := by
    have h1 := analyticAt_logGammaRem_mul 1
    have h2 := analyticAt_logGammaRem_mul (-1)
    unfold i13W
    fun_prop
  have hX : AnalyticAt ℂ i13X 0 := by unfold i13X; fun_prop
  have hY : AnalyticAt ℂ i13Y 0 := by unfold i13Y; fun_prop
  have hEG : AnalyticAt ℂ (fun ε => QED.DimReg.expRem3 (ε ^ 2 * i13X ε)) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  have hES : AnalyticAt ℂ (fun ε => QED.DimReg.expRem3 (-(ε ^ 2 * i13Y ε))) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  have hdG : AnalyticAt ℂ i13dG 0 := by unfold i13dG i13dGp; fun_prop
  have hdS : AnalyticAt ℂ i13dS 0 := by unfold i13dS i13dSp; fun_prop
  have hS : AnalyticAt ℂ i13S 0 := by unfold i13S; fun_prop
  have hP : AnalyticAt ℂ i5WireP 0 := by unfold i5WireP; fun_prop
  have hGp : AnalyticAt ℂ i13Gp 0 := by unfold i13Gp; fun_prop
  have hB2 : AnalyticAt ℂ i5B2 0 := by unfold i5B2; fun_prop
  have hD : AnalyticAt ℂ i5D 0 := by unfold i5D; fun_prop
  have hRL : AnalyticAt ℂ i5RemLaurent 0 := by unfold i5RemLaurent; fun_prop
  have hK : AnalyticAt ℂ i5K 0 := by unfold i5K; fun_prop
  unfold i5R i5H
  refine AnalyticAt.div (by fun_prop) (by fun_prop) ?_
  norm_num [i5D]

/-- **The set (d) input for `I₅` from the expansion of `Rem`**: if
`Rem = Rem_L + ε³ R` with `R` analytic at `0`, then `I₅ C⁻¹ = L₅ + ε² R₅` with `R₅` analytic
at `0`. -/
theorem hasTruncLaurent_setDMasterI5_of_Rem (hRem : HasTruncLaurent i5Rem i5RemLaurent 3) :
    HasTruncLaurent setDMasterI5 setDLaurentI5 2 := by
  obtain ⟨RR, hRR, hRe⟩ := hRem
  refine ⟨fun ε => i5R ε (RR ε), analyticAt_i5R hRR, ?_⟩
  filter_upwards [setDGamma_eventually_small, hRe, self_mem_nhdsWithin] with ε hε hRε h0
  have h0 : ε ≠ 0 := h0
  have hD := i5D_ne_zero hε
  have h1 : (1 : ℂ) - ε ≠ 0 :=
    setDGamma_lin_ne_zero hε 1 (-1) (by norm_num) (by norm_num) (by ring)
  have hL : setDLaurentI5 ε = i5L5e ε / ε ^ 3 := by
    simp only [setDLaurentI5, laportaC1, i5L5e]
    field_simp
    ring
  have hS0 : i13Sp ε + ε ^ 6 * i13dS ε ≠ 0 := by
    rw [← i13S_trunc]; exact Complex.exp_ne_zero _
  have hSG : Gamma (1 + 1 * ε) * Gamma (1 + (-1) * ε) = (i13Sp ε + ε ^ 6 * i13dS ε)⁻¹ := by
    rw [i13GammaProd_eq hε, ← i13S_trunc, i13S, Complex.exp_neg, inv_inv]
  have key := i5Wire_key ε
  rw [setDMasterI5_eq h0 hε, i5T, i5Tail_eq h0 hε, hRε, i13G_eq hε, i13G_trunc, hSG, hL,
    i5R, i5H, i13S_trunc]
  simp only [i5K] at key ⊢
  generalize i13Gp ε = Gp at *
  generalize i13dG ε = dG at *
  generalize i5B2 ε = B2 at *
  generalize i5D ε = D at *
  generalize i5RemLaurent ε = RL at *
  generalize RR ε = R at *
  generalize i13Sp ε = Sp at *
  generalize i13dS ε = dS at *
  generalize i5L5e ε = L at *
  generalize i5WireP ε = P at *
  field_simp
  linear_combination key

end QED.ThreeLoopD
