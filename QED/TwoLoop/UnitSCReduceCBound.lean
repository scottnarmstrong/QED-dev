/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCReduceCV
public import QED.TwoLoop.UnitXGraphReduceBound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integrability of the `C₊` integrand on the simplex

The real integrand `cornerG` of the class `C₊` (`QED/TwoLoop/UnitSCReduceCV.lean`) is integrable
on the simplex `Δ₇` (`integrableOn_cornerG`), for `0 < m_γ ≤ Λ` and `m = 1`.

The bound (as for the crossed ladder, `QED/TwoLoop/UnitXGraphReduceBound.lean`). On the open
simplex the slot numerators of `C₊` satisfy `|S₀|, |S₁|, |T₀|, |T₁| ≤ 2U` (`abs_cpS0n_le`, …).
By the polynomial identities of `QED/TwoLoop/UnitSCGraphCpMain.lean`,
`512 W M₁ = H₁(S₀, S₁, T₀, T₁, U)` and `-1024 M₂ = H₂(S₀, S₁, T₀, T₁, U; ℓ)` with `H₁`
homogeneous of degree `4` and `H₂` of degree `2` in the slot data and linear in four group sums
`ℓ` (each in `[-1, 1]`); bounded on the compact cube `[-2, 2]ⁿ`, they give `|W M₁| ≤ C₁ U⁴`,
`|M₂| ≤ C₂ U²`. With `U ≤ 1` and `V ≥ v₀ = (3/4) min(1/4, m_γ²)`
(`QED.Integration.TwoLoop.symanzikV_classCpPV_ge`), `|cornerG| ≤ C/U³`. Finally
`∏ₖ zₖ ≤ z_o² y₃ y₄ z_a² z_b² = (z_o y₃)(z_o z_b)(z_a y₄)(z_a z_b) ≤ U⁴`, so
`U⁻³ ≤ ∏ₖ zₖ^{-3/4}`, which is integrable on the simplex.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.TwoLoop.UnitSCReduce

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.UnitSCGraph
open QED.TwoLoop.UnitLGraphReduce QED.TwoLoop.UnitXGraph QED.TwoLoop.Bridge
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrixPV symanzikV symanzikU
  simplexPoint_castSucc simplexPoint_last)

/-! ### The homogeneous polynomials -/

/-- The polynomial `H₁` with `H₁(S₀, S₁, T₀, T₁, U) = 512 W M₁` (`cpHom1_identity`). -/
def cH1 (s0 s1 t0 t1 u : ℝ) : ℝ :=
  -512 * s0 ^ 3 * s1 - 1024 * s0 ^ 2 * s1 ^ 2 + 512 * s0 ^ 2 * s1 * u - 512 * s0 ^ 2 * t0 * u +
  512 * s0 ^ 2 * t1 * u - 512 * s0 ^ 2 * u ^ 2 - 512 * s0 * s1 ^ 3 + 512 * s0 * s1 ^ 2 * u -
  1024 * s0 * s1 * t0 * u + 1024 * s0 * s1 * t1 * u + 1024 * s0 * t0 * u ^ 2 - 1024 * s0 * t1 *
  u ^ 2 - 512 * s1 ^ 2 * t0 * u + 512 * s1 ^ 2 * t1 * u + 512 * s1 ^ 2 * u ^ 2 + 1024 * s1 * t0
  * u ^ 2 - 1024 * s1 * t1 * u ^ 2

/-- The polynomial `H₂` with `H₂(S₀, S₁, T₀, T₁, U; ℓ) = -1024 M₂` (`cpHom2_identity`). -/
def cH2 (s0 s1 t0 t1 u l1 l2 l3 l4 : ℝ) : ℝ :=
  -1024 * s0 ^ 2 * l1 - 2048 * s0 ^ 2 * l2 - 2048 * s0 ^ 2 * l2 - 2048 * s0 * s1 * l1 - 2048 *
  s0 * s1 * l2 - 2048 * s0 * s1 * l2 - 1024 * s0 * s1 * l4 - 1024 * s0 * t1 * l3 + 1024 * s0 *
  t1 * l3 + 1024 * s0 * u * l1 + 1024 * s0 * u * l2 + 3072 * s0 * u * l2 - 2048 * s0 * u * l3 -
  1024 * s0 * u * l3 - 1024 * s0 * u * l4 - 1024 * s1 ^ 2 * l1 + 1024 * s1 * t0 * l3 - 1024 * s1
  * t0 * l3 + 1024 * s1 * u * l1 + 1024 * s1 * u * l2 - 2048 * s1 * u * l3 + 1024 * s1 * u * l4
  + 2048 * t0 * u * l2 + 1024 * t0 * u * l2 + 1024 * t0 * u * l3 + 1024 * t0 * u * l3 + 1024 *
  t0 * u * l4 + 2048 * t1 * u * l2 + 1024 * t1 * u * l3 + 2048 * t1 * u * l3 - 1024 * t1 * u *
  l4 - 1024 * u ^ 2 * l2 - 2048 * u ^ 2 * l2 + 1024 * u ^ 2 * l3 + 2048 * u ^ 2 * l3 - 1024 * u
  ^ 2 * l4

theorem cH1_eq (z : Fin 8 → ℝ) :
    cH1 (cpS0n z) (cpS1n z) (cpT0n z) (cpT1n z) (cpU z) = 512 * (cpW z * cpM1 z) := by
  rw [← mul_assoc, ← cpHom1_identity z]
  rfl

theorem cH2_eq (z : Fin 8 → ℝ) :
    cH2 (cpS0n z) (cpS1n z) (cpT0n z) (cpT1n z) (cpU z) (z 0 + z 1 + spza z) (-z 2)
      (z 3 + spzb z) (z 2 + z 3 + spzb z) = -1024 * cpM2 z := by
  rw [← cpHom2_identity z]
  rfl

theorem cH1_smul (s s0 s1 t0 t1 u : ℝ) :
    cH1 (s * s0) (s * s1) (s * t0) (s * t1) (s * u) = s ^ 4 * cH1 s0 s1 t0 t1 u := by
  simp only [cH1]; ring

theorem cH2_smul (s s0 s1 t0 t1 u l1 l2 l3 l4 : ℝ) :
    cH2 (s * s0) (s * s1) (s * t0) (s * t1) (s * u) l1 l2 l3 l4 =
      s ^ 2 * cH2 s0 s1 t0 t1 u l1 l2 l3 l4 := by
  simp only [cH2]; ring

theorem exists_bound_cH1 : ∃ C : ℝ, ∀ s0 s1 t0 t1 : ℝ,
    s0 ∈ Icc (-2 : ℝ) 2 → s1 ∈ Icc (-2 : ℝ) 2 → t0 ∈ Icc (-2 : ℝ) 2 → t1 ∈ Icc (-2 : ℝ) 2 →
    |cH1 s0 s1 t0 t1 1| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_cube2 4).exists_bound_of_continuousOn
    (f := fun v : Fin 4 → ℝ => cH1 (v 0) (v 1) (v 2) (v 3) 1) (by unfold cH1; fun_prop)
  refine ⟨C, fun s0 s1 t0 t1 h0 h1 h2 h3 => ?_⟩
  have hv : ![s0, s1, t0, t1] ∈ cube2 4 := by
    intro i _
    fin_cases i <;> simpa
  simpa [Real.norm_eq_abs] using hC _ hv

theorem exists_bound_cH2 : ∃ C : ℝ, ∀ s0 s1 t0 t1 l1 l2 l3 l4 : ℝ,
    s0 ∈ Icc (-2 : ℝ) 2 → s1 ∈ Icc (-2 : ℝ) 2 → t0 ∈ Icc (-2 : ℝ) 2 → t1 ∈ Icc (-2 : ℝ) 2 →
    l1 ∈ Icc (-2 : ℝ) 2 → l2 ∈ Icc (-2 : ℝ) 2 → l3 ∈ Icc (-2 : ℝ) 2 → l4 ∈ Icc (-2 : ℝ) 2 →
    |cH2 s0 s1 t0 t1 1 l1 l2 l3 l4| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_cube2 8).exists_bound_of_continuousOn
    (f := fun v : Fin 8 → ℝ => cH2 (v 0) (v 1) (v 2) (v 3) 1 (v 4) (v 5) (v 6) (v 7))
    (by unfold cH2; fun_prop)
  refine ⟨C, fun s0 s1 t0 t1 l1 l2 l3 l4 h0 h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  have hv : ![s0, s1, t0, t1, l1, l2, l3, l4] ∈ cube2 8 := by
    intro i _
    fin_cases i <;> simpa
  simpa [Real.norm_eq_abs] using hC _ hv

/-! ### Bounds on the slot data -/

section Slots

variable {z : Fin 8 → ℝ}

theorem cpU_pos (hz : ∀ i, 0 < z i) : 0 < cpU z := by
  have := hz 0; have := hz 1; have := hz 2; have := hz 3
  have := hz 4; have := hz 5; have := hz 6; have := hz 7
  rw [cpU_eq_gCU]
  unfold gCU spza spzb
  nlinarith [mul_pos (hz 2) (hz 3), mul_pos (hz 0) (hz 3), mul_pos (hz 2) (hz 5)]

theorem cpU_expand (z : Fin 8 → ℝ) :
    cpU z = (z 0 + z 1 + spza z) * (z 2 + z 3 + spzb z) + z 2 * (z 3 + spzb z) := by
  unfold cpU; ring

theorem abs_cpS0n_le (hz : ∀ i, 0 < z i) : |cpS0n z| ≤ 2 * cpU z := by
  have h0 := (hz 0).le; have h1 := (hz 1).le; have h2 := (hz 2).le; have h3 := (hz 3).le
  have h4 := (hz 4).le; have h5 := (hz 5).le; have h6 := (hz 6).le; have h7 := (hz 7).le
  rw [abs_le, cpU_expand]
  unfold cpS0n spza spzb
  constructor <;> nlinarith [mul_nonneg h0 h2, mul_nonneg h0 h3, mul_nonneg h0 h5, mul_nonneg h0 h7,
    mul_nonneg h1 h2, mul_nonneg h1 h3, mul_nonneg h1 h5, mul_nonneg h1 h7, mul_nonneg h4 h2,
    mul_nonneg h4 h3, mul_nonneg h4 h5, mul_nonneg h4 h7, mul_nonneg h6 h2, mul_nonneg h6 h3,
    mul_nonneg h6 h5, mul_nonneg h6 h7, mul_nonneg h2 h3, mul_nonneg h2 h5, mul_nonneg h2 h7]

theorem abs_cpS1n_le (hz : ∀ i, 0 < z i) : |cpS1n z| ≤ 2 * cpU z := by
  have h0 := (hz 0).le; have h1 := (hz 1).le; have h2 := (hz 2).le; have h3 := (hz 3).le
  have h4 := (hz 4).le; have h5 := (hz 5).le; have h6 := (hz 6).le; have h7 := (hz 7).le
  rw [abs_le, cpU_expand]
  unfold cpS1n spza spzb
  constructor <;> nlinarith [mul_nonneg h0 h2, mul_nonneg h0 h3, mul_nonneg h0 h5, mul_nonneg h0 h7,
    mul_nonneg h1 h2, mul_nonneg h1 h3, mul_nonneg h1 h5, mul_nonneg h1 h7, mul_nonneg h4 h2,
    mul_nonneg h4 h3, mul_nonneg h4 h5, mul_nonneg h4 h7, mul_nonneg h6 h2, mul_nonneg h6 h3,
    mul_nonneg h6 h5, mul_nonneg h6 h7, mul_nonneg h2 h3, mul_nonneg h2 h5, mul_nonneg h2 h7]

theorem abs_cpT0n_le (hz : ∀ i, 0 < z i) : |cpT0n z| ≤ 2 * cpU z := by
  have h0 := (hz 0).le; have h1 := (hz 1).le; have h2 := (hz 2).le; have h3 := (hz 3).le
  have h4 := (hz 4).le; have h5 := (hz 5).le; have h6 := (hz 6).le; have h7 := (hz 7).le
  rw [abs_le, cpU_expand]
  unfold cpT0n spza spzb
  constructor <;> nlinarith [mul_nonneg h0 h2, mul_nonneg h0 h3, mul_nonneg h0 h5, mul_nonneg h0 h7,
    mul_nonneg h1 h2, mul_nonneg h1 h3, mul_nonneg h1 h5, mul_nonneg h1 h7, mul_nonneg h4 h2,
    mul_nonneg h4 h3, mul_nonneg h4 h5, mul_nonneg h4 h7, mul_nonneg h6 h2, mul_nonneg h6 h3,
    mul_nonneg h6 h5, mul_nonneg h6 h7, mul_nonneg h2 h3, mul_nonneg h2 h5, mul_nonneg h2 h7]

theorem abs_cpT1n_le (hz : ∀ i, 0 < z i) : |cpT1n z| ≤ 2 * cpU z := by
  have h0 := (hz 0).le; have h1 := (hz 1).le; have h2 := (hz 2).le; have h3 := (hz 3).le
  have h4 := (hz 4).le; have h5 := (hz 5).le; have h6 := (hz 6).le; have h7 := (hz 7).le
  rw [abs_le, cpU_expand]
  unfold cpT1n spza spzb
  constructor <;> nlinarith [mul_nonneg h0 h2, mul_nonneg h0 h3, mul_nonneg h0 h5, mul_nonneg h0 h7,
    mul_nonneg h1 h2, mul_nonneg h1 h3, mul_nonneg h1 h5, mul_nonneg h1 h7, mul_nonneg h4 h2,
    mul_nonneg h4 h3, mul_nonneg h4 h5, mul_nonneg h4 h7, mul_nonneg h6 h2, mul_nonneg h6 h3,
    mul_nonneg h6 h5, mul_nonneg h6 h7, mul_nonneg h2 h3, mul_nonneg h2 h5, mul_nonneg h2 h7]

theorem cpU_le_one (hz : ∀ i, 0 < z i) (hz1 : ∑ i, z i = 1) : cpU z ≤ 1 := by
  rw [Fin.sum_univ_eight] at hz1
  have h0 := (hz 0).le; have h1 := (hz 1).le; have h2 := (hz 2).le; have h3 := (hz 3).le
  have h4 := (hz 4).le; have h5 := (hz 5).le; have h6 := (hz 6).le; have h7 := (hz 7).le
  have hsq : cpU z ≤ (z 0 + z 1 + z 2 + z 3 + z 4 + z 5 + z 6 + z 7) ^ 2 := by
    rw [cpU_expand]
    unfold spza spzb
    nlinarith [sq_nonneg (z 0 + z 1 + z 4 + z 6), sq_nonneg (z 2 + z 3 + z 5 + z 7),
      mul_nonneg h2 h3, mul_nonneg h2 h5, mul_nonneg h2 h7, mul_nonneg h3 h5, mul_nonneg h3 h7]
  rw [hz1, one_pow] at hsq
  exact hsq

theorem abs_le_two_of_sum (hz : ∀ i, 0 < z i) (hz1 : ∑ i, z i = 1) :
    z 0 + z 1 + spza z ∈ Icc (-2 : ℝ) 2 ∧ -z 2 ∈ Icc (-2 : ℝ) 2 ∧
      z 3 + spzb z ∈ Icc (-2 : ℝ) 2 ∧ z 2 + z 3 + spzb z ∈ Icc (-2 : ℝ) 2 := by
  rw [Fin.sum_univ_eight] at hz1
  have h0 := (hz 0).le; have h1 := (hz 1).le; have h2 := (hz 2).le; have h3 := (hz 3).le
  have h4 := (hz 4).le; have h5 := (hz 5).le; have h6 := (hz 6).le; have h7 := (hz 7).le
  unfold spza spzb
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

end Slots

theorem abs_cpWM1_le {C : ℝ} (hC : ∀ s0 s1 t0 t1 : ℝ,
      s0 ∈ Icc (-2 : ℝ) 2 → s1 ∈ Icc (-2 : ℝ) 2 → t0 ∈ Icc (-2 : ℝ) 2 → t1 ∈ Icc (-2 : ℝ) 2 →
      |cH1 s0 s1 t0 t1 1| ≤ C)
    {z : Fin 8 → ℝ} (hz : ∀ i, 0 < z i) : |cpW z * cpM1 z| ≤ C / 512 * cpU z ^ 4 := by
  have hU := cpU_pos hz
  have hb := hC _ _ _ _ (mem_Icc_div_of_abs_le hU (abs_cpS0n_le hz))
    (mem_Icc_div_of_abs_le hU (abs_cpS1n_le hz)) (mem_Icc_div_of_abs_le hU (abs_cpT0n_le hz))
    (mem_Icc_div_of_abs_le hU (abs_cpT1n_le hz))
  have hc : ∀ x, cpU z * (x / cpU z) = x := fun x => by field_simp
  have e := cH1_smul (cpU z) (cpS0n z / cpU z) (cpS1n z / cpU z) (cpT0n z / cpU z)
    (cpT1n z / cpU z) 1
  simp only [hc, mul_one, cH1_eq] at e
  have e' : cpW z * cpM1 z = cpU z ^ 4 * cH1 (cpS0n z / cpU z) (cpS1n z / cpU z)
      (cpT0n z / cpU z) (cpT1n z / cpU z) 1 / 512 := by linarith
  rw [e', abs_div, abs_mul, abs_of_pos (by positivity : 0 < cpU z ^ 4),
    abs_of_pos (by norm_num : (0 : ℝ) < 512)]
  have := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ cpU z ^ 4)
  linarith

theorem abs_cpM2_le {C : ℝ} (hC : ∀ s0 s1 t0 t1 l1 l2 l3 l4 : ℝ,
      s0 ∈ Icc (-2 : ℝ) 2 → s1 ∈ Icc (-2 : ℝ) 2 → t0 ∈ Icc (-2 : ℝ) 2 → t1 ∈ Icc (-2 : ℝ) 2 →
      l1 ∈ Icc (-2 : ℝ) 2 → l2 ∈ Icc (-2 : ℝ) 2 → l3 ∈ Icc (-2 : ℝ) 2 → l4 ∈ Icc (-2 : ℝ) 2 →
      |cH2 s0 s1 t0 t1 1 l1 l2 l3 l4| ≤ C)
    {z : Fin 8 → ℝ} (hz : ∀ i, 0 < z i) (hz1 : ∑ i, z i = 1) :
    |cpM2 z| ≤ C / 1024 * cpU z ^ 2 := by
  have hU := cpU_pos hz
  obtain ⟨l1, l2, l3, l4⟩ := abs_le_two_of_sum hz hz1
  have hb := hC _ _ _ _ _ _ _ _ (mem_Icc_div_of_abs_le hU (abs_cpS0n_le hz))
    (mem_Icc_div_of_abs_le hU (abs_cpS1n_le hz)) (mem_Icc_div_of_abs_le hU (abs_cpT0n_le hz))
    (mem_Icc_div_of_abs_le hU (abs_cpT1n_le hz)) l1 l2 l3 l4
  have hc : ∀ x, cpU z * (x / cpU z) = x := fun x => by field_simp
  have e := cH2_smul (cpU z) (cpS0n z / cpU z) (cpS1n z / cpU z) (cpT0n z / cpU z)
    (cpT1n z / cpU z) 1 (z 0 + z 1 + spza z) (-z 2) (z 3 + spzb z) (z 2 + z 3 + spzb z)
  simp only [hc, mul_one, cH2_eq] at e
  have e' : cpM2 z = -(cpU z ^ 2 * cH2 (cpS0n z / cpU z) (cpS1n z / cpU z)
      (cpT0n z / cpU z) (cpT1n z / cpU z) 1 (z 0 + z 1 + spza z) (-z 2) (z 3 + spzb z)
      (z 2 + z 3 + spzb z)) / 1024 := by linarith
  rw [e', abs_div, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < cpU z ^ 2),
    abs_of_pos (by norm_num : (0 : ℝ) < 1024)]
  have := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ cpU z ^ 2)
  linarith

/-! ### The pointwise bound -/

/-- **The pointwise bound** `|cornerG| ≤ (3C₁/v₀⁴ + C₂/v₀³)/U³` on the open simplex. -/
theorem abs_cornerGz_le {C₁ C₂ v₀ W M1 M2 U V : ℝ} (hv₀ : 0 < v₀) (hU : 0 < U) (hU1 : U ≤ 1)
    (h₁ : |W * M1| ≤ C₁ * U ^ 4) (h₂ : |M2| ≤ C₂ * U ^ 2) (hV : v₀ ≤ V) :
    |cornerGz W M1 M2 U V| ≤ (3 * C₁ / v₀ ^ 4 + C₂ / v₀ ^ 3) / U ^ 3 := by
  have hV0 : 0 < V := hv₀.trans_le hV
  have hC₁ : 0 ≤ C₁ := by
    have := (abs_nonneg _).trans h₁
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have hC₂ : 0 ≤ C₂ := by
    have := (abs_nonneg _).trans h₂
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have e1 : |3 * W * M1 / (U ^ 6 * V ^ 4)| ≤ 3 * C₁ / v₀ ^ 4 / U ^ 3 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < U ^ 6 * V ^ 4), mul_assoc, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    calc 3 * |W * M1| / (U ^ 6 * V ^ 4) ≤ 3 * (C₁ * U ^ 4) / (U ^ 6 * v₀ ^ 4) := by
          refine div_le_div₀ (by positivity) (by linarith) (by positivity) ?_
          gcongr
      _ = 3 * C₁ / v₀ ^ 4 / U ^ 2 := by field_simp
      _ ≤ 3 * C₁ / v₀ ^ 4 / U ^ 3 := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          calc U ^ 3 = U ^ 2 * U := by ring
            _ ≤ U ^ 2 * 1 := by gcongr
            _ = U ^ 2 := mul_one _
  have e2 : |M2 / (U ^ 5 * V ^ 3)| ≤ C₂ / v₀ ^ 3 / U ^ 3 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < U ^ 5 * V ^ 3)]
    calc |M2| / (U ^ 5 * V ^ 3) ≤ C₂ * U ^ 2 / (U ^ 5 * v₀ ^ 3) := by
          refine div_le_div₀ (by positivity) h₂ (by positivity) ?_
          gcongr
      _ = C₂ / v₀ ^ 3 / U ^ 3 := by field_simp
  unfold cornerGz
  calc _ ≤ _ := abs_sub _ _
    _ ≤ 3 * C₁ / v₀ ^ 4 / U ^ 3 + C₂ / v₀ ^ 3 / U ^ 3 := add_le_add e1 e2
    _ = (3 * C₁ / v₀ ^ 4 + C₂ / v₀ ^ 3) / U ^ 3 := by ring

/-! ### The product of the coordinates -/

theorem prod_le_cpU_pow_four {z : Fin 8 → ℝ} (hz : ∀ i, 0 ≤ z i) : ∏ i, z i ≤ cpU z ^ 4 := by
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2; have h3 := hz 3
  have h4 := hz 4; have h5 := hz 5; have h6 := hz 6; have h7 := hz 7
  set o := z 0 + z 1
  have ho : 0 ≤ o := by positivity
  have ha : 0 ≤ spza z := by unfold spza; positivity
  have hb : 0 ≤ spzb z := by unfold spzb; positivity
  have h01 : z 0 * z 1 ≤ o ^ 2 := by simp only [o]; nlinarith
  have h46 : z 4 * z 6 ≤ spza z ^ 2 := by unfold spza; nlinarith
  have h57 : z 5 * z 7 ≤ spzb z ^ 2 := by unfold spzb; nlinarith
  have hU : cpU z = (o + spza z) * (z 2 + z 3 + spzb z) + z 2 * (z 3 + spzb z) := cpU_expand z
  have m1 : o * z 2 ≤ cpU z := by
    rw [hU]; nlinarith [mul_nonneg ho h3, mul_nonneg ho hb,
      mul_nonneg ha h2, mul_nonneg ha h3, mul_nonneg ha hb, mul_nonneg h2 h3, mul_nonneg h2 hb]
  have m2 : o * spzb z ≤ cpU z := by
    rw [hU]; nlinarith [mul_nonneg ho h3, mul_nonneg ho h2,
      mul_nonneg ha h2, mul_nonneg ha h3, mul_nonneg ha hb, mul_nonneg h2 h3, mul_nonneg h2 hb]
  have m3 : spza z * z 3 ≤ cpU z := by
    rw [hU]; nlinarith [mul_nonneg ho h3, mul_nonneg ho h2,
      mul_nonneg ho hb, mul_nonneg ha h2, mul_nonneg ha hb, mul_nonneg h2 h3, mul_nonneg h2 hb]
  have m4 : spza z * spzb z ≤ cpU z := by
    rw [hU]; nlinarith [mul_nonneg ho h3, mul_nonneg ho h2,
      mul_nonneg ho hb, mul_nonneg ha h2, mul_nonneg ha h3, mul_nonneg h2 h3, mul_nonneg h2 hb]
  rw [Fin.prod_univ_eight]
  calc z 0 * z 1 * z 2 * z 3 * z 4 * z 5 * z 6 * z 7 =
        (z 0 * z 1) * z 2 * z 3 * (z 4 * z 6) * (z 5 * z 7) := by ring
    _ ≤ o ^ 2 * z 2 * z 3 * spza z ^ 2 * spzb z ^ 2 := by gcongr
    _ = (o * z 2) * (o * spzb z) * (spza z * z 3) * (spza z * spzb z) := by ring
    _ ≤ cpU z * cpU z * cpU z * cpU z := by
        have := mul_nonneg ho h2; have := mul_nonneg ho hb; have := mul_nonneg ha h3
        have := mul_nonneg ha hb
        have hU0 : 0 ≤ cpU z := le_trans (mul_nonneg ho h2) m1
        gcongr
    _ = cpU z ^ 4 := by ring

theorem inv_cpU_pow_three_le_prod_rpow {z : Fin 8 → ℝ} (hz : ∀ i, 0 < z i) :
    (cpU z ^ 3)⁻¹ ≤ ∏ i, z i ^ (-(3 / 4 : ℝ)) := by
  have hz' : ∀ i, 0 ≤ z i := fun i => (hz i).le
  have hP : 0 < ∏ i, z i := Finset.prod_pos fun i _ => hz i
  have hle := prod_le_cpU_pow_four hz'
  have hU : 0 < cpU z := cpU_pos hz
  rw [Real.finsetProd_rpow _ _ (fun i _ => hz' i)]
  calc (cpU z ^ 3)⁻¹ = (cpU z ^ 4) ^ (-(3 / 4 : ℝ)) := by
        rw [← Real.rpow_natCast (cpU z) 4, ← Real.rpow_mul hU.le]
        norm_num
    _ ≤ (∏ i, z i) ^ (-(3 / 4 : ℝ)) := Real.rpow_le_rpow_of_nonpos hP hle (by norm_num)

/-! ### Integrability -/

theorem measurable_cornerG (P : Params) : Measurable (cornerG P) := by
  unfold cornerG cornerGz cornerV gCE gCEn gCU cpW cpM1 cpM2 cpM1pa cpM1pb cpM1pc cpM1pd cpM2pa
    cpM2pb cpM2pc cpM2pd cpU spza spzb
  fun_prop

/-- The lower bound `V ≥ (3/4) min(1/4, m_γ²)` on the simplex (`C₊`). -/
theorem le_cornerV {P : Params} (hm : P.m = 1) (hΛ : P.mγ ^ 2 ≤ P.Λ ^ 2) {z : Fin 8 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : cpU z ≠ 0) :
    3 / 4 * min (1 / 4) (P.mγ ^ 2) ≤ cornerV P (z 0 + z 1) (z 2) (z 3) (spza z) (spzb z) z := by
  have h := QED.Integration.TwoLoop.symanzikV_classCpPV_ge (mass := 1) (mγ := P.mγ)
    (lam₁ := P.mγ) (lam₂ := P.mγ) (lam₃ := P.Λ) (lam₄ := P.Λ)
    (p := restMomentum 1) (p' := restMomentum 1) (by rw [dot_restMomentum])
    (by rw [dot_restMomentum]) (by simp [QED.Minkowski.dot_eq]) le_rfl le_rfl hΛ hΛ hz hz1
    (by rw [← symanzikU_Cp] at hU; exact hU)
  rw [← symanzikV_Cp P hm hU]
  convert h using 2
  · norm_num
  · funext i
    rw [hm]
    rfl
  · simp [pvMasses, hm]

/-- **The `C₊` integrand is integrable on the simplex** (`m = 1`, `0 < m_γ ≤ Λ`). -/
theorem integrableOn_cornerG {P : Params} (hm : P.m = 1) (hmγ : 0 < P.mγ) (hΛ : P.mγ ≤ P.Λ) :
    IntegrableOn (fun x => cornerG P (simplexPoint x)) (simplexSet 7) := by
  obtain ⟨C₁, hC₁⟩ := exists_bound_cH1
  obtain ⟨C₂, hC₂⟩ := exists_bound_cH2
  set v₀ : ℝ := 3 / 4 * min (1 / 4) (P.mγ ^ 2)
  have hv₀ : 0 < v₀ := by positivity
  have hΛ2 : P.mγ ^ 2 ≤ P.Λ ^ 2 := pow_le_pow_left₀ hmγ.le hΛ 2
  set C : ℝ := 3 * (C₁ / 512) / v₀ ^ 4 + C₂ / 1024 / v₀ ^ 3
  have hint : IntegrableOn (fun x => C * ∏ i ∈ Finset.univ, simplexPoint x i ^ (-(3 / 4 : ℝ)))
      (simplexSet 7) :=
    (QED.Integration.TwoLoop.integrableOn_prod_simplexPoint_rpow Finset.univ (by norm_num)
      (by norm_num)).const_mul C
  refine hint.mono' ((measurable_cornerG P).comp
    QED.Integration.TwoLoop.continuous_simplexPoint'.measurable).aestronglyMeasurable ?_
  filter_upwards [ae_mem_openSimplex (by norm_num : 0 < 7)] with x hx
  set z := simplexPoint x
  have hzpos := simplexPoint_pos_of_mem_openSimplex hx
  have hz1 : ∑ i, z i = 1 := by
    simp only [z, Fin.sum_univ_castSucc, simplexPoint_castSucc, simplexPoint_last]; ring
  have hU : 0 < cpU z := cpU_pos hzpos
  have hV := le_cornerV hm hΛ2 (fun i => (hzpos i).le) hz1 hU.ne'
  have hb := abs_cornerGz_le hv₀ hU (cpU_le_one hzpos hz1) (abs_cpWM1_le hC₁ hzpos)
    (abs_cpM2_le hC₂ hzpos hz1) hV
  rw [Real.norm_eq_abs]
  refine hb.trans ?_
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans hb
    have hU3 : 0 < (cpU z ^ 3)⁻¹ := by positivity
    rw [div_eq_mul_inv] at this
    exact nonneg_of_mul_nonneg_left this hU3
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_cpU_pow_three_le_prod_rpow hzpos) hC

end QED.TwoLoop.UnitSCReduce

end
