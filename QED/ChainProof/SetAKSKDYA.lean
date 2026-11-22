/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKDRed
public import QED.GradedProof.RPi4Join
public import QED.Integration.SimplexMerge

/-!
# Set (a), stage D: the inner `y`-integral of the `VA` outer integrand

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification). The reduced outer `VA` integrand `ksDGA` (stage D,
`SetAKSKDRed`) is integrated over its outer Feynman simplex `Δ₂` in closed form, leaving the
inner parameter `x` and the outer fraction `σ = y₁`. On the simplex the denominator is affine
in the merged-line parameter `r = y₀`:
`D = A(σ) + b (1 - σ - r)`, `A(σ) = M² + σ(1 - σ)s` (the one-loop denominator), and
`b = M²/(1 - x) + u/x - M²`; the photon mass² enters only through `b`.

Main results:

* `ksD_integral_simplexTwo`: `∫_{Δ₂} g = ∫₀¹ ∫₀^{1-t} g(r, t) dr dt`;
* `ksD_integral_lin`: `∫₀^Y r (a₀/(A + b(Y - r))² + 2a₁/(A + b(Y - r))) dr = ksDLin A b Y a₀ a₁`,
  with `L = log((A + bY)/A)`, `ksDLin = a₀ (Y/(bA) - L/b²) + 2a₁ ((A + bY)L - bY)/b²`;
* **`ksD_integral_ksDGA`**: `∫_{Δ₂} ksDGA M u x s = ∫₀¹ ksDYA M u x s σ dσ` for `M > 0`,
  `s > -4M²`, `x ∈ (0, 1)`, `u > 0`;
* **`ksD_ksDNestA`**: the nested `VA` integral with the inner simplex integrated out, flavour sum
  inside the `σ`-integral.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral
open scoped Real

namespace QED.ChainProof.SetAKS

open QED.Integration.Feynman (simplexSet simplexPoint isCompact_simplexSet
  measurableSet_simplexSet)
open QED.GradedProof.RPi4

/-! ### Iterated integrals over `Δ₁` and `Δ₂` -/

theorem ksD_simplexOne :
    simplexSet 1 = (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Icc (0 : ℝ) 1 := by
  ext x
  rw [QED.Integration.SimplexMerge.mem_simplexSet_iff_le one_pos]
  simp [MeasurableEquiv.funUnique]

theorem ksD_integral_simplexOne (h : ℝ → ℝ) :
    ∫ x in simplexSet 1, h (x 0) = ∫ t in (0 : ℝ)..1, h t := by
  rw [ksD_simplexOne, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact (volume_preserving_funUnique (Fin 1) ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding h _

theorem ksD_snoc_smul (t : ℝ) (y : Fin 1 → ℝ) :
    (Fin.snoc ((1 - t) • y) t : Fin 2 → ℝ) = ![(1 - t) * y 0, t] := by
  ext i
  fin_cases i <;> simp [Fin.snoc]

/-- **`Δ₂` as an iterated integral**: `∫_{Δ₂} g = ∫₀¹ ∫₀^{1-t} g(r, t) dr dt`. -/
theorem ksD_integral_simplexTwo {g : (Fin 2 → ℝ) → ℝ} (hg : IntegrableOn g (simplexSet 2)) :
    ∫ y in simplexSet 2, g y = ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..(1 - t), g ![r, t] := by
  rw [integral_simplex_peel hg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [ksD_snoc_smul, pow_one, smul_eq_mul]
  rw [ksD_integral_simplexOne (fun r => g ![(1 - t) * r, t])]
  rcases eq_or_ne (1 - t) 0 with h | h
  · rw [h]
    simp
  · rw [intervalIntegral.integral_comp_mul_left (fun r => g ![r, t]) h, smul_eq_mul, mul_zero,
      mul_one, ← mul_assoc, mul_inv_cancel₀ h, one_mul]

/-! ### The elementary integral -/

/-- The closed form of `∫₀^Y r (a₀/(A + b(Y - r))² + 2a₁/(A + b(Y - r))) dr`. -/
noncomputable def ksDLin (A b Y a₀ a₁ : ℝ) : ℝ :=
  a₀ * (Y / (b * A) - Real.log ((A + b * Y) / A) / b ^ 2) +
    2 * a₁ * (((A + b * Y) * Real.log ((A + b * Y) / A) - b * Y) / b ^ 2)

/-- The integrand of `ksDLin`. -/
noncomputable def ksDLinI (A b Y a₀ a₁ r : ℝ) : ℝ :=
  r * (a₀ / (A + b * (Y - r)) ^ 2 + 2 * a₁ / (A + b * (Y - r)))

theorem ksD_den_pos {A b Y r : ℝ} (hA : 0 < A) (hb : 0 < b) (hr : r ≤ Y) :
    0 < A + b * (Y - r) := by
  have : 0 ≤ b * (Y - r) := mul_nonneg hb.le (by linarith)
  linarith

/-- **The elementary integral** of the `VA` integrand along the merged line. -/
theorem ksD_integral_lin {A b Y : ℝ} (a₀ a₁ : ℝ) (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y) :
    ∫ r in (0 : ℝ)..Y, ksDLinI A b Y a₀ a₁ r = ksDLin A b Y a₀ a₁ := by
  set P := A + b * Y with hP
  have hpos : ∀ r ∈ uIcc (0 : ℝ) Y, 0 < A + b * (Y - r) := fun r hr => by
    rw [uIcc_of_le hY] at hr
    exact ksD_den_pos hA hb hr.2
  set F : ℝ → ℝ := fun r => a₀ / b ^ 2 * (P / (A + b * (Y - r)) + Real.log (A + b * (Y - r))) +
    2 * a₁ * (-r / b - P / b ^ 2 * Real.log (A + b * (Y - r))) with hF
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) Y, HasDerivAt F (ksDLinI A b Y a₀ a₁ r) r := by
    intro r hr
    have h0 := (hpos r hr).ne'
    have hL : HasDerivAt (fun r => A + b * (Y - r)) (-b) r := by
      have := ((hasDerivAt_id r).const_sub Y).const_mul b |>.const_add A
      simpa using this
    have h1 := (hasDerivAt_const r P).div hL h0
    have h2 := hL.log h0
    have h3 := (hasDerivAt_id r).neg.div_const b
    have hb0 := hb.ne'
    have hF' := ((h1.add h2).const_mul (a₀ / b ^ 2)).add
      ((h3.sub (h2.const_mul (P / b ^ 2))).const_mul (2 * a₁))
    refine HasDerivAt.congr_deriv (f := F) hF' ?_
    simp only [ksDLinI, hP]
    field_simp
    ring
  have hcont : ContinuousOn (ksDLinI A b Y a₀ a₁) (uIcc (0 : ℝ) Y) := by
    show ContinuousOn (fun r => ksDLinI A b Y a₀ a₁ r) (uIcc (0 : ℝ) Y)
    simp only [ksDLinI]
    refine continuousOn_id.mul (ContinuousOn.add ?_ ?_)
    · exact continuousOn_const.div (by fun_prop) fun r hr => pow_ne_zero 2 (hpos r hr).ne'
    · exact continuousOn_const.div (by fun_prop) fun r hr => (hpos r hr).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hPA : 0 < P := by have := mul_nonneg hb.le hY; rw [hP]; linarith
  simp only [hF, ksDLin, sub_zero, sub_self, mul_zero, add_zero, ← hP]
  rw [Real.log_div hPA.ne' hA.ne']
  field_simp
  ring

/-! ### The `VA` integrand on the simplex -/

/-- The one-loop denominator `A(σ) = M² + σ(1 - σ)s`. -/
def ksDA (M s σ : ℝ) : ℝ := M ^ 2 + σ * (1 - σ) * s

/-- The slope `b = M²/(1 - x) + u/x - M²` of the `VA` denominator in the inner-line parameter. -/
noncomputable def ksDb (M u x : ℝ) : ℝ := M ^ 2 / (1 - x) + u / x - M ^ 2

/-- The moment `a₀` of the `VA` integrand. -/
def ksDa0 (M x s σ : ℝ) : ℝ := 16 * σ * (1 - σ) * (4 * M ^ 2 - (1 - x) * M ^ 2 +
  (1 - x) * σ ^ 2 * s)

/-- The moment `a₁` of the `VA` integrand. -/
def ksDa1 (x σ : ℝ) : ℝ := -8 * (1 - x) * σ * (4 * σ - 3)

/-- **The `VA` integrand after the inner `y`-integral**, at the outer fraction `σ`. -/
noncomputable def ksDYA (M u x s σ : ℝ) : ℝ :=
  ksDLin (ksDA M s σ) (ksDb M u x) (1 - σ) (ksDa0 M x s σ) (ksDa1 x σ)

theorem ksD_simplexPoint_two (r t : ℝ) :
    simplexPoint ![r, t] = ![r, t, 1 - (r + t)] := by
  rw [QED.Integration.TwoLoop.simplexPoint_eq_snoc]
  ext i
  fin_cases i <;> simp [Fin.snoc, Fin.sum_univ_two]

theorem ksD_ksDGA_pt (M u x s r t : ℝ) :
    ksDGA M u x s (simplexPoint ![r, t]) =
      ksDLinI (ksDA M s t) (ksDb M u x) (1 - t) (ksDa0 M x s t) (ksDa1 x t) r := by
  rw [ksD_simplexPoint_two]
  simp only [ksDGA, ksDLinI, ksDA, ksDb, ksDa0, ksDa1, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hS : r + t + (1 - (r + t)) = 1 := by ring
  have hD : t * (r + (1 - (r + t))) * s / (r + t + (1 - (r + t))) + (r + t) * M ^ 2 +
      (1 - (r + t)) * (M ^ 2 / (1 - x) + u / x) =
      M ^ 2 + t * (1 - t) * s + (M ^ 2 / (1 - x) + u / x - M ^ 2) * (1 - t - r) := by
    rw [hS]; ring
  rw [hD, hS]
  ring

theorem ksD_ksDA_pos {M s σ : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    0 < ksDA M s σ := by
  obtain ⟨h0, h1⟩ := hσ
  have hq : 0 ≤ σ * (1 - σ) := mul_nonneg h0 (by linarith)
  have hq4 : σ * (1 - σ) ≤ 1 / 4 := by nlinarith [sq_nonneg (σ - 1 / 2)]
  have hM2 : 0 < M ^ 2 := by positivity
  simp only [ksDA]
  rcases le_or_gt 0 s with hs0 | hs0
  · nlinarith [mul_nonneg hq hs0]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 4 - σ * (1 - σ)) (by linarith : 0 ≤ -s)]

theorem ksD_ksDb_pos {M u x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) : 0 < ksDb M u x := by
  obtain ⟨h0, h1⟩ := hx
  have h1x : 0 < 1 - x := by linarith
  have h : M ^ 2 / (1 - x) - M ^ 2 = M ^ 2 * x / (1 - x) := by field_simp; ring
  have h2 : 0 ≤ M ^ 2 * x / (1 - x) := by positivity
  have h3 : 0 < u / x := div_pos hu h0
  simp only [ksDb]
  linarith

/-- On `Δ₂`, the `VA` integrand is the elementary integrand at `r = y₀`, `σ = y₁`. -/
theorem ksD_ksDGA_eq (M u x s : ℝ) (y : Fin 2 → ℝ) :
    ksDGA M u x s (simplexPoint y) =
      ksDLinI (ksDA M s (y 1)) (ksDb M u x) (1 - y 1) (ksDa0 M x s (y 1)) (ksDa1 x (y 1))
        (y 0) := by
  have hy : y = ![y 0, y 1] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [hy]
  exact ksD_ksDGA_pt M u x s (y 0) (y 1)

theorem ksD_integrableOn_ksDGA {M u x s : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    IntegrableOn (fun y => ksDGA M u x s (simplexPoint y)) (simplexSet 2) := by
  have hb := ksD_ksDb_pos (M := M) hx hu
  simp only [ksD_ksDGA_eq]
  refine ContinuousOn.integrableOn_compact (isCompact_simplexSet 2) ?_
  intro y hy
  rw [QED.Integration.SimplexMerge.mem_simplexSet_iff_le (by norm_num)] at hy
  obtain ⟨hy0, hy1⟩ := hy
  rw [Fin.sum_univ_two] at hy1
  have hσ : y 1 ∈ Icc (0 : ℝ) 1 := ⟨hy0 1, by linarith [hy0 0]⟩
  have hA := ksD_ksDA_pos hM hs hσ
  have hD : 0 < ksDA M s (y 1) + ksDb M u x * (1 - y 1 - y 0) :=
    ksD_den_pos hA hb (by linarith)
  refine ContinuousAt.continuousWithinAt ?_
  have c0 : Continuous fun y : Fin 2 → ℝ => y 0 := continuous_apply 0
  have c1 : Continuous fun y : Fin 2 → ℝ => y 1 := continuous_apply 1
  have cD : Continuous fun y : Fin 2 → ℝ =>
      ksDA M s (y 1) + ksDb M u x * (1 - y 1 - y 0) := by
    simp only [ksDA]; fun_prop
  have ca0 : Continuous fun y : Fin 2 → ℝ => ksDa0 M x s (y 1) := by
    simp only [ksDa0]; fun_prop
  have ca1 : Continuous fun y : Fin 2 → ℝ => ksDa1 x (y 1) := by
    simp only [ksDa1]; fun_prop
  simp only [ksDLinI]
  refine c0.continuousAt.mul ((ca0.continuousAt.div (cD.continuousAt.pow 2)
    (pow_ne_zero 2 hD.ne')).add ((continuousAt_const.mul ca1.continuousAt).div cD.continuousAt
      hD.ne'))

/-- **The inner `y`-integral of `VA`** in closed form. -/
theorem ksD_integral_ksDGA {M u x s : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    ∫ y in simplexSet 2, ksDGA M u x s (simplexPoint y) =
      ∫ σ in (0 : ℝ)..1, ksDYA M u x s σ := by
  rw [ksD_integral_simplexTwo (ksD_integrableOn_ksDGA hM hs hx hu)]
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  rw [uIcc_of_le zero_le_one] at hσ
  simp only [ksD_ksDGA_pt, ksDYA]
  exact ksD_integral_lin _ _ (ksD_ksDA_pos hM hs hσ) (ksD_ksDb_pos hx hu) (by linarith [hσ.2])

theorem ksD_continuousOn_ksDYA {M u x s : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    ContinuousOn (ksDYA M u x s) (Icc 0 1) := by
  have hb := ksD_ksDb_pos (M := M) hx hu
  intro σ hσ
  have hA := ksD_ksDA_pos hM hs hσ
  have hP : 0 < ksDA M s σ + ksDb M u x * (1 - σ) := by
    have := mul_nonneg hb.le (by linarith [hσ.2] : (0 : ℝ) ≤ 1 - σ)
    linarith
  refine ContinuousAt.continuousWithinAt ?_
  have cA : Continuous (ksDA M s) := by unfold ksDA; fun_prop
  have cP : Continuous fun σ => ksDA M s σ + ksDb M u x * (1 - σ) := by unfold ksDA; fun_prop
  have ca0 : Continuous (ksDa0 M x s) := by unfold ksDa0; fun_prop
  have ca1 : Continuous (ksDa1 x) := by unfold ksDa1; fun_prop
  have cL : ContinuousAt (fun σ => Real.log ((ksDA M s σ + ksDb M u x * (1 - σ)) / ksDA M s σ))
      σ :=
    ((cP.continuousAt.div cA.continuousAt hA.ne').log (div_pos hP hA).ne')
  show ContinuousAt (fun σ => ksDYA M u x s σ) σ
  simp only [ksDYA, ksDLin]
  refine (ca0.continuousAt.mul (((continuousAt_const.sub continuousAt_id).div
    (continuousAt_const.mul cA.continuousAt) (mul_pos hb hA).ne').sub
      (cL.div_const _))).add ((continuousAt_const.mul ca1.continuousAt).mul
        (((cP.continuousAt.mul cL).sub (continuousAt_const.mul
          (continuousAt_const.sub continuousAt_id))).div_const _))

/-- **The nested `VA` integral with the inner simplex integrated out.** -/
theorem ksD_ksDNestA {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {u s : ℝ}
    (hM : ∀ f, 0 < Φ.mass f) (hs : ∀ f, -(4 * Φ.mass f ^ 2) < s) (hu : 0 < u) :
    ksDNestA Φ u s = ∫ x in Ioo (0 : ℝ) 1, x⁻¹ * ∫ σ in (0 : ℝ)..1,
      ∑ f, Φ.coeff f * ksDYA (Φ.mass f) u x s σ := by
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  congr 1
  rw [integral_finsetSum _ fun f _ => (ksD_integrableOn_ksDGA (hM f) (hs f) hx hu).const_mul _,
    intervalIntegral.integral_finsetSum fun f _ =>
      ((ksD_continuousOn_ksDYA (hM f) (hs f) hx hu).intervalIntegrable_of_Icc
        zero_le_one).const_mul _]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MeasureTheory.integral_const_mul, intervalIntegral.integral_const_mul,
    ksD_integral_ksDGA (hM f) (hs f) hx hu]

/-- The same at the configuration `decCfg μ x`, for `s > -4μ²`. -/
theorem ksD_ksDNestA_cfg {μ x u s : ℝ} (hμ : 0 < μ) (hx : μ ^ 2 ≤ x) (hs : -(4 * μ ^ 2) < s)
    (hu : 0 < u) :
    ksDNestA (decCfg μ x) u s = ∫ x' in Ioo (0 : ℝ) 1, x'⁻¹ * ∫ σ in (0 : ℝ)..1,
      ∑ f, (decCfg μ x).coeff f * ksDYA ((decCfg μ x).mass f) u x' s σ := by
  refine ksD_ksDNestA _ (fun f => hμ.trans_le (ksK_mass hμ hx f)) (fun f => ?_) hu
  have h := ksK_mass hμ hx f
  nlinarith

end QED.ChainProof.SetAKS

end
