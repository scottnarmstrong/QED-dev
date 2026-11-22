/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSETail
public import QED.ChainProof.SetCRegDispShellSERep
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The quadratic blocks of the class `V` limit as tails of the dressed photon

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S6 of the plan (b1c). With
`A = a²`, `B = b²`, `U = μ²` pairwise distinct, `R(t) = t² D(t)²/(t + U)` the dressed photon
and `w` the self-energy argument, the quadratic blocks `seQuadBlk` of one flavour piece of the
class `V` limit (`QED/ChainProof/SetCRegDispShellSEExp.lean`) are a single Feynman-parameter
integral of the two tails

`T₀(w) = ∫_w^∞ R` (closed form `bubTailVP`) and `T₁(w) = ∫_w^∞ R(t)/t dt` (closed form
`quadTailVP`, from the partial fractions of `R(t)/t = t D(t)²/(t + U)`):

`seQuadBlk = ∫₀¹ 2 seWt₂(y) (G₂(y) (-2k/(1-y)²) T₁(w) - G₁ (-2k/(1-y)) (T₀(w) - w T₁(w))) dy`,

`k = U/(A - B)²`. The two-simplex integrals of the three blocks combine pointwise
(`quadJ₂_sum`, `quadJ₁_sum`): the logarithm of `1 - y` cancels.

* `bubTailVP`, `quadTailVP`: the closed forms;
* `continuousOn_seSimJ₂`, `continuousOn_seSimJ₁`: the two-simplex integrals depend
  continuously on nodes bounded below;
* **`quadJ₂_sum`**, **`quadJ₁_sum`**: the pointwise identities;
* **`seQuadBlk_eq_tail`**: the quadratic blocks as one integral.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.WickModel.SelfEnergyLimit QED.OneLoop
open QED.ChainProof.SetCRegDispSE (seWt seProdLim)
open QED.ChainProof.SetCRegBubble (bubCoefC bubCoefA bubCoefB bubCoefA2 bubCoefB2)
open QED.Integration.Feynman (simplexSet isCompact_simplexSet measurableSet_simplexSet)

/-! ### The closed forms -/

/-- The closed form of `∫_w^∞ R` in terms of `A, B, U`. -/
noncomputable def bubTailVP (A B U w : ℝ) : ℝ :=
  -bubCoefC A B U * Real.log (w + U) - bubCoefA A B U * Real.log (w + A) -
    bubCoefB A B U * Real.log (w + B) + bubCoefA2 A U / (w + A) + bubCoefB2 B U / (w + B)

/-- The closed form of `∫_w^∞ R(t)/t dt`, from the partial fractions of `t D(t)²/(t + U)`. -/
noncomputable def quadTailVP (A B U w : ℝ) : ℝ :=
  U * (A - B) ^ 2 / ((A - U) ^ 2 * (B - U) ^ 2) * Real.log (w + U) -
    (2 * A ^ 2 - A * U - B * U) / ((A - B) * (A - U) ^ 2) * Real.log (w + A) -
    (A * U - 2 * B ^ 2 + B * U) / ((A - B) * (B - U) ^ 2) * Real.log (w + B) +
    A / (A - U) / (w + A) + B / (B - U) / (w + B)

theorem photonTailVP_eq_bubTailVP (m mγ Λ T w : ℝ) :
    photonTailVP m mγ Λ T w = bubTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) w := rfl

/-! ### The pointwise identities -/

section Pointwise

variable {A B U w l : ℝ} (hA : 0 < w + A) (hB : 0 < w + B) (hU : 0 < w + U) (hl : 0 < l)
  (hAB : A ≠ B) (hAU : A ≠ U) (hBU : B ≠ U)

include hA hB hU hl hAB hAU hBU in
/-- **The `J₂` sum of the three quadratic blocks.** -/
theorem quadJ₂_sum :
    2 * A * U / ((A - B) * (A - U)) * seSimJ₂ (l * (w + A)) (l * (w + A)) (l * (w + B)) -
        2 * B * U / ((A - B) * (B - U)) * seSimJ₂ (l * (w + A)) (l * (w + B)) (l * (w + B)) +
        2 * U ^ 2 / ((A - U) * (B - U)) *
          seSimJ₂ (l * (w + A)) (l * (w + B)) (l * (w + U)) =
      -(2 * (U / (A - B) ^ 2)) / l ^ 2 * quadTailVP A B U w := by
  have pa : 0 < l * (w + A) := mul_pos hl hA
  have pb : 0 < l * (w + B) := mul_pos hl hB
  have pu : 0 < l * (w + U) := mul_pos hl hU
  have r1 : A - B ≠ 0 := sub_ne_zero.2 hAB
  have r2 : A - U ≠ 0 := sub_ne_zero.2 hAU
  have r3 : B - U ≠ 0 := sub_ne_zero.2 hBU
  have dab : l * (w + A) ≠ l * (w + B) := fun h =>
    hAB (by have := mul_left_cancel₀ hl.ne' h; linarith)
  have dau : l * (w + A) ≠ l * (w + U) := fun h =>
    hAU (by have := mul_left_cancel₀ hl.ne' h; linarith)
  have dbu : l * (w + B) ≠ l * (w + U) := fun h =>
    hBU (by have := mul_left_cancel₀ hl.ne' h; linarith)
  rw [seSimJ₂_rep01 pa pb dab, seSimJ₂_rep12 pa pb dab, seSimJ₂_eq pa pb pu dab dau dbu]
  unfold seSimI₂ quadTailVP
  rw [Real.log_mul hl.ne' hA.ne', Real.log_mul hl.ne' hB.ne', Real.log_mul hl.ne' hU.ne']
  have e1 : l * (w + A) - l * (w + B) = l * (A - B) := by ring
  have e2 : l * (w + A) - l * (w + U) = l * (A - U) := by ring
  have e3 : l * (w + B) - l * (w + U) = l * (B - U) := by ring
  have e4 : l * (w + B) - l * (w + A) = -(l * (A - B)) := by ring
  rw [e1, e2, e3, e4]
  have r4 : B - A ≠ 0 := fun h => r1 (by linarith)
  field_simp
  ring

include hA hB hU hl hAB hAU hBU in
/-- **The `J₁` sum of the three quadratic blocks.** -/
theorem quadJ₁_sum :
    2 * A * U / ((A - B) * (A - U)) * seSimJ₁ (l * (w + A)) (l * (w + A)) (l * (w + B)) -
        2 * B * U / ((A - B) * (B - U)) * seSimJ₁ (l * (w + A)) (l * (w + B)) (l * (w + B)) +
        2 * U ^ 2 / ((A - U) * (B - U)) *
          seSimJ₁ (l * (w + A)) (l * (w + B)) (l * (w + U)) =
      -(2 * (U / (A - B) ^ 2)) / l * (bubTailVP A B U w - w * quadTailVP A B U w) := by
  have pa : 0 < l * (w + A) := mul_pos hl hA
  have pb : 0 < l * (w + B) := mul_pos hl hB
  have pu : 0 < l * (w + U) := mul_pos hl hU
  have r1 : A - B ≠ 0 := sub_ne_zero.2 hAB
  have r2 : A - U ≠ 0 := sub_ne_zero.2 hAU
  have r3 : B - U ≠ 0 := sub_ne_zero.2 hBU
  have dab : l * (w + A) ≠ l * (w + B) := fun h =>
    hAB (by have := mul_left_cancel₀ hl.ne' h; linarith)
  have dau : l * (w + A) ≠ l * (w + U) := fun h =>
    hAU (by have := mul_left_cancel₀ hl.ne' h; linarith)
  have dbu : l * (w + B) ≠ l * (w + U) := fun h =>
    hBU (by have := mul_left_cancel₀ hl.ne' h; linarith)
  rw [seSimJ₁_rep01 pa pb dab, seSimJ₁_rep12 pa pb dab, seSimJ₁_eq pa pb pu dab dau dbu]
  unfold seSimI₁ quadTailVP bubTailVP
  simp only [bubCoefC, bubCoefA, bubCoefB, bubCoefA2, bubCoefB2]
  rw [Real.log_mul hl.ne' hA.ne', Real.log_mul hl.ne' hB.ne', Real.log_mul hl.ne' hU.ne']
  have e1 : l * (w + A) - l * (w + B) = l * (A - B) := by ring
  have e2 : l * (w + A) - l * (w + U) = l * (A - U) := by ring
  have e3 : l * (w + B) - l * (w + U) = l * (B - U) := by ring
  have e4 : l * (w + B) - l * (w + A) = -(l * (A - B)) := by ring
  rw [e1, e2, e3, e4]
  have r4 : B - A ≠ 0 := fun h => r1 (by linarith)
  have r5 : U - A ≠ 0 := fun h => r2 (by linarith)
  have r6 : U - B ≠ 0 := fun h => r3 (by linarith)
  field_simp
  ring

end Pointwise

/-! ### Continuity of the two-simplex integrals -/

theorem simplexAff_ge {d₀ d₁ d₂ c : ℝ} (h₀ : c ≤ d₀) (h₁ : c ≤ d₁) (h₂ : c ≤ d₂)
    {u : Fin 2 → ℝ} (hu : u ∈ simplexSet 2) : c ≤ simplexAff d₀ d₁ d₂ u := by
  obtain ⟨hnn, hs⟩ := (QED.Integration.SimplexMerge.mem_simplexSet_iff_le two_pos u).1 hu
  rw [Fin.sum_univ_two] at hs
  have e : simplexAff d₀ d₁ d₂ u = (1 - u 0 - u 1) * d₂ + u 0 * d₀ + u 1 * d₁ := by
    unfold simplexAff; ring
  rw [e]
  have h0 := hnn 0
  have h1 := hnn 1
  nlinarith [mul_le_mul_of_nonneg_left h₀ h0, mul_le_mul_of_nonneg_left h₁ h1,
    mul_le_mul_of_nonneg_left h₂ (by linarith : 0 ≤ 1 - u 0 - u 1)]

section Cont

variable {d₀ d₁ d₂ : ℝ → ℝ} (hd₀ : Continuous d₀) (hd₁ : Continuous d₁) (hd₂ : Continuous d₂)
  {c₀ : ℝ} (hc₀ : 0 < c₀) {S : Set ℝ} (h₀ : ∀ y ∈ S, c₀ ≤ d₀ y) (h₁ : ∀ y ∈ S, c₀ ≤ d₁ y)
  (h₂ : ∀ y ∈ S, c₀ ≤ d₂ y)

include hd₀ hd₁ hd₂ in
theorem continuous_simplexAff_uncurry :
    Continuous fun q : ℝ × (Fin 2 → ℝ) => simplexAff (d₀ q.1) (d₁ q.1) (d₂ q.1) q.2 := by
  unfold simplexAff
  have := hd₀.comp (continuous_fst (X := ℝ) (Y := Fin 2 → ℝ))
  have := hd₁.comp (continuous_fst (X := ℝ) (Y := Fin 2 → ℝ))
  have := hd₂.comp (continuous_fst (X := ℝ) (Y := Fin 2 → ℝ))
  fun_prop

include hd₀ hd₁ hd₂ hc₀ h₀ h₁ h₂ in
theorem continuousOn_seSimJ₂ :
    ContinuousOn (fun y => seSimJ₂ (d₀ y) (d₁ y) (d₂ y)) S := by
  set F : ℝ → (Fin 2 → ℝ) → ℝ := fun y u =>
    (max c₀ (simplexAff (d₀ y) (d₁ y) (d₂ y) u) ^ 2)⁻¹
  have hF : Continuous (Function.uncurry F) :=
    ((continuous_const.max (continuous_simplexAff_uncurry hd₀ hd₁ hd₂)).pow 2).inv₀
      fun q => (pow_pos (hc₀.trans_le (le_max_left _ _)) 2).ne'
  refine (continuous_parametric_integral_of_continuous (μ := volume) hF
    (isCompact_simplexSet 2)).continuousOn.congr fun y hy => ?_
  refine setIntegral_congr_fun (measurableSet_simplexSet 2) fun u hu => ?_
  simp only [F, max_eq_right (simplexAff_ge (h₀ y hy) (h₁ y hy) (h₂ y hy) hu)]

include hd₀ hd₁ hd₂ hc₀ h₀ h₁ h₂ in
theorem continuousOn_seSimJ₁ :
    ContinuousOn (fun y => seSimJ₁ (d₀ y) (d₁ y) (d₂ y)) S := by
  set F : ℝ → (Fin 2 → ℝ) → ℝ := fun y u =>
    (max c₀ (simplexAff (d₀ y) (d₁ y) (d₂ y) u))⁻¹
  have hF : Continuous (Function.uncurry F) :=
    (continuous_const.max (continuous_simplexAff_uncurry hd₀ hd₁ hd₂)).inv₀
      fun q => (hc₀.trans_le (le_max_left _ _)).ne'
  refine (continuous_parametric_integral_of_continuous (μ := volume) hF
    (isCompact_simplexSet 2)).continuousOn.congr fun y hy => ?_
  refine setIntegral_congr_fun (measurableSet_simplexSet 2) fun u hu => ?_
  simp only [F, max_eq_right (simplexAff_ge (h₀ y hy) (h₁ y hy) (h₂ y hy) hu)]

end Cont

/-! ### The quadratic blocks -/

theorem continuous_seQuadG₂ (p : Fin 4 → ℝ) (α β : Fin 4) (P : Fin 4 → ℝ) :
    Continuous fun y : ℝ => seQuadG₂ p α β P y := by
  unfold seQuadG₂
  have h : Continuous fun y : ℝ => seQuad p α β (-(y • P)) :=
    (continuous_seQuad p α β).comp (by fun_prop)
  fun_prop

section Quad

variable {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀) {P : Fin 4 → ℝ}
  (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot P P) y)

include hM₀ hc₀ hP in
theorem integrableOn_quadBlk {x₀ x₁ x₂ : ℝ} (h₀ : M₀ ≤ x₀) (h₁ : M₀ ≤ x₁) (h₂ : M₀ ≤ x₂)
    (p : Fin 4 → ℝ) (α β : Fin 4) :
    IntegrableOn (fun y => seWt 2 y *
        (seQuadG₂ p α β P y * (seSimJ₂ (selfEnergyFeynmanMass m x₀ (Minkowski.dot P P) y)
            (selfEnergyFeynmanMass m x₁ (Minkowski.dot P P) y)
            (selfEnergyFeynmanMass m x₂ (Minkowski.dot P P) y) : ℂ) -
          seQuadG₁ p α β * (seSimJ₁ (selfEnergyFeynmanMass m x₀ (Minkowski.dot P P) y)
            (selfEnergyFeynmanMass m x₁ (Minkowski.dot P P) y)
            (selfEnergyFeynmanMass m x₂ (Minkowski.dot P P) y) : ℂ)))
      (Ioc (0 : ℝ) 1) := by
  have hge : ∀ x, M₀ ≤ x → ∀ y ∈ Icc (0 : ℝ) 1,
      c₀ ≤ selfEnergyFeynmanMass m x (Minkowski.dot P P) y := fun x hx y hy =>
    (hP y hy).trans (SetCRegDispSE.selfEnergyFeynmanMass_mono hM₀ hx hy)
  have c := continuous_selfEnergyFeynmanMass_y m
  have hJ2 := continuousOn_seSimJ₂ (c x₀ _) (c x₁ _) (c x₂ _) hc₀ (hge x₀ h₀) (hge x₁ h₁)
    (hge x₂ h₂)
  have hJ1 := continuousOn_seSimJ₁ (c x₀ _) (c x₁ _) (c x₂ _) hc₀ (hge x₀ h₀) (hge x₁ h₁)
    (hge x₂ h₂)
  have hw : Continuous fun y : ℝ => seWt 2 y := by unfold seWt; fun_prop
  refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
  exact hw.continuousOn.mul (((continuous_seQuadG₂ p α β P).continuousOn.mul
    (Complex.continuous_ofReal.comp_continuousOn hJ2)).sub (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn hJ1)))

include hM₀ hc₀ hP in
/-- **The quadratic blocks of a flavour piece as one integral of the tails**: with
`k = μ²/(a² - b²)²` and `w = seArg m s y`,
`seQuadBlk = ∫₀¹ 2 seWt₂ (G₂ (-2k/(1-y)²) T₁(w) - G₁ (-2k/(1-y)) (T₀(w) - w T₁(w))) dy`. -/
theorem seQuadBlk_eq_tail {a b μ : ℝ} (ha : M₀ ≤ a) (hb : M₀ ≤ b) (hμ : M₀ ≤ μ)
    (hAB : a ^ 2 ≠ b ^ 2) (hAU : a ^ 2 ≠ μ ^ 2) (hBU : b ^ 2 ≠ μ ^ 2) (p : Fin 4 → ℝ)
    (α β : Fin 4) :
    seQuadBlk (seQuadA p α β) (seQuad p α β) m a b μ P = ∫ y in Ioc (0 : ℝ) 1,
      2 * seWt 2 y * (seQuadG₂ p α β P y *
          ((-(2 * (μ ^ 2 / (a ^ 2 - b ^ 2) ^ 2)) / (1 - y) ^ 2 *
            quadTailVP (a ^ 2) (b ^ 2) (μ ^ 2) (seArg m (Minkowski.dot P P) y) : ℝ) : ℂ) -
        seQuadG₁ p α β * ((-(2 * (μ ^ 2 / (a ^ 2 - b ^ 2) ^ 2)) / (1 - y) *
          (bubTailVP (a ^ 2) (b ^ 2) (μ ^ 2) (seArg m (Minkowski.dot P P) y) -
            seArg m (Minkowski.dot P P) y *
              quadTailVP (a ^ 2) (b ^ 2) (μ ^ 2) (seArg m (Minkowski.dot P P) y)) : ℝ) :
                ℂ)) := by
  set s := Minkowski.dot P P with hs
  unfold seQuadBlk
  rw [seProdLim_seQuad_three hM₀ hc₀ hP ha ha hb, seProdLim_seQuad_three hM₀ hc₀ hP ha hb hb,
    seProdLim_seQuad_three hM₀ hc₀ hP ha hb hμ]
  have i1 := integrableOn_quadBlk hM₀ hc₀ hP ha ha hb p α β
  have i2 := integrableOn_quadBlk hM₀ hc₀ hP ha hb hb p α β
  have i3 := integrableOn_quadBlk hM₀ hc₀ hP ha hb hμ p α β
  set k1 : ℂ := 2 * (a : ℂ) ^ 2 * μ ^ 2 / ((a ^ 2 - b ^ 2 : ℂ) * (a ^ 2 - μ ^ 2 : ℂ))
  set k2 : ℂ := 2 * (b : ℂ) ^ 2 * μ ^ 2 / ((a ^ 2 - b ^ 2 : ℂ) * (b ^ 2 - μ ^ 2 : ℂ))
  set k3 : ℂ := 2 * (μ : ℂ) ^ 4 / ((a ^ 2 - μ ^ 2 : ℂ) * (b ^ 2 - μ ^ 2 : ℂ))
  have j1 := i1.const_mul (k1 * 2)
  have j2 := i2.const_mul (k2 * 2)
  have j3 := i3.const_mul (k3 * 2)
  rw [← mul_assoc k1, ← mul_assoc k2, ← mul_assoc k3, ← integral_const_mul,
    ← integral_const_mul, ← integral_const_mul]
  have j12 := j1.sub j2
  simp only [Pi.sub_def] at j12
  rw [← integral_sub j1 j2, ← integral_add j12 j3, integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
  have hy1 : 0 < 1 - y := by linarith [hy.2]
  have hyI : y ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hy
  set w := seArg m s y with hw
  have hD : ∀ M : ℝ, M₀ ≤ M → selfEnergyFeynmanMass m M s y = (1 - y) * (w + M ^ 2) ∧
      0 < w + M ^ 2 := by
    intro M hM
    have e := selfEnergyFeynmanMass_eq_seArg m M s hy.2.ne
    have p := selfEnergyFeynmanMass_pos_of_le hM₀ hc₀ hP hM hyI
    rw [e] at p
    exact ⟨e, pos_of_mul_pos_right p hy1.le⟩
  obtain ⟨ea, pa⟩ := hD a ha
  obtain ⟨eb, pb⟩ := hD b hb
  obtain ⟨eu, pu⟩ := hD μ hμ
  have hJ2 := quadJ₂_sum pa pb pu hy1 hAB hAU hBU
  have hJ1 := quadJ₁_sum pa pb pu hy1 hAB hAU hBU
  have hJ2c := congrArg (fun r : ℝ => (r : ℂ)) hJ2
  have hJ1c := congrArg (fun r : ℝ => (r : ℂ)) hJ1
  beta_reduce at hJ2c hJ1c ⊢
  rw [ea, eb, eu]
  push_cast at hJ2c hJ1c ⊢
  linear_combination (2 * seWt 2 y * seQuadG₂ p α β P y) * hJ2c -
    (2 * seWt 2 y * seQuadG₁ p α β) * hJ1c

end Quad

end QED.ChainProof.SetCRegDisp

end
