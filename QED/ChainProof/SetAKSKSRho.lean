/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.SetASpectral
public import QED.Polylog.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# R-KS, stage S: the derivative of the Källén–Sabry density, and identity by derivatives

Helper level for the identification (R-KS) of the regulator limit of the frozen goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` with the Källén–Sabry function (the open
input `SetAKSFix e`). Stage S identifies the model's summed spectral density with
`ρ⁽⁴⁾ - (3/4) L ρ_D` by comparing derivatives on `(0, 1)` and one boundary value. This file
provides the two generic pieces:

* `ksRhoDer`, `ksS_hasDerivAt_ksRho`: `ρ⁽⁴⁾` (`QED.Chain.ksRho`) is differentiable on `(0, 1)`,
  with an explicit elementary derivative (the dilogarithms differentiate to logarithms,
  `Li₂((1-δ)/(1+δ))' = 2 log(2δ/(1+δ))/(1-δ²)` and `Li₂(-(1-δ)/(1+δ))' = 2 log(2/(1+δ))/(1-δ²)`);
* `ksS_eqOn_of_hasDerivAt`: two functions with equal derivatives on `(0, 1)` whose difference
  tends to `0` at `1⁻` agree on `(0, 1)`.
-/

@[expose] public section

open Real Filter Topology Set QED.Polylog

namespace QED.ChainProof.SetAKS

open QED.Chain

/-- **The derivative of `ρ⁽⁴⁾`** on `(0, 1)`, in the notation of `QED.Chain.ksRho`
(`P₁ = 11/16 + 11δ²/24 - 7δ⁴/48`, `P₂ = 1/2 + δ²/3 - δ⁴/6`, `Q₁ = 5/8 - 3δ²/8`,
`Q₂ = 1/2 - δ²/6` and the three logarithms `ℓ₁, ℓ₂, ℓ₃`). -/
noncomputable def ksRhoDer (δ : ℝ) : ℝ :=
  (11 / 12 * δ - 7 / 12 * δ ^ 3 + (2 * δ / 3 - 2 * δ ^ 3 / 3) *
      log ((1 + δ) ^ 3 / (8 * δ ^ 2)) +
      (1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6) * (3 / (1 + δ) - 2 / δ)) * log ((1 + δ) / (1 - δ)) +
    (11 / 16 + 11 / 24 * δ ^ 2 - 7 / 48 * δ ^ 4 +
      (1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6) * log ((1 + δ) ^ 3 / (8 * δ ^ 2))) * (2 / (1 - δ ^ 2)) +
    (5 / 8 - 3 / 8 * δ ^ 2 - (1 / 2 - δ ^ 2 / 6) * log (64 * δ ^ 4 / (1 - δ ^ 2) ^ 3)) +
    δ * (-(3 / 4 * δ) + δ / 3 * log (64 * δ ^ 4 / (1 - δ ^ 2) ^ 3) -
      (1 / 2 - δ ^ 2 / 6) * (4 / δ + 6 * δ / (1 - δ ^ 2))) +
    2 * (2 * δ / 3 - 2 * δ ^ 3 / 3) *
      (2 * Li₂ ((1 - δ) / (1 + δ)) + Li₂ (-((1 - δ) / (1 + δ)))) +
    2 * (1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6) *
      ((4 * log (2 * δ / (1 + δ)) + 2 * log (2 / (1 + δ))) / (1 - δ ^ 2))

section Deriv

variable {δ : ℝ}

theorem ksS_hasDerivAt_w (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun d : ℝ => (1 - d) / (1 + d)) (-2 / (1 + δ) ^ 2) δ := by
  have h1 : (1 + δ) ≠ 0 := by linarith [hδ.1]
  refine (((hasDerivAt_id' δ).const_sub 1).fun_div ((hasDerivAt_id' δ).const_add 1)
    h1).congr_deriv ?_
  field_simp
  ring

theorem ksS_hasDerivAt_li2w (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun d : ℝ => Li₂ ((1 - d) / (1 + d)))
      (2 * log (2 * δ / (1 + δ)) / (1 - δ ^ 2)) δ := by
  obtain ⟨h0, h1⟩ := hδ
  have hp : 0 < 1 + δ := by linarith
  have hw0 : 0 < (1 - δ) / (1 + δ) := div_pos (by linarith) hp
  have hw1 : (1 - δ) / (1 + δ) < 1 := (div_lt_one hp).2 (by linarith)
  have ha : |(1 - δ) / (1 + δ)| < 1 := by rw [abs_of_pos hw0]; exact hw1
  refine ((hasDerivAt_Li₂ ha hw0.ne').comp δ (ksS_hasDerivAt_w ⟨h0, h1⟩)).congr_deriv ?_
  have e : 1 - (1 - δ) / (1 + δ) = 2 * δ / (1 + δ) := by field_simp; ring
  have hm : (1 - δ) ≠ 0 := by linarith
  have hd : 1 - δ ^ 2 ≠ 0 := by nlinarith
  rw [e]
  field_simp
  ring

theorem ksS_hasDerivAt_li2nw (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun d : ℝ => Li₂ (-((1 - d) / (1 + d))))
      (2 * log (2 / (1 + δ)) / (1 - δ ^ 2)) δ := by
  obtain ⟨h0, h1⟩ := hδ
  have hp : 0 < 1 + δ := by linarith
  have hw0 : 0 < (1 - δ) / (1 + δ) := div_pos (by linarith) hp
  have hw1 : (1 - δ) / (1 + δ) < 1 := (div_lt_one hp).2 (by linarith)
  have ha : |-((1 - δ) / (1 + δ))| < 1 := by rw [abs_neg, abs_of_pos hw0]; exact hw1
  refine ((hasDerivAt_Li₂ ha (neg_ne_zero.2 hw0.ne')).comp δ
    (ksS_hasDerivAt_w ⟨h0, h1⟩).neg).congr_deriv ?_
  have e : 1 - -((1 - δ) / (1 + δ)) = 2 / (1 + δ) := by field_simp; ring
  have hm : (1 - δ) ≠ 0 := by linarith
  have hd : 1 - δ ^ 2 ≠ 0 := by nlinarith
  rw [e]
  field_simp
  ring

theorem ksS_hasDerivAt_l1 (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun d : ℝ => log ((1 + d) ^ 3 / (8 * d ^ 2))) (3 / (1 + δ) - 2 / δ) δ := by
  obtain ⟨h0, h1⟩ := hδ
  have hp : 0 < 1 + δ := by linarith
  have hq : (8 * δ ^ 2) ≠ 0 := by positivity
  have hf : HasDerivAt (fun d : ℝ => (1 + d) ^ 3 / (8 * d ^ 2))
      ((3 * (1 + δ) ^ 2 * (8 * δ ^ 2) - (1 + δ) ^ 3 * (16 * δ)) / (8 * δ ^ 2) ^ 2) δ := by
    have ha : HasDerivAt (fun d : ℝ => (1 + d) ^ 3) (3 * (1 + δ) ^ 2) δ := by
      refine (((hasDerivAt_id' δ).const_add 1).fun_pow 3).congr_deriv ?_
      push_cast
      ring
    have hb : HasDerivAt (fun d : ℝ => 8 * d ^ 2) (16 * δ) δ := by
      refine ((hasDerivAt_pow 2 δ).const_mul 8).congr_deriv ?_
      push_cast
      ring
    exact ha.fun_div hb hq
  refine (hf.log (by positivity)).congr_deriv ?_
  have hδ0 : δ ≠ 0 := h0.ne'
  have hp0 : 1 + δ ≠ 0 := hp.ne'
  field_simp
  ring

theorem ksS_hasDerivAt_l2 (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun d : ℝ => log ((1 + d) / (1 - d))) (2 / (1 - δ ^ 2)) δ := by
  obtain ⟨h0, h1⟩ := hδ
  have hm : (1 - δ) ≠ 0 := by linarith
  have hp : (1 + δ) ≠ 0 := by linarith
  have hf := ((hasDerivAt_id' δ).const_add 1).fun_div ((hasDerivAt_id' δ).const_sub 1) hm
  refine (hf.log (div_pos (by linarith) (by linarith)).ne').congr_deriv ?_
  have : 1 - δ ^ 2 = (1 - δ) * (1 + δ) := by ring
  rw [this]
  field_simp
  ring

theorem ksS_hasDerivAt_l3 (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun d : ℝ => log (64 * d ^ 4 / (1 - d ^ 2) ^ 3))
      (4 / δ + 6 * δ / (1 - δ ^ 2)) δ := by
  obtain ⟨h0, h1⟩ := hδ
  have hd : 0 < 1 - δ ^ 2 := by nlinarith
  have hq : (1 - δ ^ 2) ^ 3 ≠ 0 := by positivity
  have ha : HasDerivAt (fun d : ℝ => 64 * d ^ 4) (256 * δ ^ 3) δ := by
    refine ((hasDerivAt_pow 4 δ).const_mul 64).congr_deriv ?_
    push_cast
    ring
  have hb : HasDerivAt (fun d : ℝ => (1 - d ^ 2) ^ 3) (-(6 * δ * (1 - δ ^ 2) ^ 2)) δ := by
    refine (((hasDerivAt_pow 2 δ).const_sub 1).fun_pow 3).congr_deriv ?_
    push_cast
    ring
  have hf := ha.fun_div hb hq
  refine (hf.log (by positivity)).congr_deriv ?_
  have hδ0 : δ ≠ 0 := h0.ne'
  have hd0 : 1 - δ ^ 2 ≠ 0 := hd.ne'
  field_simp
  ring

/-- **`ρ⁽⁴⁾` is differentiable on `(0, 1)`**, with derivative `ksRhoDer`. -/
theorem ksS_hasDerivAt_ksRho (hδ : δ ∈ Ioo (0 : ℝ) 1) : HasDerivAt ksRho (ksRhoDer δ) δ := by
  have hP1 : HasDerivAt (fun d : ℝ => 11 / 16 + 11 / 24 * d ^ 2 - 7 / 48 * d ^ 4)
      (11 / 12 * δ - 7 / 12 * δ ^ 3) δ := by
    have := ((((hasDerivAt_id δ).pow 2).const_mul (11 / 24)).const_add (11 / 16)).sub
      (((hasDerivAt_id δ).pow 4).const_mul (7 / 48))
    refine this.congr_deriv ?_
    simp only [id]
    push_cast
    ring
  have hP2 : HasDerivAt (fun d : ℝ => 1 / 2 + d ^ 2 / 3 - d ^ 4 / 6)
      (2 * δ / 3 - 2 * δ ^ 3 / 3) δ := by
    have := ((((hasDerivAt_id δ).pow 2).div_const 3).const_add (1 / 2)).sub
      (((hasDerivAt_id δ).pow 4).div_const 6)
    refine this.congr_deriv ?_
    simp only [id]
    push_cast
    ring
  have hQ1 : HasDerivAt (fun d : ℝ => 5 / 8 - 3 / 8 * d ^ 2) (-(3 / 4 * δ)) δ := by
    refine ((((hasDerivAt_id δ).pow 2).const_mul (3 / 8)).const_sub (5 / 8)).congr_deriv ?_
    simp only [id]
    push_cast
    ring
  have hQ2 : HasDerivAt (fun d : ℝ => 1 / 2 - d ^ 2 / 6) (-(δ / 3)) δ := by
    refine ((((hasDerivAt_id δ).pow 2).div_const 6).const_sub (1 / 2)).congr_deriv ?_
    simp only [id]
    push_cast
    ring
  have hA := (hP1.add (hP2.mul (ksS_hasDerivAt_l1 hδ))).mul (ksS_hasDerivAt_l2 hδ)
  have hB := (hasDerivAt_id δ).mul (hQ1.sub (hQ2.mul (ksS_hasDerivAt_l3 hδ)))
  have hC := (hP2.const_mul 2).mul
    (((ksS_hasDerivAt_li2w hδ).const_mul 2).add (ksS_hasDerivAt_li2nw hδ))
  have h := (hA.add hB).add hC
  have h' : HasDerivAt ksRho _ δ := h
  refine h'.congr_deriv ?_
  simp only [ksRhoDer, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id]
  ring

end Deriv

/-- **Identity of densities by derivatives**: if `f` and `g` have the same derivative at every
point of `(0, 1)` and `f - g → 0` at `1⁻`, then `f = g` on `(0, 1)`. -/
theorem ksS_eqOn_of_hasDerivAt {f g f' : ℝ → ℝ}
    (hf : ∀ δ ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' δ) δ)
    (hg : ∀ δ ∈ Ioo (0 : ℝ) 1, HasDerivAt g (f' δ) δ)
    (hlim : Tendsto (fun δ => f δ - g δ) (𝓝[<] 1) (𝓝 0)) : EqOn f g (Ioo 0 1) := by
  set h : ℝ → ℝ := fun δ => f δ - g δ with hh
  have hd : ∀ δ ∈ Ioo (0 : ℝ) 1, HasDerivAt h 0 δ := fun δ hδ => by
    have := (hf δ hδ).fun_sub (hg δ hδ)
    rwa [sub_self] at this
  have hdiff : DifferentiableOn ℝ h (Ioo 0 1) := fun δ hδ =>
    (hd δ hδ).differentiableAt.differentiableWithinAt
  have hderiv : EqOn (deriv h) 0 (Ioo 0 1) := fun δ hδ => (hd δ hδ).deriv
  have hc : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1, h x = h y := fun x hx y hy =>
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hderiv hx hy
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hev : h =ᶠ[𝓝[<] 1] fun _ => h (1 / 2) := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with δ hδ
    exact hc δ hδ (1 / 2) hhalf
  have hlim' : Tendsto h (𝓝[<] 1) (𝓝 (h (1 / 2))) :=
    (tendsto_congr' hev).2 tendsto_const_nhds
  have h0 : h (1 / 2) = 0 := tendsto_nhds_unique hlim' hlim
  intro δ hδ
  have := (hc δ hδ (1 / 2) hhalf).trans h0
  simp only [hh] at this
  linarith

end QED.ChainProof.SetAKS

end
