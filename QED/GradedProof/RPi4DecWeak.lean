/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecGlue

/-!
# (R-Π₄) step L9, D3: `DecScalAff` from continuity at `s = 0` and two Lipschitz bounds

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling).
The series construction (`dec_exists_scal`) uses Lipschitz bounds near `s = 0` only at the two
configurations `x = 4, 8`, and only continuity at `s = 0` elsewhere. Here the interface of
`dec_scalAff_of` is weakened accordingly:

* `DecContT e`, `DecContD e`: `decT₀ e 1 x`, `decD₀ e 1 x` tend to `0` at `s = 0`, every `x > 0`;
* `DecLipT48 e`, `DecLipD48 e`: Lipschitz near `0` at `x = 4` and `x = 8`;
* `dec_exists_scal_anom_weak` (the anomalous series construction under these inputs);
* **`dec_scalAff_of_weak`**: `DecFaceGen → DecContD → DecLipD48 → DecContT → DecLipT48 →
  DecScalAff` (with `κ = -3/(16π²)`, D3a, D3b, D3c₁ and the glue all proved).
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

/-- **Continuity at `s = 0` of the per-flavour function** at every fixed configuration. -/
def DecContT (e : ℝ) : Prop := ∀ x : ℝ, 0 < x → Tendsto (decT₀ e 1 x) (𝓝 0) (𝓝 0)

/-- **Continuity at `s = 0` of the one-loop functional** at every fixed configuration. -/
def DecContD (e : ℝ) : Prop := ∀ x : ℝ, 0 < x → Tendsto (decD₀ e 1 x) (𝓝 0) (𝓝 0)

/-- **Lipschitz near `0` of the per-flavour function at the configurations `x = 4, 8`.** -/
def DecLipT48 (e : ℝ) : Prop := DecLip0 (decT₀ e 1 4) ∧ DecLip0 (decT₀ e 1 8)

/-- **Lipschitz near `0` of the one-loop functional at the configurations `x = 4, 8`.** -/
def DecLipD48 (e : ℝ) : Prop := DecLip0 (decD₀ e 1 4) ∧ DecLip0 (decD₀ e 1 8)

theorem DecLipD.weak {e : ℝ} (h : DecLipD e) : DecContD e ∧ DecLipD48 e :=
  ⟨fun x hx => (h x hx).tendsto (decD₀_zero e 1 x), h 4 (by norm_num), h 8 (by norm_num)⟩

theorem DecLipT.weak {e : ℝ} (h : DecLipT e) : DecContT e ∧ DecLipT48 e :=
  ⟨fun x hx => (h x hx).tendsto (decT₀_zero e 1 x), h 4 (by norm_num), h 8 (by norm_num)⟩

/-- The anomaly term tends to `0` at `s = 0` when `φ` does. -/
theorem dec_tendsto_decLφ {φ : ℝ → ℂ} (hφ : Tendsto φ (𝓝 0) (𝓝 0)) (x : ℝ) :
    Tendsto (fun s => decLφ φ x s) (𝓝 0) (𝓝 0) := by
  have h1 : Tendsto (fun s : ℝ => φ (s / x)) (𝓝 0) (𝓝 0) := by
    refine hφ.comp ?_
    simpa using (continuous_id.div_const x).tendsto (0 : ℝ)
  have h2 : Tendsto (fun s : ℝ => φ (s / 2)) (𝓝 0) (𝓝 0) := by
    refine hφ.comp ?_
    simpa using (continuous_id.div_const (2 : ℝ)).tendsto (0 : ℝ)
  have := (h1.const_mul (Real.log x : ℂ)).add (h2.const_mul (((1 - x : ℝ) : ℂ) * Real.log 2))
  simp only [mul_zero, add_zero] at this
  refine this.congr fun s => ?_
  simp only [decLφ]

/-- **The anomalous series construction from continuity at `0` and Lipschitz at `x = 4, 8`.** -/
theorem dec_exists_scal_anom_weak {T D : ℝ → ℝ → ℂ} (κ : ℂ) (hD : DecDil D)
    (hD0 : ∀ x, 0 < x → D x 0 = 0) (hDc : ∀ x, 0 < x → Tendsto (D x) (𝓝 0) (𝓝 0))
    (hD4 : DecLip0 (D 4)) (hD8 : DecLip0 (D 8))
    (hT : ∀ Λ x s : ℝ, 0 < Λ → 0 < x → -(4 * min 1 x) < s → -(4 * min 1 Λ) < Λ * s →
      T (Λ * x) (Λ * s) + ((x - 2 : ℝ) : ℂ) * T Λ (Λ * s) +
        ((1 - x : ℝ) : ℂ) * T (2 * Λ) (Λ * s) = T x s + κ * (Real.log Λ : ℂ) * D x s)
    (hT0 : ∀ x, 0 < x → T x 0 = 0) (hTc : ∀ x, 0 < x → Tendsto (T x) (𝓝 0) (𝓝 0))
    (hT4 : DecLip0 (T 4)) (hT8 : DecLip0 (T 8)) :
    ∃ (G φ : ℝ → ℂ) (δ L : ℝ), 0 < δ ∧ 0 ≤ L ∧ G 0 = 0 ∧ φ 0 = 0 ∧
      (∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ → ‖G σ - G σ'‖ ≤ L * |σ - σ'|) ∧
      (∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ → ‖φ σ - φ σ'‖ ≤ L * |σ - σ'|) ∧
      ∀ x s : ℝ, 0 < x → -(4 * min 1 x) < s → T x s = decR G x s + κ * decLφ φ x s := by
  -- the one-loop profile
  obtain ⟨δ₁, L₁, hδ₁, -, h4, h8⟩ := hD4.common hD8
  obtain ⟨φ, hφ0, hφl, hDφ⟩ := dec_exists_scal hD hD0 hDc hδ₁ h4 h8
  have hφL : DecLip0 φ := ⟨δ₁, 8 * L₁, hδ₁, hφl⟩
  -- the anomaly-free two-loop functional
  set T' : ℝ → ℝ → ℂ := fun x s => T x s - κ * decLφ φ x s with hT'
  have hL' : ∀ x, 1 ≤ x → DecLip0 fun s => decLφ φ x s := fun x hx =>
    ((hφL.comp_div hx).const_mul _).add ((hφL.comp_div one_le_two).const_mul _)
  have hT'0 : ∀ x, 0 < x → T' x 0 = 0 := fun x hx => by
    simp [hT', decLφ, hT0 x hx, hφ0]
  have hT'c : ∀ x, 0 < x → Tendsto (T' x) (𝓝 0) (𝓝 0) := fun x hx => by
    have := (hTc x hx).sub ((dec_tendsto_decLφ (hφL.tendsto hφ0) x).const_mul κ)
    simpa only [mul_zero, sub_zero] using this
  have hT'4 : DecLip0 (T' 4) := hT4.sub ((hL' 4 (by norm_num)).const_mul κ)
  have hT'8 : DecLip0 (T' 8) := hT8.sub ((hL' 8 (by norm_num)).const_mul κ)
  have hT'dil : DecDil T' := by
    intro Λ x s hΛ hx hs hΛs
    have h := hT Λ x s hΛ hx hs hΛs
    have hl := decLφ_dil φ hΛ hx s
    simp only [hT']
    rw [hDφ x s hx hs] at h
    linear_combination h - κ * hl
  obtain ⟨δ₂, L₂, hδ₂, -, h4', h8'⟩ := hT'4.common hT'8
  obtain ⟨G, hG0, hGl, hTG⟩ := dec_exists_scal hT'dil hT'0 hT'c hδ₂ h4' h8'
  have hGL : DecLip0 G := ⟨δ₂, 8 * L₂, hδ₂, hGl⟩
  obtain ⟨δ, L, hδ, hL, hG, hφ⟩ := hGL.common hφL
  refine ⟨G, φ, δ, L, hδ, hL, hG0, hφ0, hG, hφ, fun x s hx hs => ?_⟩
  have := hTG x s hx hs
  simp only [hT'] at this
  linear_combination this

/-- **`DecScalAff` from the weakened interface** (scaling and anomaly abstract). -/
theorem dec_scalAff_of_weak_abs {e : ℝ} (κ : ℂ) (hS : DecScaleT₀ e) (hA : DecAnomT₀ e κ)
    (hD : DecDil (decD₀ e 1)) (hDc : DecContD e) (hD48 : DecLipD48 e) (hTc : DecContT e)
    (hT48 : DecLipT48 e) : DecScalAff e := by
  obtain ⟨G, φ, δ, L, hδ, hL, hG0, hφ0, hG, hφ, hT⟩ := dec_exists_scal_anom_weak κ hD
    (fun x _ => decD₀_zero e 1 x) hDc hD48.1 hD48.2 hA (fun x _ => decT₀_zero e 1 x) hTc
    hT48.1 hT48.2
  refine ⟨G, φ, κ, δ, L,
    fun μ s => -2 * G (s / μ ^ 2) + G (s / μ ^ 2 / 2) +
      κ * (Real.log 2 : ℂ) * φ (s / μ ^ 2 / 2),
    fun μ s => (G (s / μ ^ 2) - G (s / μ ^ 2 / 2) - κ * (Real.log 2 : ℂ) * φ (s / μ ^ 2 / 2)) /
      ((μ ^ 2 : ℝ) : ℂ),
    hδ, hL, hG0, hφ0, hG, hφ, fun μ x s hμ hx hs => ?_⟩
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hy : 1 ≤ x / μ ^ 2 := by rwa [le_div_iff₀ hμ2, one_mul]
  have ht : -(4 * min 1 (x / μ ^ 2)) < s / μ ^ 2 := by
    rw [min_eq_left hy, lt_div_iff₀ hμ2]
    linarith
  rw [hS μ x s hμ hx hs, hT _ _ (zero_lt_one.trans_le hy) ht]
  have hx0 : x ≠ 0 := (hμ2.trans_le hx).ne'
  have hμc : ((μ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hμ2.ne'
  simp only [decR, decLφ, decT]
  rw [show s / μ ^ 2 / (x / μ ^ 2) = s / x by field_simp]
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  push_cast
  field_simp
  ring

/-- **`DecScalAff` modulo `DecFaceGen`, continuity at `s = 0` and the Lipschitz bounds at
`x = 4, 8`.** -/
theorem dec_scalAff_of_weak (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e)
    (hDc : DecContD P.e) (hD48 : DecLipD48 P.e) (hTc : DecContT P.e) (hT48 : DecLipT48 P.e) :
    DecScalAff P.e :=
  dec_scalAff_of_weak_abs _ (dec_scaleT₀_of_faceGen P he hF) (dec_anomT₀ P he hF)
    (dec_dil_decD₀ P he) hDc hD48 hTc hT48

end QED.GradedProof.RPi4

end
