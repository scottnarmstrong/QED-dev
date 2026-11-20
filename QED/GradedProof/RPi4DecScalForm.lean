/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# (R-Π₄) step L9, D3e: the scaling form with the counterterm-mass anomaly

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
part D3e. Model-free. The per-flavour two-loop functional `T` (counterterms at the fixed mass
`1`) is dilation covariant only up to the anomaly `κ log Λ · D` of the counterterm mass, where
`D` is an (exactly covariant) one-loop functional. Then:

* `DecLip0 f`: `f` is Lipschitz on some `[-δ, δ]`; closure under sums, scalars and `t ↦ t / k`;
* `dec_exists_scal_anom`: **`D = decR φ` and `T = decR G + κ L_φ`**, `L_φ(x, s) =
  log x · φ(s/x) + (1 - x) log 2 · φ(s/2)`, with `G`, `φ` vanishing at `0` and Lipschitz near
  `0`; that is, `T x s = G(s/x) + κ log x · φ(s/x) + (an affine function of x)`.
-/

@[expose] public section

open Filter Topology

namespace QED.GradedProof.RPi4

/-- **Lipschitz near `0`.** -/
def DecLip0 (f : ℝ → ℂ) : Prop :=
  ∃ δ L : ℝ, 0 < δ ∧ ∀ t t' : ℝ, |t| ≤ δ → |t'| ≤ δ → ‖f t - f t'‖ ≤ L * |t - t'|

theorem DecLip0.mono {f : ℝ → ℂ} {δ L δ' L' : ℝ} (hf : ∀ t t' : ℝ, |t| ≤ δ → |t'| ≤ δ →
    ‖f t - f t'‖ ≤ L * |t - t'|) (hδ : δ' ≤ δ) (hL : L ≤ L') :
    ∀ t t' : ℝ, |t| ≤ δ' → |t'| ≤ δ' → ‖f t - f t'‖ ≤ L' * |t - t'| := fun t t' ht ht' =>
  (hf t t' (ht.trans hδ) (ht'.trans hδ)).trans (mul_le_mul_of_nonneg_right hL (abs_nonneg _))

/-- Two functions Lipschitz near `0` are so with common `δ`, `L`, `L ≥ 0`. -/
theorem DecLip0.common {f g : ℝ → ℂ} (hf : DecLip0 f) (hg : DecLip0 g) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 ≤ L ∧
      (∀ t t' : ℝ, |t| ≤ δ → |t'| ≤ δ → ‖f t - f t'‖ ≤ L * |t - t'|) ∧
      ∀ t t' : ℝ, |t| ≤ δ → |t'| ≤ δ → ‖g t - g t'‖ ≤ L * |t - t'| := by
  obtain ⟨δ₁, L₁, h₁, hf⟩ := hf
  obtain ⟨δ₂, L₂, h₂, hg⟩ := hg
  refine ⟨min δ₁ δ₂, max (max L₁ L₂) 0, lt_min h₁ h₂, le_max_right _ _, ?_, ?_⟩
  · exact DecLip0.mono hf (min_le_left _ _) ((le_max_left _ _).trans (le_max_left _ _))
  · exact DecLip0.mono hg (min_le_right _ _) ((le_max_right _ _).trans (le_max_left _ _))

theorem DecLip0.add {f g : ℝ → ℂ} (hf : DecLip0 f) (hg : DecLip0 g) :
    DecLip0 fun t => f t + g t := by
  obtain ⟨δ, L, hδ, -, hf, hg⟩ := hf.common hg
  refine ⟨δ, 2 * L, hδ, fun t t' ht ht' => ?_⟩
  calc ‖f t + g t - (f t' + g t')‖ = ‖(f t - f t') + (g t - g t')‖ := by ring_nf
    _ ≤ L * |t - t'| + L * |t - t'| := (norm_add_le _ _).trans
        (add_le_add (hf t t' ht ht') (hg t t' ht ht'))
    _ = _ := by ring

theorem DecLip0.const_mul {f : ℝ → ℂ} (hf : DecLip0 f) (c : ℂ) : DecLip0 fun t => c * f t := by
  obtain ⟨δ, L, hδ, hf⟩ := hf
  refine ⟨δ, ‖c‖ * L, hδ, fun t t' ht ht' => ?_⟩
  rw [← mul_sub, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf t t' ht ht') (norm_nonneg _)

theorem DecLip0.sub {f g : ℝ → ℂ} (hf : DecLip0 f) (hg : DecLip0 g) :
    DecLip0 fun t => f t - g t := by
  have := hf.add (hg.const_mul (-1))
  simpa [sub_eq_add_neg] using this

theorem DecLip0.comp_div {f : ℝ → ℂ} (hf : DecLip0 f) {k : ℝ} (hk : 1 ≤ k) :
    DecLip0 fun t => f (t / k) := by
  obtain ⟨δ, L, hδ, hf⟩ := hf
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have e : ∀ τ : ℝ, |τ / k| ≤ |τ| := fun τ => by
    rw [abs_div, abs_of_pos hk0]
    exact div_le_self (abs_nonneg _) hk
  refine ⟨δ, |L|, hδ, fun t t' ht ht' => ?_⟩
  have h := hf _ _ ((e t).trans ht) ((e t').trans ht')
  rw [← sub_div] at h
  calc _ ≤ L * |(t - t') / k| := h
    _ ≤ |L| * |(t - t') / k| := mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)
    _ ≤ |L| * |t - t'| := mul_le_mul_of_nonneg_left (e _) (abs_nonneg _)

theorem DecLip0.tendsto {f : ℝ → ℂ} (hf : DecLip0 f) (h0 : f 0 = 0) :
    Tendsto f (𝓝 0) (𝓝 0) := by
  obtain ⟨δ, L, hδ, hf⟩ := hf
  exact dec_tendsto_of_lip h0 hδ hf

/-- The anomaly term on `ν_x`: `log x · φ(s/x) + (1 - x) log 2 · φ(s/2)`. -/
noncomputable def decLφ (φ : ℝ → ℂ) (x s : ℝ) : ℂ :=
  (Real.log x : ℂ) * φ (s / x) + ((1 - x : ℝ) : ℂ) * (Real.log 2 : ℂ) * φ (s / 2)

/-- **The anomaly term is covariant up to `log Λ · decR φ`.** -/
theorem decLφ_dil (φ : ℝ → ℂ) {Λ x : ℝ} (hΛ : 0 < Λ) (hx : 0 < x) (s : ℝ) :
    decLφ φ (Λ * x) (Λ * s) + ((x - 2 : ℝ) : ℂ) * decLφ φ Λ (Λ * s) +
      ((1 - x : ℝ) : ℂ) * decLφ φ (2 * Λ) (Λ * s) =
      decLφ φ x s + (Real.log Λ : ℂ) * decR φ x s := by
  simp only [decLφ, decR]
  rw [Real.log_mul hΛ.ne' hx.ne', Real.log_mul two_ne_zero hΛ.ne',
    mul_div_mul_left _ _ hΛ.ne', show Λ * s / Λ = s by field_simp,
    show Λ * s / (2 * Λ) = s / 2 by field_simp]
  push_cast
  ring

/-- **D3e with the anomaly.** If the one-loop functional `D` is dilation covariant and the
two-loop functional `T` is covariant up to `κ log Λ · D`, both vanishing at `s = 0` and Lipschitz
near `0` at every `x > 0`, then `D = decR φ` and `T = decR G + κ decLφ φ` with `G`, `φ` vanishing
at `0` and Lipschitz on a common `[-δ, δ]`. -/
theorem dec_exists_scal_anom {T D : ℝ → ℝ → ℂ} (κ : ℂ) (hD : DecDil D)
    (hD0 : ∀ x, 0 < x → D x 0 = 0) (hDl : ∀ x, 0 < x → DecLip0 (D x))
    (hT : ∀ Λ x s : ℝ, 0 < Λ → 0 < x → -(4 * min 1 x) < s → -(4 * min 1 Λ) < Λ * s →
      T (Λ * x) (Λ * s) + ((x - 2 : ℝ) : ℂ) * T Λ (Λ * s) +
        ((1 - x : ℝ) : ℂ) * T (2 * Λ) (Λ * s) = T x s + κ * (Real.log Λ : ℂ) * D x s)
    (hT0 : ∀ x, 0 < x → T x 0 = 0) (hTl : ∀ x, 0 < x → DecLip0 (T x)) :
    ∃ (G φ : ℝ → ℂ) (δ L : ℝ), 0 < δ ∧ 0 ≤ L ∧ G 0 = 0 ∧ φ 0 = 0 ∧
      (∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ → ‖G σ - G σ'‖ ≤ L * |σ - σ'|) ∧
      (∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ → ‖φ σ - φ σ'‖ ≤ L * |σ - σ'|) ∧
      ∀ x s : ℝ, 0 < x → -(4 * min 1 x) < s → T x s = decR G x s + κ * decLφ φ x s := by
  -- the one-loop profile
  obtain ⟨δ₁, L₁, hδ₁, -, h4, h8⟩ := (hDl 4 (by norm_num)).common (hDl 8 (by norm_num))
  obtain ⟨φ, hφ0, hφl, hDφ⟩ := dec_exists_scal hD hD0
    (fun x hx => (hDl x hx).tendsto (hD0 x hx)) hδ₁ h4 h8
  have hφL : DecLip0 φ := ⟨δ₁, 8 * L₁, hδ₁, hφl⟩
  -- the anomaly-free two-loop functional
  set T' : ℝ → ℝ → ℂ := fun x s => T x s - κ * decLφ φ x s with hT'
  have hL' : ∀ x, 0 < x → DecLip0 fun s => decLφ φ x s := by
    intro x hx
    simp only [decLφ]
    refine DecLip0.add ?_ ?_
    · rcases le_or_gt 1 x with h | h
      · exact (hφL.comp_div h).const_mul _
      · -- `x < 1`: `φ(s/x) = φ(s / x)` with `x⁻¹ > 1`; use the scaled bound directly
        obtain ⟨δ, L, hδ, hf⟩ := hφL
        refine ⟨δ * x, |L| * x⁻¹ * ‖(Real.log x : ℂ)‖, by positivity, fun t t' ht ht' => ?_⟩
        have e : ∀ τ : ℝ, |τ| ≤ δ * x → |τ / x| ≤ δ := fun τ hτ => by
          rw [abs_div, abs_of_pos hx, div_le_iff₀ hx]
          exact hτ
        have hb := hf _ _ (e t ht) (e t' ht')
        rw [← sub_div, abs_div, abs_of_pos hx] at hb
        rw [← mul_sub, norm_mul]
        calc ‖(Real.log x : ℂ)‖ * ‖φ (t / x) - φ (t' / x)‖ ≤
            ‖(Real.log x : ℂ)‖ * (|L| * (|t - t'| / x)) :=
              mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
                (by positivity))) (norm_nonneg _)
          _ = _ := by field_simp
    · exact (hφL.comp_div one_le_two).const_mul _
  have hT'0 : ∀ x, 0 < x → T' x 0 = 0 := fun x hx => by
    simp [hT', decLφ, hT0 x hx, hφ0]
  have hT'l : ∀ x, 0 < x → DecLip0 (T' x) := fun x hx =>
    (hTl x hx).sub ((hL' x hx).const_mul κ)
  have hT'dil : DecDil T' := by
    intro Λ x s hΛ hx hs hΛs
    have h := hT Λ x s hΛ hx hs hΛs
    have hl := decLφ_dil φ hΛ hx s
    simp only [hT']
    rw [hDφ x s hx hs] at h
    linear_combination h - κ * hl
  obtain ⟨δ₂, L₂, hδ₂, -, h4', h8'⟩ := (hT'l 4 (by norm_num)).common (hT'l 8 (by norm_num))
  obtain ⟨G, hG0, hGl, hTG⟩ := dec_exists_scal hT'dil hT'0
    (fun x hx => (hT'l x hx).tendsto (hT'0 x hx)) hδ₂ h4' h8'
  have hGL : DecLip0 G := ⟨δ₂, 8 * L₂, hδ₂, hGl⟩
  obtain ⟨δ, L, hδ, hL, hG, hφ⟩ := hGL.common hφL
  refine ⟨G, φ, δ, L, hδ, hL, hG0, hφ0, hG, hφ, fun x s hx hs => ?_⟩
  have := hTG x s hx hs
  simp only [hT'] at this
  linear_combination this

end QED.GradedProof.RPi4

end
