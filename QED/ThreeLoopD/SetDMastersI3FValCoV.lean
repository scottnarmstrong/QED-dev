/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI3FAnalytic
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Set (d), master `I₃`: `i3FInt 0` in photon and electron Feynman parameters

At `ε = 0` the integrand of `QED.ThreeLoopD.i3FInt` is `1 / ((1 + t) N)`, `N = i3FPoly`. Undoing
the Cheng–Wu normalization of `QED.ThreeLoopD.SetDMastersI3F`, put

  `d₁ = λ s (1 - u)`, `e₁ = λ s u`, `d₃ = λ (1 - s)(1 - v)`, `e₃ = λ (1 - s) v`,
  `λ = c / (s (1 - s) t)`, `c = x (1 - x)`,

(photon parameters `d₁, d₃`, electron parameters `e₁, e₃`, the bubble normalized to `c`). The
Jacobian of `(λ, s, u, v) ↦ (d₁, e₁, d₃, e₃)` is `λ³ s (1 - s)`, that of `t ↦ λ` is
`c / (s (1 - s) t²)`, and with

  `U = c (D + D') + D D'`, `F = U + c (e₁ + e₃)² + e₁² D' + e₃² D`, `D = d₁ + e₁`, `D' = d₃ + e₃`

one has `U = λ c (1 + t) / t` and `F = λ c N / (s (1 - s) t²)`, so the integrand becomes
`1 / (U F)` (`QED.ThreeLoopD.i3V_dens_cov`). The change of variables is done with lower
integrals: polar coordinates `(a, b) = (l s, l (1 - s))` on the quadrant three times
(`QED.ThreeLoopD.i3V_lintegral_polar`), the inversion `λ = k / t` and Tonelli swaps.

## Main results

* `QED.ThreeLoopD.i3V_lintegral_cov4`: the four-dimensional change of variables.
* `QED.ThreeLoopD.i3FInt_zero_eq_lintegral`: `i3FInt 0` is the real lower integral of
  `1 / (U F)` over `x ∈ (0, 1)` and `e₁, e₃, d₃, d₁ ∈ (0, ∞)`.
-/

@[expose] public section

open Real Set MeasureTheory
open scoped ENNReal

namespace QED.ThreeLoopD

/-- The shift `b = l - a` at fixed `a`. -/
theorem i3V_lintegral_shift (a : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ b in Ioi (0 : ℝ), g b = ∫⁻ l in Ioi a, g (l - a) := by
  have hd : ∀ l ∈ Ioi a, HasDerivWithinAt (fun l => l - a) 1 (Ioi a) l :=
    fun l _ => ((hasDerivAt_id l).sub_const a).hasDerivWithinAt
  have hinj : InjOn (fun l : ℝ => l - a) (Ioi a) := fun l _ m _ h => by simpa using h
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd hinj g
  have himg : (fun l : ℝ => l - a) '' Ioi a = Ioi 0 := by
    ext b; constructor
    · rintro ⟨l, hl, rfl⟩; exact sub_pos.2 (mem_Ioi.1 hl)
    · intro hb; exact ⟨b + a, by simpa using (mem_Ioi.1 hb), by ring⟩
  rw [himg] at h
  rw [h]; simp

/-- The scaling `a = l s` at fixed `l > 0`. -/
theorem i3V_lintegral_scale {l : ℝ} (hl : 0 < l) (g : ℝ → ℝ≥0∞) :
    ∫⁻ a in Ioo (0 : ℝ) l, g a = ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal l * g (l * s) := by
  have hd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun s => l * s) l (Ioo 0 1) s :=
    fun s _ => ((hasDerivAt_id s).const_mul l).hasDerivWithinAt.congr_deriv (mul_one l)
  have hinj : InjOn (fun s : ℝ => l * s) (Ioo 0 1) :=
    fun s _ t _ h => mul_left_cancel₀ hl.ne' h
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hd hinj g
  rw [image_mul_left_Ioo hl, mul_zero, mul_one, abs_of_pos hl] at h
  exact h

/-- **Polar coordinates on the quadrant**: `(a, b) = (l s, l (1 - s))`, Jacobian `l`. -/
theorem i3V_lintegral_polar {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a in Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ), f (a, b) =
      ∫⁻ l in Ioi (0 : ℝ), ∫⁻ s in Ioo (0 : ℝ) 1,
        ENNReal.ofReal l * f (l * s, l * (1 - s)) := by
  set T : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2} with hT
  have hTm : MeasurableSet T :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  set G : ℝ × ℝ → ℝ≥0∞ := T.indicator fun p => f (p.1, p.2 - p.1) with hG
  have hGm : Measurable G :=
    (hf.comp (measurable_fst.prodMk (measurable_snd.sub measurable_fst))).indicator hTm
  have h1 : ∀ a ∈ Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ), f (a, b) = ∫⁻ l, G (a, l) := by
    intro a ha
    rw [i3V_lintegral_shift a (fun b => f (a, b)), ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun l => ?_
    by_cases hl : a < l
    · simp [hG, hT, indicator, mem_Ioi.1 ha, hl]
    · simp [hG, hT, indicator, hl]
  have h2 : ∀ l ∈ Ioi (0 : ℝ), ∫⁻ a, G (a, l) = ∫⁻ s in Ioo (0 : ℝ) 1,
      ENNReal.ofReal l * f (l * s, l * (1 - s)) := by
    intro l hl
    have e : ∫⁻ a, G (a, l) = ∫⁻ a in Ioo (0 : ℝ) l, f (a, l - a) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      refine lintegral_congr fun a => ?_
      simp [hG, hT, indicator, mem_Ioo]
    rw [e, i3V_lintegral_scale hl (fun a => f (a, l - a))]
    refine setLIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
    simp only [mul_sub, mul_one]
  have h3 : ∀ a, a ∉ Ioi (0 : ℝ) → ∀ l, G (a, l) = 0 := by
    intro a ha l
    exact indicator_of_notMem (fun h => ha h.1) _
  have h4 : ∀ l, l ∉ Ioi (0 : ℝ) → ∀ a, G (a, l) = 0 := by
    intro l hl a
    exact indicator_of_notMem (fun h => hl (h.1.trans h.2)) _
  calc ∫⁻ a in Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ), f (a, b)
      = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ l, G (a, l) := setLIntegral_congr_fun measurableSet_Ioi h1
    _ = ∫⁻ a, ∫⁻ l, G (a, l) := by
        rw [← lintegral_indicator measurableSet_Ioi]
        refine lintegral_congr fun a => ?_
        by_cases ha : a ∈ Ioi (0 : ℝ)
        · simp [indicator, ha]
        · simp [indicator, ha, h3 a ha]
    _ = ∫⁻ l, ∫⁻ a, G (a, l) := lintegral_lintegral_swap hGm.aemeasurable
    _ = ∫⁻ l in Ioi (0 : ℝ), ∫⁻ a, G (a, l) := by
        rw [← lintegral_indicator measurableSet_Ioi]
        refine lintegral_congr fun l => ?_
        by_cases hl : l ∈ Ioi (0 : ℝ)
        · simp [indicator, hl]
        · simp [indicator, hl, h4 l hl]
    _ = _ := setLIntegral_congr_fun measurableSet_Ioi h2

/-- Tonelli for two set lower integrals over `ℝ`. -/
theorem i3V_swap {A B : Set ℝ} {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a in A, ∫⁻ b in B, f (a, b) = ∫⁻ b in B, ∫⁻ a in A, f (a, b) :=
  lintegral_lintegral_swap (f := fun a b => f (a, b)) hf.aemeasurable

/-- Measurability of a parametric set lower integral. -/
theorem i3V_meas_lint {α : Type*} [MeasurableSpace α] {A : Set ℝ} {f : α × ℝ → ℝ≥0∞}
    (hf : Measurable f) : Measurable fun a => ∫⁻ b in A, f (a, b) :=
  hf.lintegral_prod_right'

/-- **The four-dimensional change of variables** `(d₁, e₁, d₃, e₃) = (λ s (1 - u), λ s u,
λ (1 - s)(1 - v), λ (1 - s) v)`, Jacobian `λ³ s (1 - s)`. -/
theorem i3V_lintegral_cov4 {φ : ℝ × ℝ × ℝ × ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ e1 in Ioi (0 : ℝ), ∫⁻ e3 in Ioi (0 : ℝ), ∫⁻ d3 in Ioi (0 : ℝ), ∫⁻ d1 in Ioi (0 : ℝ),
        φ (d1, e1, d3, e3) =
      ∫⁻ s in Ioo (0 : ℝ) 1, ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) 1,
        ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal l * (ENNReal.ofReal (l * s) *
          (ENNReal.ofReal (l * (1 - s)) * φ (l * s * (1 - u), l * s * u,
            l * (1 - s) * (1 - v), l * (1 - s) * v))) := by
  -- Step A: reorder to `e₁, d₁, e₃, d₃`.
  have hA : ∀ e1 : ℝ, ∫⁻ e3 in Ioi (0 : ℝ), ∫⁻ d3 in Ioi (0 : ℝ), ∫⁻ d1 in Ioi (0 : ℝ),
      φ (d1, e1, d3, e3) = ∫⁻ d1 in Ioi (0 : ℝ), ∫⁻ e3 in Ioi (0 : ℝ),
        ∫⁻ d3 in Ioi (0 : ℝ), φ (d1, e1, d3, e3) := by
    intro e1
    have h1 : ∀ e3 : ℝ, ∫⁻ d3 in Ioi (0 : ℝ), ∫⁻ d1 in Ioi (0 : ℝ), φ (d1, e1, d3, e3) =
        ∫⁻ d1 in Ioi (0 : ℝ), ∫⁻ d3 in Ioi (0 : ℝ), φ (d1, e1, d3, e3) := fun e3 =>
      i3V_swap (f := fun q => φ (q.2, e1, q.1, e3)) (by fun_prop)
    simp_rw [h1]
    exact i3V_swap (f := fun q => ∫⁻ d3 in Ioi (0 : ℝ), φ (q.2, e1, d3, q.1))
      (i3V_meas_lint (f := fun q : (ℝ × ℝ) × ℝ => φ (q.1.2, e1, q.2, q.1.1)) (by fun_prop))
  simp_rw [hA]
  -- Step B: the inner polar coordinates `(e₃, d₃) = (D' v, D' (1 - v))`.
  have hB : ∀ e1 d1 : ℝ, ∫⁻ e3 in Ioi (0 : ℝ), ∫⁻ d3 in Ioi (0 : ℝ), φ (d1, e1, d3, e3) =
      ∫⁻ D' in Ioi (0 : ℝ), ∫⁻ v in Ioo (0 : ℝ) 1,
        ENNReal.ofReal D' * φ (d1, e1, D' * (1 - v), D' * v) := fun e1 d1 =>
    i3V_lintegral_polar (f := fun q => φ (d1, e1, q.2, q.1)) (by fun_prop)
  simp_rw [hB]
  -- Step C: the outer polar coordinates `(e₁, d₁) = (D u, D (1 - u))`.
  have hgm : Measurable fun q : ℝ × ℝ => ∫⁻ D' in Ioi (0 : ℝ), ∫⁻ v in Ioo (0 : ℝ) 1,
      ENNReal.ofReal D' * φ (q.2, q.1, D' * (1 - v), D' * v) :=
    i3V_meas_lint (f := fun r : (ℝ × ℝ) × ℝ => ∫⁻ v in Ioo (0 : ℝ) 1,
      ENNReal.ofReal r.2 * φ (r.1.2, r.1.1, r.2 * (1 - v), r.2 * v))
      (i3V_meas_lint (f := fun r : ((ℝ × ℝ) × ℝ) × ℝ =>
        ENNReal.ofReal r.1.2 * φ (r.1.1.2, r.1.1.1, r.1.2 * (1 - r.2), r.1.2 * r.2))
        (by fun_prop))
  rw [i3V_lintegral_polar hgm]
  -- Step D: move the `D'`-integral outside the `u`-integral.
  have hD : ∀ D : ℝ, ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal D *
      ∫⁻ D' in Ioi (0 : ℝ), ∫⁻ v in Ioo (0 : ℝ) 1,
        ENNReal.ofReal D' * φ (D * (1 - u), D * u, D' * (1 - v), D' * v) =
      ∫⁻ D' in Ioi (0 : ℝ), ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) 1,
        ENNReal.ofReal D * (ENNReal.ofReal D' *
          φ (D * (1 - u), D * u, D' * (1 - v), D' * v)) := by
    intro D
    simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact i3V_swap (f := fun q => ∫⁻ v in Ioo (0 : ℝ) 1, ENNReal.ofReal D *
      (ENNReal.ofReal q.2 * φ (D * (1 - q.1), D * q.1, q.2 * (1 - v), q.2 * v)))
      (i3V_meas_lint (f := fun r : (ℝ × ℝ) × ℝ => ENNReal.ofReal D *
        (ENNReal.ofReal r.1.2 * φ (D * (1 - r.1.1), D * r.1.1, r.1.2 * (1 - r.2),
          r.1.2 * r.2))) (by fun_prop))
  simp_rw [hD]
  -- Step E: polar coordinates `(D, D') = (λ s, λ (1 - s))`.
  have hkm : Measurable fun q : ℝ × ℝ => ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) 1,
      ENNReal.ofReal q.1 * (ENNReal.ofReal q.2 *
        φ (q.1 * (1 - u), q.1 * u, q.2 * (1 - v), q.2 * v)) :=
    i3V_meas_lint (f := fun r : (ℝ × ℝ) × ℝ => ∫⁻ v in Ioo (0 : ℝ) 1,
      ENNReal.ofReal r.1.1 * (ENNReal.ofReal r.1.2 *
        φ (r.1.1 * (1 - r.2), r.1.1 * r.2, r.1.2 * (1 - v), r.1.2 * v)))
      (i3V_meas_lint (f := fun r : ((ℝ × ℝ) × ℝ) × ℝ => ENNReal.ofReal r.1.1.1 *
        (ENNReal.ofReal r.1.1.2 * φ (r.1.1.1 * (1 - r.1.2), r.1.1.1 * r.1.2,
          r.1.1.2 * (1 - r.2), r.1.1.2 * r.2))) (by fun_prop))
  rw [i3V_lintegral_polar hkm]
  -- Step F: move the `λ`-integral innermost.
  have hF : ∀ s : ℝ, ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal l *
      ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (l * s) * (ENNReal.ofReal (l * (1 - s)) *
          φ (l * s * (1 - u), l * s * u, l * (1 - s) * (1 - v), l * (1 - s) * v)) =
      ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) 1, ∫⁻ l in Ioi (0 : ℝ),
        ENNReal.ofReal l * (ENNReal.ofReal (l * s) * (ENNReal.ofReal (l * (1 - s)) *
          φ (l * s * (1 - u), l * s * u, l * (1 - s) * (1 - v), l * (1 - s) * v))) := by
    intro s
    simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hm : Measurable fun r : ℝ × ℝ × ℝ => ENNReal.ofReal r.1 *
        (ENNReal.ofReal (r.1 * s) * (ENNReal.ofReal (r.1 * (1 - s)) *
          φ (r.1 * s * (1 - r.2.1), r.1 * s * r.2.1, r.1 * (1 - s) * (1 - r.2.2),
            r.1 * (1 - s) * r.2.2))) := by fun_prop
    rw [i3V_swap (f := fun q => ∫⁻ v in Ioo (0 : ℝ) 1, ENNReal.ofReal q.1 *
      (ENNReal.ofReal (q.1 * s) * (ENNReal.ofReal (q.1 * (1 - s)) *
        φ (q.1 * s * (1 - q.2), q.1 * s * q.2, q.1 * (1 - s) * (1 - v),
          q.1 * (1 - s) * v))))
      (i3V_meas_lint (f := fun r : (ℝ × ℝ) × ℝ => _)
        (hm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))))]
    refine setLIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
    exact i3V_swap (f := fun q => ENNReal.ofReal q.1 *
      (ENNReal.ofReal (q.1 * s) * (ENNReal.ofReal (q.1 * (1 - s)) *
        φ (q.1 * s * (1 - u), q.1 * s * u, q.1 * (1 - s) * (1 - q.2),
          q.1 * (1 - s) * q.2))))
      (hm.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
  have hsw := i3V_swap (A := Ioi (0 : ℝ)) (B := Ioo (0 : ℝ) 1)
    (f := fun q => ENNReal.ofReal q.1 * ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (q.1 * q.2) * (ENNReal.ofReal (q.1 * (1 - q.2)) *
        φ (q.1 * q.2 * (1 - u), q.1 * q.2 * u, q.1 * (1 - q.2) * (1 - v),
          q.1 * (1 - q.2) * v))) (measurable_fst.ennreal_ofReal.mul (hkm.comp
            ((measurable_fst.mul measurable_snd).prodMk
              (measurable_fst.mul (measurable_const.sub measurable_snd)))))
  rw [hsw]
  exact setLIntegral_congr_fun measurableSet_Ioo fun s _ => hF s

/-- `U = c (D + D') + D D'`, `D = d₁ + e₁`, `D' = d₃ + e₃`. -/
def i3VU (c d1 e1 d3 e3 : ℝ) : ℝ := c * (d1 + e1 + (d3 + e3)) + (d1 + e1) * (d3 + e3)

/-- `F = U + c (e₁ + e₃)² + e₁² D' + e₃² D`. -/
def i3VF (c d1 e1 d3 e3 : ℝ) : ℝ :=
  i3VU c d1 e1 d3 e3 + c * (e1 + e3) ^ 2 + e1 ^ 2 * (d3 + e3) + e3 ^ 2 * (d1 + e1)

/-- The integrand `1 / (U F)`. -/
noncomputable def i3VDens (c d1 e1 d3 e3 : ℝ) : ℝ := 1 / (i3VU c d1 e1 d3 e3 * i3VF c d1 e1 d3 e3)

/-- The integrand in the new variables. -/
theorem i3V_dens_cov {x s u v t : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (ht : 0 < t) :
    x * (1 - x) / (s * (1 - s)) / t ^ 2 * (x * (1 - x) / (s * (1 - s)) / t *
      (x * (1 - x) / (s * (1 - s)) / t * s * (x * (1 - x) / (s * (1 - s)) / t * (1 - s) *
        i3VDens (x * (1 - x)) (x * (1 - x) / (s * (1 - s)) / t * s * (1 - u))
          (x * (1 - x) / (s * (1 - s)) / t * s * u)
          (x * (1 - x) / (s * (1 - s)) / t * (1 - s) * (1 - v))
          (x * (1 - x) / (s * (1 - s)) / t * (1 - s) * v)))) =
      1 / ((1 + t) * i3FPoly x s u v t) := by
  have hN := i3FPoly_pos (u := u) (v := v) hx hs ht
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  have hs1 : 0 < 1 - s := by linarith [hs.2]
  have hσ : 0 < s * (1 - s) := mul_pos hs.1 hs1
  set c := x * (1 - x) with hcdef
  set l := c / (s * (1 - s)) / t with hl
  have hl0 : 0 < l := by positivity
  have hU : i3VU c (l * s * (1 - u)) (l * s * u) (l * (1 - s) * (1 - v)) (l * (1 - s) * v) =
      l * c * (1 + t) / t := by
    simp only [i3VU, hl]; field_simp; ring
  have hF : i3VF c (l * s * (1 - u)) (l * s * u) (l * (1 - s) * (1 - v)) (l * (1 - s) * v) =
      l * c * i3FPoly x s u v t / (s * (1 - s) * t ^ 2) := by
    rw [i3VF, hU]
    have h0 : s ≠ 0 := hs.1.ne'
    have h1 : 1 - s ≠ 0 := hs1.ne'
    have h2 : t ≠ 0 := ht.ne'
    simp only [i3FPoly, hl, hcdef]; field_simp; ring
  rw [i3VDens, hU, hF]
  have h0 : s ≠ 0 := hs.1.ne'
  have h1 : 1 - s ≠ 0 := hs1.ne'
  have h2 : t ≠ 0 := ht.ne'
  have h3 : i3FPoly x s u v t ≠ 0 := hN.ne'
  rw [hl]
  field_simp


/-- The inversion `λ = k / t`. -/
theorem i3V_lintegral_inv {k : ℝ} (hk : 0 < k) (g : ℝ → ℝ≥0∞) :
    ∫⁻ l in Ioi (0 : ℝ), g l = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (k / t ^ 2) * g (k / t) := by
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun t => k / t) (-(k / t ^ 2)) (Ioi 0) t := by
    intro t ht
    have h := (hasDerivAt_inv (ne_of_gt ht)).const_mul k
    refine (h.congr_deriv ?_).hasDerivWithinAt.congr_of_mem (fun y _ => div_eq_mul_inv k y) ht
    ring
  have hinj : InjOn (fun t : ℝ => k / t) (Ioi 0) := by
    intro a ha b hb hab
    simp only at hab
    rw [div_eq_div_iff (ne_of_gt (mem_Ioi.1 ha)) (ne_of_gt (mem_Ioi.1 hb))] at hab
    exact (mul_left_cancel₀ hk.ne' hab).symm
  have himg : (fun t : ℝ => k / t) '' Ioi 0 = Ioi 0 := by
    ext l; constructor
    · rintro ⟨t, ht, rfl⟩; exact div_pos hk ht
    · intro hl
      exact ⟨k / l, div_pos hk hl, by field_simp [ne_of_gt (mem_Ioi.1 hl)]⟩
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd hinj g
  rw [himg] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [abs_neg, abs_of_pos (div_pos hk (pow_pos (mem_Ioi.1 ht) 2))]

/-- Measurability of the integrand. -/
theorem measurable_i3VDens (c : ℝ) :
    Measurable fun p : ℝ × ℝ × ℝ × ℝ => ENNReal.ofReal (i3VDens c p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold i3VDens i3VF i3VU; fun_prop

/-- **The change of variables at fixed `x`.** -/
theorem i3V_inner {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫⁻ s in Ioo (0 : ℝ) 1, ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) 1, ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (1 / ((1 + t) * i3FPoly x s u v t)) =
      ∫⁻ e1 in Ioi (0 : ℝ), ∫⁻ e3 in Ioi (0 : ℝ), ∫⁻ d3 in Ioi (0 : ℝ), ∫⁻ d1 in Ioi (0 : ℝ),
        ENNReal.ofReal (i3VDens (x * (1 - x)) d1 e1 d3 e3) := by
  rw [i3V_lintegral_cov4 (measurable_i3VDens (x * (1 - x)))]
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  refine setLIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
  refine setLIntegral_congr_fun measurableSet_Ioo fun v _ => ?_
  have hs1 : 0 < 1 - s := by linarith [hs.2]
  have hk : 0 < x * (1 - x) / (s * (1 - s)) := div_pos hc (mul_pos hs.1 hs1)
  conv_rhs => rw [i3V_lintegral_inv hk]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have hl : 0 < x * (1 - x) / (s * (1 - s)) / t := div_pos hk ht0
  dsimp only
  rw [← ENNReal.ofReal_mul (mul_pos hl hs1).le, ← ENNReal.ofReal_mul (mul_pos hl hs.1).le,
    ← ENNReal.ofReal_mul hl.le, ← ENNReal.ofReal_mul (by positivity)]
  rw [i3V_dens_cov hx hs ht0]

/-- **`i3FInt 0` as a four-fold photon/electron parametric integral.** -/
theorem i3FInt_zero_eq_lintegral :
    i3FInt 0 = (((∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ e1 in Ioi (0 : ℝ), ∫⁻ e3 in Ioi (0 : ℝ),
      ∫⁻ d3 in Ioi (0 : ℝ), ∫⁻ d1 in Ioi (0 : ℝ),
        ENNReal.ofReal (i3VDens (x * (1 - x)) d1 e1 d3 e3)).toReal : ℝ) : ℂ) := by
  set g : ℝ × ℝ × ℝ × ℝ × ℝ → ℝ := fun z =>
    1 / ((1 + z.2.2.2.2) * i3FPoly z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) with hg
  have hgm : Measurable g := by rw [hg]; unfold i3FPoly; fun_prop
  have hI : ∀ z, i3FIntegrand 0 z = (g z : ℂ) := by
    intro z
    simp only [i3FIntegrand, hg, mul_zero, Complex.cpow_zero, one_mul, zero_sub, sub_zero,
      Complex.cpow_neg_one]
    push_cast
    rw [one_div, mul_inv]
  rw [i3FInt_eq]
  simp_rw [hI]
  rw [integral_complex_ofReal]
  congr 1
  have hpos : 0 ≤ᵐ[volume.restrict i3FDom] g := by
    filter_upwards [ae_restrict_mem (by measurability : MeasurableSet i3FDom)] with z hz
    have ht : 0 < z.2.2.2.2 := hz.2.2.2.2
    have hN := i3FPoly_pos (u := z.2.2.1) (v := z.2.2.2.1) hz.1 hz.2.1 ht
    simp only [Pi.zero_apply, hg]
    positivity
  rw [integral_eq_lintegral_of_nonneg_ae hpos hgm.aestronglyMeasurable]
  congr 1
  rw [volume_restrict_prod5]
  rw [lintegral_prod _ hgm.ennreal_ofReal.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have m1 : Measurable fun y : ℝ × ℝ × ℝ × ℝ => ENNReal.ofReal (g (x, y)) := by fun_prop
  rw [← i3V_inner hx, lintegral_prod _ m1.aemeasurable]
  refine lintegral_congr fun s => ?_
  have m2 : Measurable fun y : ℝ × ℝ × ℝ => ENNReal.ofReal (g (x, s, y)) := by fun_prop
  rw [lintegral_prod _ m2.aemeasurable]
  refine lintegral_congr fun u => ?_
  have m3 : Measurable fun y : ℝ × ℝ => ENNReal.ofReal (g (x, s, u, y)) := by fun_prop
  rw [lintegral_prod _ m3.aemeasurable]

end QED.ThreeLoopD
