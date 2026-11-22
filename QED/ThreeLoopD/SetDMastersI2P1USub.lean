/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Set (d), master `I₂`: substitutions on the Feynman-parameter triangle

Lower integrals of a measurable `g : ℝ → ℝ → ℝ≥0∞` over the triangle
`{u, v > 0, u + v < 1}` of the Feynman parameters `α₁ = (1 - w) x`, `α₂ = w`,
`α₃ = (1 - w)(1 - x)` of the set (d) master `I₂`:

* `(x, w) ↦ (α₁, α₂)` and `(x, w) ↦ (α₁, α₃)` carry `(1 - w) dx dw` to `du dv`
  (`QED.ThreeLoopD.i2P1US_xw_A`, `QED.ThreeLoopD.i2P1US_xw_C`);
* `u = s (1 - t) / (1 - s t)`, `v = t (1 - s) / (1 - s t)` maps the unit square onto the
  triangle with Jacobian `(1 - s)(1 - t) / (1 - s t)³`, and `u v / ((1 - u)(1 - v)) = s t`
  (`QED.ThreeLoopD.i2P1US_tri_sq`);
* `z = s t`: `∫∫ k(s) F(s t) ds dt = ∫ F(z) ∫_z^1 k(s) / s ds dz`
  (`QED.ThreeLoopD.i2P1US_sq_z`).

Each is a composition of one-dimensional substitutions and Tonelli swaps.
-/

@[expose] public section

open Real Set MeasureTheory Function
open scoped ENNReal

namespace QED.ThreeLoopD

/-- The scaling `a = l s` at fixed `l > 0`. -/
theorem i2P1US_scale {l : ℝ} (hl : 0 < l) (g : ℝ → ℝ≥0∞) :
    ∫⁻ a in Ioo (0 : ℝ) l, g a = ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal l * g (l * s) := by
  have hd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun s => l * s) l (Ioo 0 1) s :=
    fun s _ => ((hasDerivAt_id s).const_mul l).hasDerivWithinAt.congr_deriv (mul_one l)
  have hinj : InjOn (fun s : ℝ => l * s) (Ioo 0 1) :=
    fun s _ t _ h => mul_left_cancel₀ hl.ne' h
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hd hinj g
  rw [image_mul_left_Ioo hl, mul_zero, mul_one, abs_of_pos hl] at h
  exact h

/-- The reflection `a ↦ c - a` of `(0, c)`. -/
theorem i2P1US_reflect (c : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ a in Ioo (0 : ℝ) c, g (c - a) = ∫⁻ a in Ioo (0 : ℝ) c, g a := by
  have hd : ∀ a ∈ Ioo (0 : ℝ) c, HasDerivWithinAt (fun a => c - a) (-1) (Ioo 0 c) a :=
    fun a _ => ((hasDerivAt_id a).const_sub c).hasDerivWithinAt
  have hinj : InjOn (fun a : ℝ => c - a) (Ioo 0 c) := fun a _ b _ h => by simpa using h
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hd hinj g
  have himg : (fun a : ℝ => c - a) '' Ioo 0 c = Ioo 0 c := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨by linarith [ha.2], by linarith [ha.1]⟩
    · intro hb
      exact ⟨c - b, ⟨by linarith [hb.2], by linarith [hb.1]⟩, by ring⟩
  rw [himg] at h
  rw [h]
  simp

/-- **Tonelli on a region** of the unit square cut out by a measurable set `T`. -/
theorem i2P1US_swap_ind {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (uncurry f)) {T : Set (ℝ × ℝ)}
    (hT : MeasurableSet T) {J K : ℝ → Set ℝ}
    (hJ : ∀ a ∈ Ioo (0 : ℝ) 1, Prod.mk a ⁻¹' T ∩ Ioo 0 1 = J a)
    (hK : ∀ b ∈ Ioo (0 : ℝ) 1, (fun a => (a, b)) ⁻¹' T ∩ Ioo 0 1 = K b) :
    ∫⁻ a in Ioo (0 : ℝ) 1, ∫⁻ b in J a, f a b = ∫⁻ b in Ioo (0 : ℝ) 1, ∫⁻ a in K b, f a b := by
  have h1 : ∀ a ∈ Ioo (0 : ℝ) 1, ∫⁻ b in J a, f a b =
      ∫⁻ b in Ioo (0 : ℝ) 1, T.indicator (uncurry f) (a, b) := by
    intro a ha
    have e : (fun b => T.indicator (uncurry f) (a, b)) = (Prod.mk a ⁻¹' T).indicator (f a) := by
      funext b
      by_cases h : (a, b) ∈ T <;> simp [indicator, h]
    rw [e, lintegral_indicator (measurable_prodMk_left hT), Measure.restrict_restrict
      (measurable_prodMk_left hT), hJ a ha]
  have h2 : ∀ b ∈ Ioo (0 : ℝ) 1, ∫⁻ a in K b, f a b =
      ∫⁻ a in Ioo (0 : ℝ) 1, T.indicator (uncurry f) (a, b) := by
    intro b hb
    have e : (fun a => T.indicator (uncurry f) (a, b)) =
        ((fun a => (a, b)) ⁻¹' T).indicator (fun a => f a b) := by
      funext a
      by_cases h : (a, b) ∈ T <;> simp [indicator, h]
    rw [e, lintegral_indicator (measurable_prodMk_right hT), Measure.restrict_restrict
      (measurable_prodMk_right hT), hK b hb]
  rw [setLIntegral_congr_fun measurableSet_Ioo h1, setLIntegral_congr_fun measurableSet_Ioo h2]
  exact lintegral_lintegral_swap (f := fun a b => T.indicator (uncurry f) (a, b))
    (hf.indicator hT).aemeasurable

/-- Tonelli on the unit square. -/
theorem i2P1US_swap {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (uncurry f)) :
    ∫⁻ a in Ioo (0 : ℝ) 1, ∫⁻ b in Ioo (0 : ℝ) 1, f a b =
      ∫⁻ b in Ioo (0 : ℝ) 1, ∫⁻ a in Ioo (0 : ℝ) 1, f a b :=
  lintegral_lintegral_swap hf.aemeasurable

/-- The triangle `u + v < 1` in either order. -/
theorem i2P1US_tri_swap {g : ℝ → ℝ → ℝ≥0∞} (hg : Measurable (uncurry g)) :
    ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), g u v =
      ∫⁻ v in Ioo (0 : ℝ) 1, ∫⁻ u in Ioo (0 : ℝ) (1 - v), g u v := by
  refine i2P1US_swap_ind hg (T := {p | p.1 + p.2 < 1})
    (measurableSet_lt (by fun_prop) measurable_const) (fun a ha => ?_) (fun b hb => ?_)
  · ext b
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨h, h0, -⟩
      exact ⟨h0, by linarith⟩
    · rintro ⟨h0, h⟩
      exact ⟨by linarith, h0, by linarith [ha.1]⟩
  · ext a
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨h, h0, -⟩
      exact ⟨h0, by linarith⟩
    · rintro ⟨h0, h⟩
      exact ⟨by linarith, h0, by linarith [hb.1]⟩

/-- The region `z < s` in either order. -/
theorem i2P1US_lower_swap {g : ℝ → ℝ → ℝ≥0∞} (hg : Measurable (uncurry g)) :
    ∫⁻ s in Ioo (0 : ℝ) 1, ∫⁻ z in Ioo (0 : ℝ) s, g s z =
      ∫⁻ z in Ioo (0 : ℝ) 1, ∫⁻ s in Ioo z 1, g s z := by
  refine i2P1US_swap_ind hg (T := {p | p.2 < p.1})
    (measurableSet_lt measurable_snd measurable_fst) (fun a ha => ?_) (fun b hb => ?_)
  · ext b
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨h, h0, -⟩
      exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩
      exact ⟨h, h0, by linarith [ha.2]⟩
  · ext a
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨h, -, h1⟩
      exact ⟨h, h1⟩
    · rintro ⟨h, h1⟩
      exact ⟨h, by linarith [hb.1], h1⟩

/-- **`(x, w) ↦ (α₁, α₂) = ((1 - w) x, w)`** carries `(1 - w) dx dw` to the triangle. -/
theorem i2P1US_xw_A {g : ℝ → ℝ → ℝ≥0∞} (hg : Measurable (uncurry g)) :
    ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 - w) * g ((1 - w) * x) w =
      ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), g u v := by
  rw [i2P1US_swap (f := fun x w => ENNReal.ofReal (1 - w) * g ((1 - w) * x) w)
    (by
      have : Measurable fun p : ℝ × ℝ => g ((1 - p.2) * p.1) p.2 :=
        hg.comp (f := fun p : ℝ × ℝ => ((1 - p.2) * p.1, p.2)) (by fun_prop)
      exact (by fun_prop : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 - p.2)).mul this)]
  rw [setLIntegral_congr_fun measurableSet_Ioo fun w (hw : w ∈ Ioo (0 : ℝ) 1) =>
    (i2P1US_scale (by linarith [hw.2] : (0 : ℝ) < 1 - w) (fun u => g u w)).symm]
  exact i2P1US_tri_swap (g := fun a b => g b a) (hg.comp measurable_swap)

/-- **`(x, w) ↦ (α₁, α₃) = ((1 - w) x, (1 - w)(1 - x))`** carries `(1 - w) dx dw` to the
triangle. -/
theorem i2P1US_xw_C {g : ℝ → ℝ → ℝ≥0∞} (hg : Measurable (uncurry g)) :
    ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (1 - w) * g ((1 - w) * x) ((1 - w) * (1 - x)) =
      ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), g u v := by
  rw [i2P1US_swap (f := fun x w => ENNReal.ofReal (1 - w) * g ((1 - w) * x) ((1 - w) * (1 - x)))
    (by
      have : Measurable fun p : ℝ × ℝ => g ((1 - p.2) * p.1) ((1 - p.2) * (1 - p.1)) :=
        hg.comp (f := fun p : ℝ × ℝ => ((1 - p.2) * p.1, (1 - p.2) * (1 - p.1))) (by fun_prop)
      exact (by fun_prop : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 - p.2)).mul this)]
  have e : ∀ w ∈ Ioo (0 : ℝ) 1, ∫⁻ x in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (1 - w) * g ((1 - w) * x) ((1 - w) * (1 - x)) =
      ∫⁻ u in Ioo (0 : ℝ) (1 - w), g u (1 - w - u) := by
    intro w hw
    rw [i2P1US_scale (by linarith [hw.2] : (0 : ℝ) < 1 - w) (fun u => g u (1 - w - u))]
    refine lintegral_congr fun x => ?_
    rw [show 1 - w - (1 - w) * x = (1 - w) * (1 - x) by ring]
  rw [setLIntegral_congr_fun measurableSet_Ioo e]
  have hm : Measurable (uncurry fun a b => g b (1 - a - b)) :=
    hg.comp (f := fun p : ℝ × ℝ => (p.2, 1 - p.1 - p.2)) (by fun_prop)
  rw [i2P1US_tri_swap hm]
  refine setLIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
  have := i2P1US_reflect (1 - u) (fun v => g u v)
  rw [← this]
  refine lintegral_congr fun w => ?_
  rw [show 1 - w - u = 1 - u - w by ring]

/-- The Möbius substitution `u = s (1 - t) / (1 - s t)` of `(0, 1)` at fixed `t ∈ (0, 1)`. -/
theorem i2P1US_mobius {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (f : ℝ → ℝ≥0∞) :
    ∫⁻ u in Ioo (0 : ℝ) 1, f u = ∫⁻ s in Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((1 - t) / (1 - s * t) ^ 2) * f (s * (1 - t) / (1 - s * t)) := by
  obtain ⟨ht0, ht1⟩ := ht
  have hD : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < 1 - s * t := fun s hs => by nlinarith [hs.1, hs.2]
  have hd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun s => s * (1 - t) / (1 - s * t))
      ((1 - t) / (1 - s * t) ^ 2) (Ioo 0 1) s := fun s hs => by
    have h1 : HasDerivAt (fun s : ℝ => s * (1 - t)) (1 - t) s := by
      simpa using (hasDerivAt_id s).mul_const (1 - t)
    have h2 : HasDerivAt (fun s : ℝ => 1 - s * t) (-t) s := by
      simpa using ((hasDerivAt_id s).mul_const t).const_sub 1
    have := h1.div h2 (hD s hs).ne'
    refine this.hasDerivWithinAt.congr_deriv ?_
    field_simp
    ring
  have hinj : InjOn (fun s : ℝ => s * (1 - t) / (1 - s * t)) (Ioo 0 1) := fun a ha b hb h => by
    have h1 := (hD a ha).ne'
    have h2 := (hD b hb).ne'
    simp only at h
    rw [div_eq_div_iff h1 h2] at h
    have : (a - b) * (1 - t) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h3 | h3
    · linarith
    · exact absurd h3 (by linarith)
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hd hinj f
  have himg : (fun s : ℝ => s * (1 - t) / (1 - s * t)) '' Ioo 0 1 = Ioo 0 1 := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      have := hD s hs
      refine ⟨div_pos (mul_pos hs.1 (by linarith)) this, (div_lt_one this).2 ?_⟩
      nlinarith [hs.2]
    · intro hu
      have hE : 0 < 1 - t + u * t := by nlinarith [hu.1]
      refine ⟨u / (1 - t + u * t), ⟨div_pos hu.1 hE, (div_lt_one hE).2 (by nlinarith [hu.2])⟩,
        ?_⟩
      have : 1 - u / (1 - t + u * t) * t ≠ 0 := by
        rw [show 1 - u / (1 - t + u * t) * t = (1 - t) / (1 - t + u * t) by field_simp; ring]
        exact (div_pos (by linarith) hE).ne'
      simp only
      field_simp
      field_simp at this
      rw [div_eq_iff (by
        rw [show 1 - t + u * t - u * t = 1 - t by ring]; linarith)]
      ring
  rw [himg] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  rw [abs_of_pos (div_pos (by linarith) (pow_pos (hD s hs) 2))]

/-- **The triangle as the unit square**: `u = s (1 - t) / (1 - s t)`, `v = t (1 - s) / (1 - s t)`,
`du dv = (1 - s)(1 - t) / (1 - s t)³ ds dt`. -/
theorem i2P1US_tri_sq {g : ℝ → ℝ → ℝ≥0∞} (hg : Measurable (uncurry g)) :
    ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), g u v =
      ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ s in Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((1 - s) * (1 - t) / (1 - s * t) ^ 3) *
          g (s * (1 - t) / (1 - s * t)) (t * (1 - s) / (1 - s * t)) := by
  rw [setLIntegral_congr_fun measurableSet_Ioo fun u (hu : u ∈ Ioo (0 : ℝ) 1) =>
    i2P1US_scale (by linarith [hu.2] : (0 : ℝ) < 1 - u) (fun v => g u v)]
  rw [i2P1US_swap (f := fun u t => ENNReal.ofReal (1 - u) * g u ((1 - u) * t))
    ((by fun_prop : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 - p.1)).mul
      (hg.comp (f := fun p : ℝ × ℝ => (p.1, (1 - p.1) * p.2)) (by fun_prop)))]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  rw [i2P1US_mobius ht]
  refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  have hD : 0 < 1 - s * t := by nlinarith [hs.1, hs.2, ht.1, ht.2]
  have e1 : 1 - s * (1 - t) / (1 - s * t) = (1 - s) / (1 - s * t) := by
    field_simp
    ring
  have e2 : (1 - s) / (1 - s * t) * t = t * (1 - s) / (1 - s * t) := by ring
  rw [e1, e2, ← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (by linarith [ht.2])
    (pow_pos hD 2).le)]
  congr 2
  field_simp

/-- **`z = s t`**: `∫∫ k(s) F(s t) ds dt = ∫ F(z) ∫_z^1 k(s) / s ds dz`. -/
theorem i2P1US_sq_z {F k : ℝ → ℝ≥0∞} (hF : Measurable F) (hk : Measurable k) :
    ∫⁻ s in Ioo (0 : ℝ) 1, ∫⁻ t in Ioo (0 : ℝ) 1, k s * F (s * t) =
      ∫⁻ z in Ioo (0 : ℝ) 1, F z * ∫⁻ s in Ioo z 1, k s * ENNReal.ofReal (1 / s) := by
  have e : ∀ s ∈ Ioo (0 : ℝ) 1, ∫⁻ t in Ioo (0 : ℝ) 1, k s * F (s * t) =
      ∫⁻ z in Ioo (0 : ℝ) s, k s * ENNReal.ofReal (1 / s) * F z := by
    intro s hs
    have hm : Measurable fun t => F (s * t) := hF.comp (measurable_id.const_mul s)
    rw [lintegral_const_mul (k s) hm, lintegral_const_mul _ hF, i2P1US_scale hs.1 F,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [show k s * ENNReal.ofReal (1 / s) * (ENNReal.ofReal s * ∫⁻ t in Ioo (0 : ℝ) 1, F (s * t))
      = k s * (ENNReal.ofReal (1 / s) * ENNReal.ofReal s) * ∫⁻ t in Ioo (0 : ℝ) 1, F (s * t) by
        ring, ← ENNReal.ofReal_mul (by have := hs.1; positivity), one_div_mul_cancel hs.1.ne',
      ENNReal.ofReal_one, mul_one]
  rw [setLIntegral_congr_fun measurableSet_Ioo e, i2P1US_lower_swap (g := fun s z =>
    k s * ENNReal.ofReal (1 / s) * F z) ((hk.comp measurable_fst).mul
      ((by fun_prop : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.1))) |>.mul
      (hF.comp measurable_snd))]
  refine lintegral_congr fun z => ?_
  rw [lintegral_mul_const (F z) (f := fun s => k s * ENNReal.ofReal (1 / s))
    (hk.mul (by fun_prop)), mul_comm]

end QED.ThreeLoopD
