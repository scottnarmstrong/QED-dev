/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLShuffle
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Parametric integrals that are harmonic polylogarithms

Tools for proving identities `∫_{v ∈ s} g(v, x) dv = G(x)` on an interval `p < x < q`, where `G`
is typically a linear combination of harmonic polylogarithms (HPLs) of `x`, or of `φ(x)` for a
change of variables `φ`. The method is the differential-equation method:

1. differentiate under the integral sign (`hasDerivAt_setIntegral_param`, a local-domination
   form of `hasDerivAt_integral_of_dominated_loc_of_deriv_le` adapted to integrals over a
   measurable set `s` with a parameter in an open interval);
2. reduce the differentiated integrand by an exact pointwise identity
   `∂ₓ g = k + ∂ᵥ h` and the fundamental theorem of calculus in `v` with limits at the ends
   (`setIntegral_Ioo_eq_add_of_eq_add_deriv`);
3. match the derivative with that of the HPL combination (`hplSum`, with derivative
   `hasDerivAt_hplSum_prepend` and the chain rule `hasDerivAt_hplSum_prepend_comp`);
4. match one boundary value: a limit at an end of `(p, q)` (`tendsto_setIntegral_param`, by
   dominated convergence; `tendsto_hplSum_zero`, `tendsto_hplSum_one`) or a value at an interior
   point, and conclude by uniqueness (`eqOn_of_hasDerivAt_of_tendsto_left`, ...).

The main packaged statements are `eqOn_setIntegral_of_hasDerivAt_left` (limit at the left end),
`eqOn_setIntegral_of_hasDerivAt_right` (limit at the right end) and
`eqOn_setIntegral_of_hasDerivAt_of_eq` (value at an interior point). Nothing here is specific
to a particular integral: the integration set `s`, the parameter interval and the target `G` are
arbitrary.

## Main definitions

* `QED.Polylog.ParamHPL.hplSum c x = ∑ᵢ cᵢ H(wᵢ; x)` for a list `c` of pairs `(cᵢ, wᵢ)`.
* `QED.Polylog.ParamHPL.prepend a c`: every word of `c` prefixed with the letter `a`.

## Main results

* `QED.Polylog.ParamHPL.hasDerivAt_setIntegral_param`: differentiation under `∫_s`.
* `QED.Polylog.ParamHPL.eqOn_setIntegral_of_hasDerivAt_left`: the packaged method.
* `QED.Polylog.ParamHPL.hasDerivAt_hplSum_prepend`:
  `d/dx hplSum (prepend a c) x = f a x · hplSum c x` on `(0, 1)`.
* `QED.Polylog.ParamHPL.integrableOn_abs_log_pow_Ioo`: `|log v|ⁿ` is integrable on `(0, 1)`
  (a dominating function for log moments).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory Metric

namespace QED.Polylog.ParamHPL

open QED.Polylog.HPL

/-! ### Uniqueness from the derivative -/

/-- Two functions with the same derivative on `(p, q)` and the same right limit at `p` agree
on `(p, q)`. -/
theorem eqOn_of_hasDerivAt_of_tendsto_left {F G D : ℝ → ℝ} {p q c : ℝ} (hpq : p < q)
    (hF : ∀ x ∈ Ioo p q, HasDerivAt F (D x) x) (hG : ∀ x ∈ Ioo p q, HasDerivAt G (D x) x)
    (hFp : Tendsto F (𝓝[>] p) (𝓝 c)) (hGp : Tendsto G (𝓝[>] p) (𝓝 c)) :
    EqOn F G (Ioo p q) := by
  have h := eq_of_hasDerivAt_zero_of_tendsto_right (F := fun x => F x - G x) (c := 0) hpq
    (fun x hx => by
      have h := (hF x hx).sub (hG x hx); rwa [sub_self] at h) (by simpa using hFp.sub hGp)
  intro x hx
  linarith [h x hx]

/-- Two functions with the same derivative on `(p, q)` and the same left limit at `q` agree
on `(p, q)`. -/
theorem eqOn_of_hasDerivAt_of_tendsto_right {F G D : ℝ → ℝ} {p q c : ℝ} (hpq : p < q)
    (hF : ∀ x ∈ Ioo p q, HasDerivAt F (D x) x) (hG : ∀ x ∈ Ioo p q, HasDerivAt G (D x) x)
    (hFq : Tendsto F (𝓝[<] q) (𝓝 c)) (hGq : Tendsto G (𝓝[<] q) (𝓝 c)) :
    EqOn F G (Ioo p q) := by
  have h := eq_of_hasDerivAt_zero_of_tendsto_left (F := fun x => F x - G x) (c := 0) hpq
    (fun x hx => by
      have h := (hF x hx).sub (hG x hx); rwa [sub_self] at h) (by simpa using hFq.sub hGq)
  intro x hx
  linarith [h x hx]

/-- Two functions with the same derivative on `(p, q)` that agree at one point of `(p, q)` agree
on `(p, q)`. -/
theorem eqOn_of_hasDerivAt_of_eq {F G D : ℝ → ℝ} {p q x₀ : ℝ} (hx₀ : x₀ ∈ Ioo p q)
    (hF : ∀ x ∈ Ioo p q, HasDerivAt F (D x) x) (hG : ∀ x ∈ Ioo p q, HasDerivAt G (D x) x)
    (h₀ : F x₀ = G x₀) : EqOn F G (Ioo p q) := by
  intro x hx
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero (f := fun y => F y - G y)
    isPreconnected_Ioo
    (fun z hz => ((hF z hz).sub (hG z hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => ((hF z hz).sub (hG z hz)).deriv.trans (sub_self _)) hx hx₀
  linarith

/-! ### Differentiation under the integral sign -/

/-- Differentiation of `x ↦ ∫_{v ∈ s} g v x` at a point `x` of an open interval `(p, q)`, under a
domination of the `x`-derivative uniform for parameters of `(p, q)` close to `x`. -/
theorem hasDerivAt_setIntegral_param {g g' : ℝ → ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {p q x : ℝ} (hx : x ∈ Ioo p q)
    (hmeas : ∀ y ∈ Ioo p q, AEStronglyMeasurable (fun v => g v y) (volume.restrict s))
    (hint : IntegrableOn (fun v => g v x) s)
    (hmeas' : AEStronglyMeasurable (fun v => g' v x) (volume.restrict s))
    {δ : ℝ} (hδ : 0 < δ) {B : ℝ → ℝ} (hB : IntegrableOn B s)
    (hbound : ∀ v ∈ s, ∀ y ∈ Ioo p q, |y - x| < δ → |g' v y| ≤ B v)
    (hderiv : ∀ v ∈ s, ∀ y ∈ Ioo p q, HasDerivAt (g v) (g' v y) y) :
    IntegrableOn (fun v => g' v x) s ∧
      HasDerivAt (fun y => ∫ v in s, g v y) (∫ v in s, g' v x) x := by
  have hUn : Ioo p q ∩ ball x δ ∈ 𝓝 x :=
    (isOpen_Ioo.inter isOpen_ball).mem_nhds ⟨hx, mem_ball_self hδ⟩
  have hs_meas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (fun v => g v y) (volume.restrict s) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using hmeas y hy
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict s)
    (F := fun y v => g v y) (F' := fun y v => g' v y) (x₀ := x) (bound := B) hUn hs_meas hint
    hmeas' ?_ hB ?_
  · refine (ae_restrict_iff' hs).2 (ae_of_all _ fun v hv y hy => ?_)
    rw [Real.norm_eq_abs]
    exact hbound v hv y hy.1 (by simpa [Real.dist_eq] using hy.2)
  · exact (ae_restrict_iff' hs).2 (ae_of_all _ fun v hv y hy => hderiv v hv y hy.1)

/-- The derivative of `x ↦ ∫_{v ∈ s} g v x` on `(p, q)`, from a local domination at every point
of `(p, q)`. -/
theorem hasDerivAt_setIntegral_param_of_forall {g g' : ℝ → ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) {p q : ℝ}
    (hmeas : ∀ y ∈ Ioo p q, AEStronglyMeasurable (fun v => g v y) (volume.restrict s))
    (hint : ∀ y ∈ Ioo p q, IntegrableOn (fun v => g v y) s)
    (hmeas' : ∀ y ∈ Ioo p q, AEStronglyMeasurable (fun v => g' v y) (volume.restrict s))
    (hdom : ∀ x ∈ Ioo p q, ∃ δ > 0, ∃ B : ℝ → ℝ, IntegrableOn B s ∧
      ∀ v ∈ s, ∀ y ∈ Ioo p q, |y - x| < δ → |g' v y| ≤ B v)
    (hderiv : ∀ v ∈ s, ∀ y ∈ Ioo p q, HasDerivAt (g v) (g' v y) y) :
    ∀ x ∈ Ioo p q, HasDerivAt (fun y => ∫ v in s, g v y) (∫ v in s, g' v x) x := by
  intro x hx
  obtain ⟨δ, hδ, B, hB, hb⟩ := hdom x hx
  exact (hasDerivAt_setIntegral_param hs hx hmeas (hint x hx) (hmeas' x hx) hδ hB hb
    hderiv).2

/-! ### Limits of parametric integrals -/

/-- Dominated convergence for `∫_{v ∈ s} g v x` along any countably generated filter `l` on the
parameter. -/
theorem tendsto_setIntegral_param {g : ℝ → ℝ → ℝ} {g₀ : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) {l : Filter ℝ} [l.IsCountablyGenerated] {B : ℝ → ℝ}
    (hmeas : ∀ᶠ y in l, AEStronglyMeasurable (fun v => g v y) (volume.restrict s))
    (hbound : ∀ᶠ y in l, ∀ v ∈ s, |g v y| ≤ B v) (hB : IntegrableOn B s)
    (hlim : ∀ v ∈ s, Tendsto (g v) l (𝓝 (g₀ v))) :
    Tendsto (fun y => ∫ v in s, g v y) l (𝓝 (∫ v in s, g₀ v)) := by
  refine tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict s)
    (F := fun y v => g v y) B hmeas ?_ hB ((ae_restrict_iff' hs).2 (ae_of_all _ hlim))
  filter_upwards [hbound] with y hy
  exact (ae_restrict_iff' hs).2 (ae_of_all _ fun v hv => by
    rw [Real.norm_eq_abs]; exact hy v hv)

/-! ### Reduction of the differentiated integrand -/

/-- The fundamental theorem of calculus on `(a, b)` with one-sided limits at the ends:
`∫_{(a, b)} h' = h(b⁻) - h(a⁺)`. -/
theorem setIntegral_Ioo_deriv {h h' : ℝ → ℝ} {a b ha hb : ℝ} (hab : a < b)
    (hd : ∀ v ∈ Ioo a b, HasDerivAt h (h' v) v) (hi : IntegrableOn h' (Ioo a b))
    (hla : Tendsto h (𝓝[>] a) (𝓝 ha)) (hlb : Tendsto h (𝓝[<] b) (𝓝 hb)) :
    ∫ v in Ioo a b, h' v = hb - ha := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab hd ?_ hla hlb
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]
  exact hi

/-- Reduction by an exact identity `f = k + ∂ᵥ h` on `(a, b)`:
`∫_{(a, b)} f = ∫_{(a, b)} k + h(b⁻) - h(a⁺)`. -/
theorem setIntegral_Ioo_eq_add_of_eq_add_deriv {f k h h' : ℝ → ℝ} {a b ha hb : ℝ}
    (hab : a < b) (hfk : ∀ v ∈ Ioo a b, f v = k v + h' v) (hk : IntegrableOn k (Ioo a b))
    (hd : ∀ v ∈ Ioo a b, HasDerivAt h (h' v) v) (hi : IntegrableOn h' (Ioo a b))
    (hla : Tendsto h (𝓝[>] a) (𝓝 ha)) (hlb : Tendsto h (𝓝[<] b) (𝓝 hb)) :
    ∫ v in Ioo a b, f v = (∫ v in Ioo a b, k v) + (hb - ha) := by
  rw [setIntegral_congr_fun measurableSet_Ioo hfk, integral_add hk hi,
    setIntegral_Ioo_deriv hab hd hi hla hlb]

/-! ### The packaged method -/

/-- **Parametric integral = target, by the derivative and the left limit.** If
`F x = ∫_{v ∈ s} g v x` has the locally dominated derivative `∫ g' v x` on `(p, q)`, `G` has the
same derivative there, and `F`, `G` have the same right limit at `p`, then `F = G` on `(p, q)`. -/
theorem eqOn_setIntegral_of_hasDerivAt_left {g g' : ℝ → ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) {p q c : ℝ} (hpq : p < q) {G : ℝ → ℝ}
    (hmeas : ∀ y ∈ Ioo p q, AEStronglyMeasurable (fun v => g v y) (volume.restrict s))
    (hint : ∀ y ∈ Ioo p q, IntegrableOn (fun v => g v y) s)
    (hmeas' : ∀ y ∈ Ioo p q, AEStronglyMeasurable (fun v => g' v y) (volume.restrict s))
    (hdom : ∀ x ∈ Ioo p q, ∃ δ > 0, ∃ B : ℝ → ℝ, IntegrableOn B s ∧
      ∀ v ∈ s, ∀ y ∈ Ioo p q, |y - x| < δ → |g' v y| ≤ B v)
    (hderiv : ∀ v ∈ s, ∀ y ∈ Ioo p q, HasDerivAt (g v) (g' v y) y)
    (hG : ∀ x ∈ Ioo p q, HasDerivAt G (∫ v in s, g' v x) x)
    (hFp : Tendsto (fun y => ∫ v in s, g v y) (𝓝[>] p) (𝓝 c)) (hGp : Tendsto G (𝓝[>] p) (𝓝 c)) :
    ∀ x ∈ Ioo p q, ∫ v in s, g v x = G x :=
  eqOn_of_hasDerivAt_of_tendsto_left hpq
    (hasDerivAt_setIntegral_param_of_forall hs hmeas hint hmeas' hdom hderiv) hG hFp hGp

/-- **Parametric integral = target, by the derivative and the right limit.** -/
theorem eqOn_setIntegral_of_hasDerivAt_right {g g' : ℝ → ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) {p q c : ℝ} (hpq : p < q) {G : ℝ → ℝ}
    (hmeas : ∀ y ∈ Ioo p q, AEStronglyMeasurable (fun v => g v y) (volume.restrict s))
    (hint : ∀ y ∈ Ioo p q, IntegrableOn (fun v => g v y) s)
    (hmeas' : ∀ y ∈ Ioo p q, AEStronglyMeasurable (fun v => g' v y) (volume.restrict s))
    (hdom : ∀ x ∈ Ioo p q, ∃ δ > 0, ∃ B : ℝ → ℝ, IntegrableOn B s ∧
      ∀ v ∈ s, ∀ y ∈ Ioo p q, |y - x| < δ → |g' v y| ≤ B v)
    (hderiv : ∀ v ∈ s, ∀ y ∈ Ioo p q, HasDerivAt (g v) (g' v y) y)
    (hG : ∀ x ∈ Ioo p q, HasDerivAt G (∫ v in s, g' v x) x)
    (hFq : Tendsto (fun y => ∫ v in s, g v y) (𝓝[<] q) (𝓝 c)) (hGq : Tendsto G (𝓝[<] q) (𝓝 c)) :
    ∀ x ∈ Ioo p q, ∫ v in s, g v x = G x :=
  eqOn_of_hasDerivAt_of_tendsto_right hpq
    (hasDerivAt_setIntegral_param_of_forall hs hmeas hint hmeas' hdom hderiv) hG hFq hGq

/-- **Parametric integral = target, by the derivative and the value at one point.** -/
theorem eqOn_setIntegral_of_hasDerivAt_of_eq {g g' : ℝ → ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) {p q x₀ : ℝ} (hx₀ : x₀ ∈ Ioo p q) {G : ℝ → ℝ}
    (hmeas : ∀ y ∈ Ioo p q, AEStronglyMeasurable (fun v => g v y) (volume.restrict s))
    (hint : ∀ y ∈ Ioo p q, IntegrableOn (fun v => g v y) s)
    (hmeas' : ∀ y ∈ Ioo p q, AEStronglyMeasurable (fun v => g' v y) (volume.restrict s))
    (hdom : ∀ x ∈ Ioo p q, ∃ δ > 0, ∃ B : ℝ → ℝ, IntegrableOn B s ∧
      ∀ v ∈ s, ∀ y ∈ Ioo p q, |y - x| < δ → |g' v y| ≤ B v)
    (hderiv : ∀ v ∈ s, ∀ y ∈ Ioo p q, HasDerivAt (g v) (g' v y) y)
    (hG : ∀ x ∈ Ioo p q, HasDerivAt G (∫ v in s, g' v x) x)
    (h₀ : ∫ v in s, g v x₀ = G x₀) :
    ∀ x ∈ Ioo p q, ∫ v in s, g v x = G x :=
  eqOn_of_hasDerivAt_of_eq hx₀
    (hasDerivAt_setIntegral_param_of_forall hs hmeas hint hmeas' hdom hderiv) hG h₀

/-! ### Linear combinations of harmonic polylogarithms -/

/-- The linear combination `∑ᵢ cᵢ H(wᵢ; x)` of HPLs, for a list `c` of pairs `(cᵢ, wᵢ)`. -/
noncomputable def hplSum (c : List (ℝ × List Letter)) (x : ℝ) : ℝ :=
  (c.map fun e => e.1 * hpl e.2 x).sum

/-- Every word of `c` prefixed with the letter `a`. -/
def prepend (a : Letter) (c : List (ℝ × List Letter)) : List (ℝ × List Letter) :=
  c.map fun e => (e.1, a :: e.2)

@[simp] theorem hplSum_nil (x : ℝ) : hplSum [] x = 0 := rfl

@[simp] theorem hplSum_cons (e : ℝ × List Letter) (c : List (ℝ × List Letter)) (x : ℝ) :
    hplSum (e :: c) x = e.1 * hpl e.2 x + hplSum c x := by
  simp [hplSum]

theorem hplSum_append (c d : List (ℝ × List Letter)) (x : ℝ) :
    hplSum (c ++ d) x = hplSum c x + hplSum d x := by
  simp [hplSum]

@[simp] theorem prepend_nil (a : Letter) : prepend a [] = [] := rfl

@[simp] theorem prepend_cons (a : Letter) (e : ℝ × List Letter) (c : List (ℝ × List Letter)) :
    prepend a (e :: c) = (e.1, a :: e.2) :: prepend a c := rfl

/-- The constant word: `H([]; x) = 1`. -/
theorem hplSum_const (r : ℝ) (x : ℝ) : hplSum [(r, [])] x = r := by
  simp [hpl]

/-- `d/dx hplSum (prepend a c) x = f a x · hplSum c x` on `(0, 1)`. -/
theorem hasDerivAt_hplSum_prepend (a : Letter) (c : List (ℝ × List Letter)) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (hplSum (prepend a c)) (a.kernel x * hplSum c x) x := by
  induction c with
  | nil =>
    simp only [prepend_nil, hplSum_nil, mul_zero]
    rw [show hplSum [] = fun _ => (0 : ℝ) from funext hplSum_nil]
    exact hasDerivAt_const x 0
  | cons e c ih =>
    have h := ((hasDerivAt_hpl_cons a e.2 hx).const_mul e.1).add ih
    have hf : hplSum (prepend a (e :: c)) = fun y => e.1 * hpl (a :: e.2) y +
        hplSum (prepend a c) y := funext fun y => by simp
    rw [hf]
    convert h using 1
    simp only [hplSum_cons]
    ring

/-- The chain rule for `hplSum (prepend a c) ∘ φ`. -/
theorem hasDerivAt_hplSum_prepend_comp (a : Letter) (c : List (ℝ × List Letter)) {φ : ℝ → ℝ}
    {φ' z : ℝ} (hφ : HasDerivAt φ φ' z) (hz : φ z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => hplSum (prepend a c) (φ y)) (a.kernel (φ z) * φ' * hplSum c (φ z))
      z := by
  exact ((hasDerivAt_hplSum_prepend a c hz).comp z hφ).congr_deriv (by ring)

/-- The general combination grouped by first letter, `r + ∑ c₀ H(0 ·) + ∑ c₁ H(1 ·) +
∑ c₋₁ H(-1 ·)`, has derivative `c₀(x)/x + c₁(x)/(1 - x) + c₋₁(x)/(1 + x)` on `(0, 1)`. -/
theorem hasDerivAt_hplSum_letters (r : ℝ) (c₀ c₁ c₂ : List (ℝ × List Letter)) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (hplSum ((r, []) :: (prepend .zero c₀ ++ prepend .one c₁ ++ prepend .negOne c₂)))
      (x⁻¹ * hplSum c₀ x + (1 - x)⁻¹ * hplSum c₁ x + (1 + x)⁻¹ * hplSum c₂ x) x := by
  have hf : hplSum ((r, []) :: (prepend .zero c₀ ++ prepend .one c₁ ++ prepend .negOne c₂)) =
      fun y => r + (hplSum (prepend .zero c₀) y + hplSum (prepend .one c₁) y +
        hplSum (prepend .negOne c₂) y) := funext fun y => by
    simp [hplSum_append, hpl, add_assoc]
  rw [hf]
  have h := (((hasDerivAt_hplSum_prepend .zero c₀ hx).add
    (hasDerivAt_hplSum_prepend .one c₁ hx)).add
    (hasDerivAt_hplSum_prepend .negOne c₂ hx)).const_add r
  simpa using h

/-- The chain rule for the general combination of `hasDerivAt_hplSum_letters`. -/
theorem hasDerivAt_hplSum_letters_comp (r : ℝ) (c₀ c₁ c₂ : List (ℝ × List Letter))
    {φ : ℝ → ℝ} {φ' z : ℝ} (hφ : HasDerivAt φ φ' z) (hz : φ z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => hplSum ((r, []) ::
        (prepend .zero c₀ ++ prepend .one c₁ ++ prepend .negOne c₂)) (φ y))
      (((φ z)⁻¹ * hplSum c₀ (φ z) + (1 - φ z)⁻¹ * hplSum c₁ (φ z) +
        (1 + φ z)⁻¹ * hplSum c₂ (φ z)) * φ') z :=
  (hasDerivAt_hplSum_letters r c₀ c₁ c₂ hz).comp z hφ

/-- A combination of words none of which is all zeros tends to `0` at `0⁺`. -/
theorem tendsto_hplSum_zero {c : List (ℝ × List Letter)} (hc : ∀ e ∈ c, ¬AllZero e.2) :
    Tendsto (hplSum c) (𝓝[>] 0) (𝓝 0) := by
  induction c with
  | nil =>
    rw [show hplSum [] = fun _ => (0 : ℝ) from funext hplSum_nil]
    exact tendsto_const_nhds
  | cons e c ih =>
    have h1 := (tendsto_hpl_zero (hc e (by simp))).const_mul e.1
    have h2 := ih fun e' he' => hc e' (by simp [he'])
    have := h1.add h2
    simp only [mul_zero, add_zero] at this
    refine this.congr fun y => ?_
    simp

/-- The prefix by a letter `a ≠ 0` gives words that are not all zeros. -/
theorem not_allZero_of_mem_prepend {a : Letter} (ha : a ≠ Letter.zero)
    {c : List (ℝ × List Letter)} : ∀ e ∈ prepend a c, ¬AllZero e.2 := by
  intro e he h
  simp only [prepend, List.mem_map] at he
  obtain ⟨e', -, rfl⟩ := he
  exact ha (h a (by simp))

/-- A combination of words, each empty or with first letter `≠ 1`, is continuous at `1⁻`. -/
theorem tendsto_hplSum_one {c : List (ℝ × List Letter)}
    (hc : ∀ e ∈ c, e.2.head? ≠ some Letter.one) :
    Tendsto (hplSum c) (𝓝[<] 1) (𝓝 (hplSum c 1)) := by
  induction c with
  | nil =>
    rw [show hplSum [] = fun _ => (0 : ℝ) from funext hplSum_nil]
    exact tendsto_const_nhds
  | cons e c ih =>
    have h2 := ih fun e' he' => hc e' (by simp [he'])
    have h1 : Tendsto (fun y => e.1 * hpl e.2 y) (𝓝[<] 1) (𝓝 (e.1 * hpl e.2 1)) := by
      refine Tendsto.const_mul _ ?_
      rcases he : e.2 with _ | ⟨b, w⟩
      · simp [hpl]
      · have hb : b ≠ Letter.one := by
          intro hb
          have := hc e (by simp)
          rw [he, hb] at this
          exact this rfl
        exact tendsto_hpl_one hb w
    have := h1.add h2
    refine (this.congr fun y => ?_).trans (le_of_eq (by simp))
    simp

/-! ### Dominating functions for log moments -/

/-- `|log v| ^ n` is integrable on `(0, 1)`. -/
theorem integrableOn_abs_log_pow_Ioo (n : ℕ) :
    IntegrableOn (fun v => |log v| ^ n) (Ioo (0 : ℝ) 1) := by
  obtain ⟨C, hC, h⟩ := abs_log_pow_le n (δ := 1 / 2) (by norm_num)
  have hI : IntegrableOn (fun v : ℝ => C * v ^ (-(1 / 2) : ℝ)) (Ioo (0 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul C
  refine hI.mono' ?_ ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun v hv => ?_))
  · exact ((continuous_abs.comp_continuousOn (continuousOn_log.mono fun v hv =>
      ne_of_gt hv.1)).pow n).aestronglyMeasurable measurableSet_Ioo
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact h v ⟨hv.1, hv.2.le⟩

/-- `|log (1 - v)| ^ n` is integrable on `(0, 1)`. -/
theorem integrableOn_abs_log_one_sub_pow_Ioo (n : ℕ) :
    IntegrableOn (fun v => |log (1 - v)| ^ n) (Ioo (0 : ℝ) 1) := by
  have h := (integrableOn_abs_log_pow_Ioo n)
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h ⊢
  simpa using (h.comp_sub_left 1).symm

end QED.Polylog.ParamHPL
