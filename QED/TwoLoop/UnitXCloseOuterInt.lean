/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXCloseOuter
public import QED.TwoLoop.UnitXCloseFubini
public import QED.TwoLoop.UnitXCloseBound
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The outer integrations of the crossed ladder: the function `Φ_X`

Steps 1 and 2 of section 4.2 of `docs/TWO-LOOP-UNITS.md`, proved. For `(z₂, z₃)` in the open
triangle with `z₂ ≠ z₃` (`Y = z₂ + z₃`, `e = z₂ z₃`, `p = Y z₂`, `q = Y z₃`, `g = z₂ (1 - Y)`):

* the `z_a`-integral of `T(0, 0)` at fixed `z_A` is `-outerPrim` at `z_a = 0` (antiderivative
  `hasDerivAt_innerH`, limit `tendsto_innerH_atTop`), which equals
  `F₁(b) = α₂/(b+e) + α₃/(2(b+e)²) + α₄/(3(b+e)³) + β₂/(Y²(b+p)(b+q)) - α₁ L(b)`,
  `L = 2 log Y + log (b+e) - log (b+p) - log (b+q)` (`neg_innerH_zero`);
* the `z_A`-antiderivative of `F₁` is `K = Q + S L + κ_e log (b+e) + κ_p log (b+p) +
  κ_q log (b+q)` (`hasDerivAt_xK`), which tends to `0` at `∞` (`tendsto_xK_atTop`);
* hence `∫₀^∞ ∫₀^∞ T(0, 0) dz_a dz_A = Φ_X(z₂, z₃) = -K(g)` (`crossedPhi`,
  `iterated_crossedTerm_zero_eq`), and **the massless integral over `Δ₄` is
  `∫_{triangle} Φ_X`** (`integral_crossedZero_eq_phi`), eq. (4.4) of the document.

With `QED.TwoLoop.UnitXClose.xUnitLimitOne_of_iterated`, the X link reduces to
`∫_{triangle} Φ_X = 1/6 - 5 ζ(2) log 2 + (13/6) ζ(2) + (5/4) ζ(3)` (`xUnitLimit_of_phi`).
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.TwoLoop.UnitXClose

open QED.TwoLoop.UnitXGraph
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### The functions -/

/-- `L(b) = 2 log Y + log (b + e) - log (b + p) - log (b + q)`. -/
noncomputable def xL (M c B : ℝ) : ℝ :=
  2 * log (M + c) + log (B + M * c) - log (B + (M + c) * M) - log (B + (M + c) * c)

/-- `S(b) = ∑_{k=2}^{5} -r_k/((k-1) b^{k-1})`. -/
noncomputable def xS (M c B : ℝ) : ℝ :=
  -(xr₂ M c / B) - xr₃ M c / (2 * B ^ 2) - xr₄ M c / (3 * B ^ 3) - xr₅ M c / (4 * B ^ 4)

/-- `Q(b) = -c₂₀/b - c₃₀/(2b²) - c₂ₑ/(b+e) - c₃ₑ/(2(b+e)²)`. -/
noncomputable def xQ (M c B : ℝ) : ℝ :=
  -(xc₂₀ M c / B) - xc₃₀ M c / (2 * B ^ 2) - xc₂ₑ M c / (B + M * c) -
    xc₃ₑ M c / (2 * (B + M * c) ^ 2)

/-- The `z_A`-antiderivative `K = Q + S L + ∑_d κ_d log (b + d)`. -/
noncomputable def xK (M c B : ℝ) : ℝ :=
  xQ M c B + xS M c B * xL M c B + xκe M c * log (B + M * c) +
    xκp M c * log (B + (M + c) * M) + xκq M c * log (B + (M + c) * c)

/-- The `z_a`-integral `F₁(b)`. -/
noncomputable def xF1 (M c B : ℝ) : ℝ :=
  xα₂ M c B / (B + M * c) + xα₃ M c B / (2 * (B + M * c) ^ 2) +
    xα₄ M c B / (3 * (B + M * c) ^ 3) +
    xβ₂ M c B / ((M + c) ^ 2 * ((B + (M + c) * M) * (B + (M + c) * c))) - xα₁ M c B * xL M c B

/-- **`Φ_X(z₂, z₃) = -K(g)`**, `g = z₂ (1 - z₂ - z₃)`: the integrand of eq. (4.4). -/
noncomputable def crossedPhi (M c : ℝ) : ℝ := -xK M c (M * (1 - M - c))

/-- The `z_a`-antiderivative at fixed `z_A`, as a function of `z_a`. -/
noncomputable def innerH (M c A a : ℝ) : ℝ :=
  outerPrim (M + c) (A + M * (1 - M - c)) (xα₁ M c (A + M * (1 - M - c)))
    (xα₂ M c (A + M * (1 - M - c))) (xα₃ M c (A + M * (1 - M - c)))
    (xα₄ M c (A + M * (1 - M - c))) (xβ₂ M c (A + M * (1 - M - c)))
    ((A + M * (1 - M - c)) + (a + M * c))

/-! ### Generic derivatives and limits -/

theorem hasDerivAt_log_add {B d : ℝ} (h : 0 < B + d) :
    HasDerivAt (fun B => log (B + d)) (1 / (B + d)) B := by
  have := ((hasDerivAt_id B).add_const d).log h.ne'
  simpa [one_div] using this

theorem hasDerivAt_div_self {B : ℝ} (hB : B ≠ 0) (r : ℝ) :
    HasDerivAt (fun x => r / x) (-(r / B ^ 2)) B := by
  have := (hasDerivAt_inv hB).const_mul r
  convert this using 1
  · funext x; simp [div_eq_mul_inv]
  · field_simp

theorem hasDerivAt_div_mul_pow {B : ℝ} (hB : B ≠ 0) (r : ℝ) (k : ℕ) (hk : k ≠ 0) :
    HasDerivAt (fun x => r / (k * x ^ k)) (-(r / B ^ (k + 1))) B := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have := (((hasDerivAt_pow k B).const_mul (k : ℝ)).inv (by positivity)).const_mul r
  convert this using 1
  · funext x; simp [div_eq_mul_inv]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    push_cast
    field_simp
    ring

theorem tendsto_log_add_div (d : ℝ) :
    Tendsto (fun B : ℝ => log (B + d) / B) atTop (𝓝 0) := by
  have h := (tendsto_pow_log_div_mul_add_atTop 1 (-d) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_right atTop d tendsto_id)
  refine h.congr' ?_
  filter_upwards with B
  simp [pow_one, one_mul, id]

theorem tendsto_log_add_sub_log (d : ℝ) :
    Tendsto (fun B : ℝ => log (B + d) - log B) atTop (𝓝 0) := by
  have h1 : Tendsto (fun B : ℝ => 1 + d * B⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_inv_atTop_zero.const_mul d).const_add 1
  have h2 := ((continuousAt_log one_ne_zero).tendsto.comp h1)
  rw [log_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (max 0 (-d))] with B hB
  have hB0 : 0 < B := lt_of_le_of_lt (le_max_left _ _) hB
  have hBd : 0 < B + d := by linarith [le_max_right 0 (-d)]
  simp only [Function.comp_apply]
  rw [← log_div hBd.ne' hB0.ne']
  congr 1
  field_simp

/-! ### The `z_a`-integration -/

section Inner

variable {M c : ℝ} (hM : 0 < M) (hc : 0 < c) (hb : 0 < 1 - M - c)
include hM hc hb

omit hM hc hb in
theorem innerH_eq (A : ℝ) :
    innerH M c A = outerPrim (M + c) (A + M * (1 - M - c)) (xα₁ M c (A + M * (1 - M - c)))
      (xα₂ M c (A + M * (1 - M - c))) (xα₃ M c (A + M * (1 - M - c)))
      (xα₄ M c (A + M * (1 - M - c))) (xβ₂ M c (A + M * (1 - M - c))) ∘
      (fun x => (A + M * (1 - M - c)) + (x + M * c)) := rfl

theorem hasDerivAt_innerH_aux {A a : ℝ} (hA : 0 < A) (ha : 0 ≤ a) :
    HasDerivAt (innerH M c A) (outerPF (M + c) (A + M * (1 - M - c)) (xα₁ M c (A + M * (1 - M - c)))
      (xα₂ M c (A + M * (1 - M - c))) (xα₃ M c (A + M * (1 - M - c)))
      (xα₄ M c (A + M * (1 - M - c))) (xβ₂ M c (A + M * (1 - M - c)))
      ((A + M * (1 - M - c)) + (a + M * c))) a := by
  have hB : 0 < A + M * (1 - M - c) := by positivity
  have hU : 0 < (A + M * (1 - M - c)) + (a + M * c) := by positivity
  have hlin : HasDerivAt (fun x : ℝ => (A + M * (1 - M - c)) + (x + M * c)) 1 a := by
    simpa using ((hasDerivAt_id a).add_const (M * c)).const_add (A + M * (1 - M - c))
  have h := (hasDerivAt_outerPrim (α₁ := xα₁ M c (A + M * (1 - M - c)))
    (α₂ := xα₂ M c (A + M * (1 - M - c))) (α₃ := xα₃ M c (A + M * (1 - M - c)))
    (α₄ := xα₄ M c (A + M * (1 - M - c))) (β₂ := xβ₂ M c (A + M * (1 - M - c)))
    (by positivity : 0 < M + c) hB hU).comp a hlin
  rw [mul_one] at h
  rw [innerH_eq]
  exact h

theorem hasDerivAt_innerH {A a : ℝ} (hA : 0 < A) (ha : 0 < a) :
    HasDerivAt (innerH M c A) (crossedTerm 0 0 A M c a (1 - M - c)) a := by
  have hB : 0 < A + M * (1 - M - c) := by positivity
  have hU : 0 < (A + M * (1 - M - c)) + (a + M * c) := by positivity
  have h := hasDerivAt_innerH_aux hM hc hb hA ha.le
  rw [← crossedPF hB hU (by positivity : 0 < M + c), add_sub_cancel_left] at h
  rw [crossedTerm_zero_hier hA hM hc ha hb]
  exact h

theorem continuousWithinAt_innerH {A : ℝ} (hA : 0 < A) :
    ContinuousWithinAt (innerH M c A) (Ici 0) 0 :=
  (hasDerivAt_innerH_aux hM hc hb hA le_rfl).continuousAt.continuousWithinAt

omit hb in
theorem tendsto_innerH_atTop (A : ℝ) : Tendsto (innerH M c A) atTop (𝓝 0) :=
  (tendsto_outerPrim_atTop (by positivity : 0 < M + c)).comp
    (tendsto_atTop_add_const_left _ _ (tendsto_atTop_add_const_right _ _ tendsto_id))

omit hb in
theorem xL_eq {B : ℝ} (hB : 0 < B) :
    log ((M + c) ^ 2 * (B + M * c) / ((M + c) ^ 2 * (B + M * c) + B ^ 2)) = xL M c B := by
  have hY : 0 < M + c := by positivity
  have e : (M + c) ^ 2 * (B + M * c) + B ^ 2 = (B + (M + c) * M) * (B + (M + c) * c) := by ring
  rw [e, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_pow]
  unfold xL; push_cast; ring

/-- **The `z_a`-integral**: `-H(z_a = 0) = F₁(b)`. -/
theorem neg_innerH_zero {A : ℝ} (hA : 0 < A) :
    -innerH M c A 0 = xF1 M c (A + M * (1 - M - c)) := by
  have hB : 0 < A + M * (1 - M - c) := by positivity
  have hL := xL_eq hM hc hB
  have e : (M + c) ^ 2 * ((A + M * (1 - M - c)) + M * c) + (A + M * (1 - M - c)) ^ 2 =
      ((A + M * (1 - M - c)) + (M + c) * M) * ((A + M * (1 - M - c)) + (M + c) * c) := by ring
  simp only [innerH, outerPrim, xF1, zero_add]
  rw [hL, e]
  ring

end Inner

/-! ### The `z_A`-integration -/

section Outer

variable {M c : ℝ} (hM : 0 < M) (hc : 0 < c)
include hM hc

theorem hasDerivAt_xL {B : ℝ} (hB : 0 < B) :
    HasDerivAt (xL M c) (1 / (B + M * c) - 1 / (B + (M + c) * M) - 1 / (B + (M + c) * c)) B := by
  have h := (((hasDerivAt_log_add (B := B) (d := M * c) (by positivity)).const_add
    (2 * log (M + c))).sub (hasDerivAt_log_add (B := B) (d := (M + c) * M) (by positivity))).sub
    (hasDerivAt_log_add (B := B) (d := (M + c) * c) (by positivity))
  convert h using 1
  funext x; simp only [xL, Pi.sub_apply]

omit hM hc in
theorem hasDerivAt_xS {B : ℝ} (hB : 0 < B) :
    HasDerivAt (xS M c) (-xα₁ M c B) B := by
  have h0 := hasDerivAt_div_self hB.ne' (xr₂ M c)
  have h1 := hasDerivAt_div_mul_pow hB.ne' (xr₃ M c) 2 (by norm_num)
  have h2 := hasDerivAt_div_mul_pow hB.ne' (xr₄ M c) 3 (by norm_num)
  have h3 := hasDerivAt_div_mul_pow hB.ne' (xr₅ M c) 4 (by norm_num)
  push_cast at h1 h2 h3
  have h := ((h0.neg.sub h1).sub h2).sub h3
  rw [xα₁_eq hB.ne']
  convert h using 1
  · funext x; simp only [xS, Pi.sub_apply, Pi.neg_apply]
  · ring

theorem hasDerivAt_xQ {B : ℝ} (hB : 0 < B) :
    HasDerivAt (xQ M c) (xc₂₀ M c / B ^ 2 + xc₃₀ M c / B ^ 3 + xc₂ₑ M c / (B + M * c) ^ 2 +
      xc₃ₑ M c / (B + M * c) ^ 3) B := by
  have he : 0 < B + M * c := by positivity
  have h0 := hasDerivAt_div_self hB.ne' (xc₂₀ M c)
  have h1 := hasDerivAt_div_mul_pow hB.ne' (xc₃₀ M c) 2 (by norm_num)
  have h2 := (hasDerivAt_div_self he.ne' (xc₂ₑ M c)).comp_add_const B (M * c)
  have h3 := (hasDerivAt_div_mul_pow he.ne' (xc₃ₑ M c) 2 (by norm_num)).comp_add_const B (M * c)
  push_cast at h1 h3
  have h := ((h0.neg.sub h1).sub h2).sub h3
  convert h using 1
  · funext x; simp only [xQ, Pi.sub_apply, Pi.neg_apply]
  · ring

/-- **The `z_A`-antiderivative**: `K' = F₁` on `(0, ∞)`. -/
theorem hasDerivAt_xK (hMc : M ≠ c) {B : ℝ} (hB : 0 < B) : HasDerivAt (xK M c) (xF1 M c B) B := by
  have hY : 0 < M + c := by positivity
  have he : 0 < B + M * c := by positivity
  have hp : 0 < B + (M + c) * M := by positivity
  have hq : 0 < B + (M + c) * c := by positivity
  have h := ((((hasDerivAt_xQ hM hc hB).add ((hasDerivAt_xS (M := M) (c := c) hB).mul
    (hasDerivAt_xL hM hc hB))).add ((hasDerivAt_log_add he).const_mul (xκe M c))).add
    ((hasDerivAt_log_add hp).const_mul (xκp M c))).add
    ((hasDerivAt_log_add hq).const_mul (xκq M c))
  have key := crossedKRat hM hc hMc hB
  convert h using 1
  · funext x; simp only [xK, Pi.add_apply, Pi.mul_apply]
  · unfold xF1 xS
    linear_combination -key

/-- **`K(b) → 0` as `b → ∞`.** -/
theorem tendsto_xK_atTop (hMc : M ≠ c) : Tendsto (xK M c) atTop (𝓝 0) := by
  have hinv : ∀ k : ℕ, ∀ r : ℝ, Tendsto (fun B : ℝ => r / ((k + 1 : ℝ) * B ^ (k + 1))) atTop
      (𝓝 0) := fun k r => tendsto_const_nhds.div_atTop
    ((tendsto_pow_atTop (Nat.succ_ne_zero k)).const_mul_atTop (by positivity))
  have hsh : Tendsto (fun B : ℝ => B + M * c) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hQ : Tendsto (xQ M c) atTop (𝓝 0) := by
    have := ((((hinv 0 (xc₂₀ M c)).neg.sub (hinv 1 (xc₃₀ M c))).sub
      ((hinv 0 (xc₂ₑ M c)).comp hsh)).sub ((hinv 1 (xc₃ₑ M c)).comp hsh))
    simp only [neg_zero, sub_zero] at this
    refine this.congr fun B => ?_
    simp only [xQ, Function.comp_apply]; push_cast; ring_nf
  -- `B S → -r₂`, `L/B → 0`
  have hBS : Tendsto (fun B : ℝ => B * xS M c B) atTop (𝓝 (-xr₂ M c)) := by
    have := ((((hinv 0 (xr₃ M c / 2)).add (hinv 1 (xr₄ M c * 2 / 3))).add
      (hinv 2 (xr₅ M c * 3 / 4))).const_sub (-xr₂ M c))
    simp only [add_zero, sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with B hB
    simp only [xS]; push_cast; field_simp; ring
  have hLB : Tendsto (fun B : ℝ => xL M c B / B) atTop (𝓝 0) := by
    have h0 : Tendsto (fun B : ℝ => 2 * log (M + c) / B) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have := ((h0.add (tendsto_log_add_div (M * c))).sub (tendsto_log_add_div ((M + c) * M))).sub
      (tendsto_log_add_div ((M + c) * c))
    simp only [add_zero, sub_zero] at this
    refine this.congr fun B => ?_
    simp only [xL]; ring
  have hSL : Tendsto (fun B => xS M c B * xL M c B) atTop (𝓝 0) := by
    have := hBS.mul hLB
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with B hB
    field_simp
  have hκ : Tendsto (fun B => xκe M c * log (B + M * c) + xκp M c * log (B + (M + c) * M) +
      xκq M c * log (B + (M + c) * c)) atTop (𝓝 0) := by
    have := (((tendsto_log_add_sub_log (M * c)).const_mul (xκe M c)).add
      ((tendsto_log_add_sub_log ((M + c) * M)).const_mul (xκp M c))).add
      ((tendsto_log_add_sub_log ((M + c) * c)).const_mul (xκq M c))
    simp only [mul_zero, add_zero] at this
    refine this.congr fun B => ?_
    have hs := xκ_sum hM hc hMc
    linear_combination (-log B) * hs
  have := (hQ.add hSL).add hκ
  simp only [add_zero] at this
  refine this.congr fun B => ?_
  simp only [xK]; ring

end Outer

/-! ### The two integrations -/

/-- **`∫₀^∞ ∫₀^∞ T(0, 0) dz_a dz_A = Φ_X(z₂, z₃)`**, for `(z₂, z₃)` in the triangle with
`z₂ ≠ z₃`, given the integrability supplied by Fubini. -/
theorem iterated_crossedTerm_zero_eq {M c : ℝ} (hM : 0 < M) (hc : 0 < c) (hb : 0 < 1 - M - c)
    (hMc : M ≠ c)
    (hint1 : ∀ᵐ A ∂(volume.restrict (Ioi (0 : ℝ))),
      IntegrableOn (fun a => crossedTerm 0 0 A M c a (1 - M - c)) (Ioi 0))
    (hint2 : IntegrableOn (fun A => ∫ a in Ioi (0 : ℝ), crossedTerm 0 0 A M c a (1 - M - c))
      (Ioi 0)) :
    ∫ A in Ioi (0 : ℝ), ∫ a in Ioi (0 : ℝ), crossedTerm 0 0 A M c a (1 - M - c) =
      crossedPhi M c := by
  have hg : 0 < M * (1 - M - c) := by positivity
  have hK : ∀ A ∈ Ioi (0 : ℝ),
      HasDerivAt (fun A => xK M c (A + M * (1 - M - c))) (-innerH M c A 0) A := by
    intro A hA
    have hA' : (0 : ℝ) < A := hA
    rw [neg_innerH_zero hM hc hb hA']
    exact (hasDerivAt_xK hM hc hMc (by positivity : 0 < A + M * (1 - M - c))).comp_add_const _ _
  have hK0 : ContinuousWithinAt (fun A => xK M c (A + M * (1 - M - c))) (Ici 0) 0 :=
    ((hasDerivAt_xK hM hc hMc (show 0 < 0 + M * (1 - M - c) by linarith)).comp_add_const 0
      (M * (1 - M - c))).continuousAt.continuousWithinAt
  have hKinf : Tendsto (fun A => xK M c (A + M * (1 - M - c))) atTop (𝓝 0) :=
    (tendsto_xK_atTop hM hc hMc).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
  rw [iterated_Ioi_eq_of_prim (H := innerH M c)
    (fun A hA a ha => hasDerivAt_innerH hM hc hb hA ha)
    (fun A hA => continuousWithinAt_innerH hM hc hb hA)
    (fun A _ => tendsto_innerH_atTop hM hc A) hK hK0 hKinf hint1 hint2]
  simp [crossedPhi]

theorem ae_ne_diag : ∀ᵐ p ∂(volume.restrict innerTriangle), p.1 ≠ p.2 := by
  refine ae_restrict_of_ae ?_
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have h0 : (volume : Measure (ℝ × ℝ)) {p | p.1 = p.2} = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_apply hm]
    simp
  refine measure_mono_null (fun p hp => ?_) h0
  simpa using hp

/-- **The massless integral over `Δ₄` is `∫_{triangle} Φ_X`** (eq. (4.4)), given the
domination. -/
theorem integral_crossedZero_eq_phi :
    ∫ y in simplexSet 4, crossedZero (simplexPoint y) =
      ∫ p in innerTriangle, crossedPhi p.1 p.2 := by
  have hI := (tendsto_integral_crossedFour crossedDom).1
  rw [integral_crossedZero_eq_iterated hI]
  refine integral_congr_ae ?_
  filter_upwards [ae_integrableOn_inner hI, ae_ne_diag,
    ae_restrict_mem measurableSet_innerTriangle] with p hp hne hmem
  obtain ⟨h1, h2, h3⟩ := hmem
  have e : 1 - (p.1 + p.2) = 1 - p.1 - p.2 := by ring
  simp only [e] at hp ⊢
  exact iterated_crossedTerm_zero_eq h1 h2 (by linarith) hne hp.1 hp.2

/-- **The X link reduces to `∫_{triangle} Φ_X`**: if
`∫_{triangle} Φ_X = 1/6 - 5 ζ(2) log 2 + (13/6) ζ(2) + (5/4) ζ(3)`, then `XUnitLimit`. -/
theorem xUnitLimit_of_phi (hval : ∫ p in innerTriangle, crossedPhi p.1 p.2 = xValue) :
    QED.TwoLoop.HeadlineAssembly.XUnitLimit :=
  QED.TwoLoop.HeadlineAssembly.XUnitLimit.of_one
    (xUnitLimitOne_of_dom crossedDom (by rw [integral_crossedZero_eq_phi, hval]))

end QED.TwoLoop.UnitXClose

end
