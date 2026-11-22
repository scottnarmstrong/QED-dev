/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValPrim
public import QED.ThreeLoopD.SetDMastersI15KTaylor
import QED.Polylog.LiLimits
import QED.Polylog.DilogPM
import QED.Polylog.Integral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (d), master `I₁₅`: the `u`-weighted half of `∫ F₂`

Write `c = x (1 - x)`, `v = 1 - u`, `b₁ = log (c u / P²)`, `b₂ = log (c / u)` (so `F₂` is
`QED.ThreeLoopD.i15F 2`). Since `P = c v² + u`,

  `F₂ = A₁ + A₂₃`,  `A₁ = (b₁² - b₂²) / (2 c)`,  `A₂₃ = (v² b₁² - b₂²) / (2 u)`.

This file computes the `x`-integral of `A₂₃` for fixed `u`: with `X = log x`, `Y = log (1 - x)`,
`A = log (u + v x)`, `B = log (1 - v x)`, `b₁ = X + Y + log u - 2A - 2B`, `b₂ = X + Y - log u`,
and `v² b₁² - b₂²` has the explicit primitive `QED.ThreeLoopD.i15WPr` (from
`QED.ThreeLoopD.SetDMastersI15KValPrim`, with `x ↦ 1 - x` exchanging `X, Y` and `A, B`). The
result is

  `∫₀¹ A₂₃ dx = h(u) = (u - 1/u)(8 (Li₂(-u) + log u log (1+u)) + 4 (Li₂ u + log u log (1-u)))`
    `+ (1 - 3u/2) log² u + (4 - 6u) log u + 4u - 8 + π² (1/3 - u/6)`,

and `∫₀¹ h = π²/4 + 4 ζ(3) - 59/8` by the primitive `QED.ThreeLoopD.i15WPhi` (`Li₃ (± u)`).

## Main results

* `QED.ThreeLoopD.i15F_two_eq`: `F₂ = A₁ + A₂₃`.
* `QED.ThreeLoopD.integral_i15A23`: `∫∫ A₂₃ = π²/4 + 4 ζ(3) - 59/8` (given integrability).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-! ### The splitting -/

/-- `A₁ = (b₁² - b₂²) / (2 c)`. -/
noncomputable def i15A1 (z : ℝ × ℝ) : ℝ :=
  (i15B1 z.1 z.2 ^ 2 - i15B2 z.1 z.2 ^ 2) / (2 * (z.1 * (1 - z.1)))

/-- `A₂₃ = (v² b₁² - b₂²) / (2 u)`. -/
noncomputable def i15A23 (z : ℝ × ℝ) : ℝ :=
  ((1 - z.2) ^ 2 * i15B1 z.1 z.2 ^ 2 - i15B2 z.1 z.2 ^ 2) / (2 * z.2)

theorem i15F_two_eq {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    i15F 2 z = i15A1 z + i15A23 z := by
  obtain ⟨⟨hx0, hx1⟩, hu0, hu1⟩ := hz
  have hc : z.1 * (1 - z.1) ≠ 0 := (mul_pos hx0 (by linarith)).ne'
  have h1 : 1 - z.1 ≠ 0 := by linarith
  unfold i15F i15A1 i15A23
  simp only [i15P, i9Poly, Nat.factorial_two, Nat.cast_ofNat, neg_sq]
  field_simp
  ring

/-! ### The inner integrand in logarithms -/

theorem i15B1_eq {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    i15B1 x u = log x + log (1 - x) + log u - 2 * log (u + (1 - u) * x) -
      2 * log (1 - (1 - u) * x) := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hu0, hu1⟩ := hu
  have hA : 0 < u + (1 - u) * x := by nlinarith
  have hB : 0 < 1 - (1 - u) * x := by nlinarith
  have hP : i15P x u = (1 - (1 - u) * x) * (u + (1 - u) * x) := by
    unfold i15P i9Poly; ring
  unfold i15B1
  rw [Real.log_mul hx0.ne' (by linarith), hP, Real.log_mul hB.ne' hA.ne']
  ring

theorem i15B2_eq {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i15B2 x u = log x + log (1 - x) - log u := by
  unfold i15B2
  rw [Real.log_mul hx.1.ne' (by linarith [hx.2])]

/-- `v² b₁² - b₂²` in the logarithms `X, Y, A, B`. -/
noncomputable def i15Wg (u x : ℝ) : ℝ :=
  (1 - u) ^ 2 * (log x + log (1 - x) + log u - 2 * log (u + (1 - u) * x) -
      2 * log (1 - (1 - u) * x)) ^ 2 - (log x + log (1 - x) - log u) ^ 2

theorem i15A23_eq {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    i15A23 (x, u) = i15Wg u x / (2 * u) := by
  unfold i15A23 i15Wg
  rw [i15B1_eq hx hu, i15B2_eq hx]

/-! ### The primitive in `x` -/

/-- `x log x - x`. -/
noncomputable def i15WX (x : ℝ) : ℝ := x * log x - x

/-- `x log² x - 2 x log x + 2 x`. -/
noncomputable def i15WXX (x : ℝ) : ℝ := x * log x ^ 2 - 2 * (x * log x) + 2 * x

theorem hasDerivAt_i15WX {x : ℝ} (hx : 0 < x) : HasDerivAt i15WX (log x) x := by
  have := (Real.hasDerivAt_mul_log hx.ne').sub (hasDerivAt_id x)
  convert this using 1
  · funext y; simp [i15WX]
  · ring

theorem hasDerivAt_i15WXX {x : ℝ} (hx : 0 < x) : HasDerivAt i15WXX (log x ^ 2) x := by
  have hl := Real.hasDerivAt_log hx.ne'
  have hm := Real.hasDerivAt_mul_log hx.ne'
  have h := (((hasDerivAt_id x).mul (hl.pow 2)).sub (hm.const_mul 2)).add
    ((hasDerivAt_id x).const_mul 2)
  convert h using 1
  · funext y; simp [i15WXX]
  · simp only [id, Pi.pow_apply]; field_simp; ring

/-- **The primitive of `v² b₁² - b₂²` in `x`.** -/
noncomputable def i15WPr (u x : ℝ) : ℝ :=
  ((1 - u) ^ 2 - 1) * (i15WXX x - i15WXX (1 - x) + 2 * i15VLM 1 x + log u ^ 2 * x) +
    (1 - u) ^ 2 * (4 * i15VL2 u (1 - u) x + 4 * i15VL2 1 (-(1 - u)) x -
      4 * i15VLL u (1 - u) x - 4 * i15VLM (1 - u) x + 4 * i15VLM (1 - u) (1 - x) +
      4 * i15VLL u (1 - u) (1 - x) - 4 * log u * i15VL u (1 - u) x -
      4 * log u * i15VL 1 (-(1 - u)) x + 8 * i15VAB u x) +
    (2 * (1 - u) ^ 2 + 2) * log u * (i15WX x - i15WX (1 - x))

theorem hasDerivAt_i15WPr {u x : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i15WPr u) (i15Wg u x) x := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hx0, hx1⟩ := hx
  have hv : 0 < 1 - u := by linarith
  have h1x : 0 < 1 - x := by linarith
  have hA : 0 < u + (1 - u) * x := by nlinarith
  have hB : 0 < 1 + -(1 - u) * x := by nlinarith
  have hvx : (1 - u) * x < 1 := by nlinarith
  have hvx' : (1 - u) * (1 - x) < 1 := by nlinarith
  have hs : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have dXX := hasDerivAt_i15WXX hx0
  have dXX' := (hasDerivAt_i15WXX h1x).comp x hs
  have dXY := hasDerivAt_i15VLM (v := 1) one_pos hx0 (by linarith)
  have dAA := hasDerivAt_i15VL2 (p := u) (q := 1 - u) (x := x) hv.ne' hA
  have dBB := hasDerivAt_i15VL2 (p := 1) (q := -(1 - u)) (x := x) (by linarith) hB
  have dA := hasDerivAt_i15VL (p := u) (q := 1 - u) (x := x) hv.ne' hA
  have dB := hasDerivAt_i15VL (p := 1) (q := -(1 - u)) (x := x) (by linarith) hB
  have dXA := hasDerivAt_i15VLL (x := x) hu0 hv hx0
  have dXA' := (hasDerivAt_i15VLL (x := 1 - x) hu0 hv h1x).comp x hs
  have dXB := hasDerivAt_i15VLM hv hx0 hvx
  have dXB' := (hasDerivAt_i15VLM hv h1x hvx').comp x hs
  have dAB := hasDerivAt_i15VAB ⟨hu0, hu1⟩ ⟨hx0.le, hx1.le⟩
  have dX := hasDerivAt_i15WX hx0
  have dX' := (hasDerivAt_i15WX h1x).comp x hs
  have p1 := (((dXX.sub dXX').add (dXY.const_mul 2)).add
    ((hasDerivAt_id x).const_mul (log u ^ 2))).const_mul ((1 - u) ^ 2 - 1)
  have p2 := ((((((((((dAA.const_mul 4).add (dBB.const_mul 4)).sub (dXA.const_mul 4)).sub
    (dXB.const_mul 4)).add (dXB'.const_mul 4)).add (dXA'.const_mul 4)).sub
    (dA.const_mul (4 * log u))).sub (dB.const_mul (4 * log u))).add
    (dAB.const_mul 8))).const_mul ((1 - u) ^ 2)
  have p3 := (dX.sub dX').const_mul ((2 * (1 - u) ^ 2 + 2) * log u)
  have h := (p1.add p2).add p3
  convert h using 1
  · funext y
    simp only [i15WPr, Function.comp_apply, Pi.add_apply, Pi.sub_apply, id]
  · have e1 : u + (1 - u) * (1 - x) = 1 - (1 - u) * x := by ring
    have e2 : 1 - (1 - u) * (1 - x) = u + (1 - u) * x := by ring
    have e3 : 1 + -(1 - u) * x = 1 - (1 - u) * x := by ring
    have e4 : 1 - 1 * x = 1 - x := by ring
    have e5 : 1 - (1 - x) = x := by ring
    simp only [e1, e2, e3, e4]
    unfold i15Wg
    ring

/-! ### Limits of the primitive -/

theorem i15W_tendsto_of_continuousAt {f : ℝ → ℝ} {a : ℝ} (h : ContinuousAt f a) (s : Set ℝ) :
    Tendsto f (𝓝[s] a) (𝓝 (f a)) :=
  h.tendsto.mono_left nhdsWithin_le_nhds

theorem continuousAt_i15WX (x : ℝ) : ContinuousAt i15WX x :=
  (Real.continuous_mul_log.sub continuous_id).continuousAt

theorem tendsto_i15WXX_zero : Tendsto i15WXX (𝓝[>] 0) (𝓝 0) := by
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h := (tendsto_mul_log_sq_zero.sub (tendsto_mul_log_zero.const_mul 2)).add
    (hx0.const_mul 2)
  simp only [mul_zero, sub_zero, add_zero] at h
  exact h

theorem continuousAt_i15WXX {x : ℝ} (hx : 0 < x) : ContinuousAt i15WXX x :=
  (hasDerivAt_i15WXX hx).continuousAt

/-- The limit of `i15WPr u` at `0⁺`. -/
noncomputable def i15WPr0 (u : ℝ) : ℝ :=
  ((1 - u) ^ 2 - 1) * (0 - i15WXX 1 + 2 * 0 + log u ^ 2 * 0) +
    (1 - u) ^ 2 * (4 * i15VL2 u (1 - u) 0 + 4 * i15VL2 1 (-(1 - u)) 0 -
      4 * -(u / (1 - u) * log u) - 4 * 0 + 4 * i15VLM (1 - u) 1 +
      4 * i15VLL u (1 - u) 1 - 4 * log u * i15VL u (1 - u) 0 -
      4 * log u * i15VL 1 (-(1 - u)) 0 + 8 * i15VAB u 0) +
    (2 * (1 - u) ^ 2 + 2) * log u * (i15WX 0 - i15WX 1)

/-- The limit of `i15WPr u` at `1⁻`. -/
noncomputable def i15WPr1 (u : ℝ) : ℝ :=
  ((1 - u) ^ 2 - 1) * (i15WXX 1 - 0 + 2 * (2 - π ^ 2 / 6) + log u ^ 2 * 1) +
    (1 - u) ^ 2 * (4 * i15VL2 u (1 - u) 1 + 4 * i15VL2 1 (-(1 - u)) 1 -
      4 * i15VLL u (1 - u) 1 - 4 * i15VLM (1 - u) 1 + 4 * 0 +
      4 * -(u / (1 - u) * log u) - 4 * log u * i15VL u (1 - u) 1 -
      4 * log u * i15VL 1 (-(1 - u)) 1 + 8 * i15VAB u 1) +
    (2 * (1 - u) ^ 2 + 2) * log u * (i15WX 1 - i15WX 0)

theorem i15W_continuousAt_facts {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (i15VL2 u (1 - u)) x ∧ ContinuousAt (i15VL2 1 (-(1 - u))) x ∧
      ContinuousAt (i15VL u (1 - u)) x ∧ ContinuousAt (i15VL 1 (-(1 - u))) x ∧
      ContinuousAt (i15VAB u) x := by
  obtain ⟨hu0, hu1⟩ := hu
  have hv : 0 < 1 - u := by linarith
  have hA : 0 < u + (1 - u) * x := by nlinarith [hx.1]
  have hB : 0 < 1 + -(1 - u) * x := by nlinarith [hx.2]
  exact ⟨(hasDerivAt_i15VL2 hv.ne' hA).continuousAt,
    (hasDerivAt_i15VL2 (by linarith) hB).continuousAt,
    (hasDerivAt_i15VL hv.ne' hA).continuousAt, (hasDerivAt_i15VL (by linarith) hB).continuousAt,
    (hasDerivAt_i15VAB ⟨hu0, hu1⟩ hx).continuousAt⟩

theorem tendsto_i15WPr_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i15WPr u) (𝓝[>] 0) (𝓝 (i15WPr0 u)) := by
  obtain ⟨hu0, hu1⟩ := hu
  have hv : 0 < 1 - u := by linarith
  have hv1 : 1 - u < 1 := by linarith
  obtain ⟨cAA, cBB, cA, cB, cAB⟩ := i15W_continuousAt_facts ⟨hu0, hu1⟩ (x := 0) (by simp)
  have hs : Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝 1) := by
    have := ((continuous_sub_left (1 : ℝ)).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have tXX' : Tendsto (fun x => i15WXX (1 - x)) (𝓝[>] 0) (𝓝 (i15WXX 1)) :=
    (continuousAt_i15WXX one_pos).tendsto.comp hs
  have tXB' : Tendsto (fun x => i15VLM (1 - u) (1 - x)) (𝓝[>] 0) (𝓝 (i15VLM (1 - u) 1)) :=
    (hasDerivAt_i15VLM hv one_pos (by linarith)).continuousAt.tendsto.comp hs
  have tXA' : Tendsto (fun x => i15VLL u (1 - u) (1 - x)) (𝓝[>] 0)
      (𝓝 (i15VLL u (1 - u) 1)) :=
    (continuousAt_i15VLL hu0 hv one_pos).tendsto.comp hs
  have tX' : Tendsto (fun x => i15WX (1 - x)) (𝓝[>] 0) (𝓝 (i15WX 1)) :=
    (continuousAt_i15WX 1).tendsto.comp hs
  have tX : Tendsto i15WX (𝓝[>] 0) (𝓝 (i15WX 0)) := i15W_tendsto_of_continuousAt
    (continuousAt_i15WX 0) _
  have p1 := (((tendsto_i15WXX_zero.sub tXX').add ((tendsto_i15VLM_zero one_pos).const_mul 2)).add
    (hx0.const_mul (log u ^ 2))).const_mul ((1 - u) ^ 2 - 1)
  have p2 := (((((((((((i15W_tendsto_of_continuousAt cAA _).const_mul 4).add
    ((i15W_tendsto_of_continuousAt cBB _).const_mul 4)).sub
    ((tendsto_i15VLL_zero hu0 hv).const_mul 4)).sub ((tendsto_i15VLM_zero hv).const_mul 4)).add
    (tXB'.const_mul 4)).add (tXA'.const_mul 4)).sub
    ((i15W_tendsto_of_continuousAt cA _).const_mul (4 * log u))).sub
    ((i15W_tendsto_of_continuousAt cB _).const_mul (4 * log u))).add
    ((i15W_tendsto_of_continuousAt cAB _).const_mul 8))).const_mul ((1 - u) ^ 2)
  have p3 := (tX.sub tX').const_mul ((2 * (1 - u) ^ 2 + 2) * log u)
  have h := (p1.add p2).add p3
  convert h using 1
  · funext y; simp only [i15WPr]
  · simp only [i15WPr0]

theorem tendsto_i15WPr_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i15WPr u) (𝓝[<] 1) (𝓝 (i15WPr1 u)) := by
  obtain ⟨hu0, hu1⟩ := hu
  have hv : 0 < 1 - u := by linarith
  obtain ⟨cAA, cBB, cA, cB, cAB⟩ := i15W_continuousAt_facts ⟨hu0, hu1⟩ (x := 1) (by simp)
  have hs := tendsto_one_sub_nhdsLT_one
  have hx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have tXX : Tendsto i15WXX (𝓝[<] 1) (𝓝 (i15WXX 1)) :=
    i15W_tendsto_of_continuousAt (continuousAt_i15WXX one_pos) _
  have tXX' : Tendsto (fun x => i15WXX (1 - x)) (𝓝[<] 1) (𝓝 0) :=
    tendsto_i15WXX_zero.comp hs
  have tXB : Tendsto (i15VLM (1 - u)) (𝓝[<] 1) (𝓝 (i15VLM (1 - u) 1)) :=
    i15W_tendsto_of_continuousAt (hasDerivAt_i15VLM hv one_pos (by linarith)).continuousAt _
  have tXA : Tendsto (i15VLL u (1 - u)) (𝓝[<] 1) (𝓝 (i15VLL u (1 - u) 1)) :=
    i15W_tendsto_of_continuousAt (continuousAt_i15VLL hu0 hv one_pos) _
  have tXB' : Tendsto (fun x => i15VLM (1 - u) (1 - x)) (𝓝[<] 1) (𝓝 0) :=
    (tendsto_i15VLM_zero hv).comp hs
  have tXA' : Tendsto (fun x => i15VLL u (1 - u) (1 - x)) (𝓝[<] 1)
      (𝓝 (-(u / (1 - u) * log u))) :=
    (tendsto_i15VLL_zero hu0 hv).comp hs
  have tX : Tendsto i15WX (𝓝[<] 1) (𝓝 (i15WX 1)) :=
    i15W_tendsto_of_continuousAt (continuousAt_i15WX 1) _
  have tX' : Tendsto (fun x => i15WX (1 - x)) (𝓝[<] 1) (𝓝 (i15WX 0)) := by
    have := ((continuousAt_i15WX 0).tendsto).comp
      (tendsto_nhdsWithin_iff.1 hs).1
    exact this
  have p1 := (((tXX.sub tXX').add (tendsto_i15VLM_one_one.const_mul 2)).add
    (hx1.const_mul (log u ^ 2))).const_mul ((1 - u) ^ 2 - 1)
  have p2 := (((((((((((i15W_tendsto_of_continuousAt cAA _).const_mul 4).add
    ((i15W_tendsto_of_continuousAt cBB _).const_mul 4)).sub (tXA.const_mul 4)).sub
    (tXB.const_mul 4)).add (tXB'.const_mul 4)).add (tXA'.const_mul 4)).sub
    ((i15W_tendsto_of_continuousAt cA _).const_mul (4 * log u))).sub
    ((i15W_tendsto_of_continuousAt cB _).const_mul (4 * log u))).add
    ((i15W_tendsto_of_continuousAt cAB _).const_mul 8))).const_mul ((1 - u) ^ 2)
  have p3 := (tX.sub tX').const_mul ((2 * (1 - u) ^ 2 + 2) * log u)
  have h := (p1.add p2).add p3
  convert h using 1
  · funext y; simp only [i15WPr]
  · simp only [i15WPr1]

/-! ### The value of the inner integral -/

/-- `h(u)`, the inner integral of `A₂₃`. -/
noncomputable def i15Wh (u : ℝ) : ℝ :=
  (u - 1 / u) * (8 * (Li₂ (-u) + log u * log (1 + u)) + 4 * (Li₂ u + log u * log (1 - u))) +
    (1 - 3 / 2 * u) * log u ^ 2 + (4 - 6 * u) * log u + 4 * u - 8 + π ^ 2 * (1 / 3 - u / 6)

theorem i15WPr1_sub_i15WPr0 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (i15WPr1 u - i15WPr0 u) / (2 * u) = i15Wh u := by
  have hu' := hu
  obtain ⟨hu0, hu1⟩ := hu'
  have hv : 0 < 1 - u := by linarith
  have hs : 0 < 1 + u := by linarith
  have r1 := Li_two_one_sub' hu
  have r2 := Li_two_div_one_add hu
  have r3 := Li_two_inv_one_add hu
  rw [Li_two] at r1 r2 r3
  simp only [i15WPr1, i15WPr0, i15WXX, i15WX, i15VL2, i15VL, i15VLL, i15VLM, i15VAB,
    mul_one, mul_zero, add_zero, sub_zero, Real.log_one, Real.log_zero, zero_mul, one_mul]
  have e7 : u + (1 - u) = 1 := by ring
  have e8 : 1 - (1 - u) = u := by ring
  simp only [e7, e8, Real.log_one, div_one, mul_zero, sub_zero, zero_sub, r1, r2, r3]
  unfold i15Wh
  field_simp
  ring_nf

/-- **The inner integral of `A₂₃`.** -/
theorem integral_i15A23_inner {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hint : IntegrableOn (fun x => i15A23 (x, u)) (Ioo 0 1)) :
    ∫ x in Ioo (0 : ℝ) 1, i15A23 (x, u) = i15Wh u := by
  have h2u : 0 < 2 * u := by linarith [hu.1]
  have hcongr : ∀ x ∈ Ioo (0 : ℝ) 1, i15A23 (x, u) = i15Wg u x / (2 * u) :=
    fun x hx => i15A23_eq hx hu
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  have hI : IntervalIntegrable (fun x => i15Wg u x / (2 * u)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
      (hint.congr_fun hcongr measurableSet_Ioo)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (f := fun x => i15WPr u x / (2 * u))
    (fun x hx => (hasDerivAt_i15WPr hu hx).div_const _) hI
    ((tendsto_i15WPr_zero hu).div_const _) ((tendsto_i15WPr_one hu).div_const _),
    ← sub_div]
  exact i15WPr1_sub_i15WPr0 hu

/-! ### The outer integral -/

/-- A primitive of `h`. -/
noncomputable def i15WPhi (u : ℝ) : ℝ :=
  (4 * u ^ 2 - 4) * (Li₂ (-u) + log u * log (1 + u)) +
    (2 * u ^ 2 - 2) * (Li₂ u + log u * log (1 - u)) -
    8 * (2 * Li₃ (-u) - log u * Li₂ (-u)) + 4 * (log u * Li₂ u - 2 * Li₃ u) +
    u * log u ^ 2 - 3 / 4 * (u ^ 2 * log u ^ 2) - 21 / 4 * (u ^ 2 * log u) + 4 * (u * log u) -
    12 * u + 37 / 8 * u ^ 2 + π ^ 2 * (u / 3 - u ^ 2 / 12)

theorem hasDerivAt_i15WPhi {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i15WPhi (i15Wh u) u := by
  obtain ⟨hu0, hu1⟩ := hu
  have hn : |-u| < 1 := by rw [abs_neg, abs_of_pos hu0]; exact hu1
  have hp : |u| < 1 := by rw [abs_of_pos hu0]; exact hu1
  have hneg : HasDerivAt (fun u : ℝ => -u) (-1) u := hasDerivAt_neg u
  have l2n := (hasDerivAt_Li₂ hn (by linarith)).comp u hneg
  have l3n := (hasDerivAt_Li₃ hn (by linarith)).comp u hneg
  have l2 := hasDerivAt_Li₂ hp hu0.ne'
  have l3 := hasDerivAt_Li₃ hp hu0.ne'
  have hl := Real.hasDerivAt_log hu0.ne'
  have hlp : HasDerivAt (fun u : ℝ => log (1 + u)) (1 / (1 + u)) u := by
    have := ((hasDerivAt_id' u).const_add 1).log (by linarith : (0 : ℝ) < 1 + u).ne'
    simpa using this
  have hlm : HasDerivAt (fun u : ℝ => log (1 - u)) (-1 / (1 - u)) u := by
    have := ((hasDerivAt_id' u).const_sub 1).log (by linarith : (0 : ℝ) < 1 - u).ne'
    simpa [neg_div] using this
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
    simpa using hasDerivAt_pow 2 u
  have t1 := ((hsq.const_mul 4).sub_const 4).mul (l2n.add (hl.mul hlp))
  have t2 := ((hsq.const_mul 2).sub_const 2).mul (l2.add (hl.mul hlm))
  have t3 := (((l3n.const_mul 2).sub (hl.mul l2n)).const_mul 8)
  have t4 := (((hl.mul l2).sub (l3.const_mul 2)).const_mul 4)
  have t5 := (((((((hasDerivAt_id u).mul (hl.pow 2)).sub
    ((hsq.mul (hl.pow 2)).const_mul (3 / 4))).sub
    ((hsq.mul hl).const_mul (21 / 4))).add (((hasDerivAt_id u).mul hl).const_mul 4)).sub
    ((hasDerivAt_id u).const_mul 12)).add (hsq.const_mul (37 / 8))).add
    ((((hasDerivAt_id u).div_const 3).sub (hsq.div_const 12)).const_mul (π ^ 2))
  have h := (((t1.add t2).sub t3).add t4).add t5
  convert h using 1
  · funext y
    simp only [i15WPhi, Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply, id]
    ring
  · have hu1' : 1 - u ≠ 0 := by linarith
    have hu2 : 1 + u ≠ 0 := by linarith
    simp only [Function.comp_apply, id, sub_neg_eq_add, Pi.pow_apply, Pi.add_apply,
      Pi.mul_apply]
    unfold i15Wh
    field_simp
    ring

theorem tendsto_i15WPhi_zero : Tendsto i15WPhi (𝓝[>] 0) (𝓝 0) := by
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hn : Tendsto (fun x : ℝ => -x) (𝓝[>] 0) (𝓝 0) := by simpa using hx0.neg
  have hnI : ∀ᶠ x in 𝓝[>] (0 : ℝ), -x ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have l2n : Tendsto (fun x => Li₂ (-x)) (𝓝[>] 0) (𝓝 0) := by
    simpa [Li₂_zero] using tendsto_Li₂_comp (by norm_num) hn hnI
  have l3n : Tendsto (fun x => Li₃ (-x)) (𝓝[>] 0) (𝓝 0) := by
    simpa [Li₃_zero] using tendsto_Li₃_comp (by norm_num) hn hnI
  have ll2n : Tendsto (fun x => log x * Li₂ (-x)) (𝓝[>] 0) (𝓝 0) := by
    refine i15V_tendsto_log_mul_of_abs_le (C := π ^ 2 / 6) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have := abs_Li₂_le (y := -x) (by rw [abs_neg, abs_of_pos hx.1]; exact hx.2.le)
    rwa [abs_neg, abs_of_pos hx.1] at this
  have hlp := QED.Polylog.tendsto_log_mul_log_one_add_zero
  have hlm := tendsto_log_mul_log_one_sub_zero
  have hxl := tendsto_mul_log_zero
  have hxl2 := tendsto_mul_log_sq_zero
  have h := (((((((((((((hx0.pow 2).const_mul 4).sub_const 4).mul (l2n.add hlp)).add
    ((((hx0.pow 2).const_mul 2).sub_const 2).mul (tendsto_Li₂_zero_right.add hlm))).sub
    (((l3n.const_mul 2).sub ll2n).const_mul 8)).add
    ((tendsto_log_mul_Li₂_zero.sub (tendsto_Li₃_zero_right.const_mul 2)).const_mul 4)).add
    hxl2).sub ((hx0.mul hxl2).const_mul (3 / 4))).sub ((hx0.mul hxl).const_mul (21 / 4))).add
    (hxl.const_mul 4)).sub (hx0.const_mul 12)).add ((hx0.pow 2).const_mul (37 / 8))).add
    (((hx0.div_const 3).sub ((hx0.pow 2).div_const 12)).const_mul (π ^ 2))
  convert h using 1
  · funext y
    simp only [i15WPhi]
    ring
  · ring_nf

theorem tendsto_i15WPhi_one :
    Tendsto i15WPhi (𝓝[<] 1) (𝓝 (π ^ 2 / 4 + 4 * zeta3 - 59 / 8)) := by
  have hx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hn : Tendsto (fun x : ℝ => -x) (𝓝[<] 1) (𝓝 (-1)) := hx1.neg
  have hnI : ∀ᶠ x in 𝓝[<] (1 : ℝ), -x ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have l2n : Tendsto (fun x => Li₂ (-x)) (𝓝[<] 1) (𝓝 (Li₂ (-1))) :=
    tendsto_Li₂_comp (by norm_num) hn hnI
  have l3n : Tendsto (fun x => Li₃ (-x)) (𝓝[<] 1) (𝓝 (Li₃ (-1))) :=
    tendsto_Li₃_comp (by norm_num) hn hnI
  have hlog : Tendsto (fun x : ℝ => log x) (𝓝[<] 1) (𝓝 0) := by
    have := (Real.continuousAt_log (one_ne_zero (α := ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  have hlp : Tendsto (fun x : ℝ => log (1 + x)) (𝓝[<] 1) (𝓝 (log (1 + 1))) :=
    ((Real.continuousAt_log (by norm_num : (1 : ℝ) + 1 ≠ 0)).tendsto.comp
      (hx1.const_add 1))
  have hlm := tendsto_log_mul_log_one_sub_one
  have h := (((((((((((((hx1.pow 2).const_mul 4).sub_const 4).mul (l2n.add (hlog.mul hlp))).add
    ((((hx1.pow 2).const_mul 2).sub_const 2).mul (tendsto_Li₂_one_left.add hlm))).sub
    (((l3n.const_mul 2).sub (hlog.mul l2n)).const_mul 8)).add
    (((hlog.mul tendsto_Li₂_one_left).sub (tendsto_Li₃_one_left.const_mul 2)).const_mul 4)).add
    (hx1.mul (hlog.pow 2))).sub (((hx1.pow 2).mul (hlog.pow 2)).const_mul (3 / 4))).sub
    (((hx1.pow 2).mul hlog).const_mul (21 / 4))).add ((hx1.mul hlog).const_mul 4)).sub
    (hx1.const_mul 12)).add ((hx1.pow 2).const_mul (37 / 8))).add
    (((hx1.div_const 3).sub ((hx1.pow 2).div_const 12)).const_mul (π ^ 2))
  rw [Li₃_neg_one] at h
  convert h using 1
  · funext y
    simp only [i15WPhi]
  · ring_nf

/-- **`∫₀¹ h = π²/4 + 4 ζ(3) - 59/8`.** -/
theorem integral_i15Wh (hI : IntervalIntegrable i15Wh volume 0 1) :
    ∫ u in (0 : ℝ)..1, i15Wh u = π ^ 2 / 4 + 4 * zeta3 - 59 / 8 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun u hu => hasDerivAt_i15WPhi hu) hI tendsto_i15WPhi_zero tendsto_i15WPhi_one, sub_zero]

/-- **`∫∫ A₂₃ = π²/4 + 4 ζ(3) - 59/8`**, given its integrability on the square. -/
theorem integral_i15A23 (hA : IntegrableOn i15A23 (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15A23 z = π ^ 2 / 4 + 4 * zeta3 - 59 / 8 := by
  have hF : Integrable i15A23 ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [← volume_restrict_prod2]; exact hA
  rw [volume_restrict_prod2, integral_prod_symm _ hF]
  have hae : (fun u => ∫ x, i15A23 (x, u) ∂volume.restrict (Ioo (0 : ℝ) 1)) =ᵐ[volume.restrict
      (Ioo (0 : ℝ) 1)] i15Wh := by
    filter_upwards [hF.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with u hu1 hu2
    exact integral_i15A23_inner hu2 hu1
  rw [integral_congr_ae hae, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  refine integral_i15Wh ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr ?_)
  exact hF.integral_prod_right.congr hae

end QED.ThreeLoopD
