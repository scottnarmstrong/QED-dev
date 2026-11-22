/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemA2Y

/-!
# Set (d), master `I₉`: an antiderivative for the log-weighted `y`-integral of `S₁`

For `a, w > 0`, `b = a + w`, `P = a + w y`, the second Taylor coefficient of `Rem` needs

  `∫₀¹ (log y + log (1 - y)) S₁ / (y (1 - y)) dy`,

where `S₁(y) = f(P) - f(w y) - (1 - y) f(a) - y f(b) + y f(w)`, `f(t) = t log t`, is
`QED.ThreeLoopD.i9RemS 1` at `P₀ = a`. Pointwise,
`S₁ / (y (1 - y)) = a ℓ / y + b m / (1 - y) - w log y / (1 - y)` with `ℓ = log (P/a)` and
`m = log (P/b)`. This file writes down an antiderivative `QED.ThreeLoopD.i9A2HL` of the
weighted integrand, built from `Li₂`, `Li₃` and `F = QED.Polylog.logOneSubSqPrim` at the
arguments `y`, `1 - y`, `v = w y / P`, `z = b y / P` and `ρ = w (1 - y) / b`, all in `(0, 1)`,
and proves its derivative. Every `Li₂` term of the derivative cancels syntactically, so the
check is a polynomial identity in logarithms.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i9A2HL`.
-/

@[expose] public section

open Set Real QED.Polylog

namespace QED.ThreeLoopD

/-- `S₁` for general `a, w`: the `y`-subtraction of `t log t`. -/
noncomputable def i9A2S1 (a w y : ℝ) : ℝ :=
  (a + w * y) * Real.log (a + w * y) - w * y * Real.log (w * y) -
    (1 - y) * a * Real.log a - y * (a + w) * Real.log (a + w) + y * w * Real.log w

/-- `v = w y / P`. -/
noncomputable def i9A2v (a w y : ℝ) : ℝ := w * y / (a + w * y)

/-- `z = b y / P`. -/
noncomputable def i9A2z (a w y : ℝ) : ℝ := (a + w) * y / (a + w * y)

/-- `ρ = (w / b)(1 - y)`. -/
noncomputable def i9A2r (a w y : ℝ) : ℝ := w / (a + w) * (1 - y)

/-- `ℓ = log (P / a)`. -/
noncomputable def i9A2l (a w y : ℝ) : ℝ := Real.log ((a + w * y) / a)

/-- `m = log (P / b)`. -/
noncomputable def i9A2m (a w y : ℝ) : ℝ := Real.log ((a + w * y) / (a + w))

/-- **The antiderivative** of `(log y + log (1 - y)) S₁ / (y (1 - y))`. -/
noncomputable def i9A2HL (a w y : ℝ) : ℝ :=
  a * (Real.log y * Li₂ (i9A2v a w y) + Real.log y * i9A2l a w y ^ 2 / 2 - Li₃ (i9A2v a w y) -
      i9A2l a w y * Li₂ (i9A2v a w y) + logOneSubSqPrim (i9A2v a w y) - i9A2l a w y ^ 3 / 6 +
      (logOneSubSqPrim y - logOneSubSqPrim (i9A2z a w y) - logOneSubSqPrim (i9A2r a w y) -
        i9A2m a w y * Real.log (1 - y) ^ 2 + i9A2m a w y ^ 2 * Real.log (1 - y) +
        2 * Real.log ((a + w) / a) * i9A2m a w y * Real.log (1 - y) -
        2 * (Li₂ (i9A2r a w y) * Real.log (1 - y)) + 2 * Li₃ (i9A2r a w y) +
        2 * Real.log ((a + w) / a) * Li₂ (i9A2r a w y)) / 2) +
    (a + w) * (-(logOneSubSqPrim (1 - y) + logOneSubSqPrim (i9A2r a w y) -
        (Real.log y ^ 2 * Real.log (1 - y) - 2 * (i9A2m a w y * Real.log y * Real.log (1 - y)) +
          i9A2m a w y ^ 2 * Real.log (1 - y)) -
        2 * (Real.log y * Li₂ (i9A2z a w y) - i9A2m a w y * Li₂ (i9A2z a w y)) +
        2 * Li₃ (i9A2z a w y) +
        2 * (Real.log y * Li₂ (i9A2v a w y) - i9A2m a w y * Li₂ (i9A2v a w y)) -
        2 * Li₃ (i9A2v a w y)) / 2 +
      Li₂ (i9A2r a w y) * Real.log (1 - y) - Li₃ (i9A2r a w y)) +
    w * (-(Li₂ (1 - y) * Real.log (1 - y)) + 2 * (Real.log y * Li₂ y) + Li₃ (1 - y) -
      2 * Li₃ y + Real.log y ^ 2 * Real.log (1 - y))

/-! ### Chain rules -/

theorem i9A2L_hasDerivAt_Li₂ {g : ℝ → ℝ} {g' y : ℝ} (hg : HasDerivAt g g' y)
    (hm : g y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => Li₂ (g t)) (-Real.log (1 - g y) / g y * g') y :=
  (hasDerivAt_Li₂' hm).comp y hg

theorem i9A2L_hasDerivAt_Li₃ {g : ℝ → ℝ} {g' y : ℝ} (hg : HasDerivAt g g' y)
    (hm : g y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => Li₃ (g t)) (Li₂ (g y) / g y * g') y :=
  (hasDerivAt_Li₃' hm).comp y hg

theorem i9A2L_hasDerivAt_F {g : ℝ → ℝ} {g' y : ℝ} (hg : HasDerivAt g g' y)
    (hm : g y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => logOneSubSqPrim (g t)) (Real.log (1 - g y) ^ 2 / g y * g') y :=
  (hasDerivAt_logOneSubSqPrim hm).comp y hg

/-! ### The arguments -/

theorem hasDerivAt_i9A2v {a w : ℝ} (ha : 0 < a) (hw : 0 < w) {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt (i9A2v a w) (w * a / (a + w * y) ^ 2) y := by
  show HasDerivAt (fun y => w * y / (a + w * y)) _ y
  have hP : 0 < a + w * y := by positivity
  have h1 : HasDerivAt (fun y => w * y) w y := by simpa using (hasDerivAt_id y).const_mul w
  convert h1.div (h1.const_add a) hP.ne' using 1
  field_simp
  ring

theorem hasDerivAt_i9A2z {a w : ℝ} (ha : 0 < a) (hw : 0 < w) {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt (i9A2z a w) ((a + w) * a / (a + w * y) ^ 2) y := by
  show HasDerivAt (fun y => (a + w) * y / (a + w * y)) _ y
  have hP : 0 < a + w * y := by positivity
  have h1 : HasDerivAt (fun y => (a + w) * y) (a + w) y := by
    simpa using (hasDerivAt_id y).const_mul (a + w)
  have h2 : HasDerivAt (fun y => a + w * y) w y := by
    simpa using ((hasDerivAt_id y).const_mul w).const_add a
  convert h1.div h2 hP.ne' using 1
  field_simp
  ring

theorem hasDerivAt_i9A2r (a w y : ℝ) : HasDerivAt (i9A2r a w) (-(w / (a + w))) y := by
  show HasDerivAt (fun y => w / (a + w) * (1 - y)) _ y
  simpa using ((hasDerivAt_id y).const_sub 1).const_mul (w / (a + w))

theorem hasDerivAt_i9A2l {a w : ℝ} (ha : 0 < a) (hw : 0 < w) {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt (i9A2l a w) (w / (a + w * y)) y := by
  show HasDerivAt (fun y => Real.log ((a + w * y) / a)) _ y
  have hP : 0 < a + w * y := by positivity
  have h2 : HasDerivAt (fun y => (a + w * y) / a) (w / a) y := by
    simpa using (((hasDerivAt_id y).const_mul w).const_add a).div_const a
  convert h2.log (by positivity) using 1
  field_simp

theorem hasDerivAt_i9A2m {a w : ℝ} (ha : 0 < a) (hw : 0 < w) {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt (i9A2m a w) (w / (a + w * y)) y := by
  show HasDerivAt (fun y => Real.log ((a + w * y) / (a + w))) _ y
  have hP : 0 < a + w * y := by positivity
  have h2 : HasDerivAt (fun y => (a + w * y) / (a + w)) (w / (a + w)) y := by
    simpa using (((hasDerivAt_id y).const_mul w).const_add a).div_const (a + w)
  convert h2.log (by positivity) using 1
  field_simp

theorem i9A2v_mem {a w y : ℝ} (ha : 0 < a) (hw : 0 < w) (hy : y ∈ Ioo (0 : ℝ) 1) :
    i9A2v a w y ∈ Ioo (0 : ℝ) 1 := by
  have := hy.1
  have hP : 0 < a + w * y := by positivity
  exact ⟨by unfold i9A2v; positivity, by unfold i9A2v; rw [div_lt_one hP]; linarith⟩

theorem i9A2z_mem {a w y : ℝ} (ha : 0 < a) (hw : 0 < w) (hy : y ∈ Ioo (0 : ℝ) 1) :
    i9A2z a w y ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hy
  have hP : 0 < a + w * y := by positivity
  exact ⟨by unfold i9A2z; positivity, by unfold i9A2z; rw [div_lt_one hP]; nlinarith⟩

theorem i9A2r_mem {a w y : ℝ} (ha : 0 < a) (hw : 0 < w) (hy : y ∈ Ioo (0 : ℝ) 1) :
    i9A2r a w y ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hy
  have hb : 0 < a + w := by positivity
  have h1' : 0 < 1 - y := by linarith
  refine ⟨by unfold i9A2r; positivity, ?_⟩
  unfold i9A2r
  rw [div_mul_eq_mul_div, div_lt_one hb]
  nlinarith

/-! ### Logarithms of the complements -/

theorem log_one_sub_i9A2v {a w y : ℝ} (ha : 0 < a) (hP : 0 < a + w * y) :
    Real.log (1 - i9A2v a w y) = Real.log a - Real.log (a + w * y) := by
  have e : 1 - i9A2v a w y = a / (a + w * y) := by unfold i9A2v; field_simp; ring
  rw [e, Real.log_div ha.ne' hP.ne']

theorem log_one_sub_i9A2z {a w y : ℝ} (ha : 0 < a) (hP : 0 < a + w * y) (hy : y < 1) :
    Real.log (1 - i9A2z a w y) = Real.log a + Real.log (1 - y) - Real.log (a + w * y) := by
  have e : 1 - i9A2z a w y = a * (1 - y) / (a + w * y) := by unfold i9A2z; field_simp; ring
  rw [e, Real.log_div (by nlinarith) hP.ne', Real.log_mul ha.ne' (by linarith)]

theorem log_one_sub_i9A2r {a w y : ℝ} (hb : 0 < a + w) (hP : 0 < a + w * y) :
    Real.log (1 - i9A2r a w y) = Real.log (a + w * y) - Real.log (a + w) := by
  have e : 1 - i9A2r a w y = (a + w * y) / (a + w) := by unfold i9A2r; field_simp; ring
  rw [e, Real.log_div hP.ne' hb.ne']

/-! ### The derivative -/

/-- **The derivative of the antiderivative.** -/
theorem hasDerivAt_i9A2HL {a w y : ℝ} (ha : 0 < a) (hw : 0 < w) (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => i9A2HL a w y)
      ((Real.log y + Real.log (1 - y)) * i9A2S1 a w y / (y * (1 - y))) y := by
  have hvm := i9A2v_mem ha hw hy
  have hzm := i9A2z_mem ha hw hy
  have hrm := i9A2r_mem ha hw hy
  obtain ⟨hy0, hy1⟩ := hy
  have hy1' : 0 < 1 - y := by linarith
  have hP : 0 < a + w * y := by positivity
  have hb : 0 < a + w := by positivity
  have hsm : 1 - y ∈ Ioo (0 : ℝ) 1 := ⟨hy1', by linarith⟩
  have hym : (fun t : ℝ => t) y ∈ Ioo (0 : ℝ) 1 := ⟨hy0, hy1⟩
  have hv := hasDerivAt_i9A2v ha hw hy0.le
  have hz := hasDerivAt_i9A2z ha hw hy0.le
  have hr := hasDerivAt_i9A2r a w y
  have hl := hasDerivAt_i9A2l ha hw hy0.le
  have hm := hasDerivAt_i9A2m ha hw hy0.le
  have hs : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub 1
  have hid : HasDerivAt (fun y : ℝ => y) 1 y := hasDerivAt_id' y
  have hY : HasDerivAt (fun y => Real.log y) y⁻¹ y := Real.hasDerivAt_log hy0.ne'
  have hY1 : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - y)) y := hs.log hy1'.ne'
  have hLv := i9A2L_hasDerivAt_Li₂ hv hvm
  have hTv := i9A2L_hasDerivAt_Li₃ hv hvm
  have hFv := i9A2L_hasDerivAt_F hv hvm
  have hLz := i9A2L_hasDerivAt_Li₂ hz hzm
  have hTz := i9A2L_hasDerivAt_Li₃ hz hzm
  have hFz := i9A2L_hasDerivAt_F hz hzm
  have hLr := i9A2L_hasDerivAt_Li₂ hr hrm
  have hTr := i9A2L_hasDerivAt_Li₃ hr hrm
  have hFr := i9A2L_hasDerivAt_F hr hrm
  have hLy := i9A2L_hasDerivAt_Li₂ hid hym
  have hTy := i9A2L_hasDerivAt_Li₃ hid hym
  have hFy := i9A2L_hasDerivAt_F hid hym
  have hLs := i9A2L_hasDerivAt_Li₂ hs hsm
  have hTs := i9A2L_hasDerivAt_Li₃ hs hsm
  have hFs := i9A2L_hasDerivAt_F hs hsm
  have hA := (((((hY.mul hLv).add ((hY.mul (hl.pow 2)).div_const 2)).sub hTv).sub
    (hl.mul hLv)).add hFv).sub ((hl.pow 3).div_const 6) |>.add
    ((((((((((hFy.sub hFz).sub hFr).sub (hm.mul (hY1.pow 2))).add ((hm.pow 2).mul hY1)).add
      ((hm.const_mul (2 * Real.log ((a + w) / a))).mul hY1)).sub ((hLr.mul hY1).const_mul 2)).add
      (hTr.const_mul 2)).add (hLr.const_mul (2 * Real.log ((a + w) / a)))).div_const 2))
  have hB := ((((((((hFs.add hFr).sub ((((hY.pow 2).mul hY1).sub
    (((hm.mul hY).mul hY1).const_mul 2)).add ((hm.pow 2).mul hY1))).sub
    (((hY.mul hLz).sub (hm.mul hLz)).const_mul 2)).add (hTz.const_mul 2)).add
    (((hY.mul hLv).sub (hm.mul hLv)).const_mul 2)).sub (hTv.const_mul 2)).neg.div_const 2).add
    (hLr.mul hY1)).sub hTr
  have hW := (((((hLs.mul hY1).neg).add ((hY.mul hLy).const_mul 2)).add hTs).sub
    (hTy.const_mul 2)).add ((hY.pow 2).mul hY1)
  have h := ((hA.const_mul a).add (hB.const_mul (a + w))).add (hW.const_mul w)
  convert h using 1
  · funext t
    simp only [i9A2HL, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply]
  -- the derivative identity
  have e3 : (1 : ℝ) - (1 - y) = y := by ring
  simp only [e3, Pi.pow_apply, Pi.mul_apply]
  rw [log_one_sub_i9A2v ha hP, log_one_sub_i9A2z ha hP hy1, log_one_sub_i9A2r hb hP]
  have el : i9A2l a w y = Real.log (a + w * y) - Real.log a := Real.log_div hP.ne' ha.ne'
  have em : i9A2m a w y = Real.log (a + w * y) - Real.log (a + w) :=
    Real.log_div hP.ne' hb.ne'
  rw [el, em, Real.log_div hb.ne' ha.ne']
  unfold i9A2S1
  rw [Real.log_mul hw.ne' hy0.ne']
  generalize Li₂ (i9A2v a w y) = Lv
  generalize Li₂ (i9A2z a w y) = Lz
  generalize Li₂ (i9A2r a w y) = Lr
  generalize Li₂ y = Ly
  generalize Li₂ (1 - y) = Ls
  unfold i9A2v i9A2z i9A2r
  generalize Real.log (a + w * y) = LP
  generalize Real.log y = Y
  generalize Real.log (1 - y) = Y1
  generalize Real.log a = La
  generalize Real.log (a + w) = Lb
  generalize Real.log w = Lw
  field_simp
  ring

end QED.ThreeLoopD
