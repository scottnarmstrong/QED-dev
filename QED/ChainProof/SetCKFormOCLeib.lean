/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCPhiS

/-!
# Set (c), Stage K, closed forms: `𝓛(a, X)` and its `X`-derivative `ℓ_a`

Helper level (no frozen statement). Item 2 (OCLeib) of the `ρ_oC` route (Stage K notes,
Session 30+). For `a ∈ [0, 1]` and `X ∈ (0, 1)`,

`𝓛(a, X) = ∫_{(0,X)} β_c(a, x) log v(x, X) dx` (**`formOCLL`**)

equals, after `x = X s` (**`formOCLL_eq`**), `∫_{(0,1)} X β(X s) Λ(s, X) ds` with
`β(y) = -y⁴/(4 (1 - a y)(1 - y + a y))` (`formOCbr`) and
`Λ = 2 log X + log(1 - s) + log(1 + s - X s) - log(1 - X) - log(1 - X s)` (`formOCLam`).
The `s`-integrand and its `X`-derivative split as `A + B log(1 - s)` with `A`, `B` continuous
on the compact box `[0, 1] × [0, X₁] × [0, 1]` (`X log X` is continuous), whence the bound
`C (1 + |log(1 - s)|)`; differentiation under the integral sign gives
(**`hasDerivAt_formOCLs`**) the derivative

`ℓ_a(X) = ∫_{(0,1)} [(X s)⁴ β̃(X s) Λ + β(X s) X ∂_X Λ] ds` (**`formOCell`**),

`ℓ_a` is bounded on `[0, 1] × [0, X₁]` (**`formOCell_bound`**), jointly measurable
(**`stronglyMeasurable_formOCell`**), and (FTC, `𝓛(a, 0⁺) = 0` by dominated convergence)

`𝓛(a, X) = ∫₀^X ℓ_a` (**`formOCLL_eq_integral`**).
-/

@[expose] public section

open Real Set Filter MeasureTheory Topology

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- `β_c` in letters: `-y⁴/(4 (1 - a y)(1 - y + a y))`. -/
noncomputable def formOCbr (a y : ℝ) : ℝ := -y ^ 4 / (4 * ((1 - a * y) * (1 - y + a * y)))

/-- The derivative of `formOCbr a` in `y`. -/
noncomputable def formOCbrD (a y : ℝ) : ℝ :=
  -(4 * y ^ 3 * ((1 - a * y) * (1 - y + a * y)) -
    y ^ 4 * (-a * (1 - y + a * y) + (1 - a * y) * (a - 1))) /
    (4 * ((1 - a * y) * (1 - y + a * y)) ^ 2)

/-- `(y β_c)' = y⁴ formOCbrE`. -/
noncomputable def formOCbrE (a y : ℝ) : ℝ :=
  -(5 * ((1 - a * y) * (1 - y + a * y)) -
    y * (-a * (1 - y + a * y) + (1 - a * y) * (a - 1))) /
    (4 * ((1 - a * y) * (1 - y + a * y)) ^ 2)

theorem hasDerivAt_formOCbr {a y : ℝ} (h : (1 - a * y) * (1 - y + a * y) ≠ 0) :
    HasDerivAt (formOCbr a) (formOCbrD a y) y := by
  have h1 : HasDerivAt (fun y => 1 - a * y) (-a) y := by
    simpa using ((hasDerivAt_id' y).const_mul a).const_sub 1
  have h2 : HasDerivAt (fun y => 1 - y + a * y) (a - 1) y := by
    have := ((hasDerivAt_id' y).const_sub 1).add ((hasDerivAt_id' y).const_mul a)
    convert this using 1
    ring
  have hP : HasDerivAt (fun y => 4 * ((1 - a * y) * (1 - y + a * y)))
      (4 * (-a * (1 - y + a * y) + (1 - a * y) * (a - 1))) y := by
    exact (h1.mul h2).const_mul 4
  have h4 : (4 : ℝ) * ((1 - a * y) * (1 - y + a * y)) ≠ 0 := mul_ne_zero four_ne_zero h
  have h5 : HasDerivAt (fun y => -y ^ 4) (-(4 * y ^ 3)) y := by
    have := (hasDerivAt_pow 4 y).neg
    simp only [Nat.cast_ofNat] at this
    convert this using 1
  have h6 : HasDerivAt (formOCbr a) _ y := h5.div hP h4
  refine h6.congr_deriv ?_
  unfold formOCbrD
  field_simp
  ring

theorem formOCbr_add_mul_brD {a y : ℝ} (_h : (1 - a * y) * (1 - y + a * y) ≠ 0) :
    formOCbr a y + y * formOCbrD a y = y ^ 4 * formOCbrE a y := by
  unfold formOCbr formOCbrD formOCbrE
  field_simp
  ring

/-- `Λ(s, X)`: `log v(X s, X) = Λ(s, X)` on `(0, 1)`. -/
noncomputable def formOCLam (X s : ℝ) : ℝ :=
  2 * log X + log (1 - s) + log (1 + s - X * s) - log (1 - X) - log (1 - X * s)

/-- `X ∂_X Λ(s, X)`. -/
noncomputable def formOCLI (X s : ℝ) : ℝ :=
  2 - X * s / (1 + s - X * s) + X / (1 - X) + X * s / (1 - X * s)

/-- The `s`-integrand of `𝓛`: `X β(X s) Λ(s, X)`. -/
noncomputable def formOCLF (a X s : ℝ) : ℝ := X * formOCbr a (X * s) * formOCLam X s

/-- Its `X`-derivative. -/
noncomputable def formOCLg (a X s : ℝ) : ℝ :=
  (X * s) ^ 4 * formOCbrE a (X * s) * formOCLam X s + formOCbr a (X * s) * formOCLI X s

/-- **`ℓ_a(X)`** in integral form. -/
noncomputable def formOCell (a X : ℝ) : ℝ := ∫ s in Ioo (0 : ℝ) 1, formOCLg a X s

/-- **`𝓛(a, X) = ∫₀^X β_c(a, x) log v(x, X) dx`**. -/
noncomputable def formOCLL (a X : ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) X, formOCbeta a x * log (scOutVX x X)

/-- `𝓛` after `x = X s`. -/
noncomputable def formOCLs (a X : ℝ) : ℝ := ∫ s in Ioo (0 : ℝ) 1, formOCLF a X s

section

variable {a X s : ℝ}

theorem hasDerivAt_formOCLF (ha : a ∈ Icc (0 : ℝ) 1) (hX : X ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun X => formOCLF a X s) (formOCLg a X s) X := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hX0, hX1⟩ := hX
  obtain ⟨hs0, hs1⟩ := hs
  have hXs : X * s < X := mul_lt_of_lt_one_right hX0 hs1
  have hXs0 : 0 < X * s := mul_pos hX0 hs0
  have hL : 0 < 1 - a * (X * s) := by nlinarith [mul_nonneg ha0 hXs0.le]
  have hM : 0 < 1 - X * s + a * (X * s) := by nlinarith [mul_nonneg ha0 hXs0.le]
  have hP : (1 - a * (X * s)) * (1 - X * s + a * (X * s)) ≠ 0 := (mul_pos hL hM).ne'
  have h1 : 0 < 1 + s - X * s := by nlinarith
  have h2 : 0 < 1 - X := by linarith
  have h3 : 0 < 1 - X * s := by linarith
  have hb : HasDerivAt (fun X => X * formOCbr a (X * s))
      ((X * s) ^ 4 * formOCbrE a (X * s)) X := by
    have hc : HasDerivAt (fun X => formOCbr a (X * s)) (formOCbrD a (X * s) * s) X :=
      HasDerivAt.comp (h₂ := formOCbr a) (h := fun X => X * s) X (hasDerivAt_formOCbr hP)
        (hasDerivAt_mul_const s)
    have := (hasDerivAt_id' X).mul hc
    convert this using 1
    rw [← formOCbr_add_mul_brD hP]
    ring
  have hl : HasDerivAt (fun X => formOCLam X s)
      (2 / X - s / (1 + s - X * s) + 1 / (1 - X) + s / (1 - X * s)) X := by
    have e1 := ((hasDerivAt_id' X).log hX0.ne').const_mul 2
    have e2 := (((hasDerivAt_id' X).mul_const s).const_sub (1 + s)).log h1.ne'
    have e3 := ((hasDerivAt_id' X).const_sub 1).log h2.ne'
    have e4 := (((hasDerivAt_id' X).mul_const s).const_sub 1).log h3.ne'
    have := ((((e1.add_const (log (1 - s))).add e2).sub e3).sub e4)
    convert this using 1
    · funext X
      simp only [formOCLam, Pi.add_apply, Pi.sub_apply]
    · field_simp
      ring
  have := hb.mul hl
  unfold formOCLF formOCLg formOCLI
  convert this using 1
  field_simp

theorem formOCLL_zero (a : ℝ) : formOCLL a 0 = 0 := by
  simp [formOCLL]

theorem formOCLs_zero (a : ℝ) : formOCLs a 0 = 0 := by
  simp [formOCLs, formOCLF]

/-- **`x = X s`**: `𝓛 = formOCLs` on `(0, 1)`. -/
theorem formOCLL_eq (hX : X ∈ Ioo (0 : ℝ) 1) : formOCLL a X = formOCLs a X := by
  have key : ∀ s ∈ Ioo (0 : ℝ) 1, formOCbeta a (X * s) * log (scOutVX (X * s) X) =
      formOCbr a (X * s) * formOCLam X s := by
    intro s hs
    have hXs0 : 0 < X * s := mul_pos hX.1 hs.1
    have hXs : X * s < X := mul_lt_of_lt_one_right hX.1 hs.2
    have h1s : 0 < 1 - s := by linarith [hs.2]
    have h2 : 0 < 1 + s - X * s := by nlinarith [hs.1, hX.2]
    rw [formOCbeta_eq (by linarith [hX.2]), formOC_logv_eq hX.2 ⟨hXs0, hXs⟩,
      show X - X * s = X * (1 - s) by ring, show X + X * s - X * (X * s) = X * (1 + s - X * s)
        by ring, log_mul hX.1.ne' h1s.ne', log_mul hX.1.ne' h2.ne']
    unfold formOCbr formOCLam
    ring
  unfold formOCLL formOCLs
  have hcv : ∫ x in Ioo (0 : ℝ) X, formOCbeta a x * log (scOutVX x X) =
      X * ∫ s in Ioo (0 : ℝ) 1, formOCbeta a (X * s) * log (scOutVX (X * s) X) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hX.1.le, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_mul_left (fun x => formOCbeta a x * log (scOutVX x X))
        hX.1.ne', mul_zero, mul_one, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hX.1.ne',
      one_mul]
  rw [hcv, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  rw [key s hs]
  unfold formOCLF
  ring

end

/-- `x log x` (continuous on `ℝ`). -/
noncomputable def formOCxlog (x : ℝ) : ℝ := x * log x

/-- The box `[0, 1] × [0, X₁] × [0, 1]` of `(a, X, s)`. -/
def formOCLBox (X₁ : ℝ) : Set (ℝ × ℝ × ℝ) := Icc 0 1 ×ˢ (Icc 0 X₁ ×ˢ Icc 0 1)

/-- The `log`-free part of `formOCLF`. -/
noncomputable def formOCLAF (a X s : ℝ) : ℝ :=
  2 * formOCbr a (X * s) * formOCxlog X +
    X * formOCbr a (X * s) * (log (1 + s - X * s) - log (1 - X) - log (1 - X * s))

/-- The `log`-free part of `formOCLg`. -/
noncomputable def formOCLAg (a X s : ℝ) : ℝ :=
  2 * X ^ 3 * s ^ 4 * formOCbrE a (X * s) * formOCxlog X +
    (X * s) ^ 4 * formOCbrE a (X * s) * (log (1 + s - X * s) - log (1 - X) - log (1 - X * s)) +
    formOCbr a (X * s) * formOCLI X s

theorem formOCLF_split (a X s : ℝ) :
    formOCLF a X s = formOCLAF a X s + X * formOCbr a (X * s) * log (1 - s) := by
  unfold formOCLF formOCLAF formOCLam formOCxlog
  ring

theorem formOCLg_split (a X s : ℝ) :
    formOCLg a X s = formOCLAg a X s + (X * s) ^ 4 * formOCbrE a (X * s) * log (1 - s) := by
  unfold formOCLg formOCLAg formOCLam formOCxlog
  ring

section

variable {X₁ : ℝ}

theorem formOCLBox_pos (hX₁ : X₁ < 1) {p : ℝ × ℝ × ℝ} (hp : p ∈ formOCLBox X₁) :
    0 < 1 - p.1 * (p.2.1 * p.2.2) ∧ 0 < 1 - p.2.1 * p.2.2 + p.1 * (p.2.1 * p.2.2) ∧
      0 < 1 + p.2.2 - p.2.1 * p.2.2 ∧ 0 < 1 - p.2.1 ∧ 0 < 1 - p.2.1 * p.2.2 := by
  obtain ⟨⟨ha0, ha1⟩, ⟨hX0, hX1⟩, ⟨hs0, hs1⟩⟩ := hp
  have hy : p.2.1 * p.2.2 ≤ p.2.1 := mul_le_of_le_one_right hX0 hs1
  have hy0 : 0 ≤ p.2.1 * p.2.2 := mul_nonneg hX0 hs0
  have hay : p.1 * (p.2.1 * p.2.2) ≤ p.2.1 * p.2.2 := mul_le_of_le_one_left hy0 ha1
  have hay0 : 0 ≤ p.1 * (p.2.1 * p.2.2) := mul_nonneg ha0 hy0
  refine ⟨by linarith, by linarith, by nlinarith, by linarith, by linarith⟩

theorem formOCL_continuousOn (hX₁ : X₁ < 1) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => formOCLAF p.1 p.2.1 p.2.2) (formOCLBox X₁) ∧
    ContinuousOn (fun p : ℝ × ℝ × ℝ => p.2.1 * formOCbr p.1 (p.2.1 * p.2.2))
      (formOCLBox X₁) ∧
    ContinuousOn (fun p : ℝ × ℝ × ℝ => formOCLAg p.1 p.2.1 p.2.2) (formOCLBox X₁) ∧
    ContinuousOn (fun p : ℝ × ℝ × ℝ => (p.2.1 * p.2.2) ^ 4 * formOCbrE p.1 (p.2.1 * p.2.2))
      (formOCLBox X₁) := by
  have hx : Continuous formOCxlog := Real.continuous_mul_log
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩ <;>
  · obtain ⟨hL, hM, h1, h2, h3⟩ := formOCLBox_pos hX₁ hp
    have hP : (1 - p.1 * (p.2.1 * p.2.2)) * (1 - p.2.1 * p.2.2 + p.1 * (p.2.1 * p.2.2)) ≠ 0 :=
      (mul_pos hL hM).ne'
    have h2P := mul_ne_zero (two_ne_zero (α := ℝ)) hP
    have h4P := mul_ne_zero (four_ne_zero (α := ℝ)) hP
    have h4P2 := mul_ne_zero (four_ne_zero (α := ℝ)) (pow_ne_zero 2 hP)
    have h1' := h1.ne'
    have h2' := h2.ne'
    have h3' := h3.ne'
    refine ContinuousAt.continuousWithinAt ?_
    simp only [formOCLAF, formOCLAg, formOCbr, formOCbrE, formOCLI]
    fun_prop (disch := assumption)

/-- `|A + B log(1 - s)| ≤ C (1 + |log(1 - s)|)` on a compact set. -/
theorem formOCL_bound_AB {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K) {A B : ℝ × ℝ × ℝ → ℝ}
    (hA : ContinuousOn A K) (hB : ContinuousOn B K) :
    ∃ C, 0 ≤ C ∧ ∀ p ∈ K, |A p + B p * log (1 - p.2.2)| ≤ C * (1 + |log (1 - p.2.2)|) := by
  obtain ⟨CA, hCA⟩ := hK.exists_bound_of_continuousOn hA
  obtain ⟨CB, hCB⟩ := hK.exists_bound_of_continuousOn hB
  refine ⟨max CA 0 + max CB 0, by positivity, fun p hp => ?_⟩
  have hA' : |A p| ≤ max CA 0 := (hCA p hp).trans (le_max_left _ _)
  have hB' : |B p| ≤ max CB 0 := (hCB p hp).trans (le_max_left _ _)
  have hl := abs_nonneg (log (1 - p.2.2))
  calc |A p + B p * log (1 - p.2.2)| ≤ |A p| + |B p| * |log (1 - p.2.2)| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ max CA 0 + max CB 0 * |log (1 - p.2.2)| := by gcongr
    _ ≤ (max CA 0 + max CB 0) * (1 + |log (1 - p.2.2)|) := by
        nlinarith [le_max_right CA 0, le_max_right CB 0]

theorem isCompact_formOCLBox (X₁ : ℝ) : IsCompact (formOCLBox X₁) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

theorem formOCLF_bound (hX₁ : X₁ < 1) : ∃ C, 0 ≤ C ∧ ∀ a ∈ Icc (0 : ℝ) 1, ∀ X ∈ Icc 0 X₁,
    ∀ s ∈ Icc (0 : ℝ) 1, |formOCLF a X s| ≤ C * (1 + |log (1 - s)|) := by
  obtain ⟨h1, h2, -, -⟩ := formOCL_continuousOn hX₁
  obtain ⟨C, hC0, hC⟩ := formOCL_bound_AB (isCompact_formOCLBox X₁) h1 h2
  refine ⟨C, hC0, fun a ha X hX s hs => ?_⟩
  rw [formOCLF_split]
  exact hC (a, X, s) ⟨ha, hX, hs⟩

theorem formOCLg_bound (hX₁ : X₁ < 1) : ∃ C, 0 ≤ C ∧ ∀ a ∈ Icc (0 : ℝ) 1, ∀ X ∈ Icc 0 X₁,
    ∀ s ∈ Icc (0 : ℝ) 1, |formOCLg a X s| ≤ C * (1 + |log (1 - s)|) := by
  obtain ⟨-, -, h1, h2⟩ := formOCL_continuousOn hX₁
  obtain ⟨C, hC0, hC⟩ := formOCL_bound_AB (isCompact_formOCLBox X₁) h1 h2
  refine ⟨C, hC0, fun a ha X hX s hs => ?_⟩
  rw [formOCLg_split]
  exact hC (a, X, s) ⟨ha, hX, hs⟩

end

theorem formOCL_integrableOn_log (C : ℝ) :
    Integrable (fun s => C * (1 + |log (1 - s)|)) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have h : IntervalIntegrable (fun s => log (1 - s)) volume 0 1 := by
    have := (intervalIntegral.intervalIntegrable_log' (a := 1) (b := 0)).comp_sub_left 1
    simpa using this
  have h2 : IntegrableOn (fun s => |log (1 - s)|) (Ioo (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h.abs
  exact ((integrable_const 1).add h2).const_mul C

theorem measurable_formOCLF (a X : ℝ) : Measurable (formOCLF a X) := by
  unfold formOCLF formOCbr formOCLam
  fun_prop

theorem measurable_formOCLg (a X : ℝ) : Measurable (formOCLg a X) := by
  unfold formOCLg formOCbr formOCbrE formOCLam formOCLI
  fun_prop

section

variable {a X : ℝ}

/-- **Leibniz**: `formOCLs a` has derivative `ℓ_a` on `(0, 1)`. -/
theorem hasDerivAt_formOCLs (ha : a ∈ Icc (0 : ℝ) 1) (hX : X ∈ Ioo (0 : ℝ) 1) :
    Integrable (formOCLg a X) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
      HasDerivAt (formOCLs a) (formOCell a X) X := by
  set X₁ := (1 + X) / 2 with hX₁d
  have hX₁ : X₁ < 1 := by linarith [hX.2]
  obtain ⟨C, -, hC⟩ := formOCLg_bound hX₁
  obtain ⟨CF, -, hCF⟩ := formOCLF_bound hX₁
  have hU : Ioo (X / 2) X₁ ∈ 𝓝 X := Ioo_mem_nhds (by linarith [hX.1]) (by linarith [hX.2])
  have hFi : Integrable (formOCLF a X) (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine (formOCL_integrableOn_log CF).mono' (measurable_formOCLF a X).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact hCF a ha X ⟨hX.1.le, by linarith [hX.2]⟩ s ⟨hs.1.le, hs.2.le⟩
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (F := fun X s => formOCLF a X s) (F' := fun X s => formOCLg a X s) hU
    (Eventually.of_forall fun X => (measurable_formOCLF a X).aestronglyMeasurable) hFi
    (measurable_formOCLg a X).aestronglyMeasurable
    (bound := fun s => C * (1 + |log (1 - s)|)) ?_ (formOCL_integrableOn_log C) ?_
  · exact this
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs X' hX'
    exact hC a ha X' ⟨by linarith [hX.1, hX'.1], hX'.2.le⟩ s ⟨hs.1.le, hs.2.le⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs X' hX'
    exact hasDerivAt_formOCLF ha ⟨by linarith [hX.1, hX'.1], by linarith [hX'.2]⟩ hs

/-- **Continuity of `formOCLs a` on `[0, X₁]`** (dominated convergence). -/
theorem continuousOn_formOCLs (ha : a ∈ Icc (0 : ℝ) 1) {X₁ : ℝ} (hX₁ : X₁ < 1) :
    ContinuousOn (formOCLs a) (Icc 0 X₁) := by
  obtain ⟨C, -, hC⟩ := formOCLF_bound hX₁
  obtain ⟨h1, h2, -, -⟩ := formOCL_continuousOn hX₁
  refine continuousOn_of_dominated (bound := fun s => C * (1 + |log (1 - s)|))
    (fun X _ => (measurable_formOCLF a X).aestronglyMeasurable) (fun X hX => ?_)
    (formOCL_integrableOn_log C) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact hC a ha X hX s ⟨hs.1.le, hs.2.le⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hm : MapsTo (fun X : ℝ => (a, X, s)) (Icc 0 X₁) (formOCLBox X₁) :=
      fun X hX => ⟨ha, hX, ⟨hs.1.le, hs.2.le⟩⟩
    have hc : Continuous fun X : ℝ => (a, X, s) := by fun_prop
    have e : (fun X => formOCLF a X s) = fun X => formOCLAF a X s +
        X * formOCbr a (X * s) * log (1 - s) := funext fun X => formOCLF_split a X s
    rw [e]
    exact (h1.comp hc.continuousOn hm).add ((h2.comp hc.continuousOn hm).mul continuousOn_const)

/-- **A uniform bound on `ℓ_a`.** -/
theorem formOCell_bound {X₁ : ℝ} (hX₁ : X₁ < 1) :
    ∃ M, ∀ a ∈ Icc (0 : ℝ) 1, ∀ X ∈ Icc 0 X₁, |formOCell a X| ≤ M := by
  obtain ⟨C, -, hC⟩ := formOCLg_bound hX₁
  refine ⟨∫ s in Ioo (0 : ℝ) 1, C * (1 + |log (1 - s)|), fun a ha X hX => ?_⟩
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (formOCL_integrableOn_log C) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact hC a ha X hX s ⟨hs.1.le, hs.2.le⟩

theorem stronglyMeasurable_formOCell :
    StronglyMeasurable fun q : ℝ × ℝ => formOCell q.1 q.2 := by
  have h : Measurable fun r : (ℝ × ℝ) × ℝ => formOCLg r.1.1 r.1.2 r.2 := by
    unfold formOCLg formOCbr formOCbrE formOCLam formOCLI
    fun_prop
  exact h.stronglyMeasurable.integral_prod_right

theorem stronglyMeasurable_formOCell_left (a : ℝ) : StronglyMeasurable (formOCell a) := by
  have h : Measurable fun r : ℝ × ℝ => formOCLg a r.1 r.2 := by
    unfold formOCLg formOCbr formOCbrE formOCLam formOCLI
    fun_prop
  exact h.stronglyMeasurable.integral_prod_right

/-- **`𝓛(a, X) = ∫₀^X ℓ_a`.** -/
theorem formOCLL_eq_integral (ha : a ∈ Icc (0 : ℝ) 1) (hX : X ∈ Ioo (0 : ℝ) 1) :
    formOCLL a X = ∫ X' in (0 : ℝ)..X, formOCell a X' := by
  have hd : ∀ x ∈ Ioo 0 X, HasDerivAt (formOCLs a) (formOCell a x) x := fun x hx =>
    (hasDerivAt_formOCLs ha ⟨hx.1, hx.2.trans hX.2⟩).2
  obtain ⟨M, hM⟩ := formOCell_bound hX.2
  have hi : IntervalIntegrable (formOCell a) volume 0 X := by
    refine (intervalIntegrable_iff_integrableOn_Ioo_of_le hX.1.le).2 ?_
    refine Measure.integrableOn_of_bounded (M := M) (by simp)
      (stronglyMeasurable_formOCell_left a).aestronglyMeasurable ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hM a ha x ⟨hx.1.le, hx.2.le⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hX.1.le
    (continuousOn_formOCLs ha hX.2) hd hi, formOCLs_zero, sub_zero, formOCLL_eq hX]

end

end QED.ChainProof.SetCK

end
