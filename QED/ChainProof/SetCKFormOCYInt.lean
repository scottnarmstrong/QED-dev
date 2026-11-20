/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCLaur
public import QED.ChainProof.SetCKFormOCThr

/-!
# Set (c), Stage K, closed forms: the `Y`-integrals of `k` and `κ` of the outer-massive corner

Helper level (no frozen statement). Steps 3a/4a of the `ρ_oC` route (Stage K notes, Session
28+). In the coordinates `y₃ = a Y` one has `m = Y² D₀` and `m + e v = Y² D` with
`D₀ = 1 + a(1 - a) Q(x)` (`formOCD0`) and `D = 1 + a(1 - a)(Q(x) + v)` (`formOCD`), so on
branch one (`Y > Y_c`, `formOC_branch_iff`) the weights `Y κ` and `Y k` are Laurent
polynomials in `Y` (**`formOC_kap_laur`**, **`formOC_k_laur`**; generated coefficients
`formOCkap*`, `formOCk*` with `D, D₀` as atoms). On branch two `κ = 0` and `k = -x²/(2v)`.
Hence, with `0 < Y_c < 1` (**`formOCYc_pos`**, **`formOCYc_lt_one`**:
`1 - Y_c = x D/((1 - a x)(x + a(Q(x) + v)))`):

* **`formOC_integral_kap`**: `∫₀¹ Y κ dY = formOCLaurI(κ-coefficients)(Y_c)`;
* **`formOC_integral_k`**: `∫₀¹ Y k dY = formOCLaurI(k-coefficients)(Y_c) - x² Y_c²/(4 v)`.
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- `D = 1 + a(1 - a)(Q(x) + v)`: `m + e v = Y² D` at `y₃ = a Y`. -/
noncomputable def formOCD (a x v : ℝ) : ℝ := 1 + a * (1 - a) * (setCKQ x + v)

/-- `D₀ = 1 + a(1 - a) Q(x)`: `m = Y² D₀` at `y₃ = a Y`. -/
noncomputable def formOCD0 (a x : ℝ) : ℝ := 1 + a * (1 - a) * setCKQ x

/-- Coefficient `n3` of `Y·kap₁`. -/
noncomputable def formOCkapn3 (x a v D D0 : ℝ) : ℝ :=
  -a^2*v^2*x*(x - 2)*(x - 1)/(4*D^2*D0)

/-- Coefficient `n2` of `Y·kap₁`. -/
noncomputable def formOCkapn2 (x a v D D0 : ℝ) : ℝ :=
  a*v*x*(D*x + a^2*v*x^2 - 3*a^2*v*x + 2*a^2*v + a*v*x^2 - 3*a*v*x + 2*a*v)/(2*D^2*D0)

/-- Coefficient `n1` of `Y·kap₁`. -/
noncomputable def formOCkapn1 (x a v D D0 : ℝ) : ℝ :=
  x*(D^2*x^3 + 2*D*a^2*v*x^4 - 4*D*a^2*v*x^3 - 2*D*a^2*v*x^2 + 4*D*a^2*v*x - 2*D*a*v*x^3
    + 6*D*a*v*x^2 - 8*D*a*v*x + 4*D*a*v - 4*a^3*v^2*x^3 + 16*a^3*v^2*x^2 - 20*a^3*v^2*x + 8*a^3*v^2
    - a^2*v^2*x^3 + 4*a^2*v^2*x^2 - 5*a^2*v^2*x + 2*a^2*v^2)/(4*D^2*D0*(x - 1))

/-- Coefficient `p0` of `Y·kap₁`. -/
noncomputable def formOCkapp0 (x a v D D0 : ℝ) : ℝ :=
  -x*(-D^2*a*x^4 + 2*D^2*a*x^3 + D^2*x^3 - 3*D^2*x^2 + 2*D^2*x + D*a^3*v*x^4 - 2*D*a^3*v*x^3
    + D*a^3*v*x^2 + D*a^2*v*x^4 - 4*D*a^2*v*x^3 + 3*D*a^2*v*x^2 - D*a*v*x^3 + 5*D*a*v*x^2
    - 7*D*a*v*x + 3*D*a*v - a^3*v^2*x^3 + 4*a^3*v^2*x^2 - 5*a^3*v^2*x + 2*a^3*v^2)/(2*D^2*D0*(x
    - 1))

/-- Coefficient `p1` of `Y·kap₁`. -/
noncomputable def formOCkapp1 (x a v D D0 : ℝ) : ℝ :=
  x*(a*x - 1)^2*(-D*x + a*v*x - a*v)/(2*D*D0)

/-- Coefficient `n3` of `Y·k₁`. -/
noncomputable def formOCkn3 (x a v D : ℝ) : ℝ :=
  -3*a^2*v^2*(x - 1)^2/(4*D^3)

/-- Coefficient `n2` of `Y·k₁`. -/
noncomputable def formOCkn2 (x a v D : ℝ) : ℝ :=
  a*v*(x - 1)*(-4*D*x + 2*D + 3*a^2*v*x - 3*a^2*v + 3*a*v*x - 3*a*v)/(2*D^3)

/-- Coefficient `n1` of `Y·k₁`. -/
noncomputable def formOCkn1 (x a v D : ℝ) : ℝ :=
  (-5*D^2*x^2 + 4*D^2*x + 8*D*a^2*v*x^3 - 6*D*a^2*v*x^2 - 2*D*a^2*v*x + 10*D*a*v*x^2 - 18*D*a*v*x
    + 8*D*a*v - 12*a^3*v^2*x^2 + 24*a^3*v^2*x - 12*a^3*v^2 - 3*a^2*v^2*x^2 + 6*a^2*v^2*x
    - 3*a^2*v^2)/(4*D^3)

/-- Coefficient `p0` of `Y·k₁`. -/
noncomputable def formOCkp0 (x a v D : ℝ) : ℝ :=
  -(-4*D^2*a*x^3 + D^2*a*x^2 + D^2*a*x - D^2*x^2 + 2*D^2*x + 4*D*a^3*v*x^3 - 7*D*a^3*v*x^2
    + 3*D*a^3*v*x + 4*D*a^2*v*x^3 - 5*D*a^2*v*x^2 + 3*D*a^2*v*x - 2*D*a^2*v + D*a*v*x^2 - 4*D*a*v*x
    + 3*D*a*v - 3*a^3*v^2*x^2 + 6*a^3*v^2*x - 3*a^3*v^2)/(2*D^3)

/-- Coefficient `p1` of `Y·k₁`. -/
noncomputable def formOCkp1 (x a v D : ℝ) : ℝ :=
  (-4*D*a^2*x^3 + 3*D*a^2*x^2 + D*a*x^2 - D*a*x + D*x + 4*a^3*v*x^3 - 7*a^3*v*x^2 + 3*a^3*v*x
    - 2*a^2*v*x^2 + 4*a^2*v*x - 2*a^2*v - a*v*x + a*v)/(2*D^2)

section

variable {a x v Y : ℝ}

theorem formOCD0_pos (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < formOCD0 a x := by
  have h1 : 0 < a * (1 - a) := mul_pos ha.1 (by linarith [ha.2])
  have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  unfold formOCD0
  positivity

theorem formOCD_pos (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    0 < formOCD a x v := by
  have h1 : 0 < a * (1 - a) := mul_pos ha.1 (by linarith [ha.2])
  have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  unfold formOCD
  positivity

theorem formOC_m_eq : scOutCm Y (a * Y) x = Y ^ 2 * formOCD0 a x := by
  unfold scOutCm formOCD0
  ring

theorem formOC_mev_eq : scOutCm Y (a * Y) x + a * Y * (Y - a * Y) * v = Y ^ 2 * formOCD a x v := by
  unfold scOutCm formOCD
  ring

theorem formOCYc_pos (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    0 < formOCYc a x v := by
  have hax : 0 < 1 - a * x := by nlinarith [ha.1, ha.2, hx.1, hx.2]
  have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have hd : 0 < x + a * (setCKQ x + v) := by have := ha.1; have := hx.1; positivity
  unfold formOCYc
  have := ha.1
  positivity

/-- `1 - Y_c = x D/((1 - a x)(x + a(Q(x) + v)))`, so `Y_c < 1`. -/
theorem formOCYc_lt_one (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    formOCYc a x v < 1 := by
  have hax : 0 < 1 - a * x := by nlinarith [ha.1, ha.2, hx.1, hx.2]
  have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hd : 0 < x + a * (setCKQ x + v) := by have := ha.1; have := hx.1; positivity
  have hD := formOCD_pos ha hx hv
  have hQ : setCKQ x * (1 - x) = x ^ 2 := by
    unfold setCKQ
    field_simp [(by linarith [hx.2] : (1 : ℝ) - x ≠ 0)]
  unfold formOCYc
  rw [div_lt_one (by positivity)]
  have key : (1 - a * x) * (x + a * (setCKQ x + v)) - a * v * (1 - x) = x * formOCD a x v := by
    unfold formOCD
    linear_combination a * hQ
  nlinarith [mul_pos hx.1 hD]

/-- **`Y κ` on branch one is a Laurent polynomial in `Y`.** -/
theorem formOC_kap_laur (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v)
    (hY : 0 < Y) :
    Y * (scOutRho x / scOutCm Y (a * Y) x *
        (cornerA0 x (a * Y) (Y - a * Y) + cornerA1 x (a * Y) (Y - a * Y) *
          (v / (scOutRho x * (scOutCm Y (a * Y) x + a * Y * (Y - a * Y) * v))) +
          cornerA2 x (a * Y) (Y - a * Y) *
            (v / (scOutRho x * (scOutCm Y (a * Y) x + a * Y * (Y - a * Y) * v))) ^ 2)) =
      formOCLaur (formOCkapn3 x a v (formOCD a x v) (formOCD0 a x))
        (formOCkapn2 x a v (formOCD a x v) (formOCD0 a x))
        (formOCkapn1 x a v (formOCD a x v) (formOCD0 a x))
        (formOCkapp0 x a v (formOCD a x v) (formOCD0 a x))
        (formOCkapp1 x a v (formOCD a x v) (formOCD0 a x)) Y := by
  have hD := (formOCD_pos ha hx hv).ne'
  have hD0 := (formOCD0_pos ha hx).ne'
  have h1x : x - 1 ≠ 0 := by linarith [hx.2]
  have h1x' : 1 - x ≠ 0 := by linarith [hx.2]
  have hx0 := hx.1.ne'
  have hY0 := hY.ne'
  rw [formOC_mev_eq, formOC_m_eq]
  generalize formOCD a x v = D at hD ⊢
  generalize formOCD0 a x = D0 at hD0 ⊢
  unfold formOCLaur formOCkapn3 formOCkapn2 formOCkapn1 formOCkapp0 formOCkapp1 cornerA0
    cornerA1 cornerA2 QED.TwoLoop.UnitSCReduce.cornerP1 cornerG cornerQ
    scOutRho
  field_simp
  ring

/-- **`Y k` on branch one is a Laurent polynomial in `Y`.** -/
theorem formOC_k_laur (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v)
    (hY : 0 < Y) :
    Y * (cornerC1 x (a * Y) (Y - a * Y) /
          (scOutCm Y (a * Y) x + a * Y * (Y - a * Y) * v) +
        cornerC2 x (a * Y) (Y - a * Y) * v /
          (scOutRho x * (scOutCm Y (a * Y) x + a * Y * (Y - a * Y) * v) ^ 2) +
        cornerC3 x (a * Y) (Y - a * Y) * v ^ 2 /
          (scOutRho x ^ 2 * (scOutCm Y (a * Y) x + a * Y * (Y - a * Y) * v) ^ 3)) =
      formOCLaur (formOCkn3 x a v (formOCD a x v)) (formOCkn2 x a v (formOCD a x v))
        (formOCkn1 x a v (formOCD a x v)) (formOCkp0 x a v (formOCD a x v))
        (formOCkp1 x a v (formOCD a x v)) Y := by
  have hD := (formOCD_pos ha hx hv).ne'
  have h1x : x - 1 ≠ 0 := by linarith [hx.2]
  have h1x' : 1 - x ≠ 0 := by linarith [hx.2]
  have hx0 := hx.1.ne'
  have hY0 := hY.ne'
  rw [formOC_mev_eq]
  generalize formOCD a x v = D at hD ⊢
  unfold formOCLaur formOCkn3 formOCkn2 formOCkn1 formOCkp0 formOCkp1 cornerC1 cornerC2
    cornerC3 QED.TwoLoop.UnitSCReduce.cornerP2 cornerG cornerR scOutRho
  field_simp
  ring

/-- `∫₀¹ 1{Y ≤ c} b Y dY = b c²/2` for `c ∈ (0, 1)`. -/
theorem formOC_integral_lin (b : ℝ) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    IntegrableOn (fun Y => if c < Y then 0 else b * Y) (Ioo 0 1) ∧
      ∫ Y in Ioo (0 : ℝ) 1, (if c < Y then 0 else b * Y) = b * c ^ 2 / 2 := by
  have he : (fun Y : ℝ => if c < Y then 0 else b * Y) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (Ioc 0 c).indicator (fun Y => b * Y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with Y hY
    by_cases h : c < Y
    · simp only [h, ↓reduceIte]
      rw [indicator_of_notMem (show Y ∉ Ioc 0 c from fun hm => absurd hm.2 (not_le.2 h))]
    · simp only [h, ↓reduceIte]
      rw [indicator_of_mem (show Y ∈ Ioc 0 c from ⟨hY.1, not_lt.1 h⟩)]
  have hi : IntegrableOn (fun Y : ℝ => b * Y) (Ioc 0 c) :=
    (continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hsub : Ioc (0 : ℝ) c ∩ Ioo 0 1 = Ioc 0 c := by
    ext Y
    simp only [mem_inter_iff, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨h, -⟩; exact h
    · rintro ⟨h0, h1⟩; exact ⟨⟨h0, h1⟩, h0, lt_of_le_of_lt h1 hc1⟩
  refine ⟨IntegrableOn.congr_fun_ae ((hi.integrable_indicator measurableSet_Ioc).integrableOn)
    he.symm, ?_⟩
  rw [integral_congr_ae he, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, hsub, ← intervalIntegral.integral_of_le hc.le,
    intervalIntegral.integral_const_mul, integral_id]
  ring

/-- **The `Y`-integral of `Y κ`** at `y₃ = a Y`: `formOCLaurI` of the `κ`-coefficients at
`Y_c`. -/
theorem formOC_integral_kap (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    IntegrableOn (fun Y => Y * scOutCkap (cornerA0 x (a * Y) (Y - a * Y))
        (cornerA1 x (a * Y) (Y - a * Y)) (cornerA2 x (a * Y) (Y - a * Y)) (scOutCm Y (a * Y) x)
        (a * Y * (Y - a * Y)) (scOutRho x) (scOutCs Y (a * Y) x) v) (Ioo 0 1) ∧
      ∫ Y in Ioo (0 : ℝ) 1, Y * scOutCkap (cornerA0 x (a * Y) (Y - a * Y))
        (cornerA1 x (a * Y) (Y - a * Y)) (cornerA2 x (a * Y) (Y - a * Y)) (scOutCm Y (a * Y) x)
        (a * Y * (Y - a * Y)) (scOutRho x) (scOutCs Y (a * Y) x) v =
      formOCLaurI (formOCkapn3 x a v (formOCD a x v) (formOCD0 a x))
        (formOCkapn2 x a v (formOCD a x v) (formOCD0 a x))
        (formOCkapn1 x a v (formOCD a x v) (formOCD0 a x))
        (formOCkapp0 x a v (formOCD a x v) (formOCD0 a x))
        (formOCkapp1 x a v (formOCD a x v) (formOCD0 a x)) (formOCYc a x v) := by
  set L := formOCLaur (formOCkapn3 x a v (formOCD a x v) (formOCD0 a x))
    (formOCkapn2 x a v (formOCD a x v) (formOCD0 a x))
    (formOCkapn1 x a v (formOCD a x v) (formOCD0 a x))
    (formOCkapp0 x a v (formOCD a x v) (formOCD0 a x))
    (formOCkapp1 x a v (formOCD a x v) (formOCD0 a x)) with hL
  have he : EqOn (fun Y => Y * scOutCkap (cornerA0 x (a * Y) (Y - a * Y))
        (cornerA1 x (a * Y) (Y - a * Y)) (cornerA2 x (a * Y) (Y - a * Y)) (scOutCm Y (a * Y) x)
        (a * Y * (Y - a * Y)) (scOutRho x) (scOutCs Y (a * Y) x) v)
      (fun Y => if formOCYc a x v < Y then L Y else 0) (Ioo 0 1) := fun Y hY => by
    have hb := formOC_branch_iff ha hx hv hY.1
    simp only [scOutCkap]
    by_cases h : formOCYc a x v < Y
    · simp only [hb.2 h, h, ↓reduceIte, hL]
      exact formOC_kap_laur ha hx hv hY.1
    · simp only [mt hb.1 h, h, ↓reduceIte, mul_zero]
  obtain ⟨hi, hval⟩ := formOC_integral_laur (formOCkapn3 x a v (formOCD a x v) (formOCD0 a x))
    (formOCkapn2 x a v (formOCD a x v) (formOCD0 a x))
    (formOCkapn1 x a v (formOCD a x v) (formOCD0 a x))
    (formOCkapp0 x a v (formOCD a x v) (formOCD0 a x))
    (formOCkapp1 x a v (formOCD a x v) (formOCD0 a x)) (formOCYc_pos ha hx hv)
    (formOCYc_lt_one ha hx hv).le
  exact ⟨hi.congr_fun he.symm measurableSet_Ioo,
    (setIntegral_congr_fun measurableSet_Ioo he).trans hval⟩

/-- **The `Y`-integral of `Y k`** at `y₃ = a Y`: `formOCLaurI` of the `k`-coefficients at `Y_c`
plus the branch-two part `-x² Y_c²/(4 v)`. -/
theorem formOC_integral_k (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    IntegrableOn (fun Y => Y * scOutCk (cornerC0 x) (cornerC1 x (a * Y) (Y - a * Y))
        (cornerC2 x (a * Y) (Y - a * Y)) (cornerC3 x (a * Y) (Y - a * Y)) (scOutCm Y (a * Y) x)
        (a * Y * (Y - a * Y)) (scOutRho x) (scOutCs Y (a * Y) x) v) (Ioo 0 1) ∧
      ∫ Y in Ioo (0 : ℝ) 1, Y * scOutCk (cornerC0 x) (cornerC1 x (a * Y) (Y - a * Y))
        (cornerC2 x (a * Y) (Y - a * Y)) (cornerC3 x (a * Y) (Y - a * Y)) (scOutCm Y (a * Y) x)
        (a * Y * (Y - a * Y)) (scOutRho x) (scOutCs Y (a * Y) x) v =
      formOCLaurI (formOCkn3 x a v (formOCD a x v)) (formOCkn2 x a v (formOCD a x v))
        (formOCkn1 x a v (formOCD a x v)) (formOCkp0 x a v (formOCD a x v))
        (formOCkp1 x a v (formOCD a x v)) (formOCYc a x v) -
        x ^ 2 * formOCYc a x v ^ 2 / (4 * v) := by
  set L := formOCLaur (formOCkn3 x a v (formOCD a x v)) (formOCkn2 x a v (formOCD a x v))
    (formOCkn1 x a v (formOCD a x v)) (formOCkp0 x a v (formOCD a x v))
    (formOCkp1 x a v (formOCD a x v)) with hL
  set c := formOCYc a x v with hc
  have h1x : 1 - x ≠ 0 := by linarith [hx.2]
  have he : EqOn (fun Y => Y * scOutCk (cornerC0 x) (cornerC1 x (a * Y) (Y - a * Y))
        (cornerC2 x (a * Y) (Y - a * Y)) (cornerC3 x (a * Y) (Y - a * Y)) (scOutCm Y (a * Y) x)
        (a * Y * (Y - a * Y)) (scOutRho x) (scOutCs Y (a * Y) x) v)
      (fun Y => (if c < Y then L Y else 0) + (if c < Y then 0 else -(x ^ 2 / (2 * v)) * Y))
      (Ioo 0 1) := fun Y hY => by
    have hb := formOC_branch_iff ha hx hv hY.1
    simp only [scOutCk]
    by_cases h : c < Y
    · simp only [hb.2 h, h, ↓reduceIte, hL, add_zero]
      exact formOC_k_laur ha hx hv hY.1
    · simp only [mt hb.1 h, h, ↓reduceIte, zero_add]
      unfold cornerC0 scOutRho
      field_simp
  have hc0 := formOCYc_pos ha hx hv
  have hc1 := formOCYc_lt_one ha hx hv
  obtain ⟨hi, hval⟩ := formOC_integral_laur (formOCkn3 x a v (formOCD a x v))
    (formOCkn2 x a v (formOCD a x v)) (formOCkn1 x a v (formOCD a x v))
    (formOCkp0 x a v (formOCD a x v)) (formOCkp1 x a v (formOCD a x v)) hc0 hc1.le
  obtain ⟨hi2, hval2⟩ := formOC_integral_lin (-(x ^ 2 / (2 * v))) hc0 hc1
  refine ⟨(hi.add hi2).congr_fun he.symm measurableSet_Ioo, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo he, integral_add hi hi2, hval, hval2]
  ring

end

end QED.ChainProof.SetCK

end
