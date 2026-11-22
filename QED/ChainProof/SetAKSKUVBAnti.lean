/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUVBCov
public import QED.ChainProof.SetAKSKUElem

/-!
# Set (a), stage D: the slope antiderivative of the `VB` integrand

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral of the `VB` class). At a fixed
node the `VB` integrand `ksDYB` depends on the photon mass² `u` only through the slope
`b = b₀ + u/(1 - x₂)`, as a combination `ksUYBg` of the moments `ksDJ1`, `ksDJ2`. Its
antiderivative in `b` is `ksUPsiB`:

  `Ψ(b) = -τ⁻¹ ∑ᵢ Gᵢ J1ᵢ(b) + (2τ)⁻¹ P log(A + bY) + c K(bY/A)`,

`Gᵢ = Eᵢ - Hᵢ A/(2(i + 1))`, `P = ∑ᵢ Hᵢ Y^{i+1}/(i + 1)`, from `∂_b J1ₚ = -J2ₚ₊₁` and
`(p + 1) J1ₚ₊₁ + A J2ₚ₊₁ = Y^{p+2}/(A + bY)`.

Main results:

* `ksU_hasDerivAt_J1`, `ksU_J1_J2_rel`;
* **`ksU_hasDerivAt_ksUPsiB`**: `Ψ' = ksUYBg`;
* **`ksU_integral_ksUYBg`**: `∫₀^Λ ρ⁻¹ ksUYBg(b₀ + u/ρ) du = Ψ(b₀ + Λ/ρ) - Ψ(b₀)`.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace QED.ChainProof.SetAKS

/-- The `VB` integrand as a function of the slope `b`, with coefficient vectors `E`, `H`. -/
noncomputable def ksUYBg (A b Y τ c : ℝ) (E H : Fin 3 → ℝ) : ℝ :=
  τ⁻¹ * (E 0 * ksDJ2 A b Y 1 + E 1 * ksDJ2 A b Y 2 + E 2 * ksDJ2 A b Y 3) +
    (2 * τ)⁻¹ * (H 0 * ksDJ1 A b Y 1 + H 1 * ksDJ1 A b Y 2 + H 2 * ksDJ1 A b Y 3) +
    c * ksDJ1 A b Y 0

theorem ksU_ksDYB_eq (M u : ℝ) (x : Fin 3 → ℝ) (s w : ℝ) :
    ksDYB M u x s w = ksUYBg (ksDA M s w) (ksDbB M u x s) (ksDYmax (x 1 / (1 - x 2)) w)
      (x 2 * (1 - x 2)) (16 * w * (w - 1)) (ksDEc M x w) (ksDHc x w) := rfl

/-- The coefficients `Gᵢ = Eᵢ - Hᵢ A/(2(i + 1))`. -/
noncomputable def ksUGc (A : ℝ) (E H : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  E i - H i * A / (2 * ((i : ℕ) + 1 : ℝ))

/-- `P = ∑ᵢ Hᵢ Y^{i+1}/(i + 1)`. -/
noncomputable def ksUPY (Y : ℝ) (H : Fin 3 → ℝ) : ℝ := H 0 * Y + H 1 * Y ^ 2 / 2 + H 2 * Y ^ 3 / 3

/-- **The slope antiderivative of the `VB` integrand.** -/
noncomputable def ksUPsiB (A Y τ c : ℝ) (E H : Fin 3 → ℝ) (b : ℝ) : ℝ :=
  -(τ⁻¹ * (ksUGc A E H 0 * ksDJ1 A b Y 0 + ksUGc A E H 1 * ksDJ1 A b Y 1 +
      ksUGc A E H 2 * ksDJ1 A b Y 2)) +
    (2 * τ)⁻¹ * ksUPY Y H * Real.log (A + b * Y) + c * ksUK (b * Y / A)

variable {A b Y : ℝ}

theorem ksU_hasDerivAt_J1 (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y) (p : ℕ) :
    HasDerivAt (fun b => ksDJ1 A b Y p) (-ksDJ2 A b Y (p + 1)) b := by
  have hP : 0 < A + b * Y := by positivity
  have hb' : HasDerivAt (fun b : ℝ => b) 1 b := hasDerivAt_id' b
  induction p with
  | zero =>
    have hlin : HasDerivAt (fun b : ℝ => A + b * Y) Y b := by
      simpa using ((hasDerivAt_id b).mul_const Y).const_add A
    have hL : HasDerivAt (fun b : ℝ => Real.log ((A + b * Y) / A)) (Y / (A + b * Y)) b := by
      have h := (hlin.div_const A).log (div_pos hP hA).ne'
      refine h.congr_deriv ?_
      field_simp
    refine (hL.div hb' hb.ne').congr_deriv ?_
    simp only [ksDJ2, ksDJ1]
    field_simp
    ring
  | succ p ih =>
    have h1 : HasDerivAt (fun b : ℝ => Y ^ (p + 1) / (((p : ℝ) + 1) * b))
        (-(Y ^ (p + 1) * ((p : ℝ) + 1)) / (((p : ℝ) + 1) * b) ^ 2) b := by
      have h := (hasDerivAt_const b (Y ^ (p + 1))).div (hb'.const_mul ((p : ℝ) + 1))
        (by positivity)
      refine h.congr_deriv ?_
      ring
    have h2 := ((hasDerivAt_const b A).div hb' hb.ne').mul ih
    refine (h1.sub h2).congr_deriv ?_
    simp only [Pi.div_apply, ksDJ2, ksDJ1]
    field_simp
    ring

theorem ksU_J1_J2_rel (hA : A ≠ 0) (hb : b ≠ 0) (hP : A + b * Y ≠ 0) (p : ℕ) :
    ((p : ℝ) + 1) * ksDJ1 A b Y (p + 1) + A * ksDJ2 A b Y (p + 1) = Y ^ (p + 2) / (A + b * Y) := by
  induction p with
  | zero =>
    simp only [ksDJ1, ksDJ2]
    field_simp
    ring
  | succ p ih =>
    have e1 : ksDJ1 A b Y (p + 1 + 1) =
        Y ^ (p + 1 + 1) / ((((p + 1 : ℕ) : ℝ) + 1) * b) - A / b * ksDJ1 A b Y (p + 1) := rfl
    have e2 : ksDJ2 A b Y (p + 1 + 1) = ksDJ1 A b Y (p + 1) / b - A / b * ksDJ2 A b Y (p + 1) :=
      rfl
    have key : (((p + 1 : ℕ) : ℝ) + 1) * ksDJ1 A b Y (p + 1 + 1) + A * ksDJ2 A b Y (p + 1 + 1) =
        Y ^ (p + 2) / b - A / b * (((p : ℝ) + 1) * ksDJ1 A b Y (p + 1) +
          A * ksDJ2 A b Y (p + 1)) := by
      rw [e1, e2]
      push_cast
      field_simp
      ring
    rw [key, ih]
    field_simp
    ring

theorem ksU_ksUKer_mul (hA : 0 < A) (hb : 0 < b) (hY : 0 < Y) :
    ksUKer (b * Y / A) * (Y / A) = ksDJ1 A b Y 0 := by
  have h1 : 1 + b * Y / A = (A + b * Y) / A := by field_simp
  simp only [ksUKer, ksDJ1, h1]
  field_simp

/-- **The slope derivative of the antiderivative** is the `VB` integrand. -/
theorem ksU_hasDerivAt_ksUPsiB (τ c : ℝ) (E H : Fin 3 → ℝ) (hA : 0 < A) (hb : 0 < b)
    (hY : 0 < Y) :
    HasDerivAt (fun b => ksUPsiB A Y τ c E H b) (ksUYBg A b Y τ c E H) b := by
  have hP : 0 < A + b * Y := by positivity
  have hlin : HasDerivAt (fun b : ℝ => A + b * Y) Y b := by
    simpa using ((hasDerivAt_id b).mul_const Y).const_add A
  have hlog : HasDerivAt (fun b : ℝ => Real.log (A + b * Y)) (Y / (A + b * Y)) b :=
    hlin.log hP.ne'
  have hK : HasDerivAt (fun b : ℝ => ksUK (b * Y / A)) (ksUKer (b * Y / A) * (Y / A)) b := by
    have h := ((hasDerivAt_id b).mul_const Y).div_const A
    simp only [id, one_mul] at h
    exact (ksU_hasDerivAt_ksUK (by positivity)).comp b h
  have j0 := ksU_hasDerivAt_J1 hA hb hY.le 0
  have j1 := ksU_hasDerivAt_J1 hA hb hY.le 1
  have j2 := ksU_hasDerivAt_J1 hA hb hY.le 2
  have h := (((((j0.const_mul (ksUGc A E H 0)).add (j1.const_mul (ksUGc A E H 1))).add
    (j2.const_mul (ksUGc A E H 2))).const_mul τ⁻¹).neg.add
    (hlog.const_mul ((2 * τ)⁻¹ * ksUPY Y H))).add (hK.const_mul c)
  refine h.congr_deriv ?_
  have r0 := ksU_J1_J2_rel hA.ne' hb.ne' hP.ne' 0
  have r1 := ksU_J1_J2_rel hA.ne' hb.ne' hP.ne' 1
  have r2 := ksU_J1_J2_rel hA.ne' hb.ne' hP.ne' 2
  rw [ksU_ksUKer_mul hA hb hY]
  simp only [ksUYBg, ksUGc, ksUPY]
  norm_num at r0 r1 r2 ⊢
  have e1 : ksDJ1 A b Y 1 = Y ^ 2 / (A + b * Y) - A * ksDJ2 A b Y 1 := by linarith
  have e2 : ksDJ1 A b Y 2 = (Y ^ 3 / (A + b * Y) - A * ksDJ2 A b Y 2) / 2 := by linarith
  have e3 : ksDJ1 A b Y 3 = (Y ^ 4 / (A + b * Y) - A * ksDJ2 A b Y 3) / 3 := by linarith
  rw [e1, e2, e3]
  field_simp
  ring

theorem ksU_continuousAt_J (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y) (p : ℕ) :
    ContinuousAt (fun b => ksDJ1 A b Y p) b ∧ ContinuousAt (fun b => ksDJ2 A b Y p) b := by
  have hP : 0 < A + b * Y := by positivity
  refine ⟨(ksU_hasDerivAt_J1 hA hb hY p).continuousAt, ?_⟩
  induction p with
  | zero =>
    simp only [ksDJ2]
    exact continuousAt_const.div (continuousAt_const.mul (continuousAt_const.add
      (continuousAt_id.mul continuousAt_const))) (mul_pos hA hP).ne'
  | succ p ih =>
    simp only [ksDJ2]
    exact ((ksU_hasDerivAt_J1 hA hb hY p).continuousAt.div continuousAt_id hb.ne').sub
      ((continuousAt_const.div continuousAt_id hb.ne').mul ih)

theorem ksU_continuousAt_ksUYBg (τ c : ℝ) (E H : Fin 3 → ℝ) (hA : 0 < A) (hb : 0 < b)
    (hY : 0 ≤ Y) : ContinuousAt (fun b => ksUYBg A b Y τ c E H) b := by
  have J := ksU_continuousAt_J hA hb hY
  simp only [ksUYBg]
  exact ((continuousAt_const.mul ((((J 1).2.const_mul _).add ((J 2).2.const_mul _)).add
    ((J 3).2.const_mul _))).add (continuousAt_const.mul ((((J 1).1.const_mul _).add
    ((J 2).1.const_mul _)).add ((J 3).1.const_mul _)))).add ((J 0).1.const_mul _)

/-- **The photon-mass integral of the `VB` integrand at a fixed node** (`b = b₀ + u/ρ`). -/
theorem ksU_integral_ksUYBg {b₀ ρ Λ : ℝ} (τ c : ℝ) (E H : Fin 3 → ℝ) (hA : 0 < A)
    (hb₀ : 0 < b₀) (hρ : 0 < ρ) (hY : 0 < Y) (hΛ : 0 ≤ Λ) :
    ∫ u in (0 : ℝ)..Λ, ρ⁻¹ * ksUYBg A (b₀ + u / ρ) Y τ c E H =
      ksUPsiB A Y τ c E H (b₀ + Λ / ρ) - ksUPsiB A Y τ c E H b₀ := by
  have hsub : ∫ u in (0 : ℝ)..Λ, ρ⁻¹ * ksUYBg A (b₀ + u / ρ) Y τ c E H =
      ρ⁻¹ * (ρ • ∫ b in 0 / ρ + b₀..Λ / ρ + b₀, ksUYBg A b Y τ c E H) := by
    rw [intervalIntegral.integral_const_mul, ← intervalIntegral.integral_comp_div_add
      (f := fun b => ksUYBg A b Y τ c E H) hρ.ne' b₀]
    simp only [add_comm b₀]
  have hle : b₀ ≤ Λ / ρ + b₀ := by have := div_nonneg hΛ hρ.le; linarith
  have hpos : ∀ b ∈ uIcc b₀ (Λ / ρ + b₀), 0 < b := fun b hb => by
    rw [uIcc_of_le hle] at hb
    exact hb₀.trans_le hb.1
  rw [hsub, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hρ.ne', one_mul, zero_div, zero_add,
    integral_eq_sub_of_hasDerivAt (fun b hb => ksU_hasDerivAt_ksUPsiB τ c E H hA (hpos b hb) hY)
      (ContinuousOn.intervalIntegrable fun b hb =>
        (ksU_continuousAt_ksUYBg τ c E H hA (hpos b hb) hY.le).continuousWithinAt),
    add_comm (Λ / ρ)]

end QED.ChainProof.SetAKS

end
