/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRayA
public import QED.GradedProof.RPi4FaceIdRayAFlow
public import QED.GradedProof.RPi4MajRayPv
public import QED.GradedProof.RPi4LightBd
public import QED.GradedProof.WI2Merge

/-!
# (R-Π₄) step L10, T2.UV: (A) with a power loss for a photon-mass density, given a majorant

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (input (A) of
`QED.GradedProof.RPi4.faceIdRay_of_size_rate`, in the form `QED.GradedProof.RPi4.FaceIdRayAPow`).
Let `G(u, k) = pairDens (N k) α (c • k) M γ u` be the photon-mass density of a merged piece
(`m + 1` lines, photon line `γ`), and along the ray `k = r v`, `v = majRayVec 1`, `r = √s`, let
the numerator be `N(r v)(ℓ) = ∑_{t<3} r^{2t} Q_t(ℓ/r)`. With the coefficients
`T₁ = U⁻² Q(X)`, `T₂ = U⁻² H(X)·G`, `T₃ = U⁻² R·Π(G)` at `r = 1` (`faceIdRayAPOne`,
`faceIdRayAPTwo`, `faceIdRayAPThree`), the integrand of `u G` is a sum of terms
`u z_γ s^{t-j+1} T_j(Q_t) / W^{m-1-j}`, `W = V₀ + s B`, `V₀ = ∑ zᵢ Mᵢ² + z_γ u ≥ min(m₀², 1)`
when the non-photon masses are `≥ m₀ > 0` and `u ≥ 1` (`faceIdRayAP_le_V₀`). Since
`u z_γ ≤ W`, `u z_γ / W ≤ (u z_γ)^a W^{-a}`, and `QED.GradedProof.RPi4.faceIdRayA_gain_le` turns
every term into `c₀^{-m} s^{1-δ} B^{-δ} (u z_γ)^a` times `T_j(Q_t)` (`c₀ = min(m₀², 1)`), except
the top monomial `(t, j) = (2, 1)`, which
costs `T₁(Q₂)/B` (`faceIdRayAP_gain_zero`, `faceIdRayAP_gain_one`, `faceIdRayAP_sum_le`). So `u G`
is at most `C s^{1-δ} u^a ∫ F` as soon as `z_γ^a B^{-δ} S ≤ F` with `F` integrable, `S` the sum of
the absolute coefficients with `T₁(Q₂)` divided by `B` (`faceIdRayAPSum`).

* `faceIdRayAPOne`, `faceIdRayAPTwo`, `faceIdRayAPThree`, `faceIdRayAP_paramAtV_eq`,
  `faceIdRayAP_one_dilateQ`, `faceIdRayAP_two_dilateQ`, `faceIdRayAP_three_dilateQ`,
  `faceIdRayAP_norm_paramAtV_dilate_le`;
* `faceIdRayAP_gain_zero`, `faceIdRayAP_gain_one`, `faceIdRayAP_sum_le`, `faceIdRayAPSum`;
* **`faceIdRayAP_pow_pairDens`**: the majorant gives `FaceIdRayAPow` of the density.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.MassScaling
open QED.TwoLoop.LimitCovariance
open QED.GradedProof.WI2 (ehat ehat_qsum)
open QED.Integration.Feynman (simplexSet simplexPoint)

variable {m : ℕ}

/-! ### The coefficients of the merged integrand -/

section Coeff

variable (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)

/-- The coefficient `U⁻² Q(X)`, `X = -S(z)`, at the Feynman point `z = simplexPoint x`. -/
noncomputable def faceIdRayAPOne (x : Fin m → ℝ) : ℂ :=
  ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
    Q.evalC (loopComp (-loopShift α p (simplexPoint x)))

/-- The coefficient `U⁻² H(X)·G`. -/
noncomputable def faceIdRayAPTwo (x : Fin m → ℝ) : ℂ :=
  ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
    Q.contractTwo (symanzikMatrix α (simplexPoint x)) (loopComp (-loopShift α p (simplexPoint x)))

/-- The coefficient `U⁻² R·Π(G)`. -/
noncomputable def faceIdRayAPThree (x : Fin m → ℝ) : ℂ :=
  ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
    Q.contractFour (symanzikMatrix α (simplexPoint x))

theorem faceIdRayAP_paramAtV_eq (x : Fin m → ℝ) (v : ℝ) :
    paramAtV (m + 1) Q α p (simplexPoint x) v =
      ((m + 1 - 4).factorial : ℂ) * (((v : ℂ)) ^ (m + 1 - 3))⁻¹ * faceIdRayAPOne Q α p x +
        ((m + 1 - 5).factorial : ℂ) / 2 * (((v : ℂ)) ^ (m + 1 - 4))⁻¹ *
          faceIdRayAPTwo Q α p x +
        ((m + 1 - 6).factorial : ℂ) / 4 * (((v : ℂ)) ^ (m + 1 - 5))⁻¹ *
          faceIdRayAPThree Q α x := by
  simp only [paramAtV, ehat, faceIdRayAPOne, faceIdRayAPTwo, faceIdRayAPThree]
  ring

variable {r : ℝ} (hr : r ≠ 0)
include hr

theorem faceIdRayAP_one_dilateQ (x : Fin m → ℝ) :
    faceIdRayAPOne (dilateQ 1 ((r⁻¹ : ℝ) : ℂ) Q) α (r • p) x = faceIdRayAPOne Q α p x := by
  simp only [faceIdRayAPOne, evalC_dilateQ, maj_loopComp_loopShift hr α p x, one_mul]

theorem faceIdRayAP_two_dilateQ (x : Fin m → ℝ) :
    faceIdRayAPTwo (dilateQ 1 ((r⁻¹ : ℝ) : ℂ) Q) α (r • p) x =
      ((r⁻¹ : ℝ) : ℂ) ^ 2 * faceIdRayAPTwo Q α p x := by
  simp only [faceIdRayAPTwo, contractTwo_dilateQ, maj_loopComp_loopShift hr α p x]
  ring

omit hr in
theorem faceIdRayAP_three_dilateQ (x : Fin m → ℝ) :
    faceIdRayAPThree (dilateQ 1 ((r⁻¹ : ℝ) : ℂ) Q) α x =
      ((r⁻¹ : ℝ) : ℂ) ^ 4 * faceIdRayAPThree Q α x := by
  simp only [faceIdRayAPThree, contractFour_dilateQ]
  ring

end Coeff

/-- **One dilated quartic at scaled momenta**: the merged integrand of `ℓ ↦ Q(ℓ/r)` at the
momenta `r p` is at most `c₁ ‖T₁‖/v^{m-2} + (c₂ ‖T₂‖/v^{m-3} + c₃ ‖T₃‖/v^{m-4})/r²`, `r ≥ 1`. -/
theorem faceIdRayAP_norm_paramAtV_dilate_le (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (x : Fin m → ℝ) {r v : ℝ} (hr : 1 ≤ r) (hv : 0 < v) :
    ‖paramAtV (m + 1) (dilateQ 1 ((r⁻¹ : ℝ) : ℂ) Q) α (r • p) (simplexPoint x) v‖ ≤
      ((m + 1 - 4).factorial : ℝ) * ‖faceIdRayAPOne Q α p x‖ / v ^ (m + 1 - 3) +
        (((m + 1 - 5).factorial : ℝ) / 2 * ‖faceIdRayAPTwo Q α p x‖ / v ^ (m + 1 - 4) +
          ((m + 1 - 6).factorial : ℝ) / 4 * ‖faceIdRayAPThree Q α x‖ / v ^ (m + 1 - 5)) /
          r ^ 2 := by
  have hr0 : 0 < r := by linarith
  rw [faceIdRayAP_paramAtV_eq, faceIdRayAP_one_dilateQ _ _ _ hr0.ne',
    faceIdRayAP_two_dilateQ _ _ _ hr0.ne', faceIdRayAP_three_dilateQ]
  refine (norm_add₃_le).trans ?_
  have hn : ∀ n : ℕ, ‖((((v : ℝ) : ℂ)) ^ n)⁻¹‖ = 1 / v ^ n := fun n => by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv, one_div]
  have hρ : ‖(((r⁻¹ : ℝ) : ℂ))‖ = r⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0)]
  have hf : ∀ n : ℕ, ‖((n.factorial : ℂ))‖ = (n.factorial : ℝ) := fun n => by
    rw [Complex.norm_natCast]
  simp only [norm_mul, norm_div, norm_pow, hn, hρ, hf, Complex.norm_ofNat]
  have hρ1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
  have hρ0 : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
  have h4 : r⁻¹ ^ 4 ≤ r⁻¹ ^ 2 := pow_le_pow_of_le_one hρ0 hρ1 (by norm_num)
  have e2 : r⁻¹ ^ 2 = 1 / r ^ 2 := by rw [inv_pow, one_div]
  have hA := norm_nonneg (faceIdRayAPTwo Q α p x)
  have hB := norm_nonneg (faceIdRayAPThree Q α x)
  have hV5 : 0 ≤ 1 / v ^ (m + 1 - 5) := by positivity
  have hV4 : 0 ≤ 1 / v ^ (m + 1 - 4) := by positivity
  have hc : 0 ≤ ((m + 1 - 6).factorial : ℝ) / 4 := by positivity
  calc ((m + 1 - 4).factorial : ℝ) * (1 / v ^ (m + 1 - 3)) * ‖faceIdRayAPOne Q α p x‖ +
        ((m + 1 - 5).factorial : ℝ) / 2 * (1 / v ^ (m + 1 - 4)) *
          (r⁻¹ ^ 2 * ‖faceIdRayAPTwo Q α p x‖) +
        ((m + 1 - 6).factorial : ℝ) / 4 * (1 / v ^ (m + 1 - 5)) *
          (r⁻¹ ^ 4 * ‖faceIdRayAPThree Q α x‖)
      ≤ ((m + 1 - 4).factorial : ℝ) * (1 / v ^ (m + 1 - 3)) * ‖faceIdRayAPOne Q α p x‖ +
        ((m + 1 - 5).factorial : ℝ) / 2 * (1 / v ^ (m + 1 - 4)) *
          (r⁻¹ ^ 2 * ‖faceIdRayAPTwo Q α p x‖) +
        ((m + 1 - 6).factorial : ℝ) / 4 * (1 / v ^ (m + 1 - 5)) *
          (r⁻¹ ^ 2 * ‖faceIdRayAPThree Q α x‖) := by gcongr
    _ = _ := by rw [e2]; ring

/-! ### The gain with the photon weight -/

/-- `x ≤ x^a` on `[0, 1]` for `0 < a ≤ 1`. -/
theorem faceIdRayAP_le_rpow {x a : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (ha : 0 < a) (ha1 : a ≤ 1) :
    x ≤ x ^ a := by
  calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
    _ ≤ x ^ a := Real.rpow_le_rpow_of_exponent_ge' hx hx1 ha.le ha1

/-- **The gain of a term with the photon weight**: for `W ≥ V₀ + sB`, `V₀ ≥ c₀`, `0 < c₀ ≤ 1`,
`0 ≤ u z ≤ W`, `u z · s (sB)^e / Wⁿ ≤ c₀^{-K} s^{1-δ} B^{-δ} (u z)^a` when `e + δ ≤ n - 1`,
`n ≤ K`. -/
theorem faceIdRayAP_gain {s w V₀ B W e δ a c₀ K : ℝ} {n : ℕ} (hs : 0 < s) (hc₀ : 0 < c₀)
    (hc₀1 : c₀ ≤ 1) (hV₀ : c₀ ≤ V₀) (hB : 0 < B) (hW : V₀ + s * B ≤ W) (hw : 0 ≤ w)
    (hwW : w ≤ W) (he : 0 ≤ e) (hδ : 0 ≤ δ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hn : e + δ ≤ (n : ℝ) - 1) (hK : (n : ℝ) ≤ K) :
    w * (s * (s * B) ^ e / W ^ n) ≤ c₀ ^ (-K) * (s ^ (1 - δ) * B ^ (-δ) * w ^ a) := by
  have hV0 : 0 < V₀ := hc₀.trans_le hV₀
  have hW0 : 0 < W := by nlinarith [mul_pos hs hB]
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hx := faceIdRayAP_le_rpow (div_nonneg hw hW0.le) ((div_le_one hW0).mpr hwW) ha ha1
  have hg := faceIdRayA_gain_le hV0 hB hs hW he hδ
    (by linarith : e + δ ≤ ((n : ℝ) - 1) + a)
  have hV1 : V₀ ^ (e + δ - ((n - 1 : ℝ) + a)) ≤ c₀ ^ (-K) :=
    (Real.rpow_le_rpow_of_nonpos hc₀ hV₀ (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_ge hc₀ hc₀1 (by linarith))
  have hWn : W ^ n = W * W ^ ((n : ℝ) - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_one_add' hW0.le (by linarith)]
    norm_num
  have hWr : W ^ ((n - 1 : ℝ) + a) = W ^ ((n : ℝ) - 1) * W ^ a := Real.rpow_add hW0 _ _
  have hwa : (w / W) ^ a = w ^ a / W ^ a := Real.div_rpow hw hW0.le a
  have hK0 : 0 ≤ s * (s * B) ^ e := mul_nonneg hs.le (Real.rpow_nonneg (by positivity) _)
  have hWa : 0 < W ^ a := Real.rpow_pos_of_pos hW0 a
  have hWn1 : 0 < W ^ ((n : ℝ) - 1) := Real.rpow_pos_of_pos hW0 _
  calc w * (s * (s * B) ^ e / W ^ n)
      = w / W * (s * (s * B) ^ e / W ^ ((n : ℝ) - 1)) := by
        rw [hWn]; field_simp
    _ ≤ (w / W) ^ a * (s * (s * B) ^ e / W ^ ((n : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_right hx (by positivity)
    _ = w ^ a * (s * (s * B) ^ e / W ^ ((n - 1 : ℝ) + a)) := by
        rw [hwa, hWr]; field_simp
    _ ≤ w ^ a * (s ^ (1 - δ) * B ^ (-δ) * V₀ ^ (e + δ - ((n - 1 : ℝ) + a))) :=
        mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg hw _)
    _ ≤ w ^ a * (s ^ (1 - δ) * B ^ (-δ) * c₀ ^ (-K)) := by
        gcongr
    _ = c₀ ^ (-K) * (s ^ (1 - δ) * B ^ (-δ) * w ^ a) := by ring

/-- The gain for `e = 0`: `u z · s / Wⁿ ≤ c₀^{-K} s^{1-δ} B^{-δ} (u z)^a` when
`δ ≤ n - 1`. -/
theorem faceIdRayAP_gain_zero {s w V₀ B W δ a c₀ K : ℝ} {n : ℕ} (hs : 0 < s) (hc₀ : 0 < c₀)
    (hc₀1 : c₀ ≤ 1) (hV₀ : c₀ ≤ V₀) (hB : 0 < B) (hW : V₀ + s * B ≤ W) (hw : 0 ≤ w)
    (hwW : w ≤ W) (hδ : 0 ≤ δ) (ha : 0 < a) (ha1 : a ≤ 1) (hn : δ ≤ (n : ℝ) - 1)
    (hK : (n : ℝ) ≤ K) :
    s * (w / W ^ n) ≤ c₀ ^ (-K) * (s ^ (1 - δ) * B ^ (-δ) * w ^ a) := by
  have h := faceIdRayAP_gain (e := 0) hs hc₀ hc₀1 hV₀ hB hW hw hwW le_rfl hδ ha ha1
    (by linarith) hK
  rw [Real.rpow_zero, mul_one] at h
  calc s * (w / W ^ n) = w * (s / W ^ n) := by ring
    _ ≤ _ := h

/-- The gain for `e = 1`: `u z · s² B / Wⁿ ≤ c₀^{-K} s^{1-δ} B^{-δ} (u z)^a` when
`1 + δ ≤ n - 1`. -/
theorem faceIdRayAP_gain_one {s w V₀ B W δ a c₀ K : ℝ} {n : ℕ} (hs : 0 < s) (hc₀ : 0 < c₀)
    (hc₀1 : c₀ ≤ 1) (hV₀ : c₀ ≤ V₀) (hB : 0 < B) (hW : V₀ + s * B ≤ W) (hw : 0 ≤ w)
    (hwW : w ≤ W) (hδ : 0 ≤ δ) (ha : 0 < a) (ha1 : a ≤ 1) (hn : 1 + δ ≤ (n : ℝ) - 1)
    (hK : (n : ℝ) ≤ K) :
    s ^ 2 * B * (w / W ^ n) ≤ c₀ ^ (-K) * (s ^ (1 - δ) * B ^ (-δ) * w ^ a) := by
  have h := faceIdRayAP_gain (e := 1) hs hc₀ hc₀1 hV₀ hB hW hw hwW zero_le_one hδ ha ha1 hn hK
  rw [Real.rpow_one] at h
  calc s ^ 2 * B * (w / W ^ n) = w * (s * (s * B) / W ^ n) := by ring
    _ ≤ _ := h

/-- **The sum of the nine terms**: with `qₙ = u z / Wⁿ`, the bound of the three dilated
quartics `∑_t s^t (c₁ oₜ q₁ + (c₂ wₜ q₂ + c₃ hₜ q₃)/s)` is at most
`(c₁ + c₂ + c₃) Γ (o₀ + o₁ + o₂/B + ∑ₜ (wₜ + hₜ))` once `s q₁, s² B q₁, s q₂ ≤ Γ` and
`hₜ s q₃ ≤ hₜ Γ`. -/
theorem faceIdRayAP_sum_le {s B q₁ q₂ q₃ Γ c₁ c₂ c₃ : ℝ} {o w h : Fin 3 → ℝ} (hs : 1 ≤ s)
    (hB : 0 < B) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hq₃ : 0 ≤ q₃) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hc₃ : 0 ≤ c₃) (ho : ∀ t, 0 ≤ o t) (hw : ∀ t, 0 ≤ w t) (hh : ∀ t, 0 ≤ h t)
    (h₁ : s * q₁ ≤ Γ) (h₁' : s ^ 2 * B * q₁ ≤ Γ) (h₂ : s * q₂ ≤ Γ)
    (h₃ : ∀ t, h t * (s * q₃) ≤ h t * Γ) :
    c₁ * o 0 * q₁ + (c₂ * w 0 * q₂ + c₃ * h 0 * q₃) / s +
        s * (c₁ * o 1 * q₁ + (c₂ * w 1 * q₂ + c₃ * h 1 * q₃) / s) +
        s ^ 2 * (c₁ * o 2 * q₁ + (c₂ * w 2 * q₂ + c₃ * h 2 * q₃) / s) ≤
      (c₁ + c₂ + c₃) * Γ * (o 0 + o 1 + o 2 / B + ∑ t, (w t + h t)) := by
  have hs0 : 0 < s := by linarith
  have hΓ : 0 ≤ Γ := (mul_nonneg hs0.le hq₂).trans h₂
  -- each `q / s ≤ q ≤ s q`
  have k1 : ∀ q : ℝ, 0 ≤ q → q / s ≤ s * q := fun q hq => by
    have : q / s ≤ q := div_le_self hq hs
    nlinarith
  have k2 : ∀ q : ℝ, 0 ≤ q → q ≤ s * q := fun q hq => by nlinarith
  -- the photon-free parts
  have A0 : c₁ * o 0 * q₁ ≤ c₁ * o 0 * Γ :=
    mul_le_mul_of_nonneg_left ((k2 q₁ hq₁).trans h₁) (mul_nonneg hc₁ (ho 0))
  have A1 : s * (c₁ * o 1 * q₁) ≤ c₁ * o 1 * Γ := by
    have := mul_le_mul_of_nonneg_left h₁ (mul_nonneg hc₁ (ho 1))
    linarith [mul_comm s (c₁ * o 1 * q₁), show c₁ * o 1 * (s * q₁) = s * (c₁ * o 1 * q₁) by ring]
  have A2 : s ^ 2 * (c₁ * o 2 * q₁) ≤ c₁ * (o 2 / B) * Γ := by
    have := mul_le_mul_of_nonneg_left h₁' (mul_nonneg hc₁ (div_nonneg (ho 2) hB.le))
    have e : c₁ * (o 2 / B) * (s ^ 2 * B * q₁) = s ^ 2 * (c₁ * o 2 * q₁) := by
      field_simp
    linarith
  -- the terms with `q₂`, `q₃`
  have W2 : ∀ t, c₂ * w t * (s * q₂) ≤ c₂ * w t * Γ := fun t =>
    mul_le_mul_of_nonneg_left h₂ (mul_nonneg hc₂ (hw t))
  have W3 : ∀ t, c₃ * h t * (s * q₃) ≤ c₃ * h t * Γ := fun t => by
    have := mul_le_mul_of_nonneg_left (h₃ t) hc₃
    calc c₃ * h t * (s * q₃) = c₃ * (h t * (s * q₃)) := by ring
      _ ≤ c₃ * (h t * Γ) := this
      _ = c₃ * h t * Γ := by ring
  have B0 : (c₂ * w 0 * q₂ + c₃ * h 0 * q₃) / s ≤ c₂ * w 0 * Γ + c₃ * h 0 * Γ := by
    have e := k1 (c₂ * w 0 * q₂ + c₃ * h 0 * q₃) (by
      have := mul_nonneg (mul_nonneg hc₂ (hw 0)) hq₂
      have := mul_nonneg (mul_nonneg hc₃ (hh 0)) hq₃
      linarith)
    have := W2 0
    have := W3 0
    nlinarith
  have B1 : s * ((c₂ * w 1 * q₂ + c₃ * h 1 * q₃) / s) ≤ c₂ * w 1 * Γ + c₃ * h 1 * Γ := by
    rw [mul_div_cancel₀ _ hs0.ne']
    have e1 := (k2 q₂ hq₂)
    have e2 := (k2 q₃ hq₃)
    have := W2 1
    have := W3 1
    have := mul_le_mul_of_nonneg_left e1 (mul_nonneg hc₂ (hw 1))
    have := mul_le_mul_of_nonneg_left e2 (mul_nonneg hc₃ (hh 1))
    nlinarith
  have B2 : s ^ 2 * ((c₂ * w 2 * q₂ + c₃ * h 2 * q₃) / s) ≤ c₂ * w 2 * Γ + c₃ * h 2 * Γ := by
    have e : s ^ 2 * ((c₂ * w 2 * q₂ + c₃ * h 2 * q₃) / s) =
        c₂ * w 2 * (s * q₂) + c₃ * h 2 * (s * q₃) := by
      field_simp
    rw [e]
    exact add_le_add (W2 2) (W3 2)
  have hsum : ∑ t, (w t + h t) = (w 0 + h 0) + (w 1 + h 1) + (w 2 + h 2) := Fin.sum_univ_three _
  rw [hsum]
  have ho2 : 0 ≤ o 2 / B := div_nonneg (ho 2) hB.le
  have hw0 := hw 0; have hw1 := hw 1; have hw2 := hw 2
  have hh0 := hh 0; have hh1 := hh 1; have hh2 := hh 2
  have ho0 := ho 0; have ho1 := ho 1
  have L : c₁ * o 0 * Γ + c₁ * o 1 * Γ + c₁ * (o 2 / B) * Γ +
      (c₂ * w 0 * Γ + c₃ * h 0 * Γ) + (c₂ * w 1 * Γ + c₃ * h 1 * Γ) +
      (c₂ * w 2 * Γ + c₃ * h 2 * Γ) ≤
      (c₁ + c₂ + c₃) * Γ * (o 0 + o 1 + o 2 / B + ((w 0 + h 0) + (w 1 + h 1) + (w 2 + h 2))) := by
    have e : (c₁ + c₂ + c₃) * Γ * (o 0 + o 1 + o 2 / B + ((w 0 + h 0) + (w 1 + h 1) +
        (w 2 + h 2))) - (c₁ * o 0 * Γ + c₁ * o 1 * Γ + c₁ * (o 2 / B) * Γ +
        (c₂ * w 0 * Γ + c₃ * h 0 * Γ) + (c₂ * w 1 * Γ + c₃ * h 1 * Γ) +
        (c₂ * w 2 * Γ + c₃ * h 2 * Γ)) =
        Γ * ((c₂ + c₃) * (o 0 + o 1 + o 2 / B) + (c₁ + c₃) * (w 0 + w 1 + w 2) +
          (c₁ + c₂) * (h 0 + h 1 + h 2)) := by ring
    have : 0 ≤ Γ * ((c₂ + c₃) * (o 0 + o 1 + o 2 / B) + (c₁ + c₃) * (w 0 + w 1 + w 2) +
        (c₁ + c₂) * (h 0 + h 1 + h 2)) := by positivity
    linarith
  have e : c₁ * o 0 * q₁ + (c₂ * w 0 * q₂ + c₃ * h 0 * q₃) / s +
      s * (c₁ * o 1 * q₁ + (c₂ * w 1 * q₂ + c₃ * h 1 * q₃) / s) +
      s ^ 2 * (c₁ * o 2 * q₁ + (c₂ * w 2 * q₂ + c₃ * h 2 * q₃) / s) =
      c₁ * o 0 * q₁ + s * (c₁ * o 1 * q₁) + s ^ 2 * (c₁ * o 2 * q₁) +
        (c₂ * w 0 * q₂ + c₃ * h 0 * q₃) / s + s * ((c₂ * w 1 * q₂ + c₃ * h 1 * q₃) / s) +
        s ^ 2 * ((c₂ * w 2 * q₂ + c₃ * h 2 * q₃) / s) := by ring
  rw [e]
  linarith

/-! ### The density -/

/-- **The absolute coefficient sum** of the three quartics at `r = 1`, with the top monomial
`T₁(Q₂)` divided by `B = remainder α z cs`. -/
noncomputable def faceIdRayAPSum (Q : Fin 3 → LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (cs : Fin (m + 1) → ℝ) (x : Fin m → ℝ) : ℝ :=
  ‖faceIdRayAPOne (Q 0) α p x‖ + ‖faceIdRayAPOne (Q 1) α p x‖ +
    ‖faceIdRayAPOne (Q 2) α p x‖ / remainder α (simplexPoint x) cs +
    ∑ t, (‖faceIdRayAPTwo (Q t) α p x‖ + ‖faceIdRayAPThree (Q t) α x‖)

theorem faceIdRayAPSum_nonneg (Q : Fin 3 → LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (cs : Fin (m + 1) → ℝ) (x : Fin m → ℝ)
    (hB : 0 ≤ remainder α (simplexPoint x) cs) : 0 ≤ faceIdRayAPSum Q α p cs x := by
  unfold faceIdRayAPSum
  have : 0 ≤ ∑ t, (‖faceIdRayAPTwo (Q t) α p x‖ + ‖faceIdRayAPThree (Q t) α x‖) :=
    Finset.sum_nonneg fun _ _ => by positivity
  have : 0 ≤ ‖faceIdRayAPOne (Q 2) α p x‖ / remainder α (simplexPoint x) cs :=
    div_nonneg (norm_nonneg _) hB
  positivity

/-- `V₀ = ∑ zᵢ (M with Mγ = 0)ᵢ² + z_γ u ≥ min(m₀², 1)` for non-photon masses `Mᵢ² ≥ m₀²`,
`u ≥ 1`. -/
theorem faceIdRayAP_le_V₀ (M : Fin (m + 1) → ℝ) (γ : Fin (m + 1)) {m₀ : ℝ}
    (hM : ∀ i, i ≠ γ → m₀ ^ 2 ≤ M i ^ 2) {z : Fin (m + 1) → ℝ} (hz0 : ∀ i, 0 ≤ z i)
    (hz1 : ∑ i, z i = 1) {u : ℝ} (hu : 1 ≤ u) :
    min (m₀ ^ 2) 1 ≤ ∑ i, z i * Function.update M γ 0 i ^ 2 + z γ * u := by
  set c := min (m₀ ^ 2) 1 with hc
  have hc1 : c ≤ 1 := min_le_right _ _
  have hcm : c ≤ m₀ ^ 2 := min_le_left _ _
  have h : ∀ i, c * z i ≤ z i * Function.update M γ 0 i ^ 2 +
      (if i = γ then c * z i else 0) := by
    intro i
    by_cases hi : i = γ
    · subst hi
      simp
    · rw [Function.update_of_ne hi, ite_eq_right_iff.mpr (fun h => absurd h hi), add_zero]
      nlinarith [hz0 i, hM i hi]
  have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h i
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ γ, ← Finset.mul_sum] at h2
  simp only [Finset.mem_univ, ite_true, hz1] at h2
  have : c * z γ ≤ z γ * u := by nlinarith [hz0 γ]
  linarith

/-- **(A) with a power loss for a photon-mass density, from a majorant.** For a merged piece
with `m + 1 ≥ 6` lines, photon line `γ`, non-photon masses `≥ m₀ > 0` and a numerator
`N(r v)(ℓ) = ∑_{t<3} r^{2t} Q_t(ℓ/r)` along the ray (`Q_t` without quartic part for six
lines), suppose that for some `0 < δ ≤ 1` and every `0 < a ≤ 1` the weight
`z_γ^a B^{-δ} faceIdRayAPSum` has an integrable majorant (and `B > 0` a.e.). Then
`FaceIdRayAPow` holds for the density. -/
theorem faceIdRayAP_pow_pairDens (hm : 5 ≤ m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (cs : Fin (m + 1) → ℝ) (M : Fin (m + 1) → ℝ) (γ : Fin (m + 1)) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hM : ∀ i, i ≠ γ → m₀ ^ 2 ≤ M i ^ 2) (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (Q : Fin 3 → LoopQuartic)
    (hN : ∀ r : ℝ, 1 ≤ r → ∀ ℓ, N (r • majRayVec 1) ℓ =
      ∑ t : Fin 3, ((r : ℂ) ^ 2) ^ (t : ℕ) * (Q t).eval (r⁻¹ • ℓ))
    (hq : 6 ≤ m ∨ ∀ t, (Q t).quart = 0)
    (hMaj : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∃ F : (Fin m → ℝ) → ℝ,
      IntegrableOn F (simplexSet m) ∧ ∀ᵐ x ∂(volume.restrict (simplexSet m)),
        0 < remainder α (simplexPoint x) cs ∧
          simplexPoint x γ ^ a * remainder α (simplexPoint x) cs ^ (-δ) *
            faceIdRayAPSum Q α (fun i => cs i • majRayVec 1) cs x ≤ F x) :
    FaceIdRayAPow fun u k => pairDens (N k) α (fun l => cs l • k) M γ u := by
  obtain ⟨δ, hδ, hδ1, hMaj⟩ := hMaj
  refine ⟨δ, hδ, fun a ha => ?_⟩
  set a' := min a 1 with ha'_def
  have ha' : 0 < a' := lt_min ha one_pos
  have ha'1 : a' ≤ 1 := min_le_right _ _
  obtain ⟨F, hF, hFx⟩ := hMaj a' ha' ha'1
  set c₁ : ℝ := ((m + 1 - 4).factorial : ℝ) with hc₁
  set c₂ : ℝ := ((m + 1 - 5).factorial : ℝ) / 2 with hc₂
  set c₃ : ℝ := ((m + 1 - 6).factorial : ℝ) / 4 with hc₃
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hc₃0 : 0 ≤ c₃ := by positivity
  set c₀ : ℝ := min (m₀ ^ 2) 1 with hc₀_def
  have hc₀ : 0 < c₀ := lt_min (by positivity) one_pos
  have hc₀1 : c₀ ≤ 1 := min_le_right _ _
  set Kc : ℝ := (c₁ + c₂ + c₃) * c₀ ^ (-(m : ℝ)) with hKc
  have hF0 : 0 ≤ ∫ x in simplexSet m, F x := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hFx, ae_restrict_mem (QED.Integration.Feynman.measurableSet_simplexSet m)]
      with x ⟨hB, hx⟩ hxS
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    refine le_trans ?_ hx
    have := faceIdRayAPSum_nonneg Q α (fun i => cs i • majRayVec 1) cs x hB.le
    have := Real.rpow_nonneg (hz.1 γ) a'
    have := Real.rpow_nonneg hB.le (-δ)
    positivity
  refine ⟨π ^ 4 * Kc * ∫ x in simplexSet m, F x, fun s hs u hsu => ?_⟩
  have hs0 : 0 < s := by linarith
  have hu : 1 ≤ u := hs.trans hsu
  have hu0 : 0 < u := by linarith
  set r := Real.sqrt s with hr_def
  have hr1 : 1 ≤ r := by rw [hr_def, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hs
  have hr2 : r ^ 2 = s := Real.sq_sqrt hs0.le
  set v := majRayVec 1 with hv
  set p₁ : Fin (m + 1) → Fin 4 → ℝ := fun i => cs i • v with hp₁
  have hmom : (fun i => cs i • majRayVec s) = r • p₁ := by
    funext i
    simp only [hp₁, Pi.smul_apply, maj_majRayVec_eq hs0.le, hv]
    exact smul_comm _ _ _
  -- the quartic along the ray
  set R : LoopQuartic := qsum Finset.univ (fun t : Fin 3 => ((s : ℂ)) ^ (t : ℕ))
    (fun t => dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q t)) with hR
  have hRe : R.eval = N (majRayVec s) := by
    funext ℓ
    rw [maj_majRayVec_eq hs0.le, hN r hr1]
    simp only [hR, eval_qsum, eval_dilateQ, one_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 2
    rw [← hr2]; push_cast; ring
  change ‖(u : ℂ) * pairDens (N (majRayVec s)) α (fun l => cs l • majRayVec s) M γ u‖ ≤ _
  rw [pairDens_eq hRe, hmom]
  set f : (Fin m → ℝ) → ℂ := fun y => (simplexPoint y γ : ℂ) *
    paramAtV (m + 1) R α (r • p₁) (simplexPoint y)
      (symanzikV α (r • p₁) (Function.update M γ 0) (simplexPoint y) + simplexPoint y γ * u)
    with hf
  set g : (Fin m → ℝ) → ℝ := fun x => Kc * s ^ (1 - δ) * u ^ a' * F x with hg
  have hgi : IntegrableOn g (simplexSet m) := hF.const_mul _
  have hpt : ∀ᵐ x ∂(volume.restrict (simplexSet m)), ‖(u : ℂ) * f x‖ ≤ g x := by
    filter_upwards [hFx, ae_restrict_mem (QED.Integration.Feynman.measurableSet_simplexSet m)]
      with x ⟨hB, hx⟩ hxS
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    set z := simplexPoint x with hz_def
    set B := remainder α z cs with hB_def
    set Vm := ∑ i, z i * Function.update M γ 0 i ^ 2 with hVm
    set V₀ := Vm + z γ * u with hV₀_def
    set W := V₀ + s * B with hW_def
    have hV₀ : c₀ ≤ V₀ := faceIdRayAP_le_V₀ M γ hM hz.1 hz.2 hu
    have hVm0 : 0 ≤ Vm := Finset.sum_nonneg fun i _ => mul_nonneg (hz.1 i) (sq_nonneg _)
    have hV₀0 : 0 < V₀ := hc₀.trans_le hV₀
    have hVe : symanzikV α (r • p₁) (Function.update M γ 0) z + z γ * u = W := by
      rw [← hmom, maj_symanzikV_ray α _ z cs hs0.le, hW_def, hV₀_def, hVm, hB_def]
      ring
    have hW0 : 0 < W := by nlinarith [mul_pos hs0 hB]
    set w := u * z γ with hw_def
    have hw0 : 0 ≤ w := mul_nonneg hu0.le (hz.1 γ)
    have hwW : w ≤ W := by
      have := mul_pos hs0 hB
      simp only [hw_def, hW_def, hV₀_def]
      linarith [mul_comm u (z γ)]
    have hWW : V₀ + s * B ≤ W := le_rfl
    set Γ := c₀ ^ (-(m : ℝ)) * (s ^ (1 - δ) * B ^ (-δ) * w ^ a') with hΓ
    -- the pieces of the integrand
    have hP : ∀ t, ‖paramAtV (m + 1) (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q t)) α (r • p₁) z W‖ ≤
        c₁ * ‖faceIdRayAPOne (Q t) α p₁ x‖ / W ^ (m + 1 - 3) +
          (c₂ * ‖faceIdRayAPTwo (Q t) α p₁ x‖ / W ^ (m + 1 - 4) +
            c₃ * ‖faceIdRayAPThree (Q t) α x‖ / W ^ (m + 1 - 5)) / s := fun t => by
      rw [← hr2]
      exact faceIdRayAP_norm_paramAtV_dilate_le (Q t) α p₁ x hr1 hW0
    have hsplit : paramAtV (m + 1) R α (r • p₁) z W = ∑ t : Fin 3, ((s : ℂ)) ^ (t : ℕ) *
        paramAtV (m + 1) (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q t)) α (r • p₁) z W := by
      simp only [paramAtV, hR, ehat_qsum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have hnorm : ‖(u : ℂ) * f x‖ = w * ‖∑ t : Fin 3, ((s : ℂ)) ^ (t : ℕ) *
        paramAtV (m + 1) (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q t)) α (r • p₁) z W‖ := by
      simp only [hf]
      rw [← hz_def, hVe, hsplit, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hu0, abs_of_nonneg (hz.1 γ), hw_def]
      ring
    rw [hnorm]
    -- the three gains
    have hn1 : (1 : ℝ) + δ ≤ ((m + 1 - 3 : ℕ) : ℝ) - 1 := by
      have : (3 : ℝ) ≤ ((m + 1 - 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ m + 1 - 3)
      linarith
    have hn2 : δ ≤ ((m + 1 - 4 : ℕ) : ℝ) - 1 := by
      have : (2 : ℝ) ≤ ((m + 1 - 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ m + 1 - 4)
      linarith
    have hKn : ∀ j : ℕ, 3 ≤ j → ((m + 1 - j : ℕ) : ℝ) ≤ (m : ℝ) := fun j hj => by
      exact_mod_cast (by omega : m + 1 - j ≤ m)
    have g1 := faceIdRayAP_gain_zero (n := m + 1 - 3) hs0 hc₀ hc₀1 hV₀ hB hWW hw0 hwW hδ.le
      ha' ha'1 (by linarith) (hKn 3 le_rfl)
    have g1' := faceIdRayAP_gain_one (n := m + 1 - 3) hs0 hc₀ hc₀1 hV₀ hB hWW hw0 hwW hδ.le
      ha' ha'1 hn1 (hKn 3 le_rfl)
    have g2 := faceIdRayAP_gain_zero (n := m + 1 - 4) hs0 hc₀ hc₀1 hV₀ hB hWW hw0 hwW hδ.le
      ha' ha'1 hn2 (hKn 4 (by norm_num))
    have g3 : ∀ t, ‖faceIdRayAPThree (Q t) α x‖ * (s * (w / W ^ (m + 1 - 5))) ≤
        ‖faceIdRayAPThree (Q t) α x‖ * Γ := fun t => by
      rcases hq with h6 | hq0
      · have hn3 : δ ≤ ((m + 1 - 5 : ℕ) : ℝ) - 1 := by
          have : (2 : ℝ) ≤ ((m + 1 - 5 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 2 ≤ m + 1 - 5)
          linarith
        exact mul_le_mul_of_nonneg_left (faceIdRayAP_gain_zero hs0 hc₀ hc₀1 hV₀ hB hWW hw0 hwW
          hδ.le ha' ha'1 hn3 (hKn 5 (by norm_num))) (norm_nonneg _)
      · simp [faceIdRayAPThree, contractFour_eq_zero_of_quart _ _ (hq0 t)]
    have hsum := faceIdRayAP_sum_le (o := fun t => ‖faceIdRayAPOne (Q t) α p₁ x‖)
      (w := fun t => ‖faceIdRayAPTwo (Q t) α p₁ x‖) (h := fun t => ‖faceIdRayAPThree (Q t) α x‖)
      hs hB (by positivity : 0 ≤ w / W ^ (m + 1 - 3)) (by positivity : 0 ≤ w / W ^ (m + 1 - 4))
      (by positivity : 0 ≤ w / W ^ (m + 1 - 5)) hc₁0 hc₂0 hc₃0 (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) g1 g1' g2 g3
    -- the triangle inequality
    have htri : w * ‖∑ t : Fin 3, ((s : ℂ)) ^ (t : ℕ) *
        paramAtV (m + 1) (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q t)) α (r • p₁) z W‖ ≤
        c₁ * ‖faceIdRayAPOne (Q 0) α p₁ x‖ * (w / W ^ (m + 1 - 3)) +
          (c₂ * ‖faceIdRayAPTwo (Q 0) α p₁ x‖ * (w / W ^ (m + 1 - 4)) +
            c₃ * ‖faceIdRayAPThree (Q 0) α x‖ * (w / W ^ (m + 1 - 5))) / s +
        s * (c₁ * ‖faceIdRayAPOne (Q 1) α p₁ x‖ * (w / W ^ (m + 1 - 3)) +
          (c₂ * ‖faceIdRayAPTwo (Q 1) α p₁ x‖ * (w / W ^ (m + 1 - 4)) +
            c₃ * ‖faceIdRayAPThree (Q 1) α x‖ * (w / W ^ (m + 1 - 5))) / s) +
        s ^ 2 * (c₁ * ‖faceIdRayAPOne (Q 2) α p₁ x‖ * (w / W ^ (m + 1 - 3)) +
          (c₂ * ‖faceIdRayAPTwo (Q 2) α p₁ x‖ * (w / W ^ (m + 1 - 4)) +
            c₃ * ‖faceIdRayAPThree (Q 2) α x‖ * (w / W ^ (m + 1 - 5))) / s) := by
      rw [Fin.sum_univ_three]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, one_mul, pow_one]
      have h3 := norm_add₃_le (a := ((s : ℂ)) ^ ((0 : Fin 3) : ℕ) *
          paramAtV (m + 1) (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q 0)) α (r • p₁) z W)
        (b := ((s : ℂ)) ^ ((1 : Fin 3) : ℕ) *
          paramAtV (m + 1) (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q 1)) α (r • p₁) z W)
        (c := ((s : ℂ)) ^ ((2 : Fin 3) : ℕ) *
          paramAtV (m + 1) (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q 2)) α (r • p₁) z W)
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
        Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, one_mul, pow_one] at h3
      have k0 := hP 0
      have k1 := mul_le_mul_of_nonneg_left (hP 1) hs0.le
      have k2 := mul_le_mul_of_nonneg_left (hP 2) (sq_nonneg s)
      have hsum3 := mul_le_mul_of_nonneg_left (h3.trans (add_le_add (add_le_add k0 k1) k2)) hw0
      refine hsum3.trans (le_of_eq ?_)
      field_simp
    have hfin : (c₁ + c₂ + c₃) * Γ * faceIdRayAPSum Q α p₁ cs x ≤ g x := by
      have hw' : w ^ a' = u ^ a' * z γ ^ a' := Real.mul_rpow hu0.le (hz.1 γ)
      have hK : 0 ≤ Kc * s ^ (1 - δ) * u ^ a' := by positivity
      calc (c₁ + c₂ + c₃) * Γ * faceIdRayAPSum Q α p₁ cs x
          = Kc * s ^ (1 - δ) * u ^ a' * (z γ ^ a' * B ^ (-δ) * faceIdRayAPSum Q α p₁ cs x) := by
            rw [hΓ, hw', hKc]; ring
        _ ≤ Kc * s ^ (1 - δ) * u ^ a' * F x := mul_le_mul_of_nonneg_left hx hK
    refine htri.trans (le_trans ?_ hfin)
    refine le_of_le_of_eq hsum ?_
    simp only [faceIdRayAPSum]
    rfl
  have hint := norm_integral_le_of_norm_le hgi hpt
  have hgint : ∫ x in simplexSet m, g x = Kc * s ^ (1 - δ) * u ^ a' * ∫ x in simplexSet m, F x :=
    integral_const_mul _ _
  have hua : u ^ a' ≤ u ^ a := Real.rpow_le_rpow_of_exponent_le hu (min_le_left _ _)
  rw [integral_const_mul] at hint
  rw [show (u : ℂ) * (-((π : ℂ) ^ 4) * ∫ y in simplexSet m, f y) =
      -((π : ℂ) ^ 4) * ((u : ℂ) * ∫ y in simplexSet m, f y) by ring, norm_mul, norm_neg,
    norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [hgint] at hint
  have hK0 : 0 ≤ Kc := by positivity
  calc π ^ 4 * ‖(u : ℂ) * ∫ y in simplexSet m, f y‖
      ≤ π ^ 4 * (Kc * s ^ (1 - δ) * u ^ a' * ∫ x in simplexSet m, F x) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ ≤ π ^ 4 * (Kc * s ^ (1 - δ) * u ^ a * ∫ x in simplexSet m, F x) := by
        gcongr
    _ = π ^ 4 * Kc * (∫ x in simplexSet m, F x) * s ^ (1 - δ) * u ^ a := by ring

end QED.GradedProof.RPi4

end
