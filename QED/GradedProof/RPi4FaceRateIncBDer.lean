/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncInt
public import QED.GradedProof.RPi4FaceIdRayBRay

/-!
# (R-Π₄) step L10, T2.UV: the increment rate (B) from a derivative along the ray

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (input (B) of
`QED.GradedProof.RPi4.faceRateInc_of_size_rate`). Along `k'(σ) = tiltVec √σ σ`, suppose that
`G(u, k'(s)) - G(u, k'(1)) = ∫_1^s σ⁻¹ Gd(u, k'(σ)) dσ` for `u ≥ s ≥ 1`
(`FaceRateIncDeriv G Gd`: `Gd` is the logarithmic derivative `σ ∂_σ` of `G` along the ray), and
that `Gd` has the value rate (B) `QED.GradedProof.RPi4.FaceIdRayRateB`. Then `G` has the increment
rate (B) `QED.GradedProof.RPi4.FaceRateIncB`, with the same constant and exponent:

`‖u ΔG(u) - ΔL‖ ≤ B s^p u^{-1/2} (s - s')/s'`, `L(s) = lim_u u (G(u, k'(s)) - G(u, k'(1)))`.

## Proof

For `u, v ≥ s`, `u ΔG(u) - v ΔG(v) = ∫_{s'}^{s} σ⁻¹ ((u Gd(u) - Λ(σ)) - (v Gd(v) - Λ(σ)))`, of norm
`≤ (s - s')/s' · B s^p (u^{-1/2} + v^{-1/2})` (`faceRateIncDeriv_norm_sub_le`). With `s' = 1`
this makes `u (G(u, k'(s)) - G(u, k'(1)))` Cauchy as `u → ∞` (`faceRateIncDeriv_tendsto`); let
`v → ∞` in the bound.

* `FaceRateIncDeriv`, `faceRateIncDeriv_of_hasDerivAt` (from a pointwise derivative);
* `faceRateIncDeriv_mul_sub`, `faceRateIncDeriv_norm_sub_le`, `faceRateIncDeriv_tendsto`;
* **`faceRateIncB_of_deriv`**: `FaceIdRayRateB Gd` + `FaceRateIncDeriv G Gd` ⇒ `FaceRateIncB G`.
-/

@[expose] public section

open Complex Filter Topology Set MeasureTheory

namespace QED.GradedProof.RPi4

/-- **`Gd` is the logarithmic derivative of `G` along the ray**: for `u ≥ s ≥ 1`,
`σ ↦ σ⁻¹ Gd(u, k'(σ))` is integrable on `[1, s]` with integral `G(u, k'(s)) - G(u, k'(1))`. -/
def FaceRateIncDeriv (G Gd : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
    IntervalIntegrable (fun σ : ℝ => ((σ⁻¹ : ℝ) : ℂ) * Gd u (tiltVec (Real.sqrt σ) σ)) volume 1 s ∧
      G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt 1) 1) =
        ∫ σ in (1 : ℝ)..s, ((σ⁻¹ : ℝ) : ℂ) * Gd u (tiltVec (Real.sqrt σ) σ)

variable {G Gd : ℝ → (Fin 4 → ℝ) → ℂ}

/-- **`FaceRateIncDeriv` from a pointwise derivative**: `σ ↦ G(u, k'(σ))` continuous on
`[1, u]` with derivative `σ⁻¹ Gd(u, k'(σ))` on `(1, u)`, the derivative integrable. -/
theorem faceRateIncDeriv_of_hasDerivAt
    (hcont : ∀ u : ℝ, 1 ≤ u → ContinuousOn (fun σ => G u (tiltVec (Real.sqrt σ) σ)) (Icc 1 u))
    (hder : ∀ u σ : ℝ, 1 < σ → σ < u → HasDerivAt (fun τ => G u (tiltVec (Real.sqrt τ) τ))
      (((σ⁻¹ : ℝ) : ℂ) * Gd u (tiltVec (Real.sqrt σ) σ)) σ)
    (hint : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u → IntervalIntegrable
      (fun σ : ℝ => ((σ⁻¹ : ℝ) : ℂ) * Gd u (tiltVec (Real.sqrt σ) σ)) volume 1 s) :
    FaceRateIncDeriv G Gd := fun s hs u hu => by
  refine ⟨hint s hs u hu, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs
    ((hcont u (hs.trans hu)).mono (Icc_subset_Icc le_rfl hu))
    (fun σ hσ => hder u σ hσ.1 (hσ.2.trans_le hu)) (hint s hs u hu)]

/-- **The increment as an integral**: for `1 ≤ s' ≤ s ≤ u`,
`u ΔG(u) = ∫_{s'}^{s} u σ⁻¹ Gd(u, k'(σ))`, the integrand integrable. -/
theorem faceRateIncDeriv_mul_sub (hD : FaceRateIncDeriv G Gd) {s s' u : ℝ} (h1 : 1 ≤ s')
    (hss : s' ≤ s) (hu : s ≤ u) :
    IntervalIntegrable (fun σ : ℝ => (u : ℂ) * (((σ⁻¹ : ℝ) : ℂ) *
        Gd u (tiltVec (Real.sqrt σ) σ))) volume s' s ∧
      (u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s')) =
        ∫ σ in s'..s, (u : ℂ) * (((σ⁻¹ : ℝ) : ℂ) * Gd u (tiltVec (Real.sqrt σ) σ)) := by
  obtain ⟨hi, he⟩ := hD s (h1.trans hss) u hu
  obtain ⟨hi', he'⟩ := hD s' h1 u (hss.trans hu)
  refine ⟨(hi.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le h1 hss) right_mem_uIcc)).const_mul _,
    ?_⟩
  rw [intervalIntegral.integral_const_mul, ← intervalIntegral.integral_interval_sub_left hi hi',
    ← he, ← he']
  ring

/-- **The Cauchy bound**: for `1 ≤ s' ≤ s` and `u, v ≥ s`,
`‖u ΔG(u) - v ΔG(v)‖ ≤ (s - s')/s' · B s^p (u^{-1/2} + v^{-1/2})`. -/
theorem faceRateIncDeriv_norm_sub_le (hD : FaceRateIncDeriv G Gd) {B p : ℝ} {Λ : ℝ → ℂ}
    (hB : 0 ≤ B) (hp : 0 ≤ p)
    (hrate : ∀ σ : ℝ, 1 ≤ σ → ∀ u : ℝ, σ ≤ u →
      ‖(u : ℂ) * Gd u (tiltVec (Real.sqrt σ) σ) - Λ σ‖ ≤ B * σ ^ p * u ^ (-(1 / 2) : ℝ))
    {s s' u v : ℝ} (h1 : 1 ≤ s') (hss : s' ≤ s) (hu : s ≤ u) (hv : s ≤ v) :
    ‖(u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s')) -
        (v : ℂ) * (G v (tiltVec (Real.sqrt s) s) - G v (tiltVec (Real.sqrt s') s'))‖ ≤
      (s - s') / s' * (B * s ^ p) * (u ^ (-(1 / 2) : ℝ) + v ^ (-(1 / 2) : ℝ)) := by
  obtain ⟨hiu, heu⟩ := faceRateIncDeriv_mul_sub hD h1 hss hu
  obtain ⟨hiv, hev⟩ := faceRateIncDeriv_mul_sub hD h1 hss hv
  have hs'0 : 0 < s' := one_pos.trans_le h1
  have hu0 : 0 ≤ u ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by linarith) _
  have hv0 : 0 ≤ v ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by linarith) _
  rw [heu, hev, ← intervalIntegral.integral_sub hiu hiv]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := 1 / s' * (B * s ^ p) * (u ^ (-(1 / 2) : ℝ) + v ^ (-(1 / 2) : ℝ))) fun σ hσ => ?_).trans
    (le_of_eq ?_)
  · rw [uIoc_of_le hss] at hσ
    have hσ1 : 1 ≤ σ := h1.trans hσ.1.le
    have hσ0 : 0 < σ := one_pos.trans_le hσ1
    have e : (u : ℂ) * (((σ⁻¹ : ℝ) : ℂ) * Gd u (tiltVec (Real.sqrt σ) σ)) -
        (v : ℂ) * (((σ⁻¹ : ℝ) : ℂ) * Gd v (tiltVec (Real.sqrt σ) σ)) =
        ((σ⁻¹ : ℝ) : ℂ) * (((u : ℂ) * Gd u (tiltVec (Real.sqrt σ) σ) - Λ σ) -
          ((v : ℂ) * Gd v (tiltVec (Real.sqrt σ) σ) - Λ σ)) := by ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hσ0)]
    have hσp : σ ^ p ≤ s ^ p := Real.rpow_le_rpow hσ0.le hσ.2 hp
    have hinv : σ⁻¹ ≤ 1 / s' := by rw [one_div]; exact inv_anti₀ hs'0 hσ.1.le
    calc σ⁻¹ * ‖((u : ℂ) * Gd u (tiltVec (Real.sqrt σ) σ) - Λ σ) -
          ((v : ℂ) * Gd v (tiltVec (Real.sqrt σ) σ) - Λ σ)‖
        ≤ σ⁻¹ * (B * σ ^ p * u ^ (-(1 / 2) : ℝ) + B * σ ^ p * v ^ (-(1 / 2) : ℝ)) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add
            (hrate σ hσ1 u (hσ.2.trans hu)) (hrate σ hσ1 v (hσ.2.trans hv))))
            (inv_nonneg.2 hσ0.le)
      _ = σ⁻¹ * (B * σ ^ p) * (u ^ (-(1 / 2) : ℝ) + v ^ (-(1 / 2) : ℝ)) := by ring
      _ ≤ 1 / s' * (B * s ^ p) * (u ^ (-(1 / 2) : ℝ) + v ^ (-(1 / 2) : ℝ)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul hinv
            (mul_le_mul_of_nonneg_left hσp hB) (by positivity) (by positivity)) (by positivity)
  · rw [abs_of_nonneg (sub_nonneg.2 hss)]
    field_simp

/-- **The limit along the ray exists**: `u (G(u, k'(s)) - G(u, k'(1)))` converges as `u → ∞`. -/
theorem faceRateIncDeriv_tendsto (hD : FaceRateIncDeriv G Gd) {B p : ℝ} {Λ : ℝ → ℂ}
    (hB : 0 ≤ B) (hp : 0 ≤ p)
    (hrate : ∀ σ : ℝ, 1 ≤ σ → ∀ u : ℝ, σ ≤ u →
      ‖(u : ℂ) * Gd u (tiltVec (Real.sqrt σ) σ) - Λ σ‖ ≤ B * σ ^ p * u ^ (-(1 / 2) : ℝ))
    {s : ℝ} (hs : 1 ≤ s) :
    ∃ L : ℂ, Tendsto (fun u : ℝ => (u : ℂ) *
      (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt 1) 1))) atTop (𝓝 L) := by
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
  set K : ℝ := (s - 1) / 1 * (B * s ^ p)
  have hK : 0 ≤ K := by
    have : 0 ≤ s - 1 := by linarith
    positivity
  have ht : Tendsto (fun N : ℝ => K * (2 * N ^ (-(1 / 2) : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2).const_mul K
  obtain ⟨N, hN, hNs⟩ := ((ht.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop s)).exists
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hN0 : 0 < N := one_pos.trans_le (hs.trans hNs)
  have hnN : n ^ (-(1 / 2) : ℝ) ≤ N ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hN0 hn (by norm_num)
  calc _ ≤ K * (n ^ (-(1 / 2) : ℝ) + N ^ (-(1 / 2) : ℝ)) :=
        faceRateIncDeriv_norm_sub_le hD hB hp hrate le_rfl hs (hNs.trans hn) hNs
    _ ≤ K * (2 * N ^ (-(1 / 2) : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) hK
    _ < ε := hN

/-- **The increment rate (B) from the rate (B) of the derivative along the ray.** -/
theorem faceRateIncB_of_deriv (hGd : FaceIdRayRateB Gd) (hD : FaceRateIncDeriv G Gd) :
    FaceRateIncB G := by
  obtain ⟨B, p, hp, Λ, hrate⟩ := hGd
  have hB : 0 ≤ B := by
    have h := hrate 1 le_rfl 1 le_rfl
    rw [Real.one_rpow, Real.one_rpow, mul_one, mul_one] at h
    exact (norm_nonneg _).trans h
  have hp0 : 0 ≤ p := by linarith
  set a : ℝ → ℝ → ℂ := fun s u => (u : ℂ) *
    (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt 1) 1)) with ha
  refine ⟨B, p, hp, fun s => limUnder atTop (a s), fun s s' h1 hss _ u hu => ?_⟩
  have T := (tendsto_nhds_limUnder (faceRateIncDeriv_tendsto hD hB hp0 hrate (h1.trans hss))).sub
    (tendsto_nhds_limUnder (faceRateIncDeriv_tendsto hD hB hp0 hrate h1))
  have T2 := (tendsto_const_nhds (x := (u : ℂ) *
    (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s')))).sub T |>.norm
  have T3 : Tendsto (fun v : ℝ => (s - s') / s' * (B * s ^ p) *
      (u ^ (-(1 / 2) : ℝ) + v ^ (-(1 / 2) : ℝ))) atTop
      (𝓝 ((s - s') / s' * (B * s ^ p) * (u ^ (-(1 / 2) : ℝ) + 0))) :=
    (tendsto_const_nhds.add (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2))).const_mul _
  refine (le_of_tendsto_of_tendsto T2 T3 ?_).trans_eq (by ring)
  filter_upwards [eventually_ge_atTop s] with v hv
  have e : a s v - a s' v = (v : ℂ) *
      (G v (tiltVec (Real.sqrt s) s) - G v (tiltVec (Real.sqrt s') s')) := by
    simp only [ha]; ring
  rw [e]
  exact faceRateIncDeriv_norm_sub_le hD hB hp0 hrate h1 hss hu hv

end QED.GradedProof.RPi4

end
