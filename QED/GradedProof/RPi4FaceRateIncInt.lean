/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateInc

/-!
# (R-Π₄) step L10, T2.UV: the per-class increment rate by interpolation

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (the inputs
`QED.GradedProof.RPi4.FaceRateIncRay` of `QED.GradedProof.RPi4.faceRateInc_of_ray`). The increment
counterpart of `QED.GradedProof.RPi4.faceIdRay_of_size_rate`: along `k'(σ) = tiltVec √σ σ`, for
`1 ≤ s' ≤ s ≤ 2s'`, `u ≥ s`, `ε = (s - s')/s'`, write `ΔG(u) = G(u, k'(s)) - G(u, k'(s'))`. The
sharp increment rate `C s (s/u)^η ε` follows from

* (A) a **size bound with a gain**: `‖u ΔG(u)‖ ≤ A s^{1-δ} ε` (`FaceRateIncA`), or its form with a
  power loss `‖u ΔG(u)‖ ≤ A_a s^{1-δ} u^a ε` for every `a > 0` (`FaceRateIncAPow`);
* (B) a **rate with a polynomial constant**: `‖u ΔG(u) - (L(s) - L(s'))‖ ≤ B s^p u^{-1/2} ε`
  (`FaceRateIncB`).

These are the value inputs of `faceIdRay_of_size_rate` times `ε`; the split points are the same.

* `faceRateInc_size_le`, `faceRateInc_rate_le`: the two exponent comparisons;
* `faceRateInc_interp`: the pointwise interpolation;
* **`faceRateInc_of_size_rate`**: (A) + (B) ⇒ `FaceRateIncRay`;
* **`faceRateIncA_of_pow_rate`**: (A with a power loss) + (B) ⇒ (A);
* **`faceRateInc_of_pow_rate`**: (A with a power loss) + (B) ⇒ `FaceRateIncRay`;
* `FaceRateIncAPow.zero/add/const_mul/sum/congr`, `FaceRateIncB.zero/add/const_mul/sum/congr`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.RPi4

/-- **(A) for increments**: `‖u (G(u, k'(s)) - G(u, k'(s')))‖ ≤ A s^{1-δ} (s - s')/s'` for
`1 ≤ s' ≤ s ≤ 2s'`, `u ≥ s`, some `δ > 0`. -/
def FaceRateIncA (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ A δ : ℝ, 0 < δ ∧ ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' → ∀ u : ℝ, s ≤ u →
    ‖(u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s'))‖ ≤
      A * s ^ (1 - δ) * ((s - s') / s')

/-- **(A) for increments with a power loss**: some `δ > 0` such that for every `a > 0`,
`‖u (G(u, k'(s)) - G(u, k'(s')))‖ ≤ A s^{1-δ} u^a (s - s')/s'`. -/
def FaceRateIncAPow (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, 0 < a → ∃ A : ℝ, ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' →
    ∀ u : ℝ, s ≤ u →
      ‖(u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s'))‖ ≤
        A * s ^ (1 - δ) * u ^ a * ((s - s') / s')

/-- **(B) for increments**: `‖u (G(u, k'(s)) - G(u, k'(s'))) - (L(s) - L(s'))‖ ≤
B s^p u^{-1/2} (s - s')/s'`, some `p ≥ 1`. -/
def FaceRateIncB (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ B p : ℝ, 1 ≤ p ∧ ∃ L : ℝ → ℂ, ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' → ∀ u : ℝ, s ≤ u →
    ‖(u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s')) -
      (L s - L s')‖ ≤ B * s ^ p * u ^ (-(1 / 2) : ℝ) * ((s - s') / s')

/-! ### The interpolation -/

/-- `s (s/u)^η = s^{1+η} u^{-η}`. -/
theorem faceRateInc_mul_rpow_eq {s u η : ℝ} (hs : 0 < s) (hu : 0 < u) :
    s * (s / u) ^ η = s ^ (1 + η) * u ^ (-η) := by
  rw [Real.div_rpow hs.le hu.le, Real.rpow_neg hu.le, Real.rpow_add hs, Real.rpow_one,
    div_eq_mul_inv]
  ring

/-- Below the split: `s^{1-δ} ≤ s (s/u)^η` for `u ≤ s^q`, `η (q - 1) ≤ δ`, `η ≥ 0`. -/
theorem faceRateInc_size_le {s u δ q η : ℝ} (hs : 1 ≤ s) (hu0 : 0 < u) (hu : u ≤ s ^ q)
    (hη : 0 ≤ η) (hηδ : η * (q - 1) ≤ δ) : s ^ (1 - δ) ≤ s * (s / u) ^ η := by
  have hs0 : 0 < s := by linarith
  rw [faceRateInc_mul_rpow_eq hs0 hu0]
  have hu' : (s ^ q) ^ (-η) ≤ u ^ (-η) := Real.rpow_le_rpow_of_nonpos hu0 hu (by linarith)
  rw [← Real.rpow_mul hs0.le] at hu'
  calc s ^ (1 - δ) ≤ s ^ (1 + η + q * -η) := faceIdRay_rpow_mono hs (by nlinarith)
    _ = s ^ (1 + η) * s ^ (q * -η) := Real.rpow_add hs0 _ _
    _ ≤ s ^ (1 + η) * u ^ (-η) := mul_le_mul_of_nonneg_left hu' (Real.rpow_nonneg hs0.le _)

/-- Above the split: `s^p u^{-1/2} ≤ s (s/u)^η` for `u ≥ s^q`, `0 ≤ η ≤ 1/2`, `q (1/2 - η) ≥ p`. -/
theorem faceRateInc_rate_le {s u p q η : ℝ} (hs : 1 ≤ s) (hu : s ^ q ≤ u) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2) (hpq : p ≤ q * (1 / 2 - η)) :
    s ^ p * u ^ (-(1 / 2) : ℝ) ≤ s * (s / u) ^ η := by
  have hs0 : 0 < s := by linarith
  have hsq : 0 < s ^ q := Real.rpow_pos_of_pos hs0 _
  have hu0 : 0 < u := hsq.trans_le hu
  rw [faceRateInc_mul_rpow_eq hs0 hu0]
  have hsplit : u ^ (-(1 / 2) : ℝ) = u ^ (-η) * u ^ (-(1 / 2 - η)) := by
    rw [← Real.rpow_add hu0]; ring_nf
  have hu' : u ^ (-(1 / 2 - η)) ≤ (s ^ q) ^ (-(1 / 2 - η)) :=
    Real.rpow_le_rpow_of_nonpos hsq hu (by linarith)
  rw [← Real.rpow_mul hs0.le] at hu'
  have hsp : s ^ p * s ^ (q * -(1 / 2 - η)) ≤ s ^ (1 + η) := by
    rw [← Real.rpow_add hs0]
    exact faceIdRay_rpow_mono hs (by nlinarith)
  have hue : 0 ≤ u ^ (-η) := Real.rpow_nonneg hu0.le _
  calc s ^ p * u ^ (-(1 / 2) : ℝ) = s ^ p * u ^ (-(1 / 2 - η)) * u ^ (-η) := by
        rw [hsplit]; ring
    _ ≤ s ^ p * s ^ (q * -(1 / 2 - η)) * u ^ (-η) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hu' (Real.rpow_nonneg hs0.le _)) hue
    _ ≤ s ^ (1 + η) * u ^ (-η) := mul_le_mul_of_nonneg_right hsp hue

/-- **The pointwise interpolation**: from `‖x‖, ‖y‖ ≤ A s^{1-δ} ε` and
`‖x - y‖ ≤ B s^p u^{-1/2} ε`, `‖x - y‖ ≤ max(2|A|, |B|) s (s/u)^η ε` with
`η = min(1/4, δ/(4p - 1))`. -/
theorem faceRateInc_interp {x y : ℂ} {s u A B δ p ε : ℝ} (hs : 1 ≤ s) (hsu : s ≤ u)
    (hδ : 0 < δ) (hp : 1 ≤ p) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ A * s ^ (1 - δ) * ε) (hy : ‖y‖ ≤ A * s ^ (1 - δ) * ε)
    (hxy : ‖x - y‖ ≤ B * s ^ p * u ^ (-(1 / 2) : ℝ) * ε) :
    ‖x - y‖ ≤ max (2 * |A|) |B| * s * (s / u) ^ (min (1 / 4) (δ / (4 * p - 1))) * ε := by
  set η : ℝ := min (1 / 4) (δ / (4 * p - 1)) with hη_def
  have hp1 : 0 < 4 * p - 1 := by linarith
  have hη : 0 < η := lt_min (by norm_num) (div_pos hδ hp1)
  have hη4 : η ≤ 1 / 4 := min_le_left _ _
  have hηδ : η * (4 * p - 1) ≤ δ := by
    have := min_le_right (1 / 4 : ℝ) (δ / (4 * p - 1))
    rw [← hη_def, le_div_iff₀ hp1] at this
    exact this
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := hs0.trans_le hsu
  have hX0 : 0 ≤ s * (s / u) ^ η := mul_nonneg hs0.le (Real.rpow_nonneg (div_pos hs0 hu0).le _)
  have hM : 0 ≤ max (2 * |A|) |B| := (abs_nonneg _).trans (le_max_right _ _)
  rw [mul_assoc (max _ _ * s)]
  rw [mul_assoc (max _ _)]
  rcases le_or_gt u (s ^ (4 * p)) with hu | hu
  · have h1 : ‖x - y‖ ≤ 2 * |A| * s ^ (1 - δ) * ε := by
      have h := (norm_sub_le _ _).trans (add_le_add hx hy)
      have hA' : A * s ^ (1 - δ) * ε ≤ |A| * s ^ (1 - δ) * ε :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
          (Real.rpow_nonneg hs0.le _)) hε
      linarith
    have h2 := faceRateInc_size_le hs hu0 hu hη.le hηδ
    calc ‖x - y‖ ≤ 2 * |A| * s ^ (1 - δ) * ε := h1
      _ ≤ 2 * |A| * (s * (s / u) ^ η) * ε :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) hε
      _ ≤ max (2 * |A|) |B| * (s * (s / u) ^ η) * ε :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0) hε
      _ = _ := by ring
  · have h2 := faceRateInc_rate_le hs hu.le hη.le (by linarith)
      (by nlinarith : p ≤ 4 * p * (1 / 2 - η))
    have h3 : B * s ^ p * u ^ (-(1 / 2) : ℝ) * ε ≤ |B| * (s ^ p * u ^ (-(1 / 2) : ℝ)) * ε := by
      rw [mul_assoc B]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
        (mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg hu0.le _))) hε
    calc ‖x - y‖ ≤ |B| * (s ^ p * u ^ (-(1 / 2) : ℝ)) * ε := hxy.trans h3
      _ ≤ |B| * (s * (s / u) ^ η) * ε :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) hε
      _ ≤ max (2 * |A|) |B| * (s * (s / u) ^ η) * ε :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hX0) hε
      _ = _ := by ring

/-- **The per-class increment rate from (A) and (B).** -/
theorem faceRateInc_of_size_rate {G : ℝ → (Fin 4 → ℝ) → ℂ} (hA : FaceRateIncA G)
    (hB : FaceRateIncB G) : FaceRateIncRay G := by
  obtain ⟨A, δ, hδ, hA⟩ := hA
  obtain ⟨B, p, hp, L, hB⟩ := hB
  have hp1 : 0 < 4 * p - 1 := by linarith
  refine ⟨max (2 * |A|) |B|, min (1 / 4) (δ / (4 * p - 1)),
    lt_min (by norm_num) (div_pos hδ hp1), L, fun s s' hs' hss hs2 u hsu => ?_⟩
  have hs : 1 ≤ s := hs'.trans hss
  have hs0 : 0 < s := by linarith
  have hε : 0 ≤ (s - s') / s' := div_nonneg (by linarith) (by linarith)
  set g : ℝ → ℂ := fun v => G v (tiltVec (Real.sqrt s) s) - G v (tiltVec (Real.sqrt s') s')
    with hg
  -- the limit increment inherits the size bound
  have hL : ‖L s - L s'‖ ≤ A * s ^ (1 - δ) * ((s - s') / s') := by
    have ht : Tendsto (fun v : ℝ => (v : ℂ) * g v) atTop (𝓝 (L s - L s')) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h0 : Tendsto (fun v : ℝ => B * s ^ p * ((s - s') / s') * v ^ (-(1 / 2) : ℝ)) atTop
          (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
          (B * s ^ p * ((s - s') / s'))
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
      filter_upwards [eventually_ge_atTop s] with v hv
      exact (hB s s' hs' hss hs2 v hv).trans (le_of_eq (by ring))
    exact le_of_tendsto ht.norm (by
      filter_upwards [eventually_ge_atTop s] with v hv using hA s s' hs' hss hs2 v hv)
  exact faceRateInc_interp hs hsu hδ hp hε (hA s s' hs' hss hs2 u hsu) hL
    (hB s s' hs' hss hs2 u hsu)

/-- **(A) from its power-loss form and (B)**: split at `u = s^{2p}`, `a = δ/(4p)`; above the
split, (B) bounds `u ΔG` by the limit increment plus `|B| ε`, and the limit increment by the
value at `u = s^{2p}`. -/
theorem faceRateIncA_of_pow_rate {G : ℝ → (Fin 4 → ℝ) → ℂ} (hA : FaceRateIncAPow G)
    (hB : FaceRateIncB G) : FaceRateIncA G := by
  obtain ⟨δ, hδ, hA⟩ := hA
  obtain ⟨B, p, hp, L, hB⟩ := hB
  have hp0 : 0 < p := by linarith
  obtain ⟨A, hA⟩ := hA (δ / (4 * p)) (div_pos hδ (by linarith))
  set δ' : ℝ := min δ 1 / 2 with hδ'
  have hδ'0 : 0 < δ' := by simp only [hδ']; exact half_pos (lt_min hδ one_pos)
  have hδ'δ : δ' ≤ δ / 2 := by simp only [hδ']; linarith [min_le_left δ 1]
  have hδ'1 : δ' ≤ 1 / 2 := by simp only [hδ']; linarith [min_le_right δ 1]
  refine ⟨|A| + 2 * |B|, δ', hδ'0, fun s s' hs' hss hs2 u hsu => ?_⟩
  have hs : 1 ≤ s := hs'.trans hss
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := hs0.trans_le hsu
  have hε : 0 ≤ (s - s') / s' := div_nonneg (by linarith) (by linarith)
  set ε := (s - s') / s' with hε_def
  set g : ℝ → ℂ := fun v => G v (tiltVec (Real.sqrt s) s) - G v (tiltVec (Real.sqrt s') s')
    with hg
  set u₀ : ℝ := s ^ (2 * p) with hu₀
  have hu₀0 : 0 < u₀ := Real.rpow_pos_of_pos hs0 _
  have hsu₀ : s ≤ u₀ := by
    calc s = s ^ (1 : ℝ) := (Real.rpow_one s).symm
      _ ≤ u₀ := faceIdRay_rpow_mono hs (by linarith)
  have hgain : s ^ (1 - δ / 2) ≤ s ^ (1 - δ') := faceIdRay_rpow_mono hs (by linarith)
  have hone : 1 ≤ s ^ (1 - δ') := Real.one_le_rpow hs (by linarith)
  -- below the split: the power loss is at most `s^{δ/2}`
  have below : ∀ v : ℝ, s ≤ v → v ≤ u₀ → ‖(v : ℂ) * g v‖ ≤ |A| * s ^ (1 - δ / 2) * ε := by
    intro v hv hvu
    have hv0 : 0 < v := hs0.trans_le hv
    have hpow : v ^ (δ / (4 * p)) ≤ s ^ (δ / 2) := by
      calc v ^ (δ / (4 * p)) ≤ u₀ ^ (δ / (4 * p)) :=
            Real.rpow_le_rpow hv0.le hvu (div_pos hδ (by linarith)).le
        _ = s ^ (δ / 2) := by
            rw [hu₀, ← Real.rpow_mul hs0.le]
            congr 1
            field_simp
            ring
    have hsplit : s ^ (1 - δ) * s ^ (δ / 2) = s ^ (1 - δ / 2) := by
      rw [← Real.rpow_add hs0]; ring_nf
    calc ‖(v : ℂ) * g v‖ ≤ A * s ^ (1 - δ) * v ^ (δ / (4 * p)) * ε := hA s s' hs' hss hs2 v hv
      _ ≤ |A| * s ^ (1 - δ) * s ^ (δ / 2) * ε := by
          refine mul_le_mul_of_nonneg_right ?_ hε
          refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
            (Real.rpow_nonneg hs0.le _)) (Real.rpow_nonneg hv0.le _)).trans ?_
          exact mul_le_mul_of_nonneg_left hpow (mul_nonneg (abs_nonneg _)
            (Real.rpow_nonneg hs0.le _))
      _ = |A| * s ^ (1 - δ / 2) * ε := by rw [mul_assoc |A|, hsplit]
  rcases le_or_gt u u₀ with hu | hu
  · refine (below u hsu hu).trans (mul_le_mul_of_nonneg_right ?_ hε)
    calc |A| * s ^ (1 - δ / 2) ≤ |A| * s ^ (1 - δ') := mul_le_mul_of_nonneg_left hgain
          (abs_nonneg _)
      _ ≤ (|A| + 2 * |B|) * s ^ (1 - δ') := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (by positivity)) (by positivity)
  · -- above the split
    have hBv : ∀ v : ℝ, u₀ ≤ v → ‖(v : ℂ) * g v - (L s - L s')‖ ≤ |B| * ε := by
      intro v hv
      have hv0 : 0 < v := hu₀0.trans_le hv
      have h1 : s ^ p * v ^ (-(1 / 2) : ℝ) ≤ 1 := by
        have h2 : v ^ (-(1 / 2) : ℝ) ≤ u₀ ^ (-(1 / 2) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hu₀0 hv (by norm_num)
        have h3 : s ^ p * u₀ ^ (-(1 / 2) : ℝ) = 1 := by
          rw [hu₀, ← Real.rpow_mul hs0.le, ← Real.rpow_add hs0]
          ring_nf
          exact Real.rpow_zero s
        calc s ^ p * v ^ (-(1 / 2) : ℝ) ≤ s ^ p * u₀ ^ (-(1 / 2) : ℝ) :=
              mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hs0.le _)
          _ = 1 := h3
      calc ‖(v : ℂ) * g v - (L s - L s')‖ ≤ B * s ^ p * v ^ (-(1 / 2) : ℝ) * ε :=
            hB s s' hs' hss hs2 v (hsu₀.trans hv)
        _ ≤ |B| * (s ^ p * v ^ (-(1 / 2) : ℝ)) * ε := by
            rw [mul_assoc B]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
              (mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg hv0.le _))) hε
        _ ≤ |B| * 1 * ε := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) hε
        _ = |B| * ε := by ring
    have hL : ‖L s - L s'‖ ≤ |A| * s ^ (1 - δ / 2) * ε + |B| * ε := by
      have h1 := below u₀ hsu₀ le_rfl
      have h2 := hBv u₀ le_rfl
      have e : L s - L s' = (u₀ : ℂ) * g u₀ - ((u₀ : ℂ) * g u₀ - (L s - L s')) := by ring
      rw [e]
      exact (norm_sub_le _ _).trans (add_le_add h1 h2)
    have hgu := hBv u hu.le
    have hε1 : |B| * ε ≤ |B| * s ^ (1 - δ') * ε :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (abs_nonneg _) hone) hε
    have hε2 : |A| * s ^ (1 - δ / 2) * ε ≤ |A| * s ^ (1 - δ') * ε :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgain (abs_nonneg _)) hε
    calc ‖(u : ℂ) * g u‖ ≤ ‖(u : ℂ) * g u - (L s - L s')‖ + ‖L s - L s'‖ := by
          have h := norm_add_le ((u : ℂ) * g u - (L s - L s')) (L s - L s')
          rwa [sub_add_cancel] at h
      _ ≤ |B| * ε + (|A| * s ^ (1 - δ / 2) * ε + |B| * ε) := add_le_add hgu hL
      _ ≤ (|A| + 2 * |B|) * s ^ (1 - δ') * ε := by nlinarith

/-- **The per-class increment rate from (A) with a power loss and (B).** -/
theorem faceRateInc_of_pow_rate {G : ℝ → (Fin 4 → ℝ) → ℂ} (hA : FaceRateIncAPow G)
    (hB : FaceRateIncB G) : FaceRateIncRay G :=
  faceRateInc_of_size_rate (faceRateIncA_of_pow_rate hA hB) hB

/-! ### Linear combinations -/

namespace FaceRateIncAPow

variable {G H : ℝ → (Fin 4 → ℝ) → ℂ}

theorem zero : FaceRateIncAPow fun _ _ => 0 :=
  ⟨1, one_pos, fun _ _ => ⟨0, fun _ _ _ _ _ u _ => by simp⟩⟩

theorem add (hG : FaceRateIncAPow G) (hH : FaceRateIncAPow H) :
    FaceRateIncAPow fun u k => G u k + H u k := by
  obtain ⟨δ, hδ, hG⟩ := hG
  obtain ⟨δ', hδ', hH⟩ := hH
  refine ⟨min δ δ', lt_min hδ hδ', fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := hG a ha
  obtain ⟨A', hA'⟩ := hH a ha
  refine ⟨|A| + |A'|, fun s s' hs' hss hs2 u hsu => ?_⟩
  have hs : 1 ≤ s := hs'.trans hss
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := hs0.trans_le hsu
  have hε : 0 ≤ (s - s') / s' := div_nonneg (by linarith) (by linarith)
  have hua : 0 ≤ u ^ a := Real.rpow_nonneg hu0.le _
  have m1 : s ^ (1 - δ) ≤ s ^ (1 - min δ δ') :=
    faceIdRay_rpow_mono hs (by linarith [min_le_left δ δ'])
  have m2 : s ^ (1 - δ') ≤ s ^ (1 - min δ δ') :=
    faceIdRay_rpow_mono hs (by linarith [min_le_right δ δ'])
  have b : ∀ {C δ₀ : ℝ}, s ^ (1 - δ₀) ≤ s ^ (1 - min δ δ') →
      C * s ^ (1 - δ₀) * u ^ a * ((s - s') / s') ≤
        |C| * s ^ (1 - min δ δ') * u ^ a * ((s - s') / s') := fun {C δ₀} hm =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) hm
      (Real.rpow_nonneg hs0.le _) (abs_nonneg _)) hua) hε
  have e : (u : ℂ) * (G u (tiltVec (Real.sqrt s) s) + H u (tiltVec (Real.sqrt s) s) -
      (G u (tiltVec (Real.sqrt s') s') + H u (tiltVec (Real.sqrt s') s'))) =
      (u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s')) +
        (u : ℂ) * (H u (tiltVec (Real.sqrt s) s) - H u (tiltVec (Real.sqrt s') s')) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ((add_le_add ((hA s s' hs' hss hs2 u hsu).trans (b m1))
    ((hA' s s' hs' hss hs2 u hsu).trans (b m2))).trans (le_of_eq ?_))
  ring

theorem const_mul (hG : FaceRateIncAPow G) (r : ℂ) :
    FaceRateIncAPow fun u k => r * G u k := by
  obtain ⟨δ, hδ, hG⟩ := hG
  refine ⟨δ, hδ, fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := hG a ha
  refine ⟨‖r‖ * A, fun s s' hs' hss hs2 u hsu => ?_⟩
  have e : (u : ℂ) * (r * G u (tiltVec (Real.sqrt s) s) - r * G u (tiltVec (Real.sqrt s') s')) =
      r * ((u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s'))) := by
    ring
  rw [e, norm_mul]
  calc ‖r‖ * ‖(u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s'))‖
      ≤ ‖r‖ * (A * s ^ (1 - δ) * u ^ a * ((s - s') / s')) :=
        mul_le_mul_of_nonneg_left (hA s s' hs' hss hs2 u hsu) (norm_nonneg _)
    _ = _ := by ring

theorem sum {ι : Type*} (t : Finset ι) {G : ι → ℝ → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ t, FaceRateIncAPow (G i)) : FaceRateIncAPow fun u k => ∑ i ∈ t, G i u k := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (zero : FaceRateIncAPow fun _ _ => 0)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem congr (hG : FaceRateIncAPow G)
    (e : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
      G u (tiltVec (Real.sqrt s) s) = H u (tiltVec (Real.sqrt s) s)) :
    FaceRateIncAPow H := by
  obtain ⟨δ, hδ, hG⟩ := hG
  refine ⟨δ, hδ, fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := hG a ha
  refine ⟨A, fun s s' hs' hss hs2 u hsu => ?_⟩
  rw [← e s (hs'.trans hss) u hsu, ← e s' hs' u (hss.trans hsu)]
  exact hA s s' hs' hss hs2 u hsu

end FaceRateIncAPow

namespace FaceRateIncB

variable {G H : ℝ → (Fin 4 → ℝ) → ℂ}

theorem zero : FaceRateIncB fun _ _ => 0 :=
  ⟨0, 1, le_rfl, fun _ => 0, fun _ _ _ _ _ u _ => by simp⟩

theorem add (hG : FaceRateIncB G) (hH : FaceRateIncB H) :
    FaceRateIncB fun u k => G u k + H u k := by
  obtain ⟨B, p, hp, L, hL⟩ := hG
  obtain ⟨B', p', -, L', hL'⟩ := hH
  refine ⟨|B| + |B'|, max p p', hp.trans (le_max_left _ _), fun s => L s + L' s,
    fun s s' hs' hss hs2 u hsu => ?_⟩
  have hs : 1 ≤ s := hs'.trans hss
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := hs0.trans_le hsu
  have hε : 0 ≤ (s - s') / s' := div_nonneg (by linarith) (by linarith)
  have hue : 0 ≤ u ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hu0.le _
  have b : ∀ {C p₀ : ℝ}, p₀ ≤ max p p' →
      C * s ^ p₀ * u ^ (-(1 / 2) : ℝ) * ((s - s') / s') ≤
        |C| * s ^ max p p' * u ^ (-(1 / 2) : ℝ) * ((s - s') / s') := fun {C p₀} hm =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _)
      (faceIdRay_rpow_mono hs hm) (Real.rpow_nonneg hs0.le _) (abs_nonneg _)) hue) hε
  have e : (u : ℂ) * (G u (tiltVec (Real.sqrt s) s) + H u (tiltVec (Real.sqrt s) s) -
      (G u (tiltVec (Real.sqrt s') s') + H u (tiltVec (Real.sqrt s') s'))) -
      (L s + L' s - (L s' + L' s')) =
      ((u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s')) -
        (L s - L s')) +
      ((u : ℂ) * (H u (tiltVec (Real.sqrt s) s) - H u (tiltVec (Real.sqrt s') s')) -
        (L' s - L' s')) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ((add_le_add ((hL s s' hs' hss hs2 u hsu).trans
    (b (le_max_left _ _))) ((hL' s s' hs' hss hs2 u hsu).trans (b (le_max_right _ _)))).trans
    (le_of_eq ?_))
  ring

theorem const_mul (hG : FaceRateIncB G) (r : ℂ) :
    FaceRateIncB fun u k => r * G u k := by
  obtain ⟨B, p, hp, L, hL⟩ := hG
  refine ⟨‖r‖ * B, p, hp, fun s => r * L s, fun s s' hs' hss hs2 u hsu => ?_⟩
  have e : (u : ℂ) * (r * G u (tiltVec (Real.sqrt s) s) - r * G u (tiltVec (Real.sqrt s') s')) -
      (r * L s - r * L s') =
      r * ((u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s')) -
        (L s - L s')) := by ring
  rw [e, norm_mul]
  calc ‖r‖ * ‖(u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s')) -
        (L s - L s')‖
      ≤ ‖r‖ * (B * s ^ p * u ^ (-(1 / 2) : ℝ) * ((s - s') / s')) :=
        mul_le_mul_of_nonneg_left (hL s s' hs' hss hs2 u hsu) (norm_nonneg _)
    _ = _ := by ring

theorem sum {ι : Type*} (t : Finset ι) {G : ι → ℝ → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ t, FaceRateIncB (G i)) : FaceRateIncB fun u k => ∑ i ∈ t, G i u k := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (zero : FaceRateIncB fun _ _ => 0)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem congr (hG : FaceRateIncB G)
    (e : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
      G u (tiltVec (Real.sqrt s) s) = H u (tiltVec (Real.sqrt s) s)) :
    FaceRateIncB H := by
  obtain ⟨B, p, hp, L, hL⟩ := hG
  refine ⟨B, p, hp, L, fun s s' hs' hss hs2 u hsu => ?_⟩
  rw [← e s (hs'.trans hss) u hsu, ← e s' hs' u (hss.trans hsu)]
  exact hL s s' hs' hss hs2 u hsu

end FaceRateIncB

end QED.GradedProof.RPi4

end
