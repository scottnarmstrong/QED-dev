/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajGlue

/-!
# (R-Π₄) step L10: the scale-Lipschitz bound of the photon limit from increments on one scale

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10, input
`QED.GradedProof.RPi4.MajLimLip4`. Write `Π = asmPolLim (decCfg 1 4)` and `w(s) = 1 + log(1 + s)`.
The bound `‖Π(s) - Π(s')‖ ≤ K w(s) (s - s')/s'` (`0 < s' ≤ s`) splits by the size of `s/s'`:

* `s ≥ 2s'`: then `(s - s')/s' ≥ 1`, and the value bound `‖Π‖ ≤ K w` suffices; it is the limit of
  the value bound `MajRayVal` uniform in the photon pair;
* `s ≤ 2s'`, `s' ≥ 1`: increments on one scale, uniform in the photon pair (`MajRayInc`), pass to
  the limit;
* `s ≤ 2s'`, `s' < 1`: a Lipschitz bound on `[0, 2]`: near `0` (`DecLip0`) and on `[s₀, 2]` for
  every `s₀ > 0` (`MajLipMid4`).

* `MajRayInc Φ rep e`: `‖Q(a, b; s) - Q(a, b; s')‖ ≤ K w(s) (s - s')/s'` for
  `1 ≤ s' ≤ s ≤ 2s'`, uniformly for light `a` and heavy `b`;
* `MajLipMid4 e`: `Π` is Lipschitz on `[s₀, 2]` (pairs `s' ≤ s ≤ 2s'`) for every `s₀ > 0`;
* `majLip_of_parts`: the model-free case split;
* **`majLip_limLip4_of`**: `DecFaceGen`, `DecLip0 (decT₀ e 1 4)`, `MajRayVal`, `MajRayInc` (at
  `decCfg 1 4`) and `MajLipMid4` give `MajLimLip4`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

/-- **Increments on one scale at fixed fermion masses**, uniform in the photon pair:
`‖Q(a, b; s) - Q(a, b; s')‖ ≤ K w(s) (s - s')/s'` for `1 ≤ s' ≤ s ≤ 2s'`, `0 < a < δ`, `b > R`. -/
def MajRayInc {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)
    (e : ℝ) : Prop :=
  ∃ K δ R : ℝ, 0 < δ ∧ ∀ a b : ℝ, 0 < a → a < δ → R < b → ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s →
    s ≤ 2 * s' → ‖qPair Φ rep e a b s - qPair Φ rep e a b s'‖ ≤ K * majW s * ((s - s') / s')

/-- **The photon limit at `decCfg 1 4` is Lipschitz on `[s₀, 2]`** for every `s₀ > 0`, on pairs
`s' ≤ s ≤ 2s'`. -/
def MajLipMid4 (e : ℝ) : Prop :=
  ∀ s₀ : ℝ, 0 < s₀ → ∃ L : ℝ, ∀ s s' : ℝ, s₀ ≤ s' → s' ≤ s → s ≤ 2 → s ≤ 2 * s' →
    ‖asmPolLim (decCfg 1 4) (fun _ => 0) e s - asmPolLim (decCfg 1 4) (fun _ => 0) e s'‖ ≤
      L * (s - s')

/-- **The model-free case split**: a value bound `A w`, a Lipschitz bound near `0`, Lipschitz
bounds on `[s₀, 2]` and increments `K w(s) (s - s')/s'` on one scale for `s' ≥ 1` give the
scale-Lipschitz bound for all `0 < s' ≤ s`. -/
theorem majLip_of_parts {f : ℝ → ℂ} {A : ℝ} (hV : ∀ s : ℝ, 0 ≤ s → ‖f s‖ ≤ A * majW s)
    (hZ : ∃ δ L : ℝ, 0 < δ ∧ ∀ t t' : ℝ, |t| ≤ δ → |t'| ≤ δ → ‖f t - f t'‖ ≤ L * |t - t'|)
    (hM : ∀ s₀ : ℝ, 0 < s₀ → ∃ L : ℝ, ∀ s s' : ℝ, s₀ ≤ s' → s' ≤ s → s ≤ 2 → s ≤ 2 * s' →
      ‖f s - f s'‖ ≤ L * (s - s'))
    (hI : ∃ K : ℝ, ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' →
      ‖f s - f s'‖ ≤ K * majW s * ((s - s') / s')) :
    ∃ K : ℝ, ∀ s s' : ℝ, 0 < s' → s' ≤ s → ‖f s - f s'‖ ≤ K * majW s * ((s - s') / s') := by
  obtain ⟨δ, L₁, hδ, hZ⟩ := hZ
  obtain ⟨L₂, hM⟩ := hM (δ / 2) (by positivity)
  obtain ⟨K₃, hI⟩ := hI
  refine ⟨2 * |A| + |L₁| + |L₂| + |K₃|, fun s s' hs' hss => ?_⟩
  have hs0 : 0 ≤ s := hs'.le.trans hss
  have hw := maj_one_le_majW hs0
  have hq : 0 ≤ (s - s') / s' := div_nonneg (by linarith) hs'.le
  have hwq : 0 ≤ majW s * ((s - s') / s') := mul_nonneg (by linarith) hq
  -- the four constants are each at most the sum
  have hK : ∀ X : ℝ, X = 2 * |A| ∨ X = |L₁| ∨ X = |L₂| ∨ X = |K₃| →
      X * majW s * ((s - s') / s') ≤ (2 * |A| + |L₁| + |L₂| + |K₃|) * majW s * ((s - s') / s') := by
    intro X hX
    rw [mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hwq
    rcases hX with rfl | rfl | rfl | rfl <;>
      linarith [abs_nonneg A, abs_nonneg L₁, abs_nonneg L₂, abs_nonneg K₃]
  -- `(s - s') ≤ w(s) (s - s')/s'` when `s' ≤ 1`
  have hsmall : s' ≤ 1 → s - s' ≤ majW s * ((s - s') / s') := by
    intro h1
    have : s - s' ≤ (s - s') / s' := by
      rw [le_div_iff₀ hs']
      nlinarith
    exact this.trans (le_mul_of_one_le_left hq hw)
  rcases le_or_gt (2 * s') s with h2 | h2
  · -- far apart: the value bound
    have hq1 : 1 ≤ (s - s') / s' := by rw [le_div_iff₀ hs']; linarith
    have h1 : ‖f s‖ ≤ |A| * majW s :=
      (hV s hs0).trans (mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith))
    have h2' : ‖f s'‖ ≤ |A| * majW s :=
      (hV s' hs'.le).trans ((mul_le_mul_of_nonneg_right (le_abs_self A)
        (by linarith [maj_one_le_majW hs'.le])).trans
        (mul_le_mul_of_nonneg_left (majW_mono hs'.le hss) (abs_nonneg A)))
    refine (norm_sub_le _ _).trans ?_
    refine le_trans ?_ (hK _ (Or.inl rfl))
    have : 2 * |A| * majW s ≤ 2 * |A| * majW s * ((s - s') / s') :=
      le_mul_of_one_le_right (by positivity) hq1
    linarith
  · rcases le_or_gt 1 s' with h1 | h1
    · -- one scale, `s' ≥ 1`
      refine (hI s s' h1 hss h2.le).trans (le_trans ?_ (hK _ (Or.inr (Or.inr (Or.inr rfl)))))
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
        (by linarith)) hq
    · rcases le_or_gt s δ with hsδ | hsδ
      · -- near `0`
        have h := hZ s s' (by rw [abs_of_nonneg hs0]; exact hsδ)
          (by rw [abs_of_pos hs']; linarith)
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - s')] at h
        refine h.trans (le_trans ?_ (hK _ (Or.inr (Or.inl rfl))))
        rw [mul_assoc]
        exact mul_le_mul (le_abs_self _) (hsmall h1.le) (by linarith) (abs_nonneg _)
      · -- the middle range `[δ/2, 2]`
        have h := hM s s' (by linarith) hss (by linarith) h2.le
        refine h.trans (le_trans ?_ (hK _ (Or.inr (Or.inr (Or.inl rfl)))))
        rw [mul_assoc]
        exact mul_le_mul (le_abs_self _) (hsmall h1.le) (by linarith) (abs_nonneg _)

/-- **(L10) `MajLimLip4` from increments on one scale**: the value bound and the increments
uniform in the photon pair pass to the photon limit; near `0` and on `[s₀, 2]` the limit is
Lipschitz. -/
theorem majLip_limLip4_of (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e)
    (hZ : DecLip0 (decT₀ P.e 1 4)) (hV : MajRayVal (decCfg 1 4) (fun _ => 0) P.e)
    (hI : MajRayInc (decCfg 1 4) (fun _ => 0) P.e) (hM : MajLipMid4 P.e) : MajLimLip4 P.e := by
  obtain ⟨K₁, δ₁, R₁, hδ₁, hK₁⟩ := hV
  obtain ⟨K₂, δ₂, R₂, hδ₂, hK₂⟩ := hI
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero (by norm_num : (0 : ℝ) ≤ 4)
  have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
    fun _ => rfl
  set Q := qPair (decCfg 1 4) (fun _ => 0) P.e with hQ
  set f := asmPolLim (decCfg 1 4) (fun _ => 0) P.e with hf
  have hlim : ∀ s : ℝ, 0 ≤ s → Tendsto (fun Λ : ℝ => Q Λ⁻¹ Λ s - Q Λ⁻¹ Λ 0) atTop (𝓝 (f s)) :=
    fun s hs => dec_tendsto_asmPolLim (Φ := decCfg 1 4) (rep := fun _ => 0) one_pos hmass hrep P
      he hpv.1 hpv.2 hF (by linarith)
  have hev : ∀ᶠ Λ : ℝ in atTop, 0 < Λ⁻¹ ∧ Λ⁻¹ < min δ₁ δ₂ ∧ max R₁ R₂ < Λ := by
    have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    filter_upwards [eventually_gt_atTop (max R₁ R₂), eventually_gt_atTop (min δ₁ δ₂)⁻¹]
      with Λ hR hΛ
    have hΛ0 : 0 < Λ := (inv_pos.2 hδ).trans hΛ
    exact ⟨inv_pos.2 hΛ0, by rwa [inv_lt_comm₀ hΛ0 hδ], hR⟩
  -- the value bound of the limit
  have hval : ∀ s : ℝ, 0 ≤ s → ‖f s‖ ≤ K₁ * majW s := fun s hs => by
    refine le_of_tendsto (hlim s hs).norm ?_
    filter_upwards [hev] with Λ hΛ
    exact hK₁ _ _ hΛ.1 (hΛ.2.1.trans_le (min_le_left _ _))
      ((le_max_left _ _).trans_lt hΛ.2.2) s hs
  -- the increments of the limit
  have hinc : ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' →
      ‖f s - f s'‖ ≤ K₂ * majW s * ((s - s') / s') := by
    intro s s' hs' hss hs2
    have ht := ((hlim s (by linarith)).sub (hlim s' (by linarith))).norm
    refine le_of_tendsto ht ?_
    filter_upwards [hev] with Λ hΛ
    have e : Q Λ⁻¹ Λ s - Q Λ⁻¹ Λ 0 - (Q Λ⁻¹ Λ s' - Q Λ⁻¹ Λ 0) = Q Λ⁻¹ Λ s - Q Λ⁻¹ Λ s' := by
      ring
    rw [e]
    exact hK₂ _ _ hΛ.1 (hΛ.2.1.trans_le (min_le_right _ _))
      ((le_max_right _ _).trans_lt hΛ.2.2) s s' hs' hss hs2
  -- Lipschitz near `0`: `f = e⁴ decT₀`
  have hZ' : ∃ δ L : ℝ, 0 < δ ∧ ∀ t t' : ℝ, |t| ≤ δ → |t'| ≤ δ → ‖f t - f t'‖ ≤ L * |t - t'| := by
    obtain ⟨δ, L, hδ, hL⟩ := hZ
    have he' : (P.e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 he
    refine ⟨δ, ‖(P.e : ℂ) ^ 4‖ * L, hδ, fun t t' ht ht' => ?_⟩
    have e : f t - f t' = (P.e : ℂ) ^ 4 * (decT₀ P.e 1 4 t - decT₀ P.e 1 4 t') := by
      simp only [hf, decT₀]
      field_simp
    rw [e, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hL t t' ht ht') (norm_nonneg _)
  obtain ⟨K, hK⟩ := majLip_of_parts hval hZ' hM ⟨K₂, hinc⟩
  exact ⟨K, hK⟩

end QED.GradedProof.RPi4

end
