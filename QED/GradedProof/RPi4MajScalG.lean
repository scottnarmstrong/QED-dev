/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecWeak
public import QED.GradedProof.RPi4MajLim
public import QED.GradedProof.RPi4MajProf

/-!
# (R-Π₄) step L10: global bounds on the scaling profiles from one fixed configuration

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10, limit part.
The scaling form of the decoupling (step L9) is built from the one-loop functional
`D₁ = decD₀ e 1` (`D₁ = decR φ`) and the per-flavour function `T₁ = decT₀ e 1`
(`T₁ - κ decLφ φ = decR G`, `κ = -3/(16π²)`). At the configuration `x = 4` (flavours
`1, √2, 2`) these identities are halving identities for the profiles `φ` and `G`, so global
bounds on the two functions of one variable `D₁(4, ·)`, `T₁(4, ·)` give global bounds on the
profiles (`maj_profile_norm_le`, `maj_profile_norm_sub_le`), hence `MajScalGlob`:

* `MajGrowD e`: `D₁(4, ·)` is bounded, and bounded on the scale of `t`, for `t ≥ 0`;
* `MajGrowT e`: `T₁(4, ·)` is `O(w(t))`, also on the scale of `t`, `w(t) = 1 + log(1 + t)`;
* `maj_scalGlob_of`: **`DecFaceGen → DecContD → DecLipD48 → DecContT → DecLipT48 → MajGrowT →
  MajGrowD → MajScalGlob`** (the first five are the inputs of the decoupling, step L9);
* `maj_limBound_of_grow`: the same hypotheses give **`MajLimBound`**.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)

namespace QED.GradedProof.RPi4

/-- **(L10 input, two loops) growth at the configuration `x = 4`**: `T₁(4, t)` is `O(w(t))`
for `t ≥ 0`, and so are its increments on the scale of `t`. -/
def MajGrowT (e : ℝ) : Prop :=
  ∃ A : ℝ, ∀ t : ℝ, 0 ≤ t → ‖decT₀ e 1 4 t‖ ≤ A * majW t ∧
    ∀ t' : ℝ, 0 < t' → t' ≤ t → ‖decT₀ e 1 4 t - decT₀ e 1 4 t'‖ ≤ A * majW t * ((t - t') / t')

/-- **(L10 input, one loop) boundedness at the configuration `x = 4`**: `D₁(4, t)` is bounded
for `t ≥ 0`, and so are its increments on the scale of `t`. -/
def MajGrowD (e : ℝ) : Prop :=
  ∃ A : ℝ, ∀ t : ℝ, 0 ≤ t → ‖decD₀ e 1 4 t‖ ≤ A ∧
    ∀ t' : ℝ, 0 < t' → t' ≤ t → ‖decD₀ e 1 4 t - decD₀ e 1 4 t'‖ ≤ A * ((t - t') / t')

/-- A scale-Lipschitz bound in the form used by `maj_profile_norm_sub_le`. -/
theorem maj_ratio_of {f : ℝ → ℂ} {ω : ℝ → ℝ} {A : ℝ}
    (h : ∀ t, 0 ≤ t → ∀ t', 0 < t' → t' ≤ t → ‖f t - f t'‖ ≤ A * ω t * ((t - t') / t'))
    (hnn : ∀ t, 0 ≤ t → 0 ≤ A * ω t) :
    ∀ s r, 0 ≤ s → 0 < r → r ≤ 1 → ‖f s - f (r * s)‖ ≤ A * ω s * ((1 - r) / r) := by
  intro s r hs hr hr1
  rcases hs.eq_or_lt with rfl | hs0
  · simp only [mul_zero, sub_self, norm_zero]
    exact mul_nonneg (hnn 0 le_rfl) (div_nonneg (by linarith) hr.le)
  · have := h s hs0.le (r * s) (by positivity) (by nlinarith)
    rwa [show (s - r * s) / (r * s) = (1 - r) / r by field_simp] at this

/-- The anomaly term at `x = 4` from bounds on `φ`. -/
theorem maj_norm_decLφ_four_le {φ : ℝ → ℂ} {K s : ℝ} (hs : 0 ≤ s)
    (hφ : ∀ τ, 0 ≤ τ → ‖φ τ‖ ≤ K * majW τ) (hK : 0 ≤ K) :
    ‖decLφ φ 4 s‖ ≤ (Real.log 4 + 3 * Real.log 2) * K * majW s := by
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have e1 : ‖φ (s / 4)‖ ≤ K * majW s :=
    (hφ _ (by positivity)).trans (mul_le_mul_of_nonneg_left (majW_mono (by positivity)
      (by linarith)) hK)
  have e2 : ‖φ (s / 2)‖ ≤ K * majW s :=
    (hφ _ (by positivity)).trans (mul_le_mul_of_nonneg_left (majW_mono (by positivity)
      (by linarith)) hK)
  simp only [decLφ]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg h4, Real.norm_of_nonneg h2,
    show ‖(1 - 4 : ℝ)‖ = 3 by norm_num]
  nlinarith [mul_le_mul_of_nonneg_left e1 h4, mul_le_mul_of_nonneg_left e2 h2]

/-- The anomaly term at `x = 4`, on the scale of `s`. -/
theorem maj_norm_decLφ_four_sub_le {φ : ℝ → ℂ} {K s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r)
    (hr1 : r ≤ 1)
    (hφ : ∀ τ, 0 ≤ τ → ‖φ τ - φ (r * τ)‖ ≤ K * majW τ * ((1 - r) / r)) (hK : 0 ≤ K) :
    ‖decLφ φ 4 s - decLφ φ 4 (r * s)‖ ≤
      (Real.log 4 + 3 * Real.log 2) * K * majW s * ((1 - r) / r) := by
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hq : 0 ≤ (1 - r) / r := div_nonneg (by linarith) hr.le
  have e1 : ‖φ (s / 4) - φ (r * (s / 4))‖ ≤ K * majW s * ((1 - r) / r) :=
    (hφ _ (by positivity)).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (majW_mono (by positivity) (by linarith)) hK) hq)
  have e2 : ‖φ (s / 2) - φ (r * (s / 2))‖ ≤ K * majW s * ((1 - r) / r) :=
    (hφ _ (by positivity)).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (majW_mono (by positivity) (by linarith)) hK) hq)
  have e : decLφ φ 4 s - decLφ φ 4 (r * s) =
      (Real.log 4 : ℂ) * (φ (s / 4) - φ (r * (s / 4))) +
        ((1 - 4 : ℝ) : ℂ) * (Real.log 2 : ℂ) * (φ (s / 2) - φ (r * (s / 2))) := by
    simp only [decLφ]
    rw [show r * s / 4 = r * (s / 4) by ring, show r * s / 2 = r * (s / 2) by ring]
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg h4, Real.norm_of_nonneg h2,
    show ‖(1 - 4 : ℝ)‖ = 3 by norm_num]
  nlinarith [mul_le_mul_of_nonneg_left e1 h4, mul_le_mul_of_nonneg_left e2 h2]

/-- The halving identity of a profile at `x = 4`. -/
theorem maj_halving_decR {g : ℝ → ℂ} (s : ℝ) :
    decR g 4 s = 2 * (g s - g (s / 2)) - (g (s / 2) - g (s / 2 / 2)) := by
  simp only [decR]
  rw [show s / 2 / 2 = s / 4 by ring]
  push_cast
  ring

/-- The scaling form of `decT₀` (with its affine part) from the scaling `DecScaleT₀` and the
representation at `μ = 1`. -/
theorem maj_rep_of {e : ℝ} {G φ : ℝ → ℂ} {κ : ℂ} (hS : DecScaleT₀ e)
    (hT : ∀ x s : ℝ, 0 < x → -(4 * min 1 x) < s →
      decT₀ e 1 x s = decR G x s + κ * decLφ φ x s) :
    ∀ μ x s : ℝ, 0 < μ → μ ^ 2 ≤ x → -(4 * μ ^ 2) < s →
      decT₀ e μ x s = decT G φ κ μ x s +
        ((-2 * G (s / μ ^ 2) + G (s / μ ^ 2 / 2) + κ * (Real.log 2 : ℂ) * φ (s / μ ^ 2 / 2)) +
          (G (s / μ ^ 2) - G (s / μ ^ 2 / 2) - κ * (Real.log 2 : ℂ) * φ (s / μ ^ 2 / 2)) /
            ((μ ^ 2 : ℝ) : ℂ) * x) := by
  intro μ x s hμ hx hs
  have hμ2 : 0 < μ ^ 2 := pow_pos hμ 2
  have hy : 1 ≤ x / μ ^ 2 := by rwa [le_div_iff₀ hμ2, one_mul]
  have ht : -(4 * min 1 (x / μ ^ 2)) < s / μ ^ 2 := by
    rw [min_eq_left hy, lt_div_iff₀ hμ2]
    linarith
  rw [hS μ x s hμ hx hs, hT _ _ (zero_lt_one.trans_le hy) ht]
  have hx0 : x ≠ 0 := (hμ2.trans_le hx).ne'
  have hμc : ((μ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hμ2.ne'
  simp only [decR, decLφ, decT]
  rw [show s / μ ^ 2 / (x / μ ^ 2) = s / x by field_simp]
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  push_cast
  field_simp
  ring

/-- **(L10, limit part) global bounds on the scaling profiles** from the inputs of the
decoupling and the growth at the configuration `x = 4`. -/
theorem maj_scalGlob_of (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e)
    (hDc : DecContD P.e) (hD48 : DecLipD48 P.e) (hTc : DecContT P.e) (hT48 : DecLipT48 P.e)
    (hGT : MajGrowT P.e) (hGD : MajGrowD P.e) : MajScalGlob P.e := by
  set κ : ℂ := ((-3 / (16 * Real.pi ^ 2) : ℝ) : ℂ) with hκ
  have hS := dec_scaleT₀_of_faceGen P he hF
  have hA := dec_anomT₀ P he hF
  have hD := dec_dil_decD₀ P he
  -- the one-loop profile (as in `dec_exists_scal_anom_weak`)
  obtain ⟨δ₁, L₁, hδ₁, hL₁, h4, h8⟩ := hD48.1.common hD48.2
  obtain ⟨φ, hφ0, hφl, hDφ⟩ := dec_exists_scal hD (fun x _ => decD₀_zero P.e 1 x) hDc hδ₁ h4 h8
  have hφL : DecLip0 φ := ⟨δ₁, 8 * L₁, hδ₁, hφl⟩
  -- the anomaly-free two-loop functional
  set T' : ℝ → ℝ → ℂ := fun x s => decT₀ P.e 1 x s - κ * decLφ φ x s with hT'
  have hL' : ∀ x, 1 ≤ x → DecLip0 fun s => decLφ φ x s := fun x hx =>
    ((hφL.comp_div hx).const_mul _).add ((hφL.comp_div one_le_two).const_mul _)
  have hT'0 : ∀ x, 0 < x → T' x 0 = 0 := fun x hx => by
    simp [hT', decLφ, decT₀_zero, hφ0]
  have hT'c : ∀ x, 0 < x → Tendsto (T' x) (𝓝 0) (𝓝 0) := fun x hx => by
    have := (hTc x hx).sub ((dec_tendsto_decLφ (hφL.tendsto hφ0) x).const_mul κ)
    simpa only [mul_zero, sub_zero] using this
  have hT'4 : DecLip0 (T' 4) := hT48.1.sub ((hL' 4 (by norm_num)).const_mul κ)
  have hT'8 : DecLip0 (T' 8) := hT48.2.sub ((hL' 8 (by norm_num)).const_mul κ)
  have hT'dil : DecDil T' := by
    intro Λ x s hΛ hx hs hΛs
    have h := hA Λ x s hΛ hx hs hΛs
    have hl := decLφ_dil φ hΛ hx s
    simp only [hT']
    rw [hDφ x s hx hs] at h
    linear_combination h - κ * hl
  obtain ⟨δ₂, L₂, hδ₂, hL₂, h4', h8'⟩ := hT'4.common hT'8
  obtain ⟨G, hG0, hGl, hTG⟩ := dec_exists_scal hT'dil hT'0 hT'c hδ₂ h4' h8'
  -- growth of `φ`
  obtain ⟨AD, hAD⟩ := hGD
  have hAD0 : 0 ≤ AD := (norm_nonneg _).trans (hAD 0 le_rfl).1
  have hφv : ∀ s, 0 ≤ s → 2 * (φ s - φ (s / 2)) - (φ (s / 2) - φ (s / 2 / 2)) =
      decD₀ P.e 1 4 s := fun s hs => by
    rw [hDφ 4 s (by norm_num) (by norm_num; linarith), maj_halving_decR]
  have hω1 : ∀ s t : ℝ, 0 ≤ s → s ≤ t → (fun _ : ℝ => (1 : ℝ)) s ≤ (fun _ => 1) t :=
    fun _ _ _ _ => le_rfl
  have hAr := maj_ratio_of (f := decD₀ P.e 1 4) (ω := fun _ => 1) (A := AD)
    (fun t ht t' ht' htt => by simpa using (hAD t ht).2 t' ht' htt) (fun _ _ => by simpa)
  set Kφ : ℝ := 8 * L₁ * δ₁ + majC δ₁ * AD with hKφ
  have hKφ0 : 0 ≤ Kφ := by have := majC_nonneg hδ₁; positivity
  have hφn : ∀ τ, 0 ≤ τ → ‖φ τ‖ ≤ Kφ * majW τ := fun τ hτ => by
    simpa using maj_profile_norm_le (ω := fun _ => 1) (A := AD) hδ₁ (by positivity) hφ0 hφl
      hφv hω1 (fun _ _ => le_rfl) hAD0 (fun s hs => by simpa using (hAD s hs).1) hτ
  have hφd : ∀ τ r, 0 ≤ τ → 0 < r → r ≤ 1 →
      ‖φ τ - φ (r * τ)‖ ≤ Kφ * majW τ * ((1 - r) / r) := fun τ r hτ hr hr1 => by
    simpa using maj_profile_norm_sub_le (ω := fun _ => 1) (A := AD) hδ₁ (by positivity) hφl
      hφv hω1 (fun _ _ => le_rfl) hAD0 hAr hτ hr hr1
  -- growth of `G`
  obtain ⟨AT, hAT⟩ := hGT
  have hAT0 : 0 ≤ AT := by
    have := (norm_nonneg _).trans (hAT 0 le_rfl).1
    simpa [majW] using this
  set c₄ : ℝ := Real.log 4 + 3 * Real.log 2 with hc₄
  have hc₄0 : 0 ≤ c₄ := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  set A' : ℝ := AT + ‖κ‖ * (c₄ * Kφ) with hA'
  have hA'0 : 0 ≤ A' := by positivity
  have hGv : ∀ s, 0 ≤ s → 2 * (G s - G (s / 2)) - (G (s / 2) - G (s / 2 / 2)) = T' 4 s :=
    fun s hs => by rw [hTG 4 s (by norm_num) (by norm_num; linarith), maj_halving_decR]
  have hv : ∀ s, 0 ≤ s → ‖T' 4 s‖ ≤ A' * majW s := fun s hs => by
    have e1 := (hAT s hs).1
    have e2 := maj_norm_decLφ_four_le hs hφn hKφ0
    simp only [hT']
    calc _ ≤ ‖decT₀ P.e 1 4 s‖ + ‖κ‖ * ‖decLφ φ 4 s‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ AT * majW s + ‖κ‖ * (c₄ * Kφ * majW s) := by gcongr
      _ = _ := by ring
  have hvr : ∀ s r, 0 ≤ s → 0 < r → r ≤ 1 →
      ‖T' 4 s - T' 4 (r * s)‖ ≤ A' * majW s * ((1 - r) / r) := fun s r hs hr hr1 => by
    have e1 := maj_ratio_of (f := decT₀ P.e 1 4) (ω := majW) (A := AT)
      (fun t ht t' ht' htt => (hAT t ht).2 t' ht' htt)
      (fun t ht => mul_nonneg hAT0 (majW_pos ht).le) s r hs hr hr1
    have e2 := maj_norm_decLφ_four_sub_le hs hr hr1 (fun τ hτ => hφd τ r hτ hr hr1) hKφ0
    have e : T' 4 s - T' 4 (r * s) = (decT₀ P.e 1 4 s - decT₀ P.e 1 4 (r * s)) -
        κ * (decLφ φ 4 s - decLφ φ 4 (r * s)) := by
      simp only [hT']
      ring
    rw [e]
    calc _ ≤ ‖decT₀ P.e 1 4 s - decT₀ P.e 1 4 (r * s)‖ +
          ‖κ‖ * ‖decLφ φ 4 s - decLφ φ 4 (r * s)‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ AT * majW s * ((1 - r) / r) + ‖κ‖ * (c₄ * Kφ * majW s * ((1 - r) / r)) := by
          gcongr
      _ = _ := by ring
  set KG : ℝ := 8 * L₂ * δ₂ + majC δ₂ * A' with hKG
  have hKG0 : 0 ≤ KG := by have := majC_nonneg hδ₂; positivity
  have hmW : ∀ s t, 0 ≤ s → s ≤ t → majW s ≤ majW t := fun s t hs hst => majW_mono hs hst
  have hGn : ∀ τ, 0 ≤ τ → ‖G τ‖ ≤ KG * majW τ ^ 2 := fun τ hτ => by
    have := maj_profile_norm_le (ω := majW) (A := A') hδ₂ (by positivity) hG0 hGl hGv hmW
      (fun s hs => maj_one_le_majW hs) hA'0 hv hτ
    rw [sq, ← mul_assoc]
    exact this
  have hGd : ∀ τ r, 0 ≤ τ → 0 < r → r ≤ 1 →
      ‖G τ - G (r * τ)‖ ≤ KG * majW τ ^ 2 * ((1 - r) / r) := fun τ r hτ hr hr1 => by
    have := maj_profile_norm_sub_le (ω := majW) (A := A') hδ₂ (by positivity) hGl hGv hmW
      (fun s hs => maj_one_le_majW hs) hA'0 hvr hτ hr hr1
    rw [sq, ← mul_assoc]
    exact this
  -- assembly
  set Bφ : ℝ := 8 * L₁ + Kφ + Kφ / δ₁ with hBφ
  have hBφ0 : 0 ≤ Bφ := by positivity
  have hr' : ∀ τ τ' : ℝ, 0 < τ' → τ' ≤ τ →
      0 < τ' / τ ∧ τ' / τ ≤ 1 ∧ τ' / τ * τ = τ' ∧ (1 - τ' / τ) / (τ' / τ) = (τ - τ') / τ' := by
    intro τ τ' h0 h1
    have hτ : 0 < τ := h0.trans_le h1
    refine ⟨by positivity, (div_le_one hτ).2 h1, by field_simp, by field_simp⟩
  refine ⟨G, φ, κ, KG + Bφ,
    fun μ s => -2 * G (s / μ ^ 2) + G (s / μ ^ 2 / 2) +
      κ * (Real.log 2 : ℂ) * φ (s / μ ^ 2 / 2),
    fun μ s => (G (s / μ ^ 2) - G (s / μ ^ 2 / 2) - κ * (Real.log 2 : ℂ) * φ (s / μ ^ 2 / 2)) /
      ((μ ^ 2 : ℝ) : ℂ), hφ0, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    have hw := (majW_pos hτ).le
    exact (hGn τ hτ).trans (by nlinarith [sq_nonneg (majW τ)])
  · intro τ τ' h0 h1
    obtain ⟨hr0, hr1, hrτ, hq⟩ := hr' τ τ' h0 h1
    have := hGd τ _ (h0.le.trans h1) hr0 hr1
    rw [hrτ, hq] at this
    refine this.trans ?_
    have : 0 ≤ (τ - τ') / τ' := div_nonneg (by linarith) h0.le
    have := sq_nonneg (majW τ)
    nlinarith [mul_nonneg (mul_nonneg hBφ0 (sq_nonneg (majW τ))) ‹0 ≤ (τ - τ') / τ'›]
  · intro τ hτ
    have hmin : 0 ≤ min τ 1 * majW τ := mul_nonneg (le_min hτ zero_le_one) (majW_pos hτ).le
    have h := maj_le_min_form (q := ‖φ τ‖) (X := 1) hτ hδ₁ (by positivity : 0 ≤ 8 * L₁) hKφ0
      zero_le_one (by simpa using hφn τ hτ) (fun hτδ => by
        have h1 : |τ| ≤ δ₁ := by rw [abs_of_nonneg hτ]; exact hτδ
        have := hφl τ 0 h1 (by simpa using hδ₁.le)
        rw [hφ0, sub_zero, sub_zero, abs_of_nonneg hτ] at this
        simpa using this)
    rw [mul_one] at h
    refine h.trans ?_
    have : 0 ≤ KG * min τ 1 * majW τ :=
      mul_nonneg (mul_nonneg hKG0 (le_min hτ zero_le_one)) (majW_pos hτ).le
    have e : (KG + Bφ) * min τ 1 * majW τ = KG * min τ 1 * majW τ + Bφ * min τ 1 * majW τ := by
      ring
    rw [e]
    linarith
  · intro τ τ' h0 h1
    have hτ : 0 ≤ τ := h0.le.trans h1
    obtain ⟨hr0, hr1, hrτ, hq⟩ := hr' τ τ' h0 h1
    have hX : 0 ≤ (τ - τ') / τ' := div_nonneg (by linarith) h0.le
    have hd := hφd τ _ hτ hr0 hr1
    rw [hrτ, hq] at hd
    have h := maj_le_min_form (q := ‖φ τ - φ τ'‖) (X := (τ - τ') / τ') hτ hδ₁
      (by positivity : 0 ≤ 8 * L₁) hKφ0 hX hd (fun hτδ => by
        have h1' : |τ| ≤ δ₁ := by rw [abs_of_nonneg hτ]; exact hτδ
        have h2' : |τ'| ≤ δ₁ := by rw [abs_of_nonneg h0.le]; linarith
        have := hφl τ τ' h1' h2'
        rw [abs_of_nonneg (by linarith : 0 ≤ τ - τ')] at this
        refine this.trans ?_
        have e : 8 * L₁ * (τ - τ') = 8 * L₁ * ((τ - τ') / τ') * τ' := by field_simp
        rw [e]
        have h3 := mul_le_mul_of_nonneg_left h1
          (mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * L₁) hX)
        linarith)
    refine h.trans ?_
    have : 0 ≤ KG * min τ 1 * majW τ * ((τ - τ') / τ') :=
      mul_nonneg (mul_nonneg (mul_nonneg hKG0 (le_min hτ zero_le_one)) (majW_pos hτ).le) hX
    have e : (KG + Bφ) * min τ 1 * majW τ * ((τ - τ') / τ') =
        KG * min τ 1 * majW τ * ((τ - τ') / τ') + Bφ * min τ 1 * majW τ * ((τ - τ') / τ') := by
      ring
    rw [e]
    linarith
  · exact maj_rep_of hS fun x s hx hs => by
      have := hTG x s hx hs
      simp only [hT'] at this
      linear_combination this

section Frozen

variable {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)

/-- **(L10, limit part) `MajLimBound` from the inputs of the decoupling and the growth at the
configuration `x = 4`.** -/
theorem maj_limBound_of_grow (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hF : DecFaceGen P₀.e) (hDc : DecContD P₀.e) (hD48 : DecLipD48 P₀.e) (hTc : DecContT P₀.e)
    (hT48 : DecLipT48 P₀.e) (hGT : MajGrowT P₀.e) (hGD : MajGrowD P₀.e) : MajLimBound P₀ mH :=
  maj_limBound_of_scalGlob P₀ mH he hm hmH hF
    (maj_scalGlob_of P₀ he hF hDc hD48 hTc hT48 hGT hGD)

end Frozen

end QED.GradedProof.RPi4

end
