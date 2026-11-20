/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajSplit
public import QED.GradedProof.RPi4DensBound

/-!
# (R-Π₄) step L10, two loops: the heavy half of the photon pair, from density bounds

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.UV). The heavy
half `Q(1, b; s) - Q(1, b; 0)` is the integral over the squared photon mass `u ∈ [1, b²]` of
the subtracted density `Δ(s, u) = qDens(s, u) - qDens(0, u)`
(`QED.GradedProof.RPi4.qPair_eq_integral`, at the tilt `c = √s`). Two density bounds along the
ray give `K w(s)` uniformly in `b`:

* `MajDensBd`: `‖u qDens(s, u)‖ ≤ C` and `‖u qDens(0, u)‖ ≤ C` for `s, u ≥ 1` (bounded density,
  `∫_1^s du/u = log s`); it follows from the per-class bounds `MajDRay` (`maj_densBd_of_dRay`);
* `MajFaceRate` (the interface for the face identification): `‖u Δ(s, u)‖ ≤ C (s/u)^η` for
  `u ≥ s ≥ 1`, a rate in the face-limit identity `QED.GradedProof.RPi4.FaceLimitId`, uniform
  along the ray (`∫_s^∞ (s/u)^η du/u = 1/η`).

* `maj_norm_integral_dens_le`: the model-free integral bound `A log s + B/η`;
* **`maj_uvVal_of_dens`**: `DecFaceGen` (for `s ≤ 1`), `MajDensBd` and `MajFaceRate` give the heavy
  half `MajUVVal Φ rep e 1`;
* **`maj_rayVal_of_inputs`**: with the light half (`maj_irVal_of_lray`), `MajRayVal`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

/-! ### The model-free integral bound -/

/-- `‖∫_1^X Δ‖ ≤ A log s + B/η` if `‖Δ u‖ ≤ A/u` for `u ≥ 1` and `‖Δ u‖ ≤ B s^η u^{-η-1}` for
`u ≥ s ≥ 1`. -/
theorem maj_norm_integral_dens_le {Δ : ℝ → ℂ} {A B η s X : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hη : 0 < η) (hs : 1 ≤ s) (hX : 1 ≤ X) (hint : IntervalIntegrable Δ volume 1 X)
    (h₁ : ∀ u : ℝ, 1 ≤ u → ‖Δ u‖ ≤ A * u⁻¹)
    (h₂ : ∀ u : ℝ, s ≤ u → ‖Δ u‖ ≤ B * s ^ η * u ^ (-η - 1)) :
    ‖∫ u in (1 : ℝ)..X, Δ u‖ ≤ A * Real.log s + B / η := by
  have hlow : ∀ Y : ℝ, 1 ≤ Y → Y ≤ s → IntervalIntegrable Δ volume 1 Y →
      ‖∫ u in (1 : ℝ)..Y, Δ u‖ ≤ A * Real.log s := by
    intro Y hY hYs _
    have hg : IntervalIntegrable (fun u : ℝ => A * u⁻¹) volume 1 Y :=
      (intervalIntegral.intervalIntegrable_inv (fun x hx => by
        have := (Set.mem_uIcc.1 hx)
        show x ≠ 0
        rcases this with h | h <;> (intro h0; linarith [h.1, h.2])) continuousOn_id).const_mul A
    refine (intervalIntegral.norm_integral_le_of_norm_le hY (Filter.Eventually.of_forall
      fun u hu => h₁ u hu.1.le) hg).trans ?_
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos (by linarith), div_one]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hYs) hA
  have hBη : 0 ≤ B / η := div_nonneg hB hη.le
  rcases le_or_gt X s with hXs | hXs
  · linarith [hlow X hX hXs hint]
  · have hint₁ : IntervalIntegrable Δ volume 1 s := hint.mono_set (by
      rw [Set.uIcc_of_le hs, Set.uIcc_of_le hX]
      exact Set.Icc_subset_Icc le_rfl hXs.le)
    have hint₂ : IntervalIntegrable Δ volume s X := hint.mono_set (by
      rw [Set.uIcc_of_le hXs.le, Set.uIcc_of_le hX]
      exact Set.Icc_subset_Icc hs le_rfl)
    rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂]
    refine (norm_add_le _ _).trans (add_le_add (hlow s hs le_rfl hint₁) ?_)
    have hs0 : 0 < s := by linarith
    have h0 : (0 : ℝ) ∉ Set.uIcc s X := Set.notMem_uIcc_of_lt hs0 (by linarith)
    have hne : -η - 1 ≠ -1 := by linarith
    have hg : IntervalIntegrable (fun u : ℝ => B * s ^ η * u ^ (-η - 1)) volume s X :=
      (intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).const_mul _
    refine (intervalIntegral.norm_integral_le_of_norm_le hXs.le (Filter.Eventually.of_forall
      fun u hu => h₂ u hu.1.le) hg).trans ?_
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨hne, h0⟩)]
    have e1 : -η - 1 + 1 = -η := by ring
    rw [e1]
    have hXη : 0 ≤ X ^ (-η) := Real.rpow_nonneg (by linarith) _
    have hsη : s ^ η * s ^ (-η) = 1 := by
      rw [← Real.rpow_add hs0, add_neg_cancel, Real.rpow_zero]
    have hsη0 : 0 ≤ s ^ η := Real.rpow_nonneg hs0.le _
    have key : B * s ^ η * ((X ^ (-η) - s ^ (-η)) / -η) =
        B / η * (1 - s ^ η * X ^ (-η)) := by
      field_simp
      rw [← hsη]
      ring
    rw [key]
    have : 0 ≤ s ^ η * X ^ (-η) := mul_nonneg hsη0 hXη
    nlinarith

/-! ### The density bounds and the heavy half -/

section UV

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- **Bounded density along the ray**: `‖u qDens(s, u)‖ ≤ C`, `‖u qDens(0, u)‖ ≤ C` at the tilt
`c = √s`, for `s ≥ 1`, `u ≥ 1`. -/
def MajDensBd (e m₀ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, 1 ≤ u →
    ‖(u : ℂ) * qDens Φ rep e m₀ (Real.sqrt s) s u‖ ≤ C ∧
      ‖(u : ℂ) * qDens Φ rep e m₀ (Real.sqrt s) 0 u‖ ≤ C

/-- **(Interface for the face identification) the face-limit identity with a rate, along the
ray**: `‖u (qDens(s, u) - qDens(0, u))‖ ≤ C (s/u)^η` at the tilt `c = √s`, for `u ≥ s ≥ 1`. -/
def MajFaceRate (e m₀ : ℝ) : Prop :=
  ∃ C η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
    ‖(u : ℂ) * (qDens Φ rep e m₀ (Real.sqrt s) s u - qDens Φ rep e m₀ (Real.sqrt s) 0 u)‖ ≤
      C * (s / u) ^ η

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **(T2.UV, assembly) The heavy half at `R₀ = 1`** from the face-limit identity (`s ≤ 1`),
the bounded density and the face rate along the ray (`s ≥ 1`). -/
theorem maj_uvVal_of_dens (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e)
    (hD : MajDensBd Φ rep P.e m₀) (hR : MajFaceRate Φ rep P.e m₀) :
    MajUVVal Φ rep P.e 1 := by
  obtain ⟨CD, hCD⟩ := hD
  obtain ⟨CR, η, hη, hCR⟩ := hR
  have hm2 := pow_pos hm₀ 2
  -- small `s`: the compact heavy-pair bound
  obtain ⟨C₀, hC₀⟩ := exists_norm_qPair_sub_heavy_le Φ rep P hm₀ hmass hrep hPV₁ hPV₂ he
    one_pos (S₀ := 0) (S := 1) (by linarith) le_rfl zero_le_one (by norm_num)
    fun s h₀ h₁ => hF F Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ 1 s one_pos (by linarith)
      (by linarith)
  refine ⟨|C₀| + 2 * |CD| + |CR| / η, 1, fun b hb s hs => ?_⟩
  have hw := maj_one_le_majW hs
  have hK0 : 0 ≤ |C₀| + 2 * |CD| + |CR| / η := by positivity
  rcases le_or_gt s 1 with hs1 | hs1
  · have h := hC₀ s hs hs1 1 b le_rfl hb.le
    rw [div_one] at h
    have : |C₀| ≤ (|C₀| + 2 * |CD| + |CR| / η) * majW s := by
      have h1 : |C₀| ≤ |C₀| + 2 * |CD| + |CR| / η := by
        have := div_nonneg (abs_nonneg CR) hη.le
        linarith [abs_nonneg CD]
      exact h1.trans (le_mul_of_one_le_right hK0 hw)
    exact h.trans ((le_abs_self _).trans this)
  · -- large `s`: the density representation at the tilt `c = √s`
    set c : ℝ := Real.sqrt s with hc_def
    have hs0 : 0 < s := by linarith
    have hc : 0 < c := Real.sqrt_pos.mpr hs0
    have hc2 : c ^ 2 = s := Real.sq_sqrt hs0.le
    have hsr : -(4 * m₀ ^ 2) < s := by linarith
    have hs2 : s < 2 * c ^ 2 := by rw [hc2]; linarith
    have h0r : -(4 * m₀ ^ 2) < 0 := by linarith
    have h02 : (0 : ℝ) < 2 * c ^ 2 := by positivity
    obtain ⟨iS, eS⟩ := qPair_eq_integral Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he one_pos hb hc hsr hs2
    obtain ⟨i0, e0⟩ := qPair_eq_integral Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he one_pos hb hc h0r h02
    rw [eS, e0, ← intervalIntegral.integral_sub iS i0, one_pow]
    rw [one_pow] at iS i0
    have hX : 1 ≤ b ^ 2 := by nlinarith
    have hlog : Real.log s ≤ majW s := by
      have := Real.log_le_log hs0 (by linarith : s ≤ 1 + s)
      simp only [majW]
      linarith
    refine (maj_norm_integral_dens_le (A := 2 * |CD|) (B := |CR|) (by positivity)
      (abs_nonneg _) hη hs1.le hX (iS.sub i0) (fun u hu => ?_) (fun u hu => ?_)).trans ?_
    · have hu0 : 0 < u := by linarith
      have h := hCD s hs1.le u hu
      have hn : ‖(u : ℂ)‖ = u := by rw [Complex.norm_real, Real.norm_of_nonneg hu0.le]
      have h1 : ‖qDens Φ rep P.e m₀ c s u‖ ≤ |CD| * u⁻¹ := by
        rw [le_mul_inv_iff₀ hu0, mul_comm]
        calc u * ‖qDens Φ rep P.e m₀ c s u‖ = ‖(u : ℂ) * qDens Φ rep P.e m₀ c s u‖ := by
              rw [norm_mul, hn]
          _ ≤ |CD| := h.1.trans (le_abs_self _)
      have h2 : ‖qDens Φ rep P.e m₀ c 0 u‖ ≤ |CD| * u⁻¹ := by
        rw [le_mul_inv_iff₀ hu0, mul_comm]
        calc u * ‖qDens Φ rep P.e m₀ c 0 u‖ = ‖(u : ℂ) * qDens Φ rep P.e m₀ c 0 u‖ := by
              rw [norm_mul, hn]
          _ ≤ |CD| := h.2.trans (le_abs_self _)
      calc _ ≤ ‖qDens Φ rep P.e m₀ c s u‖ + ‖qDens Φ rep P.e m₀ c 0 u‖ := norm_sub_le _ _
        _ ≤ |CD| * u⁻¹ + |CD| * u⁻¹ := add_le_add h1 h2
        _ = 2 * |CD| * u⁻¹ := by ring
    · have hu0 : 0 < u := by linarith
      have h := hCR s hs1.le u hu
      have hn : ‖(u : ℂ)‖ = u := by rw [Complex.norm_real, Real.norm_of_nonneg hu0.le]
      rw [norm_mul, hn] at h
      have hr : (s / u) ^ η = s ^ η * u ^ (-η) := by
        rw [Real.div_rpow hs0.le hu0.le, Real.rpow_neg hu0.le, div_eq_mul_inv]
      have hr' : u ^ (-η - 1) = u ^ (-η) * u⁻¹ := by
        rw [Real.rpow_sub hu0, Real.rpow_one, div_eq_mul_inv]
      rw [hr', ← mul_assoc]
      rw [hr] at h
      rw [le_mul_inv_iff₀ hu0]
      calc _ = u * ‖qDens Φ rep P.e m₀ c s u - qDens Φ rep P.e m₀ c 0 u‖ := by ring
        _ ≤ CR * (s ^ η * u ^ (-η)) := h
        _ ≤ |CR| * (s ^ η * u ^ (-η)) := mul_le_mul_of_nonneg_right (le_abs_self _)
            (mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg hu0.le _))
        _ = _ := by ring
    · have hCRη : 0 ≤ |CR| / η := div_nonneg (abs_nonneg _) hη.le
      nlinarith [abs_nonneg C₀, abs_nonneg CD, mul_nonneg (abs_nonneg CD) (by linarith :
        (0 : ℝ) ≤ majW s - Real.log s), mul_nonneg hCRη (by linarith : (0 : ℝ) ≤ majW s - 1),
        mul_nonneg (abs_nonneg C₀) (by linarith : (0 : ℝ) ≤ majW s)]

end UV

/-! ### The bounded density from the classes -/

/-- **One class density along the ray**: `‖u G(u, k'(s))‖ ≤ C s` and `‖u G(u, k'_s(0))‖ ≤ C s`
at the tilt `c = √s`, for `s ≥ 1`, `u ≥ 1`. -/
def MajDRay (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, 1 ≤ u →
    ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s)‖ ≤ C * s ∧
      ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) 0)‖ ≤ C * s

/-- `|u σ(M, u)| ≤ 3e²/(16π²) + e²|M|/(2π²)` for `u ≥ 1`. -/
theorem maj_abs_mul_sigma_le (e : ℝ) {m u : ℝ} (hm : m ≠ 0) (hu : 1 ≤ u) :
    |u * sigma e m u| ≤ 3 * e ^ 2 / (16 * Real.pi ^ 2) + e ^ 2 * |m| / (2 * Real.pi ^ 2) := by
  have h := abs_mul_sigma_add_le e hm (by linarith : (0 : ℝ) < u)
  have h1 : u ^ (-(1 / 2) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu (by norm_num)
  have h2 : e ^ 2 * |m| / (2 * Real.pi ^ 2) * u ^ (-(1 / 2) : ℝ) ≤
      e ^ 2 * |m| / (2 * Real.pi ^ 2) :=
    mul_le_of_le_one_right (by positivity) h1
  have h3 : |3 * e ^ 2 / (16 * Real.pi ^ 2)| = 3 * e ^ 2 / (16 * Real.pi ^ 2) :=
    abs_of_nonneg (by positivity)
  calc |u * sigma e m u|
      = |(u * sigma e m u + 3 * e ^ 2 / (16 * Real.pi ^ 2)) - 3 * e ^ 2 / (16 * Real.pi ^ 2)| := by
        ring_nf
    _ ≤ |u * sigma e m u + 3 * e ^ 2 / (16 * Real.pi ^ 2)| +
        |3 * e ^ 2 / (16 * Real.pi ^ 2)| := abs_sub _ _
    _ ≤ _ := by rw [h3]; linarith

section Dens

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **`MajDensBd` from the three class densities** (`MajDRay`) and the single-flavour one-loop
blocks along the ray (`MajTiltRay`); at `s = 0` the blocks are `s` times their projection at
`0` (covariance). -/
theorem maj_densBd_of_dRay (P : Params) (he : P.e ≠ 0)
    (hA : MajDRay fun u k => vDens aVA baseVA cVA Φ P.e m₀ u k 2 3)
    (hB : MajDRay fun u k => vDens aVB baseVB cVB Φ P.e m₀ u k 2 3)
    (hC : MajDRay fun u k => vDens aVC baseVC cVC Φ P.e m₀ u k 2 3)
    (hFl : ∀ g, MajTiltRay (fLim Φ rep P.e (Pi.single g 1))) : MajDensBd Φ rep P.e m₀ := by
  obtain ⟨CA, hCA⟩ := hA
  obtain ⟨CB, hCB⟩ := hB
  obtain ⟨CC, hCC⟩ := hC
  choose CF hCF using hFl
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  set Sg : F → ℝ := fun g =>
    3 * P.e ^ 2 / (16 * Real.pi ^ 2) + P.e ^ 2 * |Φ.mass g| / (2 * Real.pi ^ 2) with hSg
  set Eg : F → ℝ := fun g =>
    max |CF g| ‖projS (fLim Φ rep P.e (Pi.single g 1)) 0‖ with hEg
  have hS0 : ∀ g, 0 ≤ Sg g := fun g => by simp only [hSg]; positivity
  have hE0 : ∀ g, 0 ≤ Eg g := fun g => (abs_nonneg _).trans (le_max_left _ _)
  set C : ℝ := |CA| + |CB| + |CC| + ∑ g, Sg g * Eg g with hC_def
  refine ⟨C, fun s hs u hu => ?_⟩
  have hs0 : 0 < s := by linarith
  set c : ℝ := Real.sqrt s with hc_def
  have hc : 0 < c := Real.sqrt_pos.mpr hs0
  have hc2 : c ^ 2 = s := Real.sq_sqrt hs0.le
  have hn : ‖(u : ℂ)‖ = u := by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  -- the common estimate at `s' ∈ {s, 0}`
  have key : ∀ s' : ℝ,
      ‖(u : ℂ) * vDens aVA baseVA cVA Φ P.e m₀ u (tiltVec c s') 2 3‖ ≤ CA * s →
      ‖(u : ℂ) * vDens aVB baseVB cVB Φ P.e m₀ u (tiltVec c s') 2 3‖ ≤ CB * s →
      ‖(u : ℂ) * vDens aVC baseVC cVC Φ P.e m₀ u (tiltVec c s') 2 3‖ ≤ CC * s →
      (∀ g, ‖fLim Φ rep P.e (Pi.single g 1) (tiltVec c s') 2 3‖ ≤ Eg g * s) →
      ‖(u : ℂ) * qDens Φ rep P.e m₀ c s' u‖ ≤ C := by
    intro s' h1 h2 h3 h4
    have hM : ‖(u : ℂ) * ∑ g, (sigma P.e (Φ.mass g) u : ℂ) *
        fLim Φ rep P.e (Pi.single g 1) (tiltVec c s') 2 3‖ ≤ (∑ g, Sg g * Eg g) * s := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
      rw [← mul_assoc, norm_mul, norm_mul, hn, Complex.norm_real, Real.norm_eq_abs]
      have hua : u * |sigma P.e (Φ.mass g) u| = |u * sigma P.e (Φ.mass g) u| := by
        rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < u)]
      rw [hua]
      have := maj_abs_mul_sigma_le P.e (hpos g).ne' hu
      calc |u * sigma P.e (Φ.mass g) u| * ‖fLim Φ rep P.e (Pi.single g 1) (tiltVec c s') 2 3‖
          ≤ Sg g * (Eg g * s) := mul_le_mul this (h4 g) (norm_nonneg _) (hS0 g)
        _ = Sg g * Eg g * s := by ring
    have e : (u : ℂ) * qDens Φ rep P.e m₀ c s' u = -I / ((c ^ 2 : ℝ) : ℂ) *
        ((u : ℂ) * vDens aVA baseVA cVA Φ P.e m₀ u (tiltVec c s') 2 3 +
          (u : ℂ) * vDens aVB baseVB cVB Φ P.e m₀ u (tiltVec c s') 2 3 +
          (u : ℂ) * vDens aVC baseVC cVC Φ P.e m₀ u (tiltVec c s') 2 3 +
          (u : ℂ) * ∑ g, (sigma P.e (Φ.mass g) u : ℂ) *
            fLim Φ rep P.e (Pi.single g 1) (tiltVec c s') 2 3) := by
      simp only [qDens]
      ring
    have hsum := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)) hM)
    rw [e, norm_mul, norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity), hc2]
    have hCA : CA * s ≤ |CA| * s := mul_le_mul_of_nonneg_right (le_abs_self _) hs0.le
    have hCB : CB * s ≤ |CB| * s := mul_le_mul_of_nonneg_right (le_abs_self _) hs0.le
    have hCC : CC * s ≤ |CC| * s := mul_le_mul_of_nonneg_right (le_abs_self _) hs0.le
    calc 1 / s * ‖_‖ ≤ 1 / s * (C * s) := by
          refine mul_le_mul_of_nonneg_left (hsum.trans ?_) (by positivity)
          rw [hC_def]
          linarith
      _ = C := by field_simp
  refine ⟨key s (hCA s hs u hu).1 (hCB s hs u hu).1 (hCC s hs u hu).1 fun g => ?_,
    key 0 (hCA s hs u hu).2 (hCB s hs u hu).2 (hCC s hs u hu).2 fun g => ?_⟩
  · exact ((hCF g s hs).1.trans (mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (le_max_left _ _)) hs0.le))
  · have hm2 := pow_pos hm₀ 2
    have h := projS_eq_tilt (tcov_fLim Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he (Pi.single g 1)) hc
      (by nlinarith : -(2 * m₀) ^ 2 < (0 : ℝ)) (by positivity : (0 : ℝ) < 2 * c ^ 2)
    have hc2' : ((c ^ 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; positivity
    have e : fLim Φ rep P.e (Pi.single g 1) (tiltVec c 0) 2 3 =
        -(((c ^ 2 : ℝ) : ℂ) * projS (fLim Φ rep P.e (Pi.single g 1)) 0) := by
      rw [h]
      field_simp
    rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
      hc2, mul_comm]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hs0.le

/-- **(T2) `MajRayVal` from its inputs**: the light half (`MajLRay` of the three class entries),
the heavy half (`DecFaceGen`, `MajDRay` of the three class densities, `MajFaceRate`) and the
single-flavour one-loop blocks along the ray. -/
theorem maj_rayVal_of_inputs (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e)
    (hA : MajLRay fun a b k => vVal aVA baseVA cVA Φ P.e m₀ a b k 2 3)
    (hB : MajLRay fun a b k => vVal aVB baseVB cVB Φ P.e m₀ a b k 2 3)
    (hC : MajLRay fun a b k => vVal aVC baseVC cVC Φ P.e m₀ a b k 2 3)
    (hDA : MajDRay fun u k => vDens aVA baseVA cVA Φ P.e m₀ u k 2 3)
    (hDB : MajDRay fun u k => vDens aVB baseVB cVB Φ P.e m₀ u k 2 3)
    (hDC : MajDRay fun u k => vDens aVC baseVC cVC Φ P.e m₀ u k 2 3)
    (hR : MajFaceRate Φ rep P.e m₀)
    (hFl : ∀ g, MajTiltRay (fLim Φ rep P.e (Pi.single g 1))) : MajRayVal Φ rep P.e :=
  maj_rayVal_of_split Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he one_pos
    (maj_irVal_of_lray P Φ rep hrep hPV₁ hPV₂ hm₀ hmass he hA hB hC hFl)
    (maj_uvVal_of_dens Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he hF
      (maj_densBd_of_dRay Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he hDA hDB hDC hFl) hR)

end Dens

end QED.GradedProof.RPi4

end
