/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.Tadpole
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Numerators in integer dimension: radial integrals and isotropy on `ℝ^D`

The dimensionally continued one-loop integrals with numerators are defined by formulas in `d`
(for instance `QED.DimReg.OneLoopBridge.pauliIntegrandDR`). This file proves the formulas they
continue: in every integer dimension `D ≥ 1`, for the Euclidean loop momentum `v ∈ ℝ^D`,
* `∫ h(|v|²) dᴰv = π^(D/2) / Γ(D/2) · ∫₀^∞ t^(D/2-1) h(t) dt` (`integral_radial`), with no
  integrability hypothesis;
* `∫ (|v|²)^k (|v|² + Δ)^(-n) dᴰv / π^(D/2) = (D/2)_k · T(Δ, n, D + 2k)`
  (`integral_radial_power`), where `T = QED.DimReg.tadpole` is the closed form of the
  dimensionally continued tadpole and `(D/2)_k = Γ(D/2 + k) / Γ(D/2)`: a numerator `(v²)^k`
  is a Pochhammer polynomial in `D` times the shift `D ↦ D + 2k`;
* `∫ v_i v_j g(|v|²) = δ_ij / D · ∫ |v|² g(|v|²)` (`integral_coord_mul_coord_smul_radial`,
  `integral_coord_sq_smul_radial`).

The right-hand sides are meromorphic in the dimension, so they are the continuation to complex
`d` of the integer-dimension integrals; this is the sense in which a polynomial numerator is
continued in `d`.
-/

@[expose] public section

open MeasureTheory Set Complex
open scoped Real

namespace QED.DimReg.OneLoopBridgeNum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Radial integrals -/

theorem integral_radial_norm (D : ℕ) (h : ℝ → E) :
    ∫ v : Fin D → ℝ, h (∑ k, v k ^ 2) =
      ∫ x : EuclideanSpace ℝ (Fin D), h (‖x‖ ^ 2) := by
  have e := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin D)).integral_comp'
    (fun v : Fin D → ℝ => h (∑ k, v k ^ 2))
  rw [← e]
  congr 1
  funext x
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- The substitution `t = r²` in the radial integral. -/
theorem integral_pow_smul_sq {D : ℕ} (hD : 0 < D) (h : ℝ → E) :
    ∫ r in Ioi (0 : ℝ), r ^ (D - 1) • h (r ^ 2) =
      (1 / 2 : ℝ) • ∫ t in Ioi (0 : ℝ), t ^ ((D : ℝ) / 2 - 1) • h t := by
  rw [← integral_comp_rpow_Ioi (fun t => t ^ ((D : ℝ) / 2 - 1) • h t) two_ne_zero,
    ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
  have key : 1 / 2 * (|(2 : ℝ)| * r ^ ((2 : ℝ) - 1)) * (r ^ (2 : ℝ)) ^ ((D : ℝ) / 2 - 1) =
      r ^ (D - 1) := by
    rw [abs_two, ← Real.rpow_mul hr.le, ← Real.rpow_natCast r (D - 1), Nat.cast_sub hD,
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Nat.cast_one]
    calc 1 / 2 * (2 * r) * r ^ (2 * ((D : ℝ) / 2 - 1))
        = r ^ (1 : ℝ) * r ^ (2 * ((D : ℝ) / 2 - 1)) := by rw [Real.rpow_one]; ring
      _ = r ^ ((D : ℝ) - 1) := by rw [← Real.rpow_add hr]; congr 1; ring
  simp only [smul_smul, Real.rpow_two] at key ⊢
  congr 1
  rw [← key]
  ring

/-- **Radial integrals in `D` dimensions**:
`∫_{ℝ^D} h(|v|²) dv = π^(D/2) / Γ(D/2) · ∫₀^∞ t^(D/2-1) h(t) dt`, with no integrability
hypothesis. -/
theorem integral_radial {D : ℕ} (hD : 0 < D) (h : ℝ → E) :
    ∫ v : Fin D → ℝ, h (∑ k, v k ^ 2) =
      (π ^ ((D : ℝ) / 2) / Real.Gamma (D / 2)) •
        ∫ t in Ioi (0 : ℝ), t ^ ((D : ℝ) / 2 - 1) • h t := by
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have : Nontrivial (EuclideanSpace ℝ (Fin D)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simp [hD])
  rw [integral_radial_norm, integral_fun_norm_addHaar volume (fun r => h (r ^ 2))]
  simp only [finrank_euclideanSpace_fin, measureReal_def]
  rw [EuclideanSpace.volume_ball, Fintype.card_fin]
  rw [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal (by positivity),
    integral_pow_smul_sq hD, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
  congr 1
  have hD2 : (D : ℝ) / 2 ≠ 0 := by positivity
  have hΓ : Real.Gamma (D / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [Real.Gamma_add_one hD2, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul
    Real.pi_pos.le]
  field_simp

/-! ### The power integrals -/

/-- **Numerators `(v²)^k` in integer dimension.** For `Δ > 0` and `re n > k + D/2`,
`∫_{ℝ^D} (|v|²)^k (|v|² + Δ)^(-n) dv = π^(D/2) · Γ(D/2 + k) / Γ(D/2) · T(Δ, n, D + 2k)`,
where `T = QED.DimReg.tadpole` is the dimensionally continued tadpole. -/
theorem integral_radial_power {D : ℕ} (hD : 0 < D) (k : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) {n : ℂ}
    (hn : (k : ℝ) + D / 2 < n.re) :
    ∫ v : Fin D → ℝ, ((∑ j, v j ^ 2 : ℝ) : ℂ) ^ k * ((∑ j, v j ^ 2 + Δ : ℝ) : ℂ) ^ (-n) =
      (π : ℂ) ^ ((D : ℂ) / 2) * (Gamma ((D : ℂ) / 2 + k) / Gamma ((D : ℂ) / 2)) *
        tadpole Δ n (D + 2 * k) := by
  rw [integral_radial hD (fun t => (t : ℂ) ^ k * ((t + Δ : ℝ) : ℂ) ^ (-n))]
  set a : ℂ := (D : ℂ) / 2 + k
  set b : ℂ := n - a
  have ha : 0 < a.re := by simp [a]; positivity
  have hb : 0 < b.re := by simp [b, a]; linarith
  have hinner : ∫ t in Ioi (0 : ℝ), t ^ ((D : ℝ) / 2 - 1) •
      ((t : ℂ) ^ k * ((t + Δ : ℝ) : ℂ) ^ (-n)) =
      (Δ : ℂ) ^ (-n) * ∫ t in Ioi (0 : ℝ), betaPrimeIntegrand a b Δ⁻¹ t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    rw [betaPrimeIntegrand, Complex.real_smul, ofReal_cpow ht.le,
      show t + Δ = Δ * (1 + Δ⁻¹ * t) by field_simp; ring, ofReal_mul,
      mul_cpow_ofReal_nonneg hΔ.le (by positivity), show a + b = n by simp [b]]
    rw [← cpow_natCast (t : ℂ) k]
    rw [show ((t : ℂ) ^ (((D : ℝ) / 2 - 1 : ℝ) : ℂ)) * ((t : ℂ) ^ ((k : ℕ) : ℂ) *
        ((Δ : ℂ) ^ (-n) * ((1 + Δ⁻¹ * t : ℝ) : ℂ) ^ (-n))) =
        (Δ : ℂ) ^ (-n) * (((t : ℂ) ^ (((D : ℝ) / 2 - 1 : ℝ) : ℂ) * (t : ℂ) ^ ((k : ℕ) : ℂ)) *
          ((1 + Δ⁻¹ * t : ℝ) : ℂ) ^ (-n)) by ring, ← cpow_add _ _ ht0]
    congr 3
    simp [a]
    ring
  rw [hinner, integral_betaPrime ha hb (inv_pos.mpr hΔ), show a + b = n by simp [b], tadpole]
  rw [Complex.real_smul, ofReal_div, ofReal_cpow Real.pi_pos.le, ← Gamma_ofReal]
  push_cast
  have hΓ : Gamma ((D : ℂ) / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; positivity)
  have hΔ0 : (Δ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hΔ.ne'
  have hinv : ((Δ : ℂ)⁻¹) ^ (-a) = (Δ : ℂ) ^ a := by
    rw [← ofReal_inv, cpow_def_of_ne_zero (by simpa using hΔ.ne'), cpow_def_of_ne_zero hΔ0,
      ← ofReal_log (inv_pos.mpr hΔ).le, ← ofReal_log hΔ.le, Real.log_inv]
    push_cast
    ring_nf
  rw [hinv, show n - ((D : ℂ) + 2 * k) / 2 = b by simp [b, a]; ring,
    show ((D : ℂ) + 2 * k) / 2 - n = a + -n by simp [a]; ring, cpow_add a (-n) hΔ0]
  clear_value a b
  simp only [div_eq_mul_inv]
  ring

/-! ### Isotropy of second moments in `D` dimensions -/

/-- Mixed second moments of radial functions vanish (no integrability needed). -/
theorem integral_coord_mul_coord_smul_radial {D : ℕ} (g : ℝ → E) {k l : Fin D} (hkl : k ≠ l) :
    ∫ v : Fin D → ℝ, (v k * v l) • g (∑ j, v j ^ 2) = 0 := by
  let e : (Fin D → ℝ) ≃ᵐ (Fin D → ℝ) := MeasurableEquiv.piCongrRight fun i =>
    if i = k then MeasurableEquiv.neg ℝ else MeasurableEquiv.refl ℝ
  have he : ∀ v i, e v i = if i = k then -v i else v i := by
    intro v i
    change (if i = k then MeasurableEquiv.neg ℝ else MeasurableEquiv.refl ℝ) (v i) = _
    split_ifs <;> rfl
  have hmp : MeasurePreserving e volume volume := by
    refine volume_preserving_pi fun i => ?_
    by_cases hi : i = k
    · simp only [hi, ↓reduceIte]
      exact Measure.measurePreserving_neg volume
    · simp only [hi, ↓reduceIte]
      exact MeasurePreserving.id volume
  have h := hmp.integral_comp' (fun v : Fin D → ℝ => (v k * v l) • g (∑ j, v j ^ 2))
  have hsq : ∀ v, ∑ j, e v j ^ 2 = ∑ j, v j ^ 2 := by
    intro v
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [he]
    split_ifs <;> simp
  have hk : ∀ v, e v k = -v k := fun v => by rw [he, ite_eq_left rfl]
  have hl : ∀ v, e v l = v l := fun v => by rw [he, ite_eq_right hkl.symm]
  simp only [hsq, hk, hl, neg_mul, neg_smul, integral_neg] at h
  have h2 : (2 : ℝ) • ∫ v : Fin D → ℝ, (v k * v l) • g (∑ j, v j ^ 2) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- The second moments `∫ v_k² g(|v|²)` do not depend on `k` (no integrability needed). -/
theorem integral_coord_sq_smul_radial_eq {D : ℕ} (g : ℝ → E) (k l : Fin D) :
    ∫ v : Fin D → ℝ, v k ^ 2 • g (∑ j, v j ^ 2) = ∫ v : Fin D → ℝ, v l ^ 2 • g (∑ j, v j ^ 2) := by
  let e : (Fin D → ℝ) ≃ᵐ (Fin D → ℝ) :=
    MeasurableEquiv.arrowCongr' (Equiv.swap k l) (MeasurableEquiv.refl ℝ)
  have he : ∀ v j, e v j = v (Equiv.swap k l j) := fun v j => rfl
  have hmp : MeasurePreserving e :=
    volume_preserving_arrowCongr' _ _ (MeasurePreserving.id volume)
  have h := hmp.integral_comp' (fun v : Fin D → ℝ => v k ^ 2 • g (∑ j, v j ^ 2))
  have hsum : ∀ v : Fin D → ℝ, ∑ j, v (Equiv.swap k l j) ^ 2 = ∑ j, v j ^ 2 := fun v =>
    Equiv.sum_comp (Equiv.swap k l) (fun j => v j ^ 2)
  simp only [he, Equiv.swap_apply_left, hsum] at h
  exact h.symm

/-- **Isotropy of second moments in `D` dimensions**:
`∫ v_k² g(|v|²) = (1/D) ∫ |v|² g(|v|²)`, when `|v|² g(|v|²)` is integrable. -/
theorem integral_coord_sq_smul_radial {D : ℕ} (g : ℝ → E)
    (hg : Integrable fun v : Fin D → ℝ => (∑ j, v j ^ 2) • g (∑ j, v j ^ 2)) (k : Fin D) :
    ∫ v : Fin D → ℝ, v k ^ 2 • g (∑ j, v j ^ 2) =
      (1 / D : ℝ) • ∫ v : Fin D → ℝ, (∑ j, v j ^ 2) • g (∑ j, v j ^ 2) := by
  have hint : ∀ i : Fin D, Integrable fun v : Fin D → ℝ => v i ^ 2 • g (∑ j, v j ^ 2) := by
    intro i
    have : Nonempty (Fin D) := ⟨i⟩
    have h1 : AEStronglyMeasurable (fun v : Fin D → ℝ =>
        (v i ^ 2 / ∑ j, v j ^ 2) • ((∑ j, v j ^ 2) • g (∑ j, v j ^ 2))) volume :=
      (by fun_prop : Measurable fun v : Fin D → ℝ =>
        v i ^ 2 / ∑ j, v j ^ 2).aestronglyMeasurable.smul hg.aestronglyMeasurable
    have h0 : ∀ᵐ v : Fin D → ℝ, v ≠ 0 := by
      rw [ae_iff]
      simp
    have hmeas : AEStronglyMeasurable (fun v : Fin D → ℝ => v i ^ 2 • g (∑ j, v j ^ 2))
        volume := by
      refine h1.congr ?_
      filter_upwards [h0] with v hv
      have hne : ∑ j, v j ^ 2 ≠ 0 := by
        intro hz
        rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (v j)] at hz
        exact hv (funext fun j => pow_eq_zero_iff two_ne_zero |>.mp (hz j (Finset.mem_univ j)))
      rw [smul_smul, div_mul_cancel₀ _ hne]
    refine hg.norm.mono' hmeas (Filter.Eventually.of_forall fun v => ?_)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg (v j))]
    gcongr
    exact Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hsum : ∫ v : Fin D → ℝ, (∑ j, v j ^ 2) • g (∑ j, v j ^ 2) =
      ∑ i, ∫ v : Fin D → ℝ, v i ^ 2 • g (∑ j, v j ^ 2) := by
    simp_rw [Finset.sum_smul]
    exact integral_finsetSum _ fun i _ => hint i
  have hD : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos k).ne'
  rw [hsum, Finset.sum_congr rfl fun i _ => integral_coord_sq_smul_radial_eq g i k,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    one_div, inv_mul_cancel₀ hD, one_smul]

end QED.DimReg.OneLoopBridgeNum
