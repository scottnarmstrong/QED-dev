/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4InstClass
public import QED.GradedProof.RPi4QDens
public import QED.GradedProof.RPi4UnifF
public import QED.GradedProof.RPi4SigmaAsym
public import QED.GradedProof.RPi4SectorEl

/-!
# (R-Π₄) step L6d: the heavy-photon density bound, given the face-limit identity

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d (heavy photon
pair). The density `qDens(s, t)` of the projected class sum satisfies
`‖t · qDens(s, t) - 𝓛(s)‖ ≤ C t^{-1/2}` for `t ≥ 1`, uniformly for `s` in a compact interval
`[S₀, S]` below threshold (`exists_qDens_rate`): the class densities by
`QED.GradedProof.RPi4.heavyRate_vDens_VA` (and `VB`, `VC`) along the tilt segment, the mass part
by `t σ(t) = -3e²/(16π²) + O(t^{-1/2})` (`abs_sigma_add_le`, `log_one_add_le_two_mul_sqrt`) and the
boundedness of the one-loop limits `fLim` at the tilted vectors.

The face-limit identity (step L6d3) is the hypothesis `FaceLimitId`: `t (qDens(s, t) -
qDens(0, t)) → 0`, i.e. `𝓛(s) = 𝓛(0)` (`faceLimitId_of_tendsto`, `exists_tendsto_mul_qDens`).
Given it, `‖qDens(s, t) - qDens(0, t)‖ ≤ C t^{-3/2}` (`norm_qDens_sub_le`), and by
`norm_qPair_sub_le_of_dens` the heavy photon pair is `O(1/b)`:
`‖qPair(b, d; s) - qPair(b, d; 0)‖ ≤ C/b` for `1 ≤ b ≤ d` (`exists_norm_qPair_sub_heavy_le`).
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.WickModel (Params)

/-! ### Elementary estimates -/

theorem log_one_add_le_two_mul_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log (1 + x) ≤ 2 * Real.sqrt x := by
  have h1 : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.2 (by linarith)
  have h2 := Real.log_le_sub_one_of_pos h1
  rw [Real.log_sqrt (by linarith)] at h2
  have h3 : Real.sqrt (1 + x) ≤ 1 + Real.sqrt x := by
    rw [Real.sqrt_le_left]
    · nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]
    · positivity
  linarith

theorem rpow_neg_half_eq_inv_sqrt {t : ℝ} (ht : 0 ≤ t) :
    t ^ (-(1 / 2) : ℝ) = (Real.sqrt t)⁻¹ := by
  rw [Real.rpow_neg ht, Real.sqrt_eq_rpow]

/-- **The mass-insertion density at a heavy photon**: `|t σ(t) + 3e²/(16π²)| ≤
(e²|m|/(2π²)) t^{-1/2}`. -/
theorem abs_mul_sigma_add_le (e : ℝ) {m t : ℝ} (hm : m ≠ 0) (ht : 0 < t) :
    |t * sigma e m t + 3 * e ^ 2 / (16 * π ^ 2)| ≤
      e ^ 2 * |m| / (2 * π ^ 2) * t ^ (-(1 / 2) : ℝ) := by
  have hm2 : 0 < m ^ 2 := by positivity
  have hma : 0 < |m| := abs_pos.2 hm
  have h := abs_sigma_add_le e hm ht
  have hlog := log_one_add_le_two_mul_sqrt (div_nonneg ht.le hm2.le)
  have hsq : Real.sqrt (t / m ^ 2) = Real.sqrt t / |m| := by
    rw [Real.sqrt_div' _ hm2.le, Real.sqrt_sq_eq_abs]
  rw [hsq] at hlog
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have htt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have e1 : t * sigma e m t + 3 * e ^ 2 / (16 * π ^ 2) =
      t * (sigma e m t + 3 * e ^ 2 / (16 * π ^ 2 * t)) := by
    field_simp
  rw [e1, abs_mul, abs_of_pos ht, rpow_neg_half_eq_inv_sqrt ht.le]
  have hL : 0 ≤ Real.log (1 + t / m ^ 2) := Real.log_nonneg (by
    have : 0 ≤ t / m ^ 2 := by positivity
    linarith)
  calc t * |sigma e m t + 3 * e ^ 2 / (16 * π ^ 2 * t)|
      ≤ t * (e ^ 2 * m ^ 2 / (4 * π ^ 2 * t ^ 2) * Real.log (1 + t / m ^ 2)) :=
        mul_le_mul_of_nonneg_left h ht.le
    _ ≤ t * (e ^ 2 * m ^ 2 / (4 * π ^ 2 * t ^ 2) * (2 * (Real.sqrt t / |m|))) := by
        gcongr
    _ = e ^ 2 * |m| / (2 * π ^ 2) * (Real.sqrt t)⁻¹ := by
        have key : ∀ r : ℝ, 0 < r → r * r = t → t * (e ^ 2 * |m| ^ 2 / (4 * π ^ 2 * t ^ 2) *
            (2 * (r / |m|))) = e ^ 2 * |m| / (2 * π ^ 2) * r⁻¹ := by
          intro r hr hrt
          subst hrt
          field_simp
          ring
        rw [← sq_abs m]
        exact key _ hst htt

/-! ### The face-limit identity (the target of step L6d3) -/

section Dens

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- **The face-limit identity** (step L6d3): the `t → ∞` limit of `t · qDens(s, t)` does not
depend on `s`, in the form `t (qDens(s, t) - qDens(0, t)) → 0`. -/
def FaceLimitId (e m₀ c s : ℝ) : Prop :=
  Tendsto (fun t : ℝ => (t : ℂ) * (qDens Φ rep e m₀ c s t - qDens Φ rep e m₀ c 0 t)) atTop
    (𝓝 0)

theorem faceLimitId_of_tendsto {e m₀ c s : ℝ} {L : ℂ}
    (hs : Tendsto (fun t : ℝ => (t : ℂ) * qDens Φ rep e m₀ c s t) atTop (𝓝 L))
    (h0 : Tendsto (fun t : ℝ => (t : ℂ) * qDens Φ rep e m₀ c 0 t) atTop (𝓝 L)) :
    FaceLimitId Φ rep e m₀ c s := by
  have := hs.sub h0
  rw [sub_self] at this
  exact this.congr fun t => by ring

variable (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **The heavy-photon rate of the density of the projected class sum**, uniformly on a compact
interval below threshold: `‖t qDens(s, t) - 𝓛(s)‖ ≤ C t^{-1/2}` for `t ≥ 1`. -/
theorem exists_qDens_rate (he : P.e ≠ 0) {c S₀ S : ℝ} (hc : 0 < c)
    (hS₀ : -(4 * m₀ ^ 2) < S₀) (hS₀S : S₀ ≤ S) (hS : S < 2 * c ^ 2) :
    ∃ C : ℝ, ∃ L : ℝ → ℂ, ∀ s : ℝ, S₀ ≤ s → s ≤ S → ∀ t : ℝ, 1 ≤ t →
      ‖(t : ℂ) * qDens Φ rep P.e m₀ c s t - L s‖ ≤ C * t ^ (-(1 / 2) : ℝ) := by
  set k₀ := tiltBase c S₀ S
  set w := tiltDir c S₀ S
  have hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u) :=
    fun u hu => (dot_lineK_tilt_mem (c := c) hS hS₀S hu).1
  have hS₀' : -(2 * m₀) ^ 2 < S₀ := by nlinarith
  obtain ⟨CA, LA, hA⟩ := heavyRate_vDens_VA Φ hm₀ hmass P.e hS₀' hseg 2 3
  obtain ⟨CB, LB, hB⟩ := heavyRate_vDens_VB Φ hm₀ hmass P.e hS₀' hseg 2 3
  obtain ⟨CC, LC, hC⟩ := heavyRate_vDens_VC Φ hm₀ hmass P.e hS₀' hseg 2 3
  choose CF hCF using fun g : F => exists_norm_fLim_tilt_le P Φ rep hm₀ hmass hrep hPV₁ hPV₂ he
    (Pi.single g 1) hS₀ hS₀S hS 2 3
  have hu : ∀ s, ∃ u, S₀ ≤ s → s ≤ S → |u| ≤ 1 / 2 ∧ tiltVec c s = lineK k₀ w u := fun s => by
    by_cases h : S₀ ≤ s ∧ s ≤ S
    · obtain ⟨u, hu, he⟩ := exists_tiltVec_eq_lineK (c := c) h.1 h.2
      exact ⟨u, fun _ _ => ⟨hu, he⟩⟩
    · exact ⟨0, fun h₀ h₁ => absurd ⟨h₀, h₁⟩ h⟩
  choose U hU using hu
  set κm : ℝ := 3 * P.e ^ 2 / (16 * π ^ 2)
  set Fg : F → ℝ → ℂ := fun g s => fLim Φ rep P.e (Pi.single g 1) (tiltVec c s) 2 3
  set L : ℝ → ℂ := fun s => -I / ((c ^ 2 : ℝ) : ℂ) *
    (LA (U s) + LB (U s) + LC (U s) + ∑ g, ((-κm : ℝ) : ℂ) * Fg g s)
  set Cm : ℝ := ∑ g, P.e ^ 2 * |Φ.mass g| / (2 * π ^ 2) * |CF g|
  have hc2 : 0 < c ^ 2 := by positivity
  refine ⟨(c ^ 2)⁻¹ * (CA + CB + CC + Cm), L, fun s h₀ h₁ t ht => ?_⟩
  obtain ⟨hU1, hU2⟩ := hU s h₀ h₁
  have ht0 : 0 < t := one_pos.trans_le ht
  set vA := vDens aVA baseVA cVA Φ P.e m₀ t (tiltVec c s) 2 3
  set vB := vDens aVB baseVB cVB Φ P.e m₀ t (tiltVec c s) 2 3
  set vC := vDens aVC baseVC cVC Φ P.e m₀ t (tiltVec c s) 2 3
  set σg : F → ℝ := fun g => sigma P.e (Φ.mass g) t
  have key : (t : ℂ) * qDens Φ rep P.e m₀ c s t - L s = -I / ((c ^ 2 : ℝ) : ℂ) *
      (((t : ℂ) * vA - LA (U s)) + ((t : ℂ) * vB - LB (U s)) + ((t : ℂ) * vC - LC (U s)) +
        ∑ g, ((t * σg g + κm : ℝ) : ℂ) * Fg g s) := by
    have hs : (t : ℂ) * ∑ g, (σg g : ℂ) * Fg g s - ∑ g, ((-κm : ℝ) : ℂ) * Fg g s =
        ∑ g, ((t * σg g + κm : ℝ) : ℂ) * Fg g s := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun g _ => by push_cast; ring
    simp only [qDens, L]
    rw [← hs]
    ring
  rw [key, norm_mul, norm_div, norm_neg, Complex.norm_I, Complex.norm_real,
    Real.norm_of_nonneg hc2.le, one_div, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hc2.le)
  have eA := hA (U s) hU1 t ht
  have eB := hB (U s) hU1 t ht
  have eC := hC (U s) hU1 t ht
  rw [← hU2] at eA eB eC
  have eM : ‖∑ g, ((t * σg g + κm : ℝ) : ℂ) * Fg g s‖ ≤ Cm * t ^ (-(1 / 2) : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    simp only [Cm, Finset.sum_mul]
    refine Finset.sum_le_sum fun g _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_mul_sigma_add_le P.e (hm₀.trans_le (hmass g)).ne' ht0
    have h2 : ‖Fg g s‖ ≤ |CF g| := (hCF g s h₀ h₁).trans (le_abs_self _)
    calc |t * σg g + κm| * ‖Fg g s‖
        ≤ (P.e ^ 2 * |Φ.mass g| / (2 * π ^ 2) * t ^ (-(1 / 2) : ℝ)) * |CF g| :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = P.e ^ 2 * |Φ.mass g| / (2 * π ^ 2) * |CF g| * t ^ (-(1 / 2) : ℝ) := by ring
  calc ‖((t : ℂ) * vA - LA (U s)) + ((t : ℂ) * vB - LB (U s)) + ((t : ℂ) * vC - LC (U s)) +
        ∑ g, ((t * σg g + κm : ℝ) : ℂ) * Fg g s‖
      ≤ ‖(t : ℂ) * vA - LA (U s)‖ + ‖(t : ℂ) * vB - LB (U s)‖ + ‖(t : ℂ) * vC - LC (U s)‖ +
          ‖∑ g, ((t * σg g + κm : ℝ) : ℂ) * Fg g s‖ := norm_add₄_le
    _ ≤ CA * t ^ (-(1 / 2) : ℝ) + CB * t ^ (-(1 / 2) : ℝ) + CC * t ^ (-(1 / 2) : ℝ) +
          Cm * t ^ (-(1 / 2) : ℝ) := by gcongr
    _ = (CA + CB + CC + Cm) * t ^ (-(1 / 2) : ℝ) := by ring

/-- **The limits `𝓛(s) = lim_{t → ∞} t qDens(s, t)` exist** on a compact interval below
threshold. -/
theorem exists_tendsto_mul_qDens (he : P.e ≠ 0) {c S₀ S : ℝ} (hc : 0 < c)
    (hS₀ : -(4 * m₀ ^ 2) < S₀) (hS₀S : S₀ ≤ S) (hS : S < 2 * c ^ 2) :
    ∃ L : ℝ → ℂ, ∀ s : ℝ, S₀ ≤ s → s ≤ S →
      Tendsto (fun t : ℝ => (t : ℂ) * qDens Φ rep P.e m₀ c s t) atTop (𝓝 (L s)) := by
  obtain ⟨C, L, hC⟩ := exists_qDens_rate Φ rep P hm₀ hmass hrep hPV₁ hPV₂ he hc hS₀ hS₀S hS
  refine ⟨L, fun s h₀ h₁ => ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hr : Tendsto (fun t : ℝ => C * t ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_atTop.2 ⟨1, fun t ht => hC s h₀ h₁ t ht⟩) hr

/-- **The heavy-photon density bound, given the face-limit identity** (step L6d, conditional on
L6d3): `‖qDens(s, t) - qDens(0, t)‖ ≤ C t^{-3/2}` for `t ≥ 1`, `s ∈ [S₀, S] ∋ 0`. -/
theorem norm_qDens_sub_le (he : P.e ≠ 0) {c S₀ S : ℝ} (hc : 0 < c)
    (hS₀ : -(4 * m₀ ^ 2) < S₀) (hS₀0 : S₀ ≤ 0) (h0S : 0 ≤ S) (hS : S < 2 * c ^ 2)
    (hId : ∀ s : ℝ, S₀ ≤ s → s ≤ S → FaceLimitId Φ rep P.e m₀ c s) :
    ∃ C : ℝ, ∀ s : ℝ, S₀ ≤ s → s ≤ S → ∀ t : ℝ, 1 ≤ t →
      ‖qDens Φ rep P.e m₀ c s t - qDens Φ rep P.e m₀ c 0 t‖ ≤ C * t ^ (-(3 / 2) : ℝ) := by
  have hS₀S : S₀ ≤ S := hS₀0.trans h0S
  obtain ⟨C, L, hC⟩ := exists_qDens_rate Φ rep P hm₀ hmass hrep hPV₁ hPV₂ he hc hS₀ hS₀S hS
  have hr : Tendsto (fun t : ℝ => C * t ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C
  have hT : ∀ s, S₀ ≤ s → s ≤ S →
      Tendsto (fun t : ℝ => (t : ℂ) * qDens Φ rep P.e m₀ c s t) atTop (𝓝 (L s)) :=
    fun s h₀ h₁ => by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
        (eventually_atTop.2 ⟨1, fun t ht => hC s h₀ h₁ t ht⟩) hr
  refine ⟨2 * C, fun s h₀ h₁ t ht => ?_⟩
  have hL : L s = L 0 := by
    have h := (hT s h₀ h₁).sub (hT 0 hS₀0 h0S)
    have h' : Tendsto (fun t : ℝ => (t : ℂ) * (qDens Φ rep P.e m₀ c s t -
        qDens Φ rep P.e m₀ c 0 t)) atTop (𝓝 (L s - L 0)) := h.congr fun t => by ring
    exact sub_eq_zero.1 (tendsto_nhds_unique h' (hId s h₀ h₁))
  have ht0 : 0 < t := one_pos.trans_le ht
  have e : qDens Φ rep P.e m₀ c s t - qDens Φ rep P.e m₀ c 0 t = (t⁻¹ : ℂ) *
      (((t : ℂ) * qDens Φ rep P.e m₀ c s t - L s) -
        ((t : ℂ) * qDens Φ rep P.e m₀ c 0 t - L 0)) := by
    rw [hL]
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    field_simp
    ring
  have hpow : t ^ (-(3 / 2) : ℝ) = t⁻¹ * t ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]
    norm_num
  rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht0.le, hpow]
  calc t⁻¹ * ‖((t : ℂ) * qDens Φ rep P.e m₀ c s t - L s) -
        ((t : ℂ) * qDens Φ rep P.e m₀ c 0 t - L 0)‖
      ≤ t⁻¹ * (C * t ^ (-(1 / 2) : ℝ) + C * t ^ (-(1 / 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans
          (add_le_add (hC s h₀ h₁ t ht) (hC 0 hS₀0 h0S t ht))) (inv_nonneg.2 ht0.le)
    _ = 2 * C * (t⁻¹ * t ^ (-(1 / 2) : ℝ)) := by ring

/-- `qPair` vanishes at a coinciding photon pair. -/
theorem qPair_self_eq_zero (he : P.e ≠ 0) {b : ℝ} (hb : 0 < b) {s : ℝ}
    (hs : -(4 * m₀ ^ 2) < s) : qPair Φ rep P.e b b s = 0 := by
  have h := qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he hb hb hb hs
  linear_combination -h

/-- **The heavy photon pair, given the face-limit identity** (step L6d, conditional on L6d3):
`‖qPair(b, d; s) - qPair(b, d; 0)‖ ≤ C/b` for `1 ≤ b ≤ d`, uniformly for `s ∈ [S₀, S] ∋ 0`. -/
theorem exists_norm_qPair_sub_heavy_le (he : P.e ≠ 0) {c S₀ S : ℝ} (hc : 0 < c)
    (hS₀ : -(4 * m₀ ^ 2) < S₀) (hS₀0 : S₀ ≤ 0) (h0S : 0 ≤ S) (hS : S < 2 * c ^ 2)
    (hId : ∀ s : ℝ, S₀ ≤ s → s ≤ S → FaceLimitId Φ rep P.e m₀ c s) :
    ∃ C : ℝ, ∀ s : ℝ, S₀ ≤ s → s ≤ S → ∀ b d : ℝ, 1 ≤ b → b ≤ d →
      ‖qPair Φ rep P.e b d s - qPair Φ rep P.e b d 0‖ ≤ C / b := by
  obtain ⟨C, hC⟩ := norm_qDens_sub_le Φ rep P hm₀ hmass hrep hPV₁ hPV₂ he hc hS₀ hS₀0 h0S hS
    hId
  refine ⟨2 * C, fun s h₀ h₁ b d hb hbd => ?_⟩
  have hs : -(4 * m₀ ^ 2) < s := hS₀.trans_le h₀
  have hs2 : s < 2 * c ^ 2 := h₁.trans_lt hS
  have h00 : -(4 * m₀ ^ 2) < 0 := hS₀.trans_le hS₀0
  have h02 : (0 : ℝ) < 2 * c ^ 2 := by positivity
  have hint : IntegrableOn (fun t : ℝ => C * t ^ (-(3 / 2) : ℝ)) (Ici (1 ^ 2)) := by
    rw [one_pow, integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul C
  have h := norm_qPair_sub_le_of_dens (Q := fun b d =>
      qPair Φ rep P.e b d s - qPair Φ rep P.e b d 0)
    (Δ := fun t => qDens Φ rep P.e m₀ c s t - qDens Φ rep P.e m₀ c 0 t) one_pos
    (fun b d hb hbd => by
      have hb0 : 0 < b := one_pos.trans_le hb
      obtain ⟨i1, e1⟩ := qPair_eq_integral Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he hb0 hbd hc hs hs2
      obtain ⟨i2, e2⟩ := qPair_eq_integral Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he hb0 hbd hc h00
        h02
      exact ⟨i1.sub i2, by rw [e1, e2, intervalIntegral.integral_sub i1 i2]⟩)
    (fun b hb => by
      have hb0 : 0 < b := one_pos.trans_le hb
      simp only [qPair_self_eq_zero Φ rep P hm₀ hmass hrep hPV₁ hPV₂ he hb0 hs,
        qPair_self_eq_zero Φ rep P hm₀ hmass hrep hPV₁ hPV₂ he hb0 h00, sub_zero])
    hint (fun t ht => hC s h₀ h₁ t (by simpa using ht)) b d hb hbd
  have hb0 : 0 < b := one_pos.trans_le hb
  have hb2 : 0 < b ^ 2 := by positivity
  refine h.trans (le_of_eq ?_)
  rw [integral_Ici_eq_integral_Ioi, integral_const_mul, integral_Ioi_rpow_neg_three_halves hb2,
    rpow_neg_half_eq_inv_sqrt hb2.le, Real.sqrt_sq hb0.le]
  field_simp

end Dens

end QED.GradedProof.RPi4

end
