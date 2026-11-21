/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajUV
public import QED.GradedProof.RPi4MajSplit
public import QED.GradedProof.RPi4FaceIdOneLoop

/-!
# (R-Π₄) step L10, T2.UV: the face rate `MajFaceRate` from per-class rates

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.UV, the
input `QED.GradedProof.RPi4.MajFaceRate`). Both limits `lim_u u qDens(c, s', u)` vanish (the
class-level face identity `QED.GradedProof.RPi4.faceId_faceClassGen`), so the face rate is a
decay bound for each of `u qDens(√s, s, u)` and `u qDens(√s, 0, u)`. Writing
`u qDens = -(i/c²) (∑_X (u vDens_X - L_X) + ∑_g (u σ_g + 3e²/16π²) fLim_g)` with
`∑_X L_X = (3e²/16π²) ∑_g fLim_g` (uniqueness of limits), the mass part is
`O(u^{-1/2}) · O(s)` and the class parts are what remains:

* `FaceIdRateCls G`: `‖u G(u, k) - L(s)‖ ≤ C s (s/u)^η` at `k = k'(s)` and at `k = k'_s(0)`
  (tilt `c = √s`), for `u ≥ s ≥ 1`;
* `faceIdRate_tendsto_of_rate`: such a bound identifies `L(s)` as the limit;
* `faceIdRate_norm_mul_qDens_le`: the estimate at one point;
* **`faceIdRate_of_cls`**: `FaceIdRateCls` of the three class densities and `MajTiltRay` of the
  single-flavour one-loop blocks give `MajFaceRate`;
* **`faceIdRate_cfg4`**: the same at `decCfg 1 4` (the blocks are discharged).
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

/-- **The per-class face rate along the ray**: at the tilt `c = √s`, for `u ≥ s ≥ 1`,
`‖u G(u, k'(s)) - L(s)‖ ≤ C s (s/u)^η` and `‖u G(u, k'_s(0)) - L₀(s)‖ ≤ C s (s/u)^η`. -/
def FaceIdRateCls (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ C η : ℝ, 0 < η ∧ ∃ L L₀ : ℝ → ℂ, ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
    ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s) - L s‖ ≤ C * s * (s / u) ^ η ∧
      ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) 0) - L₀ s‖ ≤ C * s * (s / u) ^ η

/-- `(s/u)^η ≤ (s/u)^η'` for `η' ≤ η` and `0 < s ≤ u`. -/
theorem faceIdRate_rpow_le {s u η η' : ℝ} (hs : 0 < s) (hsu : s ≤ u) (hη : η' ≤ η) :
    (s / u) ^ η ≤ (s / u) ^ η' :=
  Real.rpow_le_rpow_of_exponent_ge (div_pos hs (hs.trans_le hsu))
    ((div_le_one (hs.trans_le hsu)).2 hsu) hη

/-- `u^{-1/2} ≤ (s/u)^{1/2}` for `1 ≤ s` and `0 < u`. -/
theorem faceIdRate_rpow_neg_half_le {s u : ℝ} (hs : 1 ≤ s) (hu : 0 < u) :
    u ^ (-(1 / 2) : ℝ) ≤ (s / u) ^ (1 / 2 : ℝ) := by
  rw [Real.rpow_neg hu.le, ← Real.inv_rpow hu.le]
  refine Real.rpow_le_rpow (inv_nonneg.2 hu.le) ?_ (by norm_num)
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_right hs hu.le

/-- **A rate identifies the limit**: `‖u g(u) - L‖ ≤ K (s/u)^η` for `u ≥ s` gives
`u g(u) → L`. -/
theorem faceIdRate_tendsto_of_rate {g : ℝ → ℂ} {L : ℂ} {K s η : ℝ} (hs : 0 < s) (hη : 0 < η)
    (h : ∀ u : ℝ, s ≤ u → ‖(u : ℂ) * g u - L‖ ≤ K * (s / u) ^ η) :
    Tendsto (fun u : ℝ => (u : ℂ) * g u) atTop (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun u : ℝ => K * (s ^ η * u ^ (-η))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hη).const_mul (s ^ η)).const_mul K
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [eventually_ge_atTop s] with u hu
  have hu0 : 0 < u := hs.trans_le hu
  refine (h u hu).trans (le_of_eq ?_)
  rw [Real.div_rpow hs.le hu0.le, Real.rpow_neg hu0.le, div_eq_mul_inv]

section Classes

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- **The estimate at one point**: from per-class rates with limits summing to the mass
insertion (the face identity) and an `O(s)` bound on the one-loop blocks,
`‖u qDens(c, s', u)‖ ≤ (C_A + C_B + C_C + ∑_g S_g E_g) (s/u)^η` (`c² = s`, `η ≤ 1/2`). -/
theorem faceIdRate_norm_mul_qDens_le (e m₀ : ℝ) (hmass : ∀ g, Φ.mass g ≠ 0) {c s s' u η : ℝ}
    (hc2 : c ^ 2 = s) (hs : 1 ≤ s) (hsu : s ≤ u) (hη2 : η ≤ 1 / 2) {CA CB CC : ℝ}
    {LA LB LC : ℂ} (E : F → ℝ)
    (hA : ‖(u : ℂ) * vDens aVA baseVA cVA Φ e m₀ u (tiltVec c s') 2 3 - LA‖ ≤
      CA * s * (s / u) ^ η)
    (hB : ‖(u : ℂ) * vDens aVB baseVB cVB Φ e m₀ u (tiltVec c s') 2 3 - LB‖ ≤
      CB * s * (s / u) ^ η)
    (hC : ‖(u : ℂ) * vDens aVC baseVC cVC Φ e m₀ u (tiltVec c s') 2 3 - LC‖ ≤
      CC * s * (s / u) ^ η)
    (hL : LA + LB + LC = ((3 * e ^ 2 / (16 * Real.pi ^ 2) : ℝ) : ℂ) *
      ∑ g, fLim Φ rep e (Pi.single g 1) (tiltVec c s') 2 3)
    (hE : ∀ g, ‖fLim Φ rep e (Pi.single g 1) (tiltVec c s') 2 3‖ ≤ E g * s) :
    ‖(u : ℂ) * qDens Φ rep e m₀ c s' u‖ ≤
      (CA + CB + CC + ∑ g, e ^ 2 * |Φ.mass g| / (2 * Real.pi ^ 2) * E g) * (s / u) ^ η := by
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := hs0.trans_le hsu
  set κ : ℝ := 3 * e ^ 2 / (16 * Real.pi ^ 2) with hκ
  set Fg : F → ℂ := fun g => fLim Φ rep e (Pi.single g 1) (tiltVec c s') 2 3 with hFg
  set Sg : F → ℝ := fun g => e ^ 2 * |Φ.mass g| / (2 * Real.pi ^ 2) with hSg
  set X : ℝ := (s / u) ^ η with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg (div_pos hs0 hu0).le _
  have hhalf : u ^ (-(1 / 2) : ℝ) ≤ X :=
    (faceIdRate_rpow_neg_half_le hs hu0).trans (faceIdRate_rpow_le hs0 hsu hη2)
  -- the mass part
  have hM : ‖∑ g, ((u * sigma e (Φ.mass g) u + κ : ℝ) : ℂ) * Fg g‖ ≤
      (∑ g, Sg g * E g) * s * X := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_mul_sigma_add_le e (hmass g) hu0
    have hS0 : 0 ≤ Sg g := by simp only [hSg]; positivity
    have hE0 : 0 ≤ E g * s := (norm_nonneg _).trans (hE g)
    calc |u * sigma e (Φ.mass g) u + κ| * ‖Fg g‖
        ≤ (Sg g * u ^ (-(1 / 2) : ℝ)) * (E g * s) :=
          mul_le_mul h1 (hE g) (norm_nonneg _) (by positivity)
      _ ≤ (Sg g * X) * (E g * s) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhalf hS0) hE0
      _ = Sg g * E g * s * X := by ring
  -- the decomposition
  have key : (u : ℂ) * qDens Φ rep e m₀ c s' u = -I / ((c ^ 2 : ℝ) : ℂ) *
      (((u : ℂ) * vDens aVA baseVA cVA Φ e m₀ u (tiltVec c s') 2 3 - LA) +
        ((u : ℂ) * vDens aVB baseVB cVB Φ e m₀ u (tiltVec c s') 2 3 - LB) +
        ((u : ℂ) * vDens aVC baseVC cVC Φ e m₀ u (tiltVec c s') 2 3 - LC) +
        ∑ g, ((u * sigma e (Φ.mass g) u + κ : ℝ) : ℂ) * Fg g) := by
    have hs : ∑ g, ((u * sigma e (Φ.mass g) u + κ : ℝ) : ℂ) * Fg g =
        (u : ℂ) * ∑ g, (sigma e (Φ.mass g) u : ℂ) * Fg g + (κ : ℂ) * ∑ g, Fg g := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun g _ => by push_cast; ring
    rw [hs, ← hL]
    simp only [qDens, hFg]
    ring
  have hsum := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add hA hB)) hC)) hM)
  rw [key, norm_mul, norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by rw [hc2]; exact hs0), hc2]
  calc 1 / s * ‖_‖ ≤ 1 / s * (CA * s * X + CB * s * X + CC * s * X + (∑ g, Sg g * E g) * s * X) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (CA + CB + CC + ∑ g, Sg g * E g) * X := by field_simp

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **`MajFaceRate` from the per-class rates** of the three class densities and the single-flavour
one-loop blocks along the ray. -/
theorem faceIdRate_of_cls (P : Params) (he : P.e ≠ 0)
    (hA : FaceIdRateCls fun u k => vDens aVA baseVA cVA Φ P.e m₀ u k 2 3)
    (hB : FaceIdRateCls fun u k => vDens aVB baseVB cVB Φ P.e m₀ u k 2 3)
    (hC : FaceIdRateCls fun u k => vDens aVC baseVC cVC Φ P.e m₀ u k 2 3)
    (hFl : ∀ g, MajTiltRay (fLim Φ rep P.e (Pi.single g 1))) :
    MajFaceRate Φ rep P.e m₀ := by
  obtain ⟨CA, ηA, hηA, LA, LA₀, hCA⟩ := hA
  obtain ⟨CB, ηB, hηB, LB, LB₀, hCB⟩ := hB
  obtain ⟨CC, ηC, hηC, LC, LC₀, hCC⟩ := hC
  choose CF hCF using hFl
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  have hmg : ∀ g, Φ.mass g ≠ 0 := fun g => (hpos g).ne'
  set η : ℝ := min (min ηA ηB) (min ηC (1 / 2)) with hη_def
  have hη : 0 < η := lt_min (lt_min hηA hηB) (lt_min hηC (by norm_num))
  have hηA' : η ≤ ηA := (min_le_left _ _).trans (min_le_left _ _)
  have hηB' : η ≤ ηB := (min_le_left _ _).trans (min_le_right _ _)
  have hηC' : η ≤ ηC := (min_le_right _ _).trans (min_le_left _ _)
  have hη2 : η ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set E : F → ℝ := fun g => max |CF g| ‖projS (fLim Φ rep P.e (Pi.single g 1)) 0‖ with hE_def
  set K : ℝ := |CA| + |CB| + |CC| +
    ∑ g, P.e ^ 2 * |Φ.mass g| / (2 * Real.pi ^ 2) * E g with hK
  refine ⟨2 * K, η, hη, fun s hs u hsu => ?_⟩
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := hs0.trans_le hsu
  set c : ℝ := Real.sqrt s with hc_def
  have hc : 0 < c := Real.sqrt_pos.mpr hs0
  have hc2 : c ^ 2 = s := Real.sq_sqrt hs0.le
  have hm2 := pow_pos hm₀ 2
  set X : ℝ := (s / u) ^ η with hX
  -- the per-class bounds at the common exponent
  have tr : ∀ {C' η' u' : ℝ}, η ≤ η' → s ≤ u' → ∀ {x : ℂ}, ‖x‖ ≤ C' * s * (s / u') ^ η' →
      ‖x‖ ≤ |C'| * s * (s / u') ^ η := fun {C' η' u'} hle hu' {x} hx =>
    hx.trans (mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hs0.le)
      (faceIdRate_rpow_le hs0 hu' hle) (Real.rpow_nonneg (div_pos hs0 (hs0.trans_le hu')).le _)
      (mul_nonneg (abs_nonneg _) hs0.le))
  -- the class limits sum to the mass insertion
  have hlim : ∀ s' : ℝ, -(4 * m₀ ^ 2) < s' → s' < 2 * c ^ 2 → ∀ {LA' LB' LC' : ℂ} {η' : ℝ},
      0 < η' →
      (∀ u, s ≤ u → ‖(u : ℂ) * vDens aVA baseVA cVA Φ P.e m₀ u (tiltVec c s') 2 3 - LA'‖ ≤
        |CA| * s * (s / u) ^ η') →
      (∀ u, s ≤ u → ‖(u : ℂ) * vDens aVB baseVB cVB Φ P.e m₀ u (tiltVec c s') 2 3 - LB'‖ ≤
        |CB| * s * (s / u) ^ η') →
      (∀ u, s ≤ u → ‖(u : ℂ) * vDens aVC baseVC cVC Φ P.e m₀ u (tiltVec c s') 2 3 - LC'‖ ≤
        |CC| * s * (s / u) ^ η') →
      LA' + LB' + LC' = ((3 * P.e ^ 2 / (16 * Real.pi ^ 2) : ℝ) : ℂ) *
        ∑ g, fLim Φ rep P.e (Pi.single g 1) (tiltVec c s') 2 3 := by
    intro s' h1 h2 LA' LB' LC' η' hη' iA iB iC
    have tA := faceIdRate_tendsto_of_rate hs0 hη' iA
    have tB := faceIdRate_tendsto_of_rate hs0 hη' iB
    have tC := faceIdRate_tendsto_of_rate hs0 hη' iC
    have hid := faceId_faceClassGen P.e F Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ c s' hc h1 h2
    refine tendsto_nhds_unique ((tA.add tB).add tC |>.congr fun t => ?_) hid
    ring
  have bound : ∀ s' : ℝ, -(4 * m₀ ^ 2) < s' → s' < 2 * c ^ 2 → ∀ {LA' LB' LC' : ℂ},
      (∀ u, s ≤ u → ‖(u : ℂ) * vDens aVA baseVA cVA Φ P.e m₀ u (tiltVec c s') 2 3 - LA'‖ ≤
        |CA| * s * (s / u) ^ η) →
      (∀ u, s ≤ u → ‖(u : ℂ) * vDens aVB baseVB cVB Φ P.e m₀ u (tiltVec c s') 2 3 - LB'‖ ≤
        |CB| * s * (s / u) ^ η) →
      (∀ u, s ≤ u → ‖(u : ℂ) * vDens aVC baseVC cVC Φ P.e m₀ u (tiltVec c s') 2 3 - LC'‖ ≤
        |CC| * s * (s / u) ^ η) →
      (∀ g, ‖fLim Φ rep P.e (Pi.single g 1) (tiltVec c s') 2 3‖ ≤ E g * s) →
      ‖(u : ℂ) * qDens Φ rep P.e m₀ c s' u‖ ≤ K * X := by
    intro s' h1 h2 LA' LB' LC' iA iB iC hE
    exact faceIdRate_norm_mul_qDens_le Φ rep P.e m₀ hmg hc2 hs hsu hη2 E (iA u hsu) (iB u hsu)
      (iC u hsu) (hlim s' h1 h2 hη iA iB iC) hE
  -- the two ends
  have hs1 : -(4 * m₀ ^ 2) < s := by linarith
  have hs2 : s < 2 * c ^ 2 := by rw [hc2]; linarith
  have h01 : -(4 * m₀ ^ 2) < (0 : ℝ) := by linarith
  have h02 : (0 : ℝ) < 2 * c ^ 2 := by positivity
  have bS := bound s hs1 hs2 (fun u' hu' => tr hηA' hu' (hCA s hs u' hu').1)
    (fun u' hu' => tr hηB' hu' (hCB s hs u' hu').1) (fun u' hu' => tr hηC' hu' (hCC s hs u' hu').1)
    fun g => (hCF g s hs).1.trans (mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (le_max_left _ _)) hs0.le)
  have b0 := bound 0 h01 h02 (fun u' hu' => tr hηA' hu' (hCA s hs u' hu').2)
    (fun u' hu' => tr hηB' hu' (hCB s hs u' hu').2) (fun u' hu' => tr hηC' hu' (hCC s hs u' hu').2)
    fun g => by
      have h := projS_eq_tilt (tcov_fLim Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he (Pi.single g 1)) hc
        (by nlinarith : -(2 * m₀) ^ 2 < (0 : ℝ)) h02
      have hc2' : ((c ^ 2 : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]; positivity
      have e : fLim Φ rep P.e (Pi.single g 1) (tiltVec c 0) 2 3 =
          -(((c ^ 2 : ℝ) : ℂ) * projS (fLim Φ rep P.e (Pi.single g 1)) 0) := by
        rw [h]
        field_simp
      rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        hc2, mul_comm]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hs0.le
  rw [mul_sub]
  calc ‖(u : ℂ) * qDens Φ rep P.e m₀ c s u - (u : ℂ) * qDens Φ rep P.e m₀ c 0 u‖
      ≤ K * X + K * X := (norm_sub_le _ _).trans (add_le_add bS b0)
    _ = 2 * K * X := by ring

end Classes

/-- **`MajFaceRate` at `decCfg 1 4`** from the per-class rates of the three class densities (the
one-loop blocks along the ray are `maj_tiltRay_fLim_gen`). -/
theorem faceIdRate_cfg4 (P : Params) (he : P.e ≠ 0)
    (hA : FaceIdRateCls fun u k => vDens aVA baseVA cVA (decCfg 1 4) P.e 1 u k 2 3)
    (hB : FaceIdRateCls fun u k => vDens aVB baseVB cVB (decCfg 1 4) P.e 1 u k 2 3)
    (hC : FaceIdRateCls fun u k => vDens aVC baseVC cVC (decCfg 1 4) P.e 1 u k 2 3) :
    MajFaceRate (decCfg 1 4) (fun _ => 0) P.e 1 := by
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero (by norm_num : (0 : ℝ) ≤ 4)
  have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
    fun _ => rfl
  exact faceIdRate_of_cls (decCfg 1 4) (fun _ => 0) one_pos hmass hrep hpv.1 hpv.2 P he hA hB hC
    fun g => maj_tiltRay_fLim_gen P (decCfg 1 4) (fun _ => 0) hrep hpv.1 hpv.2 hmass he _

end QED.GradedProof.RPi4

end
