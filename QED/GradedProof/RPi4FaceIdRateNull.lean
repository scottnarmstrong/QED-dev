/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRate
public import QED.GradedProof.RPi4FaceIdRateCont

/-!
# (R-Π₄) step L10, T2.UV: the null end of the per-class face rate

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.UV, the
input `QED.GradedProof.RPi4.MajFaceRate`). At the null end `k'_s(0) = tiltVec √s 0` the class
densities are homogeneous: the class values at a photon pair are covariant limits, so
`vVal(a, b; tiltVec c 0)²³ = -c² projS(W)(0)` (`projS_eq_tilt`), and two continuous densities
with the same integrals over every interval of `(0, ∞)` agree. Hence
`u vDens(u, k'_s(0))²³ = s · u vDens(u, tiltVec 1 0)²³`, and the fixed-tilt heavy-photon rate
(`heavyRate_vDens_*` at `c = 1`) gives the null end of `FaceIdRateCls` with `η = 1/2`. What
remains of the face rate is its end at `k'(s)` (`FaceIdRateRay`).

* `faceIdRate_eqOn_of_integral_eq`: continuous densities with equal interval integrals agree;
* `faceIdRate_dens_tilt_null`: the homogeneity of a density from that of its pair values;
* `FaceIdRateRay`; `faceIdRate_cls_of_ray`: the null end from homogeneity and a fixed-tilt rate;
* `faceIdRate_cls_VA`, `faceIdRate_cls_VB`, `faceIdRate_cls_VC`;
* **`faceIdRate_of_ray`**, **`faceIdRate_cfg4_of_ray`**: `MajFaceRate` from `FaceIdRateRay` of
  the three class densities.
-/

@[expose] public section

open Complex Filter Topology Set MeasureTheory
open QED.WickModel (Params)

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

/-- **Continuous densities with equal integrals over every interval of `(0, ∞)` agree.** -/
theorem faceIdRate_eqOn_of_integral_eq {f g : ℝ → ℂ} (hf : ContinuousOn f (Ioi 0))
    (hg : ContinuousOn g (Ioi 0))
    (h : ∀ x y : ℝ, 0 < x → x < y → ∫ u in x..y, f u = ∫ u in x..y, g u) :
    ∀ u : ℝ, 0 < u → f u = g u := by
  intro x₀ hx₀
  set d : ℝ → ℂ := fun u => f u - g u with hd
  have hdc : ContinuousOn d (Ioi 0) := hf.sub hg
  have hii : ∀ x y : ℝ, 0 < x → x ≤ y → IntervalIntegrable d volume x y := fun x y hx hxy =>
    (hdc.mono fun u hu => (show (0 : ℝ) < u from hx.trans_le (by
      rw [uIcc_of_le hxy] at hu; exact hu.1))).intervalIntegrable
  have hfi : ∀ x y : ℝ, 0 < x → x ≤ y → IntervalIntegrable f volume x y := fun x y hx hxy =>
    (hf.mono fun u hu => (show (0 : ℝ) < u from hx.trans_le (by
      rw [uIcc_of_le hxy] at hu; exact hu.1))).intervalIntegrable
  have hgi : ∀ x y : ℝ, 0 < x → x ≤ y → IntervalIntegrable g volume x y := fun x y hx hxy =>
    (hg.mono fun u hu => (show (0 : ℝ) < u from hx.trans_le (by
      rw [uIcc_of_le hxy] at hu; exact hu.1))).intervalIntegrable
  have h0 : ∀ y : ℝ, x₀ / 2 ≤ y → ∫ u in x₀ / 2..y, d u = 0 := fun y hy => by
    rcases hy.lt_or_eq with hy | hy
    · rw [hd, intervalIntegral.integral_sub (hfi _ _ (by linarith) hy.le)
        (hgi _ _ (by linarith) hy.le), h _ _ (by linarith) hy, sub_self]
    · rw [hy, intervalIntegral.integral_same]
  have hD : HasDerivAt (fun y => ∫ u in x₀ / 2..y, d u) (d x₀) x₀ :=
    intervalIntegral.integral_hasDerivAt_right (hii _ _ (by linarith) (by linarith))
      (hdc.stronglyMeasurableAtFilter isOpen_Ioi x₀ hx₀)
      (hdc.continuousAt (isOpen_Ioi.mem_nhds hx₀))
  have hD0 : HasDerivAt (fun y => ∫ u in x₀ / 2..y, d u) 0 x₀ :=
    (hasDerivAt_const x₀ (0 : ℂ)).congr_of_eventuallyEq
      (by filter_upwards [lt_mem_nhds (show x₀ / 2 < x₀ by linarith)] with y hy
          using h0 y hy.le)
  have := hD.unique hD0
  simpa [hd, sub_eq_zero] using this

/-- **Homogeneity of a density at the null tilt** from that of its pair values: if `V(a, b; k) =
∫_{a²}^{b²} D(·, k)` below threshold, `D(·, k)` is continuous on `(0, ∞)` and
`V(a, b; tiltVec c 0) = c² V(a, b; tiltVec 1 0)`, then `D(u, tiltVec c 0) = c² D(u, tiltVec 1 0)`
for `u > 0`. -/
theorem faceIdRate_dens_tilt_null {m₀ : ℝ} (hm₀ : 0 < m₀) {V : ℝ → ℝ → (Fin 4 → ℝ) → ℂ}
    {D : ℝ → (Fin 4 → ℝ) → ℂ} (hP : PairInt m₀ V D)
    (hC : ∀ k : Fin 4 → ℝ, -(2 * m₀) ^ 2 < Minkowski.dot k k →
      ContinuousOn (fun u => D u k) (Ioi 0))
    {c : ℝ} (hc : 0 < c)
    (hV : ∀ a b : ℝ, 0 < a → a < b →
      V a b (tiltVec c 0) = ((c ^ 2 : ℝ) : ℂ) * V a b (tiltVec 1 0)) :
    ∀ u : ℝ, 0 < u → D u (tiltVec c 0) = ((c ^ 2 : ℝ) : ℂ) * D u (tiltVec 1 0) := by
  have hdot : ∀ c' : ℝ, 0 < c' → -(2 * m₀) ^ 2 < Minkowski.dot (tiltVec c' 0) (tiltVec c' 0) :=
    fun c' hc' => by
      rw [dot_tiltVec (by positivity)]
      nlinarith
  refine faceIdRate_eqOn_of_integral_eq (hC _ (hdot c hc))
    ((hC _ (hdot 1 one_pos)).const_smul (((c ^ 2 : ℝ) : ℂ)) |>.congr fun u _ => rfl)
    fun x y hx hxy => ?_
  have ha : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hab : Real.sqrt x < Real.sqrt y := Real.sqrt_lt_sqrt hx.le hxy
  have ex : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have ey : Real.sqrt y ^ 2 = y := Real.sq_sqrt (hx.le.trans hxy.le)
  obtain ⟨-, e1⟩ := hP _ (hdot c hc) _ _ ha hab
  obtain ⟨-, e2⟩ := hP _ (hdot 1 one_pos) _ _ ha hab
  rw [ex, ey] at e1 e2
  rw [← e1, hV _ _ ha hab, e2, intervalIntegral.integral_const_mul]

/-- **The face rate at the end `k'(s)`**: at the tilt `c = √s`, for `u ≥ s ≥ 1`,
`‖u G(u, k'(s)) - L(s)‖ ≤ C s (s/u)^η`. -/
def FaceIdRateRay (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ C η : ℝ, 0 < η ∧ ∃ L : ℝ → ℂ, ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
    ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s) - L s‖ ≤ C * s * (s / u) ^ η

/-- **The null end from homogeneity and a fixed-tilt rate.** -/
theorem faceIdRate_cls_of_ray {G : ℝ → (Fin 4 → ℝ) → ℂ}
    (hom : ∀ c : ℝ, 0 < c → ∀ u : ℝ, 0 < u →
      G u (tiltVec c 0) = ((c ^ 2 : ℝ) : ℂ) * G u (tiltVec 1 0))
    (hr : ∃ C : ℝ, ∃ L : ℂ, ∀ t : ℝ, 1 ≤ t →
      ‖(t : ℂ) * G t (tiltVec 1 0) - L‖ ≤ C * t ^ (-(1 / 2) : ℝ))
    (hR : FaceIdRateRay G) : FaceIdRateCls G := by
  obtain ⟨C, η, hη, L, hL⟩ := hR
  obtain ⟨C₀, L₀, hC₀⟩ := hr
  refine ⟨max C |C₀|, min η (1 / 2), lt_min hη (by norm_num), L, fun s => (s : ℂ) * L₀,
    fun s hs u hsu => ⟨?_, ?_⟩⟩
  · have hs0 : 0 < s := by linarith
    refine (hL s hs u hsu).trans (mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _)
      hs0.le) (faceIdRate_rpow_le hs0 hsu (min_le_left _ _))
      (Real.rpow_nonneg (div_pos hs0 (hs0.trans_le hsu)).le _) ?_)
    exact mul_nonneg ((abs_nonneg _).trans (le_max_right _ _)) hs0.le
  · have hs0 : 0 < s := by linarith
    have hu0 : 0 < u := hs0.trans_le hsu
    have hc2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
    have e : (u : ℂ) * G u (tiltVec (Real.sqrt s) 0) - (s : ℂ) * L₀ =
        (s : ℂ) * ((u : ℂ) * G u (tiltVec 1 0) - L₀) := by
      rw [hom _ (Real.sqrt_pos.2 hs0) u hu0, hc2]
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    have h1 := hC₀ u (hs.trans hsu)
    have h2 : C₀ * u ^ (-(1 / 2) : ℝ) ≤ |C₀| * (s / u) ^ (min η (1 / 2)) :=
      mul_le_mul (le_abs_self _) ((faceIdRate_rpow_neg_half_le hs hu0).trans
        (faceIdRate_rpow_le hs0 hsu (min_le_right _ _))) (Real.rpow_nonneg hu0.le _)
        (abs_nonneg _)
    have h3 : |C₀| * (s / u) ^ (min η (1 / 2)) ≤ max C |C₀| * (s / u) ^ (min η (1 / 2)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (div_pos hs0 hu0).le _)
    calc s * ‖(u : ℂ) * G u (tiltVec 1 0) - L₀‖
        ≤ s * (max C |C₀| * (s / u) ^ (min η (1 / 2))) :=
          mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) hs0.le
      _ = max C |C₀| * s * (s / u) ^ (min η (1 / 2)) := by ring

/-- The pair values of a covariant class at the null tilt: `W(tiltVec c 0)²³ = c² W(tiltVec 1 0)²³`
for a covariant `W` with `projS` read at `0`. -/
theorem faceIdRate_tcov_null {T : ℝ} {W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (hcov : TCov T W)
    (hT : 0 < T) {c : ℝ} (hc : 0 < c) :
    W (tiltVec c 0) 2 3 = ((c ^ 2 : ℝ) : ℂ) * W (tiltVec 1 0) 2 3 := by
  have hT2 : -T ^ 2 < 0 := by nlinarith
  have h1 := projS_eq_tilt hcov hc hT2 (by positivity)
  have h2 := projS_eq_tilt hcov one_pos hT2 (by norm_num)
  have hc2 : ((c ^ 2 : ℝ) : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
  rw [h2] at h1
  simp only [one_pow, Complex.ofReal_one, div_one] at h1
  field_simp at h1
  linear_combination h1

/-- **The null end of one class from its parts**: pair integrals, continuity, homogeneity of
the pair values at the null tilt and the fixed-tilt heavy-photon rate at `c = 1`. -/
theorem faceIdRate_cls_of_parts {m₀ : ℝ} (hm₀ : 0 < m₀) {V : ℝ → ℝ → (Fin 4 → ℝ) → ℂ}
    {D : ℝ → (Fin 4 → ℝ) → ℂ} (hP : PairInt m₀ V D)
    (hC : ∀ k : Fin 4 → ℝ, -(2 * m₀) ^ 2 < Minkowski.dot k k →
      ContinuousOn (fun u => D u k) (Ioi 0))
    (hV : ∀ c : ℝ, 0 < c → ∀ a b : ℝ, 0 < a → a < b →
      V a b (tiltVec c 0) = ((c ^ 2 : ℝ) : ℂ) * V a b (tiltVec 1 0))
    (hr : HeavyRate (tiltBase 1 (-(2 * m₀ ^ 2)) 0) (tiltDir 1 (-(2 * m₀ ^ 2)) 0) D)
    (hR : FaceIdRateRay D) : FaceIdRateCls D := by
  refine faceIdRate_cls_of_ray (fun c hc => faceIdRate_dens_tilt_null hm₀ hP hC hc (hV c hc))
    ?_ hR
  obtain ⟨C, L, hCL⟩ := hr
  obtain ⟨u₀, hu₀, he⟩ := exists_tiltVec_eq_lineK (c := 1) (S₀ := -(2 * m₀ ^ 2)) (S := 0)
    (by nlinarith) le_rfl
  exact ⟨C, L u₀, fun t ht => by rw [he]; exact hCL u₀ hu₀ t ht⟩

/-- The segment of the fixed tilt `c = 1` over `[-2m₀², 0]` stays above `-2m₀²`. -/
theorem faceIdRate_seg {m₀ : ℝ} (u : ℝ) (hu : |u| ≤ 1 / 2) :
    -(2 * m₀ ^ 2) ≤ Minkowski.dot (lineK (tiltBase 1 (-(2 * m₀ ^ 2)) 0)
      (tiltDir 1 (-(2 * m₀ ^ 2)) 0) u) (lineK (tiltBase 1 (-(2 * m₀ ^ 2)) 0)
      (tiltDir 1 (-(2 * m₀ ^ 2)) 0) u) :=
  (dot_lineK_tilt_mem (c := 1) (by norm_num) (by nlinarith [sq_nonneg m₀]) hu).1

theorem faceIdRate_dot_null {m₀ c : ℝ} (hm₀ : 0 < m₀) (hc : 0 < c) :
    -(4 * m₀ ^ 2) < Minkowski.dot (tiltVec c 0) (tiltVec c 0) := by
  rw [dot_tiltVec (by positivity)]
  nlinarith


section Classes

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **The class `VA`: the null end.** -/
theorem faceIdRate_cls_VA (e : ℝ)
    (hR : FaceIdRateRay fun u k => vDens aVA baseVA cVA Φ e m₀ u k 2 3) :
    FaceIdRateCls fun u k => vDens aVA baseVA cVA Φ e m₀ u k 2 3 :=
  faceIdRate_cls_of_parts hm₀ (pairInt_vVal_VA Φ hm₀ hmass e 2 3)
    (fun _ hk => faceIdRate_continuousOn_vDens_VA Φ hm₀ hmass e hk 2 3)
    (fun c hc a b ha hab => by
      have hb : 0 < b := ha.trans hab
      rw [← wV_eq_vVal_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ e ha hb (faceIdRate_dot_null hm₀ hc),
        ← wV_eq_vVal_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ e ha hb (faceIdRate_dot_null hm₀ one_pos)]
      exact faceIdRate_tcov_null (tcov_wV Φ (vpjv_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ e ha hb).1)
        (by positivity) hc)
    (heavyRate_vDens_VA Φ hm₀ hmass e (by nlinarith) faceIdRate_seg 2 3) hR

/-- **The class `VB`: the null end.** -/
theorem faceIdRate_cls_VB (e : ℝ)
    (hR : FaceIdRateRay fun u k => vDens aVB baseVB cVB Φ e m₀ u k 2 3) :
    FaceIdRateCls fun u k => vDens aVB baseVB cVB Φ e m₀ u k 2 3 :=
  faceIdRate_cls_of_parts hm₀ (pairInt_vVal_VB Φ hm₀ hmass e 2 3)
    (fun _ hk => faceIdRate_continuousOn_vDens_VB Φ hm₀ hmass e hk 2 3)
    (fun c hc a b ha hab => by
      have hb : 0 < b := ha.trans hab
      rw [← wV_eq_vVal_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ e ha hb (faceIdRate_dot_null hm₀ hc),
        ← wV_eq_vVal_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ e ha hb (faceIdRate_dot_null hm₀ one_pos)]
      exact faceIdRate_tcov_null (tcov_wV Φ (vpjv_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ e ha hb).1)
        (by positivity) hc)
    (heavyRate_vDens_VB Φ hm₀ hmass e (by nlinarith) faceIdRate_seg 2 3) hR

/-- **The class `VC`: the null end.** -/
theorem faceIdRate_cls_VC (e : ℝ)
    (hR : FaceIdRateRay fun u k => vDens aVC baseVC cVC Φ e m₀ u k 2 3) :
    FaceIdRateCls fun u k => vDens aVC baseVC cVC Φ e m₀ u k 2 3 :=
  faceIdRate_cls_of_parts hm₀ (pairInt_vVal_VC Φ hm₀ hmass e 2 3)
    (fun _ hk => faceIdRate_continuousOn_vDens_VC Φ hm₀ hmass e hk 2 3)
    (fun c hc a b ha hab => by
      have hb : 0 < b := ha.trans hab
      rw [← wV_eq_vVal_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ e ha hb (faceIdRate_dot_null hm₀ hc),
        ← wV_eq_vVal_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ e ha hb (faceIdRate_dot_null hm₀ one_pos)]
      exact faceIdRate_tcov_null (tcov_wV Φ (vpjv_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ e ha hb).1)
        (by positivity) hc)
    (heavyRate_vDens_VC Φ hm₀ hmass e (by nlinarith) faceIdRate_seg 2 3) hR

/-- **`MajFaceRate` from the face rate at the end `k'(s)`** of the three class densities. -/
theorem faceIdRate_of_ray (P : Params) (he : P.e ≠ 0)
    (hA : FaceIdRateRay fun u k => vDens aVA baseVA cVA Φ P.e m₀ u k 2 3)
    (hB : FaceIdRateRay fun u k => vDens aVB baseVB cVB Φ P.e m₀ u k 2 3)
    (hC : FaceIdRateRay fun u k => vDens aVC baseVC cVC Φ P.e m₀ u k 2 3)
    (hFl : ∀ g, MajTiltRay (fLim Φ rep P.e (Pi.single g 1))) :
    MajFaceRate Φ rep P.e m₀ :=
  faceIdRate_of_cls Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he
    (faceIdRate_cls_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hA)
    (faceIdRate_cls_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hB)
    (faceIdRate_cls_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hC) hFl

end Classes

/-- **`MajFaceRate` at `decCfg 1 4`** from the face rate at the end `k'(s)` of the three class
densities (this is the remaining analytic input). -/
theorem faceIdRate_cfg4_of_ray (P : Params) (he : P.e ≠ 0)
    (hA : FaceIdRateRay fun u k => vDens aVA baseVA cVA (decCfg 1 4) P.e 1 u k 2 3)
    (hB : FaceIdRateRay fun u k => vDens aVB baseVB cVB (decCfg 1 4) P.e 1 u k 2 3)
    (hC : FaceIdRateRay fun u k => vDens aVC baseVC cVC (decCfg 1 4) P.e 1 u k 2 3) :
    MajFaceRate (decCfg 1 4) (fun _ => 0) P.e 1 := by
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero (by norm_num : (0 : ℝ) ≤ 4)
  have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
    fun _ => rfl
  exact faceIdRate_of_ray (decCfg 1 4) (fun _ => 0) one_pos hmass hrep hpv.1 hpv.2 P he hA hB hC
    fun g => maj_tiltRay_fLim_gen P (decCfg 1 4) (fun _ => 0) hrep hpv.1 hpv.2 hmass he _

end QED.GradedProof.RPi4

end
