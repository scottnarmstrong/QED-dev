/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRayInt
public import QED.GradedProof.RPi4MajLipRay
public import QED.GradedProof.RPi4MajLipMid

/-!
# (R-Π₄) step L10, T2.UV: the face rate on one scale from per-class increment rates

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (the input
`QED.GradedProof.RPi4.MajFaceRateInc` of `QED.GradedProof.RPi4.MajLipIns`). Along the ray
`k'(σ) = tiltVec √σ σ`, `u qDens(√σ, σ, u) = -i Z(σ)/σ` with
`Z(σ) = ∑_X u vDens_X(u, k'(σ)) + ∑_g u σ_g(u) fLim_g(k'(σ))`. For `1 ≤ s' ≤ s ≤ 2s'`, `u ≥ s`,
`‖Z(s)/s - Z(s')/s'‖ ≤ (X + Y)(s - s')/s'` once `‖Z(s) - Z(s')‖ ≤ X (s - s')` and
`‖Z(s')‖ ≤ Y s'` (`QED.GradedProof.RPi4.majLip_norm_div_sub_le`):

* `Y` is the value face rate at `s'` (`QED.GradedProof.RPi4.faceIdRate_norm_mul_qDens_le`, from
  `FaceIdRateRay` of the three classes and the one-loop blocks);
* `X`: the class increments minus their limit increments, `FaceRateIncRay`, plus the mass part
  `∑_g (u σ_g + 3e²/16π²)(fLim_g(k'(s)) - fLim_g(k'(s')))`, which is `O(u^{-1/2})(s - s')`
  (`MajTiltRay` increments); the limit increments of the classes sum to
  `(3e²/16π²) ∑_g (fLim_g(k'(s)) - fLim_g(k'(s')))` by the class-level face identity at both
  points (`QED.GradedProof.RPi4.faceId_faceClassGen`).

* `FaceRateIncRay G`: the per-class increment rate
  `‖u (G(u, k'(s)) - G(u, k'(s'))) - (L(s) - L(s'))‖ ≤ C s (s/u)^η (s - s')/s'`;
* **`faceRateInc_of_ray`**: `MajFaceRateInc` from `FaceIdRateRay` and `FaceRateIncRay` of the
  three class densities and `MajTiltRay` of the one-loop blocks (any Pauli–Villars-closed flavour
  set);
* **`faceRateInc_decDil`**: the same at `decDil l (decCfg 1 4)`, `l ≥ 1`, `m₀ = l` (the shape of
  the last slot of `MajLipIns`; the blocks are discharged).
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

/-- **The per-class face rate on one scale along the ray**: for `1 ≤ s' ≤ s ≤ 2s'`, `u ≥ s`,
`‖u (G(u, k'(s)) - G(u, k'(s'))) - (L(s) - L(s'))‖ ≤ C s (s/u)^η (s - s')/s'`
(`k'(σ) = tiltVec √σ σ`). -/
def FaceRateIncRay (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ C η : ℝ, 0 < η ∧ ∃ L : ℝ → ℂ, ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' → ∀ u : ℝ, s ≤ u →
    ‖(u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s')) -
      (L s - L s')‖ ≤ C * s * (s / u) ^ η * ((s - s') / s')

/-- `s (s - s')/s' ≤ 2 (s - s')` for `0 < s' ≤ s ≤ 2s'`. -/
theorem faceRateInc_mul_eps_le {s s' : ℝ} (hs' : 0 < s') (hss : s' ≤ s) (hs2 : s ≤ 2 * s') :
    s * ((s - s') / s') ≤ 2 * (s - s') := by
  rw [mul_div_assoc', div_le_iff₀ hs']
  nlinarith

/-- `u qDens(√σ, σ, u) = -i Z(σ)/σ` along the ray. -/
theorem faceRateInc_mul_qDens_eq {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (rep : F → F) (e m₀ : ℝ) {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    (u : ℂ) * qDens Φ rep e m₀ (Real.sqrt σ) σ u = -I * ((u : ℂ) *
      (vDens aVA baseVA cVA Φ e m₀ u (tiltVec (Real.sqrt σ) σ) 2 3 +
        vDens aVB baseVB cVB Φ e m₀ u (tiltVec (Real.sqrt σ) σ) 2 3 +
        vDens aVC baseVC cVC Φ e m₀ u (tiltVec (Real.sqrt σ) σ) 2 3 +
        ∑ g, (sigma e (Φ.mass g) u : ℂ) *
          fLim Φ rep e (Pi.single g 1) (tiltVec (Real.sqrt σ) σ) 2 3) / (σ : ℂ)) := by
  simp only [qDens]
  rw [Real.sq_sqrt hσ.le]
  ring

section Classes

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- The class sum along the ray tends to the mass insertion (the face identity at `k'(σ)`). -/
theorem faceRateInc_faceClassId (e : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      (vDens aVA baseVA cVA Φ e m₀ t (tiltVec (Real.sqrt σ) σ) 2 3 +
        vDens aVB baseVB cVB Φ e m₀ t (tiltVec (Real.sqrt σ) σ) 2 3 +
        vDens aVC baseVC cVC Φ e m₀ t (tiltVec (Real.sqrt σ) σ) 2 3)) atTop
      (𝓝 (((3 * e ^ 2 / (16 * Real.pi ^ 2) : ℝ) : ℂ) *
        ∑ g, fLim Φ rep e (Pi.single g 1) (tiltVec (Real.sqrt σ) σ) 2 3)) := by
  have hm2 := pow_pos hm₀ 2
  exact faceId_faceClassGen e F Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ (Real.sqrt σ) σ
    (Real.sqrt_pos.mpr hσ) (by linarith) (by rw [Real.sq_sqrt hσ.le]; linarith)

/-- **`MajFaceRateInc` from the per-class rates and increment rates** of the three class
densities along the ray and `MajTiltRay` of the single-flavour one-loop blocks. -/
theorem faceRateInc_of_ray (e : ℝ)
    (hA : FaceIdRateRay fun u k => vDens aVA baseVA cVA Φ e m₀ u k 2 3)
    (hB : FaceIdRateRay fun u k => vDens aVB baseVB cVB Φ e m₀ u k 2 3)
    (hC : FaceIdRateRay fun u k => vDens aVC baseVC cVC Φ e m₀ u k 2 3)
    (hA' : FaceRateIncRay fun u k => vDens aVA baseVA cVA Φ e m₀ u k 2 3)
    (hB' : FaceRateIncRay fun u k => vDens aVB baseVB cVB Φ e m₀ u k 2 3)
    (hC' : FaceRateIncRay fun u k => vDens aVC baseVC cVC Φ e m₀ u k 2 3)
    (hFl : ∀ g, MajTiltRay (fLim Φ rep e (Pi.single g 1))) :
    MajFaceRateInc Φ rep e m₀ := by
  obtain ⟨CA, ηA, hηA, LA, hCA⟩ := hA
  obtain ⟨CB, ηB, hηB, LB, hCB⟩ := hB
  obtain ⟨CC, ηC, hηC, LC, hCC⟩ := hC
  obtain ⟨DA, θA, hθA, MA, hDA⟩ := hA'
  obtain ⟨DB, θB, hθB, MB, hDB⟩ := hB'
  obtain ⟨DC, θC, hθC, MC, hDC⟩ := hC'
  choose CF hCF using hFl
  have hmg : ∀ g, Φ.mass g ≠ 0 := fun g => (hm₀.trans_le (hmass g)).ne'
  set η : ℝ := min (min (min ηA ηB) (min ηC (1 / 2))) (min (min θA θB) θC) with hη_def
  have hη : 0 < η := lt_min (lt_min (lt_min hηA hηB) (lt_min hηC (by norm_num)))
    (lt_min (lt_min hθA hθB) hθC)
  have hηA' : η ≤ ηA := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hηB' : η ≤ ηB := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hηC' : η ≤ ηC := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη2 : η ≤ 1 / 2 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hθA' : η ≤ θA := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hθB' : η ≤ θB := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hθC' : η ≤ θC := (min_le_right _ _).trans (min_le_right _ _)
  set κ : ℝ := 3 * e ^ 2 / (16 * Real.pi ^ 2) with hκ
  set S : F → ℝ := fun g => e ^ 2 * |Φ.mass g| / (2 * Real.pi ^ 2) with hS
  have hS0 : ∀ g, 0 ≤ S g := fun g => by simp only [hS]; positivity
  set E : F → ℝ := fun g => |CF g| with hE
  set K₁ : ℝ := |CA| + |CB| + |CC| + ∑ g, S g * E g with hK₁
  set K₂ : ℝ := 2 * (|DA| + |DB| + |DC|) + ∑ g, S g * E g with hK₂
  have hSE : 0 ≤ ∑ g, S g * E g :=
    Finset.sum_nonneg fun g _ => mul_nonneg (hS0 g) (abs_nonneg _)
  have hK₁0 : 0 ≤ K₁ := by simp only [hK₁]; positivity
  have hK₂0 : 0 ≤ K₂ := by simp only [hK₂]; positivity
  refine ⟨K₂ + K₁, η, hη, fun s s' hs' hss hs2 u hsu => ?_⟩
  have hs1 : 1 ≤ s := hs'.trans hss
  have hs0 : 0 < s := by linarith
  have hs'0 : 0 < s' := by linarith
  have hu0 : 0 < u := hs0.trans_le hsu
  have hs'u : s' ≤ u := hss.trans hsu
  have hd : 0 ≤ s - s' := by linarith
  have hε : 0 ≤ (s - s') / s' := div_nonneg hd hs'0.le
  have hsε := faceRateInc_mul_eps_le hs'0 hss hs2
  set X : ℝ := (s / u) ^ η with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg (div_pos hs0 hu0).le _
  have hhalf : u ^ (-(1 / 2) : ℝ) ≤ X :=
    (faceIdRate_rpow_neg_half_le hs1 hu0).trans (faceIdRate_rpow_le hs0 hsu hη2)
  -- abbreviations along the ray
  set k : ℝ → Fin 4 → ℝ := fun σ => tiltVec (Real.sqrt σ) σ with hk
  set vA : ℝ → ℝ → ℂ := fun t σ => vDens aVA baseVA cVA Φ e m₀ t (k σ) 2 3 with hvA
  set vB : ℝ → ℝ → ℂ := fun t σ => vDens aVB baseVB cVB Φ e m₀ t (k σ) 2 3 with hvB
  set vC : ℝ → ℝ → ℂ := fun t σ => vDens aVC baseVC cVC Φ e m₀ t (k σ) 2 3 with hvC
  set Fg : ℝ → F → ℂ := fun σ g => fLim Φ rep e (Pi.single g 1) (k σ) 2 3 with hFg
  set Z : ℝ → ℂ := fun σ => (u : ℂ) * (vA u σ + vB u σ + vC u σ +
    ∑ g, (sigma e (Φ.mass g) u : ℂ) * Fg σ g) with hZ
  have hq : ∀ σ : ℝ, 0 < σ → (u : ℂ) * qDens Φ rep e m₀ (Real.sqrt σ) σ u =
      -I * (Z σ / (σ : ℂ)) := fun σ hσ => faceRateInc_mul_qDens_eq Φ rep e m₀ hσ u
  -- the value bound at `s'`: `‖Z(s')‖ ≤ K₁ X s'`
  have hY : ‖Z s'‖ ≤ K₁ * X * s' := by
    have tr : ∀ {C' η' : ℝ}, η ≤ η' → ∀ {x : ℂ}, ∀ t : ℝ, s' ≤ t →
        ‖x‖ ≤ C' * s' * (s' / t) ^ η' → ‖x‖ ≤ |C'| * s' * (s' / t) ^ η :=
      fun {C' η'} hle {x} t ht hx => hx.trans (mul_le_mul (mul_le_mul_of_nonneg_right
        (le_abs_self _) hs'0.le) (faceIdRate_rpow_le hs'0 ht hle)
        (Real.rpow_nonneg (div_pos hs'0 (hs'0.trans_le ht)).le _)
        (mul_nonneg (abs_nonneg _) hs'0.le))
    have iA : ∀ t, s' ≤ t → ‖(t : ℂ) * vA t s' - LA s'‖ ≤ |CA| * s' * (s' / t) ^ η :=
      fun t ht => tr hηA' t ht (hCA s' hs' t ht)
    have iB : ∀ t, s' ≤ t → ‖(t : ℂ) * vB t s' - LB s'‖ ≤ |CB| * s' * (s' / t) ^ η :=
      fun t ht => tr hηB' t ht (hCB s' hs' t ht)
    have iC : ∀ t, s' ≤ t → ‖(t : ℂ) * vC t s' - LC s'‖ ≤ |CC| * s' * (s' / t) ^ η :=
      fun t ht => tr hηC' t ht (hCC s' hs' t ht)
    have hL : LA s' + LB s' + LC s' = (κ : ℂ) * ∑ g, Fg s' g := by
      have tA := faceIdRate_tendsto_of_rate hs'0 hη iA
      have tB := faceIdRate_tendsto_of_rate hs'0 hη iB
      have tC := faceIdRate_tendsto_of_rate hs'0 hη iC
      have hid := faceRateInc_faceClassId Φ rep hm₀ hmass hrep hPV₁ hPV₂ e hs'0
      refine tendsto_nhds_unique ((tA.add tB).add tC |>.congr fun t => ?_) hid
      simp only [hvA, hvB, hvC]
      ring
    have hEg : ∀ g, ‖Fg s' g‖ ≤ E g * s' := fun g =>
      ((hCF g s' hs').1).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hs'0.le)
    have hc2 : Real.sqrt s' ^ 2 = s' := Real.sq_sqrt hs'0.le
    have hv := faceIdRate_norm_mul_qDens_le Φ rep e m₀ hmg hc2 hs' hs'u hη2 E (iA u hs'u)
      (iB u hs'u) (iC u hs'u) hL hEg
    rw [hq s' hs'0, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hs'0.le, div_le_iff₀ hs'0] at hv
    refine hv.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hK₁0) hs'0.le)
    exact Real.rpow_le_rpow (div_pos hs'0 hu0).le (div_le_div_of_nonneg_right hss hu0.le) hη.le
  -- the increment bound: `‖Z(s) - Z(s')‖ ≤ K₂ X (s - s')`
  have hZ' : ‖Z s - Z s'‖ ≤ K₂ * X * (s - s') := by
    have tr : ∀ {D θ : ℝ}, η ≤ θ → ∀ {x : ℂ}, ∀ t : ℝ, s ≤ t →
        ‖x‖ ≤ D * s * (s / t) ^ θ * ((s - s') / s') →
        ‖x‖ ≤ (|D| * s * ((s - s') / s')) * (s / t) ^ η :=
      fun {D θ} hle {x} t ht hx => hx.trans (by
        have h1 := faceIdRate_rpow_le hs0 ht hle
        have h2 : 0 ≤ (s / t) ^ θ := Real.rpow_nonneg (div_pos hs0 (hs0.trans_le ht)).le _
        have h3 : D * s * ((s - s') / s') ≤ |D| * s * ((s - s') / s') :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hs0.le) hε
        have h4 : 0 ≤ |D| * s * ((s - s') / s') := by positivity
        calc D * s * (s / t) ^ θ * ((s - s') / s') = (D * s * ((s - s') / s')) * (s / t) ^ θ :=
              by ring
          _ ≤ (|D| * s * ((s - s') / s')) * (s / t) ^ θ := mul_le_mul_of_nonneg_right h3 h2
          _ ≤ (|D| * s * ((s - s') / s')) * (s / t) ^ η := mul_le_mul_of_nonneg_left h1 h4)
    have jA : ∀ t, s ≤ t → ‖(t : ℂ) * (vA t s - vA t s') - (MA s - MA s')‖ ≤
        (|DA| * s * ((s - s') / s')) * (s / t) ^ η :=
      fun t ht => tr hθA' t ht (hDA s s' hs' hss hs2 t ht)
    have jB : ∀ t, s ≤ t → ‖(t : ℂ) * (vB t s - vB t s') - (MB s - MB s')‖ ≤
        (|DB| * s * ((s - s') / s')) * (s / t) ^ η :=
      fun t ht => tr hθB' t ht (hDB s s' hs' hss hs2 t ht)
    have jC : ∀ t, s ≤ t → ‖(t : ℂ) * (vC t s - vC t s') - (MC s - MC s')‖ ≤
        (|DC| * s * ((s - s') / s')) * (s / t) ^ η :=
      fun t ht => tr hθC' t ht (hDC s s' hs' hss hs2 t ht)
    -- the limit increments sum to the mass-insertion increment
    have hΔL : (MA s - MA s') + (MB s - MB s') + (MC s - MC s') =
        (κ : ℂ) * (∑ g, Fg s g - ∑ g, Fg s' g) := by
      have tA := faceIdRate_tendsto_of_rate hs0 hη jA
      have tB := faceIdRate_tendsto_of_rate hs0 hη jB
      have tC := faceIdRate_tendsto_of_rate hs0 hη jC
      have hid := (faceRateInc_faceClassId Φ rep hm₀ hmass hrep hPV₁ hPV₂ e hs0).sub
        (faceRateInc_faceClassId Φ rep hm₀ hmass hrep hPV₁ hPV₂ e hs'0)
      have h := tendsto_nhds_unique ((tA.add tB).add tC |>.congr fun t => ?_) hid
      · rw [h]
        ring
      · simp only [hvA, hvB, hvC]
        ring
    have hsum : ∑ g, ((u * sigma e (Φ.mass g) u + κ : ℝ) : ℂ) * (Fg s g - Fg s' g) =
        (u : ℂ) * ∑ g, (sigma e (Φ.mass g) u : ℂ) * Fg s g -
          (u : ℂ) * ∑ g, (sigma e (Φ.mass g) u : ℂ) * Fg s' g +
          (κ : ℂ) * (∑ g, Fg s g - ∑ g, Fg s' g) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      push_cast
      ring
    have key : Z s - Z s' =
        ((u : ℂ) * (vA u s - vA u s') - (MA s - MA s')) +
          ((u : ℂ) * (vB u s - vB u s') - (MB s - MB s')) +
          ((u : ℂ) * (vC u s - vC u s') - (MC s - MC s')) +
          ∑ g, ((u * sigma e (Φ.mass g) u + κ : ℝ) : ℂ) * (Fg s g - Fg s' g) := by
      rw [hsum]
      linear_combination hΔL
    -- the mass part
    have hM : ‖∑ g, ((u * sigma e (Φ.mass g) u + κ : ℝ) : ℂ) * (Fg s g - Fg s' g)‖ ≤
        (∑ g, S g * E g) * X * (s - s') := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := abs_mul_sigma_add_le e (hmg g) hu0
      have h2 : ‖Fg s g - Fg s' g‖ ≤ E g * (s - s') :=
        ((hCF g s hs1).2 s' hs' hss).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hd)
      calc |u * sigma e (Φ.mass g) u + κ| * ‖Fg s g - Fg s' g‖
          ≤ (S g * u ^ (-(1 / 2) : ℝ)) * (E g * (s - s')) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ ≤ (S g * X) * (E g * (s - s')) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhalf (hS0 g))
              (mul_nonneg (abs_nonneg _) hd)
        _ = S g * E g * X * (s - s') := by ring
    have hcls : ∀ D : ℝ, (|D| * s * ((s - s') / s')) * X ≤ 2 * |D| * X * (s - s') :=
      fun D => by
        have := mul_le_mul_of_nonneg_left hsε (abs_nonneg D)
        nlinarith
    rw [key]
    refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add ((jA u hsu).trans (hcls DA))
        ((jB u hsu).trans (hcls DB)))) ((jC u hsu).trans (hcls DC)))) hM)).trans (le_of_eq ?_)
    simp only [hK₂]
    ring
  -- assemble
  have hfin := majLip_norm_div_sub_le hs'0 hss (by positivity) (by positivity) hZ' hY
  rw [mul_sub, hq s hs0, hq s' hs'0, ← mul_sub, norm_mul, norm_neg, Complex.norm_I, one_mul]
  refine hfin.trans (le_of_eq ?_)
  ring

end Classes

/-- **`MajFaceRateInc` at the dilated configurations `decDil l (decCfg 1 4)`**, `l ≥ 1`,
`m₀ = l` (the last slot of `MajLipIns`), from the per-class rates and increment rates. -/
theorem faceRateInc_decDil (P : Params) (he : P.e ≠ 0) {l : ℝ} (hl : 1 ≤ l)
    (hA : FaceIdRateRay fun u k => vDens aVA baseVA cVA (decDil l (decCfg 1 4)) P.e l u k 2 3)
    (hB : FaceIdRateRay fun u k => vDens aVB baseVB cVB (decDil l (decCfg 1 4)) P.e l u k 2 3)
    (hC : FaceIdRateRay fun u k => vDens aVC baseVC cVC (decDil l (decCfg 1 4)) P.e l u k 2 3)
    (hA' : FaceRateIncRay fun u k => vDens aVA baseVA cVA (decDil l (decCfg 1 4)) P.e l u k 2 3)
    (hB' : FaceRateIncRay fun u k => vDens aVB baseVB cVB (decDil l (decCfg 1 4)) P.e l u k 2 3)
    (hC' : FaceRateIncRay fun u k => vDens aVC baseVC cVC (decDil l (decCfg 1 4)) P.e l u k 2 3) :
    MajFaceRateInc (decDil l (decCfg 1 4)) (fun _ => 0) P.e l := by
  have hl0 : 0 < l := one_pos.trans_le hl
  have hmass1 : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hm : ∀ g, l ≤ (decDil l (decCfg 1 4)).mass g := fun g => by
    simpa using majLip_decDil_mass_ge hl0.le hmass1 g
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero (by norm_num : (0 : ℝ) ≤ 4)
  have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
    fun _ => rfl
  have hpv₂ := majLip_decDil_pv₂ l hpv.2
  exact faceRateInc_of_ray (decDil l (decCfg 1 4)) (fun _ => 0) hl0 hm hrep hpv.1 hpv₂ P.e
    hA hB hC hA' hB' hC' fun g => maj_tiltRay_fLim_gen P (decDil l (decCfg 1 4)) (fun _ => 0)
      hrep hpv.1 hpv₂ (fun g => hl.trans (hm g)) he (Pi.single g 1)

end QED.GradedProof.RPi4

end
