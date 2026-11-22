/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncW7

/-!
# (R-Π₄) step L10, B-inc: the rate (B) of the two derivative terms of a piece

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10, the rate (B) of
the face-rate increment. Besides the Euler numerator, the `σ`-derivative of a merged piece along
the ray has the two terms `pieceFd n - pieceFw (n + 1)` (`faceIdRayD_hasDerivAt_pieceF`). Their
unscaled form is `pairDensD`, and its rate (B) is the analogue of
`QED.GradedProof.RPi4.faceIdRayB_vpPiece`, with `faceIdRayD_piece_rate` in place of
`faceIdRayB_piece_rate`:

* `faceIdRayE_cOneAt_congr`, `…_cTwoAt_congr`, `…_cThreeAt_congr`: the coefficients depend only on
  the value of the numerator; `faceIdRayE_coeff_int`: their integrability on a merged piece;
* `faceIdRayE_mul_absBr_le`, `faceIdRayE_norm_pieceF_le`, `faceIdRayE_integrableOn_pieceFdw`:
  domination and integrability of the two terms;
* `faceIdRayE_pieceFd_dilateQ`, `faceIdRayE_pieceFw_dilateQ`: their dilation;
* `pairDensD`, `faceIdRayE_rateB_of_scaled` (the assembly of `faceIdRayB_vpPiece`);
* **`faceIdRayE_vpPieceD`**, **`faceIdRayE_vpPieceD_of_nodes`**: the rate (B) of `pairDensD`.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.MassScaling
open QED.GradedProof.WI2 (dbl)
open QED.Integration.Feynman (simplexSet simplexPoint simplexPoint_mem_stdSimplex
  measurableSet_simplexSet)
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.TwoLoop.PauliZeroExplicit (numQuartic eval_numQuartic)

variable {m : ℕ}

/-! ### The coefficients depend only on the value of the numerator -/

section Congr

variable {Q Q' : LoopQuartic} (h : Q.eval = Q'.eval) (n : ℕ) (α : Fin (m + 1) → Fin 2 → ℝ)
  (p : Fin (m + 1) → Fin 4 → ℝ) (z : Fin (m + 1) → ℝ)

include h

theorem faceIdRayE_cOneAt_congr : cOneAt n Q α p z = cOneAt n Q' α p z := by
  have h1 : Q.evalC (loopComp (-loopShift α p z)) = Q'.evalC (loopComp (-loopShift α p z)) :=
    congrFun h _
  simp only [cOneAt, h1]

theorem faceIdRayE_cTwoAt_congr : cTwoAt n Q α p z = cTwoAt n Q' α p z := by
  simp only [cTwoAt, QED.TwoLoop.PauliZeroExplicit.NumeratorCongr.contractTwo_congr h
    (symanzikMatrix_transpose α _)]

theorem faceIdRayE_cThreeAt_congr : cThreeAt n Q α z = cThreeAt n Q' α z := by
  simp only [cThreeAt, QED.TwoLoop.PauliZeroExplicit.NumeratorCongr.contractFour_congr h
    (symanzikMatrix_transpose α _)]

end Congr

/-! ### Domination and integrability -/

/-- `z_γ absBr ≤ ∑ ‖z_γ cX‖ c^{-kX}` where `v ≥ c > 0` (or `U = 0`). -/
theorem faceIdRayE_mul_absBr_le {n : ℕ} {Q : LoopQuartic} {α : Fin (m + 1) → Fin 2 → ℝ}
    {p : Fin (m + 1) → Fin 4 → ℝ} {z : Fin (m + 1) → ℝ} {γ₀ : Fin (m + 1)} {c v : ℝ}
    (hc : 0 < c) (hz : 0 ≤ z γ₀) (hv : symanzikU α z ≠ 0 → c ≤ v) :
    z γ₀ * absBr n Q α p z v ≤ ‖(z γ₀ : ℂ) * cOneAt n Q α p z‖ * (c ^ (n - 3))⁻¹ +
      ‖(z γ₀ : ℂ) * cTwoAt n Q α p z‖ * (c ^ (n - 4))⁻¹ +
      ‖(z γ₀ : ℂ) * cThreeAt n Q α z‖ * (c ^ (n - 5))⁻¹ := by
  by_cases hU : symanzikU α z = 0
  · rw [faceIdRayD_absBr_eq_zero hU, mul_zero]
    positivity
  · have hcv := hv hU
    have hk : ∀ k : ℕ, (v ^ k)⁻¹ ≤ (c ^ k)⁻¹ := fun k =>
      inv_anti₀ (pow_pos hc k) (pow_le_pow_left₀ hc.le hcv k)
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hz, absBr]
    have h1 := mul_le_mul_of_nonneg_left (hk (n - 3)) (mul_nonneg hz (norm_nonneg
      (cOneAt n Q α p z)))
    have h2 := mul_le_mul_of_nonneg_left (hk (n - 4)) (mul_nonneg hz (norm_nonneg
      (cTwoAt n Q α p z)))
    have h3 := mul_le_mul_of_nonneg_left (hk (n - 5)) (mul_nonneg hz (norm_nonneg
      (cThreeAt n Q α z)))
    nlinarith

/-- `‖pieceF‖ ≤ ∑ ‖z_γ cX‖ c^{-kX}` where `v ≥ c > 0` (or `U = 0`). -/
theorem faceIdRayE_norm_pieceF_le {n : ℕ} {Q : LoopQuartic} {α : Fin (m + 1) → Fin 2 → ℝ}
    {pp : Fin (m + 1) → Fin 4 → ℝ} {M : Fin (m + 1) → ℝ} {γ₀ : Fin (m + 1)} {u c : ℝ}
    {z : Fin (m + 1) → ℝ} (hc : 0 < c) (hz : 0 ≤ z γ₀)
    (hv : symanzikU α z ≠ 0 → c ≤ symanzikV α pp M z + z γ₀ * u) :
    ‖pieceF n Q α pp M γ₀ u z‖ ≤ ‖(z γ₀ : ℂ) * cOneAt n Q α pp z‖ * (c ^ (n - 3))⁻¹ +
      ‖(z γ₀ : ℂ) * cTwoAt n Q α pp z‖ * (c ^ (n - 4))⁻¹ +
      ‖(z γ₀ : ℂ) * cThreeAt n Q α z‖ * (c ^ (n - 5))⁻¹ := by
  by_cases hU : symanzikU α z = 0
  · have : paramAtV n Q α pp z (symanzikV α pp M z + z γ₀ * u) = 0 := by simp [paramAtV, hU]
    rw [pieceF, this, mul_zero, norm_zero]
    positivity
  · have h := norm_paramAtV_le (n := n) (Q := Q) (α := α) (p := pp) (z := z) hc (hv hU)
    simp only [pieceF, norm_mul, Complex.norm_real, Real.norm_of_nonneg hz]
    have e : z γ₀ * (‖cOneAt n Q α pp z‖ * (c ^ (n - 3))⁻¹ +
        ‖cTwoAt n Q α pp z‖ * (c ^ (n - 4))⁻¹ + ‖cThreeAt n Q α z‖ * (c ^ (n - 5))⁻¹) =
        z γ₀ * ‖cOneAt n Q α pp z‖ * (c ^ (n - 3))⁻¹ +
        z γ₀ * ‖cTwoAt n Q α pp z‖ * (c ^ (n - 4))⁻¹ +
        z γ₀ * ‖cThreeAt n Q α z‖ * (c ^ (n - 5))⁻¹ := by ring
    rw [← e]
    exact mul_le_mul_of_nonneg_left h hz

/-- **Integrability of the two derivative terms** from that of the photon-weighted coefficients,
`v ≥ c > 0` and `V(0) ≥ 0` where `U ≠ 0`. -/
theorem faceIdRayE_integrableOn_pieceFdw {n : ℕ} (hn : 6 ≤ n) {Q : LoopQuartic}
    {α : Fin (m + 1) → Fin 2 → ℝ} {pp : Fin (m + 1) → Fin 4 → ℝ} {M : Fin (m + 1) → ℝ}
    {γ₀ : Fin (m + 1)} {u c : ℝ} (hc : 0 < c) (hu : 0 ≤ u)
    (k1 : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cOneAt n Q α pp (simplexPoint y))
      (simplexSet m))
    (k2 : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cTwoAt n Q α pp (simplexPoint y))
      (simplexSet m))
    (k3 : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cThreeAt n Q α (simplexPoint y))
      (simplexSet m))
    (hV : ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 →
      c ≤ symanzikV α pp M (simplexPoint y) + simplexPoint y γ₀ * u)
    (hB : ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 →
      0 ≤ symanzikV α pp 0 (simplexPoint y)) :
    IntegrableOn (fun y => pieceFd n Q α pp M γ₀ u (simplexPoint y)) (simplexSet m) ∧
      IntegrableOn (fun y => pieceFw (n + 1) Q α pp M γ₀ u (simplexPoint y)) (simplexSet m) := by
  have k1' : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) *
      cOneAt (n + 1) Q α pp (simplexPoint y)) (simplexSet m) := by
    refine IntegrableOn.congr_fun (k1.const_mul ((n - 3 : ℕ) : ℂ)) (fun y _ => ?_)
      (measurableSet_simplexSet m)
    simp only [faceIdRayD_cOneAt_succ n Q α pp _ (by omega)]
    ring
  have k2' : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) *
      cTwoAt (n + 1) Q α pp (simplexPoint y)) (simplexSet m) := by
    refine IntegrableOn.congr_fun (k2.const_mul ((n - 4 : ℕ) : ℂ)) (fun y _ => ?_)
      (measurableSet_simplexSet m)
    simp only [faceIdRayD_cTwoAt_succ n Q α pp _ (by omega)]
    ring
  have k3' : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) *
      cThreeAt (n + 1) Q α (simplexPoint y)) (simplexSet m) := by
    refine IntegrableOn.congr_fun (k3.const_mul ((n - 5 : ℕ) : ℂ)) (fun y _ => ?_)
      (measurableSet_simplexSet m)
    simp only [faceIdRayD_cThreeAt_succ n Q α _ hn]
    ring
  have hF := integrableOn_pieceF (n := n + 1) hc k1' k2' k3' hV
  have hzm : Measurable fun y : Fin m → ℝ => simplexPoint y γ₀ :=
    (continuous_apply γ₀).measurable.comp
      QED.Integration.TwoLoop.continuous_simplexPoint'.measurable
  have hVm : Measurable fun y : Fin m → ℝ =>
      symanzikV α pp M (simplexPoint y) + simplexPoint y γ₀ * u :=
    ((measurable_symanzikV α pp M).comp
      QED.Integration.TwoLoop.continuous_simplexPoint'.measurable).add (hzm.mul measurable_const)
  have hBm : Measurable fun y : Fin m → ℝ => symanzikV α pp 0 (simplexPoint y) :=
    (measurable_symanzikV α pp 0).comp QED.Integration.TwoLoop.continuous_simplexPoint'.measurable
  set g : (Fin m → ℝ) → ℝ := fun y => ((n - 3 : ℕ) : ℝ) *
    (‖(simplexPoint y γ₀ : ℂ) * cOneAt n Q α pp (simplexPoint y)‖ * (c ^ (n - 3))⁻¹ +
      ‖(simplexPoint y γ₀ : ℂ) * cTwoAt n Q α pp (simplexPoint y)‖ * (c ^ (n - 4))⁻¹ +
      ‖(simplexPoint y γ₀ : ℂ) * cThreeAt n Q α (simplexPoint y)‖ * (c ^ (n - 5))⁻¹) with hg_def
  have hg : IntegrableOn g (simplexSet m) :=
    (((k1.norm.mul_const _).add (k2.norm.mul_const _)).add (k3.norm.mul_const _)).const_mul _
  have hb : ∀ y ∈ simplexSet m, ((n - 3 : ℕ) : ℝ) * (simplexPoint y γ₀ *
      absBr n Q α pp (simplexPoint y)
        (symanzikV α pp M (simplexPoint y) + simplexPoint y γ₀ * u)) ≤ g y := fun y hy => by
    have hz := simplexPoint_mem_stdSimplex hy
    exact mul_le_mul_of_nonneg_left (faceIdRayE_mul_absBr_le hc (hz.1 γ₀) (hV y hy))
      (Nat.cast_nonneg _)
  constructor
  · have hm : AEStronglyMeasurable (fun y => pieceFd n Q α pp M γ₀ u (simplexPoint y))
        (volume.restrict (simplexSet m)) := by
      have e : (fun y => pieceFd n Q α pp M γ₀ u (simplexPoint y)) = fun y =>
          ((symanzikV α pp M (simplexPoint y) + simplexPoint y γ₀ * u : ℝ) : ℂ) *
            pieceF (n + 1) Q α pp M γ₀ u (simplexPoint y) :=
        funext fun y => faceIdRayD_pieceFd_eq n Q α pp M γ₀ u _
      rw [e]
      exact (Complex.measurable_ofReal.comp hVm).aestronglyMeasurable.mul hF.aestronglyMeasurable
    refine Integrable.mono' hg hm (ae_restrict_of_forall_mem (measurableSet_simplexSet m)
      fun y hy => ?_)
    have hz := simplexPoint_mem_stdSimplex hy
    exact (faceIdRayD_norm_pieceFd_le hn hu hz.1 (hB y hy)).trans (hb y hy)
  · have hm : AEStronglyMeasurable (fun y => pieceFw (n + 1) Q α pp M γ₀ u (simplexPoint y))
        (volume.restrict (simplexSet m)) :=
      (Complex.measurable_ofReal.comp hBm).aestronglyMeasurable.mul hF.aestronglyMeasurable
    refine Integrable.mono' hg hm (ae_restrict_of_forall_mem (measurableSet_simplexSet m)
      fun y hy => ?_)
    have hz := simplexPoint_mem_stdSimplex hy
    exact (faceIdRayD_norm_pieceFw_le hn hu hz.1 (hB y hy)).trans (hb y hy)

/-! ### The integrability of the coefficients on a merged piece -/

/-- **The coefficients of a merged piece are integrable** (the argument of
`faceIdRayB_vpPiece`): any representative `Q` of a numerator of degree `m - 2` with the refined
bound of the doubled data, at any momenta. -/
theorem faceIdRayE_coeff_int (base : Fin 5 → Fin 2 → ℤ) (hm : m = 5 ∨ m = 6)
    (sh : Fin (m + 2) → Fin 5) (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ))
    {E : Finset (Fin (m + 2))} (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hpoly : IsLoopPoly 2 (m + 1 - 3) F)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 F) {Q : LoopQuartic}
    (hQ : Q.eval = F) (p : Fin (m + 1) → Fin 4 → ℝ) :
    IntegrableOn (fun y => (simplexPoint y (Fin.last m) : ℂ) * cOneAt (m + 1) Q
      (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc)) p (simplexPoint y))
      (simplexSet m) ∧
    IntegrableOn (fun y => (simplexPoint y (Fin.last m) : ℂ) * cTwoAt (m + 1) Q
      (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc)) p (simplexPoint y))
      (simplexSet m) ∧
    IntegrableOn (fun y => (simplexPoint y (Fin.last m) : ℂ) * cThreeAt (m + 1) Q
      (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc)) (simplexPoint y))
      (simplexSet m) := by
  have hm0 : 0 < m := by omega
  set γ₀ := Fin.last m with hγ₀
  set α := castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc) with hα_def
  have hl : sh (Fin.last (m + 1)) = sh (Fin.last m).castSucc := by
    rw [(hsh _).2 (by simp), (hsh _).2 (by simp)]
  have hαd : castLoopMatrix (fun l => base (sh l)) = dbl γ₀ α :=
    comp_eq_dbl sh hl fun r s => (base r s : ℝ)
  have hcrit' : NoSubdivergenceRefined 2 E (dbl γ₀ α) :=
    hαd ▸ (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).2 hcrit
  obtain ⟨Qg, hq, hBQ, hQg⟩ := good_of_poly (n := m + 1) (by omega) hpoly (hαd ▸ hB)
  have hcoef : IntegrableOn (coeffOne Qg (dbl γ₀ α) (dbl γ₀ p)) (simplexSet (m + 1)) ∧
      IntegrableOn (coeffTwo Qg (dbl γ₀ α) (dbl γ₀ p)) (simplexSet (m + 1)) ∧
      IntegrableOn (coeffThree Qg (dbl γ₀ α)) (simplexSet (m + 1)) := by
    rcases hq with h7 | hq0
    · exact integrableOn_coeff Qg (dbl γ₀ α) (dbl γ₀ p) h7 hcrit' hBQ
    · exact integrableOn_coeff_cubic Qg (dbl γ₀ α) (dbl γ₀ p) hq0 (by omega) hcrit' hBQ
  have k1 := integrableOn_mul_of_dbl hm0 γ₀ (f := cOneAt (m + 1) Qg (dbl γ₀ α) (dbl γ₀ p))
    (g := cOneAt (m + 1) Qg α p) (cOneAt_dbl _ Qg α p · γ₀) hcoef.1
  have k2 := integrableOn_mul_of_dbl hm0 γ₀ (f := cTwoAt (m + 1) Qg (dbl γ₀ α) (dbl γ₀ p))
    (g := cTwoAt (m + 1) Qg α p) (cTwoAt_dbl _ Qg α p · γ₀) hcoef.2.1
  have k3 := integrableOn_mul_of_dbl hm0 γ₀ (f := cThreeAt (m + 1) Qg (dbl γ₀ α))
    (g := cThreeAt (m + 1) Qg α) (cThreeAt_dbl _ Qg α · γ₀) hcoef.2.2
  have he : Qg.eval = Q.eval := hQg.trans hQ.symm
  refine ⟨k1.congr_fun (fun y _ => ?_) (measurableSet_simplexSet m),
    k2.congr_fun (fun y _ => ?_) (measurableSet_simplexSet m),
    k3.congr_fun (fun y _ => ?_) (measurableSet_simplexSet m)⟩
  · simp only [faceIdRayE_cOneAt_congr he]
  · simp only [faceIdRayE_cTwoAt_congr he]
  · simp only [faceIdRayE_cThreeAt_congr he]

/-! ### The dilation of the two terms -/

section Dilate

variable (n : ℕ) (Q : LoopQuartic) (a : ℂ) {r : ℝ} (hr : r ≠ 0)
  (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (z : Fin (m + 1) → ℝ)

include hr

theorem faceIdRayE_pieceFd_dilateQ (hn : 5 ≤ n) (M : Fin (m + 1) → ℝ) (γ : Fin (m + 1))
    (u : ℝ) :
    pieceFd n (dilateQ a ((r⁻¹ : ℝ) : ℂ) Q) α (r • p) (r • M) γ (r ^ 2 * u) z =
      a * ((r⁻¹ : ℝ) : ℂ) ^ (2 * (n - 3)) * pieceFd n Q α p M γ u z := by
  rw [faceIdRayD_pieceFd_eq, faceIdRayD_pieceFd_eq,
    faceIdRayB_pieceF_dilateQ (n + 1) Q a hr α p z (by omega), faceIdRayB_symanzikV_smul]
  have e : n + 1 - 3 = (n - 3) + 1 := by omega
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr
  rw [e, mul_add, pow_add]
  push_cast
  field_simp

theorem faceIdRayE_pieceFw_dilateQ (hn : 5 ≤ n) (M : Fin (m + 1) → ℝ) (γ : Fin (m + 1))
    (u : ℝ) :
    pieceFw (n + 1) (dilateQ a ((r⁻¹ : ℝ) : ℂ) Q) α (r • p) (r • M) γ (r ^ 2 * u) z =
      a * ((r⁻¹ : ℝ) : ℂ) ^ (2 * (n - 3)) * pieceFw (n + 1) Q α p M γ u z := by
  have hV : symanzikV α (r • p) 0 z = r ^ 2 * symanzikV α p 0 z := by
    have h := faceIdRayB_symanzikV_smul α p z 0 r
    rwa [smul_zero] at h
  rw [pieceFw, pieceFw, faceIdRayB_pieceF_dilateQ (n + 1) Q a hr α p z (by omega), hV]
  have e : n + 1 - 3 = (n - 3) + 1 := by omega
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr
  rw [e, mul_add, pow_add]
  push_cast
  field_simp

end Dilate

/-! ### The unscaled derivative terms and the assembly along the ray -/

/-- **The two derivative terms of a piece, unscaled**:
`-π⁴ ∫_Δ (pieceFd (m + 1) - pieceFw (m + 2))` at the numerator `F`. -/
noncomputable def pairDensD (F : (Fin 2 → Fin 4 → ℝ) → ℂ) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (u : ℝ) : ℂ :=
  -((π : ℂ) ^ 4) * ∫ y in simplexSet m, (pieceFd (m + 1) (numQuartic F) α p M i u (simplexPoint y) -
    pieceFw (m + 1 + 1) (numQuartic F) α p M i u (simplexPoint y))

/-- **The assembly of `faceIdRayB_vpPiece`**: a value `-π⁴ κ(s) J(s, u/s)` along the ray, with
`‖κ(s)‖ ≤ s^D` and the scaled rate `‖t J(s, t) - L(s)‖ ≤ C (1 + s/m₀²)^N t^{-1/2}`, has the
rate (B). -/
theorem faceIdRayE_rateB_of_scaled {G : ℝ → (Fin 4 → ℝ) → ℂ} (J : {s : ℝ // 1 ≤ s} → ℝ → ℂ)
    (κ : {s : ℝ // 1 ≤ s} → ℂ) {D : ℕ} (hκb : ∀ s, ‖κ s‖ ≤ s.1 ^ D) {m₀ : ℝ} (hm₀ : 0 < m₀)
    {C : ℝ} {N' : ℕ} (L : {s : ℝ // 1 ≤ s} → ℂ)
    (hG : ∀ s : {s : ℝ // 1 ≤ s}, ∀ u : ℝ, s.1 ≤ u →
      G u (tiltVec (Real.sqrt s.1) s.1) = -((π : ℂ) ^ 4) * (κ s * J s (u / s.1)))
    (hC : ∀ (s : {s : ℝ // 1 ≤ s}) (t : ℝ), 1 ≤ t →
      ‖t • J s t - L s‖ ≤ C * (1 + (m₀ ^ 2 / s.1)⁻¹) ^ N' * t ^ (-(1 / 2) : ℝ)) :
    FaceIdRayRateB G := by
  set W : ℝ := 1 + (m₀ ^ 2)⁻¹
  refine ⟨π ^ 4 * |C| * W ^ N', ((D + N' + 2 : ℕ) : ℝ), by norm_cast; omega,
    fun s => if h : 1 ≤ s then -((π : ℂ) ^ 4) * κ ⟨s, h⟩ * (s : ℂ) * L ⟨s, h⟩ else 0,
    fun s hs u hu => ?_⟩
  set s' : {s : ℝ // 1 ≤ s} := ⟨s, hs⟩
  have hs0 : 0 < s := one_pos.trans_le hs
  have hu0 : 0 < u := hs0.trans_le hu
  have hu1 : 1 ≤ u / s := by rw [le_div_iff₀ hs0]; linarith
  simp only [hs, dite_true]
  rw [hG s' u hu]
  set J' := J s' (u / s)
  have e : (u : ℂ) * (-((π : ℂ) ^ 4) * (κ s' * J')) - -((π : ℂ) ^ 4) * κ s' * (s : ℂ) * L s' =
      -((π : ℂ) ^ 4) * κ s' * (s : ℂ) * ((u / s) • J' - L s') := by
    have hsC : (s : ℂ) ≠ 0 := ofReal_ne_zero.2 hs0.ne'
    rw [Complex.real_smul]
    push_cast
    field_simp
    ring
  rw [e]
  have hR := hC s' (u / s) hu1
  have hm2 : 0 ≤ (m₀ ^ 2)⁻¹ := by positivity
  have hW1 : 1 ≤ W := by simp only [W]; linarith
  have hWs : 1 + (m₀ ^ 2 / s)⁻¹ ≤ W * s := by
    rw [inv_div]
    have : s / m₀ ^ 2 = (m₀ ^ 2)⁻¹ * s := by ring
    simp only [W]; nlinarith
  have hpow : (1 + (m₀ ^ 2 / s)⁻¹) ^ N' ≤ W ^ N' * s ^ N' := by
    rw [← mul_pow]
    have h0 : 0 ≤ (m₀ ^ 2 / s)⁻¹ := by positivity
    exact pow_le_pow_left₀ (by linarith) hWs N'
  have hus : (u / s) ^ (-(1 / 2) : ℝ) ≤ s * u ^ (-(1 / 2) : ℝ) := by
    rw [Real.div_rpow hu0.le hs0.le, div_eq_mul_inv, ← Real.rpow_neg hs0.le, neg_neg, mul_comm]
    have h12 : s ^ (1 / 2 : ℝ) ≤ s := by
      simpa using Real.rpow_le_rpow_of_exponent_le hs (by norm_num : (1 / 2 : ℝ) ≤ 1)
    exact mul_le_mul_of_nonneg_right (by simpa using h12) (Real.rpow_nonneg hu0.le _)
  have hR' : ‖(u / s) • J' - L s'‖ ≤ |C| * (W ^ N' * s ^ N') * (s * u ^ (-(1 / 2) : ℝ)) := by
    have h0 : 0 ≤ (1 + (m₀ ^ 2 / s)⁻¹) ^ N' := by positivity
    have h1 : 0 ≤ (u / s) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by positivity) _
    refine hR.trans ?_
    calc C * (1 + (m₀ ^ 2 / s)⁻¹) ^ N' * (u / s) ^ (-(1 / 2) : ℝ)
        ≤ |C| * (1 + (m₀ ^ 2 / s)⁻¹) ^ N' * (u / s) ^ (-(1 / 2) : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) h0) h1
      _ ≤ |C| * (W ^ N' * s ^ N') * (s * u ^ (-(1 / 2) : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)) hus h1
            (by positivity)
  have hκs : ‖κ s'‖ ≤ s ^ D := hκb s'
  rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg hs0.le]
  have hsp : s ^ (((D + N' + 2 : ℕ)) : ℝ) = s ^ D * s ^ N' * s * s := by
    rw [Real.rpow_natCast]; ring
  rw [hsp]
  have hX : 0 ≤ ‖(u / s) • J' - L s'‖ := norm_nonneg _
  calc π ^ 4 * ‖κ s'‖ * s * ‖(u / s) • J' - L s'‖
      ≤ π ^ 4 * s ^ D * s * (|C| * (W ^ N' * s ^ N') * (s * u ^ (-(1 / 2) : ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκs (by positivity))
          hs0.le) hR' hX (by positivity)
    _ = _ := by ring

/-! ### The rate (B) of the two derivative terms of one piece -/

theorem faceIdRayE_dot_vhat : Minkowski.dot faceIdRayB_vhat faceIdRayB_vhat = 1 := by
  have h := faceIdRayB_tiltVec_eq (s := 1) zero_le_one
  rw [Real.sqrt_one, one_smul] at h
  rw [← h]
  exact dot_tiltVec (by norm_num)

section Piece

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])

include hflow hrow hrow4

/-- **The rate (B) of the two derivative terms of one merged piece**, under the hypotheses of
`faceIdRayB_vpPiece`. -/
theorem faceIdRayE_vpPieceD {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : ∀ k, IsLoopPoly 2 (m + 1 - 3) (N k))
    (hB : ∀ k, RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 (N k))
    (D : ℕ) (Q₁ Q₀ : {s : ℝ // 1 ≤ s} → LoopQuartic) {B₁ B₀ : ℝ} (hQ₁ : LQBdd Q₁ B₁)
    (hQ₀ : LQBdd Q₀ B₀)
    (he₁ : ∀ s : {s : ℝ // 1 ≤ s}, (dilateQ ((Real.sqrt s.1 : ℂ) ^ D)
      (((Real.sqrt s.1)⁻¹ : ℝ) : ℂ) (Q₁ s)).eval = N (tiltVec (Real.sqrt s.1) s.1))
    (he₀ : ∀ s, (Q₀ s).eval = (Q₁ s).eval) {d₁ d₀ : ℕ}
    (hQd₁ : ∀ s, LoopDegLe 1 d₁ (Q₁ s)) (hQd₀ : ∀ s, LoopDegLe 0 d₀ (Q₀ s))
    (hq : m = 6 ∨ ∀ s, (Q₁ s).quart = 0 ∧ (Q₀ s).quart = 0)
    (hd₁ : d₁ ≤ 3) (hd₀ : d₀ ≤ 3)
    (hA1 : 2 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card)
    (hd11 : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card = 2 →
      d₁ ≤ 1)
    (hR1 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![1, 0])
    (hA0 : 2 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card)
    (hd01 : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card = 2 →
      d₀ ≤ 1)
    (hR0 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![0, 1])
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l) :
    FaceIdRayRateB fun t k => pairDensD (N k)
      (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
      (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) t := by
  classical
  set γ₀ := Fin.last m with hγ₀
  set α := castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc) with hα_def
  set cs : Fin (m + 1) → ℝ := fun l => c (sh l.castSucc) with hcs
  have hrows := castLoopMatrix_rows base hrow hrow4 fun l : Fin (m + 1) => sh l.castSucc
  have hne : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 ↔ l ≠ γ₀ := fun l => by
    rw [Ne, hsh, Ne, Fin.ext_iff]
    simp only [Fin.val_castSucc, γ₀, Fin.val_last]
    have := l.isLt
    omega
  have hr10 : (![1, 0] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
    have := congrFun h 1; simp at this
  have hr01 : (![0, 1] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
    have := congrFun h 0; simp at this
  have huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀ := fun l => by
    constructor
    · intro h
      by_contra hl
      rcases (hrows l).1 ((hne l).2 hl) with h' | h'
      · exact hr10 (h'.symm.trans h)
      · exact hr01 (h'.symm.trans h)
    · intro hl
      exact (hrows l).2 (not_not.1 fun h => (hne l).1 h hl)
  have hrow3 : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1] := fun l => by
    by_cases h4 : sh l.castSucc = 4
    · exact Or.inr (Or.inr ((hrows l).2 h4))
    · rcases (hrows l).1 h4 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hf10 : (Finset.univ.filter fun l => α l ≠ ![1, 0]) =
      Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0] := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, α]
    exact not_congr (castLoopMatrix_eq_row10_iff _ l)
  have hf01 : (Finset.univ.filter fun l => α l ≠ ![0, 1]) =
      Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1] := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, α]
    exact not_congr (castLoopMatrix_eq_row01_iff _ l)
  -- the ray, the scaled masses and the unscaled quartics
  let ι := {s : ℝ // 1 ≤ s}
  set rr : ι → ℝ := fun s => Real.sqrt s.1 with hrr
  have hr1 : ∀ s : ι, 1 ≤ rr s := fun s => Real.one_le_sqrt.2 s.2
  have hr0 : ∀ s : ι, 0 < rr s := fun s => one_pos.trans_le (hr1 s)
  have hrs : ∀ s : ι, rr s ^ 2 = s.1 := fun s => Real.sq_sqrt (one_pos.le.trans s.2)
  set kk : ι → Fin 4 → ℝ := fun s => tiltVec (rr s) s.1 with hkk
  have hkv : ∀ s : ι, kk s = rr s • faceIdRayB_vhat := fun s =>
    faceIdRayB_tiltVec_eq (one_pos.le.trans s.2)
  set Mh : ι → Fin (m + 1) → ℝ := fun s => (rr s)⁻¹ • Ms with hMh
  have hMsc : ∀ s : ι, rr s • Mh s = Ms := fun s => by
    simp only [hMh, smul_smul, mul_inv_cancel₀ (hr0 s).ne', one_smul]
  have hpsc : ∀ s : ι, (fun i => cs i • kk s) = rr s • fun i => cs i • faceIdRayB_vhat :=
    fun s => by
      funext i
      simp only [hkv, Pi.smul_apply, smul_smul, mul_comm]
  set Qu : ι → LoopQuartic := fun s =>
    dilateQ ((rr s : ℂ) ^ D) (((rr s)⁻¹ : ℝ) : ℂ) (Q₁ s) with hQu
  have hferF : ∀ z : Fin (m + 1) → ℝ, ferSum α z =
      ∑ i ∈ Finset.univ.filter (fun i => sh (Fin.castSucc i) ≠ 4), z i := fun z => by
    simp only [ferSum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Ne, huniq l, hne l]
  have hdotu : ∀ s : ι, Minkowski.dot (kk s) (kk s) = s.1 := fun s => dot_tiltVec (by
    rw [hrs s]; linarith [s.2])
  -- P0 at the unscaled momenta (`k'(s)` is spacelike)
  have hVu : ∀ (s : ι) (z : Fin (m + 1) → ℝ), (∀ l, 0 ≤ z l) → ∑ l, z l = 1 →
      symanzikU α z ≠ 0 → m₀ ^ 2 * ferSum α z ≤ symanzikV α (fun i => cs i • kk s) Ms z := by
    intro s z hz _ hU
    have hP0 := symanzikV_vp_ge_fermion base c y₁ y₂ hflow (fun l : Fin (m + 1) => sh l.castSucc)
      Ms hm₀ hf (k := kk s) (by rw [hdotu s]; nlinarith [s.2]) hz hU
    rw [← hferF] at hP0
    have hmin : min 1 (1 + Minkowski.dot (kk s) (kk s) / (2 * m₀) ^ 2) = 1 := by
      rw [hdotu s]
      exact min_eq_left (le_add_of_nonneg_right (by have := s.2; positivity))
    rw [hmin, one_mul] at hP0
    exact hP0
  have hc₀u : 0 < m₀ ^ 2 := by positivity
  -- P0 at the scaled data
  have hVs : ∀ (s : ι) (z : Fin (m + 1) → ℝ), (∀ l, 0 ≤ z l) → ∑ l, z l = 1 →
      symanzikU α z ≠ 0 → m₀ ^ 2 / s.1 * ferSum α z ≤
        symanzikV α (fun i => cs i • faceIdRayB_vhat) (Mh s) z := by
    intro s z hz hz1 hU
    have h := hVu s z hz hz1 hU
    rw [hpsc s, ← hMsc s, symanzikV_smul, hrs s] at h
    have hs0 : 0 < s.1 := one_pos.trans_le s.2
    rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
    linarith
  -- `V(0) ≥ 0` at the scaled and the unscaled momenta
  have hB0s : ∀ (s : ι) (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → 0 ≤ symanzikV α (fun i => cs i • faceIdRayB_vhat) 0 w :=
    fun _ w hw _ hU => faceIdRayD_symanzikV_zero_nonneg base c y₁ y₂ hflow
      (fun l : Fin (m + 1) => sh l.castSucc) (by rw [faceIdRayE_dot_vhat]; norm_num) hw hU
  have hB0u : ∀ (s : ι) (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) →
      symanzikU α w ≠ 0 → 0 ≤ symanzikV α (fun i => cs i • kk s) 0 w :=
    fun s w hw hU => faceIdRayD_symanzikV_zero_nonneg base c y₁ y₂ hflow
      (fun l : Fin (m + 1) => sh l.castSucc) (by rw [hdotu s]; linarith [s.2]) hw hU
  -- the rates of the scaled families
  have hn : m + 1 = 7 ∨ (m + 1 = 6 ∧ ∀ s, (Q₁ s).quart = 0 ∧ (Q₁ s).quart = 0 ∧
      (Q₀ s).quart = 0) := by
    rcases hm with h5 | h6
    · refine Or.inr ⟨by omega, fun s => ?_⟩
      rcases hq with h | h
      · omega
      · exact ⟨(h s).1, (h s).1, (h s).2⟩
    · exact Or.inl (by omega)
  have hMb : ∀ (s : ι) l, |Mh s l| ≤ ∑ j, |Ms j| := fun s l => by
    have h1 : |Mh s l| ≤ |Ms l| := by
      simp only [hMh, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos (hr0 s)]
      exact mul_le_of_le_one_left (abs_nonneg _) (inv_le_one_of_one_le₀ (hr1 s))
    exact h1.trans (Finset.single_le_sum (f := fun j => |Ms j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ l))
  obtain ⟨⟨C, N', L, hC⟩, ⟨C', N'', L', hC'⟩⟩ := faceIdRayD_piece_rate (n := m + 1) (by omega)
    α γ₀ huniq hrow3 (by rwa [hf10])
    (by obtain ⟨l, hl⟩ := hR1; exact ⟨l, (castLoopMatrix_eq_row10_iff _ l).2 hl⟩)
    (by rwa [hf01])
    (by obtain ⟨l, hl⟩ := hR0; exact ⟨l, (castLoopMatrix_eq_row01_iff _ l).2 hl⟩)
    cs (fun _ => faceIdRayB_vhat) Mh Q₁ Q₁ Q₀ hQ₁ hQ₁ hQ₀ (fun _ => rfl) he₀
    (fun s => (hQd₁ s).mono hd₁)
    (fun h s => (hQd₁ s).mono (hd11 (by rwa [hf10] at h))) (fun s => (hQd₀ s).mono hd₀)
    (fun h s => (hQd₀ s).mono (hd01 (by rwa [hf01] at h))) hn (fun _ => le_rfl) hMb
    (fun s => m₀ ^ 2 / s.1) (fun s => by have := one_pos.trans_le s.2; positivity) hVs hB0s
  -- integrability of the two unscaled terms at every `t ≥ 1`
  have hint : ∀ (s : ι) (t : ℝ), 1 ≤ t →
      IntegrableOn (fun x => pieceFd (m + 1) (Qu s) α (fun i => cs i • kk s) Ms γ₀ t
        (simplexPoint x)) (simplexSet m) ∧
      IntegrableOn (fun x => pieceFw (m + 1 + 1) (Qu s) α (fun i => cs i • kk s) Ms γ₀ t
        (simplexPoint x)) (simplexSet m) := by
    intro s t ht
    obtain ⟨k1, k2, k3⟩ := faceIdRayE_coeff_int base hm sh hsh hcrit (hpoly (kk s)) (hB (kk s))
      (he₁ s) (fun i => cs i • kk s)
    refine faceIdRayE_integrableOn_pieceFdw (by omega) (lt_min hc₀u one_pos) (by linarith)
      k1 k2 k3 (fun y hy hU => ?_) (fun y hy hU =>
        hB0u s _ (simplexPoint_mem_stdSimplex hy).1 hU)
    have hz := simplexPoint_mem_stdSimplex hy
    have h1 := hVu s _ hz.1 hz.2 hU
    rw [ferSum_eq_one_sub huniq hz.2] at h1
    have hzγ := hz.1 γ₀
    have hzγ1 : simplexPoint y γ₀ ≤ 1 := by
      rw [← hz.2]
      exact Finset.single_le_sum (fun j _ => hz.1 j) (Finset.mem_univ γ₀)
    have e1 := mul_le_mul_of_nonneg_right (min_le_left (m₀ ^ 2) 1) (sub_nonneg.2 hzγ1)
    have e2 := mul_le_mul_of_nonneg_right (min_le_right (m₀ ^ 2) 1) hzγ
    have e3 := mul_le_mul_of_nonneg_left ht hzγ
    nlinarith
  -- the dilation
  set κ : ι → ℂ := fun s => (rr s : ℂ) ^ D * (((rr s)⁻¹ : ℝ) : ℂ) ^ (2 * (m + 1 - 3)) with hκ
  have hdil : ∀ (s : ι) (t : ℝ) (z : Fin (m + 1) → ℝ),
      pieceFd (m + 1) (Qu s) α (fun i => cs i • kk s) Ms γ₀ t z =
        κ s * pieceFd (m + 1) (Q₁ s) α (fun i => cs i • faceIdRayB_vhat) (Mh s) γ₀
          (t / s.1) z ∧
      pieceFw (m + 1 + 1) (Qu s) α (fun i => cs i • kk s) Ms γ₀ t z =
        κ s * pieceFw (m + 1 + 1) (Q₁ s) α (fun i => cs i • faceIdRayB_vhat) (Mh s) γ₀
          (t / s.1) z := by
    intro s t z
    have ht : rr s ^ 2 * (t / s.1) = t := by
      rw [hrs s]; field_simp [(one_pos.trans_le s.2).ne']
    have e := faceIdRayE_pieceFd_dilateQ (m + 1) (Q₁ s) ((rr s : ℂ) ^ D) (hr0 s).ne' α
      (fun i => cs i • faceIdRayB_vhat) z (by omega) (Mh s) γ₀ (t / s.1)
    have e' := faceIdRayE_pieceFw_dilateQ (m + 1) (Q₁ s) ((rr s : ℂ) ^ D) (hr0 s).ne' α
      (fun i => cs i • faceIdRayB_vhat) z (by omega) (Mh s) γ₀ (t / s.1)
    rw [ht, ← hpsc s, hMsc s] at e e'
    exact ⟨e, e'⟩
  have hκ0 : ∀ s, κ s ≠ 0 := fun s => by
    have := (hr0 s).ne'
    simp only [hκ]
    exact mul_ne_zero (pow_ne_zero _ (ofReal_ne_zero.2 this))
      (pow_ne_zero _ (ofReal_ne_zero.2 (inv_ne_zero this)))
  have hκb : ∀ s : ι, ‖κ s‖ ≤ s.1 ^ D := fun s => by
    have h1 : ‖(rr s : ℂ) ^ D‖ ≤ s.1 ^ D := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (hr0 s).le]
      refine pow_le_pow_left₀ (hr0 s).le ?_ D
      have := hr1 s
      nlinarith [hrs s]
    have h2 : ‖(((rr s)⁻¹ : ℝ) : ℂ) ^ (2 * (m + 1 - 3))‖ ≤ 1 := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (hr0 s).le)]
      exact pow_le_one₀ (inv_nonneg.2 (hr0 s).le) (inv_le_one_of_one_le₀ (hr1 s))
    simp only [hκ, norm_mul]
    calc _ ≤ s.1 ^ D * 1 := mul_le_mul h1 h2 (norm_nonneg _) (by have := s.2; positivity)
      _ = _ := mul_one _
  -- the scaled integrability
  have hIs : ∀ (s : ι) (t : ℝ), 1 ≤ t →
      IntegrableOn (fun x => pieceFd (m + 1) (Q₁ s) α (fun i => cs i • faceIdRayB_vhat) (Mh s)
        γ₀ t (simplexPoint x)) (simplexSet m) ∧
      IntegrableOn (fun x => pieceFw (m + 1 + 1) (Q₁ s) α (fun i => cs i • faceIdRayB_vhat)
        (Mh s) γ₀ t (simplexPoint x)) (simplexSet m) := by
    intro s t ht
    have hs0 : 0 < s.1 := one_pos.trans_le s.2
    have hts : 1 ≤ t * s.1 := by nlinarith [s.2]
    have e : t * s.1 / s.1 = t := by field_simp
    obtain ⟨h1, h2⟩ := hint s (t * s.1) hts
    refine ⟨IntegrableOn.congr_fun (Integrable.const_mul h1 (κ s)⁻¹) (fun x _ => ?_)
      (measurableSet_simplexSet m), IntegrableOn.congr_fun (Integrable.const_mul h2 (κ s)⁻¹)
      (fun x _ => ?_) (measurableSet_simplexSet m)⟩
    · simp only [(hdil s _ _).1, e, ← mul_assoc, inv_mul_cancel₀ (hκ0 s), one_mul]
    · simp only [(hdil s _ _).2, e, ← mul_assoc, inv_mul_cancel₀ (hκ0 s), one_mul]
  -- the numerator quartic of `pairDensD`
  have hnq : ∀ s : ι,
      pieceFd (m + 1) (numQuartic (N (kk s))) α (fun i => cs i • kk s) Ms γ₀ =
        pieceFd (m + 1) (Qu s) α (fun i => cs i • kk s) Ms γ₀ ∧
      pieceFw (m + 1 + 1) (numQuartic (N (kk s))) α (fun i => cs i • kk s) Ms γ₀ =
        pieceFw (m + 1 + 1) (Qu s) α (fun i => cs i • kk s) Ms γ₀ := fun s => by
    have h : (numQuartic (N (kk s))).eval = (Qu s).eval :=
      (eval_numQuartic ⟨Qu s, he₁ s⟩).trans (he₁ s).symm
    exact ⟨by funext u z; simp only [pieceFd, paramAtV_congr h],
      by funext u z; simp only [pieceFw, pieceF, paramAtV_congr h]⟩
  -- the two rates
  have R1 : FaceIdRayRateB fun t k => -((π : ℂ) ^ 4) * ∫ x in simplexSet m,
      pieceFd (m + 1) (numQuartic (N k)) α (fun i => cs i • k) Ms γ₀ t (simplexPoint x) := by
    refine faceIdRayE_rateB_of_scaled (fun s t => ∫ x in simplexSet m, pieceFd (m + 1) (Q₁ s) α
      (fun i => cs i • faceIdRayB_vhat) (Mh s) γ₀ t (simplexPoint x)) κ hκb hm₀ L
      (fun s u _ => ?_) fun s t ht => hC s t ht (hIs s t ht).1
    change -((π : ℂ) ^ 4) * ∫ x in simplexSet m, pieceFd (m + 1) (numQuartic (N (kk s))) α
      (fun i => cs i • kk s) Ms γ₀ u (simplexPoint x) = _
    rw [(hnq s).1]
    congr 1
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (measurableSet_simplexSet m) fun x _ => (hdil s u _).1
  have R2 : FaceIdRayRateB fun t k => -((π : ℂ) ^ 4) * ∫ x in simplexSet m,
      pieceFw (m + 1 + 1) (numQuartic (N k)) α (fun i => cs i • k) Ms γ₀ t (simplexPoint x) := by
    refine faceIdRayE_rateB_of_scaled (fun s t => ∫ x in simplexSet m, pieceFw (m + 1 + 1)
      (Q₁ s) α (fun i => cs i • faceIdRayB_vhat) (Mh s) γ₀ t (simplexPoint x)) κ hκb hm₀ L'
      (fun s u _ => ?_) fun s t ht => hC' s t ht (hIs s t ht).2
    change -((π : ℂ) ^ 4) * ∫ x in simplexSet m, pieceFw (m + 1 + 1) (numQuartic (N (kk s))) α
      (fun i => cs i • kk s) Ms γ₀ u (simplexPoint x) = _
    rw [(hnq s).2]
    congr 1
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (measurableSet_simplexSet m) fun x _ => (hdil s u _).2
  refine (R1.add (R2.const_mul (-1))).congr fun s hs u hu => ?_
  set s' : ι := ⟨s, hs⟩
  obtain ⟨h1, h2⟩ := hint s' u (hs.trans hu)
  rw [← (hnq s').1] at h1
  rw [← (hnq s').2] at h2
  change _ = -((π : ℂ) ^ 4) * ∫ y in simplexSet m,
    (pieceFd (m + 1) (numQuartic (N (kk s'))) α (fun i => cs i • kk s') Ms γ₀ u (simplexPoint y) -
      pieceFw (m + 1 + 1) (numQuartic (N (kk s'))) α (fun i => cs i • kk s') Ms γ₀ u
        (simplexPoint y))
  rw [integral_sub h1 h2]
  ring

/-- **The rate (B) of the two derivative terms of one merged piece**, with the numerator
hypotheses of `faceIdRayB_vpPiece_of_nodes`. -/
theorem faceIdRayE_vpPieceD_of_nodes {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : ∀ k, IsLoopPoly 2 (m + 1 - 3) (N k))
    (hB : ∀ k, RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 (N k))
    {d : ℕ} (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ) {d₁ d₀ : ℕ}
    (hQ₁ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧ LoopDegLe 1 d₁ Q ∧ (m = 6 ∨ Q.quart = 0))
    (hQ₀ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧ LoopDegLe 0 d₀ Q ∧ (m = 6 ∨ Q.quart = 0))
    (hd₁ : d₁ ≤ 3) (hd₀ : d₀ ≤ 3)
    (hA1 : 2 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card)
    (hd11 : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card = 2 →
      d₁ ≤ 1)
    (hR1 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![1, 0])
    (hA0 : 2 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card)
    (hd01 : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card = 2 →
      d₀ ≤ 1)
    (hR0 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![0, 1])
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l) :
    FaceIdRayRateB fun t k => pairDensD (N k)
      (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
      (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) t := by
  obtain ⟨Q₁, B₁, hB₁, he₁, hd₁', hq₁⟩ := faceIdRayB_numFamily N hk hQ₁
  obtain ⟨Q₀, B₀, hB₀, he₀, hd₀', hq₀⟩ := faceIdRayB_numFamily N hk hQ₀
  have hr : ∀ s : {s : ℝ // 1 ≤ s}, 0 < Real.sqrt s.1 := fun s =>
    Real.sqrt_pos.2 (one_pos.trans_le s.2)
  refine faceIdRayE_vpPieceD base c y₁ y₂ hflow hrow hrow4 hm sh hsh hcrit N hpoly hB (d + 4)
    Q₁ Q₀ hB₁ hB₀ (fun s => faceIdRayB_eval_dilateQ_inv (hr s) (d + 4) (he₁ s))
    (fun s => (he₀ s).trans (he₁ s).symm) hd₁' hd₀' ?_ hd₁ hd₀ hA1 hd11 hR1 hA0 hd01 hR0 hm₀ Ms
    hf
  rcases hq₁ with h | h
  · exact Or.inl h
  · rcases hq₀ with h' | h'
    · exact Or.inl h'
    · exact Or.inr fun s => ⟨h s, h' s⟩

end Piece

end QED.GradedProof.RPi4

end
