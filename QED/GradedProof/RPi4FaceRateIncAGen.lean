/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncARed
public import QED.GradedProof.RPi4FaceIdRayAQGen
public import QED.GradedProof.RPi4MajLIncGen

/-!
# (R-Π₄) step L10: (A) for increments of a photon-mass density from a majorant

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. Under the
hypotheses of `QED.GradedProof.RPi4.faceIdRayAQ_pow_pairDens` (the majorant of the value bound
(A) with a power loss) and the integrability of the integrands along the ray, the density
satisfies (A) for increments at every photon mass, `QED.GradedProof.RPi4.FaceRateIncAQPow`.

Along the ray the integrand is `u z_γ ∑_t X_t(s)` with
`X_t(s) = QED.GradedProof.RPi4.majIncX (m+1) t T₁ T₂ T₃ (V₀ + s B) s`, the coefficients `Tⱼ`
independent of `s` (`faceRateIncAQ_integrand_eq`). For `1 ≤ s' ≤ s ≤ 2s'` the increment of
`X_t` is at most `(m+1) ε` times its absolute coefficient sum at `s'`
(`QED.GradedProof.RPi4.majIncX_sub_le`), `ε = (s - s')/s'`, and that sum times `u z_γ` is the
quantity the value proof bounds by `K s'^{1-δ} u^a F`.

* `faceRateIncAQ_integrand_eq`;
* **`faceRateIncAQ_pow_pairDens`**.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.MassScaling
open QED.TwoLoop.LimitCovariance
open QED.GradedProof.WI2 (ehat ehat_qsum)
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.PauliZeroExplicit (numQuartic eval_numQuartic)

variable {m : ℕ}

/-- **The integrand along the ray in the form `majIncX`.** -/
theorem faceRateIncAQ_integrand_eq (α : Fin (m + 1) → Fin 2 → ℝ) (cs : Fin (m + 1) → ℝ)
    (M : Fin (m + 1) → ℝ) (γ : Fin (m + 1)) (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (Q : Fin 3 → LoopQuartic)
    (hN : ∀ r : ℝ, 1 ≤ r → ∀ ℓ, N (r • majRayVec 1) ℓ =
      ∑ t : Fin 3, ((r : ℂ) ^ 2) ^ (t : ℕ) * (Q t).eval (r⁻¹ • ℓ))
    {σ : ℝ} (hσ : 1 ≤ σ) (u : ℝ) (x : Fin m → ℝ) :
    (u : ℂ) * ((simplexPoint x γ : ℂ) * paramAtV (m + 1) (numQuartic (N (majRayVec σ))) α
      (fun l => cs l • majRayVec σ) (simplexPoint x)
      (symanzikV α (fun l => cs l • majRayVec σ) (Function.update M γ 0) (simplexPoint x) +
        simplexPoint x γ * u)) =
    ((u * simplexPoint x γ : ℝ) : ℂ) * ∑ t : Fin 3, majIncX (m + 1) t
      (((m + 1 - 4).factorial : ℂ) * faceIdRayAPOne (Q t) α (fun i => cs i • majRayVec 1) x)
      (((m + 1 - 5).factorial : ℂ) / 2 *
        faceIdRayAPTwo (Q t) α (fun i => cs i • majRayVec 1) x)
      (((m + 1 - 6).factorial : ℂ) / 4 * faceIdRayAPThree (Q t) α x)
      ((∑ i, simplexPoint x i * Function.update M γ 0 i ^ 2 + simplexPoint x γ * u) +
        σ * remainder α (simplexPoint x) cs) σ := by
  have hσ0 : 0 < σ := by linarith
  set r := Real.sqrt σ with hr_def
  have hr1 : 1 ≤ r := by rw [hr_def, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hσ
  have hr0 : r ≠ 0 := by positivity
  have hr2 : r ^ 2 = σ := Real.sq_sqrt hσ0.le
  set p₁ : Fin (m + 1) → Fin 4 → ℝ := fun i => cs i • majRayVec 1 with hp₁
  have hmom : (fun i => cs i • majRayVec σ) = r • p₁ := by
    funext i
    simp only [hp₁, Pi.smul_apply, maj_majRayVec_eq hσ0.le]
    exact smul_comm _ _ _
  set R : LoopQuartic := qsum Finset.univ (fun t : Fin 3 => ((σ : ℂ)) ^ (t : ℕ))
    (fun t => dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q t)) with hR
  have hRe : R.eval = N (majRayVec σ) := by
    funext ℓ
    rw [maj_majRayVec_eq hσ0.le, hN r hr1]
    simp only [hR, eval_qsum, eval_dilateQ, one_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 2
    rw [← hr2]; push_cast; ring
  have hQe : (numQuartic (N (majRayVec σ))).eval = R.eval :=
    (eval_numQuartic ⟨R, hRe⟩).trans hRe.symm
  set z := simplexPoint x with hz
  set V := (∑ i, z i * Function.update M γ 0 i ^ 2 + z γ * u) + σ * remainder α z cs with hV
  have hVe : symanzikV α (fun l => cs l • majRayVec σ) (Function.update M γ 0) z + z γ * u =
      V := by
    rw [maj_symanzikV_ray α _ z cs hσ0.le, hV]
    ring
  rw [paramAtV_congr hQe, hVe, hmom]
  have hsplit : paramAtV (m + 1) R α (r • p₁) z V = ∑ t : Fin 3, ((σ : ℂ)) ^ (t : ℕ) *
      paramAtV (m + 1) (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q t)) α (r • p₁) z V := by
    simp only [paramAtV, hR, ehat_qsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hsplit, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hz, faceIdRayAP_paramAtV_eq, faceIdRayAP_one_dilateQ _ _ _ hr0,
    faceIdRayAP_two_dilateQ _ _ _ hr0, faceIdRayAP_three_dilateQ]
  simp only [majIncX]
  push_cast
  ring

/-- **(A) for increments at every photon mass of a photon-mass density from the majorant of
`QED.GradedProof.RPi4.faceIdRayAQ_pow_pairDens`** and the integrability of the integrands along
the ray. -/
theorem faceRateIncAQ_pow_pairDens (hm : 5 ≤ m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (cs : Fin (m + 1) → ℝ) (M : Fin (m + 1) → ℝ) (γ : Fin (m + 1)) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hM : ∀ i, i ≠ γ → m₀ ^ 2 ≤ M i ^ 2) (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (Q : Fin 3 → LoopQuartic)
    (hN : ∀ r : ℝ, 1 ≤ r → ∀ ℓ, N (r • majRayVec 1) ℓ =
      ∑ t : Fin 3, ((r : ℂ) ^ 2) ^ (t : ℕ) * (Q t).eval (r⁻¹ • ℓ))
    (hq : 6 ≤ m ∨ ∀ t, (Q t).quart = 0)
    (hMaj : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∃ F : (Fin m → ℝ) → ℝ,
      IntegrableOn F (simplexSet m) ∧ ∀ᵐ x ∂(volume.restrict (simplexSet m)),
        0 < remainder α (simplexPoint x) cs ∧
          simplexPoint x γ ^ a * remainder α (simplexPoint x) cs ^ (-δ) *
            faceIdRayAPSum Q α (fun i => cs i • majRayVec 1) cs x ≤ F x)
    (hInt : ∀ σ : ℝ, 1 ≤ σ → ∀ u : ℝ, 1 ≤ u → IntegrableOn (fun y => (simplexPoint y γ : ℂ) *
      paramAtV (m + 1) (numQuartic (N (majRayVec σ))) α (fun l => cs l • majRayVec σ)
        (simplexPoint y)
        (symanzikV α (fun l => cs l • majRayVec σ) (Function.update M γ 0) (simplexPoint y) +
          simplexPoint y γ * u)) (simplexSet m)) :
    FaceRateIncAQPow fun u k => pairDens (N k) α (fun l => cs l • k) M γ u := by
  obtain ⟨δ, hδ, hδ1, hMaj⟩ := hMaj
  refine ⟨δ, hδ, fun a ha => ?_⟩
  set a' := min a 1 with ha'_def
  have ha' : 0 < a' := lt_min ha one_pos
  have ha'1 : a' ≤ 1 := min_le_right _ _
  obtain ⟨F, hF, hFx⟩ := hMaj a' ha' ha'1
  set c₁ : ℝ := ((m + 1 - 4).factorial : ℝ) with hc₁
  set c₂ : ℝ := ((m + 1 - 5).factorial : ℝ) / 2 with hc₂
  set c₃ : ℝ := ((m + 1 - 6).factorial : ℝ) / 4 with hc₃
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hc₃0 : 0 ≤ c₃ := by positivity
  set c₀ : ℝ := min (m₀ ^ 2) 1 with hc₀_def
  have hc₀ : 0 < c₀ := lt_min (by positivity) one_pos
  have hc₀1 : c₀ ≤ 1 := min_le_right _ _
  set Kc : ℝ := (c₁ + c₂ + c₃) * c₀ ^ (-(m : ℝ)) with hKc
  have hK0 : 0 ≤ Kc := by positivity
  have hF0 : 0 ≤ ∫ x in simplexSet m, F x := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hFx, ae_restrict_mem (QED.Integration.Feynman.measurableSet_simplexSet m)]
      with x ⟨hB, hx⟩ hxS
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    refine le_trans ?_ hx
    have := faceIdRayAPSum_nonneg Q α (fun i => cs i • majRayVec 1) cs x hB.le
    have := Real.rpow_nonneg (hz.1 γ) a'
    have := Real.rpow_nonneg hB.le (-δ)
    positivity
  refine ⟨π ^ 4 * ((m + 1 : ℝ) * Kc) * ∫ x in simplexSet m, F x,
    fun s s' hs' hss hs2 u hu => ?_⟩
  have hs : 1 ≤ s := hs'.trans hss
  have hs0 : 0 < s := by linarith
  have hs'0 : 0 < s' := by linarith
  have hu0 : 0 < u := by linarith
  set ε : ℝ := (s - s') / s' with hε_def
  have hε : 0 ≤ ε := div_nonneg (by linarith) hs'0.le
  set p₁ : Fin (m + 1) → Fin 4 → ℝ := fun i => cs i • majRayVec 1 with hp₁
  set f : ℝ → (Fin m → ℝ) → ℂ := fun σ y => (simplexPoint y γ : ℂ) *
    paramAtV (m + 1) (numQuartic (N (majRayVec σ))) α (fun l => cs l • majRayVec σ)
      (simplexPoint y)
      (symanzikV α (fun l => cs l • majRayVec σ) (Function.update M γ 0) (simplexPoint y) +
        simplexPoint y γ * u) with hf
  set g : (Fin m → ℝ) → ℝ := fun x =>
    (m + 1 : ℝ) * ε * (Kc * s' ^ (1 - δ) * u ^ a' * F x) with hg
  have hgi : IntegrableOn g (simplexSet m) :=
    (hF.const_mul ((m + 1 : ℝ) * ε * (Kc * s' ^ (1 - δ) * u ^ a'))).congr
      (Filter.Eventually.of_forall fun x => by simp only [hg]; ring)
  have hpt : ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      ‖(u : ℂ) * f s x - (u : ℂ) * f s' x‖ ≤ g x := by
    filter_upwards [hFx, ae_restrict_mem (QED.Integration.Feynman.measurableSet_simplexSet m)]
      with x ⟨hB, hx⟩ hxS
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    set z := simplexPoint x with hz_def
    set B := remainder α z cs with hB_def
    set V₀ := ∑ i, z i * Function.update M γ 0 i ^ 2 + z γ * u with hV₀_def
    have hV₀ : c₀ ≤ V₀ := faceIdRayAP_le_V₀ M γ hM hz.1 hz.2 hu
    have hV₀0 : 0 < V₀ := hc₀.trans_le hV₀
    set W := V₀ + s' * B with hW_def
    have hW0 : 0 < W := by nlinarith [mul_pos hs'0 hB]
    set w := u * z γ with hw_def
    have hw0 : 0 ≤ w := mul_nonneg hu0.le (hz.1 γ)
    have hVm0 : 0 ≤ ∑ i, z i * Function.update M γ 0 i ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hz.1 i) (sq_nonneg _)
    have hwW : w ≤ W := by
      have := mul_pos hs'0 hB
      simp only [hw_def, hW_def, hV₀_def]
      linarith [mul_comm u (z γ)]
    set T₁ : Fin 3 → ℂ := fun t => ((m + 1 - 4).factorial : ℂ) * faceIdRayAPOne (Q t) α p₁ x
      with hT₁
    set T₂ : Fin 3 → ℂ := fun t => ((m + 1 - 5).factorial : ℂ) / 2 *
      faceIdRayAPTwo (Q t) α p₁ x with hT₂
    set T₃ : Fin 3 → ℂ := fun t => ((m + 1 - 6).factorial : ℂ) / 4 * faceIdRayAPThree (Q t) α x
      with hT₃
    have hfs : ∀ σ : ℝ, 1 ≤ σ → (u : ℂ) * f σ x = ((w : ℝ) : ℂ) * ∑ t : Fin 3,
        majIncX (m + 1) t (T₁ t) (T₂ t) (T₃ t) (V₀ + σ * B) σ := fun σ hσ =>
      faceRateIncAQ_integrand_eq α cs M γ N Q hN hσ u x
    rw [hfs s hs, hfs s' hs', ← mul_sub, ← Finset.sum_sub_distrib,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
    -- the increment of each `majIncX`
    have hinc : ‖∑ t : Fin 3, (majIncX (m + 1) t (T₁ t) (T₂ t) (T₃ t) (V₀ + s * B) s -
        majIncX (m + 1) t (T₁ t) (T₂ t) (T₃ t) (V₀ + s' * B) s')‖ ≤
        (m + 1 : ℝ) * ε * ∑ t : Fin 3, majIncA (m + 1) t (T₁ t) (T₂ t) (T₃ t) W s' := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun t _ => ?_
      have h := majIncX_sub_le (m := m + 1) (by omega) (Nat.lt_succ_iff.mp t.isLt) (T₁ t)
        (T₂ t) (T₃ t) hV₀0 hB.le hs' hss hs2
      push_cast at h
      exact h
    -- the absolute sum at `s'` is the value bound of `faceIdRayAQ_pow_pairDens` at `s'`
    set Γ := c₀ ^ (-(m : ℝ)) * (s' ^ (1 - δ) * B ^ (-δ) * w ^ a') with hΓ
    have hWW : V₀ + s' * B ≤ W := le_rfl
    have hn1 : (1 : ℝ) + δ ≤ ((m + 1 - 3 : ℕ) : ℝ) - 1 := by
      have : (3 : ℝ) ≤ ((m + 1 - 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ m + 1 - 3)
      linarith
    have hn2 : δ ≤ ((m + 1 - 4 : ℕ) : ℝ) - 1 := by
      have : (2 : ℝ) ≤ ((m + 1 - 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ m + 1 - 4)
      linarith
    have hKn : ∀ j : ℕ, 3 ≤ j → ((m + 1 - j : ℕ) : ℝ) ≤ (m : ℝ) := fun j hj => by
      exact_mod_cast (by omega : m + 1 - j ≤ m)
    have g1 := faceIdRayAP_gain_zero (n := m + 1 - 3) hs'0 hc₀ hc₀1 hV₀ hB hWW hw0 hwW hδ.le
      ha' ha'1 (by linarith) (hKn 3 le_rfl)
    have g1' := faceIdRayAP_gain_one (n := m + 1 - 3) hs'0 hc₀ hc₀1 hV₀ hB hWW hw0 hwW hδ.le
      ha' ha'1 hn1 (hKn 3 le_rfl)
    have g2 := faceIdRayAP_gain_zero (n := m + 1 - 4) hs'0 hc₀ hc₀1 hV₀ hB hWW hw0 hwW hδ.le
      ha' ha'1 hn2 (hKn 4 (by norm_num))
    have g3 : ∀ t, ‖faceIdRayAPThree (Q t) α x‖ * (s' * (w / W ^ (m + 1 - 5))) ≤
        ‖faceIdRayAPThree (Q t) α x‖ * Γ := fun t => by
      rcases hq with h6 | hq0
      · have hn3 : δ ≤ ((m + 1 - 5 : ℕ) : ℝ) - 1 := by
          have : (2 : ℝ) ≤ ((m + 1 - 5 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 2 ≤ m + 1 - 5)
          linarith
        exact mul_le_mul_of_nonneg_left (faceIdRayAP_gain_zero hs'0 hc₀ hc₀1 hV₀ hB hWW hw0 hwW
          hδ.le ha' ha'1 hn3 (hKn 5 (by norm_num))) (norm_nonneg _)
      · simp [faceIdRayAPThree, contractFour_eq_zero_of_quart _ _ (hq0 t)]
    have hsum := faceIdRayAP_sum_le (o := fun t => ‖faceIdRayAPOne (Q t) α p₁ x‖)
      (w := fun t => ‖faceIdRayAPTwo (Q t) α p₁ x‖) (h := fun t => ‖faceIdRayAPThree (Q t) α x‖)
      hs' hB (by positivity : 0 ≤ w / W ^ (m + 1 - 3)) (by positivity : 0 ≤ w / W ^ (m + 1 - 4))
      (by positivity : 0 ≤ w / W ^ (m + 1 - 5)) hc₁0 hc₂0 hc₃0 (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) g1 g1' g2 g3
    have habs : w * ∑ t : Fin 3, majIncA (m + 1) t (T₁ t) (T₂ t) (T₃ t) W s' =
        c₁ * ‖faceIdRayAPOne (Q 0) α p₁ x‖ * (w / W ^ (m + 1 - 3)) +
          (c₂ * ‖faceIdRayAPTwo (Q 0) α p₁ x‖ * (w / W ^ (m + 1 - 4)) +
            c₃ * ‖faceIdRayAPThree (Q 0) α x‖ * (w / W ^ (m + 1 - 5))) / s' +
        s' * (c₁ * ‖faceIdRayAPOne (Q 1) α p₁ x‖ * (w / W ^ (m + 1 - 3)) +
          (c₂ * ‖faceIdRayAPTwo (Q 1) α p₁ x‖ * (w / W ^ (m + 1 - 4)) +
            c₃ * ‖faceIdRayAPThree (Q 1) α x‖ * (w / W ^ (m + 1 - 5))) / s') +
        s' ^ 2 * (c₁ * ‖faceIdRayAPOne (Q 2) α p₁ x‖ * (w / W ^ (m + 1 - 3)) +
          (c₂ * ‖faceIdRayAPTwo (Q 2) α p₁ x‖ * (w / W ^ (m + 1 - 4)) +
            c₃ * ‖faceIdRayAPThree (Q 2) α x‖ * (w / W ^ (m + 1 - 5))) / s') := by
      have hn : ∀ (k : ℕ) (T : ℂ), ‖(k.factorial : ℂ) * T‖ = (k.factorial : ℝ) * ‖T‖ :=
        fun k T => by rw [norm_mul, Complex.norm_natCast]
      have hn' : ∀ (k : ℕ) (d : ℕ) (T : ℂ), ‖(k.factorial : ℂ) / (d : ℂ) * T‖ =
          (k.factorial : ℝ) / d * ‖T‖ := fun k d T => by
        rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
      simp only [Fin.sum_univ_three, majIncA, hT₁, hT₂, hT₃, hn,
        show ((2 : ℂ)) = ((2 : ℕ) : ℂ) by norm_num, show ((4 : ℂ)) = ((4 : ℕ) : ℂ) by norm_num,
        hn', Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, hc₁, hc₂, hc₃]
      push_cast
      field_simp
    have hfin : (c₁ + c₂ + c₃) * Γ * faceIdRayAPSum Q α p₁ cs x ≤
        Kc * s' ^ (1 - δ) * u ^ a' * F x := by
      have hw' : w ^ a' = u ^ a' * z γ ^ a' := Real.mul_rpow hu0.le (hz.1 γ)
      have hK : 0 ≤ Kc * s' ^ (1 - δ) * u ^ a' := by positivity
      calc (c₁ + c₂ + c₃) * Γ * faceIdRayAPSum Q α p₁ cs x
          = Kc * s' ^ (1 - δ) * u ^ a' * (z γ ^ a' * B ^ (-δ) * faceIdRayAPSum Q α p₁ cs x) := by
            rw [hΓ, hw', hKc]; ring
        _ ≤ Kc * s' ^ (1 - δ) * u ^ a' * F x := mul_le_mul_of_nonneg_left hx hK
    have hval : w * ∑ t : Fin 3, majIncA (m + 1) t (T₁ t) (T₂ t) (T₃ t) W s' ≤
        Kc * s' ^ (1 - δ) * u ^ a' * F x := by
      rw [habs]
      refine le_trans ?_ hfin
      refine le_of_le_of_eq hsum ?_
      simp only [faceIdRayAPSum]
      rfl
    have hmε : 0 ≤ (m + 1 : ℝ) * ε := by positivity
    calc w * ‖∑ t : Fin 3, (majIncX (m + 1) t (T₁ t) (T₂ t) (T₃ t) (V₀ + s * B) s -
          majIncX (m + 1) t (T₁ t) (T₂ t) (T₃ t) (V₀ + s' * B) s')‖
        ≤ w * ((m + 1 : ℝ) * ε * ∑ t : Fin 3, majIncA (m + 1) t (T₁ t) (T₂ t) (T₃ t) W s') :=
          mul_le_mul_of_nonneg_left hinc hw0
      _ = (m + 1 : ℝ) * ε * (w * ∑ t : Fin 3, majIncA (m + 1) t (T₁ t) (T₂ t) (T₃ t) W s') := by
          ring
      _ ≤ g x := mul_le_mul_of_nonneg_left hval hmε
  have hint := norm_integral_le_of_norm_le hgi hpt
  have hI : ∫ x in simplexSet m, ((u : ℂ) * f s x - (u : ℂ) * f s' x) =
      (u : ℂ) * (∫ x in simplexSet m, f s x) - (u : ℂ) * ∫ x in simplexSet m, f s' x := by
    have h1 : IntegrableOn (fun x => (u : ℂ) * f s x) (simplexSet m) :=
      (hInt s hs u hu).const_mul _
    have h2 : IntegrableOn (fun x => (u : ℂ) * f s' x) (simplexSet m) :=
      (hInt s' hs' u hu).const_mul _
    rw [integral_sub h1 h2, integral_const_mul, integral_const_mul]
  rw [hI] at hint
  have hgint : ∫ x in simplexSet m, g x =
      (m + 1 : ℝ) * ε * (Kc * s' ^ (1 - δ) * u ^ a') * ∫ x in simplexSet m, F x := by
    simp only [hg]
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hgint] at hint
  have hua : u ^ a' ≤ u ^ a := Real.rpow_le_rpow_of_exponent_le hu (min_le_left _ _)
  have hss' : s' ^ (1 - δ) ≤ s ^ (1 - δ) :=
    Real.rpow_le_rpow hs'0.le hss (by linarith)
  change ‖(u : ℂ) * (pairDens (N (majRayVec s)) α (fun l => cs l • majRayVec s) M γ u -
    pairDens (N (majRayVec s')) α (fun l => cs l • majRayVec s') M γ u)‖ ≤ _
  simp only [pairDens]
  change ‖(u : ℂ) * (-((π : ℂ) ^ 4) * (∫ y in simplexSet m, f s y) -
    -((π : ℂ) ^ 4) * (∫ y in simplexSet m, f s' y))‖ ≤ _
  rw [show (u : ℂ) * (-((π : ℂ) ^ 4) * (∫ y in simplexSet m, f s y) -
      -((π : ℂ) ^ 4) * (∫ y in simplexSet m, f s' y)) =
      -((π : ℂ) ^ 4) * ((u : ℂ) * (∫ y in simplexSet m, f s y) -
        (u : ℂ) * (∫ y in simplexSet m, f s' y)) by ring, norm_mul, norm_neg,
    norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hm1 : (0 : ℝ) ≤ (m + 1 : ℝ) * ε := by positivity
  calc π ^ 4 * ‖(u : ℂ) * (∫ y in simplexSet m, f s y) - (u : ℂ) * ∫ y in simplexSet m, f s' y‖
      ≤ π ^ 4 * ((m + 1 : ℝ) * ε * (Kc * s' ^ (1 - δ) * u ^ a') *
          ∫ x in simplexSet m, F x) := mul_le_mul_of_nonneg_left hint (by positivity)
    _ ≤ π ^ 4 * ((m + 1 : ℝ) * ε * (Kc * s ^ (1 - δ) * u ^ a) * ∫ x in simplexSet m, F x) := by
        gcongr
    _ = π ^ 4 * ((m + 1 : ℝ) * Kc) * (∫ x in simplexSet m, F x) * s ^ (1 - δ) * u ^ a * ε := by
        ring

end QED.GradedProof.RPi4

end
