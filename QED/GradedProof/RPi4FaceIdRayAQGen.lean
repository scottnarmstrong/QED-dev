/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRayAQCoef

/-!
# (R-Π₄) step L10, T2.UV: (A) with a power loss for all `u ≥ 1`, and the majorant of a piece

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (input (A) of
`QED.GradedProof.RPi4.faceIdRay_of_size_rate`). `FaceIdRayAQPow` is
`QED.GradedProof.RPi4.FaceIdRayAPow` for all `u ≥ 1` (not only `u ≥ s`), the form the
`WireDRay` reduction consumes; the majorant argument of
`QED.GradedProof.RPi4.faceIdRayAP_pow_pairDens` gives it verbatim (`faceIdRayAQ_pow_pairDens`).

The majorant (`faceIdRayAQ_hMaj`): for data with rows `(1,0)`, `(0,1)`, `(1,-1)`, a cut pair
`t₁, t₂` (parallel lines with different shifts, `B ≥ c z_{t₁} z_{t₂}`), a top-monomial bound
`‖T₁(Q₂)‖ 2√(zᵢ zⱼ) ≤ K B U⁻²` (the flows of two fermion lines), and coefficient bounds
`‖T₂‖ ≤ C U⁻³ ∑_{J₂} z`, `‖T₃‖ ≤ C U⁻⁴ (∑_{J₁} z)(∑_{J₃} z)`, the weight
`z_γ^a B^{-1/100} faceIdRayAPSum` is at most a sum of the monomial weights
`U⁻ᵏ z_γ^a (z_{t₁} z_{t₂})^{-1/100} ∏ zₜ^{eₜ/2}` of `QED.GradedProof.RPi4.FaceIdRayAQCheck`,
each integrable once its integer check holds.

* `FaceIdRayAQPow`, `FaceIdRayAQPow.faceIdRayAPow`, `.zero`, `.add`, `.const_mul`, `.sum`;
* **`faceIdRayAQ_pow_pairDens`**;
* `faceIdRayAQWt`, `faceIdRayAQ_prod_W`, `faceIdRayAQ_prod_half_one`, `faceIdRayAQ_prod_half_two`;
* **`faceIdRayAQ_hMaj`**.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.MassScaling
open QED.TwoLoop.LimitCovariance
open QED.GradedProof.WI2 (ehat ehat_qsum)
open QED.Integration.Feynman (simplexSet simplexPoint)

variable {m : ℕ}

/-- **Input (A) with a power loss, for all `u ≥ 1`**: some `δ > 0` such that for every `a > 0`,
`‖u G(u, k'(s))‖ ≤ A_a s^{1-δ} u^a` for `s ≥ 1`, `u ≥ 1`. -/
def FaceIdRayAQPow (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, 0 < a → ∃ A : ℝ, ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, 1 ≤ u →
    ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s)‖ ≤ A * s ^ (1 - δ) * u ^ a

namespace FaceIdRayAQPow

variable {G H : ℝ → (Fin 4 → ℝ) → ℂ}

theorem faceIdRayAPow (h : FaceIdRayAQPow G) : FaceIdRayAPow G := by
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨δ, hδ, fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := h a ha
  exact ⟨A, fun s hs u hu => hA s hs u (hs.trans hu)⟩

theorem zero : FaceIdRayAQPow fun _ _ => 0 :=
  ⟨1, one_pos, fun _ _ => ⟨0, fun s _ u _ => by simp⟩⟩

theorem mono {A δ δ' a s u : ℝ} (hs : 1 ≤ s) (hu : 1 ≤ u) (hδ : δ' ≤ δ) :
    A * s ^ (1 - δ) * u ^ a ≤ |A| * s ^ (1 - δ') * u ^ a := by
  have hu0 : 0 ≤ u ^ a := Real.rpow_nonneg (by linarith) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self A)
    (faceIdRay_rpow_mono hs (by linarith)) (Real.rpow_nonneg (by linarith) _)
    (abs_nonneg A)) hu0

theorem add (hG : FaceIdRayAQPow G) (hH : FaceIdRayAQPow H) :
    FaceIdRayAQPow fun u k => G u k + H u k := by
  obtain ⟨δ, hδ, hG⟩ := hG
  obtain ⟨δ', hδ', hH⟩ := hH
  refine ⟨min δ δ', lt_min hδ hδ', fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := hG a ha
  obtain ⟨B, hB⟩ := hH a ha
  refine ⟨|A| + |B|, fun s hs u hu => ?_⟩
  rw [mul_add, add_mul, add_mul]
  exact (norm_add_le _ _).trans (add_le_add
    ((hA s hs u hu).trans (mono hs hu (min_le_left _ _)))
    ((hB s hs u hu).trans (mono hs hu (min_le_right _ _))))

theorem const_mul (hG : FaceIdRayAQPow G) (r : ℂ) : FaceIdRayAQPow fun u k => r * G u k := by
  obtain ⟨δ, hδ, hG⟩ := hG
  refine ⟨δ, hδ, fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := hG a ha
  refine ⟨‖r‖ * A, fun s hs u hu => ?_⟩
  rw [mul_left_comm, norm_mul, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hA s hs u hu) (norm_nonneg _)

theorem sum {ι : Type*} (t : Finset ι) {G : ι → ℝ → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ t, FaceIdRayAQPow (G i)) : FaceIdRayAQPow fun u k => ∑ i ∈ t, G i u k := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (zero : FaceIdRayAQPow fun _ _ => 0)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end FaceIdRayAQPow

/-- **`FaceIdRayAQPow` of a photon-mass density from a majorant**: the proof of
`QED.GradedProof.RPi4.faceIdRayAP_pow_pairDens` uses `s ≤ u` only through `u ≥ 1`, so the
bound holds for all `u ≥ 1`. -/
theorem faceIdRayAQ_pow_pairDens (hm : 5 ≤ m) (α : Fin (m + 1) → Fin 2 → ℝ)
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
            faceIdRayAPSum Q α (fun i => cs i • majRayVec 1) cs x ≤ F x) :
    FaceIdRayAQPow fun u k => pairDens (N k) α (fun l => cs l • k) M γ u := by
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
  refine ⟨π ^ 4 * Kc * ∫ x in simplexSet m, F x, fun s hs u hu => ?_⟩
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := by linarith
  set r := Real.sqrt s with hr_def
  have hr1 : 1 ≤ r := by rw [hr_def, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hs
  have hr2 : r ^ 2 = s := Real.sq_sqrt hs0.le
  set v := majRayVec 1 with hv
  set p₁ : Fin (m + 1) → Fin 4 → ℝ := fun i => cs i • v with hp₁
  have hmom : (fun i => cs i • majRayVec s) = r • p₁ := by
    funext i
    simp only [hp₁, Pi.smul_apply, maj_majRayVec_eq hs0.le, hv]
    exact smul_comm _ _ _
  -- the quartic along the ray
  set R : LoopQuartic := qsum Finset.univ (fun t : Fin 3 => ((s : ℂ)) ^ (t : ℕ))
    (fun t => dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q t)) with hR
  have hRe : R.eval = N (majRayVec s) := by
    funext ℓ
    rw [maj_majRayVec_eq hs0.le, hN r hr1]
    simp only [hR, eval_qsum, eval_dilateQ, one_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 2
    rw [← hr2]; push_cast; ring
  change ‖(u : ℂ) * pairDens (N (majRayVec s)) α (fun l => cs l • majRayVec s) M γ u‖ ≤ _
  rw [pairDens_eq hRe, hmom]
  set f : (Fin m → ℝ) → ℂ := fun y => (simplexPoint y γ : ℂ) *
    paramAtV (m + 1) R α (r • p₁) (simplexPoint y)
      (symanzikV α (r • p₁) (Function.update M γ 0) (simplexPoint y) + simplexPoint y γ * u)
    with hf
  set g : (Fin m → ℝ) → ℝ := fun x => Kc * s ^ (1 - δ) * u ^ a' * F x with hg
  have hgi : IntegrableOn g (simplexSet m) := hF.const_mul _
  have hpt : ∀ᵐ x ∂(volume.restrict (simplexSet m)), ‖(u : ℂ) * f x‖ ≤ g x := by
    filter_upwards [hFx, ae_restrict_mem (QED.Integration.Feynman.measurableSet_simplexSet m)]
      with x ⟨hB, hx⟩ hxS
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    set z := simplexPoint x with hz_def
    set B := remainder α z cs with hB_def
    set Vm := ∑ i, z i * Function.update M γ 0 i ^ 2 with hVm
    set V₀ := Vm + z γ * u with hV₀_def
    set W := V₀ + s * B with hW_def
    have hV₀ : c₀ ≤ V₀ := faceIdRayAP_le_V₀ M γ hM hz.1 hz.2 hu
    have hVm0 : 0 ≤ Vm := Finset.sum_nonneg fun i _ => mul_nonneg (hz.1 i) (sq_nonneg _)
    have hV₀0 : 0 < V₀ := hc₀.trans_le hV₀
    have hVe : symanzikV α (r • p₁) (Function.update M γ 0) z + z γ * u = W := by
      rw [← hmom, maj_symanzikV_ray α _ z cs hs0.le, hW_def, hV₀_def, hVm, hB_def]
      ring
    have hW0 : 0 < W := by nlinarith [mul_pos hs0 hB]
    set w := u * z γ with hw_def
    have hw0 : 0 ≤ w := mul_nonneg hu0.le (hz.1 γ)
    have hwW : w ≤ W := by
      have := mul_pos hs0 hB
      simp only [hw_def, hW_def, hV₀_def]
      linarith [mul_comm u (z γ)]
    have hWW : V₀ + s * B ≤ W := le_rfl
    set Γ := c₀ ^ (-(m : ℝ)) * (s ^ (1 - δ) * B ^ (-δ) * w ^ a') with hΓ
    -- the pieces of the integrand
    have hP : ∀ t, ‖paramAtV (m + 1) (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q t)) α (r • p₁) z W‖ ≤
        c₁ * ‖faceIdRayAPOne (Q t) α p₁ x‖ / W ^ (m + 1 - 3) +
          (c₂ * ‖faceIdRayAPTwo (Q t) α p₁ x‖ / W ^ (m + 1 - 4) +
            c₃ * ‖faceIdRayAPThree (Q t) α x‖ / W ^ (m + 1 - 5)) / s := fun t => by
      rw [← hr2]
      exact faceIdRayAP_norm_paramAtV_dilate_le (Q t) α p₁ x hr1 hW0
    have hsplit : paramAtV (m + 1) R α (r • p₁) z W = ∑ t : Fin 3, ((s : ℂ)) ^ (t : ℕ) *
        paramAtV (m + 1) (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q t)) α (r • p₁) z W := by
      simp only [paramAtV, hR, ehat_qsum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have hnorm : ‖(u : ℂ) * f x‖ = w * ‖∑ t : Fin 3, ((s : ℂ)) ^ (t : ℕ) *
        paramAtV (m + 1) (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q t)) α (r • p₁) z W‖ := by
      simp only [hf]
      rw [← hz_def, hVe, hsplit, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hu0, abs_of_nonneg (hz.1 γ), hw_def]
      ring
    rw [hnorm]
    -- the three gains
    have hn1 : (1 : ℝ) + δ ≤ ((m + 1 - 3 : ℕ) : ℝ) - 1 := by
      have : (3 : ℝ) ≤ ((m + 1 - 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ m + 1 - 3)
      linarith
    have hn2 : δ ≤ ((m + 1 - 4 : ℕ) : ℝ) - 1 := by
      have : (2 : ℝ) ≤ ((m + 1 - 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ m + 1 - 4)
      linarith
    have hKn : ∀ j : ℕ, 3 ≤ j → ((m + 1 - j : ℕ) : ℝ) ≤ (m : ℝ) := fun j hj => by
      exact_mod_cast (by omega : m + 1 - j ≤ m)
    have g1 := faceIdRayAP_gain_zero (n := m + 1 - 3) hs0 hc₀ hc₀1 hV₀ hB hWW hw0 hwW hδ.le
      ha' ha'1 (by linarith) (hKn 3 le_rfl)
    have g1' := faceIdRayAP_gain_one (n := m + 1 - 3) hs0 hc₀ hc₀1 hV₀ hB hWW hw0 hwW hδ.le
      ha' ha'1 hn1 (hKn 3 le_rfl)
    have g2 := faceIdRayAP_gain_zero (n := m + 1 - 4) hs0 hc₀ hc₀1 hV₀ hB hWW hw0 hwW hδ.le
      ha' ha'1 hn2 (hKn 4 (by norm_num))
    have g3 : ∀ t, ‖faceIdRayAPThree (Q t) α x‖ * (s * (w / W ^ (m + 1 - 5))) ≤
        ‖faceIdRayAPThree (Q t) α x‖ * Γ := fun t => by
      rcases hq with h6 | hq0
      · have hn3 : δ ≤ ((m + 1 - 5 : ℕ) : ℝ) - 1 := by
          have : (2 : ℝ) ≤ ((m + 1 - 5 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 2 ≤ m + 1 - 5)
          linarith
        exact mul_le_mul_of_nonneg_left (faceIdRayAP_gain_zero hs0 hc₀ hc₀1 hV₀ hB hWW hw0 hwW
          hδ.le ha' ha'1 hn3 (hKn 5 (by norm_num))) (norm_nonneg _)
      · simp [faceIdRayAPThree, contractFour_eq_zero_of_quart _ _ (hq0 t)]
    have hsum := faceIdRayAP_sum_le (o := fun t => ‖faceIdRayAPOne (Q t) α p₁ x‖)
      (w := fun t => ‖faceIdRayAPTwo (Q t) α p₁ x‖) (h := fun t => ‖faceIdRayAPThree (Q t) α x‖)
      hs hB (by positivity : 0 ≤ w / W ^ (m + 1 - 3)) (by positivity : 0 ≤ w / W ^ (m + 1 - 4))
      (by positivity : 0 ≤ w / W ^ (m + 1 - 5)) hc₁0 hc₂0 hc₃0 (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) g1 g1' g2 g3
    -- the triangle inequality
    have htri : w * ‖∑ t : Fin 3, ((s : ℂ)) ^ (t : ℕ) *
        paramAtV (m + 1) (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q t)) α (r • p₁) z W‖ ≤
        c₁ * ‖faceIdRayAPOne (Q 0) α p₁ x‖ * (w / W ^ (m + 1 - 3)) +
          (c₂ * ‖faceIdRayAPTwo (Q 0) α p₁ x‖ * (w / W ^ (m + 1 - 4)) +
            c₃ * ‖faceIdRayAPThree (Q 0) α x‖ * (w / W ^ (m + 1 - 5))) / s +
        s * (c₁ * ‖faceIdRayAPOne (Q 1) α p₁ x‖ * (w / W ^ (m + 1 - 3)) +
          (c₂ * ‖faceIdRayAPTwo (Q 1) α p₁ x‖ * (w / W ^ (m + 1 - 4)) +
            c₃ * ‖faceIdRayAPThree (Q 1) α x‖ * (w / W ^ (m + 1 - 5))) / s) +
        s ^ 2 * (c₁ * ‖faceIdRayAPOne (Q 2) α p₁ x‖ * (w / W ^ (m + 1 - 3)) +
          (c₂ * ‖faceIdRayAPTwo (Q 2) α p₁ x‖ * (w / W ^ (m + 1 - 4)) +
            c₃ * ‖faceIdRayAPThree (Q 2) α x‖ * (w / W ^ (m + 1 - 5))) / s) := by
      rw [Fin.sum_univ_three]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, one_mul, pow_one]
      have h3 := norm_add₃_le (a := ((s : ℂ)) ^ ((0 : Fin 3) : ℕ) *
          paramAtV (m + 1) (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q 0)) α (r • p₁) z W)
        (b := ((s : ℂ)) ^ ((1 : Fin 3) : ℕ) *
          paramAtV (m + 1) (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q 1)) α (r • p₁) z W)
        (c := ((s : ℂ)) ^ ((2 : Fin 3) : ℕ) *
          paramAtV (m + 1) (dilateQ 1 (((r⁻¹ : ℝ)) : ℂ) (Q 2)) α (r • p₁) z W)
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
        Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, one_mul, pow_one] at h3
      have k0 := hP 0
      have k1 := mul_le_mul_of_nonneg_left (hP 1) hs0.le
      have k2 := mul_le_mul_of_nonneg_left (hP 2) (sq_nonneg s)
      have hsum3 := mul_le_mul_of_nonneg_left (h3.trans (add_le_add (add_le_add k0 k1) k2)) hw0
      refine hsum3.trans (le_of_eq ?_)
      field_simp
    have hfin : (c₁ + c₂ + c₃) * Γ * faceIdRayAPSum Q α p₁ cs x ≤ g x := by
      have hw' : w ^ a' = u ^ a' * z γ ^ a' := Real.mul_rpow hu0.le (hz.1 γ)
      have hK : 0 ≤ Kc * s ^ (1 - δ) * u ^ a' := by positivity
      calc (c₁ + c₂ + c₃) * Γ * faceIdRayAPSum Q α p₁ cs x
          = Kc * s ^ (1 - δ) * u ^ a' * (z γ ^ a' * B ^ (-δ) * faceIdRayAPSum Q α p₁ cs x) := by
            rw [hΓ, hw', hKc]; ring
        _ ≤ Kc * s ^ (1 - δ) * u ^ a' * F x := mul_le_mul_of_nonneg_left hx hK
    refine htri.trans (le_trans ?_ hfin)
    refine le_of_le_of_eq hsum ?_
    simp only [faceIdRayAPSum]
    rfl
  have hint := norm_integral_le_of_norm_le hgi hpt
  have hgint : ∫ x in simplexSet m, g x = Kc * s ^ (1 - δ) * u ^ a' * ∫ x in simplexSet m, F x :=
    integral_const_mul _ _
  have hua : u ^ a' ≤ u ^ a := Real.rpow_le_rpow_of_exponent_le hu (min_le_left _ _)
  rw [integral_const_mul] at hint
  rw [show (u : ℂ) * (-((π : ℂ) ^ 4) * ∫ y in simplexSet m, f y) =
      -((π : ℂ) ^ 4) * ((u : ℂ) * ∫ y in simplexSet m, f y) by ring, norm_mul, norm_neg,
    norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [hgint] at hint
  have hK0 : 0 ≤ Kc := by positivity
  calc π ^ 4 * ‖(u : ℂ) * ∫ y in simplexSet m, f y‖
      ≤ π ^ 4 * (Kc * s ^ (1 - δ) * u ^ a' * ∫ x in simplexSet m, F x) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ ≤ π ^ 4 * (Kc * s ^ (1 - δ) * u ^ a * ∫ x in simplexSet m, F x) := by
        gcongr
    _ = π ^ 4 * Kc * (∫ x in simplexSet m, F x) * s ^ (1 - δ) * u ^ a := by ring

/-! ### The majorant of a piece -/

/-- The monomial weight `U⁻ᵏ ∏ₜ zₜ^{wₜ}` of the integer check. -/
noncomputable def faceIdRayAQWt (α : Fin (m + 1) → Fin 2 → ℝ) (γ t₁ t₂ : Fin (m + 1)) (k : ℕ)
    (e : Fin (m + 1) → ℤ) (a : ℝ) (x : Fin m → ℝ) : ℝ :=
  (symanzikU α (simplexPoint x) ^ k)⁻¹ * ∏ t, simplexPoint x t ^ faceIdRayAQW γ t₁ t₂ e a t

/-- `∏ₜ zₜ^{wₜ} = z_γ^a (z_{t₁} z_{t₂})^{-1/100} ∏ₜ zₜ^{eₜ/2}`. -/
theorem faceIdRayAQ_prod_W {z : Fin (m + 1) → ℝ} (hz : ∀ t, 0 < z t) (γ t₁ t₂ : Fin (m + 1))
    (ht : t₁ ≠ t₂) (e : Fin (m + 1) → ℤ) (a : ℝ) :
    ∏ t, z t ^ faceIdRayAQW γ t₁ t₂ e a t =
      z γ ^ a * (z t₁ ^ (-(1 / 100) : ℝ) * z t₂ ^ (-(1 / 100) : ℝ)) *
        ∏ t, z t ^ ((e t : ℝ) / 2) := by
  have h : ∀ t, z t ^ faceIdRayAQW γ t₁ t₂ e a t = z t ^ ((e t : ℝ) / 2) *
      (z t ^ (if t = γ then a else 0) * (z t ^ (if t = t₁ then (-(1 / 100) : ℝ) else 0) *
        z t ^ (if t = t₂ then (-(1 / 100) : ℝ) else 0))) := fun t => by
    rw [← Real.rpow_add (hz t), ← Real.rpow_add (hz t), ← Real.rpow_add (hz t),
      faceIdRayAQW_eq]
    congr 1
    rcases eq_or_ne t t₁ with h1 | h1 <;> rcases eq_or_ne t t₂ with h2 | h2
    · exact absurd (h1.symm.trans h2) ht
    · subst h1; simp only [ht, true_or, ite_true, ite_false]; ring
    · subst h2; simp only [Ne.symm ht, or_true, ite_true, ite_false]; ring
    · simp only [h1, h2, or_self, ite_false]; ring
  rw [Finset.prod_congr rfl fun t _ => h t, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, faceIdRayAQ_prod_rpow_ite, faceIdRayAQ_prod_rpow_ite,
    faceIdRayAQ_prod_rpow_ite]
  ring

theorem faceIdRayAQ_prod_half_one {z : Fin (m + 1) → ℝ} (u : Fin (m + 1)) (c : ℤ) :
    ∏ t, z t ^ (((if t = u then c else 0 : ℤ) : ℝ) / 2) = z u ^ ((c : ℝ) / 2) := by
  rw [← faceIdRayAQ_prod_rpow_ite z u]
  refine Finset.prod_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem faceIdRayAQ_prod_half_two {z : Fin (m + 1) → ℝ} (hz : ∀ t, 0 < z t) (u v : Fin (m + 1))
    (c d : ℤ) :
    ∏ t, z t ^ (((if t = u then c else 0) + (if t = v then d else 0) : ℤ) / 2 : ℝ) =
      z u ^ ((c : ℝ) / 2) * z v ^ ((d : ℝ) / 2) := by
  rw [← faceIdRayAQ_prod_half_one u c, ← faceIdRayAQ_prod_half_one v d,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [← Real.rpow_add (hz t)]
  push_cast
  ring_nf

/-- **The majorant of a merged piece.** -/
theorem faceIdRayAQ_hMaj (α : Fin (m + 1) → Fin 2 → ℝ) (cl : Fin (m + 1) → Fin 3)
    (hα : ∀ t, α t = faceIdRayAQRow (cl t)) (cs : Fin (m + 1) → ℝ)
    (γ t₁ t₂ i j : Fin (m + 1)) (ht : t₁ ≠ t₂) (hcl : cl t₁ = cl t₂) (hcs : cs t₁ ≠ cs t₂)
    (Q : Fin 3 → LoopQuartic) (J₂ J₁ J₃ : Fin (m + 1) → Prop) [DecidablePred J₂]
    [DecidablePred J₁] [DecidablePred J₃]
    (hT₂ : ∃ C, 0 ≤ C ∧ ∀ x : Fin m → ℝ, (∀ i, 0 ≤ simplexPoint x i) →
      0 < symanzikU α (simplexPoint x) → ∀ t,
        ‖faceIdRayAPTwo (Q t) α (fun i => cs i • majRayVec 1) x‖ ≤
          C * (∑ u, if J₂ u then simplexPoint x u else 0) / symanzikU α (simplexPoint x) ^ 3)
    (hT₃ : ∃ C, 0 ≤ C ∧ ∀ x : Fin m → ℝ, (∀ i, 0 ≤ simplexPoint x i) →
      0 < symanzikU α (simplexPoint x) → ∀ t,
        ‖faceIdRayAPThree (Q t) α x‖ ≤ C * ((∑ u, if J₁ u then simplexPoint x u else 0) *
          (∑ u, if J₃ u then simplexPoint x u else 0)) / symanzikU α (simplexPoint x) ^ 4)
    (hTop : ∃ K, 0 ≤ K ∧ ∀ x : Fin m → ℝ, (∀ i, 0 ≤ simplexPoint x i) →
      0 < symanzikU α (simplexPoint x) →
        ‖faceIdRayAPOne (Q 2) α (fun i => cs i • majRayVec 1) x‖ *
          (2 * Real.sqrt (simplexPoint x i * simplexPoint x j)) ≤
            K * remainder α (simplexPoint x) cs / symanzikU α (simplexPoint x) ^ 2)
    (c₁ : FaceIdRayAQCheck cl γ t₁ t₂ 2 0)
    (c₂ : FaceIdRayAQCheck cl γ t₁ t₂ 2
      fun t => (if t = i then -1 else 0) + (if t = j then -1 else 0))
    (c₃ : ∀ u, J₂ u → FaceIdRayAQCheck cl γ t₁ t₂ 3 fun t => if t = u then 2 else 0)
    (c₄ : ∀ u v, J₁ u → J₃ v → FaceIdRayAQCheck cl γ t₁ t₂ 4
      fun t => (if t = u then 2 else 0) + (if t = v then 2 else 0)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∃ F : (Fin m → ℝ) → ℝ,
      IntegrableOn F (simplexSet m) ∧ ∀ᵐ x ∂(volume.restrict (simplexSet m)),
        0 < remainder α (simplexPoint x) cs ∧
          simplexPoint x γ ^ a * remainder α (simplexPoint x) cs ^ (-δ) *
            faceIdRayAPSum Q α (fun i => cs i • majRayVec 1) cs x ≤ F x := by
  classical
  obtain ⟨C₂, hC₂, hT₂⟩ := hT₂
  obtain ⟨C₃, hC₃, hT₃⟩ := hT₃
  obtain ⟨K, hK, hTop⟩ := hTop
  obtain ⟨A₀, hA₀, h₀⟩ := faceIdRayAQ_norm_one_le (Q 0) α cs
  obtain ⟨A₁, hA₁, h₁⟩ := faceIdRayAQ_norm_one_le (Q 1) α cs
  set c : ℝ := (cs t₁ - cs t₂) ^ 2 / 2 with hc
  have hc0 : 0 < c := by
    have : cs t₁ - cs t₂ ≠ 0 := sub_ne_zero.mpr hcs
    positivity
  obtain ⟨j₀, hj₀⟩ := (c₁.2.2 0).1
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      exact absurd (congrArg cl (Fin.ext (by have := j₀.isLt; omega) : j₀ = 0)) hj₀
    · exact h0
  refine ⟨1 / 100, by norm_num, by norm_num, fun a ha _ => ?_⟩
  set eT : Fin (m + 1) → ℤ := fun t => (if t = i then -1 else 0) + (if t = j then -1 else 0)
  set e₂ : Fin (m + 1) → Fin (m + 1) → ℤ := fun u t => if t = u then 2 else 0
  set e₃ : Fin (m + 1) → Fin (m + 1) → Fin (m + 1) → ℤ :=
    fun u v t => (if t = u then 2 else 0) + (if t = v then 2 else 0)
  set W := faceIdRayAQWt α γ t₁ t₂ with hW
  have hWi : ∀ k e, FaceIdRayAQCheck cl γ t₁ t₂ k e → IntegrableOn (W k e a) (simplexSet m) :=
    fun k e h => faceIdRayAQ_integrableOn_check α cl hα γ t₁ t₂ k e h ha
  refine ⟨fun x => c ^ (-(1 / 100) : ℝ) * ((A₀ + A₁) * W 2 0 a x + K / 2 * W 2 eT a x +
      3 * C₂ * ∑ u ∈ Finset.univ.filter J₂, W 3 (e₂ u) a x +
      3 * C₃ * ∑ u ∈ Finset.univ.filter J₁, ∑ v ∈ Finset.univ.filter J₃, W 4 (e₃ u v) a x),
    ?_, ?_⟩
  · refine Integrable.const_mul (Integrable.add (Integrable.add (Integrable.add
      ((hWi 2 0 c₁).const_mul _) ((hWi 2 eT c₂).const_mul _)) (Integrable.const_mul
        (integrable_finsetSum _ fun u hu => hWi 3 (e₂ u) (c₃ u (Finset.mem_filter.mp hu).2))
        _)) (Integrable.const_mul (integrable_finsetSum _ fun u hu =>
          integrable_finsetSum _ fun v hv => hWi 4 (e₃ u v)
            (c₄ u v (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2)) _)) _
  rw [ae_restrict_iff' (QED.Integration.Feynman.measurableSet_simplexSet m)]
  filter_upwards [ae_simplexPoint_ne_zero hm] with x hx0 hxS
  obtain ⟨hz0, hz1⟩ := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
  set z := simplexPoint x with hzdef
  have hz : ∀ t, 0 < z t := fun t => lt_of_le_of_ne (hz0 t) (hx0 t).symm
  have hz1' : ∀ t, z t ≤ 1 := fun t =>
    (Finset.single_le_sum (fun i _ => hz0 i) (Finset.mem_univ t)).trans hz1.le
  -- `U > 0`
  have hU : 0 < symanzikU α z := by
    have hrow := mul_sum_pairDet_sq_le_two_mul_symanzikU α hz0 0
    have hdet : pairDet α 0 j₀ ≠ 0 := by
      have : j₀ ∈ faceIdRayAPLines α 0 := by
        rw [faceIdRayAQ_lines_eq α cl hα 0]; simp [hj₀]
      exact (Finset.mem_filter.mp this).2
    have hpos : 0 < ∑ t, z t * pairDet α 0 t ^ 2 :=
      lt_of_lt_of_le (mul_pos (hz j₀) (pow_pos (abs_pos.mpr hdet) 2 |>.trans_eq (sq_abs _)))
        (Finset.single_le_sum (f := fun t => z t * pairDet α 0 t ^ 2)
          (fun t _ => mul_nonneg (hz0 t) (sq_nonneg _)) (Finset.mem_univ j₀))
    nlinarith [mul_pos (hz 0) hpos]
  -- the cut
  have hα₁₂ : α t₁ = α t₂ := by rw [hα, hα, hcl]
  have hcut := fun y => faceIdRayA_cut_pair α cs ht hα₁₂ y
  have hBge := faceIdRayA_remainder_ge_prod α hz0 hz1' hU.ne' {t₁, t₂} hcut
  rw [Finset.prod_pair ht] at hBge
  set B := remainder α z cs with hBdef
  have hB : 0 < B := lt_of_lt_of_le (mul_pos hc0 (mul_pos (hz t₁) (hz t₂))) hBge
  refine ⟨hB, ?_⟩
  have hBδ := faceIdRayA_rpow_neg_remainder_le α hz0 hz1' hU.ne' {t₁, t₂} hc0
    (by norm_num : (0 : ℝ) ≤ 1 / 100) (fun t _ => hz t) hcut
  rw [Finset.prod_pair ht] at hBδ
  -- the coefficient sum
  set U := symanzikU α z with hUdef
  set S := faceIdRayAPSum Q α (fun i => cs i • majRayVec 1) cs x with hSdef
  set Z₂ := ∑ u, if J₂ u then z u else 0
  set Z₁ := ∑ u, if J₁ u then z u else 0
  set Z₃ := ∑ u, if J₃ u then z u else 0
  set τ := z i ^ (-(1 / 2) : ℝ) * z j ^ (-(1 / 2) : ℝ) with hτ
  have hsq : Real.sqrt (z i * z j) * τ = 1 := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow (hz i).le (hz j).le, hτ]
    rw [show z i ^ (1 / 2 : ℝ) * z j ^ (1 / 2 : ℝ) * (z i ^ (-(1 / 2) : ℝ) *
        z j ^ (-(1 / 2) : ℝ)) = (z i ^ (1 / 2 : ℝ) * z i ^ (-(1 / 2) : ℝ)) *
          (z j ^ (1 / 2 : ℝ) * z j ^ (-(1 / 2) : ℝ)) by ring, ← Real.rpow_add (hz i),
      ← Real.rpow_add (hz j)]
    norm_num
  have hτ0 : 0 ≤ τ := mul_nonneg (Real.rpow_nonneg (hz0 i) _) (Real.rpow_nonneg (hz0 j) _)
  have hS : S ≤ (A₀ + A₁) / U ^ 2 + K / 2 * τ / U ^ 2 + 3 * C₂ * Z₂ / U ^ 3 +
      3 * C₃ * (Z₁ * Z₃) / U ^ 4 := by
    have k0 := h₀ x hz0 hU
    have k1 := h₁ x hz0 hU
    have kT := hTop x hz0 hU
    have k2 := hT₂ x hz0 hU
    have k3 := hT₃ x hz0 hU
    have hsq0 : 0 < Real.sqrt (z i * z j) := Real.sqrt_pos.mpr (mul_pos (hz i) (hz j))
    have kT' : ‖faceIdRayAPOne (Q 2) α (fun i => cs i • majRayVec 1) x‖ / B ≤
        K / 2 * τ / U ^ 2 := by
      rw [div_le_iff₀ hB]
      have e : K / 2 * τ / U ^ 2 * B = (K * B / U ^ 2) * τ / 2 := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right kT hτ0
      have e2 : ‖faceIdRayAPOne (Q 2) α (fun i => cs i • majRayVec 1) x‖ *
          (2 * Real.sqrt (z i * z j)) * τ =
            2 * ‖faceIdRayAPOne (Q 2) α (fun i => cs i • majRayVec 1) x‖ := by
        rw [mul_assoc, mul_assoc, hsq]; ring
      linarith
    have s2 : ∑ t, (‖faceIdRayAPTwo (Q t) α (fun i => cs i • majRayVec 1) x‖ +
        ‖faceIdRayAPThree (Q t) α x‖) ≤ 3 * (C₂ * Z₂ / U ^ 3 + C₃ * (Z₁ * Z₃) / U ^ 4) := by
      rw [Fin.sum_univ_three]
      linarith [k2 0, k2 1, k2 2, k3 0, k3 1, k3 2]
    simp only [hSdef, faceIdRayAPSum]
    have e1 : (A₀ + A₁) / U ^ 2 = A₀ / U ^ 2 + A₁ / U ^ 2 := by ring
    have e3 : 3 * (C₂ * Z₂ / U ^ 3 + C₃ * (Z₁ * Z₃) / U ^ 4) =
        3 * C₂ * Z₂ / U ^ 3 + 3 * C₃ * (Z₁ * Z₃) / U ^ 4 := by ring
    linarith
  -- the weights
  have hω : ∀ k (e : Fin (m + 1) → ℤ), W k e a x = (U ^ k)⁻¹ *
      (z γ ^ a * (z t₁ ^ (-(1 / 100) : ℝ) * z t₂ ^ (-(1 / 100) : ℝ))) *
        ∏ t, z t ^ ((e t : ℝ) / 2) := fun k e => by
    simp only [hW, faceIdRayAQWt, ← hzdef, ← hUdef, faceIdRayAQ_prod_W hz γ t₁ t₂ ht e a]
    ring
  set ω := z γ ^ a * (z t₁ ^ (-(1 / 100) : ℝ) * z t₂ ^ (-(1 / 100) : ℝ)) with hωdef
  have w0 : W 2 0 a x = ω / U ^ 2 := by
    rw [hω]; simp [div_eq_mul_inv, mul_comm]
  have wT : W 2 eT a x = ω * τ / U ^ 2 := by
    rw [hω, faceIdRayAQ_prod_half_two hz i j (-1) (-1), hτ]
    push_cast
    rw [div_eq_mul_inv, mul_comm (U ^ 2)⁻¹ ω]
    ring_nf
  have w2 : ∀ u, W 3 (e₂ u) a x = ω * z u / U ^ 3 := fun u => by
    rw [hω]
    simp only [e₂]
    rw [faceIdRayAQ_prod_half_one u 2]
    norm_num
    rw [div_eq_mul_inv]; ring
  have w3 : ∀ u v, W 4 (e₃ u v) a x = ω * (z u * z v) / U ^ 4 := fun u v => by
    rw [hω]
    simp only [e₃]
    rw [faceIdRayAQ_prod_half_two hz u v 2 2]
    norm_num
    rw [div_eq_mul_inv]; ring
  have sum2 : ∑ u ∈ Finset.univ.filter J₂, W 3 (e₂ u) a x = ω * Z₂ / U ^ 3 := by
    calc ∑ u ∈ Finset.univ.filter J₂, W 3 (e₂ u) a x =
        ω / U ^ 3 * ∑ u ∈ Finset.univ.filter J₂, z u := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun u _ => by rw [w2]; ring
      _ = ω * Z₂ / U ^ 3 := by rw [Finset.sum_filter]; ring
  have sum3 : ∑ u ∈ Finset.univ.filter J₁, ∑ v ∈ Finset.univ.filter J₃, W 4 (e₃ u v) a x =
      ω * (Z₁ * Z₃) / U ^ 4 := by
    calc ∑ u ∈ Finset.univ.filter J₁, ∑ v ∈ Finset.univ.filter J₃, W 4 (e₃ u v) a x =
        ω / U ^ 4 * ∑ u ∈ Finset.univ.filter J₁, ∑ v ∈ Finset.univ.filter J₃, z u * z v := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by rw [w3]; ring
      _ = ω * (Z₁ * Z₃) / U ^ 4 := by
          rw [← Finset.sum_mul_sum, Finset.sum_filter, Finset.sum_filter]; ring
  have hω0 : 0 ≤ ω := mul_nonneg (Real.rpow_nonneg (hz0 γ) _)
    (mul_nonneg (Real.rpow_nonneg (hz0 t₁) _) (Real.rpow_nonneg (hz0 t₂) _))
  have hS0 : 0 ≤ S := faceIdRayAPSum_nonneg Q α _ cs x hB.le
  have hzγ : 0 ≤ z γ ^ a := Real.rpow_nonneg (hz0 γ) a
  calc z γ ^ a * B ^ (-(1 / 100) : ℝ) * S
      ≤ z γ ^ a * (c ^ (-(1 / 100) : ℝ) * (z t₁ ^ (-(1 / 100) : ℝ) *
          z t₂ ^ (-(1 / 100) : ℝ))) * S := by gcongr
    _ = c ^ (-(1 / 100) : ℝ) * ω * S := by rw [hωdef]; ring
    _ ≤ c ^ (-(1 / 100) : ℝ) * ω * ((A₀ + A₁) / U ^ 2 + K / 2 * τ / U ^ 2 +
          3 * C₂ * Z₂ / U ^ 3 + 3 * C₃ * (Z₁ * Z₃) / U ^ 4) := by gcongr
    _ = _ := by
        rw [w0, wT, sum2, sum3]
        ring

end QED.GradedProof.RPi4

end
