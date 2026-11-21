/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRayBFace

/-!
# (R-Π₄) step L10, B-inc: the weighted face and its rate

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10, the rate (B) of
the face-rate increment (`FaceRateIncB`). In the scaled frame the `σ`-derivative of a piece
contains the bracket of `n + 1` multiplied by a weight `ω(z)` (the second Symanzik function at
masses `0`), which is not of the form `FaceBr`. In join coordinates the weight is a function
`ωJ(ρ, W, V)`, and the abstract `σ`-integration (`SigData`) takes arbitrary coefficients, so the
face rate carries over with the coefficients `coefJ · ωJ`:

* `FaceShape.hJw`, `FaceShape.gJw`, `FaceShape.fUw`: the weighted face integrand, face function
  and collapsed integrand; `FaceShape.hJw_eq`, `FaceShape.gJw_eq_sigG`;
* `FaceShape.integrand_join_eq_w`: the weighted integrand in join coordinates;
* `FaceShape.integral_faceCut_eq_of`: the face sector of any integrand whose join form is given
  (the argument of `FaceShape.integral_faceCut_eq` with the integrand abstracted);
* `faceIdRayW_sigData`, `faceIdRayW_face_rate`: the face rate `C (1 + c₁⁻¹)^N u^{-1/2}` for
  arbitrary uniformly Lipschitz coefficients;
* **`faceIdRayW_face_rate_w`**, **`faceIdRayW_face_sector_rate`**: the same for the weighted face.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)

/-! ### The weighted face -/

namespace FaceShape

variable {p q r : ℕ} (S : FaceShape p q) (B : FaceBr r)
  (ωJ : ℝ → (Fin (p + 1) → ℝ) → (Fin (q + 1) → ℝ) → ℝ)

/-- The weighted coefficients `coefJ · ωJ` on the product. -/
noncomputable def coefXw (j : Fin r) (ρ : ℝ) (x : (Fin p → ℝ) × (Fin q → ℝ)) : ℂ :=
  S.coefX B j ρ x * (ωJ ρ (simplexPoint x.1) (simplexPoint x.2) : ℂ)

/-- **The weighted face integrand** `θ ∑ⱼ coefJⱼ ωJ (vHat + θσ)^{-kⱼ}`. -/
noncomputable def hJw (ρ σ : ℝ) (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) : ℂ :=
  (W S.γ : ℂ) * ∑ j, S.coefJ B j ρ W V * (ωJ ρ W V : ℂ) *
    (((S.vHat ρ W V + W S.γ * σ : ℝ) : ℂ) ^ B.k j)⁻¹

/-- **The weighted face function** `(1 - ρ)^q ∫_{Δ_p × Δ_q} hJw ρ σ`. -/
noncomputable def gJw (ρ σ : ℝ) : ℂ :=
  (((1 - ρ) ^ q : ℝ) : ℂ) * ∫ x in simplexSet p ×ˢ simplexSet q,
    S.hJw B ωJ ρ σ (simplexPoint x.1) (simplexPoint x.2)

theorem gJw_eq_sigG (ρ σ : ℝ) :
    S.gJw B ωJ ρ σ = sigG (volume.restrict (simplexSet p ×ˢ simplexSet q)) q S.thetaX
      (S.coefXw B ωJ) S.vX B.k ρ σ := rfl

theorem hJw_eq (ρ σ : ℝ) (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) :
    S.hJw B ωJ ρ σ W V = (ωJ ρ W V : ℂ) * S.hJ B ρ σ W V := by
  simp only [hJw, hJ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The weighted collapsed integrand `ω(z) fU`. -/
noncomputable def fUw (ω : (Fin (p + 1 + q + 1) → ℝ) → ℝ) (n : ℕ) (Q : LoopQuartic) (u : ℝ)
    (z : Fin (p + 1 + q + 1) → ℝ) : ℂ :=
  (ω z : ℂ) * S.fU n Q u z

variable {B} {n : ℕ} {Q : LoopQuartic}

/-- **The weighted integrand in join coordinates is the weighted face integrand** (`ρ > 0`),
when the weight in join coordinates is `ωJ`. -/
theorem integrand_join_eq_w (hB : B.Rep n p Q S.α S.pp) {ρ : ℝ} (hρ : 0 < ρ)
    (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) (hu : S.uJ ρ W V ≠ 0) (u : ℝ)
    {ω : (Fin (p + 1 + q + 1) → ℝ) → ℝ} (hω : ω (joinZ ρ W V) = ωJ ρ W V) :
    (ρ : ℂ) ^ p * S.fUw ω n Q u (joinZ ρ W V) = S.hJw B ωJ ρ (ρ * u) W V := by
  rw [hJw_eq, ← S.integrand_join_eq hB hρ W V hu u, fUw, hω]
  ring

end FaceShape

namespace FaceShape

variable {p q : ℕ}

/-- **The face sector of an integrand with a given join form**: if `ρ^p F(joinZ ρ W V) = H ρ W V`
for `0 < ρ < 1`, then the integral over the simplex of `F` cut to `{∑_{face block} z ≤ ρ₀}` is
`∫₀^{ρ₀} (1 - ρ)^q ∫_{Δ_p × Δ_q} H ρ dρ`. -/
theorem integral_faceCut_eq_of (F : (Fin (p + 1 + q + 1) → ℝ) → ℂ)
    (H : ℝ → (Fin (p + 1) → ℝ) → (Fin (q + 1) → ℝ) → ℂ) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hρ₁ : ρ₀ < 1)
    (hpt : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ w ∈ simplexSet p, ∀ v ∈ simplexSet q,
      (ρ : ℂ) ^ p * F (joinZ ρ (simplexPoint w) (simplexPoint v)) =
        H ρ (simplexPoint w) (simplexPoint v))
    (hf : IntegrableOn (fun x => F (simplexPoint x)) (simplexSet (p + 1 + q)))
    (hHi : ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → IntegrableOn
      (fun x : (Fin p → ℝ) × (Fin q → ℝ) => H ρ (simplexPoint x.1) (simplexPoint x.2))
      (simplexSet p ×ˢ simplexSet q)) :
    ∫ x in simplexSet (p + 1 + q), {z | blockSum z ≤ ρ₀}.indicator F (simplexPoint x) =
      ∫ ρ in (0 : ℝ)..ρ₀, (((1 - ρ) ^ q : ℝ) : ℂ) * ∫ x in simplexSet p ×ˢ simplexSet q,
        H ρ (simplexPoint x.1) (simplexPoint x.2) := by
  have hm : MeasurableSet ((fun x : Fin (p + 1 + q) → ℝ => simplexPoint x) ⁻¹'
      {z | blockSum z ≤ ρ₀}) :=
    continuous_simplexPoint'.measurable (measurableSet_blockSum_le ρ₀)
  have hf' : IntegrableOn (fun x => {z | blockSum z ≤ ρ₀}.indicator F (simplexPoint x))
      (simplexSet (p + 1 + q)) := by
    have := hf.indicator hm
    refine this.congr_fun (fun x _ => ?_) (measurableSet_simplexSet _)
    by_cases hx : simplexPoint x ∈ {z | blockSum z ≤ ρ₀}
    · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ _ from hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (show x ∉ _ from hx)]
  set G : ℝ → ℂ := fun ρ => (ρ ^ p * (1 - ρ) ^ q) • ∫ w in simplexSet p,
    ∫ v in simplexSet q, F (joinZ ρ (simplexPoint w) (simplexPoint v)) with hG
  have hcut : ∀ ρ, (ρ ^ p * (1 - ρ) ^ q) • ∫ w in simplexSet p, ∫ v in simplexSet q,
      {z | blockSum z ≤ ρ₀}.indicator F (joinZ ρ (simplexPoint w) (simplexPoint v)) =
      (Iic ρ₀).indicator G ρ := by
    intro ρ
    have hb : ∀ (w : Fin p → ℝ) (v : Fin q → ℝ),
        blockSum (p := p) (q := q) (joinZ ρ (simplexPoint w) (simplexPoint v)) = ρ :=
      fun w v => blockSum_joinZ ρ w _
    by_cases hρ : ρ ≤ ρ₀
    · rw [indicator_of_mem (show ρ ∈ Iic ρ₀ from hρ)]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun w => integral_congr_ae (ae_of_all _ fun v => ?_))
      exact indicator_of_mem (s := {z : Fin (p + 1 + q + 1) → ℝ | blockSum z ≤ ρ₀})
        (show blockSum (p := p) (q := q) (joinZ ρ (simplexPoint w) (simplexPoint v)) ≤ ρ₀ by
          rw [hb w v]; exact hρ) F
    · rw [indicator_of_notMem (show ρ ∉ Iic ρ₀ from hρ)]
      have h0 : ∀ (w : Fin p → ℝ) (v : Fin q → ℝ), {z | blockSum z ≤ ρ₀}.indicator F
          (joinZ ρ (simplexPoint w) (simplexPoint v)) = 0 := fun w v =>
        indicator_of_notMem (show joinZ ρ (simplexPoint w) (simplexPoint v) ∉
          {z : Fin (p + 1 + q + 1) → ℝ | blockSum z ≤ ρ₀} from fun h => hρ (by
            have h' : blockSum (p := p) (q := q) (joinZ ρ (simplexPoint w) (simplexPoint v)) ≤ ρ₀ :=
              h
            rwa [hb w v] at h')) _
      simp only [h0, integral_zero, smul_zero]
  rw [integral_simplex_join hf']
  refine (intervalIntegral.integral_congr (fun ρ _ => hcut ρ)).trans ?_
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hρ₀.le,
    setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hρ₁.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun ρ hρ => ?_
  have hρ0 : 0 < ρ := hρ.1
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρ.2 hρ₁
  have hprod := setIntegral_prod (μ := (volume : Measure (Fin p → ℝ)))
    (ν := (volume : Measure (Fin q → ℝ)))
    (fun x : (Fin p → ℝ) × (Fin q → ℝ) => H ρ (simplexPoint x.1) (simplexPoint x.2))
    (s := simplexSet p) (t := simplexSet q)
    (by rw [← Measure.volume_eq_prod]; exact hHi ρ hρ0 hρ.2)
  rw [← Measure.volume_eq_prod] at hprod
  rw [hprod, hG]
  dsimp only
  rw [Complex.real_smul, ofReal_mul, ofReal_pow, mul_comm ((ρ : ℂ) ^ p), mul_assoc,
    ← integral_const_mul]
  congr 1
  refine setIntegral_congr_fun (measurableSet_simplexSet p) fun w hw => ?_
  rw [← integral_const_mul]
  exact setIntegral_congr_fun (measurableSet_simplexSet q) fun v hv => hpt ρ hρ0 hρ1 w hw v hv

end FaceShape

/-! ### The face rate for arbitrary coefficients -/

section Gen

variable {ι : Type*} {p q r : ℕ} {S : ι → FaceShape p q} {k : Fin r → ℕ} {ρ₀ K KM : ℝ}

/-- **The `SigData` of each member for arbitrary coefficients `D`**, uniformly bounded and
Lipschitz over the family, with common constants and the member's own lower bound `c₁ s`. -/
theorem faceIdRayW_sigData (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hK : ∀ s, (S s).kF ≤ K)
    (hKM : ∀ s, (S s).kM ≤ KM) (hk : ∀ j, 2 ≤ k j)
    (D : ι → Fin r → ℝ → (Fin p → ℝ) × (Fin q → ℝ) → ℂ)
    (hDm : ∀ s j, Measurable fun y : ℝ × ((Fin p → ℝ) × (Fin q → ℝ)) => D s j y.1 y.2)
    (hD : ∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx p q) ρ => D i.1 j ρ i.2.1)
    (c₁ : ι → ℝ) (hc₁ : ∀ s, 0 < c₁ s)
    (hV : ∀ s ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ x ∈ simplexSet p ×ˢ simplexSet q,
      c₁ s ≤ symanzikV (S s).α (S s).pp (S s).M (joinZ ρ (simplexPoint x.1) (simplexPoint x.2))) :
    ∃ BD LD LV : ℝ, 0 ≤ BD ∧ 0 ≤ LD ∧ 0 ≤ LV ∧ ∀ s,
      SigData (volume.restrict (simplexSet p ×ˢ simplexSet q)) ρ₀ (c₁ s) BD LD LV
        (S s).thetaX (D s) (S s).vX k := by
  choose Bf Lf hBL using hD
  obtain ⟨BV, LV, hBLV⟩ := FaceShape.unifLip_vHat S hK hρ₁ hKM
  have hBj : ∀ j, |Bf j| ≤ ∑ j, |Bf j| := fun j =>
    Finset.single_le_sum (f := fun j => |Bf j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hLj : ∀ j, |Lf j| ≤ ∑ j, |Lf j| := fun j =>
    Finset.single_le_sum (f := fun j => |Lf j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hm := FaceShape.measurableSet_prod (p := p) (q := q)
  refine ⟨∑ j, |Bf j|, ∑ j, |Lf j|, |LV|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    Finset.sum_nonneg fun _ _ => abs_nonneg _, abs_nonneg _, fun s => ⟨hc₁ s, hρ₀, hρ₁.le, ?_,
    ?_, ?_, hk, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    Finset.sum_nonneg fun _ _ => abs_nonneg _, abs_nonneg _, ?_,
    hDm s, FaceShape.measurable_vX⟩⟩
  · exact ae_restrict_of_forall_mem hm fun x hx =>
      ⟨FaceShape.Wi_nonneg (⟨x, hx⟩ : FaceIdx p q) (S s).γ,
        FaceShape.Wi_le_one (⟨x, hx⟩ : FaceIdx p q) (S s).γ⟩
  · refine ae_restrict_of_forall_mem hm fun x hx j ρ hρ hρ' => ?_
    obtain ⟨h1, h2⟩ := hBL j (s, ⟨x, hx⟩) ρ hρ hρ'
    exact ⟨h1.trans ((le_abs_self _).trans (hBj j)),
      h2.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hLj j)) hρ)⟩
  · refine ae_restrict_of_forall_mem hm fun x hx ρ hρ hρ' => ⟨?_, ?_⟩
    · exact (S s).vHat_ge hρ₀ hρ₁ (hV s) ⟨x, hx⟩ hρ hρ'
    · have := (hBLV (s, ⟨x, hx⟩) ρ hρ hρ').2
      rw [← ofReal_sub, norm_real, Real.norm_eq_abs] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hρ)
  · exact (continuous_apply (S s).γ).measurable.comp
      (continuous_simplexPoint'.measurable.comp measurable_fst)

end Gen

section GenRate

variable {ι : Type*} {p q r : ℕ} {S : ι → FaceShape (p + 1) q} {k : Fin r → ℕ} {ρ₀ K KM : ℝ}

/-- **The face limit for arbitrary uniformly Lipschitz coefficients, with rate
`C (1 + c₁⁻¹)^N u^{-1/2}`** (photon last in the face block; `V₀ ≥ c₁ s` per member). -/
theorem faceIdRayW_face_rate (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hK : ∀ s, (S s).kF ≤ K)
    (hKM : ∀ s, (S s).kM ≤ KM) (hk : ∀ j, 2 ≤ k j)
    (D : ι → Fin r → ℝ → (Fin (p + 1) → ℝ) × (Fin q → ℝ) → ℂ)
    (hDm : ∀ s j, Measurable fun y : ℝ × ((Fin (p + 1) → ℝ) × (Fin q → ℝ)) => D s j y.1 y.2)
    (hD : ∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx (p + 1) q) ρ => D i.1 j ρ i.2.1)
    (c₁ : ι → ℝ) (hc₁ : ∀ s, 0 < c₁ s)
    (hV : ∀ s ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ x ∈ simplexSet (p + 1) ×ˢ simplexSet q,
      c₁ s ≤ symanzikV (S s).α (S s).pp (S s).M (joinZ ρ (simplexPoint x.1) (simplexPoint x.2)))
    (hγ : ∀ s, (S s).γ = Fin.last (p + 1)) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ s, ∀ u : ℝ, 0 < u →
      ‖u • (∫ ρ in (0 : ℝ)..ρ₀, sigG (volume.restrict (simplexSet (p + 1) ×ˢ simplexSet q)) q
          (S s).thetaX (D s) (S s).vX k ρ (ρ * u)) -
        ∫ σ in Ioi 0, sigG (volume.restrict (simplexSet (p + 1) ×ˢ simplexSet q)) q
          (S s).thetaX (D s) (S s).vX k 0 σ‖ ≤
        C * (1 + (c₁ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ) := by
  obtain ⟨BD, LD, LV, hBD, hLD, hLV, hS⟩ :=
    faceIdRayW_sigData hρ₀ hρ₁ hK hKM hk D hDm hD c₁ hc₁ hV
  set V₀ := (volume (simplexSet q)).toReal * (volume (simplexSet p)).toReal with hV₀
  have hV₀0 : 0 ≤ V₀ := by positivity
  set K₀ := ∑ _j : Fin r, BD
  set K₁ := ∑ j, (LD + BD * k j * LV)
  have hK₀ : 0 ≤ K₀ := Finset.sum_nonneg fun _ _ => hBD
  have hK₁ : 0 ≤ K₁ := Finset.sum_nonneg fun _ _ => by positivity
  set N₀ := ∑ j, k j
  refine ⟨4 * V₀ * ((q * K₀ + K₁) * ρ₀ ^ (1 / 2 : ℝ) + K₀ * ρ₀ ^ (-(1 / 2) : ℝ)), N₀ + 1,
    fun s u hu => ?_⟩
  set c := c₁ s
  have hc := hc₁ s
  set A := (volume (simplexSet q)).toReal * ((volume (simplexSet p)).toReal *
    (2 * c ^ (-(1 / 2) : ℝ)))
  have hA : ∀ σ, 0 < σ → ∫ x in simplexSet (p + 1) ×ˢ simplexSet q,
      sigM (S s).thetaX c σ x ≤ A * σ ^ (-(3 / 2) : ℝ) := fun σ hσ => by
    have e : (S s).thetaX = fun x : (Fin (p + 1) → ℝ) × (Fin q → ℝ) =>
        simplexPoint x.1 (Fin.last (p + 1)) := by
      funext x; simp only [FaceShape.thetaX, hγ]
    rw [e]
    refine (integral_sigM_prod_le hc hσ).trans (le_of_eq ?_)
    simp only [A]; ring
  have h := (hS s).norm_sigma_face_le q hA hu
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hu.le _))
  obtain ⟨e0, e1⟩ := faceIdRayB_sigK_le (r := r) hc hBD hLD hLV k
  have hW : 1 ≤ 1 + c⁻¹ := by have := inv_pos.2 hc; linarith
  have hWN : 0 ≤ (1 + c⁻¹) ^ N₀ := by positivity
  have hρa : 0 ≤ ρ₀ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hρ₀.le _
  have hρb : 0 ≤ ρ₀ ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hρ₀.le _
  have hs0 : 0 ≤ sigK₀ c BD k := (hS s).sigK₀_nonneg
  have hs1 : 0 ≤ sigK₁ c BD LD LV k := (hS s).sigK₁_nonneg
  have hA' : A ≤ 2 * V₀ * (1 + c⁻¹) := by
    have := faceIdRayB_rpow_le hc
    simp only [A, hV₀]
    have h0 : 0 ≤ (volume (simplexSet q)).toReal * (volume (simplexSet p)).toReal := by
      positivity
    nlinarith
  have hA0 : 0 ≤ A := by positivity
  have hX : (q * sigK₀ c BD k + sigK₁ c BD LD LV k) * ρ₀ ^ (1 / 2 : ℝ) +
      sigK₀ c BD k * ρ₀ ^ (-(1 / 2) : ℝ) ≤
      ((q * K₀ + K₁) * ρ₀ ^ (1 / 2 : ℝ) + K₀ * ρ₀ ^ (-(1 / 2) : ℝ)) * (1 + c⁻¹) ^ N₀ := by
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have f1 : q * sigK₀ c BD k ≤ q * (K₀ * (1 + c⁻¹) ^ N₀) := mul_le_mul_of_nonneg_left e0 hq
    have f2 := mul_le_mul_of_nonneg_right (add_le_add f1 e1) hρa
    have f3 := mul_le_mul_of_nonneg_right e0 hρb
    nlinarith
  have hX0 : 0 ≤ (q * sigK₀ c BD k + sigK₁ c BD LD LV k) * ρ₀ ^ (1 / 2 : ℝ) +
      sigK₀ c BD k * ρ₀ ^ (-(1 / 2) : ℝ) := by positivity
  set X := (q * K₀ + K₁) * ρ₀ ^ (1 / 2 : ℝ) + K₀ * ρ₀ ^ (-(1 / 2) : ℝ)
  calc 2 * A * ((q * sigK₀ c BD k + sigK₁ c BD LD LV k) * ρ₀ ^ (1 / 2 : ℝ) +
        sigK₀ c BD k * ρ₀ ^ (-(1 / 2) : ℝ))
      ≤ 2 * (2 * V₀ * (1 + c⁻¹)) * (X * (1 + c⁻¹) ^ N₀) :=
        mul_le_mul (by linarith) hX hX0 (by positivity)
    _ = 4 * V₀ * X * (1 + c⁻¹) ^ (N₀ + 1) := by rw [pow_succ]; ring

end GenRate

/-! ### The weighted face rate -/

section Weighted

variable {ι : Type*} {p q r : ℕ} {S : ι → FaceShape (p + 1) q} {B : ι → FaceBr r}
  {k : Fin r → ℕ} {ρ₀ K KM : ℝ}
  {ωJ : ι → ℝ → (Fin (p + 1 + 1) → ℝ) → (Fin (q + 1) → ℝ) → ℝ}

/-- The weighted coefficients are jointly measurable. -/
theorem faceIdRayW_measurable_coefXw {s : ι} (hB : (B s).Meas)
    (hω : Measurable fun y : ℝ × ((Fin (p + 1) → ℝ) × (Fin q → ℝ)) =>
      ωJ s y.1 (simplexPoint y.2.1) (simplexPoint y.2.2)) (j : Fin r) :
    Measurable fun y : ℝ × ((Fin (p + 1) → ℝ) × (Fin q → ℝ)) =>
      (S s).coefXw (B s) (ωJ s) j y.1 y.2 :=
  (FaceShape.measurable_coefX hB j).mul (Complex.measurable_ofReal.comp hω)

/-- **The weighted face limit of a family of face shapes, with rate
`C (1 + c₁⁻¹)^N u^{-1/2}`**: the coefficients `coefJ · ωJ` uniformly Lipschitz over the family. -/
theorem faceIdRayW_face_rate_w (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hK : ∀ s, (S s).kF ≤ K)
    (hKM : ∀ s, (S s).kM ≤ KM) (hkc : ∀ s, (B s).k = k) (hk : ∀ j, 2 ≤ k j)
    (hB : ∀ s, (B s).Meas)
    (hωm : ∀ s, Measurable fun y : ℝ × ((Fin (p + 1) → ℝ) × (Fin q → ℝ)) =>
      ωJ s y.1 (simplexPoint y.2.1) (simplexPoint y.2.2))
    (hD : ∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx (p + 1) q) ρ =>
      (S i.1).coefJ (B i.1) j ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2) *
        (ωJ i.1 ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2) : ℂ))
    (c₁ : ι → ℝ) (hc₁ : ∀ s, 0 < c₁ s)
    (hV : ∀ s ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ x ∈ simplexSet (p + 1) ×ˢ simplexSet q,
      c₁ s ≤ symanzikV (S s).α (S s).pp (S s).M (joinZ ρ (simplexPoint x.1) (simplexPoint x.2)))
    (hγ : ∀ s, (S s).γ = Fin.last (p + 1)) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ s, ∀ u : ℝ, 0 < u →
      ‖u • (∫ ρ in (0 : ℝ)..ρ₀, (S s).gJw (B s) (ωJ s) ρ (ρ * u)) -
        ∫ σ in Ioi 0, (S s).gJw (B s) (ωJ s) 0 σ‖ ≤
        C * (1 + (c₁ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ) := by
  obtain ⟨C, N, hC⟩ := faceIdRayW_face_rate hρ₀ hρ₁ hK hKM hk
    (fun s => (S s).coefXw (B s) (ωJ s))
    (fun s j => faceIdRayW_measurable_coefXw (hB s) (hωm s) j) hD c₁ hc₁ hV hγ
  refine ⟨C, N, fun s u hu => ?_⟩
  simp only [FaceShape.gJw_eq_sigG, hkc s]
  exact hC s u hu

/-- **The face sector of the weighted collapsed density of a family of face shapes, with rate
`C (1 + c₁⁻¹)^N u^{-1/2}`**, for a weight `ω` whose join form is `ωJ`. -/
theorem faceIdRayW_face_sector_rate (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hK : ∀ s, (S s).kF ≤ K)
    (hKM : ∀ s, (S s).kM ≤ KM) (hkc : ∀ s, (B s).k = k) (hk : ∀ j, 2 ≤ k j)
    (hB : ∀ s, (B s).Meas)
    (hωm : ∀ s, Measurable fun y : ℝ × ((Fin (p + 1) → ℝ) × (Fin q → ℝ)) =>
      ωJ s y.1 (simplexPoint y.2.1) (simplexPoint y.2.2))
    (hD : ∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx (p + 1) q) ρ =>
      (S i.1).coefJ (B i.1) j ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2) *
        (ωJ i.1 ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2) : ℂ))
    (c₁ : ι → ℝ) (hc₁ : ∀ s, 0 < c₁ s)
    (hV : ∀ s ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ x ∈ simplexSet (p + 1) ×ˢ simplexSet q,
      c₁ s ≤ symanzikV (S s).α (S s).pp (S s).M (joinZ ρ (simplexPoint x.1) (simplexPoint x.2)))
    (hγ : ∀ s, (S s).γ = Fin.last (p + 1)) {n : ℕ} {Q : ι → LoopQuartic}
    (hRep : ∀ s, (B s).Rep n (p + 1) (Q s) (S s).α (S s).pp)
    {ω : ι → (Fin (p + 1 + 1 + q + 1) → ℝ) → ℝ}
    (hωJ : ∀ s ρ, 0 < ρ → ρ < 1 → ∀ w ∈ simplexSet (p + 1), ∀ v ∈ simplexSet q,
      ω s (joinZ ρ (simplexPoint w) (simplexPoint v)) =
        ωJ s ρ (simplexPoint w) (simplexPoint v)) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => (S s).fUw (ω s) n (Q s) u (simplexPoint x))
        (simplexSet (p + 1 + 1 + q)) →
      ‖u • (∫ x in simplexSet (p + 1 + 1 + q),
          {z | FaceShape.blockSum z ≤ ρ₀}.indicator ((S s).fUw (ω s) n (Q s) u)
            (simplexPoint x)) -
        ∫ σ in Ioi 0, (S s).gJw (B s) (ωJ s) 0 σ‖ ≤
        C * (1 + (c₁ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ) := by
  obtain ⟨C, N, hC⟩ := faceIdRayW_face_rate_w hρ₀ hρ₁ hK hKM hkc hk hB hωm hD c₁ hc₁ hV hγ
  obtain ⟨BD, LD, LV, -, -, -, hS⟩ := faceIdRayW_sigData hρ₀ hρ₁ hK hKM hk
    (fun s => (S s).coefXw (B s) (ωJ s))
    (fun s j => faceIdRayW_measurable_coefXw (hB s) (hωm s) j) hD c₁ hc₁ hV
  refine ⟨C, N, fun s u hu hf => ?_⟩
  have e := FaceShape.integral_faceCut_eq_of ((S s).fUw (ω s) n (Q s) u)
    (fun ρ => (S s).hJw (B s) (ωJ s) ρ (ρ * u)) hρ₀ hρ₁
    (fun ρ hρ hρ1 w hw v hv => by
      obtain ⟨hw0, hw1⟩ := simplexPoint_mem_stdSimplex hw
      obtain ⟨-, hv1⟩ := simplexPoint_mem_stdSimplex hv
      refine (S s).integrand_join_eq_w (ωJ s) (hRep s) hρ _ _ (ne_of_gt ?_) u
        (hωJ s ρ hρ hρ1 w hw v hv)
      linarith [(S s).uJ_ge ρ _ _ hw0 hw1 hv1 hρ.le])
    hf (fun ρ hρ hρ' => by
      have := (hS s).integrable_sigH hρ.le hρ' (mul_nonneg hρ.le hu.le)
      rw [← hkc s] at this
      exact this)
  rw [e]
  exact hC s u hu

end Weighted

end QED.GradedProof.RPi4

end
