/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCBB2CovPow
public import QED.ChainProof.HCBB2CovNum
public import QED.ChainProof.HCBB2Limit

/-!
# Covariance of the bubble–bubble limits

Helper level, Phase 5 Stage 1a (O3-8 for `QED.ChainProof.Enum.repBB`). This file proves the
one-loop statement `QED.ChainProof.HCBB.BBCov`:

* `integrable_oneLim`, `integrable_twoLim`: the pointwise limits of the one- and two-insertion
  pieces are integrable in the Feynman parameters (they are bounded limits of measurable
  functions);
* `covRel_integral`: covariance passes through integrals of integrable matrix families;
* `covRel_ggLim`: for a covariant numerator family, the limits of two spectral factors
  (`QED.ChainProof.HCBB2.ggInt`) on the six photon-type denominators `ms6` at `(p', p)` and
  `(L p', L p)` are related by `S G'^μ T = L^μ_ν G^ν`; the limit `ggLimit` is a combination of
  `powLimit`, integrals of `specLimit`s with coefficients independent of the momenta, all
  covariant by `QED.ChainProof.HCBB2.covRel_specM`;
* `bbLim_eq`: the limits `BBLim` are `(1/i) κ (Λ² - m_γ²)³ ∑ₙ cₙ(0) Gₙ`, with `Gₙ` the limits of
  the nine pieces `bbPiece`;
* **`bbCov`**: `QED.ChainProof.HCBB.BBCov` holds.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Matrix
open scoped Real

namespace QED.ChainProof.HCBB2

open QED.OneLoop QED.OneLoop.VertexLimit QED.WickModel
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtAssembly
open QED.TwoLoop.VPHalfAt QED.TwoLoop.VPHalfAtGen QED.TwoLoop.Insertion QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.Dirac QED.ChainProof.HCBB

/-! ### Integrability of the pointwise limits -/

/-- `1/(n+1) → 0⁺`. -/
theorem tendsto_inv_succ_nhdsGT :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩

theorem inv_succ_le_one (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

section Integrable

variable {P : Params} {N : (Fin 4 → ℝ) → ℂ} {k : ℕ} {Ms : Fin (k + 2) → ℝ} {j : ℕ}
  {p' p : Fin 4 → ℝ} {α : ℂ} {CN M₀ : ℝ}

theorem integrable_oneLim (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hM₀ : 0 < M₀) (hM₀m : M₀ ≤ P.m) (hMs : ∀ i, M₀ ≤ Ms i)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (hjk : j + 1 ≤ k) {w : ℝ → ℂ}
    (hw : Measurable w) {W : ℝ} (hW : ∀ x ∈ Ioo (0 : ℝ) 1, ‖w x‖ ≤ W) :
    Integrable (oneLim P α N Ms j w p' p) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  obtain ⟨C, hg⟩ := exists_good_oneInt hm hM₁ hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 hNc hNq hNb hjk hW
  have hT : ∀ x ∈ Ioo (0 : ℝ) 1, Tendsto (fun n : ℕ => energyFirstIntegral
      (oneInt P N Ms j w (1 / ((n : ℝ) + 1)) p' p x)) atTop (𝓝 (oneLim P α N Ms j w p' p x)) :=
    fun x hx => (tendsto_efi_oneInt hm hM₁ hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 hNc hNq hNb hjk w
      hx).comp tendsto_inv_succ_nhdsGT
  have hmeas : AEStronglyMeasurable (oneLim P α N Ms j w p' p)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun n => ?_) (ae_Ioc_good hT)
    obtain ⟨G, hG⟩ := hg _ (by positivity) (inv_succ_le_one n)
    exact aestronglyMeasurable_efi_param _ (measurable_oneInt P hNc Ms j hw _ p' p)
      (ae_Ioc_good hG)
  refine Integrable.mono' (integrable_const (C * I5)) hmeas (ae_Ioc_good fun x hx => ?_)
  refine le_of_tendsto (hT x hx).norm (Eventually.of_forall fun n => ?_)
  obtain ⟨G, hG⟩ := hg _ (by positivity) (inv_succ_le_one n)
  exact (hG x hx).1.norm_efi_le

theorem integrable_twoLim (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hM₀ : 0 < M₀) (hM₀m : M₀ ≤ P.m) (hMs : ∀ i, M₀ ≤ Ms i)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (hjk : j + 2 ≤ k) {w₁ w₂ : ℝ → ℂ}
    (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) {W₁ W₂ : ℝ}
    (hW₁ : ∀ x ∈ Ioo (0 : ℝ) 1, ‖w₁ x‖ ≤ W₁) (hW₂ : ∀ x ∈ Ioo (0 : ℝ) 1, ‖w₂ x‖ ≤ W₂) :
    Integrable (twoLim P α N Ms j w₁ w₂ p' p) nu2 := by
  obtain ⟨C, hg⟩ := exists_good_twoInt hm hM₁ hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 hNc hNq hNb hjk
    hW₁ hW₂
  have hT : ∀ z : ℝ × ℝ, z.1 ∈ Ioo (0 : ℝ) 1 → z.2 ∈ Ioo (0 : ℝ) 1 →
      Tendsto (fun n : ℕ => energyFirstIntegral
        (twoInt P N Ms j w₁ w₂ (1 / ((n : ℝ) + 1)) p' p z)) atTop
        (𝓝 (twoLim P α N Ms j w₁ w₂ p' p z)) :=
    fun z hx hy => (tendsto_efi_twoInt hm hM₁ hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 hNc hNq hNb hjk
      w₁ w₂ hx hy).comp tendsto_inv_succ_nhdsGT
  have hmeas : AEStronglyMeasurable (twoLim P α N Ms j w₁ w₂ p' p) nu2 := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun n => ?_)
      (by filter_upwards [ae_nu2_mem] with z ⟨hx, hy⟩ using hT z hx hy)
    obtain ⟨G, hG⟩ := hg _ (by positivity) (inv_succ_le_one n)
    exact aestronglyMeasurable_efi_param _ (measurable_twoInt P hNc Ms j hw₁ hw₂ _ p' p)
      (by filter_upwards [ae_nu2_mem] with z ⟨hx, hy⟩ using hG z hx hy)
  refine Integrable.mono' (integrable_const (C * I5)) hmeas ?_
  filter_upwards [ae_nu2_mem] with z ⟨hx, hy⟩
  refine le_of_tendsto (hT z hx hy).norm (Eventually.of_forall fun n => ?_)
  obtain ⟨G, hG⟩ := hg _ (by positivity) (inv_succ_le_one n)
  exact (hG z hx hy).1.norm_efi_le

end Integrable

/-! ### Covariance through integrals -/

theorem covRel_integral {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
    {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {F F' : X → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hF : ∀ μ i j, Integrable (fun x => F x μ i j) ν)
    (hF' : ∀ μ i j, Integrable (fun x => F' x μ i j) ν)
    (h : ∀ᵐ x ∂ν, CovRel L S T (F x) (F' x)) :
    CovRel L S T (fun μ => Matrix.of fun i j => ∫ x, F x μ i j ∂ν)
      (fun μ => Matrix.of fun i j => ∫ x, F' x μ i j ∂ν) := by
  intro μ
  ext a b
  have e1 : (S * (Matrix.of fun i j => ∫ x, F' x μ i j ∂ν) * T) a b =
      ∫ x, (S * F' x μ * T) a b ∂ν := by
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ =>
      ((hF' μ d c).const_mul _).mul_const _]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finsetSum _ fun d _ => ((hF' μ d c).const_mul _).mul_const _]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [integral_mul_const, integral_const_mul]
  have e2 : (vecAct L (fun ν' => Matrix.of fun i j => ∫ x, F x ν' i j ∂ν) μ) a b =
      ∫ x, (vecAct L (F x) μ) a b ∂ν := by
    simp only [vecAct, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [integral_finsetSum _ fun c _ => (hF c a b).const_mul _]
    exact Finset.sum_congr rfl fun c _ => (integral_const_mul _ _).symm
  rw [e1, e2]
  exact integral_congr_ae (by filter_upwards [h] with x hx using by rw [hx μ])

/-! ### The matrices of the two-spectral-factor limits -/

section Mat

variable (P : Params) (α : Fin 4 → Fin 4 → Fin 4 → ℂ)
  (E : Fin 4 → Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ) (j : ℕ) (p' p : Fin 4 → ℝ)

/-- The matrices of `oneLim`. -/
noncomputable def oneM (w : ℝ → ℂ) (x : ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun i i' => oneLim P (α μ i i') (E μ i i') (ms6 P) j w p' p x

/-- The matrices of `twoLim`. -/
noncomputable def twoM (w₁ w₂ : ℝ → ℂ) (z : ℝ × ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun i i' => twoLim P (α μ i i') (E μ i i') (ms6 P) j w₁ w₂ p' p z

theorem oneM_eq (w : ℝ → ℂ) (x : ℝ) :
    oneM P α E j p' p w x = ∑ f, ((P.loopCoeff f : ℂ) * (((1 - 2 * x : ℝ) : ℂ) * w x)) •
      specM α E P.m p' p (j + 1) 1 (ms6 P) ![P.mass f] ![x] := by
  funext μ
  ext i i'
  simp only [oneM, oneLim, specM, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]

theorem twoM_eq (w₁ w₂ : ℝ → ℂ) (z : ℝ × ℝ) :
    twoM P α E j p' p w₁ w₂ z = ∑ f, ∑ g, ((P.loopCoeff f : ℂ) * (P.loopCoeff g : ℂ) *
      ((((1 - 2 * z.1 : ℝ) : ℂ) * w₁ z.1) * (((1 - 2 * z.2 : ℝ) : ℂ) * w₂ z.2))) •
      specM α E P.m p' p (j + 2) 2 (ms6 P) ![P.mass f, P.mass g] ![z.1, z.2] := by
  funext μ
  ext i i'
  simp only [twoM, twoLim, specM, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]

theorem ggLimit_mat_eq (a₁ a₂ : ℂ) (w₁ w₂ : ℝ → ℂ) :
    (fun μ => Matrix.of fun i i' =>
      ggLimit P (α μ i i') (E μ i i') (ms6 P) j a₁ a₂ w₁ w₂ p' p) =
      (a₁ * a₂ * logSum P 0 ^ 2) • powM α E P.m p' p j (ms6 P) -
        (a₁ * logSum P 0) • (fun μ => Matrix.of fun i i' =>
          ∫ x in Ioc (0 : ℝ) 1, oneM P α E j p' p w₂ x μ i i') -
        (a₂ * logSum P 0) • (fun μ => Matrix.of fun i i' =>
          ∫ x in Ioc (0 : ℝ) 1, oneM P α E j p' p w₁ x μ i i') +
        (fun μ => Matrix.of fun i i' => ∫ z, twoM P α E j p' p w₁ w₂ z μ i i' ∂nu2) := by
  funext μ
  ext i i'
  simp only [ggLimit, powM, oneM, twoM, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]

end Mat

/-! ### Covariance of the two-spectral-factor limits -/

theorem ms6_ge' (P : Params) {M₀ : ℝ} (ha : M₀ ≤ P.mγ) (hb : M₀ ≤ P.Λ) :
    ∀ i, M₀ ≤ ms6 P i := fun i => by fin_cases i <;> simp [ms6, ha, hb]

/-- **Covariance of the limits of two spectral factors on `ms6`**, for a covariant numerator
family `Nf` with entries `E`. -/
theorem covRel_ggLim {P : Params} (hA : QED.ChainProof.ChainAdmissible P)
    {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ} (h : IsSpinLift L S T)
    {p' p : Fin 4 → ℝ} (hpq : QED.ChainProof.IsPairQ P.m p' p) (h0 : 0 < (L *ᵥ p') 0)
    (h1 : 0 < (L *ᵥ p) 0)
    (Nf : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (E : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ)
    (hE : ∀ p' p μ i j ℓ, E p' p μ i j ℓ = Nf p' p μ ℓ i j)
    (hQ : ∀ p' p μ i j, QuadN (E p' p μ i j))
    (hP : ∀ p' p μ i j, IsLoopPoly 2 4 fun ℓ => Nf p' p μ (ℓ 0) i j)
    (hC : ∀ μ ℓ, S * Nf (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ ℓ) * T = vecAct L (fun ν => Nf p' p ν ℓ) μ)
    (j : ℕ) (hj : j ≤ 2) (a₁ a₂ : ℂ) {w₁ w₂ : ℝ → ℂ} (hw₁ : Measurable w₁)
    (hw₂ : Measurable w₂) (hW₁ : ∀ x ∈ Ioo (0 : ℝ) 1, ‖w₁ x‖ ≤ 1)
    (hW₂ : ∀ x ∈ Ioo (0 : ℝ) 1, ‖w₂ x‖ ≤ 1) {G G' : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hG : ∀ μ i i', Tendsto (fun ε => energyFirstIntegral
      (ggInt P (E p' p μ i i') (ms6 P) j a₁ a₂ w₁ w₂ ε p' p)) (𝓝[>] 0) (𝓝 (G μ i i')))
    (hG' : ∀ μ i i', Tendsto (fun ε => energyFirstIntegral
      (ggInt P (E (L *ᵥ p') (L *ᵥ p) μ i i') (ms6 P) j a₁ a₂ w₁ w₂ ε (L *ᵥ p') (L *ᵥ p)))
      (𝓝[>] 0) (𝓝 (G' μ i i'))) :
    CovRel L S T G G' := by
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hEf : E = fun p' p μ i j ℓ => Nf p' p μ ℓ i j := by
    funext p' p μ i j ℓ
    exact hE p' p μ i j ℓ
  subst hEf
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  set M₀ := min (min P.mγ P.Λ) P.m
  have hM₀ : 0 < M₀ := lt_min (lt_min hA.hmγ hA.hΛ) hA.hm
  have hM₀m : M₀ ≤ P.m := min_le_right _ _
  have hMs : ∀ i, M₀ ≤ ms6 P i := ms6_ge' P ((min_le_left _ _).trans (min_le_left _ _))
    ((min_le_left _ _).trans (min_le_right _ _))
  have hmf : ∀ f, M₀ ≤ P.mass f := fun f => hM₀m.trans (mass_ge hA.hM₁ hA.hM₂ f)
  choose α hα using fun μ i i' => (hQ p' p μ i i').quad
  choose α₂ hα₂ using fun μ i i' => (hQ (L *ᵥ p') (L *ᵥ p) μ i i').quad
  choose CN hCN using fun μ i i' => (hQ p' p μ i i').bound
  choose CN₂ hCN₂ using fun μ i i' => (hQ (L *ᵥ p') (L *ᵥ p) μ i i').bound
  have hc := fun μ i i' => (hQ p' p μ i i').cont
  have hc₂ := fun μ i i' => (hQ (L *ᵥ p') (L *ᵥ p) μ i i').cont
  -- the limits are the engine limits
  have eG : G = fun μ => Matrix.of fun i i' =>
      ggLimit P (α μ i i') (fun ℓ => Nf p' p μ ℓ i i') (ms6 P) j a₁ a₂ w₁ w₂ p' p := by
    funext μ
    ext i i'
    exact tendsto_nhds_unique (hG μ i i') (tendsto_efi_ggInt hA.hm hA.hM₁ hA.hM₂ hM₀ hM₀m hMs
      hp' hp hp0' hp0 (hc μ i i') (hα μ i i') (hCN μ i i') (by omega) a₁ a₂ hw₁ hw₂ hW₁ hW₂)
  have eG' : G' = fun μ => Matrix.of fun i i' =>
      ggLimit P (α₂ μ i i') (fun ℓ => Nf (L *ᵥ p') (L *ᵥ p) μ ℓ i i') (ms6 P) j a₁ a₂ w₁ w₂
        (L *ᵥ p') (L *ᵥ p) := by
    funext μ
    ext i i'
    exact tendsto_nhds_unique (hG' μ i i') (tendsto_efi_ggInt hA.hm hA.hM₁ hA.hM₂ hM₀ hM₀m hMs
      hpL' hpL h0 h1 (hc₂ μ i i') (hα₂ μ i i') (hCN₂ μ i i') (by omega) a₁ a₂ hw₁ hw₂ hW₁ hW₂)
  -- covariance of the `prodLimit`s, hence of the `specLimit`s
  have H0 := fun k Ms hk hk' hMs' => covRel_prodM (L := L) hA.hm hM₀ h hp' hp hq.le hp0' hp0
    h0 h1 Nf hP hC (fun p' p μ i j => (hQ p' p μ i j).cont)
    (fun p' p μ i j => (hQ p' p μ i j).bound) (α := α) (α₂ := α₂) hα hα₂ k Ms hk hk' hMs'
  have HS := covRel_specM hM₀ H0
  rw [eG, eG', ggLimit_mat_eq, ggLimit_mat_eq]
  have hpow := HS j 0 4 (ms6 P) Fin.elim0 Fin.elim0 (by omega) (by omega) hMs
    (fun i => i.elim0) (fun i => i.elim0)
  have hone : ∀ w : ℝ → ℂ, Measurable w → (∀ x ∈ Ioo (0 : ℝ) 1, ‖w x‖ ≤ 1) →
      CovRel L S T (fun μ => Matrix.of fun i i' => ∫ x in Ioc (0 : ℝ) 1,
          oneM P α (fun μ i j ℓ => Nf p' p μ ℓ i j) j p' p w x μ i i')
        (fun μ => Matrix.of fun i i' => ∫ x in Ioc (0 : ℝ) 1,
          oneM P α₂ (fun μ i j ℓ => Nf (L *ᵥ p') (L *ᵥ p) μ ℓ i j) j (L *ᵥ p') (L *ᵥ p) w x
            μ i i') := by
    intro w hw hW
    refine covRel_integral (fun μ i i' => ?_) (fun μ i i' => ?_) (ae_Ioc_good fun x hx => ?_)
    · exact integrable_oneLim hA.hm hA.hM₁ hA.hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 (hc μ i i')
        (hα μ i i') (hCN μ i i') (by omega) hw hW
    · exact integrable_oneLim hA.hm hA.hM₁ hA.hM₂ hM₀ hM₀m hMs hpL' hpL h0 h1 (hc₂ μ i i')
        (hα₂ μ i i') (hCN₂ μ i i') (by omega) hw hW
    · rw [oneM_eq, oneM_eq]
      exact CovRel.sum _ fun f _ => (HS (j + 1) 1 4 (ms6 P) ![P.mass f] ![x] (by omega)
        (by omega) hMs (fun i => by fin_cases i; simpa using hmf f)
        (fun i => by fin_cases i; simpa using hx)).smul _
  have htwo : CovRel L S T (fun μ => Matrix.of fun i i' => ∫ z,
        twoM P α (fun μ i j ℓ => Nf p' p μ ℓ i j) j p' p w₁ w₂ z μ i i' ∂nu2)
      (fun μ => Matrix.of fun i i' => ∫ z,
        twoM P α₂ (fun μ i j ℓ => Nf (L *ᵥ p') (L *ᵥ p) μ ℓ i j) j (L *ᵥ p') (L *ᵥ p) w₁ w₂ z
          μ i i' ∂nu2) := by
    refine covRel_integral (fun μ i i' => ?_) (fun μ i i' => ?_) ?_
    · exact integrable_twoLim hA.hm hA.hM₁ hA.hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 (hc μ i i')
        (hα μ i i') (hCN μ i i') (by omega) hw₁ hw₂ hW₁ hW₂
    · exact integrable_twoLim hA.hm hA.hM₁ hA.hM₂ hM₀ hM₀m hMs hpL' hpL h0 h1 (hc₂ μ i i')
        (hα₂ μ i i') (hCN₂ μ i i') (by omega) hw₁ hw₂ hW₁ hW₂
    · filter_upwards [ae_nu2_mem] with z ⟨hx, hy⟩
      rw [twoM_eq, twoM_eq]
      exact CovRel.sum _ fun f _ => CovRel.sum _ fun g _ => (HS (j + 2) 2 4 (ms6 P)
        ![P.mass f, P.mass g] ![z.1, z.2] (by omega) (by omega) hMs
        (fun i => by fin_cases i <;> simpa using hmf _)
        (fun i => by fin_cases i <;> simpa)).smul _
  exact (((hpow.smul _).sub ((hone w₂ hw₂ hW₂).smul _)).sub ((hone w₁ hw₁ hW₁).smul _)).add htwo

/-! ### The bubble–bubble limits -/

/-- **The bubble–bubble limits through the limits of the nine pieces.** -/
theorem bbLim_eq {P : Params} (hA : QED.ChainProof.ChainAdmissible P) {p' p : Fin 4 → ℝ}
    (hpq : QED.ChainProof.IsPairQ P.m p' p) {Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : BBLim P p' p Y) :
    ∃ G : Fin 9 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ n μ i j, Tendsto (fun ε => energyFirstIntegral (bbPiece P p' p μ i j ε n)) (𝓝[>] 0)
        (𝓝 (G n μ i j))) ∧
      Y = ((1 / I) * (kap P.e * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 3 : ℝ) : ℂ))) •
        ∑ n, bbCoef P 0 n • G n := by
  choose G hG using fun n μ i j => (bbPiece_ok hA hpq μ i j n).1
  refine ⟨G, hG, ?_⟩
  funext μ
  ext α β
  set c := kap P.e * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 3 : ℝ) : ℂ)
  have hlim : Tendsto (fun ε => (1 / I) * (c * ∑ n, bbCoef P ε n *
      energyFirstIntegral (bbPiece P p' p μ α β ε n))) (𝓝[>] 0)
      (𝓝 ((1 / I) * (c * ∑ n, bbCoef P 0 n * G n μ α β))) :=
    (tendsto_const_nhds.mul (tendsto_finsetSum _ fun n _ =>
      (((continuous_bbCoef P n).tendsto 0).mono_left nhdsWithin_le_nhds).mul
        (hG n μ α β))).const_mul _
  have hY' : Tendsto (fun ε => (1 / I) * (c * ∑ n, bbCoef P ε n *
      energyFirstIntegral (bbPiece P p' p μ α β ε n))) (𝓝[>] 0) (𝓝 (Y μ α β)) := by
    refine (hY μ α β).congr' ?_
    filter_upwards [ev_pos_le_one] with ε ⟨hε, hε1⟩
    have e : (fun ℓ => vertexChain P.e μ (electronPropagator P.m ε (p' + ℓ))
        (electronPropagator P.m ε (p + ℓ)) (bbInsertion P ε ℓ) α β) =
        fun ℓ => c * ∑ n, bbCoef P ε n * bbPiece P p' p μ α β ε n ℓ :=
      funext fun ℓ => bbEntry_eq P hε p' p μ α β ℓ
    rw [e, efi_const_mul, efi_sum _ fun n _ => ((bbPiece_ok hA hpq μ α β n).2 ε hε hε1).const_mul _]
    simp only [efi_const_mul]
  rw [tendsto_nhds_unique hY' hlim]
  simp only [Pi.smul_apply, Finset.sum_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  show _ = 1 / I * c * ∑ n, bbCoef P 0 n * G n μ α β
  ring

theorem numG_eq' (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (ℓ : Fin 4 → ℝ) :
    numG m p' p μ i j ℓ = NG m p' p μ ℓ i j := (NG_apply m p' p μ i j ℓ).symm

/-- **`BBCov`: the bubble–bubble limits are covariant.** -/
theorem bbCov : BBCov := by
  intro P hA L S T h p' p hpq h0 h1 Y Z hY hZ μ
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hpqL : QED.ChainProof.IsPairQ P.m (L *ᵥ p') (L *ᵥ p) := by
    refine ⟨by rw [h.dot_mulVec]; exact hp', by rw [h.dot_mulVec]; exact hp, h0, h1, ?_⟩
    rw [← Matrix.mulVec_sub, h.dot_mulVec]
    exact hq
  have hpq : QED.ChainProof.IsPairQ P.m p' p := ⟨hp', hp, hp0', hp0, hq⟩
  obtain ⟨G, hG, rfl⟩ := bbLim_eq hA hpq hY
  obtain ⟨G', hG', rfl⟩ := bbLim_eq hA hpqL hZ
  have o := fun x (hx : x ∈ Ioo (0 : ℝ) 1) => norm_wOne_le hx
  have d := fun x (hx : x ∈ Ioo (0 : ℝ) 1) => norm_wId_le hx
  have cG := covRel_ggLim hA h hpq h0 h1 (fun p' p μ ℓ => NG P.m p' p μ ℓ)
    (fun p' p μ i j => numG P.m p' p μ i j) (fun p' p μ i j ℓ => numG_eq' P.m p' p μ i j ℓ)
    (fun _ _ _ _ _ => quadN_numG _ _ _ _ _ _) (isLoopPoly_NG P.m)
    (fun μ ℓ => NG_cov h P.m p' p μ ℓ)
  have cS := covRel_ggLim hA h hpq h0 h1 (fun _ _ μ ℓ => NS μ ℓ)
    (fun _ _ μ i j => numS μ i j) (fun _ _ μ i j ℓ => (NS_apply μ i j ℓ).symm)
    (fun _ _ _ _ _ => quadN_numS _ _ _) (fun _ _ => isLoopPoly_NS)
    (fun μ ℓ => NS_cov h μ ℓ)
  have cL := covRel_ggLim hA h hpq h0 h1 (fun p' p μ ℓ => NL P.m p' p μ ℓ)
    (fun p' p μ i j => numL P.m p' p μ i j) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => quadN_numL _ _ _ _ _ _) (isLoopPoly_NL P.m)
    (fun μ ℓ => NL_cov h P.m p' p μ ℓ)
  have cQ := covRel_ggLim hA h hpq h0 h1 (fun p' p μ ℓ => NQ P.m p' p μ ℓ)
    (fun p' p μ i j => numQ P.m p' p μ i j) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => quadN_numQ _ _ _ _ _ _) (isLoopPoly_NQ P.m)
    (fun μ ℓ => NQ_cov h P.m p' p μ ℓ)
  have hn : ∀ n, CovRel L S T (G n) (G' n) := by
    intro n
    fin_cases n
    · exact cG 2 (by norm_num) (1 / 6) (1 / 6) measurable_wOne measurable_wOne o o
        (hG 0) (hG' 0)
    · exact cG 1 (by norm_num) (1 / 6) 1 measurable_wOne measurable_wId o d
        (hG 1) (hG' 1)
    · exact cG 0 (by norm_num) 1 1 measurable_wId measurable_wId d d (hG 2) (hG' 2)
    · exact cS 2 (by norm_num) (1 / 6) (1 / 6) measurable_wOne measurable_wOne o o
        (hG 3) (hG' 3)
    · exact cS 1 (by norm_num) (1 / 6) 1 measurable_wOne measurable_wId o d
        (hG 4) (hG' 4)
    · exact cL 2 (by norm_num) (1 / 6) (1 / 6) measurable_wOne measurable_wOne o o
        (hG 5) (hG' 5)
    · exact cL 1 (by norm_num) (1 / 6) 1 measurable_wOne measurable_wId o d
        (hG 6) (hG' 6)
    · exact cQ 1 (by norm_num) (1 / 6) (1 / 6) measurable_wOne measurable_wOne o o
        (hG 7) (hG' 7)
    · exact cQ 0 (by norm_num) (1 / 6) 1 measurable_wOne measurable_wId o d
        (hG 8) (hG' 8)
  exact ((CovRel.sum Finset.univ fun n _ => (hn n).smul (bbCoef P 0 n)).smul _) μ

end QED.ChainProof.HCBB2

end
