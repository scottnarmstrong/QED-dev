/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtGenAssembly

/-!
# Two spectral factors on any list of photon-type denominators

Helper level, Phase 5 Stage 1a, toward the `ε → 0⁺` limit of the bubble–bubble class
(`QED.ChainProof.HCBB.BBInsertionLimit`). After the integration by parts in its Feynman
parameter, each closed-form bubble coefficient is a *spectral function*
`G(ε, s) = a L_ε - ∫₀¹ vpRatSum(ε, s, x) w(x) dx` (`gSpec`): `Π̂_ε = c₁ G_{1/6, wOne}` and
`S_ε = c₂ G_{1, x}` (`vpLoopEps_eq_gSpec`, `vpExtraEps_eq_gSpec`). This file treats the product
of **two** spectral functions on top of `(k²)ʲ` and any list of photon-type denominators with
prescription `ε`, for any numerator `N` quadratic in the loop energy with constant leading
coefficient and of quadratic growth (not only the Pauli-projected chain): the generalization of
`QED/TwoLoop/VPHalfAtGenAssembly.lean` from one to two inserted vacuum polarizations.

* `ggInt`: `(k²)ʲ N / (D D ∏ D_{M_i}) · G₁(ε, k²) G₂(ε, k²)`.
* `ggInt_eq`: at `ε > 0`, `ggInt = a₁ a₂ L_ε² pw - a₁ L_ε ∫₀¹ oneInt w₂ - a₂ L_ε ∫₀¹ oneInt w₁ +
  ∫_{(0,1]²} twoInt w₁ w₂`, with one (`oneInt`) and two (`twoInt`) spectral insertions
  (`QED.TwoLoop.VPHalfAtGen.specInt`, `r = 1, 2`).
* `exists_good_pw`, `exists_good_oneInt`, `exists_good_twoInt`: bounds uniform in
  `ε ∈ (0, 1]` and in the Feynman parameters, for `j + 2 ≤ k` (at least `j + 4` photon-type
  denominators).
* **`tendsto_efi_ggInt`**: the energy-first integral of `ggInt` tends, as `ε → 0⁺`, to
  `ggLimit = a₁ a₂ L₀² powLimit j - a₁ L₀ ∫₀¹ oneLim w₂ - a₂ L₀ ∫₀¹ oneLim w₁ +
  ∫_{(0,1]²} twoLim w₁ w₂`, by the engine at fixed Feynman parameters and dominated convergence
  in the Feynman parameters (`QED.TwoLoop.VPHalfAtGen.tendsto_integral_efi_of_good`).
* `efInt_ggInt`: integrability in both stages at fixed `ε ∈ (0, 1]`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.HCBB2

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.WickModel
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtAssembly
open QED.TwoLoop.VPHalfAt QED.TwoLoop.VPHalfAtGen

/-! ### Spectral functions -/

/-- **A spectral function**: `G(ε, s) = a L_ε - ∫₀¹ vpRatSum(ε, s, x) w(x) dx`. -/
noncomputable def gSpec (P : Params) (a : ℂ) (w : ℝ → ℂ) (ε s : ℝ) : ℂ :=
  a * logSum P ε - ∫ x in (0 : ℝ)..1, vpRatSum P ε s x * w x

/-- The weight `x` of `S_ε`. -/
noncomputable def wId (x : ℝ) : ℂ := (x : ℂ)

/-- `Π̂_ε = c₁ G_{1/6, wOne}`. -/
theorem vpLoopEps_eq_gSpec (P : Params) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    vpLoopEps P ε s = cOne P * gSpec P (1 / 6) wOne ε s := by
  rw [vpLoopEps_eq_spectral P hε]
  simp only [cOne, gSpec, logSum, wOne]

/-- `S_ε = c₂ G_{1, x}`. -/
theorem vpExtraEps_eq_gSpec (P : Params) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    vpExtraEps P ε s = cTwo P * gSpec P 1 wId ε s := by
  rw [vpExtraEps_eq_spectral P hε]
  simp only [cTwo, gSpec, logSum, wId, one_mul]

/-! ### The pieces -/

/-- The measure `dx dy` on `(0, 1]²`. -/
noncomputable def nu2 : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))

instance : IsFiniteMeasure nu2 := by unfold nu2; infer_instance

/-- The one-insertion integrand at the Feynman parameter `x`. -/
noncomputable def oneInt (P : Params) (N : (Fin 4 → ℝ) → ℂ) {k : ℕ} (Ms : Fin (k + 2) → ℝ)
    (j : ℕ) (w : ℝ → ℂ) (ε : ℝ) (p' p : Fin 4 → ℝ) (x : ℝ) (ℓ : Fin 4 → ℝ) : ℂ :=
  ∑ f, (P.loopCoeff f : ℂ) * (((1 - 2 * x : ℝ) : ℂ) * w x) *
    specInt N P.m (j + 1) Ms (fun _ => ε) ![P.mass f] ![x] ε p' p ℓ

/-- The two-insertion integrand at the Feynman parameters `z = (x, y)`. -/
noncomputable def twoInt (P : Params) (N : (Fin 4 → ℝ) → ℂ) {k : ℕ} (Ms : Fin (k + 2) → ℝ)
    (j : ℕ) (w₁ w₂ : ℝ → ℂ) (ε : ℝ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) (ℓ : Fin 4 → ℝ) : ℂ :=
  ∑ f, ∑ g, (P.loopCoeff f : ℂ) * (P.loopCoeff g : ℂ) *
    ((((1 - 2 * z.1 : ℝ) : ℂ) * w₁ z.1) * (((1 - 2 * z.2 : ℝ) : ℂ) * w₂ z.2)) *
    specInt N P.m (j + 2) Ms (fun _ => ε) ![P.mass f, P.mass g] ![z.1, z.2] ε p' p ℓ

/-- **Two spectral factors**: `(k²)ʲ N / (D D ∏ D_{M_i}) · G₁(ε, k²) G₂(ε, k²)`. -/
noncomputable def ggInt (P : Params) (N : (Fin 4 → ℝ) → ℂ) {k : ℕ} (Ms : Fin (k + 2) → ℝ)
    (j : ℕ) (a₁ a₂ : ℂ) (w₁ w₂ : ℝ → ℂ) (ε : ℝ) (p' p ℓ : Fin 4 → ℝ) : ℂ :=
  powInt N P.m j Ms (fun _ => ε) ε p' p ℓ * gSpec P a₁ w₁ ε (Minkowski.dot ℓ ℓ) *
    gSpec P a₂ w₂ ε (Minkowski.dot ℓ ℓ)

/-- The pointwise limit of `oneInt`. -/
noncomputable def oneLim (P : Params) (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (j : ℕ) (w : ℝ → ℂ) (p' p : Fin 4 → ℝ) (x : ℝ) : ℂ :=
  ∑ f, (P.loopCoeff f : ℂ) * (((1 - 2 * x : ℝ) : ℂ) * w x) *
    specLimit α N P.m p' p (j + 1) 1 Ms ![P.mass f] ![x]

/-- The pointwise limit of `twoInt`. -/
noncomputable def twoLim (P : Params) (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (j : ℕ) (w₁ w₂ : ℝ → ℂ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) : ℂ :=
  ∑ f, ∑ g, (P.loopCoeff f : ℂ) * (P.loopCoeff g : ℂ) *
    ((((1 - 2 * z.1 : ℝ) : ℂ) * w₁ z.1) * (((1 - 2 * z.2 : ℝ) : ℂ) * w₂ z.2)) *
    specLimit α N P.m p' p (j + 2) 2 Ms ![P.mass f, P.mass g] ![z.1, z.2]

/-- **The limit of the energy-first integral of `ggInt`.** -/
noncomputable def ggLimit (P : Params) (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (j : ℕ) (a₁ a₂ : ℂ) (w₁ w₂ : ℝ → ℂ) (p' p : Fin 4 → ℝ) : ℂ :=
  a₁ * a₂ * logSum P 0 ^ 2 * powLimit α N P.m p' p j Ms -
    a₁ * logSum P 0 * (∫ x in Ioc (0 : ℝ) 1, oneLim P α N Ms j w₂ p' p x) -
    a₂ * logSum P 0 * (∫ x in Ioc (0 : ℝ) 1, oneLim P α N Ms j w₁ p' p x) +
    ∫ z, twoLim P α N Ms j w₁ w₂ p' p z ∂nu2

/-! ### The decomposition at fixed `ε` -/

theorem vpRatSum_mul_powInt (P : Params) (N : (Fin 4 → ℝ) → ℂ) {k : ℕ} (Ms : Fin (k + 2) → ℝ)
    (j : ℕ) (w : ℝ → ℂ) (ε : ℝ) (p' p : Fin 4 → ℝ) (x : ℝ) (ℓ : Fin 4 → ℝ) :
    vpRatSum P ε (Minkowski.dot ℓ ℓ) x * w x * powInt N P.m j Ms (fun _ => ε) ε p' p ℓ =
      oneInt P N Ms j w ε p' p x ℓ := by
  simp only [oneInt, vpRatSum, specInt, powInt, Fin.prod_univ_one, Matrix.cons_val_zero, fDen,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun f _ => ?_
  push_cast
  ring

theorem vpRatSum_mul_vpRatSum_mul_powInt (P : Params) (N : (Fin 4 → ℝ) → ℂ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (j : ℕ) (w₁ w₂ : ℝ → ℂ) (ε : ℝ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ)
    (ℓ : Fin 4 → ℝ) :
    vpRatSum P ε (Minkowski.dot ℓ ℓ) z.1 * w₁ z.1 * (vpRatSum P ε (Minkowski.dot ℓ ℓ) z.2 * w₂ z.2) *
        powInt N P.m j Ms (fun _ => ε) ε p' p ℓ =
      twoInt P N Ms j w₁ w₂ ε p' p z ℓ := by
  unfold twoInt
  have h1 : ∀ (x : ℝ) (w : ℝ → ℂ), vpRatSum P ε (Minkowski.dot ℓ ℓ) x * w x =
      ∑ f, (P.loopCoeff f : ℂ) * (((1 - 2 * x) * Minkowski.dot ℓ ℓ : ℝ) : ℂ) /
        ((vacuumPolarizationFeynmanMass (P.mass f) (Minkowski.dot ℓ ℓ) x : ℂ) - ε * I) * w x :=
    fun x w => by rw [vpRatSum, Finset.sum_mul]
  rw [h1, h1, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [specInt, powInt, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    fDen]
  push_cast
  ring

/-- **The decomposition of `ggInt` at fixed `ε > 0`.** -/
theorem ggInt_eq (P : Params) (N : (Fin 4 → ℝ) → ℂ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (j : ℕ)
    (a₁ a₂ : ℂ) (w₁ w₂ : ℝ → ℂ) (ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    ggInt P N Ms j a₁ a₂ w₁ w₂ ε p' p ℓ =
      a₁ * a₂ * logSum P ε ^ 2 * powInt N P.m j Ms (fun _ => ε) ε p' p ℓ -
        a₁ * logSum P ε * (∫ x in Ioc (0 : ℝ) 1, oneInt P N Ms j w₂ ε p' p x ℓ) -
        a₂ * logSum P ε * (∫ x in Ioc (0 : ℝ) 1, oneInt P N Ms j w₁ ε p' p x ℓ) +
        ∫ z, twoInt P N Ms j w₁ w₂ ε p' p z ℓ ∂nu2 := by
  set s := Minkowski.dot ℓ ℓ
  set Q := powInt N P.m j Ms (fun _ => ε) ε p' p ℓ
  set A₁ := ∫ x in Ioc (0 : ℝ) 1, vpRatSum P ε s x * w₁ x
  set A₂ := ∫ x in Ioc (0 : ℝ) 1, vpRatSum P ε s x * w₂ x
  have h1 : ∀ w : ℝ → ℂ, (∫ x in Ioc (0 : ℝ) 1, oneInt P N Ms j w ε p' p x ℓ) =
      (∫ x in Ioc (0 : ℝ) 1, vpRatSum P ε s x * w x) * Q := by
    intro w
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun x =>
      (vpRatSum_mul_powInt P N Ms j w ε p' p x ℓ).symm)
  have h2 : (∫ z, twoInt P N Ms j w₁ w₂ ε p' p z ℓ ∂nu2) = A₁ * A₂ * Q := by
    rw [show A₁ * A₂ = ∫ z, (vpRatSum P ε s z.1 * w₁ z.1) * (vpRatSum P ε s z.2 * w₂ z.2) ∂nu2
      from (integral_prod_mul (μ := volume.restrict (Ioc (0 : ℝ) 1))
        (ν := volume.restrict (Ioc (0 : ℝ) 1)) (fun x => vpRatSum P ε s x * w₁ x)
        (fun x => vpRatSum P ε s x * w₂ x)).symm, ← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun z =>
      (vpRatSum_mul_vpRatSum_mul_powInt P N Ms j w₁ w₂ ε p' p z ℓ).symm)
  rw [h1, h1, h2]
  simp only [ggInt, gSpec, intervalIntegral.integral_of_le zero_le_one]
  ring

/-! ### Uniform bounds -/

theorem efInt_sub' {F G : (Fin 4 → ℝ) → ℂ} (hF : EFInt F) (hG : EFInt G) :
    EFInt fun ℓ => F ℓ - G ℓ := by
  have h := hF.add (hG.const_mul (-1))
  have e : (fun ℓ => F ℓ + -1 * G ℓ) = fun ℓ => F ℓ - G ℓ := funext fun ℓ => by ring
  rwa [e] at h

theorem good_zero : Good (fun _ => (0 : ℂ)) 0 (fun _ => 0) := by
  refine ⟨⟨⟨fun v => integrable_zero _ _ _, ?_⟩, fun v => by simp⟩, fun v t => by simp⟩
  simp only [integral_zero]
  exact integrable_zero _ _ _

/-- `Good` is stable under finite sums. -/
theorem good_sum {ι : Type*} (s : Finset ι) {F : ι → (Fin 4 → ℝ) → ℂ} {C : ι → ℝ}
    {G : ι → (Fin 3 → ℝ) → ℝ} (h : ∀ i ∈ s, Good (F i) (C i) (G i)) :
    Good (fun ℓ => ∑ i ∈ s, F i ℓ) (∑ i ∈ s, C i) (fun v => ∑ i ∈ s, G i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have h3 := h1.add h2
    rw [Finset.sum_insert ha]
    refine (h3.congr fun ℓ => by rw [Finset.sum_insert ha]).mono le_rfl fun v => ?_
    rw [Finset.sum_insert ha]

theorem norm_coef_le {x W : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) {w : ℝ → ℂ} (hW : ‖w x‖ ≤ W) :
    ‖((1 - 2 * x : ℝ) : ℂ) * w x‖ ≤ W := by
  have h1 : |1 - 2 * x| ≤ 1 := abs_le.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |1 - 2 * x| * ‖w x‖ ≤ 1 * W := mul_le_mul h1 hW (norm_nonneg _) zero_le_one
    _ = W := one_mul W

section Bounds

variable {P : Params} {N : (Fin 4 → ℝ) → ℂ} {k : ℕ} {Ms : Fin (k + 2) → ℝ} {j : ℕ}
  {p' p : Fin 4 → ℝ} {α : ℂ} {CN M₀ : ℝ}

/-- The `(k²)ʲ` piece is `Good` uniformly in `ε ∈ (0, 1]`. -/
theorem exists_good_pw (hm : 0 < P.m) (hM₀ : 0 < M₀) (hMs : ∀ i, M₀ ≤ Ms i)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (hjk : j ≤ k) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ G : (Fin 3 → ℝ) → ℝ,
      Good (powInt N P.m j Ms (fun _ => ε) ε p' p) C G := by
  obtain ⟨K, -, g⟩ := exists_good_powInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb j k hjk
  refine ⟨(1 + (∑ i, Ms i ^ 2 + 1)) ^ j * K, fun ε hε hε1 => ?_⟩
  obtain ⟨G, -, h⟩ := g ε ε hε hε
  exact ⟨_, h _ (by positivity) Ms (fun _ => ε) hMs (fun _ => le_rfl)
    (fun i _ => norm_massShift_le_T Ms hε.le hε1 i)⟩

/-- The one-insertion pieces are `Good` uniformly in `ε ∈ (0, 1]` and `x ∈ (0, 1)`. -/
theorem exists_good_oneInt (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hM₀ : 0 < M₀) (hM₀m : M₀ ≤ P.m) (hMs : ∀ i, M₀ ≤ Ms i)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (hjk : j + 1 ≤ k) {w : ℝ → ℂ} {W : ℝ}
    (hW : ∀ x ∈ Ioo (0 : ℝ) 1, ‖w x‖ ≤ W) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ G : (Fin 3 → ℝ) → ℝ,
      ∀ x ∈ Ioo (0 : ℝ) 1, Good (oneInt P N Ms j w ε p' p x) C G := by
  obtain ⟨K, -, g⟩ := exists_good_specInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hM₀m 1 (j + 1) k
    hjk (by omega)
  set T : ℝ := ∑ i, Ms i ^ 2 + 1
  have hT : 0 ≤ T := by positivity
  refine ⟨∑ f : Fin 3, ‖(P.loopCoeff f : ℂ)‖ * W * ((1 + T) ^ (j + 1 + 1) * K),
    fun ε hε hε1 => ?_⟩
  obtain ⟨G, -, h⟩ := g ε ε hε hε le_rfl
  refine ⟨fun v => ∑ f : Fin 3, ‖(P.loopCoeff f : ℂ)‖ * W * ((1 + T) ^ (j + 1 + 1) * G v),
    fun x hx => ?_⟩
  refine good_sum Finset.univ fun f _ => ?_
  have hf : P.m ≤ P.mass f := mass_ge hM₁ hM₂ f
  have hs := h T hT Ms (fun _ => ε) hMs (fun _ => le_rfl)
    (fun i _ => norm_massShift_le_T Ms hε.le hε1 i) ![P.mass f] ![x]
    (fun i => by fin_cases i; simpa using hf) (fun i => by fin_cases i; simpa using hx)
  have hc : ‖(P.loopCoeff f : ℂ) * (((1 - 2 * x : ℝ) : ℂ) * w x)‖ ≤
      ‖(P.loopCoeff f : ℂ)‖ * W := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_coef_le hx (hW x hx)) (norm_nonneg _)
  exact hs.mul_le hc

/-- The two-insertion pieces are `Good` uniformly in `ε ∈ (0, 1]` and `x, y ∈ (0, 1)`. -/
theorem exists_good_twoInt (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hM₀ : 0 < M₀) (hM₀m : M₀ ≤ P.m) (hMs : ∀ i, M₀ ≤ Ms i)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (hjk : j + 2 ≤ k) {w₁ w₂ : ℝ → ℂ} {W₁ W₂ : ℝ}
    (hW₁ : ∀ x ∈ Ioo (0 : ℝ) 1, ‖w₁ x‖ ≤ W₁) (hW₂ : ∀ x ∈ Ioo (0 : ℝ) 1, ‖w₂ x‖ ≤ W₂) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ G : (Fin 3 → ℝ) → ℝ,
      ∀ z : ℝ × ℝ, z.1 ∈ Ioo (0 : ℝ) 1 → z.2 ∈ Ioo (0 : ℝ) 1 →
        Good (twoInt P N Ms j w₁ w₂ ε p' p z) C G := by
  obtain ⟨K, -, g⟩ := exists_good_specInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hM₀m 2 (j + 2) k
    hjk (by omega)
  set T : ℝ := ∑ i, Ms i ^ 2 + 1
  have hT : 0 ≤ T := by positivity
  set B : Fin 3 → Fin 3 → ℝ := fun f g =>
    ‖(P.loopCoeff f : ℂ)‖ * ‖(P.loopCoeff g : ℂ)‖ * (W₁ * W₂)
  refine ⟨∑ f : Fin 3, ∑ g : Fin 3, B f g * ((1 + T) ^ (j + 2 + 2) * K), fun ε hε hε1 => ?_⟩
  obtain ⟨G, -, h⟩ := g ε ε hε hε le_rfl
  refine ⟨fun v => ∑ f : Fin 3, ∑ g : Fin 3, B f g * ((1 + T) ^ (j + 2 + 2) * G v),
    fun z hx hy => ?_⟩
  refine good_sum Finset.univ fun f _ => good_sum Finset.univ fun g _ => ?_
  have hf : P.m ≤ P.mass f := mass_ge hM₁ hM₂ f
  have hg : P.m ≤ P.mass g := mass_ge hM₁ hM₂ g
  have hs := h T hT Ms (fun _ => ε) hMs (fun _ => le_rfl)
    (fun i _ => norm_massShift_le_T Ms hε.le hε1 i) ![P.mass f, P.mass g] ![z.1, z.2]
    (fun i => by fin_cases i <;> simpa) (fun i => by fin_cases i <;> simpa)
  have hW₁0 : 0 ≤ W₁ := (norm_nonneg _).trans (hW₁ _ hx)
  have hc : ‖(P.loopCoeff f : ℂ) * (P.loopCoeff g : ℂ) *
      ((((1 - 2 * z.1 : ℝ) : ℂ) * w₁ z.1) * (((1 - 2 * z.2 : ℝ) : ℂ) * w₂ z.2))‖ ≤ B f g := by
    simp only [B]
    rw [norm_mul, norm_mul (((1 - 2 * z.1 : ℝ) : ℂ) * w₁ z.1), norm_mul (P.loopCoeff f : ℂ)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (norm_coef_le hx (hW₁ _ hx))
      (norm_coef_le hy (hW₂ _ hy)) (norm_nonneg _) hW₁0) (by positivity)
  exact hs.mul_le hc

end Bounds

/-! ### Measurability -/

theorem measurable_comp_cons {X : Type*} [MeasurableSpace X] {g : X → (Fin 4 → ℝ) → ℂ}
    (hg : Measurable fun q : X × (Fin 4 → ℝ) => g q.1 q.2) :
    Measurable fun q : ((Fin 3 → ℝ) × X) × ℝ => g q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := by
  have hc : Continuous fun r : (Fin 3 → ℝ) × ℝ => (Fin.cons r.2 r.1 : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_snd continuous_fst
  have hℓ : Measurable fun q : ((Fin 3 → ℝ) × X) × ℝ => (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) :=
    hc.measurable.comp (measurable_fst.fst.prodMk measurable_snd)
  exact hg.comp (measurable_fst.snd.prodMk hℓ)

/-- Joint measurability of `specInt` in a measurable family of Feynman parameters. -/
theorem measurable_specInt_param {X : Type*} [MeasurableSpace X] {N : (Fin 4 → ℝ) → ℂ}
    (hNc : Continuous N) (m : ℝ) (j : ℕ) {k : ℕ} (Ms es : Fin (k + 2) → ℝ) {r : ℕ}
    (Msp : Fin r → ℝ) {xs : X → Fin r → ℝ} (hxs : ∀ i, Measurable fun x => xs x i) (ε : ℝ)
    (p' p : Fin 4 → ℝ) :
    Measurable fun q : X × (Fin 4 → ℝ) => specInt N m j Ms es Msp (xs q.1) ε p' p q.2 := by
  have hs : Measurable fun q : X × (Fin 4 → ℝ) => Minkowski.dot q.2 q.2 :=
    (VertexLimit.continuous_dot_comp continuous_id continuous_id).measurable.comp measurable_snd
  have hc : ∀ {r : X × (Fin 4 → ℝ) → ℝ}, Measurable r → Measurable fun q => ((r q : ℝ) : ℂ) :=
    fun hr => Complex.measurable_ofReal.comp hr
  have hD : ∀ (M e : ℝ) (c : Fin 4 → ℝ), Measurable fun q : X × (Fin 4 → ℝ) =>
      denom M e (c + q.2) := fun M e c =>
    ((continuous_denom_joint continuous_const continuous_const
      (continuous_const.add continuous_id)).measurable.comp measurable_snd :)
  have hD0 : ∀ (M e : ℝ), Measurable fun q : X × (Fin 4 → ℝ) => denom M e q.2 := fun M e =>
    ((continuous_denom_joint continuous_const continuous_const continuous_id).measurable.comp
      measurable_snd :)
  unfold specInt powInt prodIntegrand
  refine (((hc hs).pow_const j).mul ((hNc.measurable.comp measurable_snd).mul
    (((hD m ε p').mul (hD m ε p)).inv.mul
      (Finset.measurable_prod _ fun i _ => (hD0 _ _).inv)))).mul
    (Finset.measurable_prod _ fun i _ => ?_)
  unfold fDen vacuumPolarizationFeynmanMass
  have hx : Measurable fun q : X × (Fin 4 → ℝ) => xs q.1 i := (hxs i).comp measurable_fst
  exact ((hc (measurable_const.add ((hx.mul (measurable_const.sub hx)).mul hs))).sub
    measurable_const).inv

theorem measurable_oneInt (P : Params) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (j : ℕ) {w : ℝ → ℂ} (hw : Measurable w) (ε : ℝ) (p' p : Fin 4 → ℝ) :
    Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      oneInt P N Ms j w ε p' p q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := by
  refine measurable_comp_cons (g := oneInt P N Ms j w ε p' p) ?_
  unfold oneInt
  refine Finset.measurable_sum _ fun f _ => ?_
  have hx : Measurable fun q : ℝ × (Fin 4 → ℝ) => q.1 := measurable_fst
  refine (measurable_const.mul ((Complex.measurable_ofReal.comp
    (measurable_const.sub (hx.const_mul 2))).mul (hw.comp hx))).mul ?_
  exact measurable_specInt_param hNc P.m (j + 1) Ms _ _ (xs := fun x => ![x])
    (fun i => by fin_cases i; simpa using measurable_id') ε p' p

theorem measurable_twoInt (P : Params) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (j : ℕ) {w₁ w₂ : ℝ → ℂ} (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    (ε : ℝ) (p' p : Fin 4 → ℝ) :
    Measurable fun q : ((Fin 3 → ℝ) × (ℝ × ℝ)) × ℝ =>
      twoInt P N Ms j w₁ w₂ ε p' p q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := by
  refine measurable_comp_cons (g := twoInt P N Ms j w₁ w₂ ε p' p) ?_
  unfold twoInt
  refine Finset.measurable_sum _ fun f _ => Finset.measurable_sum _ fun g _ => ?_
  have hx : Measurable fun q : (ℝ × ℝ) × (Fin 4 → ℝ) => q.1.1 := measurable_fst.fst
  have hy : Measurable fun q : (ℝ × ℝ) × (Fin 4 → ℝ) => q.1.2 := measurable_fst.snd
  refine (measurable_const.mul (((Complex.measurable_ofReal.comp
    (measurable_const.sub (hx.const_mul 2))).mul (hw₁.comp hx)).mul
    ((Complex.measurable_ofReal.comp (measurable_const.sub (hy.const_mul 2))).mul
      (hw₂.comp hy)))).mul ?_
  exact measurable_specInt_param hNc P.m (j + 2) Ms _ _ (xs := fun z : ℝ × ℝ => ![z.1, z.2])
    (fun i => by fin_cases i <;> simp [measurable_fst, measurable_snd]) ε p' p

/-! ### The limit -/

theorem ae_nu2_mem : ∀ᵐ z ∂nu2, z.1 ∈ Ioo (0 : ℝ) 1 ∧ z.2 ∈ Ioo (0 : ℝ) 1 := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).ae ae_Ioc_mem_Ioo
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).ae ae_Ioc_mem_Ioo
  unfold nu2
  filter_upwards [h1, h2] with z a b using ⟨a, b⟩

section Limit

variable {P : Params} {N : (Fin 4 → ℝ) → ℂ} {k : ℕ} {Ms : Fin (k + 2) → ℝ} {j : ℕ}
  {p' p : Fin 4 → ℝ} {α : ℂ} {CN M₀ : ℝ}

/-- The pointwise limit of the one-insertion pieces. -/
theorem tendsto_efi_oneInt (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hM₀ : 0 < M₀) (hM₀m : M₀ ≤ P.m) (hMs : ∀ i, M₀ ≤ Ms i)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (hjk : j + 1 ≤ k) (w : ℝ → ℂ) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun ε => energyFirstIntegral (oneInt P N Ms j w ε p' p x)) (𝓝[>] 0)
      (𝓝 (oneLim P α N Ms j w p' p x)) := by
  obtain ⟨K, -, g⟩ := exists_good_specInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hM₀m 1 (j + 1) k
    hjk (by omega)
  have hsp : ∀ f, ∀ i : Fin 1, P.m ≤ (![P.mass f] : Fin 1 → ℝ) i := fun f i => by
    fin_cases i; simpa using mass_ge hM₁ hM₂ f
  have hxs : ∀ i : Fin 1, (![x] : Fin 1 → ℝ) i ∈ Ioo (0 : ℝ) 1 := fun i => by
    fin_cases i; simpa using hx
  have hq : ∀ f, Tendsto (fun ε => energyFirstIntegral
      (specInt N P.m (j + 1) Ms (fun _ => ε) ![P.mass f] ![x] ε p' p)) (𝓝[>] 0)
      (𝓝 (specLimit α N P.m p' p (j + 1) 1 Ms ![P.mass f] ![x])) := fun f =>
    tendsto_efi_specInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb tendsto_id (j + 1) 1 k (by omega) Ms
      (fun ε _ => ε) ![P.mass f] ![x] hMs (fun i => hM₀m.trans (hsp f i)) hxs
      (fun _ => tendsto_id)
  have hlim := tendsto_finsetSum (s := Finset.univ) fun f (_ : f ∈ Finset.univ) =>
    (hq f).const_mul ((P.loopCoeff f : ℂ) * (((1 - 2 * x : ℝ) : ℂ) * w x))
  refine hlim.congr' ?_
  filter_upwards [ev_pos_le_one] with ε ⟨hε, hε1⟩
  obtain ⟨G, -, h⟩ := g ε ε hε hε le_rfl
  have hi : ∀ f, EFInt (specInt N P.m (j + 1) Ms (fun _ => ε) ![P.mass f] ![x] ε p' p) :=
    fun f => (h _ (by positivity) Ms (fun _ => ε) hMs (fun _ => le_rfl)
      (fun i _ => norm_massShift_le_T Ms hε.le hε1 i) _ _ (hsp f) hxs).1.1
  unfold oneInt
  rw [efi_sum _ fun f _ => (hi f).const_mul _]
  exact Finset.sum_congr rfl fun f _ => (efi_const_mul _ _).symm

/-- The pointwise limit of the two-insertion pieces. -/
theorem tendsto_efi_twoInt (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hM₀ : 0 < M₀) (hM₀m : M₀ ≤ P.m) (hMs : ∀ i, M₀ ≤ Ms i)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (hjk : j + 2 ≤ k) (w₁ w₂ : ℝ → ℂ) {z : ℝ × ℝ}
    (hx : z.1 ∈ Ioo (0 : ℝ) 1) (hy : z.2 ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun ε => energyFirstIntegral (twoInt P N Ms j w₁ w₂ ε p' p z)) (𝓝[>] 0)
      (𝓝 (twoLim P α N Ms j w₁ w₂ p' p z)) := by
  obtain ⟨K, -, g⟩ := exists_good_specInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hM₀m 2 (j + 2) k
    hjk (by omega)
  have hsp : ∀ f g, ∀ i : Fin 2, P.m ≤ (![P.mass f, P.mass g] : Fin 2 → ℝ) i := fun f g i => by
    fin_cases i
    · simpa using mass_ge hM₁ hM₂ f
    · simpa using mass_ge hM₁ hM₂ g
  have hxs : ∀ i : Fin 2, (![z.1, z.2] : Fin 2 → ℝ) i ∈ Ioo (0 : ℝ) 1 := fun i => by
    fin_cases i <;> simpa
  have hq : ∀ f g, Tendsto (fun ε => energyFirstIntegral
      (specInt N P.m (j + 2) Ms (fun _ => ε) ![P.mass f, P.mass g] ![z.1, z.2] ε p' p))
      (𝓝[>] 0) (𝓝 (specLimit α N P.m p' p (j + 2) 2 Ms ![P.mass f, P.mass g] ![z.1, z.2])) :=
    fun f g => tendsto_efi_specInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb tendsto_id (j + 2) 2 k
      (by omega) Ms (fun ε _ => ε) ![P.mass f, P.mass g] ![z.1, z.2] hMs
      (fun i => hM₀m.trans (hsp f g i)) hxs (fun _ => tendsto_id)
  have hlim := tendsto_finsetSum (s := Finset.univ) fun f (_ : f ∈ Finset.univ) =>
    tendsto_finsetSum (s := Finset.univ) fun g (_ : g ∈ Finset.univ) =>
      (hq f g).const_mul ((P.loopCoeff f : ℂ) * (P.loopCoeff g : ℂ) *
        ((((1 - 2 * z.1 : ℝ) : ℂ) * w₁ z.1) * (((1 - 2 * z.2 : ℝ) : ℂ) * w₂ z.2)))
  refine hlim.congr' ?_
  filter_upwards [ev_pos_le_one] with ε ⟨hε, hε1⟩
  obtain ⟨G, -, h⟩ := g ε ε hε hε le_rfl
  have hi : ∀ f g, EFInt
      (specInt N P.m (j + 2) Ms (fun _ => ε) ![P.mass f, P.mass g] ![z.1, z.2] ε p' p) :=
    fun f g => (h _ (by positivity) Ms (fun _ => ε) hMs (fun _ => le_rfl)
      (fun i _ => norm_massShift_le_T Ms hε.le hε1 i) _ _ (hsp f g) hxs).1.1
  unfold twoInt
  rw [efi_sum _ fun f _ => EFInt.sum _ fun g _ => (hi f g).const_mul _]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [efi_sum _ fun g _ => (hi f g).const_mul _]
  exact Finset.sum_congr rfl fun g _ => (efi_const_mul _ _).symm

/-- **The energy-first integral of `ggInt` at fixed `ε ∈ (0, 1]`**, with integrability. -/
theorem efi_ggInt_eq (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hM₀ : 0 < M₀) (hM₀m : M₀ ≤ P.m) (hMs : ∀ i, M₀ ≤ Ms i)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (hjk : j + 2 ≤ k) (a₁ a₂ : ℂ) {w₁ w₂ : ℝ → ℂ}
    (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) {W₁ W₂ : ℝ}
    (hW₁ : ∀ x ∈ Ioo (0 : ℝ) 1, ‖w₁ x‖ ≤ W₁) (hW₂ : ∀ x ∈ Ioo (0 : ℝ) 1, ‖w₂ x‖ ≤ W₂)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    EFInt (ggInt P N Ms j a₁ a₂ w₁ w₂ ε p' p) ∧
      energyFirstIntegral (ggInt P N Ms j a₁ a₂ w₁ w₂ ε p' p) =
        a₁ * a₂ * logSum P ε ^ 2 *
            energyFirstIntegral (powInt N P.m j Ms (fun _ => ε) ε p' p) -
          a₁ * logSum P ε * (∫ x in Ioc (0 : ℝ) 1,
            energyFirstIntegral (oneInt P N Ms j w₂ ε p' p x)) -
          a₂ * logSum P ε * (∫ x in Ioc (0 : ℝ) 1,
            energyFirstIntegral (oneInt P N Ms j w₁ ε p' p x)) +
          ∫ z, energyFirstIntegral (twoInt P N Ms j w₁ w₂ ε p' p z) ∂nu2 := by
  obtain ⟨C0, h0⟩ := exists_good_pw hm hM₀ hMs hp' hp hp0' hp0 hNc hNq hNb (j := j) (by omega)
  obtain ⟨C1, h1⟩ := exists_good_oneInt hm hM₁ hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 hNc hNq hNb
    (j := j) (by omega) hW₁
  obtain ⟨C2, h2⟩ := exists_good_oneInt hm hM₁ hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 hNc hNq hNb
    (j := j) (by omega) hW₂
  obtain ⟨C3, h3⟩ := exists_good_twoInt hm hM₁ hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 hNc hNq hNb hjk
    hW₁ hW₂
  obtain ⟨G0, g0⟩ := h0 ε hε hε1
  obtain ⟨G1, g1⟩ := h1 ε hε hε1
  obtain ⟨G2, g2⟩ := h2 ε hε hε1
  obtain ⟨G3, g3⟩ := h3 ε hε hε1
  obtain ⟨i1, e1⟩ := efi_integral_eq_of_good (ν := volume.restrict (Ioc (0 : ℝ) 1))
    (oneInt P N Ms j w₁ ε p' p) (measurable_oneInt P hNc Ms j hw₁ ε p' p) (ae_Ioc_good g1)
  obtain ⟨i2, e2⟩ := efi_integral_eq_of_good (ν := volume.restrict (Ioc (0 : ℝ) 1))
    (oneInt P N Ms j w₂ ε p' p) (measurable_oneInt P hNc Ms j hw₂ ε p' p) (ae_Ioc_good g2)
  obtain ⟨i3, e3⟩ := efi_integral_eq_of_good (ν := nu2) (twoInt P N Ms j w₁ w₂ ε p' p)
    (measurable_twoInt P hNc Ms j hw₁ hw₂ ε p' p)
    (by filter_upwards [ae_nu2_mem] with z ⟨hx, hy⟩ using g3 z hx hy)
  have ia := g0.1.1.const_mul (a₁ * a₂ * logSum P ε ^ 2)
  have ib := i2.const_mul (a₁ * logSum P ε)
  have ic := i1.const_mul (a₂ * logSum P ε)
  have e : ggInt P N Ms j a₁ a₂ w₁ w₂ ε p' p = fun ℓ =>
      ((a₁ * a₂ * logSum P ε ^ 2 * powInt N P.m j Ms (fun _ => ε) ε p' p ℓ -
        a₁ * logSum P ε * (∫ x in Ioc (0 : ℝ) 1, oneInt P N Ms j w₂ ε p' p x ℓ)) -
        a₂ * logSum P ε * (∫ x in Ioc (0 : ℝ) 1, oneInt P N Ms j w₁ ε p' p x ℓ)) +
        ∫ z, twoInt P N Ms j w₁ w₂ ε p' p z ℓ ∂nu2 :=
    funext fun ℓ => ggInt_eq P N Ms j a₁ a₂ w₁ w₂ ε p' p ℓ
  have iab := efInt_sub' ia ib
  have iabc := efInt_sub' iab ic
  refine ⟨e ▸ iabc.add i3, ?_⟩
  rw [e, efi_add iabc i3, efi_sub iab ic, efi_sub ia ib, efi_const_mul, efi_const_mul,
    efi_const_mul, e1, e2, e3]

/-- **The `ε → 0⁺` limit of two spectral factors on `k + 2 ≥ j + 4` photon-type
denominators.** -/
theorem tendsto_efi_ggInt (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hM₀ : 0 < M₀) (hM₀m : M₀ ≤ P.m) (hMs : ∀ i, M₀ ≤ Ms i)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (hjk : j + 2 ≤ k) (a₁ a₂ : ℂ) {w₁ w₂ : ℝ → ℂ}
    (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) {W₁ W₂ : ℝ}
    (hW₁ : ∀ x ∈ Ioo (0 : ℝ) 1, ‖w₁ x‖ ≤ W₁) (hW₂ : ∀ x ∈ Ioo (0 : ℝ) 1, ‖w₂ x‖ ≤ W₂) :
    Tendsto (fun ε => energyFirstIntegral (ggInt P N Ms j a₁ a₂ w₁ w₂ ε p' p)) (𝓝[>] 0)
      (𝓝 (ggLimit P α N Ms j a₁ a₂ w₁ w₂ p' p)) := by
  have hmass : ∀ f, P.mass f ≠ 0 := fun f => (hm.trans_le (mass_ge hM₁ hM₂ f)).ne'
  obtain ⟨C1, h1⟩ := exists_good_oneInt hm hM₁ hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 hNc hNq hNb
    (j := j) (by omega) hW₁
  obtain ⟨C2, h2⟩ := exists_good_oneInt hm hM₁ hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 hNc hNq hNb
    (j := j) (by omega) hW₂
  obtain ⟨C3, h3⟩ := exists_good_twoInt hm hM₁ hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 hNc hNq hNb hjk
    hW₁ hW₂
  have hL := tendsto_logSum P hmass
  have T0 : Tendsto (fun ε : ℝ => energyFirstIntegral (powInt N P.m j Ms (fun _ => ε) ε p' p))
      (𝓝[>] 0) (𝓝 (powLimit α N P.m p' p j Ms)) :=
    tendsto_efi_powInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb tendsto_id j k (by omega) Ms
      (fun ε _ => ε) hMs (fun _ => tendsto_id)
  have T1 : ∀ (w : ℝ → ℂ) (C : ℝ), Measurable w →
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ G : (Fin 3 → ℝ) → ℝ,
        ∀ x ∈ Ioo (0 : ℝ) 1, Good (oneInt P N Ms j w ε p' p x) C G) →
      Tendsto (fun ε => ∫ x in Ioc (0 : ℝ) 1, energyFirstIntegral (oneInt P N Ms j w ε p' p x))
        (𝓝[>] 0) (𝓝 (∫ x in Ioc (0 : ℝ) 1, oneLim P α N Ms j w p' p x)) := by
    intro w C hw hg
    refine tendsto_integral_efi_of_good (fun ε => oneInt P N Ms j w ε p' p) _ (C := C)
      (Eventually.of_forall fun ε => measurable_oneInt P hNc Ms j hw ε p' p) ?_ ?_
    · filter_upwards [ev_pos_le_one] with ε ⟨hε, hε1⟩
      obtain ⟨G, hG⟩ := hg ε hε hε1
      exact ⟨G, ae_Ioc_good hG⟩
    · exact ae_Ioc_good fun x hx => tendsto_efi_oneInt hm hM₁ hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0
        hNc hNq hNb (by omega) w hx
  have T3 : Tendsto (fun ε => ∫ z, energyFirstIntegral (twoInt P N Ms j w₁ w₂ ε p' p z) ∂nu2)
      (𝓝[>] 0) (𝓝 (∫ z, twoLim P α N Ms j w₁ w₂ p' p z ∂nu2)) := by
    refine tendsto_integral_efi_of_good (fun ε => twoInt P N Ms j w₁ w₂ ε p' p) _ (C := C3)
      (Eventually.of_forall fun ε => measurable_twoInt P hNc Ms j hw₁ hw₂ ε p' p) ?_ ?_
    · filter_upwards [ev_pos_le_one] with ε ⟨hε, hε1⟩
      obtain ⟨G, hG⟩ := h3 ε hε hε1
      exact ⟨G, by filter_upwards [ae_nu2_mem] with z ⟨hx, hy⟩ using hG z hx hy⟩
    · filter_upwards [ae_nu2_mem] with z ⟨hx, hy⟩
      exact tendsto_efi_twoInt hm hM₁ hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 hNc hNq hNb hjk w₁ w₂ hx hy
  have hlim := (((((hL.pow 2).const_mul (a₁ * a₂)).mul T0).sub
    ((hL.const_mul a₁).mul (T1 w₂ C2 hw₂ h2))).sub
    ((hL.const_mul a₂).mul (T1 w₁ C1 hw₁ h1))).add T3
  unfold ggLimit
  refine hlim.congr' ?_
  filter_upwards [ev_pos_le_one] with ε ⟨hε, hε1⟩
  rw [(efi_ggInt_eq hm hM₁ hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 hNc hNq hNb hjk a₁ a₂ hw₁ hw₂ hW₁ hW₂
    hε hε1).2]

end Limit

end QED.ChainProof.HCBB2

end
