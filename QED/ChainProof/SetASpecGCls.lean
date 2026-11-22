/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecOne
public import QED.GradedProof.VP2LimG
public import QED.TwoLoop.VPHalfAtNested

/-!
# Set (a): the classes `G0`, `G1` and the counterterm have the spectral tensor form

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.

* `saTermC`, `saForm_termC`: a constant term `t(k) (k²)ʲ c` (`r = 0`, simplex of dimension one);
* `saTermL`, `saForm_termL`: a line term `t(k) (k²)ʲ ∫₀¹ w(x) fDen(M, ε, x, k)⁻¹ dx` with a
  continuous weight (`r = 1`, `ξ = x`);
* `saForm_ct`: the counterterm tensor `-c (k² g - k k)`;
* `integral_vpRatSum_mul`: the Feynman-parameter integrals of set (b)'s spectral form as line
  integrals of `fDen⁻¹`;
* **`saForm_vpLoop`**: the one-loop vacuum polarization of a three-flavour Pauli–Villars set at
  fixed `ε > 0`, `i Π̂_ε(k²) (k² g - k k) + ε S_ε(k²) g`
  (`QED.TwoLoop.VPHalfAt.energyFirstIntegral_vacuumPolarizationIntegrand_eq`), after set (b)'s
  integration by parts (`vpLoopEps_eq_spectral`, `vpExtraEps_eq_spectral`), is `SAForm`;
* **`saForm_val0_repG0`**, **`saForm_val0_repG1`**: at `ε = P.ε > 0` the values of the classes
  `G0`, `G1` are `SAForm M_lo P.ε` for every `M_lo ≤ m₀`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.Integration.TwoLoop QED.TwoLoop.VPHalfAtAssembly QED.TwoLoop.VPHalfAt
open QED.Integration.Feynman (simplexSet)
open QED.WickModel (Params vacuumPolarizationIntegrand vacuumPolarizationFeynmanMass)

/-! ### Constant and line terms -/

/-- The constant term `t(k) (k²)ʲ c`. -/
noncomputable def saTermC (j : ℕ) (t : Bool) (c : ℂ) (Mlo : ℝ) : SATerm :=
  ⟨1, j, 0, t, fun _ => c, fun _ => Mlo, fun _ => 1 / 2⟩

/-- The line term `t(k) (k²)ʲ ∫₀¹ w(x) fDen(M, ε, x, k)⁻¹ dx`. -/
noncomputable def saTermL (j : ℕ) (t : Bool) (w : ℝ → ℂ) (M : ℝ) : SATerm :=
  ⟨1, j, 1, t, fun x => w (x 0), fun _ => M, fun x => x 0⟩

theorem saTermC_val (j : ℕ) (t : Bool) (c : ℂ) (Mlo ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    (saTermC j t c Mlo).val ε k μ ν = saTens t k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ j * c := by
  change saTens t k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ j *
    (∫ _ in simplexSet 1, c * ((fDen Mlo ε (1 / 2) k) ^ 0)⁻¹) = _
  simp only [pow_zero, inv_one, mul_one]
  rw [saIntegral_simplexOne_const]

theorem saTermL_val (j : ℕ) (t : Bool) (w : ℝ → ℂ) (M ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    (saTermL j t w M).val ε k μ ν = saTens t k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ j *
      ∫ x in (0 : ℝ)..1, w x * (fDen M ε x k)⁻¹ := by
  change saTens t k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ j *
    (∫ x in simplexSet 1, w (x 0) * ((fDen M ε (x 0) k) ^ 1)⁻¹) = _
  simp only [pow_one]
  rw [saIntegral_simplexOne (fun x => w x * (fDen M ε x k)⁻¹)]

theorem saForm_termC {Mlo ε : ℝ} (j : ℕ) (t : Bool) (hj : j + (if t then 1 else 0) ≤ 2)
    (c : ℂ) : SAForm Mlo ε fun k μ ν => saTens t k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ j * c := by
  refine ⟨[saTermC j t c Mlo], fun τ hτ => ?_, fun k μ ν => by simp [saTermC_val]⟩
  rw [List.mem_singleton] at hτ
  subst hτ
  refine ⟨?_, measurable_const, measurable_const, ?_, hj⟩
  · exact (integrableOn_const (μ := (volume : Measure (Fin 1 → ℝ))) (s := simplexSet 1)
      (C := c) (QED.Integration.Feynman.isCompact_simplexSet 1).measure_lt_top.ne :)
  · have h : ∀ᵐ _ ∂((volume : Measure (Fin 1 → ℝ)).restrict (simplexSet 1)),
        Mlo ≤ Mlo ∧ (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 :=
      Eventually.of_forall fun _ => ⟨le_rfl, by norm_num, by norm_num⟩
    exact h

/-- Almost every point of the simplex of dimension one is interior. -/
theorem saAe_simplexOne :
    ∀ᵐ x ∂(volume.restrict (simplexSet 1)), x 0 ∈ Ioo (0 : ℝ) 1 := by
  have h0 : volume ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' ({0, 1} : Set ℝ)) = 0 :=
    ((volume_preserving_funUnique (Fin 1) ℝ).measure_preimage
      (s := ({0, 1} : Set ℝ)) (by measurability)).trans ((Set.toFinite _).measure_zero _)
  have hae : ∀ᵐ x ∂(volume : Measure (Fin 1 → ℝ)), x 0 ≠ 0 ∧ x 0 ≠ 1 := by
    refine measure_mono_null (fun x hx => ?_) h0
    have hx' : ¬ (x 0 ≠ 0 ∧ x 0 ≠ 1) := hx
    show x 0 ∈ ({0, 1} : Set ℝ)
    by_cases h : x 0 = 0
    · exact Or.inl h
    · exact Or.inr (not_not.mp fun h' => hx' ⟨h, h'⟩)
  filter_upwards [ae_restrict_of_ae hae,
    ae_restrict_mem (QED.Integration.Feynman.measurableSet_simplexSet 1)] with x hx hm
  rw [saSimplexOne] at hm
  obtain ⟨h1, h2⟩ := hm
  exact ⟨lt_of_le_of_ne h1 (Ne.symm hx.1), lt_of_le_of_ne h2 hx.2⟩

theorem saForm_termL {Mlo ε : ℝ} (j : ℕ) (t : Bool) (hj : j + (if t then 1 else 0) ≤ 2)
    {w : ℝ → ℂ} (hw : Continuous w) {M : ℝ} (hM : Mlo ≤ M) :
    SAForm Mlo ε fun k μ ν => saTens t k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ j *
      ∫ x in (0 : ℝ)..1, w x * (fDen M ε x k)⁻¹ := by
  refine ⟨[saTermL j t w M], fun τ hτ => ?_, fun k μ ν => by simp [saTermL_val]⟩
  rw [List.mem_singleton] at hτ
  subst hτ
  refine ⟨?_, measurable_const, ?_, ?_, hj⟩
  · exact ((hw.comp (continuous_apply (0 : Fin 1))).continuousOn.integrableOn_compact
      (μ := (volume : Measure (Fin 1 → ℝ))) (QED.Integration.Feynman.isCompact_simplexSet 1) :)
  · exact (measurable_pi_apply (0 : Fin 1) : Measurable fun x : Fin 1 → ℝ => x 0)
  · have h : ∀ᵐ x ∂(volume.restrict (simplexSet 1)), Mlo ≤ M ∧ x 0 ∈ Ioo (0 : ℝ) 1 := by
      filter_upwards [saAe_simplexOne] with x hx
      exact ⟨hM, hx⟩
    exact h

/-- **The counterterm tensor** `-c (k² g - k k)`. -/
theorem saForm_ct {Mlo ε : ℝ} (c : ℝ) :
    SAForm Mlo ε fun k μ ν =>
      -((c * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν) : ℝ) : ℂ) := by
  refine ((saForm_termC 1 false (by norm_num) (-(c : ℂ))).add
    (saForm_termC 0 true (by norm_num) (c : ℂ))).congr fun k μ ν => ?_
  simp only [saTens]
  push_cast
  ring

/-! ### The one-loop vacuum polarization at fixed `ε` -/

theorem continuous_fDen_inv (M : ℝ) {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) :
    Continuous fun x => (fDen M ε x k)⁻¹ := by
  refine Continuous.inv₀ (by unfold fDen vacuumPolarizationFeynmanMass; fun_prop) fun x => ?_
  exact slitPlane_ne_zero (feynmanMass_sub_mem_slitPlane _ _ x hε)

/-- **The Feynman-parameter integrals of the spectral form** as line integrals of `fDen⁻¹`. -/
theorem integral_vpRatSum_mul (Q : Params) {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) :
    ∫ x in (0 : ℝ)..1, vpRatSum Q ε (Minkowski.dot k k) x * ((w x : ℝ) : ℂ) =
      ∑ f, (Q.loopCoeff f : ℂ) * ((Minkowski.dot k k : ℝ) : ℂ) *
        ∫ x in (0 : ℝ)..1, (((1 - 2 * x) * w x : ℝ) : ℂ) * (fDen (Q.mass f) ε x k)⁻¹ := by
  have hc : ∀ f, Continuous fun x : ℝ => (((1 - 2 * x) * w x : ℝ) : ℂ) *
      (fDen (Q.mass f) ε x k)⁻¹ := fun f =>
    (continuous_ofReal.comp ((by fun_prop : Continuous fun x : ℝ => 1 - 2 * x).mul hw)).mul
      (continuous_fDen_inv _ hε k)
  have e : ∀ x : ℝ, vpRatSum Q ε (Minkowski.dot k k) x * ((w x : ℝ) : ℂ) =
      ∑ f, (Q.loopCoeff f : ℂ) * ((Minkowski.dot k k : ℝ) : ℂ) *
        ((((1 - 2 * x) * w x : ℝ) : ℂ) * (fDen (Q.mass f) ε x k)⁻¹) := fun x => by
    simp only [vpRatSum, fDen, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    push_cast
    ring
  simp only [e]
  rw [intervalIntegral.integral_finsetSum fun f _ =>
    ((hc f).const_mul _).intervalIntegrable 0 1]
  exact Finset.sum_congr rfl fun f _ => intervalIntegral.integral_const_mul _ _

/-- **The one-loop vacuum polarization at fixed `ε > 0`** has the spectral tensor form. -/
theorem saForm_vpLoop {Q : Params} (hm : 0 < Q.m) (hM₁ : Q.m < Q.M₁) (hM₂ : Q.m < Q.M₂)
    (hPV₁ : 1 + Q.c₁ + Q.c₂ = 0) (hPV₂ : Q.m ^ 2 + Q.c₁ * Q.M₁ ^ 2 + Q.c₂ * Q.M₂ ^ 2 = 0)
    {ε : ℝ} (hε : 0 < ε) {Mlo : ℝ} (hlo : Mlo ≤ Q.m) :
    SAForm Mlo ε fun k μ ν =>
      QED.OneLoop.energyFirstIntegral fun ℓ => vacuumPolarizationIntegrand Q ε k ℓ μ ν := by
  have hlo' : ∀ f, Mlo ≤ Q.mass f := fun f => by
    fin_cases f <;> simp [QED.WickModel.Params.mass] <;> linarith
  set C1 : ℂ := ((Q.e ^ 2 / (2 * π ^ 2) : ℝ) : ℂ) with hC1
  set C2 : ℂ := ((Q.e ^ 2 / (4 * π ^ 2) : ℝ) : ℂ) with hC2
  set L : ℂ := ∑ f, (Q.loopCoeff f : ℂ) * log (((Q.mass f ^ 2 : ℝ) : ℂ) - ε * I) with hL
  set u1 : ℝ → ℂ := fun x => (((1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3) : ℝ) : ℂ) with hu1
  set u2 : ℝ → ℂ := fun x => (((1 - 2 * x) * x : ℝ) : ℂ) with hu2
  have cu1 : Continuous u1 := by simp only [hu1]; fun_prop
  have cu2 : Continuous u2 := by simp only [hu2]; fun_prop
  have T1 := saForm_termC (Mlo := Mlo) (ε := ε) 1 false (by norm_num) (I * C1 * L / 6)
  have T2 := saForm_termC (Mlo := Mlo) (ε := ε) 0 true (by norm_num) (-(I * C1 * L / 6))
  have T5 := saForm_termC (Mlo := Mlo) (ε := ε) 0 false (by norm_num) ((ε : ℂ) * C2 * L)
  have T3 := SAForm.sum Finset.univ fun f (_ : f ∈ Finset.univ) =>
    (saForm_termL (ε := ε) 2 false (by norm_num) cu1 (hlo' f)).const_mul
      (-(I * C1 * (Q.loopCoeff f : ℂ)))
  have T4 := SAForm.sum Finset.univ fun f (_ : f ∈ Finset.univ) =>
    (saForm_termL (ε := ε) 1 true (by norm_num) cu1 (hlo' f)).const_mul
      (I * C1 * (Q.loopCoeff f : ℂ))
  have T6 := SAForm.sum Finset.univ fun f (_ : f ∈ Finset.univ) =>
    (saForm_termL (ε := ε) 1 false (by norm_num) cu2 (hlo' f)).const_mul
      (-((ε : ℂ) * C2 * (Q.loopCoeff f : ℂ)))
  refine (((((T1.add T2).add T3).add T4).add T5).add T6).congr fun k μ ν => ?_
  rw [energyFirstIntegral_vacuumPolarizationIntegrand_eq hm hM₁ hM₂ hPV₁ hPV₂ hε,
    vpLoopEps_eq_spectral Q hε, vpExtraEps_eq_spectral Q hε,
    integral_vpRatSum_mul Q hε k (w := fun x => x ^ 2 / 2 - x ^ 3 / 3) (by fun_prop)]
  have e2 : ∫ x in (0 : ℝ)..1, vpRatSum Q ε (Minkowski.dot k k) x * (x : ℂ) =
      ∑ f, (Q.loopCoeff f : ℂ) * ((Minkowski.dot k k : ℝ) : ℂ) *
        ∫ x in (0 : ℝ)..1, u2 x * (fDen (Q.mass f) ε x k)⁻¹ :=
    integral_vpRatSum_mul Q hε k (w := fun x => x) continuous_id
  rw [e2]
  simp only [saTens, Fin.sum_univ_three, ← hC1, ← hC2, ← hL, hu1]
  push_cast
  ring

/-! ### The classes -/

section Classes

open QED.GradedProof.VP2

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : QED.Graded.Counterterms F) (rep : F → F)
  {m₀ Mlo : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (hlo : Mlo ≤ m₀) (hε : 0 < P.ε)
include hm₀ hmass hrep hPV₁ hPV₂ hlo hε

/-- **The block-summed bubble at `ε = P.ε > 0`** has the spectral tensor form. -/
theorem saForm_blockBubble (d : F → ℂ) :
    SAForm Mlo P.ε fun k μ ν => QED.OneLoop.energyFirstIntegral fun q =>
      ∑ f, (Φ.coeff f : ℂ) * (d (rep f) * bubbleW P.e (Φ.mass f) P.ε k q μ ν) := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  set X : ℝ := auxX Φ with hX
  have hlt : ∀ g, Φ.mass g < X := fun g => by
    have := Finset.single_le_sum (f := Φ.mass) (fun g _ => (hpos g).le) (Finset.mem_univ g)
    simp only [hX, auxX]
    linarith
  have hXY : ∀ g, Φ.mass g < X + 1 := fun g => (hlt g).trans (by linarith)
  set Q : F → Params := fun f => triParams P (Φ.mass f) X (X + 1) with hQ
  have hpv : ∀ f, 1 + (Q f).c₁ + (Q f).c₂ = 0 := fun f =>
    triA_triB_pv₁ _ _ _ (by nlinarith [hlt f, hpos f])
  have hpv₂ : ∀ f, (Q f).m ^ 2 + (Q f).c₁ * (Q f).M₁ ^ 2 + (Q f).c₂ * (Q f).M₂ ^ 2 = 0 :=
    fun f => triA_triB_pv₂ _ _ _ (by nlinarith [hlt f, hpos f])
  have hsplit : ∀ ℓ k μ ν,
      ∑ f, (Φ.coeff f : ℂ) * (d (rep f) * bubbleW P.e (Φ.mass f) P.ε k ℓ μ ν) =
      ∑ f, (Φ.coeff f : ℂ) * (-d (rep f) * vacuumPolarizationIntegrand (Q f) P.ε k ℓ μ ν) :=
    fun ℓ k μ ν => by
      rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1)
        (fun b M => d b * bubbleW P.e M P.ε k ℓ μ ν)]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [hQ, vacuumPolarizationIntegrand_triParams]
      ring
  have hD : ∀ k μ ν f, QED.TwoLoop.NestedVP.IntegrableD fun ℓ =>
      (Φ.coeff f : ℂ) * (-d (rep f) * vacuumPolarizationIntegrand (Q f) P.ε k ℓ μ ν) :=
    fun k μ ν f => ((QED.TwoLoop.NestedVP.IntegrableD.const_mul ⟨fun v =>
      QED.WickModel.VacuumPolarizationLimit.integrable_vacuumPolarizationIntegrand_time hε _ k μ
        ν v,
      QED.WickModel.VacuumPolarizationLimit.integrable_integral_vacuumPolarizationIntegrand
        (P := Q f) (hpos f) (hlt f) (hXY f) (hpv f) (hpv₂ f) hε k μ ν⟩ _).const_mul _)
  refine (SAForm.sum Finset.univ fun f (_ : f ∈ Finset.univ) =>
    ((saForm_vpLoop (Q := Q f) (hpos f) (hlt f) (hXY f) (hpv f) (hpv₂ f) hε
      (hlo.trans (hmass f))).const_mul (-d (rep f))).const_mul (Φ.coeff f : ℂ)).congr
    fun k μ ν => ?_
  simp only [hsplit _ k μ ν]
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_finsetSum _ _ fun f _ => hD k μ ν f]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul,
    QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]

variable (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0)
include hD

/-- **The class `G0` at `ε = P.ε > 0`** has the spectral tensor form. -/
theorem saForm_val0_repG0 : SAForm Mlo P.ε fun k μ ν => val0 P Φ D k μ ν repG0 :=
  (saForm_blockBubble P Φ rep hm₀ hmass hrep hPV₁ hPV₂ hlo hε
    fun b => ((P.e ^ 2 * D.d₁ b 0 : ℝ) : ℂ)).congr fun k μ ν =>
      (val0_repG0 P Φ D rep hD k μ ν).symm

/-- **The class `G1` at `ε = P.ε > 0`** has the spectral tensor form. -/
theorem saForm_val0_repG1 : SAForm Mlo P.ε fun k μ ν => val0 P Φ D k μ ν repG1 :=
  (saForm_blockBubble P Φ rep hm₀ hmass hrep hPV₁ hPV₂ hlo hε
    fun b => ((P.e ^ 2 * D.d₁ b 0 : ℝ) : ℂ)).congr fun k μ ν =>
      (val0_repG1 P Φ D rep hD k μ ν).symm

end Classes

end QED.ChainProof.SetASpec

end
