/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecUForm
public import QED.ChainProof.SetASpecGCls

/-!
# Set (a): the classes `G0`, `G1` and the counterterm have the uniform spectral tensor form

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
The `ε`-uniform copy of `QED.ChainProof.SetASpec.saForm_termC`, …, `saForm_val0_repG1`. The
`ε`-dependent coefficients of the one-loop vacuum polarization at fixed `ε`, `ε` and
`L(ε) = ∑_f c_f log(M_f² - iε)`, are continuous on `ℝ` (`M_f > 0`), hence uniform.

* `saUForm_termC` (with a uniform coefficient), `saUForm_termL`, `saUForm_ct`;
* **`saUForm_vpLoop`**, `saUForm_blockBubble`;
* **`saUForm_val0_repG0`**, **`saUForm_val0_repG1`**.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.Integration.TwoLoop QED.TwoLoop.VPHalfAtAssembly QED.TwoLoop.VPHalfAt
open QED.Integration.Feynman (simplexSet)
open QED.WickModel (Params vacuumPolarizationIntegrand vacuumPolarizationFeynmanMass)

/-! ### Constant and line terms -/

theorem saTermC_good {Mlo : ℝ} (j : ℕ) (t : Bool) (hj : j + (if t then 1 else 0) ≤ 2)
    (c : ℂ) : (saTermC j t c Mlo).Good Mlo := by
  refine ⟨?_, measurable_const, measurable_const, ?_, hj⟩
  · exact (integrableOn_const (μ := (volume : Measure (Fin 1 → ℝ))) (s := simplexSet 1)
      (C := c) (QED.Integration.Feynman.isCompact_simplexSet 1).measure_lt_top.ne :)
  · have h : ∀ᵐ _ ∂((volume : Measure (Fin 1 → ℝ)).restrict (simplexSet 1)),
        Mlo ≤ Mlo ∧ (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 :=
      Eventually.of_forall fun _ => ⟨le_rfl, by norm_num, by norm_num⟩
    exact h

/-- **A constant term with a uniform coefficient** `t(k) (k²)ʲ c(ε)`. -/
theorem saUForm_termC {Mlo : ℝ} (j : ℕ) (t : Bool) (hj : j + (if t then 1 else 0) ≤ 2)
    {c : ℝ → ℂ} (hc : SAUCoef c) :
    SAUForm Mlo fun ε k μ ν => saTens t k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ j * c ε := by
  refine ((SAUForm.of_list [saTermC j t 1 Mlo] (fun τ hτ => by
    rw [List.mem_singleton] at hτ
    subst hτ
    exact saTermC_good j t hj 1) (fun ε _ _ k μ ν => rfl)).mul hc).congr
    fun ε _ _ k μ ν => ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, saTermC_val]
  ring

/-- **A line term** with a continuous weight. -/
theorem saUForm_termL {Mlo : ℝ} (j : ℕ) (t : Bool) (hj : j + (if t then 1 else 0) ≤ 2)
    {w : ℝ → ℂ} (hw : Continuous w) {M : ℝ} (hM : Mlo ≤ M) :
    SAUForm Mlo fun ε k μ ν => saTens t k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ j *
      ∫ x in (0 : ℝ)..1, w x * (fDen M ε x k)⁻¹ := by
  refine SAUForm.of_list [saTermL j t w M] (fun τ hτ => ?_)
    fun ε _ _ k μ ν => by simp [saTermL_val]
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
theorem saUForm_ct {Mlo : ℝ} (c : ℝ) :
    SAUForm Mlo fun _ k μ ν =>
      -((c * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν) : ℝ) : ℂ) := by
  refine ((saUForm_termC 1 false (by norm_num) (SAUCoef.const (-(c : ℂ)))).add
    (saUForm_termC 0 true (by norm_num) (SAUCoef.const (c : ℂ)))).congr fun ε _ _ k μ ν => ?_
  simp only [saTens]
  push_cast
  ring

/-! ### The one-loop vacuum polarization -/

/-- **The one-loop vacuum polarization** has the uniform spectral tensor form. -/
theorem saUForm_vpLoop {Q : Params} (hm : 0 < Q.m) (hM₁ : Q.m < Q.M₁) (hM₂ : Q.m < Q.M₂)
    (hPV₁ : 1 + Q.c₁ + Q.c₂ = 0) (hPV₂ : Q.m ^ 2 + Q.c₁ * Q.M₁ ^ 2 + Q.c₂ * Q.M₂ ^ 2 = 0)
    {Mlo : ℝ} (hlo : Mlo ≤ Q.m) :
    SAUForm Mlo fun ε k μ ν =>
      QED.OneLoop.energyFirstIntegral fun ℓ => vacuumPolarizationIntegrand Q ε k ℓ μ ν := by
  have hlo' : ∀ f, Mlo ≤ Q.mass f := fun f => by
    fin_cases f <;> simp [QED.WickModel.Params.mass] <;> linarith
  have hpos : ∀ f, 0 < Q.mass f := fun f => by
    fin_cases f <;> simp [QED.WickModel.Params.mass] <;> linarith
  set C1 : ℂ := ((Q.e ^ 2 / (2 * π ^ 2) : ℝ) : ℂ) with hC1
  set C2 : ℂ := ((Q.e ^ 2 / (4 * π ^ 2) : ℝ) : ℂ) with hC2
  set L : ℝ → ℂ := fun ε => ∑ f, (Q.loopCoeff f : ℂ) * log (((Q.mass f ^ 2 : ℝ) : ℂ) - ε * I)
    with hL
  have cL : Continuous L := by
    refine continuous_finsetSum _ fun f _ => continuous_const.mul ?_
    refine Continuous.clog (by fun_prop) fun ε => Or.inl ?_
    have := hpos f
    simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero]
    positivity
  set u1 : ℝ → ℂ := fun x => (((1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3) : ℝ) : ℂ) with hu1
  set u2 : ℝ → ℂ := fun x => (((1 - 2 * x) * x : ℝ) : ℂ) with hu2
  have cu1 : Continuous u1 := by simp only [hu1]; fun_prop
  have cu2 : Continuous u2 := by simp only [hu2]; fun_prop
  have T1 := saUForm_termC (Mlo := Mlo) 1 false (by norm_num)
    (SAUCoef.of_continuous (c := fun ε => I * C1 * L ε / 6) (by fun_prop))
  have T2 := saUForm_termC (Mlo := Mlo) 0 true (by norm_num)
    (SAUCoef.of_continuous (c := fun ε => -(I * C1 * L ε / 6)) (by fun_prop))
  have T5 := saUForm_termC (Mlo := Mlo) 0 false (by norm_num)
    (SAUCoef.of_continuous (c := fun ε => (ε : ℂ) * C2 * L ε) (by fun_prop))
  have T3 := SAUForm.sum Finset.univ fun f (_ : f ∈ Finset.univ) =>
    (saUForm_termL 2 false (by norm_num) cu1 (hlo' f)).const_mul
      (-(I * C1 * (Q.loopCoeff f : ℂ)))
  have T4 := SAUForm.sum Finset.univ fun f (_ : f ∈ Finset.univ) =>
    (saUForm_termL 1 true (by norm_num) cu1 (hlo' f)).const_mul
      (I * C1 * (Q.loopCoeff f : ℂ))
  have T6 := SAUForm.sum Finset.univ fun f (_ : f ∈ Finset.univ) =>
    (saUForm_termL 1 false (by norm_num) cu2 (hlo' f)).mul
      (SAUCoef.of_continuous (c := fun ε : ℝ => -((ε : ℂ) * C2 * (Q.loopCoeff f : ℂ)))
        (by fun_prop))
  refine (((((T1.add T2).add T3).add T4).add T5).add T6).congr fun ε hε _ k μ ν => ?_
  rw [energyFirstIntegral_vacuumPolarizationIntegrand_eq hm hM₁ hM₂ hPV₁ hPV₂ hε,
    vpLoopEps_eq_spectral Q hε, vpExtraEps_eq_spectral Q hε,
    integral_vpRatSum_mul Q hε k (w := fun x => x ^ 2 / 2 - x ^ 3 / 3) (by fun_prop)]
  have e2 : ∫ x in (0 : ℝ)..1, vpRatSum Q ε (Minkowski.dot k k) x * (x : ℂ) =
      ∑ f, (Q.loopCoeff f : ℂ) * ((Minkowski.dot k k : ℝ) : ℂ) *
        ∫ x in (0 : ℝ)..1, u2 x * (fDen (Q.mass f) ε x k)⁻¹ :=
    integral_vpRatSum_mul Q hε k (w := fun x => x) continuous_id
  rw [e2]
  simp only [saTens, Fin.sum_univ_three, ← hC1, ← hC2, hL, hu1]
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
  (hlo : Mlo ≤ m₀)
include hm₀ hmass hrep hPV₁ hPV₂ hlo

/-- **The block-summed bubble** has the uniform spectral tensor form. -/
theorem saUForm_blockBubble (d : F → ℂ) :
    SAUForm Mlo fun ε k μ ν => QED.OneLoop.energyFirstIntegral fun q =>
      ∑ f, (Φ.coeff f : ℂ) * (d (rep f) * bubbleW P.e (Φ.mass f) ε k q μ ν) := by
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
  have hsplit : ∀ ε ℓ k μ ν,
      ∑ f, (Φ.coeff f : ℂ) * (d (rep f) * bubbleW P.e (Φ.mass f) ε k ℓ μ ν) =
      ∑ f, (Φ.coeff f : ℂ) * (-d (rep f) * vacuumPolarizationIntegrand (Q f) ε k ℓ μ ν) :=
    fun ε ℓ k μ ν => by
      rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1)
        (fun b M => d b * bubbleW P.e M ε k ℓ μ ν)]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [hQ, vacuumPolarizationIntegrand_triParams]
      ring
  refine (SAUForm.sum Finset.univ fun f (_ : f ∈ Finset.univ) =>
    ((saUForm_vpLoop (Q := Q f) (hpos f) (hlt f) (hXY f) (hpv f) (hpv₂ f)
      (hlo.trans (hmass f))).const_mul (-d (rep f))).const_mul (Φ.coeff f : ℂ)).congr
    fun ε hε _ k μ ν => ?_
  have hD : ∀ f, QED.TwoLoop.NestedVP.IntegrableD fun ℓ =>
      (Φ.coeff f : ℂ) * (-d (rep f) * vacuumPolarizationIntegrand (Q f) ε k ℓ μ ν) :=
    fun f => ((QED.TwoLoop.NestedVP.IntegrableD.const_mul ⟨fun v =>
      QED.WickModel.VacuumPolarizationLimit.integrable_vacuumPolarizationIntegrand_time hε _ k μ
        ν v,
      QED.WickModel.VacuumPolarizationLimit.integrable_integral_vacuumPolarizationIntegrand
        (P := Q f) (hpos f) (hlt f) (hXY f) (hpv f) (hpv₂ f) hε k μ ν⟩ _).const_mul _)
  simp only [hsplit ε _ k μ ν]
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_finsetSum _ _ fun f _ => hD f]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul,
    QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]

variable (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0)
include hD

/-- **The class `G0`** has the uniform spectral tensor form. -/
theorem saUForm_val0_repG0 :
    SAUForm Mlo fun ε k μ ν => val0 { P with ε := ε } Φ D k μ ν repG0 :=
  (saUForm_blockBubble P Φ rep hm₀ hmass hrep hPV₁ hPV₂ hlo
    fun b => ((P.e ^ 2 * D.d₁ b 0 : ℝ) : ℂ)).congr fun ε _ _ k μ ν =>
      (val0_repG0 { P with ε := ε } Φ D rep hD k μ ν).symm

/-- **The class `G1`** has the uniform spectral tensor form. -/
theorem saUForm_val0_repG1 :
    SAUForm Mlo fun ε k μ ν => val0 { P with ε := ε } Φ D k μ ν repG1 :=
  (saUForm_blockBubble P Φ rep hm₀ hmass hrep hPV₁ hPV₂ hlo
    fun b => ((P.e ^ 2 * D.d₁ b 0 : ℝ) : ℂ)).congr fun ε _ _ k μ ν =>
      (val0_repG1 { P with ε := ε } Φ D rep hD k μ ν).symm

end Classes

end QED.ChainProof.SetASpec

end
