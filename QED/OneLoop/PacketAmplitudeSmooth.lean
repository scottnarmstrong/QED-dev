/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.PacketAmplitude
public import QED.OneLoop.VertexFormFactors
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support
import QED.Algebra.OnShell
import QED.Algebra.Spinor
import QED.Algebra.SpinorSmooth
import QED.OneLoop.FormFactorPair
import QED.OneLoop.FormFactorSmooth
import QED.OneLoop.OneParticle
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity

/-!
# Smoothness and compact support of the packet amplitude

The packet amplitude `F(k, k') = w(k') w(k) M(k', k)` (`QED.OneLoop.packetAmplitude`) is `C^∞`
in `(k, k')` jointly, and it has compact support when the profile `φ` does.

The on-shell energy `ω(k) = √(m² + |k⃗|²)` is smooth since `m > 0`. The matrix element is the
sandwich `ū₊(p') Γ(p', p) u₊(p)` of the on-shell matrix
`Γ = Z₁ e γ² + e (A γ² - (i/m) B Σ_ν q_ν S^{2ν})` (`packetMatrixElement_eq`), obtained from the
form-factor decomposition of the one-loop vertex. The spinors are smooth because `p⁰ > 0`, and the
form factors `A`, `B` are smooth functions of `q² ≥ 0 > -4m²`
(`QED.OneLoop.VertexLimit.contDiffOn_integral_formIntegrandAq`,
`QED.OneLoop.VertexLimit.contDiffOn_integral_pauliIntegrand`).

## Main statements

* `QED.OneLoop.contDiff_oneParticleMomentum`: smoothness of `k ↦ (ω(k), k⃗)`.
* `QED.OneLoop.contDiff_packetMatrixElement`: smoothness of `M(k', k)`.
* `QED.OneLoop.contDiff_packetWeight`: smoothness of the packet weight.
* `QED.OneLoop.contDiff_packetAmplitude`: smoothness of the packet amplitude.
* `QED.OneLoop.hasCompactSupport_packetAmplitude`: compact support of the packet amplitude.
-/

public section

open Matrix Complex Set
open scoped ContDiff

namespace QED.OneLoop

/-- The squared Euclidean length `k⃗ ↦ |k⃗|²` is `C^∞`. -/
private theorem contDiff_sum_sq : ContDiff ℝ ∞ (fun k : Fin 3 → ℝ => ∑ j, k j ^ 2) :=
  ContDiff.sum fun j _ => (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) j).pow 2

/-- For `m > 0`, the on-shell four-momentum `k⃗ ↦ (√(m² + |k⃗|²), k⃗)` is `C^∞`. -/
theorem contDiff_oneParticleMomentum {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ ∞ (oneParticleMomentum m) := by
  refine contDiff_pi.2 fun i => Fin.cases ?_ (fun j => ?_) i
  · simp only [oneParticleMomentum, Fin.cons_zero]
    exact (contDiff_const.add contDiff_sum_sq).sqrt
      fun k => (by positivity : 0 < m ^ 2 + ∑ j, k j ^ 2).ne'
  · simp only [oneParticleMomentum, Fin.cons_succ]
    exact contDiff_apply ℝ (fun _ : Fin 3 => ℝ) j

/-- The Minkowski square `q·q` of a `C^n` four-vector field is `C^n`. -/
theorem contDiff_dot_self_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {q : E → Fin 4 → ℝ} (hq : ContDiff ℝ n q) :
    ContDiff ℝ n (fun x => Minkowski.dot (q x) (q x)) := by
  unfold Minkowski.dot
  exact ContDiff.sum fun μ _ => ContDiff.sum fun ν _ =>
    (contDiff_const.mul (contDiff_pi.1 hq μ)).mul (contDiff_pi.1 hq ν)

/-- The momentum transfer `q = p(k⃗') - p(k⃗)` as a function of `(k⃗, k⃗')`. -/
theorem contDiff_oneParticleMomentum_sub {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ ∞ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      oneParticleMomentum m kk.2 - oneParticleMomentum m kk.1) :=
  ((contDiff_oneParticleMomentum hm).comp contDiff_snd).sub
    ((contDiff_oneParticleMomentum hm).comp contDiff_fst)

/-- For one-electron momenta, `q² = (p(k⃗') - p(k⃗))²` lies in `(-4m², ∞)`. -/
theorem dot_oneParticleMomentum_sub_mem_Ioi {m : ℝ} (hm : 0 < m) (k' k : Fin 3 → ℝ) :
    Minkowski.dot (oneParticleMomentum m k' - oneParticleMomentum m k)
        (oneParticleMomentum m k' - oneParticleMomentum m k) ∈ Ioi (-(4 * m ^ 2)) := by
  have h := Minkowski.dot_sub_self_nonneg_of_onShell (dot_oneParticleMomentum m k')
    (dot_oneParticleMomentum m k) (oneParticleMomentum_pos hm k') (oneParticleMomentum_pos hm k)
  have hm2 : 0 < 4 * m ^ 2 := by positivity
  exact mem_Ioi.2 (by linarith)

/-- The on-shell form factor `A(q²)` between one-electron momenta is `C^∞` in `(k⃗, k⃗')`. -/
theorem contDiff_formFactorA_oneParticleMomentum (e : ℝ) {m mγ Λ : ℝ} (hm : 0 < m)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    ContDiff ℝ ∞ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      VertexLimit.formFactorA e m mγ Λ (oneParticleMomentum m kk.2)
        (oneParticleMomentum m kk.1)) := by
  have h := (VertexLimit.contDiffOn_integral_formIntegrandAq hm hmγ hΛ).comp_contDiff
    (contDiff_dot_self_comp (contDiff_oneParticleMomentum_sub hm))
    fun kk => dot_oneParticleMomentum_sub_mem_Ioi hm kk.2 kk.1
  have heq : (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      VertexLimit.formFactorA e m mγ Λ (oneParticleMomentum m kk.2)
        (oneParticleMomentum m kk.1)) = fun kk => e ^ 2 / (16 * Real.pi ^ 2) *
      ∫ z, VertexLimit.formIntegrandAq m mγ Λ
        (Minkowski.dot (oneParticleMomentum m kk.2 - oneParticleMomentum m kk.1)
          (oneParticleMomentum m kk.2 - oneParticleMomentum m kk.1)) z
        ∂QED.Integration.feynmanMeasure :=
    funext fun kk => VertexLimit.formFactorA_eq_q (dot_oneParticleMomentum m kk.2)
      (dot_oneParticleMomentum m kk.1)
  rw [heq]
  exact contDiff_const.mul h

/-- The on-shell form factor `B(q²)` between one-electron momenta is `C^∞` in `(k⃗, k⃗')`. -/
theorem contDiff_formFactorB_oneParticleMomentum (e : ℝ) {m mγ Λ : ℝ} (hm : 0 < m)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    ContDiff ℝ ∞ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      VertexLimit.formFactorB e m mγ Λ (oneParticleMomentum m kk.2)
        (oneParticleMomentum m kk.1)) := by
  have h := (VertexLimit.contDiffOn_integral_pauliIntegrand hm hmγ hΛ).comp_contDiff
    (contDiff_dot_self_comp (contDiff_oneParticleMomentum_sub hm))
    fun kk => dot_oneParticleMomentum_sub_mem_Ioi hm kk.2 kk.1
  have heq : (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      VertexLimit.formFactorB e m mγ Λ (oneParticleMomentum m kk.2)
        (oneParticleMomentum m kk.1)) = fun kk => e ^ 2 / (8 * Real.pi ^ 2) *
      ∫ z, VertexLimit.pauliIntegrand m (mγ, Λ,
        Minkowski.dot (oneParticleMomentum m kk.2 - oneParticleMomentum m kk.1)
          (oneParticleMomentum m kk.2 - oneParticleMomentum m kk.1)) z
        ∂QED.Integration.feynmanMeasure :=
    funext fun kk => VertexLimit.formFactorB_eq (dot_oneParticleMomentum m kk.2)
      (dot_oneParticleMomentum m kk.1)
  rw [heq]
  exact contDiff_const.mul h

/-- The packet matrix element is the on-shell sandwich of
`Z₁ e γ² + e (A γ² - (i/m) B Σ_ν q_ν S^{2ν})`, with `q = p' - p`. -/
theorem packetMatrixElement_eq (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (k' k : Fin 3 → ℝ) :
    packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ k' k =
      Dirac.bar (Dirac.spinor m (oneParticleMomentum m k') 0) ⬝ᵥ
        ((((Z₁ * e : ℝ) : ℂ) • Dirac.gamma 2 + (e : ℂ) •
          (((VertexLimit.formFactorA e m mγ Λ (oneParticleMomentum m k')
              (oneParticleMomentum m k) : ℝ) : ℂ) • Dirac.gamma 2
            - (I / (m : ℂ) * ((VertexLimit.formFactorB e m mγ Λ (oneParticleMomentum m k')
              (oneParticleMomentum m k) : ℝ) : ℂ)) •
              ∑ ν, ((Minkowski.lower (oneParticleMomentum m k' - oneParticleMomentum m k) ν
                : ℝ) : ℂ) • Dirac.lorentzGen 2 ν))
          *ᵥ Dirac.spinor m (oneParticleMomentum m k) 0) := by
  have hp' := dot_oneParticleMomentum m k'
  have hp := dot_oneParticleMomentum m k
  have hu := Dirac.slash_mulVec_spinor m _ hp 0
  have hw := Dirac.bar_vecMul_slash m _ _ (Dirac.slash_mulVec_spinor m _ hp' 0)
  have hloop := VertexLimit.sandwich_vertexLimit (e := e) hm hmγ hΛ hp' hp
    (oneParticleMomentum_pos hm k') (oneParticleMomentum_pos hm k) 2 hu hw
  rw [← VertexLimit.vertexOneLoop_eq_limit hm hmγ hΛ hp' hp (oneParticleMomentum_pos hm k')
    (oneParticleMomentum_pos hm k) 2] at hloop
  unfold packetMatrixElement vertexFunction
  rw [Matrix.add_mulVec, dotProduct_add, hloop, Matrix.add_mulVec, dotProduct_add,
    Matrix.smul_mulVec (b := (e : ℂ)), dotProduct_smul, smul_eq_mul]

/-- **Smoothness of the matrix element.** At fixed regulators `m, m_γ, Λ > 0`, the one-electron
matrix element `M(k', k)` is `C^∞` in `(k⃗, k⃗')`; the ket momentum `k⃗` comes first. -/
theorem contDiff_packetMatrixElement (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    ContDiff ℝ ∞ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ kk.2 kk.1) := by
  have hk : ContDiff ℝ ∞ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) => oneParticleMomentum m kk.1) :=
    (contDiff_oneParticleMomentum hm).comp contDiff_fst
  have hk' : ContDiff ℝ ∞ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) => oneParticleMomentum m kk.2) :=
    (contDiff_oneParticleMomentum hm).comp contDiff_snd
  have hu := Dirac.contDiff_spinor_comp hm hk (fun kk => oneParticleMomentum_pos hm kk.1) 0
  have hw := Dirac.contDiff_bar_comp
    (Dirac.contDiff_spinor_comp hm hk' (fun kk => oneParticleMomentum_pos hm kk.2) 0)
  have hA := Dirac.contDiff_ofReal_comp (contDiff_formFactorA_oneParticleMomentum e hm hmγ hΛ)
  have hB := Dirac.contDiff_ofReal_comp (contDiff_formFactorB_oneParticleMomentum e hm hmγ hΛ)
  have hc : ∀ ν, ContDiff ℝ ∞ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      ((Minkowski.lower (oneParticleMomentum m kk.2 - oneParticleMomentum m kk.1) ν : ℝ) : ℂ)) :=
    fun ν => Dirac.contDiff_ofReal_comp
      (Dirac.contDiff_lower_comp (contDiff_oneParticleMomentum_sub hm) ν)
  simp only [packetMatrixElement_eq]
  refine Dirac.contDiff_dotProduct_mulVec hw hu fun i j => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.sum_apply,
    smul_eq_mul]
  exact contDiff_const.add (contDiff_const.mul ((hA.mul contDiff_const).sub
    ((contDiff_const.mul hB).mul (ContDiff.sum fun ν _ => (hc ν).mul contDiff_const))))

/-- **Smoothness of the packet weight.** For `m > 0` and a `C^∞` profile `φ`, the packet weight
`w(k) = φ(|k⃗|²/λ²) / ((2π)³ 2ω)` is `C^∞`. -/
theorem contDiff_packetWeight {m : ℝ} (hm : 0 < m) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (lam : ℝ) :
    ContDiff ℝ ∞ (packetWeight m φ lam) := by
  have h0 : ContDiff ℝ ∞ (fun k => oneParticleMomentum m k 0) :=
    contDiff_pi.1 (contDiff_oneParticleMomentum hm) 0
  have hr : ContDiff ℝ ∞ (fun k : Fin 3 → ℝ => (∑ j, k j ^ 2) / lam ^ 2) :=
    contDiff_sum_sq.div_const _
  unfold packetWeight
  refine (hφ.comp hr).div (contDiff_const.mul (contDiff_const.mul h0)) fun k => ?_
  have := oneParticleMomentum_pos hm k
  positivity

/-- **Smoothness of the packet amplitude.** At fixed regulators `m, m_γ, Λ > 0` and for a `C^∞`
profile `φ`, the packet amplitude `F(k, k')` is `C^∞` in `(k⃗, k⃗')` jointly. -/
theorem contDiff_packetAmplitude (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (lam : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (packetAmplitude e Z₁ m mγ Λ hm hmγ hΛ φ lam)) := by
  have hw := contDiff_packetWeight hm hφ lam
  exact (Dirac.contDiff_ofReal_comp ((hw.comp contDiff_snd).mul (hw.comp contDiff_fst))).mul
    (contDiff_packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ)

/-- If the profile `φ` has compact support and `λ ≠ 0`, then the packet weight vanishes outside
a ball. -/
theorem exists_norm_le_of_packetWeight_ne_zero {m : ℝ} {φ : ℝ → ℝ} (hφc : HasCompactSupport φ)
    {lam : ℝ} (hlam : lam ≠ 0) :
    ∃ r, ∀ k : Fin 3 → ℝ, packetWeight m φ lam k ≠ 0 → ‖k‖ ≤ r := by
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  refine ⟨Real.sqrt (R * lam ^ 2), fun k hk => ?_⟩
  have hφk : φ ((∑ j, k j ^ 2) / lam ^ 2) ≠ 0 := by
    intro h
    apply hk
    simp [packetWeight, h]
  have hmem := hR (subset_tsupport φ (Function.mem_support.2 hφk))
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
  have hsum : ∑ j, k j ^ 2 ≤ R * lam ^ 2 := by
    have hl2 : 0 < lam ^ 2 := by positivity
    have := (le_abs_self _).trans hmem
    rwa [div_le_iff₀ hl2] at this
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt
    ((Finset.single_le_sum (fun i _ => sq_nonneg (k i)) (Finset.mem_univ j)).trans hsum)

/-- **Compact support of the packet amplitude.** If the profile `φ` has compact support and
`λ ≠ 0`, then the packet amplitude `F(k, k')` has compact support in `(k⃗, k⃗')`. -/
theorem hasCompactSupport_packetAmplitude (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) {φ : ℝ → ℝ} (hφc : HasCompactSupport φ) {lam : ℝ} (hlam : lam ≠ 0) :
    HasCompactSupport (Function.uncurry (packetAmplitude e Z₁ m mγ Λ hm hmγ hΛ φ lam)) := by
  obtain ⟨r, hr⟩ := exists_norm_le_of_packetWeight_ne_zero (m := m) hφc hlam
  refine HasCompactSupport.intro (isCompact_closedBall (0 : (Fin 3 → ℝ) × (Fin 3 → ℝ)) r)
    fun kk hkk => ?_
  by_contra hne
  apply hkk
  have h1 : packetWeight m φ lam kk.2 * packetWeight m φ lam kk.1 ≠ 0 := by
    intro h
    apply hne
    simp [Function.uncurry, packetAmplitude, h]
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  exact max_le (hr _ (right_ne_zero_of_mul h1)) (hr _ (left_ne_zero_of_mul h1))

end QED.OneLoop

end
