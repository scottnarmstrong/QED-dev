/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.LszLimitOffShell
public import QED.Frozen.OneLoop.VertexFunction
public import QED.Frozen.WickModel.VacuumPolarization
public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Algebra.OnShell
import QED.OneLoop.VertexOffShellSpec
import QED.WickModel.LszLegs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The LSZ amplitude at the mass shell

Near on-shell positive-energy momenta `(p', p)`, the limit `ε → 0⁺` of
`(1/i) ū_{s'}(p') G^μ_ε(r', r) u_s(p)` at off-shell `(r', r)`
(`QED.WickModel.LszLimit.tendsto_sandwich_connectedFunction_offShell`) is the sum of

* the vertex `(1/i) ū [i (1 + δ₁) e γ^μ + V(r', r)] u`, with `V` the off-shell limit of the
  one-loop vertex integral
  (`QED.OneLoop.VertexOffShell.exists_tendsto_vertexIntegral_offShell_spec`), continuous at
  `(p', p)` with value `i V^μ_{1 loop}(p', p)`;
* the incoming leg `e ū γ^μ S̃₀(r) Σ(r) u`, which tends to `0`
  (`QED.WickModel.tendsto_electronLeg_in_spinor_of_isElectronOnShell`);
* the outgoing leg `e ū Σ(r') S̃₀(r') γ^μ u`, which tends to `0`
  (`QED.WickModel.tendsto_electronLeg_out_spinor_of_isElectronOnShell`);
* the photon leg, which tends to `e q² [1/(q² + m_γ²) - 1/(q² + Λ²)] Π(q²) ū γ^μ u`,
  `q = p' - p` (`QED.WickModel.tendsto_photonLegLimit_sandwich`).

So as `(r', r) → (p', p)` through off-shell momenta it tends to `LszLimit.closedForm`, the vertex
function (J) with `Z₁ = 1 + δ₁` between the spinors plus the photon-leg term.

## Main definitions

* `QED.WickModel.LszLimit.closedForm`: the value of the LSZ limit.

## Main statements

* `QED.WickModel.LszLimit.exists_tendsto_offShell`: a function `G` of the off-shell momenta that
  is the limit `ε → 0⁺` near `(p', p)` and tends to `LszLimit.closedForm` at the shell.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex Filter Topology Set

namespace QED.WickModel

/-- **The value of the LSZ limit**: `ū_{s'}(p') V^μ(p', p) u_s(p)`, with `V^μ` the vertex
function (J) at `Z₁ = 1 + δ₁`, plus the photon-leg term
`e q² [1/(q² + m_γ²) - 1/(q² + Λ²)] Π(q²) ū_{s'}(p') γ^μ u_s(p)`, `q = p' - p`, with `Π` the sealed
vacuum polarization (Z₇). -/
noncomputable def LszLimit.closedForm (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (p' p : Fin 4 → ℝ)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (s' s : Fin 2) (μ : Fin 4) : ℂ :=
  Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
      (QED.OneLoop.vertexFunction P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ
        *ᵥ Dirac.spinor P.m p s)
    + (P.e : ℂ) * ((Minkowski.dot (p' - p) (p' - p) *
        ((Minkowski.dot (p' - p) (p' - p) + P.mγ ^ 2)⁻¹
          - (Minkowski.dot (p' - p) (p' - p) + P.Λ ^ 2)⁻¹) : ℝ) : ℂ)
      * vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂ ⟨Minkowski.dot (p' - p) (p' - p),
          lt_of_lt_of_le (neg_lt_zero.mpr (mul_pos four_pos (pow_pos hm 2)))
            (Minkowski.dot_sub_self_nonneg_of_onShell hp' hp hp0' hp0)⟩
      * (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ (Dirac.gamma μ *ᵥ Dirac.spinor P.m p s))

/-! ### Splitting the off-shell limit -/

/-- The off-shell limit as a sum of four matrices. -/
theorem LszLimit.of_offShellLimit (P : Params) (V : Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4)
    (r' r : Fin 4 → ℝ) :
    Matrix.of (LszLimit.offShellLimit P V μ r' r) =
      ((I * (((1 + P.δ₁) * P.e : ℝ) : ℂ)) • Dirac.gamma μ + V)
      + ((I * P.e) • Dirac.gamma μ * ((1 / I) • QED.OneLoop.electronPropagator P.m 0 r)) *
          (I • LszLimit.selfEnergyMatrix P r)
      + (I • LszLimit.selfEnergyMatrix P r') *
          (((1 / I) • QED.OneLoop.electronPropagator P.m 0 r') * (I * P.e) • Dirac.gamma μ)
      + Matrix.of (photonLegLimit P (r' - r) μ) := by
  ext α β
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [LszLimit.offShellLimit, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]

/-- The incoming leg between two spinors. -/
theorem LszLimit.sandwich_legIn (e : ℝ) (G S Sig : Matrix (Fin 4) (Fin 4) ℂ)
    (w u : Fin 4 → ℂ) :
    (1 / I) * (w ⬝ᵥ ((((I * e) • G * ((1 / I) • S)) * (I • Sig)) *ᵥ u)) =
      e * (w ⬝ᵥ (G *ᵥ ((S * Sig) *ᵥ u))) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
  field_simp

/-- The outgoing leg between two spinors. -/
theorem LszLimit.sandwich_legOut (e : ℝ) (G S Sig : Matrix (Fin 4) (Fin 4) ℂ)
    (w u : Fin 4 → ℂ) :
    (1 / I) * (w ⬝ᵥ (((I • Sig) * (((1 / I) • S) * (I * e) • G)) *ᵥ u)) =
      e * ((w ᵥ* (Sig * S)) ⬝ᵥ (G *ᵥ u)) := by
  rw [← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, ← Matrix.mulVec_mulVec]
  field_simp

/-- **The off-shell limit between two spinors, split.** -/
theorem LszLimit.sandwich_offShellLimit (P : Params) (V : Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4)
    (r' r : Fin 4 → ℝ) (w u : Fin 4 → ℂ) :
    (1 / I) * (w ⬝ᵥ (Matrix.of (LszLimit.offShellLimit P V μ r' r) *ᵥ u)) =
      (1 / I) * (w ⬝ᵥ (((I * (((1 + P.δ₁) * P.e : ℝ) : ℂ)) • Dirac.gamma μ + V) *ᵥ u))
      + P.e * (w ⬝ᵥ (Dirac.gamma μ *ᵥ ((QED.OneLoop.electronPropagator P.m 0 r *
          LszLimit.selfEnergyMatrix P r) *ᵥ u)))
      + P.e * ((w ᵥ* (LszLimit.selfEnergyMatrix P r' * QED.OneLoop.electronPropagator P.m 0 r'))
          ⬝ᵥ (Dirac.gamma μ *ᵥ u))
      + (1 / I) * (w ⬝ᵥ (Matrix.of (photonLegLimit P (r' - r) μ) *ᵥ u)) := by
  rw [LszLimit.of_offShellLimit, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec,
    dotProduct_add, dotProduct_add, dotProduct_add, mul_add, mul_add, mul_add,
    LszLimit.sandwich_legIn, LszLimit.sandwich_legOut]

/-! ### The limits of the four pieces at the shell -/

/-- Entrywise limits of matrices pass to the sandwich `(1/i) w M u`. -/
theorem LszLimit.tendsto_sandwich_matrix {ι : Type*} {l : Filter ι}
    {F : ι → Matrix (Fin 4) (Fin 4) ℂ} {G : Matrix (Fin 4) (Fin 4) ℂ}
    (h : ∀ α β, Tendsto (fun i => F i α β) l (𝓝 (G α β))) (w u : Fin 4 → ℂ) :
    Tendsto (fun i => (1 / I) * (w ⬝ᵥ (F i *ᵥ u))) l (𝓝 ((1 / I) * (w ⬝ᵥ (G *ᵥ u)))) := by
  simp only [dotProduct, Matrix.mulVec]
  exact (tendsto_finsetSum _ fun α _ => (tendsto_finsetSum _ fun β _ =>
    (h α β).mul_const (u β)).const_mul (w α)).const_mul _

/-- The vertex value: `(1/i) ū [i Z₁ e γ^μ + i V^μ_{1 loop}] u = ū V^μ u` with `V^μ` the vertex
function (J). -/
theorem LszLimit.sandwich_vertex (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ : Fin 4) (w u : Fin 4 → ℂ) :
    (1 / I) * (w ⬝ᵥ (((I * (((1 + P.δ₁) * P.e : ℝ) : ℂ)) • Dirac.gamma μ + Matrix.of
        (fun i j => I * QED.OneLoop.vertexOneLoop P.e P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0'
          hp0 μ i j)) *ᵥ u)) =
      w ⬝ᵥ (QED.OneLoop.vertexFunction P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0'
        hp0 μ *ᵥ u) := by
  have h : ((I * (((1 + P.δ₁) * P.e : ℝ) : ℂ)) • Dirac.gamma μ + Matrix.of
      (fun i j => I * QED.OneLoop.vertexOneLoop P.e P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0'
        hp0 μ i j)) =
      I • QED.OneLoop.vertexFunction P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0'
        hp0 μ := by
    ext i j
    simp only [QED.OneLoop.vertexFunction, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul]
    ring
  rw [h, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← mul_assoc, one_div,
    inv_mul_cancel₀ I_ne_zero, one_mul]

/-- The off-shell pairs near `(p', p)`. -/
abbrev LszLimit.offShellPairs (m : ℝ) : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ)) :=
  {x | Minkowski.dot x.1 x.1 ≠ -m ^ 2 ∧ Minkowski.dot x.2 x.2 ≠ -m ^ 2}

/-- Through off-shell pairs, the outgoing momentum approaches `p'` through off-shell momenta. -/
theorem LszLimit.tendsto_fst_offShell (m : ℝ) (p' p : Fin 4 → ℝ) :
    Tendsto Prod.fst (𝓝[LszLimit.offShellPairs m] (p', p))
      (𝓝[{r' | Minkowski.dot r' r' ≠ -m ^ 2}] p') :=
  tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto (p', p)).mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun _ hx => hx.1⟩

/-- Through off-shell pairs, the incoming momentum approaches `p` through off-shell momenta. -/
theorem LszLimit.tendsto_snd_offShell (m : ℝ) (p' p : Fin 4 → ℝ) :
    Tendsto Prod.snd (𝓝[LszLimit.offShellPairs m] (p', p))
      (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p) :=
  tendsto_nhdsWithin_iff.2 ⟨(continuous_snd.tendsto (p', p)).mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun _ hx => hx.2⟩

/-- **The incoming leg vanishes at the shell**: `e ū γ^μ S̃₀(r) Σ(r) u → 0`. -/
theorem LszLimit.tendsto_legIn_shell (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hon : IsElectronOnShell P hm hmγ hΛ) {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (p' : Fin 4 → ℝ) (s : Fin 2) (μ : Fin 4) (w : Fin 4 → ℂ) :
    Tendsto (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => (P.e : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ
        ((QED.OneLoop.electronPropagator P.m 0 x.2 * LszLimit.selfEnergyMatrix P x.2) *ᵥ
          Dirac.spinor P.m p s))))
      (𝓝[LszLimit.offShellPairs P.m] (p', p)) (𝓝 0) := by
  have h := (tendsto_electronLeg_in_spinor_of_isElectronOnShell P hm hmγ hΛ hon hp s).comp
    (LszLimit.tendsto_snd_offShell P.m p' p)
  have hc : Continuous fun v : Fin 4 → ℂ => (P.e : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ v)) :=
    continuous_const.mul (continuous_const.dotProduct
      (continuous_const.matrix_mulVec continuous_id))
  have h' := (hc.tendsto 0).comp h
  rw [Matrix.mulVec_zero, dotProduct_zero, mul_zero] at h'
  exact h'

/-- **The outgoing leg vanishes at the shell**: `e ū Σ(r') S̃₀(r') γ^μ u → 0`. -/
theorem LszLimit.tendsto_legOut_shell (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hon : IsElectronOnShell P hm hmγ hΛ) {p' : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (p : Fin 4 → ℝ) (s' : Fin 2) (μ : Fin 4)
    (u : Fin 4 → ℂ) :
    Tendsto (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => (P.e : ℂ) *
        ((Dirac.bar (Dirac.spinor P.m p' s') ᵥ* (LszLimit.selfEnergyMatrix P x.1 *
          QED.OneLoop.electronPropagator P.m 0 x.1)) ⬝ᵥ (Dirac.gamma μ *ᵥ u)))
      (𝓝[LszLimit.offShellPairs P.m] (p', p)) (𝓝 0) := by
  have h := (tendsto_electronLeg_out_spinor_of_isElectronOnShell P hm hmγ hΛ hon hp' s').comp
    (LszLimit.tendsto_fst_offShell P.m p' p)
  have hc : Continuous fun v : Fin 4 → ℂ => (P.e : ℂ) * (v ⬝ᵥ (Dirac.gamma μ *ᵥ u)) :=
    continuous_const.mul (continuous_id.dotProduct continuous_const)
  have h' := (hc.tendsto 0).comp h
  rw [zero_dotProduct, mul_zero] at h'
  exact h'

/-- **The vertex at the shell.** If the entries of `V` are continuous at `(p', p)` with values
`i V^μ_{1 loop}(p', p)`, then `(1/i) w [i (1 + δ₁) e γ^μ + V(r', r)] u` tends to `w V^μ u`, with
`V^μ` the vertex function (J) at `Z₁ = 1 + δ₁`. -/
theorem LszLimit.tendsto_vertex_shell (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ : Fin 4)
    {V : Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℂ}
    (hcont : ∀ i j, ContinuousAt (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => V i j x.1 x.2) (p', p))
    (hval : ∀ i j, V i j p' p =
      I * QED.OneLoop.vertexOneLoop P.e P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ i j)
    (w u : Fin 4 → ℂ) :
    Tendsto (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => (1 / I) * (w ⬝ᵥ
        (((I * (((1 + P.δ₁) * P.e : ℝ) : ℂ)) • Dirac.gamma μ +
          Matrix.of (fun i j => V i j x.1 x.2)) *ᵥ u)))
      (𝓝 (p', p))
      (𝓝 (w ⬝ᵥ (QED.OneLoop.vertexFunction P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp
        hp0' hp0 μ *ᵥ u))) := by
  rw [← LszLimit.sandwich_vertex P hm hmγ hΛ hp' hp hp0' hp0 μ w u]
  refine LszLimit.tendsto_sandwich_matrix (fun α β => ?_) w u
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply]
  rw [← hval α β]
  exact tendsto_const_nhds.add (hcont α β).tendsto

/-- Near an on-shell `p`, the momenta lie in the domain of (Z₃′). -/
theorem LszLimit.eventually_selfEnergy_domain {m mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2) (hm : 0 < m) :
    ∀ᶠ r in 𝓝 p, -(m + min mγ Λ) ^ 2 < Minkowski.dot r r := by
  have hlt : -(m + min mγ Λ) ^ 2 < Minkowski.dot p p := by
    have h := lt_min hmγ hΛ
    rw [hp]
    nlinarith
  exact (LszLegs.continuous_dot_self.tendsto p).eventually (lt_mem_nhds hlt)

/-! ### The limit at the shell -/

/-- **The LSZ limit through off-shell momenta.** For `m, m_γ, Λ > 0`, regulator fermions as in
(Z₂), counterterms on shell (Z₅), on-shell positive-energy momenta `(p', p)`, spins `s'`, `s` and
an index `μ`, there is a function `G` of the momenta such that, for all off-shell `(r', r)` near
`(p', p)`, `(1/i) ū_{s'}(p') G^μ_ε(r', r) u_s(p) → G(r', r)` as `ε → 0⁺`, and `G(r', r)` tends
to `LszLimit.closedForm` as `(r', r) → (p', p)` through off-shell pairs. -/
theorem LszLimit.exists_tendsto_offShell (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (s' s : Fin 2) (μ : Fin 4) :
    ∃ G : (Fin 4 → ℝ) × (Fin 4 → ℝ) → ℂ,
      (∀ᶠ x : (Fin 4 → ℝ) × (Fin 4 → ℝ) in 𝓝 (p', p),
        Minkowski.dot x.1 x.1 ≠ -P.m ^ 2 → Minkowski.dot x.2 x.2 ≠ -P.m ^ 2 →
        Tendsto (fun ε : ℝ => (1 / I) *
            (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
              (Matrix.of (fun α β => connectedFunction { P with ε := ε } 1 1 3 ![x.1] ![x.2]
                ![x.1 - x.2] ![α] ![β] ![μ]) *ᵥ Dirac.spinor P.m p s)))
          (𝓝[>] 0) (𝓝 (G x))) ∧
      Tendsto G (𝓝[LszLimit.offShellPairs P.m] (p', p))
        (𝓝 (LszLimit.closedForm P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ p' p hp' hp hp0' hp0 s' s μ)) := by
  set w := Dirac.bar (Dirac.spinor P.m p' s') with hw
  set u := Dirac.spinor P.m p s with hu
  choose δ hδ V hV hcont hval using fun i j =>
    QED.OneLoop.VertexOffShell.exists_tendsto_vertexIntegral_offShell_spec (e := P.e) hm hmγ hΛ
      hp' hp hp0' hp0 μ i j
  refine ⟨fun x => (1 / I) * (w ⬝ᵥ (Matrix.of (LszLimit.offShellLimit P
    (Matrix.of fun i j => V i j x.1 x.2) μ x.1 x.2) *ᵥ u)), ?_, ?_⟩
  · have hVx : ∀ᶠ x : (Fin 4 → ℝ) × (Fin 4 → ℝ) in 𝓝 (p', p), ∀ i j,
        Tendsto (fun ε : ℝ => QED.OneLoop.energyFirstIntegral fun ℓ =>
          QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ ε x.1 x.2 μ ℓ i j)
          (𝓝[>] 0) (𝓝 (V i j x.1 x.2)) := by
      refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
      refine Metric.eventually_nhds_iff.2 ⟨δ i j, hδ i j, fun x hx => ?_⟩
      rw [Prod.dist_eq] at hx
      exact (hV i j x.1 x.2 (lt_of_le_of_lt (le_max_left _ _) hx)
        (lt_of_le_of_lt (le_max_right _ _) hx)).2
    have hd := (LszLimit.eventually_selfEnergy_domain hmγ hΛ hp' hm).prod_nhds
      (LszLimit.eventually_selfEnergy_domain hmγ hΛ hp hm)
    filter_upwards [hVx, hd, eventually_photonLeg_domain hm hmγ hΛ hp' hp hp0' hp0]
      with x hVx' hdx hqx hx1 hx2
    exact LszLimit.tendsto_sandwich_connectedFunction_offShell P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂
      hx1 hx2 hdx.1 hdx.2 hqx.1 hqx.2.1 hqx.2.2 μ hVx' w u
  · simp only [LszLimit.sandwich_offShellLimit]
    have h1 := (LszLimit.tendsto_vertex_shell P hm hmγ hΛ hp' hp hp0' hp0 μ hcont hval w
      u).mono_left (nhdsWithin_le_nhds (s := LszLimit.offShellPairs P.m))
    have h2 := LszLimit.tendsto_legIn_shell P hm hmγ hΛ hon hp p' s μ w
    have h3 := LszLimit.tendsto_legOut_shell P hm hmγ hΛ hon hp' p s' μ u
    have h4 := (tendsto_photonLegLimit_sandwich P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hp' hp hp0' hp0
      s' s μ).mono_left (nhdsWithin_le_nhds (s := LszLimit.offShellPairs P.m))
    convert ((h1.add h2).add h3).add h4 using 2
    rw [LszLimit.closedForm]
    push_cast
    ring

end QED.WickModel

end
