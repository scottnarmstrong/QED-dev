/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ParametricBridgeC
public import QED.TwoLoop.NestedVPAmplitude

/-!
# The vacuum-polarization class in parametric form: routing and the flavour sum

Part of obligations O2-7 and O2-10 (`docs/TWO-LOOP-DERIVATION.md`, sections 4.1–4.4) for the
class `VP` of five gauge vertices (`QED.TwoLoop.Enumeration.Class5.VP`). Its representative
(`QED.TwoLoop.NestedVP.cV`) has the open line `0 → 1 → 2` (external photon at `1`), the closed
loop `3 → 4 → 3` and the photons `(0 3)`, `(2 4)`; the chords (T₁) are `v₀v₁` (`ℓ 0`) and `v₄v₃`
(`ℓ 1`).

**The class routing** (`classMomVP`): the loop matrix `class5LoopMatrix .VP` and the external
momenta `classVPMomenta p p'`, in the line order `v₀v₁, v₁v₂, v₃v₄, v₄v₃`, photons `(v₀v₃)`,
`(v₂v₄)` (`lineIdxVP`). It is conserved (`isConserved_classMomVP`), and the frozen routing is the
class routing at `matVP ℓ + (0, -p)` with `matVP` integer unimodular (`lineMomentum₂_cV_class`);
the frozen loop matrix is `class5LoopMatrix .VP * matVP` (`frozenLoopMatrixVP_eq`,
kernel-checked). In the nested variables of `QED/TwoLoop/NestedVPRouting.lean` the class routing
at `λ` is `nestedMom p k_ext (λ 0) (-λ 1)` (`classMomVP_eq_nestedMom`).

**The numerator** (`vpNumer`): the amplitude of loop flavour `f` with every propagator replaced by
its numerator, `(i e)⁵ (1/i)⁶ ∑ (γ^ν (m - p̸₁₂) γ^μ (m - p̸₀₁) γ^ρ)_{αβ} g_{ρσ}(Λ² - m_γ²)
g_{ντ}(Λ² - m_γ²) Tr[γ^σ (M - q̸) γ^τ (M - (q + k)̸)]`, as a function of the loop mass `M`.
`contractionAmplitude₂_flavV_eq` writes the amplitude (T₇) of flavour `f` as `vpNumer` at
`M = M_f` times the inverse line denominators, for `ε ≠ 0`.

**The value as a flavour sum** (`contractionValue₂_VP_eq_flavourSum`): for `ε ≠ 0` and under
momentum conservation the value (T₁₀) is the joint energy-first integral of
`(2π)⁻⁸ ∑_f c_f N_f(λ) ∏ᵢ₌₀⁷ D_{f,i}(λ)⁻¹` with the eight Pauli–Villars line denominators of loop
mass `M_f` (`pvDenomVP f`, loop matrix `class5LoopMatrixPV .VP`). For a single flavour that loop
matrix violates the no-subdivergence criterion (`not_noSubdivergence_loopMatrixPV_VP`: the bubble
has two lines); the flavour sum is turned into the doubled-bubble form in
`QED/TwoLoop/ParametricBridgeVPFlavour.lean`.
-/

@[expose] public section

namespace QED.TwoLoop.Bridge

open Complex QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Routing QED.TwoLoop.Relabel
open QED.TwoLoop.NestedVP (cV lineV photV flavV nestedMom)
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrix
  class5LoopMatrixPV classVPMomenta classVPPVMasses pvLines IntNoSubdivergence NoSubdivergence)

/-! ### The class routing -/

/-- The index of a line of the `VP` representative in the line order of `class5LoopMatrix .VP`,
read off its label (X₂₀): fermion lines by head (`v₀v₁` label `1`, `v₁v₂` label `2`, `v₄v₃`
label `3`, `v₃v₄` label `4`), photon lines `0 → 3` (label `5`) and `2 → 4` (label `9`). -/
def lineIdxVP (f : Line cV) : Fin 6 :=
  match f.label with
  | 1 => 0
  | 2 => 1
  | 3 => 3
  | 4 => 2
  | 5 => 4
  | _ => 5

/-- The routing of the `VP` representative by the class loop matrix `class5LoopMatrix .VP` and
the external momenta `classVPMomenta p p'`, at loop momenta `ℓ`. -/
def classMomVP (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line cV) : Fin 4 → ℝ :=
  lineMomentum (castLoopMatrix (class5LoopMatrix .VP)) (classVPMomenta p p') (lineIdxVP f) ℓ

theorem lineIdxVP_lines : lineIdxVP (.inl (lineV 0)) = 0 ∧ lineIdxVP (.inl (lineV 1)) = 1 ∧
    lineIdxVP (.inl (lineV 2)) = 3 ∧ lineIdxVP (.inl (lineV 3)) = 2 ∧
    lineIdxVP (.inr (photV 0)) = 4 ∧ lineIdxVP (.inr (photV 1)) = 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The class routing of `VP` is conserved at every vertex, under momentum conservation. -/
theorem isConserved_classMomVP {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsConserved cV pOut pIn kIn (classMomVP (pIn 0) (pOut 0) ℓ) := by
  obtain ⟨e0, e1, e2, e3⟩ := QED.TwoLoop.NestedVP.ends_lineV
  obtain ⟨g0, g1⟩ := QED.TwoLoop.NestedVP.ends_photV
  obtain ⟨i0, i1, i2, i3, i4, i5⟩ := lineIdxVP_lines
  intro v
  rw [inflow, QED.TwoLoop.NestedVP.sum_line, QED.TwoLoop.NestedVP.externalMomentum_cV, hmom]
  simp only [classMomVP, e0, e1, e2, e3, g0, g1, i0, i1, i2, i3, i4, i5]
  funext μ
  fin_cases v <;>
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, classVPMomenta, Fin.sum_univ_two]
  ring

/-- The unimodular change of loop momenta from the frozen routing of `VP` to its class routing. -/
def matVP : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

theorem isUnit_det_matVP : IsUnit matVP.det := by
  rw [Matrix.det_fin_two]
  simp [matVP]

/-- The class loop momenta of `VP` in terms of the frozen ones: `(ℓ₁, ℓ₀ - p)`. -/
def chgVP (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 2 → Fin 4 → ℝ :=
  (fun s => ∑ r, matVP s r • ℓ r) + ![0, -p]

/-- **The frozen routing of `VP` is the class routing** at the loop momenta `chgVP p ℓ`, under
momentum conservation. -/
theorem lineMomentum₂_cV_class {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ cV pOut pIn kIn ℓ = classMomVP (pIn 0) (pOut 0) (chgVP (pIn 0) ℓ) := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved (isConserved_classMomVP hmom _) (fun g hg => ?_) f).symm
  obtain ⟨c0, c1⟩ := QED.TwoLoop.NestedVP.chordMomentum_lineV ℓ
  obtain ⟨i0, -, i2, -⟩ := lineIdxVP_lines
  rcases (QED.TwoLoop.NestedVP.isChord_cV_iff g).mp hg with rfl | rfl
  · rw [c0, classMomVP, i0]
    funext μ
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, classVPMomenta, chgVP, matVP,
      Fin.sum_univ_two]
  · rw [c1, classMomVP, i2]
    funext μ
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, classVPMomenta, chgVP, matVP,
      Fin.sum_univ_two]

/-- The loop matrix of the frozen routing of `VP` (rows `v₀v₁, v₁v₂, v₃v₄, v₄v₃`, photons
`0 → 3`, `2 → 4`; columns the chord momenta `ℓ₀`, `ℓ₁`). -/
def frozenLoopMatrixVP : Fin 6 → Fin 2 → ℤ :=
  ![![1, 0], ![1, 0], ![-1, 1], ![0, 1], ![-1, 0], ![1, 0]]

/-- The external momenta of the frozen routing of `VP`. -/
def frozenMomentaVP (p k : Fin 4 → ℝ) : Fin 6 → Fin 4 → ℝ := ![0, k, p, 0, p, -p]

theorem frozenLoopMatrixVP_eq :
    frozenLoopMatrixVP = fun i s => ∑ r, class5LoopMatrix .VP i r * matVP r s := by
  decide

/-- **The frozen routing of `VP` with its loop matrix**: `k_f(ℓ) = ∑ₛ αᵢₛ ℓₛ + pᵢ` with
`α = frozenLoopMatrixVP`, `i = lineIdxVP f`. -/
theorem lineMomentum₂_cV_eq_frozen {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line cV) :
    lineMomentum₂ cV pOut pIn kIn ℓ f =
      lineMomentum (castLoopMatrix frozenLoopMatrixVP) (frozenMomentaVP (pIn 0) (kIn 0))
        (lineIdxVP f) ℓ := by
  rw [lineMomentum₂_cV_class hmom, classMomVP, hmom]
  generalize lineIdxVP f = i
  funext μ
  fin_cases i <;>
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, classVPMomenta, chgVP, matVP,
      frozenLoopMatrixVP, frozenMomentaVP, Fin.sum_univ_two] <;>
    ring

/-- The frozen loop matrix of `VP` violates the no-subdivergence criterion, with one denominator
per line and with the photon lines doubled (the bubble). -/
theorem not_intNoSubdivergence_frozenLoopMatrixVP :
    ¬ IntNoSubdivergence frozenLoopMatrixVP ∧
      ¬ IntNoSubdivergence fun i => frozenLoopMatrixVP (pvLines i) := by
  decide

/-- **The class routing in the nested variables**: at `λ` it is the nested routing with loop
momentum `q = λ 0` and photon momentum `k = -λ 1`. -/
theorem classMomVP_eq_nestedMom (p kext : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    classMomVP p (p + kext) ℓ = nestedMom p kext (ℓ 0) (-ℓ 1) := by
  have h := lineMomentum₂_cV_class (pOut := ![p + kext]) (pIn := ![p]) (kIn := ![kext]) rfl
    ![ℓ 1 + p, ℓ 0]
  have h' := QED.TwoLoop.NestedVP.lineMomentum₂_cV (pOut := ![p + kext]) (pIn := ![p])
    (kIn := ![kext]) rfl ![ℓ 1 + p, ℓ 0]
  have hc : chgVP p ![ℓ 1 + p, ℓ 0] = ℓ := by
    funext s μ
    fin_cases s <;> simp [chgVP, matVP, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hc] at h h'
  rw [← h, h']
  congr 1
  funext μ
  simp

/-! ### The numerator -/

/-- The open-line numerator `γ^ν (m - (p + k_ext - k)̸) γ^μ (m - (p - k)̸) γ^ρ`. -/
noncomputable def outerNum (P : Params) (p kext k : Fin 4 → ℝ) (μ ρ ν : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Dirac.gamma ν * electronNumerator P.m (p + kext - k) * Dirac.gamma μ *
    electronNumerator P.m (p - k) * Dirac.gamma ρ

/-- The loop numerator `Tr[γ^σ (M - q̸) γ^τ (M - (q + k)̸)]` of loop mass `M`. -/
noncomputable def loopTrace (M : ℝ) (q k : Fin 4 → ℝ) (σ τ : Fin 4) : ℂ :=
  Matrix.trace (Dirac.gamma σ * electronNumerator M q * Dirac.gamma τ *
    electronNumerator M (q + k))

/-- **The numerator of `VP`** for loop mass `M`, open-line momentum `p`, external photon momentum
`k_ext`, loop momentum `q` and photon momentum `k`, at the external indices `α, β, μ`. -/
noncomputable def vpNumer (P : Params) (M : ℝ) (p kext : Fin 4 → ℝ) (α β μ : Fin 4)
    (q k : Fin 4 → ℝ) : ℂ :=
  (I * P.e) ^ 5 * (1 / I) ^ 6 * ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4, ∑ l4 : Fin 4,
    outerNum P p kext k μ l0 l2 α β *
      ((Minkowski.metric l0 l3 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ) *
      ((Minkowski.metric l2 l4 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ) * loopTrace M q k l3 l4

/-- The numerator of `VP` in the class loop momenta `λ` (`q = λ 0`, `k = -λ 1`). -/
noncomputable def vpNumerator (P : Params) (M : ℝ) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  vpNumer P M (pIn 0) (kIn 0) (αOut 0) (βIn 0) (μ 0) (ℓ 0) (-ℓ 1)

theorem electronPropagator_eq_smul (m ε : ℝ) (p : Fin 4 → ℝ) :
    QED.OneLoop.electronPropagator m ε p = (propDenom m ε p)⁻¹ • electronNumerator m p := by
  ext a b
  rw [electronPropagator_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

/-- **The amplitude of flavour `f` as numerator times denominators** (nested variables): for
`ε ≠ 0`, `vpNumer` at the loop mass `M_f` times the inverse denominators of the open line
(`p - k`, `p + k_ext - k`, mass `m`), of the photon pairs (`k`, `-k`, masses `m_γ`, `Λ`) and of the
loop (`q + k`, `q`, mass `M_f`). -/
theorem contractionAmplitude₂_flavV_eq (P : Params) (hε : P.ε ≠ 0) (f : Fin 3)
    (pIn kIn : Fin 1 → Fin 4 → ℝ) (q k : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P cV (flavV f) pIn kIn (nestedMom (pIn 0) (kIn 0) q k) αOut βIn μ =
      vpNumer P (P.mass f) (pIn 0) (kIn 0) (αOut 0) (βIn 0) (μ 0) q k *
        ((propDenom P.m P.ε (pIn 0 - k))⁻¹ * (propDenom P.m P.ε (pIn 0 + kIn 0 - k))⁻¹ *
          ((propDenom P.mγ P.ε k)⁻¹ * (propDenom P.Λ P.ε k)⁻¹) *
          ((propDenom P.mγ P.ε (-k))⁻¹ * (propDenom P.Λ P.ε (-k))⁻¹) *
          (propDenom (P.mass f) P.ε (q + k))⁻¹ * (propDenom (P.mass f) P.ε q)⁻¹) := by
  rw [QED.TwoLoop.NestedVP.contractionAmplitude₂_flavV]
  unfold vpNumer QED.TwoLoop.NestedVP.outerChain outerNum loopTrace
  simp only [electronPropagator_eq_smul, photonPropagator_eq_mul _ _ hε, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_apply, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-! ### The value as a flavour sum of Pauli–Villars forms -/

/-- The Pauli–Villars line denominators of `VP` with loop flavour `f`: loop matrix
`class5LoopMatrixPV .VP`, momenta `classVPMomenta`, masses `m` (open line), `M_f` (loop), `m_γ`
(lines `4, 5`) and `Λ` (lines `6, 7`). -/
noncomputable def pvDenomVP (P : Params) (f : Fin 3) (p p' : Fin 4 → ℝ) (i : Fin 8)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  lineDenom (castLoopMatrix (class5LoopMatrixPV .VP)) (pvMomentaE .VP p p')
    (classVPPVMasses P.m (P.mass f) P.mγ P.mγ P.Λ P.Λ) P.ε i ℓ

/-- The eight line momenta of the Pauli–Villars form of `VP`, in the nested variables. -/
theorem lineMomentum_pvVP (p kext : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (castLoopMatrix (class5LoopMatrixPV .VP)) (pvMomentaE .VP p (p + kext)) 0 ℓ =
        p - -ℓ 1 ∧
      lineMomentum (castLoopMatrix (class5LoopMatrixPV .VP)) (pvMomentaE .VP p (p + kext)) 1 ℓ =
        p + kext - -ℓ 1 ∧
      lineMomentum (castLoopMatrix (class5LoopMatrixPV .VP)) (pvMomentaE .VP p (p + kext)) 2 ℓ =
        ℓ 0 + -ℓ 1 ∧
      lineMomentum (castLoopMatrix (class5LoopMatrixPV .VP)) (pvMomentaE .VP p (p + kext)) 3 ℓ =
        ℓ 0 ∧
      lineMomentum (castLoopMatrix (class5LoopMatrixPV .VP)) (pvMomentaE .VP p (p + kext)) 4 ℓ =
        -ℓ 1 ∧
      lineMomentum (castLoopMatrix (class5LoopMatrixPV .VP)) (pvMomentaE .VP p (p + kext)) 5 ℓ =
        - -ℓ 1 ∧
      lineMomentum (castLoopMatrix (class5LoopMatrixPV .VP)) (pvMomentaE .VP p (p + kext)) 6 ℓ =
        -ℓ 1 ∧
      lineMomentum (castLoopMatrix (class5LoopMatrixPV .VP)) (pvMomentaE .VP p (p + kext)) 7 ℓ =
        - -ℓ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext μ <;>
    simp [lineMomentum, castLoopMatrix, class5LoopMatrixPV, class5LoopMatrix, pvMomentaE,
      extMomenta, classVPMomenta, pvLines, Fin.sum_univ_two] <;>
    ring

/-- The amplitude of flavour `f` in the class routing: `vpNumerator` at `M_f` times the eight
Pauli–Villars line denominators of flavour `f`. -/
theorem contractionAmplitude₂_flavV_classMomVP (P : Params) (hε : P.ε ≠ 0) (f : Fin 3)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    contractionAmplitude₂ P cV (flavV f) pIn kIn (classMomVP (pIn 0) (pOut 0) ℓ) αOut βIn μ =
      vpNumerator P (P.mass f) pIn kIn αOut βIn μ ℓ *
        ∏ i : Fin 8, (pvDenomVP P f (pIn 0) (pOut 0) i ℓ)⁻¹ := by
  rw [hmom, classMomVP_eq_nestedMom, contractionAmplitude₂_flavV_eq P hε, vpNumerator]
  congr 1
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := lineMomentum_pvVP (pIn 0) (kIn 0) ℓ
  simp only [pvDenomVP, Fin.prod_univ_eight, lineDenom_eq_propDenom, h0, h1, h2, h3, h4, h5, h6,
    h7]
  simp [classVPPVMasses]
  ring

open scoped Classical in
/-- **The integrand of `VP` as a flavour sum**: for `ε ≠ 0`, the regulated amplitude (T₈) in the
class routing is `∑_f c_f N_f ∏ᵢ D_{f,i}⁻¹`. -/
theorem regulatedAmplitude₂_classMomVP (P : Params) (hε : P.ε ≠ 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    regulatedAmplitude₂ P cV pIn kIn (classMomVP (pIn 0) (pOut 0) ℓ) αOut βIn μ =
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) * (vpNumerator P (P.mass f) pIn kIn αOut βIn μ ℓ *
        ∏ i : Fin 8, (pvDenomVP P f (pIn 0) (pOut 0) i ℓ)⁻¹) := by
  rw [regulatedAmplitude₂, QED.TwoLoop.NestedVP.sum_preserves]
  simp only [QED.TwoLoop.NestedVP.loopWeight_flavV,
    contractionAmplitude₂_flavV_classMomVP P hε _ hmom]

/-- **The value of `VP` as a flavour sum of Pauli–Villars forms.** For `ε ≠ 0` and under momentum
conservation, the value (T₁₀) is the joint energy-first integral of
`(2π)⁻⁸ ∑_f c_f N_f(λ) ∏ᵢ₌₀⁷ D_{f,i}(λ)⁻¹` in the class loop momenta. No integrability is
needed. -/
theorem contractionValue₂_VP_eq_flavourSum (P : Params) (hε : P.ε ≠ 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.VP.rep pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ =>
        (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          ∑ f : Fin 3, (P.loopCoeff f : ℂ) * (vpNumerator P (P.mass f) pIn kIn αOut βIn μ ℓ *
            ∏ i : Fin 8, (pvDenomVP P f (pIn 0) (pOut 0) i ℓ)⁻¹) := by
  rw [contractionValue₂_eq_of_loopCount P (loopCount_rep .VP)]
  simp only [lineMomentum₂_cV_class hmom]
  have h := JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
    (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P cV pIn kIn (classMomVP (pIn 0) (pOut 0) ℓ) αOut βIn μ)
    matVP isUnit_det_matVP ![0, -(pIn 0)]
  refine h.trans ?_
  refine congrArg (QED.TwoLoop.jointEnergyFirstIntegral 2) (funext fun ℓ => ?_)
  rw [regulatedAmplitude₂_classMomVP P hε hmom]

end QED.TwoLoop.Bridge

end
