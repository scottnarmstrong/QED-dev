/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLimCtD
public import QED.ChainProof.SetCLimCtCDAmp
public import QED.ChainProof.SetCLimCtCDPiece
public import QED.ChainProof.SetCLinkIntDeg6
public import QED.TwoLoop.ClassLimitVP

/-!
# Set (c): limits and covariance of the four classes `CD0`, `CD1`

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The classes
`repCD0 s`, `repCD1 s` are the one-loop vertex with a level-`0` `fermionCt` vertex on its outgoing,
resp. incoming, internal electron line and a level-`0` `photonCt` vertex on the photon line. Their
value is the energy-first integral of the vertex chain with the inserted electron and photon lines
(`QED/ChainProof/SetCLimCtCDAmp.lean`), whose numerator has degree six. At `ε > 0` it splits into
three products with numerators of degree four (`QED/ChainProof/SetCLimCtCDNum.lean`), each
integrable; the third carries a factor `iε`. Each product has a limit, a parametric value divided by
`auxLimit m` (`QED/ChainProof/SetCLimCtCDPiece.lean`), so the class converges to the sum of the
limits of the first two (`isClassLimC_CDIn`, `isClassLimC_CDOut`), which is covariant.

* **`setCClassLim_CD01`**, **`setCClassCov_CD01`**: the limit and covariance links of the classes
  `.inr (.inl (k, s))` of `QED.ChainProof.SetCPauli.ctFam`, `k < 2`;
* **`setCLimitLink_of_main_cb`**, **`setCCovLink_of_main_cb`**: the limit and covariance links of
  (HS₆) from the per-class links of the 36 two-loop-outer classes and the five classes `CBₖ`.
-/

@[expose] public section

open Complex Matrix Filter Topology

namespace QED.ChainProof.SetCPauli

open QED.WickModel (Params contractionValue₂)
open QED.TwoLoop.Insertion QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit
open QED.TwoLoop.LimitCovariance QED.TwoLoop.ReflCovariance QED.Dirac QED.ChainProof.SetCLink
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### The values -/

/-- The value of `CD0 s` (`k = 0`) and `CD1 s` (`k = 1`) at the open-line parameters. -/
theorem cd01Val_apply (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (s : Fin 2) (i j : Fin 4) :
    cdVal P Φ D p' p μ s 0 i j = contractionValue₂ (ctParamsLevel P Φ D 0) (repCD0 s)
        (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) ∧
      cdVal P Φ D p' p μ s 1 i j = contractionValue₂ (ctParamsLevel P Φ D 0) (repCD1 s)
        (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) := by
  constructor
  · change Graded.contractionValue P Φ D (repCD0 s) (fun _ => 0) _ _ _ _ _ _ = _
    rw [contractionValue_eq_ctLevel P Φ D _ (SetCLinkDeg6.cycle_CD0 s)]
  · change Graded.contractionValue P Φ D (repCD1 s) (fun _ => 0) _ _ _ _ _ _ = _
    rw [contractionValue_eq_ctLevel P Φ D _ (SetCLinkDeg6.cycle_CD1 s)]

/-- The value of `CD1 s` is the energy-first integral of the vertex chain with the inserted
electron line on the incoming side. -/
theorem value_repCD1 (Q : Params) (s : Fin 2) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    contractionValue₂ Q (repCD1 s) (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
        (fun _ => j) (fun _ => μ) =
      QED.OneLoop.energyFirstIntegral fun k =>
        vertexChain Q.e μ (QED.OneLoop.electronPropagator Q.m Q.ε (p' + k))
          (electronInsertion Q.m Q.ε Q.δ₂ Q.δm (p + k)) (photonInsertion Q.δ₃ Q.mγ Q.Λ Q.ε k)
          i j := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  fin_cases s
  · exact contractionValue₂_repCD1a Q hmom _ _ _
  · exact contractionValue₂_repCD1b Q hmom _ _ _

/-- The value of `CD0 s` is the energy-first integral of the vertex chain with the inserted
electron line on the outgoing side. -/
theorem value_repCD0 (Q : Params) (s : Fin 2) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    contractionValue₂ Q (repCD0 s) (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
        (fun _ => j) (fun _ => μ) =
      QED.OneLoop.energyFirstIntegral fun k =>
        vertexChain Q.e μ (electronInsertion Q.m Q.ε Q.δ₂ Q.δm (p' + k))
          (QED.OneLoop.electronPropagator Q.m Q.ε (p + k)) (photonInsertion Q.δ₃ Q.mγ Q.Λ Q.ε k)
          i j := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  fin_cases s
  · exact contractionValue₂_repCD0a Q hmom _ _ _
  · exact contractionValue₂_repCD0b Q hmom _ _ _

/-! ### The split at `ε > 0` -/

/-- The energy-first integral of three integrable products, the third with a factor `c`. -/
theorem energyFirstIntegral_three {F G H : (Fin 4 → ℝ) → ℂ} (c : ℂ)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => F (ℓ 0))
    (hG : QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => G (ℓ 0))
    (hH : QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => H (ℓ 0)) :
    QED.OneLoop.energyFirstIntegral (fun k => F k + G k + c * H k) =
      QED.OneLoop.energyFirstIntegral F + QED.OneLoop.energyFirstIntegral G +
        c * QED.OneLoop.energyFirstIntegral H := by
  simp only [← QED.TwoLoop.jointEnergyFirstIntegral_one_eq]
  rw [QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add
      (QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add hF hG)
      (QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul c hH),
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add hF hG,
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]

/-! ### The limits at fixed parameters -/

/-- The limit of `CD1 s`: the limits of the first two products. -/
noncomputable def cdInLim (Q : Params) (p' p : Fin 4 → ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  pieceLim (den₁ Q p' p) (numIn₁ Q p' p) + pieceLim (denIn₂ Q p' p) (numIn₂ Q p' p)

/-- The limit of `CD0 s`: the limits of the first two products. -/
noncomputable def cdOutLim (Q : Params) (p' p : Fin 4 → ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  pieceLim (den₁ Q p' p) (numOut₁ Q p' p) + pieceLim (denOut₂ Q p' p) (numOut₂ Q p' p)

theorem tendsto_ofReal_mul_I_mul {f : ℝ → ℂ} {a : ℂ} (hf : Tendsto f (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * I * f ε) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  simpa using (h0.mul_const I).mul hf

section Limits

variable (Q : Params) (hm : 0 < Q.m) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -Q.m ^ 2) (hp' : Minkowski.dot p' p' = -Q.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hm hmγ hΛ hp hp' hq

/-- **The class `CD1 s` converges** to `cdInLim`. -/
theorem tendsto_cdIn (s : Fin 2) (μ i j : Fin 4) :
    Tendsto (fun ε => contractionValue₂ { Q with ε := ε } (repCD1 s) (fun _ => p') (fun _ => p)
      (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)) (𝓝[>] 0)
      (𝓝 (cdInLim Q p' p μ i j)) := by
  obtain ⟨v₁, -, T₁, E₁⟩ := pieceLim_entry (by norm_num) kindsD3 (massesD3 Q) hm (lt_min hmγ hΛ)
    (massesD3_sq_of_ne_pho Q) (min_sq_le_massesD3_sq Q hmγ hΛ) intNoSubdivergenceRefined_kindsD3
    (by decide) (by decide) hp hp' hq (den₁ Q p' p) (numIn₁ Q p' p)
    (fun μ i j => (affMat_numIn₁ Q p' p μ i j).isLoopPoly) (fun ε _ ℓ => den₁_fac Q p p' ε ℓ) μ i j
  obtain ⟨v₂, -, T₂, E₂⟩ := pieceLim_entry (by norm_num) kindsIn₂ (massesD₂ Q) hm
    (lt_min hmγ hΛ) (massesD₂_sq_of_ne_pho_in Q) (min_sq_le_massesD₂_sq_in Q hmγ hΛ)
    intNoSubdivergenceRefined_kindsIn₂ (by decide) (by decide) hp hp' hq (denIn₂ Q p' p)
    (numIn₂ Q p' p) (fun μ i j => (affMat_numIn₂ Q p' p μ i j).isLoopPoly)
    (fun ε _ ℓ => denIn₂_fac Q p p' ε ℓ) μ i j
  obtain ⟨v₃, -, T₃, -⟩ := pieceLim_entry (by norm_num) kindsIn₂ (massesD₂ Q) hm
    (lt_min hmγ hΛ) (massesD₂_sq_of_ne_pho_in Q) (min_sq_le_massesD₂_sq_in Q hmγ hΛ)
    intNoSubdivergenceRefined_kindsIn₂ (by decide) (by decide) hp hp' hq (denIn₂ Q p' p)
    (numIn₁ Q p' p) (fun μ i j => (affMat_numIn₁ Q p' p μ i j).isLoopPoly)
    (fun ε _ ℓ => denIn₂_fac Q p p' ε ℓ) μ i j
  have hL : cdInLim Q p' p μ i j = v₁ / auxLimit Q.m + v₂ / auxLimit Q.m + 0 := by
    simp only [cdInLim, Pi.add_apply, Matrix.add_apply, E₁, E₂, add_zero]
  rw [hL]
  refine ((T₁.add T₂).add (tendsto_ofReal_mul_I_mul T₃)).congr'
    (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  dsimp only
  rw [value_repCD1]
  have e : (fun k => vertexChain Q.e μ (QED.OneLoop.electronPropagator Q.m ε (p' + k))
      (electronInsertion Q.m ε Q.δ₂ Q.δm (p + k)) (photonInsertion Q.δ₃ Q.mγ Q.Λ ε k) i j) =
      fun k => den₁ Q p' p ε k * numIn₁ Q p' p μ k i j +
        denIn₂ Q p' p ε k * numIn₂ Q p' p μ k i j +
        (ε : ℂ) * I * (denIn₂ Q p' p ε k * numIn₁ Q p' p μ k i j) := funext fun k => by
    rw [integrandIn_eq Q p' p μ hε.ne' k]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  exact (congrArg _ e).trans (energyFirstIntegral_three _
    (jointEnergyFirstIntegrable_den₁ Q p' p hε (affMat_numIn₁ Q p' p μ i j))
    (jointEnergyFirstIntegrable_denIn₂ Q p' p hε (affMat_numIn₂ Q p' p μ i j))
    (jointEnergyFirstIntegrable_denIn₂ Q p' p hε (affMat_numIn₁ Q p' p μ i j))) |>.symm

/-- **The class `CD0 s` converges** to `cdOutLim`. -/
theorem tendsto_cdOut (s : Fin 2) (μ i j : Fin 4) :
    Tendsto (fun ε => contractionValue₂ { Q with ε := ε } (repCD0 s) (fun _ => p') (fun _ => p)
      (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)) (𝓝[>] 0)
      (𝓝 (cdOutLim Q p' p μ i j)) := by
  obtain ⟨v₁, -, T₁, E₁⟩ := pieceLim_entry (by norm_num) kindsD3 (massesD3 Q) hm (lt_min hmγ hΛ)
    (massesD3_sq_of_ne_pho Q) (min_sq_le_massesD3_sq Q hmγ hΛ) intNoSubdivergenceRefined_kindsD3
    (by decide) (by decide) hp hp' hq (den₁ Q p' p) (numOut₁ Q p' p)
    (fun μ i j => (affMat_numOut₁ Q p' p μ i j).isLoopPoly) (fun ε _ ℓ => den₁_fac Q p p' ε ℓ)
    μ i j
  obtain ⟨v₂, -, T₂, E₂⟩ := pieceLim_entry (by norm_num) kindsOut₂ (massesD₂ Q) hm
    (lt_min hmγ hΛ) (massesD₂_sq_of_ne_pho_out Q) (min_sq_le_massesD₂_sq_out Q hmγ hΛ)
    intNoSubdivergenceRefined_kindsOut₂ (by decide) (by decide) hp hp' hq (denOut₂ Q p' p)
    (numOut₂ Q p' p) (fun μ i j => (affMat_numOut₂ Q p' p μ i j).isLoopPoly)
    (fun ε _ ℓ => denOut₂_fac Q p p' ε ℓ) μ i j
  obtain ⟨v₃, -, T₃, -⟩ := pieceLim_entry (by norm_num) kindsOut₂ (massesD₂ Q) hm
    (lt_min hmγ hΛ) (massesD₂_sq_of_ne_pho_out Q) (min_sq_le_massesD₂_sq_out Q hmγ hΛ)
    intNoSubdivergenceRefined_kindsOut₂ (by decide) (by decide) hp hp' hq (denOut₂ Q p' p)
    (numOut₁ Q p' p) (fun μ i j => (affMat_numOut₁ Q p' p μ i j).isLoopPoly)
    (fun ε _ ℓ => denOut₂_fac Q p p' ε ℓ) μ i j
  have hL : cdOutLim Q p' p μ i j = v₁ / auxLimit Q.m + v₂ / auxLimit Q.m + 0 := by
    simp only [cdOutLim, Pi.add_apply, Matrix.add_apply, E₁, E₂, add_zero]
  rw [hL]
  refine ((T₁.add T₂).add (tendsto_ofReal_mul_I_mul T₃)).congr'
    (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  dsimp only
  rw [value_repCD0]
  have e : (fun k => vertexChain Q.e μ (electronInsertion Q.m ε Q.δ₂ Q.δm (p' + k))
      (QED.OneLoop.electronPropagator Q.m ε (p + k)) (photonInsertion Q.δ₃ Q.mγ Q.Λ ε k) i j) =
      fun k => den₁ Q p' p ε k * numOut₁ Q p' p μ k i j +
        denOut₂ Q p' p ε k * numOut₂ Q p' p μ k i j +
        (ε : ℂ) * I * (denOut₂ Q p' p ε k * numOut₁ Q p' p μ k i j) := funext fun k => by
    rw [integrandOut_eq Q p' p μ hε.ne' k]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  exact (congrArg _ e).trans (energyFirstIntegral_three _
    (jointEnergyFirstIntegrable_den₁ Q p' p hε (affMat_numOut₁ Q p' p μ i j))
    (jointEnergyFirstIntegrable_denOut₂ Q p' p hε (affMat_numOut₂ Q p' p μ i j))
    (jointEnergyFirstIntegrable_denOut₂ Q p' p hε (affMat_numOut₁ Q p' p μ i j))) |>.symm

omit hp hp' hq in
/-- **Covariance of the limit of `CD1 s`.** -/
theorem cdInLim_map {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S T) (hp : Minkowski.dot p p = -Q.m ^ 2)
    (hp' : Minkowski.dot p' p' = -Q.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (μ : Fin 4) :
    S * cdInLim Q (L *ᵥ p') (L *ᵥ p) μ * T = vecAct L (cdInLim Q p' p) μ := by
  have h₁ : S * pieceLim (den₁ Q (L *ᵥ p') (L *ᵥ p)) (numIn₁ Q (L *ᵥ p') (L *ᵥ p)) μ * T =
      vecAct L (pieceLim (den₁ Q p' p) (numIn₁ Q p' p)) μ :=
    pieceLim_map (by norm_num) kindsD3 (massesD3 Q) hm (lt_min hmγ hΛ)
      (massesD3_sq_of_ne_pho Q) (min_sq_le_massesD3_sq Q hmγ hΛ)
      intNoSubdivergenceRefined_kindsD3 (by decide) (by decide) h (fun p p' => den₁ Q p' p)
      (fun p p' => numIn₁ Q p' p) (fun p p' μ i j => (affMat_numIn₁ Q p' p μ i j).isLoopPoly)
      (fun p p' ε _ ℓ => den₁_fac Q p p' ε ℓ) (fun p p' μ k => numIn₁_map h Q p' p μ k)
      hp hp' hq μ
  have h₂ : S * pieceLim (denIn₂ Q (L *ᵥ p') (L *ᵥ p)) (numIn₂ Q (L *ᵥ p') (L *ᵥ p)) μ * T =
      vecAct L (pieceLim (denIn₂ Q p' p) (numIn₂ Q p' p)) μ :=
    pieceLim_map (by norm_num) kindsIn₂ (massesD₂ Q) hm (lt_min hmγ hΛ)
      (massesD₂_sq_of_ne_pho_in Q) (min_sq_le_massesD₂_sq_in Q hmγ hΛ)
      intNoSubdivergenceRefined_kindsIn₂ (by decide) (by decide) h (fun p p' => denIn₂ Q p' p)
      (fun p p' => numIn₂ Q p' p) (fun p p' μ i j => (affMat_numIn₂ Q p' p μ i j).isLoopPoly)
      (fun p p' ε _ ℓ => denIn₂_fac Q p p' ε ℓ) (fun p p' μ k => numIn₂_map h Q p' p μ k)
      hp hp' hq μ
  rw [cdInLim, Pi.add_apply, Matrix.mul_add, Matrix.add_mul, h₁, h₂]
  exact (vecAct_add L _ _ μ).symm

omit hp hp' hq in
/-- **Covariance of the limit of `CD0 s`.** -/
theorem cdOutLim_map {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S T) (hp : Minkowski.dot p p = -Q.m ^ 2)
    (hp' : Minkowski.dot p' p' = -Q.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (μ : Fin 4) :
    S * cdOutLim Q (L *ᵥ p') (L *ᵥ p) μ * T = vecAct L (cdOutLim Q p' p) μ := by
  have h₁ : S * pieceLim (den₁ Q (L *ᵥ p') (L *ᵥ p)) (numOut₁ Q (L *ᵥ p') (L *ᵥ p)) μ * T =
      vecAct L (pieceLim (den₁ Q p' p) (numOut₁ Q p' p)) μ :=
    pieceLim_map (by norm_num) kindsD3 (massesD3 Q) hm (lt_min hmγ hΛ)
      (massesD3_sq_of_ne_pho Q) (min_sq_le_massesD3_sq Q hmγ hΛ)
      intNoSubdivergenceRefined_kindsD3 (by decide) (by decide) h (fun p p' => den₁ Q p' p)
      (fun p p' => numOut₁ Q p' p) (fun p p' μ i j => (affMat_numOut₁ Q p' p μ i j).isLoopPoly)
      (fun p p' ε _ ℓ => den₁_fac Q p p' ε ℓ) (fun p p' μ k => numOut₁_map h Q p' p μ k)
      hp hp' hq μ
  have h₂ : S * pieceLim (denOut₂ Q (L *ᵥ p') (L *ᵥ p)) (numOut₂ Q (L *ᵥ p') (L *ᵥ p)) μ * T =
      vecAct L (pieceLim (denOut₂ Q p' p) (numOut₂ Q p' p)) μ :=
    pieceLim_map (by norm_num) kindsOut₂ (massesD₂ Q) hm (lt_min hmγ hΛ)
      (massesD₂_sq_of_ne_pho_out Q) (min_sq_le_massesD₂_sq_out Q hmγ hΛ)
      intNoSubdivergenceRefined_kindsOut₂ (by decide) (by decide) h (fun p p' => denOut₂ Q p' p)
      (fun p p' => numOut₂ Q p' p) (fun p p' μ i j => (affMat_numOut₂ Q p' p μ i j).isLoopPoly)
      (fun p p' ε _ ℓ => denOut₂_fac Q p p' ε ℓ) (fun p p' μ k => numOut₂_map h Q p' p μ k)
      hp hp' hq μ
  rw [cdOutLim, Pi.add_apply, Matrix.mul_add, Matrix.add_mul, h₁, h₂]
  exact (vecAct_add L _ _ μ).symm

end Limits

/-! ### The links of the classes `CD0`, `CD1` -/

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

/-- The limit of the class `CDₖ s`, `k < 2`. -/
noncomputable def cd01Lim (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt) (s : ℝ × ℝ × ℝ)
    (k : Fin 5) (p' p : Fin 4 → ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  if k = 0 then cdOutLim (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) p' p
  else cdInLim (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) p' p

theorem lt_two_cases {k : Fin 5} (hk : k < 2) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp_all

/-- At admissible data and an on-shell positive-energy pair, the class `CDₖ s` (`k < 2`)
converges to `cd01Lim`. -/
theorem isClassLimC_CD01 (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (k : Fin 5) (hk : k < 2)
    (t : Fin 2) {p' p : Fin 4 → ℝ} (hpq : IsPairQ P₀.m p' p) :
    IsClassLimC ctFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inr (.inl (k, t))) p' p
      (cd01Lim P₀ M₁ M₂ c₁ c₂ mγ Λ D s k p' p) := by
  obtain ⟨-, -, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  have hm : 0 < P₀.m := by linarith
  intro μ i j
  rcases lt_two_cases hk with rfl | rfl
  · exact (tendsto_cdOut (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) hm hmγ hΛ hp hp' hq.le t μ i
      j).congr fun ε => ((cd01Val_apply _ _ _ p' p μ t i j).1).symm
  · exact (tendsto_cdIn (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) hm hmγ hΛ hp hp' hq.le t μ i
      j).congr fun ε => ((cd01Val_apply _ _ _ p' p μ t i j).2).symm

/-- **The limit links of the four classes `CD0 s`, `CD1 s`.** -/
theorem setCClassLim_CD01 (k : Fin 5) (hk : k < 2) (t : Fin 2) :
    SetCClassLim ctFam P₀ (.inr (.inl (k, t))) :=
  fun _ _ _ _ _ _ _ _ hA _ _ hpq => ⟨_, isClassLimC_CD01 hA k hk t hpq⟩

/-- **The covariance links of the four classes `CD0 s`, `CD1 s`.** -/
theorem setCClassCov_CD01 (k : Fin 5) (hk : k < 2) (t : Fin 2) :
    SetCClassCov ctFam P₀ (.inr (.inl (k, t))) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA L S T h p' p hpq h0 h1 Y Z hY hZ μ
  have hpq' := isPairQ_map h hpq h0 h1
  have eY : Y = cd01Lim P₀ M₁ M₂ c₁ c₂ mγ Λ D s k p' p := by
    funext ν
    ext i j
    exact tendsto_nhds_unique (hY ν i j) (isClassLimC_CD01 hA k hk t hpq ν i j)
  have eZ : Z = cd01Lim P₀ M₁ M₂ c₁ c₂ mγ Λ D s k (L *ᵥ p') (L *ᵥ p) := by
    funext ν
    ext i j
    exact tendsto_nhds_unique (hZ ν i j) (isClassLimC_CD01 hA k hk t hpq' ν i j)
  obtain ⟨-, -, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  have hm : 0 < P₀.m := by linarith
  rw [eY, eZ]
  rcases lt_two_cases hk with rfl | rfl
  · exact cdOutLim_map (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) hm hmγ hΛ h hp hp' hq.le μ
  · exact cdInLim_map (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) hm hmγ hΛ h hp hp' hq.le μ

/-! ### The links of (HS₆) with the ten classes `CDₖ s` discharged -/

/-- **The limit link of (HS₆)** from the limit links of the 36 two-loop-outer classes and of
the five classes `CBₖ`. -/
theorem setCLimitLink_of_main_cb (hM : ∀ r, SetCClassLim mainFam P₀ r)
    (hCB : ∀ k, SetCClassLim ctFam P₀ (.inl k)) : SetCLimitLink P₀ :=
  setCLimitLink_of_main_cb_cd01 hM hCB fun k s hk => setCClassLim_CD01 k hk s

/-- **The covariance link of (HS₆)** from the limit and covariance links of the 36
two-loop-outer classes and of the five classes `CBₖ`. -/
theorem setCCovLink_of_main_cb (hM : ∀ r, SetCClassLim mainFam P₀ r)
    (hCB : ∀ k, SetCClassLim ctFam P₀ (.inl k)) (hMc : ∀ r, SetCClassCov mainFam P₀ r)
    (hCBc : ∀ k, SetCClassCov ctFam P₀ (.inl k)) : SetCCovLink P₀ :=
  setCCovLink_of_main_cb_cd01 hM hCB (fun k s hk => setCClassLim_CD01 k hk s) hMc hCBc
    fun k s hk => setCClassCov_CD01 k hk s

end QED.ChainProof.SetCPauli

end
