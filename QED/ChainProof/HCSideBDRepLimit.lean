/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideBDRows
public import QED.ChainProof.HCLimit
public import QED.TwoLoop.RelabelInvariance

/-!
# The `ε → 0⁺` limits of the bubble–`δ₃` and `δ₃`–bubble representatives

Helper level, Phase 5 Stage 1a, obligation O3-6 for `QED.ChainProof.Enum.repBD s` and
`QED.ChainProof.Enum.repDB s`.

* `contractionValue₂_repBD_eq`, `contractionValue₂_repDB_eq`: the value (T₁₀) is the joint
  energy-first integral of the class-variable integrand `bdG`, resp. `dbG`, under momentum
  conservation (an integer unimodular affine change of loop momenta).
* `jointHasLim_bdG`, `jointHasLim_dbG`: at admissible parameters, on-shell `p, p'` with
  `(p' - p)² ≥ 0`, the joint integrals of these integrands converge as `ε → 0⁺`. The integrands
  are split into pieces on rows of the `VP` class matrix (`QED.ChainProof.RepsInt.bdG_eq`,
  `QED.ChainProof.RepsInt.dbG_eq`), each converging by
  `QED/ChainProof/HCSideBDRows.lean`; the coefficients `m_γ² - iε` and `ε` converge.
* **`repLimit_repBD`, `repLimit_repDB`**: `RepLimit (repBD s)` and `RepLimit (repDB s)`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology

namespace QED.ChainProof.HCSide

open QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit
  QED.ChainProof.Enum QED.ChainProof.RepsInt QED.TwoLoop.ClassIntegrable QED.ChainProof.HCLimit
open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrix classVPMasses)
open QED.TwoLoop.JointIntegralInvariance (jointEnergyFirstIntegral_comp_matrix_add)

/-! ### The value in the class variables -/

theorem det_bdMat : IsUnit (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det := by
  rw [Matrix.det_fin_two]; simp

/-- **The value of `repBD s`** is the joint integral of `bdG`, under momentum conservation. -/
theorem contractionValue₂_repBD_eq (P : Params) (s : Fin 2) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.WickModel.contractionValue₂ P (repBD s) pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral 2 (bdG P αOut βIn μ s pIn kIn) := by
  refine (QED.TwoLoop.Relabel.contractionValue₂_eq_of_loopCount P (loopCount_repBD s) _ _ _ _ _
    _).trans (Eq.trans ?_ (jointEnergyFirstIntegral_comp_matrix_add 2
      (bdG P αOut βIn μ s pIn kIn) !![1, 1; 1, 0] det_bdMat ![-(pIn 0), -(pIn 0)]))
  refine congrArg (QED.TwoLoop.jointEnergyFirstIntegral 2) (funext fun ℓ => ?_)
  rw [lineMomentum₂_repBD s hmom, bdG]
  congr 3
  · funext ν
    simp [Fin.sum_univ_two]
    ring
  · funext ν
    simp [Fin.sum_univ_two]
    ring

/-- **The value of `repDB s`** is the joint integral of `dbG`, under momentum conservation. -/
theorem contractionValue₂_repDB_eq (P : Params) (s : Fin 2) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.WickModel.contractionValue₂ P (repDB s) pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral 2 (dbG P αOut βIn μ s pIn kIn) := by
  refine (QED.TwoLoop.Relabel.contractionValue₂_eq_of_loopCount P (loopCount_repDB s) _ _ _ _ _
    _).trans (Eq.trans ?_ (jointEnergyFirstIntegral_comp_matrix_add 2
      (dbG P αOut βIn μ s pIn kIn) !![1, 1; 1, 0] det_bdMat ![-(pIn 0), -(pIn 0)]))
  refine congrArg (QED.TwoLoop.jointEnergyFirstIntegral 2) (funext fun ℓ => ?_)
  rw [lineMomentum₂_repDB s hmom, dbG]
  congr 3
  · funext ν
    simp [Fin.sum_univ_two]
    ring
  · funext ν
    simp [Fin.sum_univ_two]
    ring

/-! ### Convergence of the integrands -/

theorem tendsto_mγ_sub (P : Params) (K : ℂ) :
    Tendsto (fun ε : ℝ => K * (((P.mγ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)) (𝓝[>] 0)
      (𝓝 (K * (((P.mγ ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I))) :=
  ((continuous_const.mul (continuous_const.sub (continuous_ofReal.mul continuous_const))).tendsto
    0).mono_left nhdsWithin_le_nhds

section Assembly

variable (P : Params) (hA : ChainAdmissible P) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))

include hA hp hp' hq

/-- **The integrand of `repBD s` converges** at admissible parameters, on-shell `p, p'` with
`(p' - p)² ≥ 0`. -/
theorem jointHasLim_bdG (s : Fin 2) (α β μ : Fin 4) :
    JointHasLim fun ε => bdG { P with ε := ε } (fun _ => α) (fun _ => β) (fun _ => μ) s
      (fun _ => p) (fun _ => p' - p) := by
  have h₁ : P.m ^ 2 ≤ P.M₁ ^ 2 := pow_le_pow_left₀ hA.hm.le hA.hM₁.le 2
  have h₂ : P.m ^ 2 ≤ P.M₂ ^ 2 := pow_le_pow_left₀ hA.hm.le hA.hM₂.le 2
  have hΛ : P.mγ ^ 2 ≤ P.Λ ^ 2 := pow_le_pow_left₀ hA.hmγ.le hA.hmγΛ.le 2
  have hc : 0 < 3 / 4 * min (P.m ^ 2) (P.mγ ^ 2) :=
    mul_pos (by norm_num) (lt_min (pow_pos hA.hm 2) (pow_pos hA.hmγ 2))
  have hpp : p + (p' - p) = p' := by abel
  have hp'' : Minkowski.dot (p + (p' - p)) (p + (p' - p)) = -P.m ^ 2 := by rw [hpp]; exact hp'
  have hq'' : 0 ≤ Minkowski.dot (p + (p' - p) - p) (p + (p' - p) - p) := by rw [hpp]; exact hq
  obtain ⟨m1, m2, m3a, m3b, m3c⟩ := massL_ge P h₁ h₂ hΛ
  obtain ⟨c1, c2, c3a, c3b, c3c⟩ := crit_L
  have hA1 := (jointHasLim_vpSum_ext1 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
    (fun _ => β) (fun _ => μ) hA.hm hA.hmγ h₁ h₂ hΛ hΛ hp hp' hq).const_mul
    ((((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * (-(P.δ₃ / 2 : ℂ)) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ))
  have hA2 := (jointHasLim_vpSum_ext2 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
    (fun _ => β) (fun _ => μ) hA.hm hA.hmγ h₁ h₂ hΛ le_rfl hΛ hp hp' hq).mul_left
    (tendsto_mγ_sub P ((((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * (P.δ₃ / 2 : ℂ) *
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)))
  have hL1 := jointHasLim_bdPiece P (by norm_num) lineL1 (massL1 P) p (p' - p) μ α β 8
    isLoopAffine_zero' rfl rfl rfl (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.1.symm) (by decide)
    (by decide) (by decide) (by decide) c1 (bdκL P) hc
    (symanzikV_vpRows_ge _ _ m1 hp hp'' hq'')
  have hL2 := jointHasLim_bdPiece P (by norm_num) lineL2 (massL1 P) p (p' - p) μ α β 8
    (IsLoopAffine.add' isLoopAffine_zero' isLoopAffine_neg_one) rfl rfl rfl
    (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.1.symm) (by decide) (by decide) (by decide)
    (by decide) c2 (-bdκL P) hc (symanzikV_vpRows_ge _ _ m2 hp hp'' hq'')
  have hL3a := (jointHasLim_bdPiece P (by norm_num) lineL3a (massL3a P) p (p' - p) μ α β 3
    isLoopAffine_neg_one rfl rfl rfl (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm)
    (by decide) (by decide) (by decide) (by decide) c3a (-(bdκL P * I)) hc
    (symanzikV_vpRows_ge _ _ m3a hp hp'' hq'')).eps_mul
  have hL3b := (jointHasLim_bdPiece P (by norm_num) lineL3b (massL3b P) p (p' - p) μ α β 3
    isLoopAffine_neg_one rfl rfl rfl (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm)
    (by decide) (by decide) (by decide) (by decide) c3b (-(bdκL P * I)) hc
    (symanzikV_vpRows_ge _ _ m3b hp hp'' hq'')).eps_mul
  have hL3c := (jointHasLim_bdPiece P (by norm_num) lineL3c (massL3c P) p (p' - p) μ α β 3
    isLoopAffine_neg_one rfl rfl rfl (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm)
    (by decide) (by decide) (by decide) (by decide) c3c (-(bdκL P * I)) hc
    (symanzikV_vpRows_ge _ _ m3c hp hp'' hq'')).eps_mul
  refine (((((((hA1.add hA2).add hL1).add hL2).add hL3a).add hL3b).add hL3c).congr ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  intro ℓ
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  rw [bdG_eq { P with ε := ε } (fun _ => α) (fun _ => β) (fun _ => μ) s (pOut := fun _ => p') hε.ne'
    hA.hPV₁ hA.hPV₂ hmom ℓ]
  have e1 : bdκL { P with ε := ε } = bdκL P := rfl
  have e3 : massL1 { P with ε := ε } = massL1 P := rfl
  have e3a : massL3a { P with ε := ε } = massL3a P := rfl
  have e3b : massL3b { P with ε := ε } = massL3b P := rfl
  have e3c : massL3c { P with ε := ε } = massL3c P := rfl
  have e2 : ∀ a b c d e f g, bdN { P with ε := ε } a b c d e f g = bdN P a b c d e f g :=
    fun _ _ _ _ _ _ _ => rfl
  simp only [e1, e2, e3, e3a, e3b, e3c]
  ring

/-- **The integrand of `repDB s` converges**, as `jointHasLim_bdG`. -/
theorem jointHasLim_dbG (s : Fin 2) (α β μ : Fin 4) :
    JointHasLim fun ε => dbG { P with ε := ε } (fun _ => α) (fun _ => β) (fun _ => μ) s
      (fun _ => p) (fun _ => p' - p) := by
  have h₁ : P.m ^ 2 ≤ P.M₁ ^ 2 := pow_le_pow_left₀ hA.hm.le hA.hM₁.le 2
  have h₂ : P.m ^ 2 ≤ P.M₂ ^ 2 := pow_le_pow_left₀ hA.hm.le hA.hM₂.le 2
  have hΛ : P.mγ ^ 2 ≤ P.Λ ^ 2 := pow_le_pow_left₀ hA.hmγ.le hA.hmγΛ.le 2
  have hc : 0 < 3 / 4 * min (P.m ^ 2) (P.mγ ^ 2) :=
    mul_pos (by norm_num) (lt_min (pow_pos hA.hm 2) (pow_pos hA.hmγ 2))
  have hpp : p + (p' - p) = p' := by abel
  have hp'' : Minkowski.dot (p + (p' - p)) (p + (p' - p)) = -P.m ^ 2 := by rw [hpp]; exact hp'
  have hq'' : 0 ≤ Minkowski.dot (p + (p' - p) - p) (p + (p' - p) - p) := by rw [hpp]; exact hq
  obtain ⟨m1, m2, m3a, m3b, m3c⟩ := massL_ge P h₁ h₂ hΛ
  obtain ⟨c1, c2, c3a, c3b, c3c⟩ := crit_L
  have hA1 := (jointHasLim_vpSum_ext1 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
    (fun _ => β) (fun _ => μ) hA.hm hA.hmγ h₁ h₂ hΛ hΛ hp hp' hq).const_mul
    ((((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * (-(P.δ₃ / 2 : ℂ)) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ))
  have hA2 := (jointHasLim_vpSum_ext2 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
    (fun _ => β) (fun _ => μ) hA.hm hA.hmγ h₁ h₂ hΛ le_rfl hΛ hp hp' hq).mul_left
    (tendsto_mγ_sub P ((((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * (P.δ₃ / 2 : ℂ) *
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)))
  have hL1 := jointHasLim_dbPiece P (by norm_num) lineL1 (massL1 P) p (p' - p) μ α β 8
    isLoopAffine_zero' rfl rfl rfl (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.1.symm) (by decide)
    (by decide) (by decide) (by decide) c1 (bdκL P) hc
    (symanzikV_vpRows_ge _ _ m1 hp hp'' hq'')
  have hL2 := jointHasLim_dbPiece P (by norm_num) lineL2 (massL1 P) p (p' - p) μ α β 8
    (IsLoopAffine.add' isLoopAffine_zero' isLoopAffine_neg_one) rfl rfl rfl
    (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.1.symm) (by decide) (by decide) (by decide)
    (by decide) c2 (-bdκL P) hc (symanzikV_vpRows_ge _ _ m2 hp hp'' hq'')
  have hL3a := (jointHasLim_dbPiece P (by norm_num) lineL3a (massL3a P) p (p' - p) μ α β 3
    isLoopAffine_neg_one rfl rfl rfl (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm)
    (by decide) (by decide) (by decide) (by decide) c3a (-(bdκL P * I)) hc
    (symanzikV_vpRows_ge _ _ m3a hp hp'' hq'')).eps_mul
  have hL3b := (jointHasLim_dbPiece P (by norm_num) lineL3b (massL3b P) p (p' - p) μ α β 3
    isLoopAffine_neg_one rfl rfl rfl (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm)
    (by decide) (by decide) (by decide) (by decide) c3b (-(bdκL P * I)) hc
    (symanzikV_vpRows_ge _ _ m3b hp hp'' hq'')).eps_mul
  have hL3c := (jointHasLim_dbPiece P (by norm_num) lineL3c (massL3c P) p (p' - p) μ α β 3
    isLoopAffine_neg_one rfl rfl rfl (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm)
    (by decide) (by decide) (by decide) (by decide) c3c (-(bdκL P * I)) hc
    (symanzikV_vpRows_ge _ _ m3c hp hp'' hq'')).eps_mul
  refine (((((((hA1.add hA2).add hL1).add hL2).add hL3a).add hL3b).add hL3c).congr ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  intro ℓ
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  rw [dbG_eq { P with ε := ε } (fun _ => α) (fun _ => β) (fun _ => μ) s (pOut := fun _ => p') hε.ne'
    hA.hPV₁ hA.hPV₂ hmom ℓ]
  have e1 : bdκL { P with ε := ε } = bdκL P := rfl
  have e3 : massL1 { P with ε := ε } = massL1 P := rfl
  have e3a : massL3a { P with ε := ε } = massL3a P := rfl
  have e3b : massL3b { P with ε := ε } = massL3b P := rfl
  have e3c : massL3c { P with ε := ε } = massL3c P := rfl
  have e2 : ∀ a b c d e f g, dbN { P with ε := ε } a b c d e f g = dbN P a b c d e f g :=
    fun _ _ _ _ _ _ _ => rfl
  simp only [e1, e2, e3, e3a, e3b, e3c]
  ring

end Assembly

/-! ### The representatives -/

/-- **The bubble–`δ₃` representatives have `ε → 0⁺` limits**, for both field pairings. -/
theorem repLimit_repBD (s : Fin 2) : RepLimit (repBD s) := by
  intro P hA p' p hpq α β μ
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  obtain ⟨-, L, hL⟩ := jointHasLim_bdG P hA hp hp' hq.le s α β μ
  refine ⟨L, hL.congr' (Eventually.of_forall fun ε => ?_)⟩
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hΦ : chainFlavors P =
      (⟨({ P with ε := ε } : Params).mass, ({ P with ε := ε } : Params).loopCoeff, 0⟩ :
        QED.Lepton.Flavors (Fin 3)) := rfl
  dsimp only
  rw [hΦ, contractionValue₂_params', contractionValue₂_repBD_eq _ s hmom]

/-- **The `δ₃`–bubble representatives have `ε → 0⁺` limits**, for both field pairings. -/
theorem repLimit_repDB (s : Fin 2) : RepLimit (repDB s) := by
  intro P hA p' p hpq α β μ
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  obtain ⟨-, L, hL⟩ := jointHasLim_dbG P hA hp hp' hq.le s α β μ
  refine ⟨L, hL.congr' (Eventually.of_forall fun ε => ?_)⟩
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hΦ : chainFlavors P =
      (⟨({ P with ε := ε } : Params).mass, ({ P with ε := ε } : Params).loopCoeff, 0⟩ :
        QED.Lepton.Flavors (Fin 3)) := rfl
  dsimp only
  rw [hΦ, contractionValue₂_params', contractionValue₂_repDB_eq _ s hmom]

end QED.ChainProof.HCSide

end
