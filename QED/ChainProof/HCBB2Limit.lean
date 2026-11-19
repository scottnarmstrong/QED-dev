/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCBB2Spec
public import QED.ChainProof.HCBB2Num
public import QED.ChainProof.HCBBLimit

/-!
# The `ε → 0⁺` limit of the bubble–bubble vertex, entry by entry

Helper level, Phase 5 Stage 1a, obligation O3-6 for `QED.ChainProof.Enum.repBB`. This file proves
the one-loop analytic statement `QED.ChainProof.HCBB.BBInsertionLimit`, and with it
`RepLimit repBB` from the three-loop integrability `QED.ChainProof.HCBB.BBJointIntegrable`.

* `bbEntry_eq`: at `ε > 0`, every matrix entry of the one-loop vertex with the double insertion
  `bbInsertion = d³ (X g - Ψ k k)` (`X = Π̂²k⁴ - 2iεΠ̂Sk² - ε²S²`, `Ψ = Π̂²k² - 2iεΠ̂S`) is
  `κ (Λ² - m_γ²)³ ∑_{n<9} c_n(ε) T_n`, with `T_n` two spectral factors
  (`QED.ChainProof.HCBB2.ggInt`) on the six photon-type denominators `(m_γ, Λ)³` of `d³`, and
  numerators `numG`, `numS`, `numL`, `numQ`. The longitudinal part `k̸ S γ^μ S k̸` is reduced by
  `ℓ̸ ℓ̸ = -ℓ²` (`QED.ChainProof.HCBB2.slash_mul_massSub`), so every numerator is quadratic and
  every power of `k²` is at most `2`: the engine applies with `j + 2 ≤ 4`.
* `ggInt_ok`: each piece converges and is integrable in both stages at `ε ∈ (0, 1]`.
* **`bbInsertionLimit`**: `QED.ChainProof.HCBB.BBInsertionLimit` holds.
* **`repLimit_repBB`**: `RepLimit repBB` from `BBJointIntegrable`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Matrix
open scoped Real

namespace QED.ChainProof.HCBB2

open QED.OneLoop QED.OneLoop.VertexLimit QED.WickModel
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtAssembly
open QED.TwoLoop.VPHalfAt QED.TwoLoop.VPHalfAtGen QED.TwoLoop.Insertion QED.TwoLoop.Bridge
open QED.ChainProof.HCBB

/-! ### The pieces -/

/-- The six photon-type masses of `d(k)³`. -/
def ms6 (P : Params) : Fin (4 + 2) → ℝ := ![P.mγ, P.Λ, P.mγ, P.Λ, P.mγ, P.Λ]

/-- The vertex prefactor `(ie)³ (1/i)³ (2π)⁻⁴`. -/
noncomputable def kap (e : ℝ) : ℂ :=
  (I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹

/-- The nine pieces of an entry of the bubble–bubble vertex. -/
noncomputable def bbPiece (P : Params) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (ε : ℝ) :
    Fin 9 → (Fin 4 → ℝ) → ℂ :=
  ![ggInt P (numG P.m p' p μ i j) (ms6 P) 2 (1 / 6) (1 / 6) wOne wOne ε p' p,
    ggInt P (numG P.m p' p μ i j) (ms6 P) 1 (1 / 6) 1 wOne wId ε p' p,
    ggInt P (numG P.m p' p μ i j) (ms6 P) 0 1 1 wId wId ε p' p,
    ggInt P (numS μ i j) (ms6 P) 2 (1 / 6) (1 / 6) wOne wOne ε p' p,
    ggInt P (numS μ i j) (ms6 P) 1 (1 / 6) 1 wOne wId ε p' p,
    ggInt P (numL P.m p' p μ i j) (ms6 P) 2 (1 / 6) (1 / 6) wOne wOne ε p' p,
    ggInt P (numL P.m p' p μ i j) (ms6 P) 1 (1 / 6) 1 wOne wId ε p' p,
    ggInt P (numQ P.m p' p μ i j) (ms6 P) 1 (1 / 6) (1 / 6) wOne wOne ε p' p,
    ggInt P (numQ P.m p' p μ i j) (ms6 P) 0 (1 / 6) 1 wOne wId ε p' p]

/-- Their coefficients. -/
noncomputable def bbCoef (P : Params) (ε : ℝ) : Fin 9 → ℂ :=
  ![cOne P ^ 2, -(2 * I * (ε : ℂ) * cOne P * cTwo P), -((ε : ℂ) ^ 2 * cTwo P ^ 2),
    -(cOne P ^ 2), 2 * I * (ε : ℂ) * cOne P * cTwo P,
    -(cOne P ^ 2), 2 * I * (ε : ℂ) * cOne P * cTwo P,
    -(cOne P ^ 2), 2 * I * (ε : ℂ) * cOne P * cTwo P]

/-! ### Matrix algebra -/

/-- `∑_{νρ} k_ν k_ρ γ^ρ A γ^μ B γ^ν = k̸ A γ^μ B k̸`. -/
theorem sum_lower_smul (ℓ : Fin 4 → ℝ) (A B : Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    ∑ ν, ∑ ρ, (((Minkowski.lower ℓ ν : ℝ) : ℂ) * ((Minkowski.lower ℓ ρ : ℝ) : ℂ)) •
        (Dirac.gamma ρ * A * Dirac.gamma μ * B * Dirac.gamma ν) =
      Dirac.slash ℓ * A * Dirac.gamma μ * B * Dirac.slash ℓ := by
  simp only [Dirac.slash, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]

/-- The longitudinal matrix `k̸ (m - (p'+k)̸) γ^μ (m - (p+k)̸) k̸`, entrywise. -/
theorem longitudinal_apply (m : ℝ) (p' p ℓ : Fin 4 → ℝ) (μ i j : Fin 4) :
    (Dirac.slash ℓ * electronNumerator m (p' + ℓ) * Dirac.gamma μ * electronNumerator m (p + ℓ) *
        Dirac.slash ℓ) i j =
      ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) * numS μ i j ℓ +
        ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) * numL m p' p μ i j ℓ + numQ m p' p μ i j ℓ := by
  set s : ℂ := ((Minkowski.dot ℓ ℓ : ℝ) : ℂ)
  set A' := (m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p'
  set B' := (m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p
  have e : Dirac.slash ℓ * electronNumerator m (p' + ℓ) * Dirac.gamma μ *
      electronNumerator m (p + ℓ) * Dirac.slash ℓ =
      (s * s) • Dirac.gamma μ + s • (Dirac.slash ℓ * (A' * Dirac.gamma μ) +
        (Dirac.gamma μ * B') * Dirac.slash ℓ) +
        Dirac.slash ℓ * (A' * Dirac.gamma μ * B') * Dirac.slash ℓ := by
    have h1 := slash_mul_massSub m p' ℓ
    have h2 := massSub_mul_slash m p ℓ
    rw [show Dirac.slash ℓ * electronNumerator m (p' + ℓ) * Dirac.gamma μ *
        electronNumerator m (p + ℓ) * Dirac.slash ℓ =
        (Dirac.slash ℓ * electronNumerator m (p' + ℓ)) * Dirac.gamma μ *
          (electronNumerator m (p + ℓ) * Dirac.slash ℓ) by simp only [Matrix.mul_assoc],
      electronNumerator, electronNumerator, h1, h2]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_smul, Matrix.mul_assoc, smul_add]
    abel
  rw [e]
  simp only [numS, numL, numQ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, A', B', s]
  ring

/-- The Feynman-gauge entry of the vertex chain. -/
theorem vertexChain_gPhoton_apply (e m : ℝ) (p' p ℓ : Fin 4 → ℝ) (μ i j : Fin 4) :
    vertexChain e μ (electronNumerator m (p' + ℓ)) (electronNumerator m (p + ℓ)) gPhoton i j =
      kap e * numG m p' p μ i j ℓ := by
  simp only [vertexChain, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, gPhoton, numG,
    vertexNumerator, electronNumerator, kap, Finset.mul_sum]

/-- The longitudinal entry of the vertex chain. -/
theorem vertexChain_lower_apply (e m : ℝ) (p' p ℓ : Fin 4 → ℝ) (μ i j : Fin 4) :
    vertexChain e μ (electronNumerator m (p' + ℓ)) (electronNumerator m (p + ℓ))
        (fun ν ρ => ((Minkowski.lower ℓ ν : ℝ) : ℂ) * ((Minkowski.lower ℓ ρ : ℝ) : ℂ)) i j =
      kap e * (((Minkowski.dot ℓ ℓ : ℝ) : ℂ) * numS μ i j ℓ +
        ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) * numL m p' p μ i j ℓ + numQ m p' p μ i j ℓ) := by
  rw [← longitudinal_apply, ← sum_lower_smul]
  simp only [vertexChain, Matrix.smul_apply, smul_eq_mul, kap]

/-- `d(k) = (Λ² - m_γ²) D_{m_γ}⁻¹ D_Λ⁻¹`. -/
theorem photonScalar_eq_prod (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) (ℓ : Fin 4 → ℝ) :
    photonScalar mγ Λ ε ℓ = ((Λ ^ 2 - mγ ^ 2 : ℝ) : ℂ) * (denom mγ ε ℓ)⁻¹ * (denom Λ ε ℓ)⁻¹ := by
  have ha := denom_ne_zero_of_pos (M := mγ) hε ℓ
  have hb := denom_ne_zero_of_pos (M := Λ) hε ℓ
  have e : photonScalar mγ Λ ε ℓ = (denom mγ ε ℓ)⁻¹ - (denom Λ ε ℓ)⁻¹ := rfl
  rw [e]
  field_simp
  simp only [denom]
  push_cast
  ring

/-! ### The decomposition of an entry -/

/-- **An entry of the bubble–bubble vertex as nine pieces**, at `ε > 0`. -/
theorem bbEntry_eq (P : Params) {ε : ℝ} (hε : 0 < ε) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)
    (ℓ : Fin 4 → ℝ) :
    vertexChain P.e μ (electronPropagator P.m ε (p' + ℓ)) (electronPropagator P.m ε (p + ℓ))
        (bbInsertion P ε ℓ) i j =
      kap P.e * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 3 : ℝ) : ℂ) *
        ∑ n, bbCoef P ε n * bbPiece P p' p μ i j ε n ℓ := by
  set s : ℂ := ((Minkowski.dot ℓ ℓ : ℝ) : ℂ)
  set Pi := vpLoopEps P ε (Minkowski.dot ℓ ℓ)
  set Sx := vpExtraEps P ε (Minkowski.dot ℓ ℓ)
  set d := photonScalar P.mγ P.Λ ε ℓ
  set X : ℂ := Pi ^ 2 * s ^ 2 - 2 * I * ε * Pi * Sx * s - (ε : ℂ) ^ 2 * Sx ^ 2
  set Ψ : ℂ := Pi ^ 2 * s - 2 * I * ε * Pi * Sx
  have hI : bbInsertion P ε ℓ = fun ν ρ => (d ^ 3 * X) * gPhoton ν ρ +
      (d ^ 3 * -Ψ) * (((Minkowski.lower ℓ ν : ℝ) : ℂ) * ((Minkowski.lower ℓ ρ : ℝ) : ℂ)) := by
    funext ν ρ
    rw [bbInsertion_split]
    simp only [X, Ψ, s, Pi, Sx, d]
    ring
  rw [hI, QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul,
    QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul, vertexChain_smul_out,
    vertexChain_smul_in, vertexChain_add_photon, vertexChain_smul_photon,
    vertexChain_smul_photon]
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  rw [vertexChain_gPhoton_apply, vertexChain_lower_apply]
  -- the scalar algebra
  have hPi := vpLoopEps_eq_gSpec P hε (Minkowski.dot ℓ ℓ)
  have hSx := vpExtraEps_eq_gSpec P hε (Minkowski.dot ℓ ℓ)
  have hd := photonScalar_eq_prod P.mγ P.Λ hε ℓ
  simp only [X, Ψ, d, Pi, Sx] at *
  rw [hPi, hSx, hd, propDenom_eq_denom, propDenom_eq_denom]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, bbCoef, bbPiece, ggInt, powInt, prodIntegrand,
    ms6, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  push_cast
  ring

/-! ### Each piece converges -/

theorem norm_wOne_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : ‖wOne x‖ ≤ 1 := by
  have a1 := hx.1
  have a2 := hx.2
  have a3 : x ^ 2 ≤ 1 := by nlinarith
  have a4 : x ^ 3 ≤ 1 := by nlinarith
  have a5 : 0 ≤ x ^ 3 := by positivity
  have a6 : 0 ≤ x ^ 2 := by positivity
  rw [wOne, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

theorem norm_wId_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : ‖wId x‖ ≤ 1 := by
  rw [wId, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
  exact hx.2.le

theorem measurable_wOne : Measurable wOne := by
  unfold wOne
  exact Complex.measurable_ofReal.comp (by fun_prop)

theorem measurable_wId : Measurable wId := Complex.measurable_ofReal

/-- **Each piece converges as `ε → 0⁺` and is integrable at `ε ∈ (0, 1]`.** -/
theorem ggInt_ok {P : Params} (hA : QED.ChainProof.ChainAdmissible P) {p' p : Fin 4 → ℝ}
    (hpq : QED.ChainProof.IsPairQ P.m p' p) {N : (Fin 4 → ℝ) → ℂ} (hN : QuadN N) {j : ℕ}
    (hj : j ≤ 2) (a₁ a₂ : ℂ) {w₁ w₂ : ℝ → ℂ} (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    (hW₁ : ∀ x ∈ Ioo (0 : ℝ) 1, ‖w₁ x‖ ≤ 1) (hW₂ : ∀ x ∈ Ioo (0 : ℝ) 1, ‖w₂ x‖ ≤ 1) :
    (∃ L : ℂ, Tendsto (fun ε => energyFirstIntegral (ggInt P N (ms6 P) j a₁ a₂ w₁ w₂ ε p' p))
      (𝓝[>] 0) (𝓝 L)) ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → EFInt (ggInt P N (ms6 P) j a₁ a₂ w₁ w₂ ε p' p) := by
  obtain ⟨hp', hp, hp0', hp0, -⟩ := hpq
  obtain ⟨hNc, ⟨α, hNq⟩, ⟨CN, hNb⟩⟩ := hN
  set M₀ := min (min P.mγ P.Λ) P.m
  have hM₀ : 0 < M₀ := lt_min (lt_min hA.hmγ hA.hΛ) hA.hm
  have hM₀m : M₀ ≤ P.m := min_le_right _ _
  have ha : M₀ ≤ P.mγ := (min_le_left _ _).trans (min_le_left _ _)
  have hb : M₀ ≤ P.Λ := (min_le_left _ _).trans (min_le_right _ _)
  have hMs : ∀ i, M₀ ≤ ms6 P i := fun i => by fin_cases i <;> simp [ms6, ha, hb]
  refine ⟨⟨_, tendsto_efi_ggInt hA.hm hA.hM₁ hA.hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 hNc hNq hNb
    (by omega) a₁ a₂ hw₁ hw₂ hW₁ hW₂⟩, fun ε hε hε1 => ?_⟩
  exact (efi_ggInt_eq hA.hm hA.hM₁ hA.hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0 hNc hNq hNb (by omega)
    a₁ a₂ hw₁ hw₂ hW₁ hW₂ hε hε1).1

theorem bbPiece_ok {P : Params} (hA : QED.ChainProof.ChainAdmissible P) {p' p : Fin 4 → ℝ}
    (hpq : QED.ChainProof.IsPairQ P.m p' p) (μ i j : Fin 4) (n : Fin 9) :
    (∃ L : ℂ, Tendsto (fun ε => energyFirstIntegral (bbPiece P p' p μ i j ε n)) (𝓝[>] 0)
      (𝓝 L)) ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → EFInt (bbPiece P p' p μ i j ε n) := by
  have o := fun x (hx : x ∈ Ioo (0 : ℝ) 1) => norm_wOne_le hx
  have d := fun x (hx : x ∈ Ioo (0 : ℝ) 1) => norm_wId_le hx
  fin_cases n
  · exact ggInt_ok hA hpq (quadN_numG _ _ _ _ _ _) (by norm_num) _ _ measurable_wOne
      measurable_wOne o o
  · exact ggInt_ok hA hpq (quadN_numG _ _ _ _ _ _) (by norm_num) _ _ measurable_wOne
      measurable_wId o d
  · exact ggInt_ok hA hpq (quadN_numG _ _ _ _ _ _) (by norm_num) _ _ measurable_wId
      measurable_wId d d
  · exact ggInt_ok hA hpq (quadN_numS _ _ _) (by norm_num) _ _ measurable_wOne measurable_wOne o o
  · exact ggInt_ok hA hpq (quadN_numS _ _ _) (by norm_num) _ _ measurable_wOne measurable_wId o d
  · exact ggInt_ok hA hpq (quadN_numL _ _ _ _ _ _) (by norm_num) _ _ measurable_wOne
      measurable_wOne o o
  · exact ggInt_ok hA hpq (quadN_numL _ _ _ _ _ _) (by norm_num) _ _ measurable_wOne
      measurable_wId o d
  · exact ggInt_ok hA hpq (quadN_numQ _ _ _ _ _ _) (by norm_num) _ _ measurable_wOne
      measurable_wOne o o
  · exact ggInt_ok hA hpq (quadN_numQ _ _ _ _ _ _) (by norm_num) _ _ measurable_wOne
      measurable_wId o d

theorem continuous_bbCoef (P : Params) (n : Fin 9) : Continuous fun ε : ℝ => bbCoef P ε n := by
  fin_cases n <;> simp only [bbCoef] <;> fun_prop

/-! ### The limit -/

/-- **The `ε → 0⁺` limit of the one-loop vertex with the double insertion exists**, entrywise
(`QED.ChainProof.HCBB.BBInsertionLimit`). -/
theorem bbInsertionLimit : BBInsertionLimit := by
  intro P hA p' p hpq α β μ
  have h := bbPiece_ok hA hpq μ α β
  choose L hL using fun n => (h n).1
  have hI := fun n => (h n).2
  set c := kap P.e * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 3 : ℝ) : ℂ)
  refine ⟨c * ∑ n, bbCoef P 0 n * L n, ?_⟩
  have hlim : Tendsto (fun ε => c * ∑ n, bbCoef P ε n *
      energyFirstIntegral (bbPiece P p' p μ α β ε n)) (𝓝[>] 0)
      (𝓝 (c * ∑ n, bbCoef P 0 n * L n)) :=
    tendsto_const_nhds.mul (tendsto_finsetSum _ fun n _ =>
      (((continuous_bbCoef P n).tendsto 0).mono_left nhdsWithin_le_nhds).mul (hL n))
  refine hlim.congr' ?_
  filter_upwards [ev_pos_le_one] with ε ⟨hε, hε1⟩
  have e : (fun ℓ => vertexChain P.e μ (electronPropagator P.m ε (p' + ℓ))
      (electronPropagator P.m ε (p + ℓ)) (bbInsertion P ε ℓ) α β) =
      fun ℓ => c * ∑ n, bbCoef P ε n * bbPiece P p' p μ α β ε n ℓ :=
    funext fun ℓ => bbEntry_eq P hε p' p μ α β ℓ
  rw [e, efi_const_mul, efi_sum _ fun n _ => (hI n ε hε hε1).const_mul _]
  simp only [efi_const_mul]

/-- **`RepLimit repBB`** from the three-loop integrability `BBJointIntegrable` (the transport of
(HC₀) for `repBB`; hypothesis). -/
theorem repLimit_repBB (hF : BBJointIntegrable) :
    QED.ChainProof.HCLimit.RepLimit QED.ChainProof.Enum.repBB :=
  repLimit_repBB_of hF bbInsertionLimit

end QED.ChainProof.HCBB2

end
