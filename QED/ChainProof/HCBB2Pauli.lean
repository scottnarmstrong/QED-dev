/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCBB2Limit
public import QED.ChainProof.HCBBPauli
public import QED.ChainProof.HCSideLinks

/-!
# The Pauli projection of the bubble–bubble limit, and the `repBB` links

Helper level, Phase 5 Stage 1a, toward the nested value `QED.ChainProof.HCBB.BBNestedAt` of the
bubble–bubble class. With the entrywise limit of `QED/ChainProof/HCBB2Limit.lean`:

* `efInt_bbEntry`: every entry of the one-loop vertex with the double insertion is integrable
  in both stages at `ε ∈ (0, 1]`.
* `pauliNum_bb_eq`: at `ε > 0`, the Pauli numerator of the vertex is
  `(Λ² - m_γ²)³ (c₁² T₀ - 2iε c₁ c₂ T₁ - ε² c₂² T₂)`, three pieces `QED.ChainProof.HCBB2.ggInt`
  with numerator the Pauli-projected chain `pauliChain`.
* `tendsto_efi_pauliNum_bb`: it tends to `bbPauliLimit = (Λ² - m_γ²)³ c₁² ggLimit(Pg, 2, Π̂, Π̂)`,
  an explicit closed form in the engine limits (`powLimit`, `specLimit`) with spectral
  integrals over `(0, 1]` and `(0, 1]²`.
* **`pauliNum_of_bbLim`**: every limit `Y` (`QED.ChainProof.HCBB.BBLim`) has
  `pauliNum Y = (1/i) bbPauliLimit`.
* **`bbNestedAt_of_value`**: `BBNestedAt` from the `ε`-free value identity `BBPauliValue`
  (`bbPauliLimit` at the canonical pair is the one-loop Pauli functional of
  `enumPhoton 0 = Π_loop² s² D³`), which is **not proved here**.
* `repNested_repBB_of`, `repCov_repBB_of`: `RepNested repBB (enumPhoton 0)` and `RepCov repBB`
  (inputs of `QED.ChainProof.HCSide.classLinks_of_reps`) from `BBJointIntegrable` and
  `BBNestedAt`, resp. `BBCov`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Matrix
open scoped Real

namespace QED.ChainProof.HCBB2

open QED.OneLoop QED.OneLoop.VertexLimit QED.WickModel QED.Integration
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtAssembly
open QED.TwoLoop.VPHalfAt QED.TwoLoop.VPHalfAtGen QED.TwoLoop.Insertion QED.TwoLoop.Bridge
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZero
open QED.ChainProof.HCBB QED.ChainProof.HCValue QED.ChainProof.HCSide

/-! ### Integrability of the entries -/

theorem efInt_bbEntry {P : Params} (hA : QED.ChainProof.ChainAdmissible P) {p' p : Fin 4 → ℝ}
    (hpq : QED.ChainProof.IsPairQ P.m p' p) (μ i j : Fin 4) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    EFInt fun ℓ => vertexChain P.e μ (electronPropagator P.m ε (p' + ℓ))
      (electronPropagator P.m ε (p + ℓ)) (bbInsertion P ε ℓ) i j := by
  have e : (fun ℓ => vertexChain P.e μ (electronPropagator P.m ε (p' + ℓ))
      (electronPropagator P.m ε (p + ℓ)) (bbInsertion P ε ℓ) i j) =
      fun ℓ => kap P.e * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 3 : ℝ) : ℂ) *
        ∑ n, bbCoef P ε n * bbPiece P p' p μ i j ε n ℓ :=
    funext fun ℓ => bbEntry_eq P hε p' p μ i j ℓ
  rw [e]
  exact (EFInt.sum _ fun n _ =>
    ((bbPiece_ok hA hpq μ i j n).2 ε hε hε1).const_mul _).const_mul _

/-! ### The Pauli numerator -/

/-- The three Pauli-projected pieces. -/
noncomputable def pPiece (P : Params) (p' p : Fin 4 → ℝ) (ε : ℝ) : Fin 3 → (Fin 4 → ℝ) → ℂ :=
  ![ggInt P (pauliChain P.e P.m p' p) (ms6 P) 2 (1 / 6) (1 / 6) wOne wOne ε p' p,
    ggInt P (pauliChain P.e P.m p' p) (ms6 P) 1 (1 / 6) 1 wOne wId ε p' p,
    ggInt P (pauliChain P.e P.m p' p) (ms6 P) 0 1 1 wId wId ε p' p]

/-- Their coefficients. -/
noncomputable def pCoef (P : Params) (ε : ℝ) : Fin 3 → ℂ :=
  ![cOne P ^ 2, -(2 * I * (ε : ℂ) * cOne P * cTwo P), -((ε : ℂ) ^ 2 * cTwo P ^ 2)]

/-- **The Pauli numerator of the bubble–bubble vertex as three pieces**, at `ε > 0`. -/
theorem pauliNum_bb_eq (P : Params) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
    (hm : P.m ≠ 0) {ε : ℝ} (hε : 0 < ε) (ℓ : Fin 4 → ℝ) :
    pauliNum P.m p' p (fun μ => vertexChain P.e μ (electronPropagator P.m ε (p' + ℓ))
        (electronPropagator P.m ε (p + ℓ)) (bbInsertion P ε ℓ)) =
      (((P.Λ ^ 2 - P.mγ ^ 2) ^ 3 : ℝ) : ℂ) * ∑ n, pCoef P ε n * pPiece P p' p ε n ℓ := by
  rw [pauliNum_bbVertex_split P hp' hp hq hm ε ℓ, vpLoopEps_eq_gSpec P hε,
    vpExtraEps_eq_gSpec P hε, photonScalar_eq_prod P.mγ P.Λ hε ℓ, propDenom_eq_denom,
    propDenom_eq_denom]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, pCoef, pPiece, ggInt, powInt, prodIntegrand,
    ms6, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  push_cast
  ring

/-- **The explicit `ε → 0⁺` limit of the Pauli numerator**:
`(Λ² - m_γ²)³ c₁² ggLimit(Pg, 2, Π̂, Π̂)` on the six photon-type denominators of `d³`. -/
noncomputable def bbPauliLimit (P : Params) (p' p : Fin 4 → ℝ) : ℂ :=
  (((P.Λ ^ 2 - P.mγ ^ 2) ^ 3 : ℝ) : ℂ) * cOne P ^ 2 *
    ggLimit P (Classical.choose (pauliChain_quadratic P.e P.m p' p)) (pauliChain P.e P.m p' p)
      (ms6 P) 2 (1 / 6) (1 / 6) wOne wOne p' p

theorem continuous_pCoef (P : Params) (n : Fin 3) : Continuous fun ε : ℝ => pCoef P ε n := by
  fin_cases n <;> simp only [pCoef] <;> fun_prop

/-- **The `ε → 0⁺` limit of the Pauli numerator.** -/
theorem tendsto_efi_pauliNum_bb {P : Params} (hA : QED.ChainProof.ChainAdmissible P)
    {p' p : Fin 4 → ℝ} (hpq : QED.ChainProof.IsPairQ P.m p' p) :
    Tendsto (fun ε => energyFirstIntegral fun ℓ =>
        pauliNum P.m p' p (fun μ => vertexChain P.e μ (electronPropagator P.m ε (p' + ℓ))
          (electronPropagator P.m ε (p + ℓ)) (bbInsertion P ε ℓ))) (𝓝[>] 0)
      (𝓝 (bbPauliLimit P p' p)) := by
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hpq : QED.ChainProof.IsPairQ P.m p' p := ⟨hp', hp, hp0', hp0, hq⟩
  have hQ : QuadN (pauliChain P.e P.m p' p) :=
    ⟨continuous_pauliChain P.e P.m p' p, pauliChain_quadratic P.e P.m p' p,
      pauliChain_bound P.e P.m p' p⟩
  have o := fun x (hx : x ∈ Ioo (0 : ℝ) 1) => norm_wOne_le hx
  have d := fun x (hx : x ∈ Ioo (0 : ℝ) 1) => norm_wId_le hx
  -- the leading piece, with its explicit limit
  set α := Classical.choose (pauliChain_quadratic P.e P.m p' p)
  have hα := Classical.choose_spec (pauliChain_quadratic P.e P.m p' p)
  obtain ⟨CN, hCN⟩ := pauliChain_bound P.e P.m p' p
  set M₀ := min (min P.mγ P.Λ) P.m
  have hM₀ : 0 < M₀ := lt_min (lt_min hA.hmγ hA.hΛ) hA.hm
  have hM₀m : M₀ ≤ P.m := min_le_right _ _
  have ha : M₀ ≤ P.mγ := (min_le_left _ _).trans (min_le_left _ _)
  have hb : M₀ ≤ P.Λ := (min_le_left _ _).trans (min_le_right _ _)
  have hMs : ∀ i, M₀ ≤ ms6 P i := fun i => by fin_cases i <;> simp [ms6, ha, hb]
  have T0 := tendsto_efi_ggInt hA.hm hA.hM₁ hA.hM₂ hM₀ hM₀m hMs hp' hp hp0' hp0
    (continuous_pauliChain P.e P.m p' p) hα hCN (j := 2) (by norm_num) (1 / 6) (1 / 6)
    measurable_wOne measurable_wOne o o
  obtain ⟨⟨L1, T1⟩, i1⟩ := ggInt_ok hA hpq hQ (j := 1) (by norm_num) (1 / 6) 1 measurable_wOne
    measurable_wId o d
  obtain ⟨⟨L2, T2⟩, i2⟩ := ggInt_ok hA hpq hQ (j := 0) (by norm_num) 1 1 measurable_wId
    measurable_wId d d
  obtain ⟨-, i0⟩ := ggInt_ok hA hpq hQ (j := 2) (by norm_num) (1 / 6) (1 / 6) measurable_wOne
    measurable_wOne o o
  set c := (((P.Λ ^ 2 - P.mγ ^ 2) ^ 3 : ℝ) : ℂ)
  set L : Fin 3 → ℂ := ![ggLimit P α (pauliChain P.e P.m p' p) (ms6 P) 2 (1 / 6) (1 / 6) wOne
    wOne p' p, L1, L2]
  have hL : ∀ n, Tendsto (fun ε => energyFirstIntegral (pPiece P p' p ε n)) (𝓝[>] 0)
      (𝓝 (L n)) := fun n => by fin_cases n <;> assumption
  have hI : ∀ n, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → EFInt (pPiece P p' p ε n) := fun n => by
    fin_cases n <;> assumption
  have hlim : Tendsto (fun ε => c * ∑ n, pCoef P ε n * energyFirstIntegral (pPiece P p' p ε n))
      (𝓝[>] 0) (𝓝 (c * ∑ n, pCoef P 0 n * L n)) :=
    tendsto_const_nhds.mul (tendsto_finsetSum _ fun n _ =>
      (((continuous_pCoef P n).tendsto 0).mono_left nhdsWithin_le_nhds).mul (hL n))
  have hv : c * ∑ n, pCoef P 0 n * L n = bbPauliLimit P p' p := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, pCoef, L, bbPauliLimit, c,
      Matrix.cons_val_zero, Matrix.cons_val_succ, α]
    push_cast
    ring
  rw [← hv]
  refine hlim.congr' ?_
  filter_upwards [ev_pos_le_one] with ε ⟨hε, hε1⟩
  have e : (fun ℓ => pauliNum P.m p' p (fun μ => vertexChain P.e μ
      (electronPropagator P.m ε (p' + ℓ)) (electronPropagator P.m ε (p + ℓ))
      (bbInsertion P ε ℓ))) = fun ℓ => c * ∑ n, pCoef P ε n * pPiece P p' p ε n ℓ :=
    funext fun ℓ => pauliNum_bb_eq P hp' hp hq hA.hm.ne' hε ℓ
  rw [e, efi_const_mul, efi_sum _ fun n _ => (hI n ε hε hε1).const_mul _]
  simp only [efi_const_mul]

/-- **The Pauli numerator of every bubble–bubble limit**: `pauliNum Y = (1/i) bbPauliLimit`. -/
theorem pauliNum_of_bbLim {P : Params} (hA : QED.ChainProof.ChainAdmissible P)
    {p' p : Fin 4 → ℝ} (hpq : QED.ChainProof.IsPairQ P.m p' p)
    {Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hY : BBLim P p' p Y) :
    pauliNum P.m p' p Y = (1 / I) * bbPauliLimit P p' p := by
  have hT := (tendsto_efi_pauliNum_bb hA hpq).const_mul (1 / I)
  refine tendsto_nhds_unique ?_ hT
  have hsum : Tendsto (fun ε => ∑ j : Idx, pauliWt P.m p' p j.1 j.2.1 j.2.2 *
      ((1 / I) * energyFirstIntegral fun k =>
        vertexChain P.e j.1 (electronPropagator P.m ε (p' + k))
          (electronPropagator P.m ε (p + k)) (bbInsertion P ε k) j.2.1 j.2.2)) (𝓝[>] 0)
      (𝓝 (pauliNum P.m p' p Y)) := by
    rw [pauliNum_eq_sum_idx]
    exact tendsto_finsetSum _ fun j _ => (hY j.1 j.2.1 j.2.2).const_mul _
  refine hsum.congr' ?_
  filter_upwards [ev_pos_le_one] with ε ⟨hε, hε1⟩
  have hI : ∀ j : Idx, EFInt fun k => pauliWt P.m p' p j.1 j.2.1 j.2.2 *
      vertexChain P.e j.1 (electronPropagator P.m ε (p' + k))
        (electronPropagator P.m ε (p + k)) (bbInsertion P ε k) j.2.1 j.2.2 := fun j =>
    (efInt_bbEntry hA hpq j.1 j.2.1 j.2.2 hε hε1).const_mul _
  have e : (fun k => pauliNum P.m p' p (fun μ => vertexChain P.e μ
      (electronPropagator P.m ε (p' + k)) (electronPropagator P.m ε (p + k))
      (bbInsertion P ε k))) = fun k => ∑ j : Idx, pauliWt P.m p' p j.1 j.2.1 j.2.2 *
        vertexChain P.e j.1 (electronPropagator P.m ε (p' + k))
          (electronPropagator P.m ε (p + k)) (bbInsertion P ε k) j.2.1 j.2.2 :=
    funext fun k => pauliNum_eq_sum_idx _ _ _ _
  rw [e, efi_sum _ fun j _ => hI j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [efi_const_mul]
  ring

/-! ### The nested value, reduced to an `ε`-free identity -/

/-- **The value identity of the bubble–bubble class** (`ε`-free; **not proved here**): at
admissible parameters, for all small `Q > 0`, the explicit limit `bbPauliLimit` at the canonical
pair is the one-loop Pauli functional of the photon function `enumPhoton 0 P = Π_loop² s² D³`. -/
def BBPauliValue : Prop :=
  ∀ P : Params, QED.ChainProof.ChainAdmissible P → ∀ᶠ Q in 𝓝[>] (0 : ℝ),
    bbPauliLimit P (boostMomentum P.m Q) (restMomentum P.m) =
      pauliConst P.e P.m Q * ((P.e ^ 2 / (8 * π ^ 2) * ∫ z, 2 * (z.2 ^ 2 * P.m ^ 2 *
        enumPhoton 0 P (QED.TwoLoop.VPHalf.vpK P.m Q z)) ∂feynmanMeasure : ℝ) : ℂ)

/-- **`BBNestedAt` from the value identity.** -/
theorem bbNestedAt_of_value (hV : BBPauliValue) : BBNestedAt := by
  intro P hA
  filter_upwards [hV P hA, self_mem_nhdsWithin] with Q hQV (hQ : 0 < Q)
  intro Y hY
  have hpq := QED.ChainProof.HCValue.isPairQ_canonical' hA.hm hQ
  refine formFactorProj₂_of_pauliNum hA.he hA.hm hQ
    (dot_boostMomentum_sub_restMomentum hA.hm hQ.le) ?_
  rw [pauliNum_of_bbLim hA hpq hY, hQV]

/-! ### The `repBB` inputs of `classLinks_of_reps` -/

/-- **`RepNested repBB (enumPhoton 0)`** from `BBJointIntegrable` and `BBNestedAt`. -/
theorem repNested_repBB_of (hF : BBJointIntegrable) (hN : BBNestedAt) :
    RepNested QED.ChainProof.Enum.repBB (fun P => enumPhoton 0 P) :=
  fun P hA => classNestedAt_zero_of hF hN P hA

/-- **`RepCov repBB`** from `BBJointIntegrable` and `BBCov`. -/
theorem repCov_repBB_of (hF : BBJointIntegrable) (hC : BBCov) :
    RepCov QED.ChainProof.Enum.repBB :=
  fun P hA L S T h p' p hpq h0 h1 Y Z hY hZ μ =>
    classCov_zero_of hF hC P hA L S T h p' p hpq h0 h1 Y Z hY hZ μ

/-- The three `repBB` inputs of `classLinks_of_reps`, from `BBJointIntegrable`, the value identity
`BBPauliValue` and `BBCov`. -/
theorem repBB_links_of (hF : BBJointIntegrable) (hV : BBPauliValue) (hC : BBCov) :
    QED.ChainProof.HCLimit.RepLimit QED.ChainProof.Enum.repBB ∧
      RepNested QED.ChainProof.Enum.repBB (fun P => enumPhoton 0 P) ∧
      RepCov QED.ChainProof.Enum.repBB :=
  ⟨repLimit_repBB hF, repNested_repBB_of hF (bbNestedAt_of_value hV), repCov_repBB_of hF hC⟩

end QED.ChainProof.HCBB2

end
