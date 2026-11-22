/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCPauliMainSharp
public import QED.ChainProof.SetCMainDKLink

/-!
# Set (c): the longitudinal parts of the `repD` classes are `♯`-odd

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The limits of
the longitudinal part of `repD i t` are `wKD · kCst · σ` times a combination of parametric
values of the terms `kNum` (`QED.ChainProof.SetCMain.hasLimJ_dKUnit_int`, `hasLimJ_dKUnit_ext`).
Every factor of a term is `♯`-fixed (`γ^μ`, `q̸`, `1`, electron numerators, real metric
weights), so its parametric values are `♯`-fixed
(`QED.GradedProof.V5Zero.Sharp.sharp_eq_smul_of_isParamValue_vertex`); the constant `kCst` is
real and `wKD` is imaginary, so the limit is `♯`-odd.

* `sharp_kSlotM`, `sharp_kEK`, **`sharp_kNum`**: the terms are `♯`-fixed;
* `conj_kCst`, `conj_wKD`: `kCst` is real, `wKD` imaginary;
* **`dkSharpLink`**: `DKSharpLink P₀ i t` for all 24 classes;
* **`isFormFactorPair_vertexSetC_pauli_limit_of_repBSharp`**: (HS₆) with the `♯`-law of the
  `repD` classes discharged.
-/

@[expose] public section

open Complex Matrix Filter Topology
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetCMain

open QED.TwoLoop.Enumeration QED.ChainProof.SetCUnitM QED.TwoLoop.LimitCovariance
open QED.ChainProof.SetCPauli.CB01 (HasLimJ)
open QED.ChainProof.SetCPauli
open QED.ChainProof.SetAPauli (regParams regFlavors)
open QED.GradedProof.SE2Real (sharp sharp_add sharp_sub sharp_smul sharp_one sharp_slash
  sharp_gamma sharp_sum sharp_neg)
open QED.GradedProof.V5Zero.Sharp (sharp_eq_smul_of_isParamValue_vertex sharp_electronNumerator
  sharp_openChain conj_twoLoopNorm)
open QED.Dirac (gamma slash)

/-! ### The terms are `♯`-fixed -/

theorem sharp_kSlotM (c : Class5) (σ : Fin 8) (m : ℝ) (p p' : Fin 4 → ℝ) (X : KSlot)
    (ℓ : Fin 2 → Fin 4 → ℝ) : sharp (kSlotM c σ m p p' X ℓ) = kSlotM c σ m p p' X ℓ := by
  have h2 : starRingEnd ℂ (2 * (m : ℂ)) = 2 * (m : ℂ) := by
    rw [map_mul, Complex.conj_ofReal, map_ofNat]
  cases X
  · exact sharp_one
  · exact sharp_slash _
  · simp only [kSlotM, sharp_sub, sharp_smul, h2, sharp_one, sharp_electronNumerator]
  · simp only [kSlotM, sharp_sub, sharp_smul, h2, sharp_one, sharp_electronNumerator]

theorem sharp_kEK (c : Class5) (σ : Fin 8) (m : ℝ) (p p' : Fin 4 → ℝ) (K : Finset (Fin 4))
    (j : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    sharp (kEK c σ m p p' K j ℓ) = kEK c σ m p p' K j ℓ := by
  unfold kEK
  split_ifs
  · exact sharp_electronNumerator _ _
  · exact sharp_one

/-- **The terms are `♯`-fixed.** -/
theorem sharp_kNum (π : Equiv.Perm (Fin 5)) (c : Class5) (σ : Fin 8) (m : ℝ)
    (p p' : Fin 4 → ℝ) (X Y : KSlot) (K : Finset (Fin 4)) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    sharp (kNum π c σ m p p' X Y K μ ℓ) = kNum π c σ m p p' X Y K μ ℓ := by
  unfold kNum kOpen ocW
  rw [sharp_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [sharp_smul, Complex.conj_ofReal]
  congr 1
  refine sharp_openChain (fun t => ?_) (fun j => sharp_kEK c σ m p p' K j ℓ)
  generalize π.symm t = u
  fin_cases u
  · exact sharp_gamma μ
  · exact sharp_kSlotM c σ m p p' X ℓ
  · exact sharp_kSlotM c σ m p p' Y ℓ
  · exact sharp_gamma z
  · exact sharp_gamma z

/-! ### The constants -/

theorem conj_kCst (R : Params) : starRingEnd ℂ (kCst R) = kCst R := by
  simp only [kCst, map_mul, map_pow, map_div₀, map_one, Complex.conj_I, Complex.conj_ofReal,
    conj_twoLoopNorm]
  ring

theorem conj_wKD (R : Params) (δ₃ : ℝ) : starRingEnd ℂ (wKD R δ₃) = -wKD R δ₃ := by
  simp only [wKD, map_mul, map_pow, map_div₀, map_one, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal]
  ring

/-! ### The limits -/

/-- The parametric values of a term are `♯`-fixed. -/
theorem sharp_of_paramValue_kNum {D : ParamData} (π : Equiv.Perm (Fin 5)) (c : Class5)
    (σ : Fin 8) (m : ℝ) (p p' : Fin 4 → ℝ) (X Y : KSlot) (K : Finset (Fin 4))
    {w : Fin 4 → Fin 4 → Fin 4 → ℂ}
    (hw : ∀ μ a b, IsParamValue D (fun ℓ => kNum π c σ m p p' X Y K μ ℓ a b) (w μ a b))
    (μ : Fin 4) : sharp (Matrix.of (w μ)) = Matrix.of (w μ) := by
  have h := sharp_eq_smul_of_isParamValue_vertex (D := D)
    (fun μ ℓ => kNum π c σ m p p' X Y K μ ℓ) (fun μ => Matrix.of (w μ)) 1
    (fun μ ℓ => by rw [one_smul]; exact sharp_kNum π c σ m p p' X Y K μ ℓ) hw μ
  rwa [one_smul] at h

theorem sharp_eq_neg_of_smul {Y W : Matrix (Fin 4) (Fin 4) ℂ} {a : ℂ}
    (ha : starRingEnd ℂ a = -a) (hW : sharp W = W) (hY : Y = a • W) : sharp Y = -Y := by
  rw [hY, sharp_smul, ha, hW, neg_smul]

theorem conj_wKD_mul_kCst (R : Params) (δ₃ : ℝ) (x : ℝ) :
    starRingEnd ℂ (wKD R δ₃ * (kCst R * (x : ℂ))) = -(wKD R δ₃ * (kCst R * (x : ℂ))) := by
  rw [map_mul, map_mul, conj_wKD, conj_kCst, Complex.conj_ofReal, neg_mul]

/-- **The longitudinal part of `repD i t` is `♯`-odd**: `DKSharpLink P₀ i t` for all 24
classes. -/
theorem dkSharpLink (P₀ : Params) (i : Fin 12) (t : Fin 2) : DKSharpLink P₀ i t := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq Y hY μ
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  set R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ
  set δ₃ := P₀.e ^ 2 * (shareCt D s).d₃ 0
  rcases kWard_cases i with ⟨j, hj⟩ | hW
  · choose w₁ w₂ hw₁ hw₂ hl using
      hasLimJ_dKUnit_int i t R hm hγ hγΛ p p' hp hp' hq.le j hj
    refine sharp_eq_neg_of_smul (conj_wKD_mul_kCst R δ₃ ((kSgnW i : ℤ) : ℝ))
      (W := Matrix.of (w₁ μ) - Matrix.of (w₂ μ)) ?_ ?_
    · rw [sharp_sub, sharp_of_paramValue_kNum _ _ _ _ _ _ _ _ _ hw₁,
        sharp_of_paramValue_kNum _ _ _ _ _ _ _ _ _ hw₂]
    · ext α β
      rw [tendsto_nhds_unique (hY μ α β) (tendsto_dKValD_of_hasLimJ (hl μ α β))]
      simp
      ring
  · choose w₀ w₁ w₂ w₃ hw₀ hw₁ hw₂ hw₃ hl using
      hasLimJ_dKUnit_ext i t R hm hγ hγΛ p p' hp hp' hq.le hW
    refine sharp_eq_neg_of_smul
      (conj_wKD_mul_kCst R δ₃ (((kSgnW i : ℤ) : ℝ) * ((kSgnO i : ℤ) : ℝ)))
      (W := Matrix.of (w₀ μ) + Matrix.of (w₁ μ) - Matrix.of (w₂ μ) - Matrix.of (w₃ μ)) ?_ ?_
    · rw [sharp_sub, sharp_sub, sharp_add, sharp_of_paramValue_kNum _ _ _ _ _ _ _ _ _ hw₀,
        sharp_of_paramValue_kNum _ _ _ _ _ _ _ _ _ hw₁,
        sharp_of_paramValue_kNum _ _ _ _ _ _ _ _ _ hw₂,
        sharp_of_paramValue_kNum _ _ _ _ _ _ _ _ _ hw₃]
    · ext α β
      rw [tendsto_nhds_unique (hY μ α β) (tendsto_dKValD_of_hasLimJ (hl μ α β))]
      simp
      ring

end QED.ChainProof.SetCMain

namespace QED.ThreeLoop

open QED.ChainProof.SetCPauli (MainIdx ClsPauliVal mainFam SetCClassLim SetCClassCov
  SetCClassPauli SetCClassSharp SetCRegLimitB setCPauliB)

/-- **The remaining interface of set (c), by parts, without the longitudinal `♯`-law**: (HS₆)
from the main-class limit, covariance and Pauli links, the `♯`-law of the twelve `repB` classes,
and the regulator limit of `b = setCPauliB P₀ βᴹ`; the `♯`-law of the longitudinal parts of the
twenty-four `repD` classes is `QED.ChainProof.SetCMain.dkSharpLink`. -/
theorem isFormFactorPair_vertexSetC_pauli_limit_of_repBSharp (P₀ : Params)
    {βM : MainIdx → ClsPauliVal}
    (hM : ∀ r, SetCClassLim mainFam P₀ r) (hMc : ∀ r, SetCClassCov mainFam P₀ r)
    (hPM : ∀ r, SetCClassPauli mainFam P₀ r (βM r))
    (hSB : ∀ i, SetCClassSharp mainFam P₀ (.inl i))
    (hreg : SetCRegLimitB P₀ (setCPauliB P₀ βM))
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2) ∧
        ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2 →
          (∃ s : ℝ × ℝ × ℝ, IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s) ∧
          ∀ s : ℝ × ℝ × ℝ, IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - (a1SixSetC : ℂ)‖ < η :=
  isFormFactorPair_vertexSetC_pauli_limit_of_mainParts P₀ hM hMc hPM hSB
    (QED.ChainProof.SetCMain.dkSharpLink P₀) hreg he hm η hη

end QED.ThreeLoop

end
