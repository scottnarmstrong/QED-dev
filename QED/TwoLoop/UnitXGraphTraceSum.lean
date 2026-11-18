/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXGraph
public import QED.TwoLoop.UnitLGraphTraceSum
import Mathlib.Tactic.Ring

/-!
# The crossed-ladder numerator as Lorentz contractions

Section 8 of `docs/TWO-LOOP-UNITS.md`, the graph half of the X unit. With Wick's rule
(`QED.TwoLoop.ParamNumEval.paramNumOf_elecChain`) the projected crossed numerator of
`QED.TwoLoop.UnitXGraph.openNum_X_eq` is
`N(x, u) = -π⁴ κ ∑_μ ∑_l c_{μ,l} U⁻² (6 ch(Ē) + V chainTwo + ¼ V² chainFour)`. This file

* sums the photon weights: `∑_μ ∑_l c_{μ,l} ch(B_{μ,l}; Y) = η² xw(P; Y)` with
  `η = (1/i)(Λ² - m_γ²)` and the **crossed contraction**
  `xw(P; Y) = ∑_{μνσ} tr(γ^ν P_μ γ^σ Y₀ γ_ν Y₁ γ^μ Y₂ γ_σ Y₃)` (`sum_crossedWeight_ch`);
* defines the three coefficients `T₁, T₂, T₃` of `N = T₁ + T₂ V + T₃ V²` at any point `z` of
  the parameter space (`crossedT1`, `crossedT2`, `crossedT3`, `openNum_X_eq_T`);
* writes them through `xw` (`crossedT1_eq`, `crossedT2_eq`, `crossedT3_eq`):
  `T₁ = -π⁴ κ η² U⁻² · 6 xw(P; Ē)`, `T₂` the six single contractions of slots weighted by
  `C_{kl}`, and `T₃` the three double contractions weighted by `C_{kl} C_{k'l'}`.
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.TwoLoop.UnitXGraph

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Bridge QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraph QED.TwoLoop.UnitLGraphTrace
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (LoopQuartic castLoopMatrix class5LoopMatrixPV symanzikV symanzikU
  symanzikMatrix lineMomentum loopShift)

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### The crossed contraction -/

/-- **The crossed contraction** `∑_{μνσ} tr(γ^ν P_μ γ^σ Y₀ γ_ν Y₁ γ^μ Y₂ γ_σ Y₃)`. -/
noncomputable def xw (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    ℂ :=
  ∑ μ, ∑ ν, ∑ σ, trace (gamma ν * P μ * gamma σ * Y₀ * gammaLower ν * Y₁ * gamma μ * Y₂ *
    gammaLower σ * Y₃)

theorem permX_zero : permX 0 = 2 := rfl
theorem permX_one : permX 1 = 0 := rfl
theorem permX_two : permX 2 = 3 := rfl
theorem permX_three : permX 3 = 1 := rfl
theorem permX_four : permX 4 = 4 := rfl

/-- **The crossed chain sum is the crossed contraction**:
`∑_μ ∑_l c_{μ,l} ch(B_{μ,l}; Y) = η² xw(P; Y)`. -/
theorem sum_crossedWeight_ch (P : Params) (p' p : Fin 4 → ℝ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4)
    (Fin 4) ℂ) :
    ∑ μ, ∑ l : Fin 5 → Fin 4, crossedWeight P μ l * ch (crossedB P.m p' p μ l) Y₀ Y₁ Y₂ Y₃ =
      pvConst P ^ 2 * xw (pauliMat P.m p' p) Y₀ Y₁ Y₂ Y₃ := by
  unfold xw
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [sum_fin5]
  simp only [crossedWeight, crossedB, ch, permX_zero, permX_one, permX_two, permX_three,
    permX_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single μ (fun c _ hc => by simp [kron, hc]) (by simp),
    Finset.sum_eq_single a (fun d _ hd => by simp [pvEta, Minkowski.metric, Ne.symm hd]) (by simp),
    Finset.sum_eq_single b (fun e _ he => by simp [pvEta, Minkowski.metric, Ne.symm he]) (by simp)]
  simp only [kron, ite_true, one_mul, pvEta, pvConst, gammaLower_eq_metric_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  push_cast
  ring

/-! ### The three coefficients of the projected numerator -/

/-- The external momenta of the Pauli–Villars form of the crossed ladder along the curve. -/
noncomputable abbrev crossedMom (P : Params) (u : ℝ) : Fin 8 → Fin 4 → ℝ :=
  pvMomentaE .X (restMomentum P.m) (curveMomentum P.m u)

/-- The four electron numerators of the crossed ladder at the shifted loop momenta, at the
point `z`. -/
noncomputable def crossedE (P : Params) (z : Fin 8 → ℝ) (u : ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  elecAt crossedAlpha (crossedMom P u) (fun _ => P.m) crossedLines (-loopShift crossedAlpha
      (crossedMom P u) z)

/-- The coefficient `T₁` of `V⁰` in the projected crossed numerator, at the point `z`. -/
noncomputable def crossedT1 (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ℂ :=
  -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4, crossedWeight P μ l *
    (((symanzikU crossedAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
      (6 * ch (crossedB P.m (curveMomentum P.m u) (restMomentum P.m) μ l) (crossedE P z u 0)
        (crossedE P z u 1) (crossedE P z u 2) (crossedE P z u 3)))

/-- The coefficient `T₂` of `V¹` in the projected crossed numerator, at the point `z`. -/
noncomputable def crossedT2 (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ℂ :=
  -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4, crossedWeight P μ l *
    (((symanzikU crossedAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
      chainTwo crossedAlpha (crossedB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
        (crossedE P z u) crossedLines (symanzikMatrix crossedAlpha z))

/-- The coefficient `T₃` of `V²` in the projected crossed numerator, at the point `z`. -/
noncomputable def crossedT3 (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ℂ :=
  -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4, crossedWeight P μ l *
    (((symanzikU crossedAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
      (1 / 4 * chainFour crossedAlpha
        (crossedB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
        crossedLines (symanzikMatrix crossedAlpha z)))

/-- **The projected parametric numerator of the crossed ladder, explicit** (Wick's rule). -/
theorem openNum_X_explicit (P : Params) (x : Fin 7 → ℝ) (u : ℝ) :
    openNum .X P x u = -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4,
      crossedWeight P μ l *
        (((symanzikU crossedAlpha (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
          (6 * ch (crossedB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
              (crossedE P (simplexPoint x) u 0) (crossedE P (simplexPoint x) u 1)
              (crossedE P (simplexPoint x) u 2) (crossedE P (simplexPoint x) u 3) +
            chainTwo crossedAlpha (crossedB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
                (crossedE P (simplexPoint x) u) crossedLines
                (symanzikMatrix crossedAlpha (simplexPoint x)) *
              ((symanzikV crossedAlpha (crossedMom P u) (pvMasses P) (simplexPoint x) : ℝ) : ℂ) +
            1 / 4 * chainFour crossedAlpha
                (crossedB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
                crossedLines (symanzikMatrix crossedAlpha (simplexPoint x)) *
              ((symanzikV crossedAlpha (crossedMom P u) (pvMasses P) (simplexPoint x) : ℝ) : ℂ) ^
                2)) := by
  rw [openNum_X_eq]
  simp only [crossedChain, paramNumOf_elecChain, crossedE, crossedMom]
  norm_num [Nat.factorial]

/-- **The projected crossed numerator is `T₁ + T₂ V + T₃ V²`.** -/
theorem openNum_X_eq_T (P : Params) (x : Fin 7 → ℝ) (u : ℝ) :
    openNum .X P x u = crossedT1 P (simplexPoint x) u +
      crossedT2 P (simplexPoint x) u *
        ((symanzikV crossedAlpha (crossedMom P u) (pvMasses P) (simplexPoint x) : ℝ) : ℂ) +
      crossedT3 P (simplexPoint x) u *
        ((symanzikV crossedAlpha (crossedMom P u) (pvMasses P) (simplexPoint x) : ℝ) : ℂ) ^ 2 := by
  rw [openNum_X_explicit]
  simp only [crossedT1, crossedT2, crossedT3, crossedE, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring
  · exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring

/-! ### The coefficients through the crossed contraction -/

section Coeff

variable (P : Params) (p' p : Fin 4 → ℝ)

theorem sum_crossedWeight_sum_ch (Y₀ Y₁ Y₂ Y₃ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ μ, ∑ l : Fin 5 → Fin 4, crossedWeight P μ l *
        ∑ ν, ch (crossedB P.m p' p μ l) (Y₀ ν) (Y₁ ν) (Y₂ ν) (Y₃ ν) =
      pvConst P ^ 2 * ∑ ν, xw (pauliMat P.m p' p) (Y₀ ν) (Y₁ ν) (Y₂ ν) (Y₃ ν) := by
  simp only [Finset.mul_sum]
  rw [sum_sum_sum_comm]
  exact Finset.sum_congr rfl fun ν _ => sum_crossedWeight_ch P p' p _ _ _ _

theorem sum_crossedWeight_sum_sum_ch (Y₀ Y₁ Y₂ Y₃ : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ μ, ∑ l : Fin 5 → Fin 4, crossedWeight P μ l *
        ∑ ν, ∑ ρ, ch (crossedB P.m p' p μ l) (Y₀ ν ρ) (Y₁ ν ρ) (Y₂ ν ρ) (Y₃ ν ρ) =
      pvConst P ^ 2 * ∑ ν, ∑ ρ, xw (pauliMat P.m p' p) (Y₀ ν ρ) (Y₁ ν ρ) (Y₂ ν ρ) (Y₃ ν ρ) := by
  simp only [Finset.mul_sum]
  rw [sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [sum_sum_sum_comm]
  exact Finset.sum_congr rfl fun ρ _ => by rw [← sum_crossedWeight_ch P p']

/-- The contraction coefficient `C_{kl}` of the slots `k, l` of the crossed chain. -/
noncomputable abbrev crossedC (A : Matrix (Fin 2) (Fin 2) ℝ) (k l : Fin 4) : ℂ :=
  (contrC crossedAlpha A (crossedLines k) (crossedLines l) : ℂ)

/-- **The single contractions summed over the photon weights.** -/
theorem sum_crossedWeight_chainTwo (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∑ μ, ∑ l : Fin 5 → Fin 4, crossedWeight P μ l *
        chainTwo crossedAlpha (crossedB P.m p' p μ l) E crossedLines A =
      pvConst P ^ 2 * (crossedC A 0 1 * ∑ ν, xw (pauliMat P.m p' p) (gammaLower ν) (gamma ν) (E 2)
          (E 3) +
        crossedC A 0 2 * ∑ ν, xw (pauliMat P.m p' p) (gammaLower ν) (E 1) (gamma ν) (E 3) +
        crossedC A 0 3 * ∑ ν, xw (pauliMat P.m p' p) (gammaLower ν) (E 1) (E 2) (gamma ν) +
        crossedC A 1 2 * ∑ ν, xw (pauliMat P.m p' p) (E 0) (gammaLower ν) (gamma ν) (E 3) +
        crossedC A 1 3 * ∑ ν, xw (pauliMat P.m p' p) (E 0) (gammaLower ν) (E 2) (gamma ν) +
        crossedC A 2 3 * ∑ ν, xw (pauliMat P.m p' p) (E 0) (E 1) (gammaLower ν) (gamma ν)) := by
  have h : ∀ μ (l : Fin 5 → Fin 4), crossedWeight P μ l *
      chainTwo crossedAlpha (crossedB P.m p' p μ l) E crossedLines A =
      crossedC A 0 1 * (crossedWeight P μ l * ∑ ν, ch (crossedB P.m p' p μ l) (gammaLower ν)
          (gamma ν) (E 2) (E 3)) +
      crossedC A 0 2 * (crossedWeight P μ l * ∑ ν, ch (crossedB P.m p' p μ l) (gammaLower ν) (E 1)
          (gamma ν) (E 3)) +
      crossedC A 0 3 * (crossedWeight P μ l * ∑ ν, ch (crossedB P.m p' p μ l) (gammaLower ν) (E 1)
          (E 2) (gamma ν)) +
      crossedC A 1 2 * (crossedWeight P μ l * ∑ ν, ch (crossedB P.m p' p μ l) (E 0) (gammaLower ν)
          (gamma ν) (E 3)) +
      crossedC A 1 3 * (crossedWeight P μ l * ∑ ν, ch (crossedB P.m p' p μ l) (E 0) (gammaLower ν)
          (E 2) (gamma ν)) +
      crossedC A 2 3 * (crossedWeight P μ l * ∑ ν, ch (crossedB P.m p' p μ l) (E 0) (E 1)
          (gammaLower ν) (gamma ν)) :=
    fun μ l => by
      simp only [chainTwo]
      ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [sum_crossedWeight_sum_ch]
  ring

/-- **The double contractions summed over the photon weights.** -/
theorem sum_crossedWeight_chainFour (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∑ μ, ∑ l : Fin 5 → Fin 4, crossedWeight P μ l *
        chainFour crossedAlpha (crossedB P.m p' p μ l) crossedLines A =
      pvConst P ^ 2 * (crossedC A 0 1 * crossedC A 2 3 * ∑ ν, ∑ ρ,
          xw (pauliMat P.m p' p) (gammaLower ν) (gamma ν) (gammaLower ρ) (gamma ρ) +
        crossedC A 0 2 * crossedC A 1 3 * ∑ ν, ∑ ρ,
          xw (pauliMat P.m p' p) (gammaLower ν) (gammaLower ρ) (gamma ν) (gamma ρ) +
        crossedC A 0 3 * crossedC A 1 2 * ∑ ν, ∑ ρ,
          xw (pauliMat P.m p' p) (gammaLower ν) (gammaLower ρ) (gamma ρ) (gamma ν)) := by
  have h : ∀ μ (l : Fin 5 → Fin 4), crossedWeight P μ l *
      chainFour crossedAlpha (crossedB P.m p' p μ l) crossedLines A =
      crossedC A 0 1 * crossedC A 2 3 * (crossedWeight P μ l * ∑ ν, ∑ ρ,
          ch (crossedB P.m p' p μ l) (gammaLower ν) (gamma ν) (gammaLower ρ) (gamma ρ)) +
      crossedC A 0 2 * crossedC A 1 3 * (crossedWeight P μ l * ∑ ν, ∑ ρ,
          ch (crossedB P.m p' p μ l) (gammaLower ν) (gammaLower ρ) (gamma ν) (gamma ρ)) +
      crossedC A 0 3 * crossedC A 1 2 * (crossedWeight P μ l * ∑ ν, ∑ ρ,
          ch (crossedB P.m p' p μ l) (gammaLower ν) (gammaLower ρ) (gamma ρ) (gamma ν)) :=
    fun μ l => by
      simp only [chainFour]
      ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [sum_crossedWeight_sum_sum_ch]
  ring

end Coeff

section Patterns

variable (P : Params) (z : Fin 8 → ℝ) (u : ℝ)

/-- The momentum of the chain slot `k` at the shifted loop momenta. -/
noncomputable abbrev crossedQ (k : Fin 4) : Fin 4 → ℝ :=
  lineMomentum crossedAlpha (crossedMom P u) (crossedLines k) (-loopShift crossedAlpha
      (crossedMom P u) z)

theorem crossedE_apply (k : Fin 4) :
    crossedE P z u k = electronNumerator P.m (crossedQ P z u k) := rfl

/-- **`T₁` through the crossed contraction**: `T₁ = -π⁴ κ η² U⁻² · 6 xw(P; Ē)`. -/
theorem crossedT1_eq : crossedT1 P z u = ladderK P * ((symanzikU crossedAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
    (6 * xw (ladderPauli P u) (crossedE P z u 0) (crossedE P z u 1) (crossedE P z u 2)
      (crossedE P z u 3)) := by
  have h := sum_crossedWeight_ch P (curveMomentum P.m u) (restMomentum P.m) (crossedE P z u 0)
    (crossedE P z u 1) (crossedE P z u 2) (crossedE P z u 3)
  calc crossedT1 P z u = -((π : ℂ) ^ 4) * ladderConst P *
      (((symanzikU crossedAlpha z ^ 2 : ℝ) : ℂ)⁻¹ * 6 * ∑ μ,
          ∑ l : Fin 5 → Fin 4, crossedWeight P μ l *
        ch (crossedB P.m (curveMomentum P.m u) (restMomentum P.m) μ l) (crossedE P z u 0)
          (crossedE P z u 1) (crossedE P z u 2) (crossedE P z u 3)) := by
        rw [crossedT1]
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring
    _ = _ := by
        rw [h, ladderK]
        ring

/-- **`T₂` through the crossed contraction**: the six single contractions. -/
theorem crossedT2_eq : crossedT2 P z u = ladderK P * ((symanzikU crossedAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
    (crossedC (symanzikMatrix crossedAlpha z) 0 1 *
        ∑ ν, xw (ladderPauli P u) (gammaLower ν) (gamma ν) (crossedE P z u 2) (crossedE P z u 3) +
      crossedC (symanzikMatrix crossedAlpha z) 0 2 *
        ∑ ν, xw (ladderPauli P u) (gammaLower ν) (crossedE P z u 1) (gamma ν) (crossedE P z u 3) +
      crossedC (symanzikMatrix crossedAlpha z) 0 3 *
        ∑ ν, xw (ladderPauli P u) (gammaLower ν) (crossedE P z u 1) (crossedE P z u 2) (gamma ν) +
      crossedC (symanzikMatrix crossedAlpha z) 1 2 *
        ∑ ν, xw (ladderPauli P u) (crossedE P z u 0) (gammaLower ν) (gamma ν) (crossedE P z u 3) +
      crossedC (symanzikMatrix crossedAlpha z) 1 3 *
        ∑ ν, xw (ladderPauli P u) (crossedE P z u 0) (gammaLower ν) (crossedE P z u 2) (gamma ν) +
      crossedC (symanzikMatrix crossedAlpha z) 2 3 *
        ∑ ν, xw (ladderPauli P u) (crossedE P z u 0) (crossedE P z u 1) (gammaLower ν)
          (gamma ν)) := by
  have hT : crossedT2 P z u = -((π : ℂ) ^ 4) * ladderConst P *
      ((symanzikU crossedAlpha z ^ 2 : ℝ) : ℂ)⁻¹ * ∑ μ, ∑ l : Fin 5 → Fin 4, crossedWeight P μ l *
        chainTwo crossedAlpha (crossedB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
          (crossedE P z u) crossedLines (symanzikMatrix crossedAlpha z) := by
    rw [crossedT2]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hT, sum_crossedWeight_chainTwo, ladderK]
  ring

/-- **`T₃` through the crossed contraction**: the three double contractions. -/
theorem crossedT3_eq : crossedT3 P z u = ladderK P * ((symanzikU crossedAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
    (1 / 4 * (crossedC (symanzikMatrix crossedAlpha z) 0 1 *
        crossedC (symanzikMatrix crossedAlpha z) 2 3 * ∑ ν, ∑ ρ,
          xw (ladderPauli P u) (gammaLower ν) (gamma ν) (gammaLower ρ) (gamma ρ) +
      crossedC (symanzikMatrix crossedAlpha z) 0 2 *
        crossedC (symanzikMatrix crossedAlpha z) 1 3 * ∑ ν, ∑ ρ,
          xw (ladderPauli P u) (gammaLower ν) (gammaLower ρ) (gamma ν) (gamma ρ) +
      crossedC (symanzikMatrix crossedAlpha z) 0 3 *
        crossedC (symanzikMatrix crossedAlpha z) 1 2 * ∑ ν, ∑ ρ,
          xw (ladderPauli P u) (gammaLower ν) (gammaLower ρ) (gamma ρ) (gamma ν))) := by
  have hT : crossedT3 P z u = -((π : ℂ) ^ 4) * ladderConst P *
      ((symanzikU crossedAlpha z ^ 2 : ℝ) : ℂ)⁻¹ * (1 / 4) * ∑ μ, ∑ l : Fin 5 → Fin 4,
        crossedWeight P μ l * chainFour crossedAlpha
          (crossedB P.m (curveMomentum P.m u) (restMomentum P.m) μ l) crossedLines
          (symanzikMatrix crossedAlpha z) := by
    rw [crossedT3]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hT, sum_crossedWeight_chainFour, ladderK]
  ring

end Patterns

end QED.TwoLoop.UnitXGraph

end
