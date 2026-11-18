/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLGraph
public import QED.TwoLoop.UnitLGraphTraceContract
import Mathlib.Tactic.Ring

/-!
# The ladder numerator as Lorentz contractions

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the L link, graph half. The projected ladder
numerator of `QED.TwoLoop.UnitLGraph.openNum_L_explicit` is
`N(x, u) = -π⁴ κ ∑_μ ∑_l c_{μ,l} U⁻² (6 ch(Ē) + V chainTwo + ¼ V² chainFour)`. This file

* sums the photon weights: `∑_μ ∑_l c_{μ,l} ch(B_{μ,l}; Y) = η² lw(P; Y)` with
  `η = (1/i)(Λ² - m_γ²)` and `lw` the ladder contraction of
  `QED/TwoLoop/UnitLGraphTraceContract.lean` (`sum_ladderWeight_ch`);
* defines the three coefficients `T₁, T₂, T₃` of `N = T₁ + T₂ V + T₃ V²` at any point `z` of
  the parameter space (`ladderT1`, `ladderT2`, `ladderT3`, `openNum_L_eq_T`);
* writes them through the contraction patterns (`ladderT1_eq`, `ladderT2_eq`, `ladderT3_eq`):
  `T₁ = -π⁴ κ η² U⁻² · 6 lw(P; Ē)`, `T₂` the six single contractions of slots weighted by
  `C_{kl}`, and `T₃` the three double contractions weighted by `C_{kl} C_{k'l'}`.
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.TwoLoop.UnitLGraphTrace

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Bridge QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraph
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (LoopQuartic castLoopMatrix class5LoopMatrixPV symanzikV symanzikU
  symanzikMatrix lineMomentum loopShift)

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### Summing the photon weights -/

theorem sum_fin_succ_fun {n : ℕ} (g : (Fin (n + 1) → Fin 4) → ℂ) :
    ∑ l, g l = ∑ a, ∑ l : Fin n → Fin 4, g (Fin.cons a l) := by
  rw [← (Fin.consEquiv fun _ => Fin 4).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_fin5 (f : (Fin 5 → Fin 4) → ℂ) :
    ∑ l, f l = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f ![a, b, c, d, e] := by
  simp only [sum_fin_succ_fun (n := 4), sum_fin_succ_fun (n := 3), sum_fin_succ_fun (n := 2),
    sum_fin_succ_fun (n := 1), sum_fin_succ_fun (n := 0), Finset.univ_unique, Finset.sum_singleton]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ =>
      rfl

/-- The Pauli–Villars photon constant `η = (1/i)(Λ² - m_γ²)`. -/
noncomputable def pvConst (P : Params) : ℂ := (1 / I) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)

theorem permL_zero : permL 0 = 2 := rfl
theorem permL_one : permL 1 = 0 := rfl
theorem permL_two : permL 2 = 4 := rfl
theorem permL_three : permL 3 = 1 := rfl
theorem permL_four : permL 4 = 3 := rfl

/-- **The ladder chain sum is the ladder contraction**:
`∑_μ ∑_l c_{μ,l} ch(B_{μ,l}; Y) = η² lw(P; Y)`. -/
theorem sum_ladderWeight_ch (P : Params) (p' p : Fin 4 → ℝ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4)
    (Fin 4) ℂ) :
    ∑ μ, ∑ l : Fin 5 → Fin 4, ladderWeight P μ l * ch (ladderB P.m p' p μ l) Y₀ Y₁ Y₂ Y₃ =
      pvConst P ^ 2 * lw (pauliMat P.m p' p) Y₀ Y₁ Y₂ Y₃ := by
  unfold lw
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [sum_fin5]
  simp only [ladderWeight, ladderB, ch, permL_zero, permL_one, permL_two, permL_three, permL_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single μ (fun c _ hc => by simp [kron, hc]) (by simp),
    Finset.sum_eq_single b (fun d _ hd => by simp [pvEta, Minkowski.metric, Ne.symm hd]) (by simp),
    Finset.sum_eq_single a (fun e _ he => by simp [pvEta, Minkowski.metric, Ne.symm he]) (by simp)]
  simp only [kron, ite_true, one_mul, pvEta, pvConst, gammaLower_eq_metric_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  push_cast
  ring

/-! ### The three coefficients of the projected numerator -/

/-- The external momenta of the Pauli–Villars form of the ladder along the curve. -/
noncomputable abbrev ladderMom (P : Params) (u : ℝ) : Fin 8 → Fin 4 → ℝ :=
  pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u)

/-- The four electron numerators of the ladder at the shifted loop momenta, at the point `z`. -/
noncomputable def ladderE (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  elecAt ladderAlpha (ladderMom P u) (fun _ => P.m) ladderLines (-loopShift ladderAlpha
      (ladderMom P u) z)

/-- The coefficient `T₁` of `V⁰` in the projected ladder numerator, at the point `z`. -/
noncomputable def ladderT1 (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ℂ :=
  -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4, ladderWeight P μ l *
    (((symanzikU ladderAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
      (6 * ch (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l) (ladderE P z u 0)
        (ladderE P z u 1) (ladderE P z u 2) (ladderE P z u 3)))

/-- The coefficient `T₂` of `V¹` in the projected ladder numerator, at the point `z`. -/
noncomputable def ladderT2 (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ℂ :=
  -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4, ladderWeight P μ l *
    (((symanzikU ladderAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
      chainTwo ladderAlpha (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
        (ladderE P z u) ladderLines (symanzikMatrix ladderAlpha z))

/-- The coefficient `T₃` of `V²` in the projected ladder numerator, at the point `z`. -/
noncomputable def ladderT3 (P : Params) (z : Fin 8 → ℝ) (u : ℝ) : ℂ :=
  -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4, ladderWeight P μ l *
    (((symanzikU ladderAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
      (1 / 4 * chainFour ladderAlpha (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
        ladderLines (symanzikMatrix ladderAlpha z)))

/-- **The projected ladder numerator is `T₁ + T₂ V + T₃ V²`.** -/
theorem openNum_L_eq_T (P : Params) (x : Fin 7 → ℝ) (u : ℝ) :
    openNum .L P x u = ladderT1 P (simplexPoint x) u +
      ladderT2 P (simplexPoint x) u *
        ((symanzikV ladderAlpha (ladderMom P u) (pvMasses P) (simplexPoint x) : ℝ) : ℂ) +
      ladderT3 P (simplexPoint x) u *
        ((symanzikV ladderAlpha (ladderMom P u) (pvMasses P) (simplexPoint x) : ℝ) : ℂ) ^ 2 := by
  rw [openNum_L_explicit]
  simp only [ladderT1, ladderT2, ladderT3, ladderE, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring
  · exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring

/-! ### The coefficients through the contraction patterns -/

section Coeff

variable (P : Params) (p' p : Fin 4 → ℝ)

theorem sum_ladderWeight_sum_ch (Y₀ Y₁ Y₂ Y₃ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ μ, ∑ l : Fin 5 → Fin 4, ladderWeight P μ l *
        ∑ ν, ch (ladderB P.m p' p μ l) (Y₀ ν) (Y₁ ν) (Y₂ ν) (Y₃ ν) =
      pvConst P ^ 2 * ∑ ν, lw (pauliMat P.m p' p) (Y₀ ν) (Y₁ ν) (Y₂ ν) (Y₃ ν) := by
  simp only [Finset.mul_sum]
  rw [sum_sum_sum_comm]
  exact Finset.sum_congr rfl fun ν _ => sum_ladderWeight_ch P p' p _ _ _ _

theorem sum_ladderWeight_sum_sum_ch (Y₀ Y₁ Y₂ Y₃ : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ μ, ∑ l : Fin 5 → Fin 4, ladderWeight P μ l *
        ∑ ν, ∑ ρ, ch (ladderB P.m p' p μ l) (Y₀ ν ρ) (Y₁ ν ρ) (Y₂ ν ρ) (Y₃ ν ρ) =
      pvConst P ^ 2 * ∑ ν, ∑ ρ, lw (pauliMat P.m p' p) (Y₀ ν ρ) (Y₁ ν ρ) (Y₂ ν ρ) (Y₃ ν ρ) := by
  simp only [Finset.mul_sum]
  rw [sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [sum_sum_sum_comm]
  exact Finset.sum_congr rfl fun ρ _ => by rw [← sum_ladderWeight_ch P p']

/-- The contraction coefficient `C_{kl}` of the slots `k, l` of the ladder chain. -/
noncomputable abbrev ladderC (A : Matrix (Fin 2) (Fin 2) ℝ) (k l : Fin 4) : ℂ :=
  (contrC ladderAlpha A (ladderLines k) (ladderLines l) : ℂ)

/-- **The single contractions summed over the photon weights.** -/
theorem sum_ladderWeight_chainTwo (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∑ μ, ∑ l : Fin 5 → Fin 4, ladderWeight P μ l *
        chainTwo ladderAlpha (ladderB P.m p' p μ l) E ladderLines A =
      pvConst P ^ 2 * (ladderC A 0 1 * ∑ ν, lw (pauliMat P.m p' p) (gammaLower ν) (gamma ν) (E 2)
          (E 3) +
        ladderC A 0 2 * ∑ ν, lw (pauliMat P.m p' p) (gammaLower ν) (E 1) (gamma ν) (E 3) +
        ladderC A 0 3 * ∑ ν, lw (pauliMat P.m p' p) (gammaLower ν) (E 1) (E 2) (gamma ν) +
        ladderC A 1 2 * ∑ ν, lw (pauliMat P.m p' p) (E 0) (gammaLower ν) (gamma ν) (E 3) +
        ladderC A 1 3 * ∑ ν, lw (pauliMat P.m p' p) (E 0) (gammaLower ν) (E 2) (gamma ν) +
        ladderC A 2 3 * ∑ ν, lw (pauliMat P.m p' p) (E 0) (E 1) (gammaLower ν) (gamma ν)) := by
  have h : ∀ μ (l : Fin 5 → Fin 4), ladderWeight P μ l *
      chainTwo ladderAlpha (ladderB P.m p' p μ l) E ladderLines A =
      ladderC A 0 1 * (ladderWeight P μ l * ∑ ν, ch (ladderB P.m p' p μ l) (gammaLower ν)
          (gamma ν) (E 2) (E 3)) +
      ladderC A 0 2 * (ladderWeight P μ l * ∑ ν, ch (ladderB P.m p' p μ l) (gammaLower ν) (E 1)
          (gamma ν) (E 3)) +
      ladderC A 0 3 * (ladderWeight P μ l * ∑ ν, ch (ladderB P.m p' p μ l) (gammaLower ν) (E 1)
          (E 2) (gamma ν)) +
      ladderC A 1 2 * (ladderWeight P μ l * ∑ ν, ch (ladderB P.m p' p μ l) (E 0) (gammaLower ν)
          (gamma ν) (E 3)) +
      ladderC A 1 3 * (ladderWeight P μ l * ∑ ν, ch (ladderB P.m p' p μ l) (E 0) (gammaLower ν)
          (E 2) (gamma ν)) +
      ladderC A 2 3 * (ladderWeight P μ l * ∑ ν, ch (ladderB P.m p' p μ l) (E 0) (E 1)
          (gammaLower ν) (gamma ν)) :=
    fun μ l => by
      simp only [chainTwo]
      ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [sum_ladderWeight_sum_ch]
  ring

/-- **The double contractions summed over the photon weights.** -/
theorem sum_ladderWeight_chainFour (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∑ μ, ∑ l : Fin 5 → Fin 4, ladderWeight P μ l *
        chainFour ladderAlpha (ladderB P.m p' p μ l) ladderLines A =
      pvConst P ^ 2 * (ladderC A 0 1 * ladderC A 2 3 * ∑ ν, ∑ ρ,
          lw (pauliMat P.m p' p) (gammaLower ν) (gamma ν) (gammaLower ρ) (gamma ρ) +
        ladderC A 0 2 * ladderC A 1 3 * ∑ ν, ∑ ρ,
          lw (pauliMat P.m p' p) (gammaLower ν) (gammaLower ρ) (gamma ν) (gamma ρ) +
        ladderC A 0 3 * ladderC A 1 2 * ∑ ν, ∑ ρ,
          lw (pauliMat P.m p' p) (gammaLower ν) (gammaLower ρ) (gamma ρ) (gamma ν)) := by
  have h : ∀ μ (l : Fin 5 → Fin 4), ladderWeight P μ l *
      chainFour ladderAlpha (ladderB P.m p' p μ l) ladderLines A =
      ladderC A 0 1 * ladderC A 2 3 * (ladderWeight P μ l * ∑ ν, ∑ ρ,
          ch (ladderB P.m p' p μ l) (gammaLower ν) (gamma ν) (gammaLower ρ) (gamma ρ)) +
      ladderC A 0 2 * ladderC A 1 3 * (ladderWeight P μ l * ∑ ν, ∑ ρ,
          ch (ladderB P.m p' p μ l) (gammaLower ν) (gammaLower ρ) (gamma ν) (gamma ρ)) +
      ladderC A 0 3 * ladderC A 1 2 * (ladderWeight P μ l * ∑ ν, ∑ ρ,
          ch (ladderB P.m p' p μ l) (gammaLower ν) (gammaLower ρ) (gamma ρ) (gamma ν)) :=
    fun μ l => by
      simp only [chainFour]
      ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [sum_ladderWeight_sum_sum_ch]
  ring

end Coeff

section Patterns

variable (P : Params) (z : Fin 8 → ℝ) (u : ℝ)

/-- The overall constant `-π⁴ κ η²` of the three coefficients. -/
noncomputable abbrev ladderK : ℂ := -((π : ℂ) ^ 4) * ladderConst P * pvConst P ^ 2

/-- The Pauli matrices along the curve. -/
noncomputable abbrev ladderPauli : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  pauliMat P.m (curveMomentum P.m u) (restMomentum P.m)

/-- The momentum of the chain slot `k` at the shifted loop momenta. -/
noncomputable abbrev ladderQ (k : Fin 4) : Fin 4 → ℝ :=
  lineMomentum ladderAlpha (ladderMom P u) (ladderLines k) (-loopShift ladderAlpha
      (ladderMom P u) z)

theorem ladderE_apply (k : Fin 4) : ladderE P z u k = electronNumerator P.m (ladderQ P z u k) := rfl

/-- **`T₁` through the ladder contraction**: `T₁ = -π⁴ κ η² U⁻² · 6 lw(P; Ē)`. -/
theorem ladderT1_eq : ladderT1 P z u = ladderK P * ((symanzikU ladderAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
    (6 * lw (ladderPauli P u) (ladderE P z u 0) (ladderE P z u 1) (ladderE P z u 2)
      (ladderE P z u 3)) := by
  have h := sum_ladderWeight_ch P (curveMomentum P.m u) (restMomentum P.m) (ladderE P z u 0)
    (ladderE P z u 1) (ladderE P z u 2) (ladderE P z u 3)
  calc ladderT1 P z u = -((π : ℂ) ^ 4) * ladderConst P *
      (((symanzikU ladderAlpha z ^ 2 : ℝ) : ℂ)⁻¹ * 6 * ∑ μ,
          ∑ l : Fin 5 → Fin 4, ladderWeight P μ l *
        ch (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l) (ladderE P z u 0)
          (ladderE P z u 1) (ladderE P z u 2) (ladderE P z u 3)) := by
        rw [ladderT1]
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring
    _ = _ := by
        rw [h, ladderK]
        ring

/-- **`T₂` through the contraction patterns.** -/
theorem ladderT2_eq : ladderT2 P z u = ladderK P * ((symanzikU ladderAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
    (ladderC (symanzikMatrix ladderAlpha z) 0 1 *
        lw (ladderPauli P u) ((2 : ℂ) • 𝟙) 𝟙 (ladderE P z u 2) (ladderE P z u 3) +
      ladderC (symanzikMatrix ladderAlpha z) 0 2 * omL (ladderPauli P u)
        (((4 * (P.m : ℂ)) • 𝟙 + (8 : ℂ) • slash (ladderQ P z u 1)) * ladderE P z u 3) +
      ladderC (symanzikMatrix ladderAlpha z) 0 3 *
        f3 (ladderPauli P u) (ladderE P z u 1) (ladderE P z u 2) +
      ladderC (symanzikMatrix ladderAlpha z) 1 2 *
        lw (ladderPauli P u) (ladderE P z u 0) ((2 : ℂ) • 𝟙) 𝟙 (ladderE P z u 3) +
      ladderC (symanzikMatrix ladderAlpha z) 1 3 * omR (ladderPauli P u)
        (ladderE P z u 0 * ((4 * (P.m : ℂ)) • 𝟙 + (8 : ℂ) • slash (ladderQ P z u 2))) +
      ladderC (symanzikMatrix ladderAlpha z) 2 3 *
        lw (ladderPauli P u) (ladderE P z u 0) (ladderE P z u 1) ((2 : ℂ) • 𝟙) 𝟙) := by
  have hT : ladderT2 P z u = -((π : ℂ) ^ 4) * ladderConst P *
      ((symanzikU ladderAlpha z ^ 2 : ℝ) : ℂ)⁻¹ * ∑ μ, ∑ l : Fin 5 → Fin 4, ladderWeight P μ l *
        chainTwo ladderAlpha (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
          (ladderE P z u) ladderLines (symanzikMatrix ladderAlpha z) := by
    rw [ladderT2]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hT, sum_ladderWeight_chainTwo, sum_lw_01, sum_lw_03, sum_lw_12, sum_lw_23,
    sum_lw_02 _ _ _ _ fun μ => by rw [ladderE_apply]; exact sum_contract02_elec μ P.m _,
    sum_lw_13 _ _ _ _ fun μ => by rw [ladderE_apply]; exact sum_contract13_elec μ P.m _]
  rw [ladderK]
  ring

/-- **`T₃` through the contraction patterns.** -/
theorem ladderT3_eq : ladderT3 P z u = ladderK P * ((symanzikU ladderAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
    (1 / 4 * (ladderC (symanzikMatrix ladderAlpha z) 0 1 * ladderC
        (symanzikMatrix ladderAlpha z) 2 3 *
        lw (ladderPauli P u) ((2 : ℂ) • 𝟙) 𝟙 ((2 : ℂ) • 𝟙) 𝟙 +
      ladderC (symanzikMatrix ladderAlpha z) 0 2 * ladderC (symanzikMatrix ladderAlpha z) 1 3 *
        (32 * omL (ladderPauli P u) 𝟙) +
      ladderC (symanzikMatrix ladderAlpha z) 0 3 * ladderC (symanzikMatrix ladderAlpha z) 1 2 *
        f3 (ladderPauli P u) ((2 : ℂ) • 𝟙) 𝟙)) := by
  have hT : ladderT3 P z u = -((π : ℂ) ^ 4) * ladderConst P *
      ((symanzikU ladderAlpha z ^ 2 : ℝ) : ℂ)⁻¹ * (1 / 4) * ∑ μ, ∑ l : Fin 5 → Fin 4,
        ladderWeight P μ l * chainFour ladderAlpha
          (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l) ladderLines
          (symanzikMatrix ladderAlpha z) := by
    rw [ladderT3]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hT, sum_ladderWeight_chainFour, sum_lw_0123, sum_lw_0213, sum_lw_0312, ladderK]
  ring

end Patterns

end QED.TwoLoop.UnitLGraphTrace

end
