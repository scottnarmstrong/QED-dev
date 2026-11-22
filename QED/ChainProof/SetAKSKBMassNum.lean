/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdMink
public import QED.GradedProof.RPi4MajNum
public import QED.ChainProof.SetAKSKBTrace
public import QED.WickModel.VacuumPolarizationAlgebra

/-!
# Set (a), stage B4: the mass-derivative bubble as convergent one-loop pieces

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B4 (the mass
class). The mass class of the photon-mass density is `σ(u) · fLim(single 0 1)`, the limit of the
flavour sum of `M_f ∂_M` of the bubble. At the entry `(2, 3)`, with `x = k + q`, `y = q`,
`D_x`, `D_y` the propagator denominators of mass `M` and `κ = k²k³`, the mass derivative of the
bubble is `M dBubbleW = 8 κ_F M² (2q²q³ + L)(D_x⁻² D_y⁻¹ + D_x⁻¹ D_y⁻²)`, `L = k³q² + k²q³`
(`Tr[γ³γ²] = 0`, `Tr[γ³ x̸ γ² y̸] = 4(x³y² + x²y³)`). The quadratic part `2q²q³` makes each flavour
log-divergent by power counting; with `D_x - D_y = 2k·q + k·k` it is rewritten as four-line pieces
with cubic numerators plus `4q²q³ D_y⁻³`, which is odd in `q²`:

* `ksMassN`, `ksMassQ`: the cubic numerators
  `a q²q³(k·q) + b q²q³ + L(q)(c + d k·q + e q·q)` and an explicit quartic for them
  (`ksMassQ_eval`, `ksMassQ_quart`, `ksMassQ_loopDegLe`);
* `ksMassQ_evalC_X0`, `ksMassQ_cTwoG_X0`: the value and the half Laplacian at the shift
  point `(-P, 0)` of the reduced one-loop bracket;
* `ksMass_trace`: the trace of the bubble at `(2, 3)`;
* **`ksMass_dBubbleW`**: `M dBubbleW = 8 κ_F M² (N_A D_A + N_B D_B - 2iε L D_B + 4q²q³ D_y⁻³)`
  with `D_A = D_x⁻¹ D_y⁻³`, `D_B = D_x⁻² D_y⁻²`.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.TwoLoop.Bridge QED.GradedProof.VP2 QED.GradedProof.RPi4
open QED.Dirac

/-! ### The cubic numerators -/

/-- `L(q) = k³q² + k²q³`. -/
def ksMassL (k q : Fin 4 → ℝ) : ℝ := k 3 * q 2 + k 2 * q 3

/-- **The cubic numerators** `a q²q³(k·q) + b q²q³ + L(q)(c + d k·q + e q·q)`. -/
noncomputable def ksMassN (k : Fin 4 → ℝ) (a b c d e : ℂ) (q : Fin 4 → ℝ) : ℂ :=
  a * ((q 2 * q 3 * Minkowski.dot k q : ℝ) : ℂ) + b * ((q 2 * q 3 : ℝ) : ℂ) +
    ((ksMassL k q : ℝ) : ℂ) * (c + d * ((Minkowski.dot k q : ℝ) : ℂ) +
      e * ((Minkowski.dot q q : ℝ) : ℂ))

/-- The coefficients of `L`. -/
def ksMassL1 (k : Fin 4 → ℝ) (μ : Fin 4) : ℝ :=
  (if μ = 2 then k 3 else 0) + (if μ = 3 then k 2 else 0)

/-- The coefficients of `q²q³`. -/
def ksMassI (μ ν : Fin 4) : ℝ := if μ = 2 ∧ ν = 3 then 1 else 0

/-- The lowered components `k_μ`. -/
def ksMassK (k : Fin 4 → ℝ) (μ : Fin 4) : ℝ := Minkowski.metric μ μ * k μ

/-- **An explicit quartic of the cubic numerators** (loop `0` only). -/
noncomputable def ksMassQ (k : Fin 4 → ℝ) (a b c d e : ℂ) : LoopQuartic where
  const := 0
  lin x := if x.1 = 0 then c * (ksMassL1 k x.2 : ℂ) else 0
  quad x y := if x.1 = 0 ∧ y.1 = 0 then
    b * (ksMassI x.2 y.2 : ℂ) + d * (ksMassL1 k x.2 : ℂ) * (ksMassK k y.2 : ℂ) else 0
  cub x y z := if x.1 = 0 ∧ y.1 = 0 ∧ z.1 = 0 then
    a * (ksMassI x.2 y.2 : ℂ) * (ksMassK k z.2 : ℂ) +
      e * (ksMassL1 k x.2 : ℂ) * (Minkowski.metric y.2 z.2 : ℂ) else 0
  quart _ _ _ _ := 0

section Quartic

variable (k : Fin 4 → ℝ) (a b c d e : ℂ)

theorem ksMassQ_eval (ℓ : Fin 2 → Fin 4 → ℝ) :
    (ksMassQ k a b c d e).eval ℓ = ksMassN k a b c d e (ℓ 0) := by
  simp only [LoopQuartic.eval, LoopQuartic.evalC, ksMassQ, loopComp, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_four, ksMassN, ksMassL, ksMassL1, ksMassI, ksMassK,
    Minkowski.dot_eq, Minkowski.metric]
  simp
  ring

theorem ksMassQ_quart : (ksMassQ k a b c d e).quart = 0 := rfl

theorem ksMassQ_loopDegLe : LoopDegLe 1 0 (ksMassQ k a b c d e) where
  lin x hx := by
    have : x.1 ≠ 0 := fun h => by simp [loopInd, h] at hx
    simp [ksMassQ, this]
  quad x y hx := by
    have : ¬(x.1 = 0 ∧ y.1 = 0) := fun h => by simp [loopInd, h.1, h.2] at hx
    simp only [ksMassQ, this, ite_false]
  cub x y z hx := by
    have : ¬(x.1 = 0 ∧ y.1 = 0 ∧ z.1 = 0) := fun h => by
      simp [loopInd, h.1, h.2.1, h.2.2] at hx
    simp only [ksMassQ, this, ite_false]
  quart _ _ _ _ _ := rfl

theorem ksMassQ_evalC_X0 (P : Fin 4 → ℝ) :
    (ksMassQ k a b c d e).evalC (faceIdX0 P) = ksMassN k a b c d e (-P) := by
  have h := ksMassQ_eval k a b c d e ![-P, 0]
  simp only [LoopQuartic.eval, Matrix.cons_val_zero] at h
  exact h

/-- **The half Laplacian at the shift point**: `-(a + 6e) L(P) + 2d k²k³`. -/
theorem ksMassQ_cTwoG_X0 (P : Fin 4 → ℝ) :
    cTwoG (ksMassQ k a b c d e) (eS 0) (faceIdX0 P) =
      -(a + 6 * e) * ((ksMassL k P : ℝ) : ℂ) + 2 * d * ((k 2 * k 3 : ℝ) : ℂ) := by
  simp only [cTwoG, LoopQuartic.hess, LoopQuartic.quartSym, ksMassQ, gMet, eS, faceIdX0,
    loopComp, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four, ksMassL, ksMassL1,
    ksMassI, ksMassK, Minkowski.metric]
  simp
  ring

end Quartic

/-! ### The trace and the pointwise decomposition -/

/-- **The trace of the bubble at `(2, 3)`**: `Tr[γ³ x̸ γ² y̸] = 4(x³y² + y³x²)`. -/
theorem ksMass_trace (x y : Fin 4 → ℝ) :
    (gamma 3 * (slash x * (gamma 2 * slash y))).trace = 4 * ((x 3 * y 2 + y 3 * x 2 : ℝ) : ℂ) := by
  rw [faceId_gamma_eq_slash 3, faceId_gamma_eq_slash 2, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    trace_slash_mul_slash_mul_slash_mul_slash]
  simp only [ksB_single_dot, ksB_dot_single, Pi.single_eq_of_ne (show (2 : Fin 4) ≠ 3 by decide)]
  push_cast
  ring

/-- The line flags of the piece `D_x⁻¹ D_y⁻³`. -/
def ksMassBA : Fin 4 → Bool := ![true, false, false, false]

/-- The line flags of the piece `D_x⁻² D_y⁻²`. -/
def ksMassBB : Fin 4 → Bool := ![true, true, false, false]

/-- The product of the four inverse denominators of mass `M` with flags `b`. -/
noncomputable def ksMassDen (b : Fin 4 → Bool) (M ε : ℝ) (k q : Fin 4 → ℝ) : ℂ :=
  ∏ i, (propDenom ((fun _ : Fin 4 => M) i) ε (if b i then k + q else q))⁻¹

/-- The numerator of the piece `D_x⁻¹ D_y⁻³`: `-4 q²q³ (2k·q + k·k)`. -/
noncomputable def ksMassNA (k : Fin 4 → ℝ) : (Fin 4 → ℝ) → ℂ :=
  ksMassN k (-8) (-4 * (Minkowski.dot k k : ℂ)) 0 0 0

/-- The numerator of the piece `D_x⁻² D_y⁻²`: `-2 q²q³ (2k·q + k·k) + L (D⁰_x + D⁰_y)`. -/
noncomputable def ksMassNB (k : Fin 4 → ℝ) (M : ℝ) : (Fin 4 → ℝ) → ℂ :=
  ksMassN k (-4) (-2 * (Minkowski.dot k k : ℂ)) ((Minkowski.dot k k : ℂ) + 2 * (M : ℂ) ^ 2) 2 2

/-- The numerator `L` of the `iε` correction. -/
noncomputable def ksMassNL (k : Fin 4 → ℝ) : (Fin 4 → ℝ) → ℂ := ksMassN k 0 0 1 0 0

theorem ksMassDen_A (M ε : ℝ) (k q : Fin 4 → ℝ) :
    ksMassDen ksMassBA M ε k q =
      (propDenom M ε (k + q))⁻¹ * (propDenom M ε q)⁻¹ ^ 3 := by
  simp only [ksMassDen, Fin.prod_univ_four, ksMassBA, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, ite_true,
    Bool.false_eq_true, ite_false]
  ring

theorem ksMassDen_B (M ε : ℝ) (k q : Fin 4 → ℝ) :
    ksMassDen ksMassBB M ε k q =
      (propDenom M ε (k + q))⁻¹ ^ 2 * (propDenom M ε q)⁻¹ ^ 2 := by
  simp only [ksMassDen, Fin.prod_univ_four, ksMassBB, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, ite_true,
    Bool.false_eq_true, ite_false]
  ring

/-- **The mass derivative of the bubble at `(2, 3)` as convergent pieces**, up to the odd
term `4q²q³ D_y⁻³`. -/
theorem ksMass_dBubbleW (e M : ℝ) {ε : ℝ} (hε : ε ≠ 0) (k q : Fin 4 → ℝ) :
    (M : ℂ) * dBubbleW e M ε k q 2 3 = 8 * kF e * (M : ℂ) ^ 2 *
      (ksMassNA k q * ksMassDen ksMassBA M ε k q + ksMassNB k M q * ksMassDen ksMassBB M ε k q -
        2 * ((ε : ℂ) * I) * (ksMassNL k q * ksMassDen ksMassBB M ε k q) +
        4 * ((q 2 * q 3 : ℝ) : ℂ) * (propDenom M ε q)⁻¹ ^ 3) := by
  have hx := propDenom_ne_zero (M := M) hε (k + q)
  have hy := propDenom_ne_zero (M := M) hε q
  have htr : (gAF true 2 3 * gBF true 2 3).trace = 0 := maj_trace_gAB true
  have hb := bubTr_eq (isOddG_gamma _ : IsOddG (gAF true 2 3))
    (isOddG_gamma _ : IsOddG (gBF true 2 3)) M (k + q) q
  simp only [gAF, gBF, ite_true] at hb htr
  rw [ksMass_trace, htr, mul_zero, add_zero] at hb
  have hdx : propDenom M ε (k + q) = ((Minkowski.dot k k + 2 * Minkowski.dot k q +
      Minkowski.dot q q + M ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I := by
    simp only [propDenom, Minkowski.dot_eq, Pi.add_apply]
    push_cast
    ring
  have hdy : propDenom M ε q = ((Minkowski.dot q q + M ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I := rfl
  rw [hdx] at hx
  rw [hdy] at hy
  simp only [dBubbleW, dBub, gAF, gBF, ite_true, zk_true, zk_false, htr, hb, ksMassDen_A,
    ksMassDen_B, hdx, hdy, ksMassNA, ksMassNB, ksMassNL, ksMassN, ksMassL, Pi.add_apply]
  field_simp
  push_cast
  ring

end QED.ChainProof.SetAKS

end
