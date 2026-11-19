/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2FWardEF
public import QED.TwoLoop.VPUnitNestedAlgebra

/-!
# The Ward identity of the inserted bubbles at one flavour

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2, the Ward step of
the classes `F0`, `F1`. With `N_p = M - p̸`, `D_p = p² + M² - iε` and `X_p = δ₂ p̸ + δ_m M`:

* `wardF_num`: `N_{k+p} k̸ N_p = D_{k+p} N_p - D_p N_{k+p} + iε k̸` (the line-by-line Ward
  identity at real mass, with its `iε` remainder);
* `wardF_mass`: contracting the two inserted bubbles (`F0` at `x = k + q, y = q`, `F1` at
  `x = q, y = k + q`) with `k_μ`,
  `k·F0 + k·F1 = T(q) - T(k + q) + δ₂ k_μ B^μ(q) + iε Tr[γ^ν k̸] (R(k + q, q) + R(q, k + q))`,
  where `T(p) = Tr[γ^ν N_p X_p N_p] D_p⁻²` (`wfT`), `B^μ` is the bubble (`wfB`) and
  `R(x, y) = (δ₂ y² + δ_m M²) D_y⁻² D_x⁻¹` (`wfR`); checked numerically to `1e-16`;
* `wfT_eq`, `wfB_eq`: `T` and `B` in the two-line form `QED.GradedProof.VP2.tw`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.VP2

open QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### Trace expansions -/

theorem IsOddG.trace1 {A : Mat} (hA : IsOddG A) : A.trace = 0 :=
  trace_eq_zero_of_gamma5_conj hA

theorem trace_wfT {A Y : Mat} (hA : IsOddG A) (hY : IsOddG Y) (d₂ dm M : ℂ) :
    (A * (M • 1 - Y) * (d₂ • Y + (dm * M) • 1) * (M • 1 - Y)).trace =
      d₂ * (A * (Y * (Y * Y))).trace + M ^ 2 * ((d₂ - 2 * dm) * (A * Y).trace) := by
  have o1 := IsOddG.trace3 hA hY hY
  have o2 := IsOddG.trace1 hA
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, smul_sub, smul_add, smul_smul]
  rw [o1, o2]
  ring

theorem trace_wfB {A B X Y : Mat} (hA : IsOddG A) (hB : IsOddG B) (hX : IsOddG X)
    (hY : IsOddG Y) (M : ℂ) :
    (A * (M • 1 - X) * B * (M • 1 - Y)).trace =
      (A * (X * (B * Y))).trace + M ^ 2 * (A * B).trace := by
  have o1 := IsOddG.trace3 hA hX hB
  have o2 := IsOddG.trace3 hA hB hY
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.mul_assoc, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, smul_sub, smul_smul]
  rw [o1, o2]
  ring

theorem trace_wfR1 {A B Y : Mat} (hA : IsOddG A) (hB : IsOddG B) (hY : IsOddG Y)
    (d₂ dm M : ℂ) :
    (A * B * (d₂ • Y + (dm * M) • 1) * (M • 1 - Y)).trace =
      -d₂ * (A * (B * (Y * Y))).trace + dm * M ^ 2 * (A * B).trace := by
  have o1 := IsOddG.trace3 hA hB hY
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, smul_add, smul_smul]
  rw [o1]
  ring

theorem trace_wfR2 {A B Y : Mat} (hA : IsOddG A) (hB : IsOddG B) (hY : IsOddG Y)
    (d₂ dm M : ℂ) :
    (A * (M • 1 - Y) * (d₂ • Y + (dm * M) • 1) * B).trace =
      -d₂ * (A * (Y * (Y * B))).trace + dm * M ^ 2 * (A * B).trace := by
  have o1 := IsOddG.trace3 hA hY hB
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, smul_sub, smul_smul]
  rw [o1]
  ring

/-- Contracting a gamma matrix with `k_μ`. -/
theorem sum_lower_trace (k : Fin 4 → ℝ) (L R : Mat) :
    ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * (L * Dirac.gamma μ * R).trace =
      (L * Dirac.slash k * R).trace := by
  simp only [Dirac.slash, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-! ### The line-by-line identity -/

/-- **`N_{k+p} k̸ N_p = D_{k+p} N_p - D_p N_{k+p} + iε k̸`.** -/
theorem wardF_num (M ε : ℝ) (k p : Fin 4 → ℝ) :
    electronNumerator M (k + p) * Dirac.slash k * electronNumerator M p =
      propDenom M ε (k + p) • electronNumerator M p -
        propDenom M ε p • electronNumerator M (k + p) + ((ε : ℂ) * I) • Dirac.slash k := by
  have e1 := QED.TwoLoop.VPUnitNested.electronNumerator_mul_slash_add M (k + p)
  have e2 := QED.TwoLoop.VPUnitNested.slash_add_mul_electronNumerator M p
  have hk : Dirac.slash k = (Dirac.slash (k + p) + (M : ℂ) • (1 : Mat)) -
      (Dirac.slash p + (M : ℂ) • (1 : Mat)) := by
    rw [Dirac.slash_add]; abel
  have h : electronNumerator M (k + p) * Dirac.slash k * electronNumerator M p =
      ((Minkowski.dot (k + p) (k + p) + M ^ 2 : ℝ) : ℂ) • electronNumerator M p -
        ((Minkowski.dot p p + M ^ 2 : ℝ) : ℂ) • electronNumerator M (k + p) := by
    rw [hk, Matrix.mul_sub, Matrix.sub_mul, e1, Matrix.mul_assoc, e2, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  rw [h]
  have hN : electronNumerator M p - electronNumerator M (k + p) = Dirac.slash k := by
    simp only [electronNumerator, Dirac.slash_add]; abel
  rw [← hN]
  simp only [propDenom]
  module

/-! ### The Ward identity at one flavour -/

variable (ν : Fin 4)

/-- The tadpole-like term `T(p) = Tr[γ^ν N_p X_p N_p] D_p⁻²`. -/
noncomputable def wfT (d₂ dm M ε : ℝ) (p : Fin 4 → ℝ) : ℂ :=
  (Dirac.gamma ν * electronNumerator M p * QED.TwoLoop.Insertion.fermionCtMatrix d₂ dm M p *
    electronNumerator M p).trace * (propDenom M ε p)⁻¹ * (propDenom M ε p)⁻¹

/-- The bubble `B^μ(x, y) = Tr[γ^ν N_x γ^μ N_y] D_x⁻¹ D_y⁻¹`. -/
noncomputable def wfB (μ : Fin 4) (M ε : ℝ) (x y : Fin 4 → ℝ) : ℂ :=
  (Dirac.gamma ν * electronNumerator M x * Dirac.gamma μ * electronNumerator M y).trace *
    (propDenom M ε x)⁻¹ * (propDenom M ε y)⁻¹

/-- The remainder `R(x, y) = (δ₂ y² + δ_m M²) D_y⁻² D_x⁻¹`. -/
noncomputable def wfR (d₂ dm M ε : ℝ) (x y : Fin 4 → ℝ) : ℂ :=
  ((d₂ : ℂ) * v0 y + dm * (M : ℂ) ^ 2) * ((propDenom M ε y)⁻¹) ^ 2 * (propDenom M ε x)⁻¹

theorem slash_mul_slash_v0 (y : Fin 4 → ℝ) :
    Dirac.slash y * Dirac.slash y = (-v0 y) • (1 : Mat) := by
  rw [QED.Dirac.slash_mul_slash]
  simp only [v0, propDenom]
  push_cast
  ring_nf

/-- **The Ward identity of the inserted bubbles at one flavour.** -/
theorem wardF_mass (d₂ dm M : ℝ) {ε : ℝ} (hε : 0 < ε) (k q : Fin 4 → ℝ) :
    ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
        (insG (gAF true μ ν) (gBF true μ ν) d₂ dm M ε (zk k true q) (zk k false q) +
          insG (gAF false μ ν) (gBF false μ ν) d₂ dm M ε (zk k false q) (zk k true q)) =
      wfT ν d₂ dm M ε (zk k false q) - wfT ν d₂ dm M ε (zk k true q) +
        (d₂ : ℂ) * ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
          wfB ν μ M ε (zk k true q) (zk k false q) +
        ((ε : ℂ) * I) * (∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
          (Dirac.gamma ν * Dirac.gamma μ).trace) *
          (wfR d₂ dm M ε (zk k true q) (zk k false q) +
            wfR d₂ dm M ε (zk k false q) (zk k true q)) := by
  simp only [zk, ite_true, Bool.false_eq_true, ite_false, gAF, gBF]
  set G := Dirac.gamma ν
  set K := Dirac.slash k
  set Nq := electronNumerator M q
  set Nk := electronNumerator M (k + q)
  set Xq := QED.TwoLoop.Insertion.fermionCtMatrix d₂ dm M q
  set Xk := QED.TwoLoop.Insertion.fermionCtMatrix d₂ dm M (k + q)
  set a := propDenom M ε (k + q) with ha_def
  set b := propDenom M ε q with hb_def
  have ha : a ≠ 0 := propDenom_ne_zero hε.ne' _
  have hb : b ≠ 0 := propDenom_ne_zero hε.ne' _
  have w1 : Nk * K * Nq = a • Nq - b • Nk + ((ε : ℂ) * I) • K := wardF_num M ε k q
  have hX : Xk = Xq + (d₂ : ℂ) • K := by
    simp only [Xk, Xq, K, QED.TwoLoop.Insertion.fermionCtMatrix, Dirac.slash_add, smul_add]
    abel
  -- the two contractions
  have s0 : ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * insG G (Dirac.gamma μ) d₂ dm M ε (k + q) q =
      (G * Nk * K * Nq * Xq * Nq).trace * a⁻¹ * (b⁻¹) ^ 2 := by
    simp only [insG, insTr]
    rw [show G * Nk * K * Nq * Xq * Nq = G * Nk * K * (Nq * Xq * Nq) by
      simp only [Matrix.mul_assoc], ← sum_lower_trace k (G * Nk) (Nq * Xq * Nq), Finset.sum_mul,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [Matrix.mul_assoc]
    ring
  have s1 : ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * insG (Dirac.gamma μ) G d₂ dm M ε q (k + q) =
      (K * Nq * G * Nk * Xk * Nk).trace * b⁻¹ * (a⁻¹) ^ 2 := by
    simp only [insG, insTr]
    rw [show K * Nq * G * Nk * Xk * Nk = 1 * K * (Nq * G * Nk * Xk * Nk) by
      simp only [Matrix.mul_assoc, Matrix.one_mul], ← sum_lower_trace k 1 (Nq * G * Nk * Xk * Nk),
      Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [Matrix.mul_assoc, Matrix.one_mul]
    ring
  have sB : ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * wfB ν μ M ε (k + q) q =
      (G * Nk * K * Nq).trace * a⁻¹ * b⁻¹ := by
    simp only [wfB]
    rw [← sum_lower_trace k (G * Nk) Nq, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    ring
  have sG : ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * (G * Dirac.gamma μ).trace = (G * K).trace := by
    have := sum_lower_trace k G 1
    simp only [Matrix.mul_one] at this
    exact this
  rw [Finset.sum_congr rfl fun μ _ => mul_add _ _ _, Finset.sum_add_distrib, s0, s1, sB, sG]
  -- the traces
  have tr0 : (G * Nk * K * Nq * Xq * Nq).trace =
      a * (G * Nq * Xq * Nq).trace - b * (G * Nk * Xq * Nq).trace +
        ((ε : ℂ) * I) * (G * K * Xq * Nq).trace := by
    rw [show G * Nk * K * Nq * Xq * Nq = G * (Nk * K * Nq) * Xq * Nq by
      simp only [Matrix.mul_assoc], w1]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  have tr1 : (K * Nq * G * Nk * Xk * Nk).trace =
      a * (G * Nk * Xk * Nq).trace - b * (G * Nk * Xk * Nk).trace +
        ((ε : ℂ) * I) * (G * Nk * Xk * K).trace := by
    rw [show K * Nq * G * Nk * Xk * Nk = (K * Nq) * (G * Nk * Xk * Nk) by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm,
      show G * Nk * Xk * Nk * (K * Nq) = G * Nk * Xk * (Nk * K * Nq) by
        simp only [Matrix.mul_assoc], w1]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  have tr2 : (G * Nk * Xk * Nq).trace =
      (G * Nk * Xq * Nq).trace + (d₂ : ℂ) * (G * Nk * K * Nq).trace := by
    rw [hX]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  have hG := isOddG_gamma ν
  have hK := isOddG_slash k
  have hXq : Xq = (d₂ : ℂ) • Dirac.slash q + ((dm : ℂ) * M) • (1 : Mat) := by
    simp only [Xq, QED.TwoLoop.Insertion.fermionCtMatrix]; push_cast; rfl
  have hXk : Xk = (d₂ : ℂ) • Dirac.slash (k + q) + ((dm : ℂ) * M) • (1 : Mat) := by
    simp only [Xk, QED.TwoLoop.Insertion.fermionCtMatrix]; push_cast; rfl
  have r1 : (G * K * Xq * Nq).trace = ((d₂ : ℂ) * v0 q + dm * (M : ℂ) ^ 2) * (G * K).trace := by
    rw [hXq, show Nq = (M : ℂ) • 1 - Dirac.slash q from rfl,
      trace_wfR1 hG hK (isOddG_slash q), slash_mul_slash_v0]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
    ring
  have r2 : (G * Nk * Xk * K).trace =
      ((d₂ : ℂ) * v0 (k + q) + dm * (M : ℂ) ^ 2) * (G * K).trace := by
    rw [hXk, show Nk = (M : ℂ) • 1 - Dirac.slash (k + q) from rfl,
      trace_wfR2 hG hK (isOddG_slash (k + q)),
      ← Matrix.mul_assoc (Dirac.slash (k + q)), slash_mul_slash_v0]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
    ring
  rw [tr0, tr1, tr2, r1, r2]
  simp only [wfT, wfR]
  rw [← ha_def, ← hb_def]
  field_simp
  ring

/-- `T` in the two-line form. -/
theorem wfT_eq (d₂ dm M ε : ℝ) (p : Fin 4 → ℝ) :
    wfT ν d₂ dm M ε p = tw ((d₂ : ℂ) * (Dirac.gamma ν * (Dirac.slash p *
      (Dirac.slash p * Dirac.slash p))).trace)
      (((d₂ : ℂ) - 2 * dm) * (Dirac.gamma ν * Dirac.slash p).trace) M ε p p := by
  have h := trace_wfT (isOddG_gamma ν) (isOddG_slash p) d₂ dm M
  simp only [wfT, tw]
  rw [show electronNumerator M p = (M : ℂ) • 1 - Dirac.slash p from rfl,
    show QED.TwoLoop.Insertion.fermionCtMatrix d₂ dm M p =
      (d₂ : ℂ) • Dirac.slash p + ((dm : ℂ) * M) • 1 by
        simp only [QED.TwoLoop.Insertion.fermionCtMatrix]; push_cast; rfl, h]

/-- `B` in the two-line form. -/
theorem wfB_eq (μ : Fin 4) (M ε : ℝ) (x y : Fin 4 → ℝ) :
    wfB ν μ M ε x y = tw ((Dirac.gamma ν * (Dirac.slash x * (Dirac.gamma μ *
      Dirac.slash y))).trace) ((Dirac.gamma ν * Dirac.gamma μ).trace) M ε x y := by
  have h := trace_wfB (isOddG_gamma ν) (isOddG_gamma μ) (isOddG_slash x) (isOddG_slash y) M
  simp only [wfB, tw]
  rw [show electronNumerator M x = (M : ℂ) • 1 - Dirac.slash x from rfl,
    show electronNumerator M y = (M : ℂ) • 1 - Dirac.slash y from rfl, h]

end QED.GradedProof.VP2

end
