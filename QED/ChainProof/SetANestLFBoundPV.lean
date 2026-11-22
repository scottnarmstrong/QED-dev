/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestLFBoundTime
public import QED.TwoLoop.NestedVPFubiniBoundInner

/-!
# Set (a), obligation (N): Pauli–Villars cancellation in the `δ₂, δ_m` bubble

Helper level for the inner bound of the fermion-counterterm classes `FA`, `FB` of obligation (N).
For a three-flavour Pauli–Villars set `(M_i, c_i)` (`∑ c_i = 0`, `∑ c_i M_i² = 0`, `M_0` the
lightest) the flavour sum of the closed forms `insCF` of
`QED/ChainProof/SetANestLFBoundTime.lean` is bounded, uniformly for `u ∈ [0, 1]`, by
`C (1 + ‖p‖)⁸ (1 + ‖v⃗‖)⁻⁴` (`exists_norm_sum_insCF_le`).

* `InsBd n x`: `x = O(Rⁿ)` uniformly for `u ∈ [0, 1]`, `R = 1 + ‖p‖ + ‖v⃗‖`.
* `insCF_eq`: with `M² = ζ - z` (`ζ = -W(u)|_{M=0} + iε`, `z = -W(u) + iε`), the closed form
  is `-(a₅ z^{-5/2} + a₃ z^{-3/2} + a₁ z^{-1/2})` with coefficients independent of `M` and of
  sizes `R⁴`, `R²`, `R⁰`.
* `sum_insCF_eq` and the second-order cancellation bound
  `QED.WickModel.VacuumPolarizationLimit.norm_sum_cpow_le_two` give `(max ε W₀)^{-(σ+2)}`;
* `rpow_key`: `Rⁿ (max ε W₀)^{-(σ+2)} ≤ C (1 + ‖p‖)⁸ (1 + ‖v⃗‖)⁻⁴` for `n ≤ 4`, `2σ = n + 1`:
  outside the ball `‖v⃗‖ < 4‖p‖ + 2` by `W₀ ≥ (2/9)(1 + ‖v⃗‖)²`, inside by `max ε W₀ ≥ ε`.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.ChainProof.SetANest

open QED.GradedProof.VP2 QED.TwoLoop.VPHalfAtLimit
open QED.WickModel.SelfEnergyLimit (massW)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### Polynomial size -/

/-- `x(p, u, v⃗) = O(Rⁿ)` uniformly for `u ∈ [0, 1]`, `R = 1 + ‖p‖ + ‖v⃗‖`. -/
def InsBd (n : ℕ) (x : (Fin 4 → ℝ) → ℝ → (Fin 3 → ℝ) → ℂ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ p u v, u ∈ Icc (0 : ℝ) 1 → ‖x p u v‖ ≤ K * (1 + ‖p‖ + ‖v‖) ^ n

theorem one_le_insR (p : Fin 4 → ℝ) (v : Fin 3 → ℝ) : 1 ≤ 1 + ‖p‖ + ‖v‖ := by
  have := norm_nonneg p
  have := norm_nonneg v
  linarith

namespace InsBd

variable {n m : ℕ} {x y : (Fin 4 → ℝ) → ℝ → (Fin 3 → ℝ) → ℂ}

theorem mono (h : InsBd n x) (hnm : n ≤ m) : InsBd m x := by
  obtain ⟨K, hK, h⟩ := h
  exact ⟨K, hK, fun p u v hu => (h p u v hu).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_insR p v) hnm) hK)⟩

theorem add (hx : InsBd n x) (hy : InsBd n y) : InsBd n fun p u v => x p u v + y p u v := by
  obtain ⟨K, hK, hx⟩ := hx
  obtain ⟨L, hL, hy⟩ := hy
  exact ⟨K + L, by positivity, fun p u v hu => (norm_add_le _ _).trans
    ((add_le_add (hx p u v hu) (hy p u v hu)).trans_eq (by ring))⟩

theorem mul (hx : InsBd n x) (hy : InsBd m y) :
    InsBd (n + m) fun p u v => x p u v * y p u v := by
  obtain ⟨K, hK, hx⟩ := hx
  obtain ⟨L, hL, hy⟩ := hy
  refine ⟨K * L, by positivity, fun p u v hu => ?_⟩
  rw [norm_mul, pow_add]
  calc ‖x p u v‖ * ‖y p u v‖
      ≤ (K * (1 + ‖p‖ + ‖v‖) ^ n) * (L * (1 + ‖p‖ + ‖v‖) ^ m) :=
        mul_le_mul (hx p u v hu) (hy p u v hu) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem const (c : ℂ) : InsBd 0 fun _ _ _ => c :=
  ⟨‖c‖, norm_nonneg _, fun _ _ _ _ => by simp⟩

theorem const_mul (c : ℂ) (hx : InsBd n x) : InsBd n fun p u v => c * x p u v := by
  obtain ⟨K, hK, hx⟩ := hx
  refine ⟨‖c‖ * K, by positivity, fun p u v hu => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hx p u v hu) (norm_nonneg _)

theorem neg (hx : InsBd n x) : InsBd n fun p u v => -x p u v := by
  obtain ⟨K, hK, hx⟩ := hx
  exact ⟨K, hK, fun p u v hu => by rw [norm_neg]; exact hx p u v hu⟩

theorem sub (hx : InsBd n x) (hy : InsBd n y) : InsBd n fun p u v => x p u v - y p u v := by
  have h := hx.add hy.neg
  simp only [← sub_eq_add_neg] at h
  exact h

end InsBd

/-! ### The basic sizes -/

section Sizes

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem insNorm_entry_le (A : Mat) (i j : Fin 4) : ‖A i j‖ ≤ ‖A‖ := by
  have h : ‖A i j‖₊ ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact (Finset.single_le_sum (f := fun j => ‖A i j‖₊) (fun _ _ => zero_le)
      (Finset.mem_univ j)).trans
        (Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i))
  exact_mod_cast h

theorem insNorm_trace_le (A : Mat) : ‖A.trace‖ ≤ 4 * ‖A‖ := by
  unfold Matrix.trace Matrix.diag
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖A i i‖ ≤ ∑ _i : Fin 4, ‖A‖ := Finset.sum_le_sum fun i _ => insNorm_entry_le A i i
    _ = 4 * ‖A‖ := by simp

theorem insNorm_slash_le (ℓ : Fin 4 → ℝ) :
    ‖Dirac.slash ℓ‖ ≤ (∑ κ, ‖Dirac.gamma κ‖) * ‖ℓ‖ := by
  rw [Dirac.slash, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ => ?_)
  rw [norm_smul, Complex.norm_real, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h := norm_le_pi_norm ℓ
  rw [Minkowski.lower_eq]
  fin_cases κ
  · simpa using h 0
  · simpa using h 1
  · simpa using h 2
  · simpa using h 3

theorem exists_norm_insTau_le (A B : Mat) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖insTau A B x y‖ ≤ C * (‖x‖ * ‖y‖) := by
  set G := ∑ κ, ‖Dirac.gamma κ‖
  have hG : 0 ≤ G := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨4 * (‖A‖ * G * ‖B‖ * G), by positivity, fun x y => ?_⟩
  refine (insNorm_trace_le _).trans ?_
  have h1 := norm_mul_le A (Dirac.slash x * (B * Dirac.slash y))
  have h2 := norm_mul_le (Dirac.slash x) (B * Dirac.slash y)
  have h3 := norm_mul_le B (Dirac.slash y)
  have hx := insNorm_slash_le x
  have hy := insNorm_slash_le y
  have := norm_nonneg A
  have := norm_nonneg B
  have := norm_nonneg (Dirac.slash x)
  have := norm_nonneg (Dirac.slash y)
  have := norm_nonneg (B * Dirac.slash y)
  calc 4 * ‖A * (Dirac.slash x * (B * Dirac.slash y))‖
      ≤ 4 * (‖A‖ * (‖Dirac.slash x‖ * (‖B‖ * ‖Dirac.slash y‖))) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans
          (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))) (norm_nonneg _))
    _ ≤ 4 * (‖A‖ * ((G * ‖x‖) * (‖B‖ * (G * ‖y‖)))) := by gcongr
    _ = _ := by ring

end Sizes

theorem norm_insY_le (a : ℝ) (v : Fin 3 → ℝ) : ‖insY a v‖ ≤ |a| + ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [insY, Fin.cons_zero, Real.norm_eq_abs, abs_neg]
    linarith [norm_nonneg v]
  · simp only [insY, Fin.cons_succ]
    linarith [norm_le_pi_norm v j, abs_nonneg a]

theorem norm_eT_le : ‖eT‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [eT]

theorem abs_mul_apply_le {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (p : Fin 4 → ℝ) (i : Fin 4) :
    |u * p i| ≤ ‖p‖ := by
  rw [abs_mul, abs_of_nonneg hu.1]
  have h := norm_le_pi_norm p i
  rw [Real.norm_eq_abs] at h
  nlinarith [abs_nonneg (p i), hu.2]

section Coeffs

variable (A B : Mat) (d₂ dm : ℝ)

theorem insBd_al : InsBd 2 fun p u v => insAl (u * p 0) v := by
  refine ⟨3, by norm_num, fun p u v hu => ?_⟩
  have ha := abs_mul_apply_le hu p 0
  have hv : ∀ k, v k ^ 2 ≤ ‖v‖ ^ 2 := fun k => by
    have := norm_le_pi_norm v k
    rw [Real.norm_eq_abs] at this
    nlinarith [abs_nonneg (v k), sq_abs (v k)]
  have hR := one_le_insR p v
  have hp := norm_nonneg p
  have hvn := norm_nonneg v
  unfold insAl
  rw [Complex.norm_real, Real.norm_eq_abs, Fin.sum_univ_three]
  have h0 := sq_nonneg (v 0)
  have h1 := sq_nonneg (v 1)
  have h2 := sq_nonneg (v 2)
  have ha2 : (u * p 0) ^ 2 ≤ ‖p‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  rw [abs_le]
  constructor <;> nlinarith [hv 0, hv 1, hv 2]

theorem insBd_a : InsBd 1 fun p u _ => ((u * p 0 : ℝ) : ℂ) := by
  refine ⟨1, zero_le_one, fun p u v hu => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, pow_one, one_mul]
  linarith [abs_mul_apply_le hu p 0, norm_nonneg v]

theorem insBd_t0 : InsBd 2 fun p u v => insT0' A B p (u * p 0) v := by
  obtain ⟨C, hC, h⟩ := exists_norm_insTau_le A B
  refine ⟨2 * C, by positivity, fun p u v hu => ?_⟩
  have hY := norm_insY_le (u * p 0) v
  have ha := abs_mul_apply_le hu p 0
  have hXY : ‖p + insY (u * p 0) v‖ ≤ 2 * (1 + ‖p‖ + ‖v‖) :=
    (norm_add_le _ _).trans (by linarith [norm_nonneg v])
  have hY' : ‖insY (u * p 0) v‖ ≤ 1 + ‖p‖ + ‖v‖ := by linarith
  refine (h _ _).trans ?_
  calc C * (‖p + insY (u * p 0) v‖ * ‖insY (u * p 0) v‖)
      ≤ C * ((2 * (1 + ‖p‖ + ‖v‖)) * (1 + ‖p‖ + ‖v‖)) := by gcongr
    _ = _ := by ring

theorem insBd_t1 : InsBd 1 fun p u v => insT1' A B p (u * p 0) v := by
  obtain ⟨C, hC, h⟩ := exists_norm_insTau_le A B
  refine ⟨3 * C, by positivity, fun p u v hu => ?_⟩
  have hY := norm_insY_le (u * p 0) v
  have ha := abs_mul_apply_le hu p 0
  have he := norm_eT_le
  have hXY : ‖p + insY (u * p 0) v‖ ≤ 2 * (1 + ‖p‖ + ‖v‖) :=
    (norm_add_le _ _).trans (by linarith [norm_nonneg v])
  have hY' : ‖insY (u * p 0) v‖ ≤ 1 + ‖p‖ + ‖v‖ := by linarith
  refine (norm_add_le _ _).trans ?_
  have e1 := h eT (insY (u * p 0) v)
  have e2 := h (p + insY (u * p 0) v) eT
  have he0 := norm_nonneg eT
  calc ‖insTau A B eT (insY (u * p 0) v)‖ + ‖insTau A B (p + insY (u * p 0) v) eT‖
      ≤ C * (1 * (1 + ‖p‖ + ‖v‖)) + C * ((2 * (1 + ‖p‖ + ‖v‖)) * 1) := by
        refine add_le_add (e1.trans ?_) (e2.trans ?_) <;> gcongr
    _ = _ := by ring

theorem insBd_t2 : InsBd 0 fun _ _ _ => insT2' A B := InsBd.const _

/-- `ζ = -W(u)|_{M = 0} + iε`. -/
noncomputable def insZeta (ε : ℝ) (p : Fin 4 → ℝ) (u : ℝ) (v : Fin 3 → ℝ) : ℂ :=
  -(massW 0 0 p u v : ℂ) + ε * I

theorem insBd_zeta {ε : ℝ} (hε : 0 ≤ ε) : InsBd 2 fun p u v => insZeta ε p u v := by
  refine ⟨7 + ε, by positivity, fun p u v hu => ?_⟩
  set R := 1 + ‖p‖ + ‖v‖
  have hR := one_le_insR p v
  have hsq : ∀ k : Fin 3, (v k + u * p k.succ) ^ 2 ≤ R ^ 2 := fun k => by
    have h1 := norm_le_pi_norm v k
    rw [Real.norm_eq_abs] at h1
    have h2 := abs_mul_apply_le hu p k.succ
    have h3 : |v k + u * p k.succ| ≤ R := (abs_add_le _ _).trans (by linarith)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  have hd := QED.WickModel.VacuumPolarizationLimit.abs_dot_le p p
  have hu1 : 0 ≤ u * (1 - u) := mul_nonneg hu.1 (by linarith [hu.2])
  have hu2 : u * (1 - u) ≤ 1 := by nlinarith [hu.1, hu.2]
  have hpR : ‖p‖ ≤ R := by linarith [norm_nonneg v]
  have hp2 : 4 * (‖p‖ * ‖p‖) ≤ 4 * R ^ 2 := by nlinarith [norm_nonneg p]
  have hW : |massW 0 0 p u v| ≤ 7 * R ^ 2 := by
    simp only [massW, QED.WickModel.selfEnergyFeynmanMass, Fin.sum_univ_three]
    have hm : |u * (1 - u) * Minkowski.dot p p| ≤ 4 * R ^ 2 := by
      rw [abs_mul, abs_of_nonneg hu1]
      calc u * (1 - u) * |Minkowski.dot p p| ≤ 1 * (4 * R ^ 2) := by
            gcongr
            exact hd.trans hp2
        _ = _ := by ring
    have h0 := sq_nonneg (v 0 + u * p (0 : Fin 3).succ)
    have h1 := sq_nonneg (v 1 + u * p (1 : Fin 3).succ)
    have h2 := sq_nonneg (v 2 + u * p (2 : Fin 3).succ)
    rw [abs_le] at hm ⊢
    constructor <;> nlinarith [hsq 0, hsq 1, hsq 2]
  unfold insZeta
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Real.norm_of_nonneg hε]
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  nlinarith

end Coeffs

/-! ### The closed form with mass-independent coefficients -/

section Rewrite

variable (A B : Mat) (d₂ dm ε : ℝ)

/-- The coefficient of `z^{-5/2}`. -/
noncomputable def insA5 (p : Fin 4 → ℝ) (u : ℝ) (v : Fin 3 → ℝ) : ℂ :=
  (energyConst 3 : ℂ) * (insP0 A B d₂ p (u * p 0) v + insZeta ε p u v *
    insP2 A B d₂ dm p (u * p 0) v + insZeta ε p u v * insZeta ε p u v * insP4 A B dm)

/-- The coefficient of `z^{-3/2}`. -/
noncomputable def insA3 (p : Fin 4 → ℝ) (u : ℝ) (v : Fin 3 → ℝ) : ℂ :=
  -((energyConst 3 : ℂ) * (insP2 A B d₂ dm p (u * p 0) v +
      2 * insZeta ε p u v * insP4 A B dm)) +
    ((energyConst 2 - energyConst 3 : ℝ) : ℂ) * (insQ0 A B d₂ p (u * p 0) v +
      insZeta ε p u v * insQ2 A B d₂ dm)

/-- The coefficient of `z^{-1/2}`. -/
noncomputable def insA1 : ℂ :=
  (energyConst 3 : ℂ) * insP4 A B dm -
    ((energyConst 2 - energyConst 3 : ℝ) : ℂ) * insQ2 A B d₂ dm +
    ((energyConst 1 - 2 * energyConst 2 + energyConst 3 : ℝ) : ℂ) * insN4 A B d₂

theorem insBd_a5 (hε : 0 ≤ ε) : InsBd 4 (insA5 A B d₂ dm ε) := by
  have hP0 : InsBd 4 fun p u v => insP0 A B d₂ p (u * p 0) v :=
    ((InsBd.const (d₂ : ℂ)).mul (insBd_al)).mul (insBd_t0 A B)
  have hP2 : InsBd 2 fun p u v => insP2 A B d₂ dm p (u * p 0) v :=
    (((InsBd.const (-((dm : ℂ) - 2 * d₂))).mul insBd_al).mul
      (InsBd.const (A * B).trace)).add ((InsBd.const (2 * (dm : ℂ) - d₂)).mul (insBd_t0 A B))
  have hP4 : InsBd 0 fun _ _ _ => insP4 A B dm := InsBd.const _
  have hz := insBd_zeta hε
  exact InsBd.const_mul _ ((hP0.add (hz.mul hP2)).add ((hz.mul hz).mul hP4))

theorem insBd_a3 (hε : 0 ≤ ε) : InsBd 2 (insA3 A B d₂ dm ε) := by
  have hP2 : InsBd 2 fun p u v => insP2 A B d₂ dm p (u * p 0) v :=
    (((InsBd.const (-((dm : ℂ) - 2 * d₂))).mul insBd_al).mul
      (InsBd.const (A * B).trace)).add ((InsBd.const (2 * (dm : ℂ) - d₂)).mul (insBd_t0 A B))
  have hQ0 : InsBd 2 fun p u v => insQ0 A B d₂ p (u * p 0) v :=
    InsBd.const_mul _ (((insBd_al.mul (insBd_t2 A B)).add
      (((InsBd.const 2).mul insBd_a).mul (insBd_t1 A B))).sub (insBd_t0 A B))
  have hP4 : InsBd 0 fun _ _ _ => insP4 A B dm := InsBd.const _
  have hQ2 : InsBd 0 fun _ _ _ => insQ2 A B d₂ dm := InsBd.const _
  have hz := insBd_zeta hε
  exact (InsBd.const_mul _ (hP2.add (((InsBd.const 2).mul hz).mul hP4))).neg.add
    (InsBd.const_mul _ (hQ0.add (hz.mul hQ2)))

theorem insBd_a1 : InsBd 0 fun _ _ _ => insA1 A B d₂ dm := InsBd.const _

theorem insZ_eq_zeta (M : ℝ) (p : Fin 4 → ℝ) (u : ℝ) (v : Fin 3 → ℝ) :
    (M : ℂ) ^ 2 = insZeta ε p u v - insZ M ε p u v := by
  have h := QED.WickModel.VacuumPolarizationLimit.massW_sub_massW M 0 p u v
  unfold insZeta insZ
  have h' : (massW M M p u v : ℂ) = (massW 0 0 p u v : ℂ) + (M : ℂ) ^ 2 := by
    rw [show massW M M p u v = massW 0 0 p u v + M ^ 2 by linarith]
    push_cast
    ring
  rw [h']
  ring

/-- **The closed form with mass-independent coefficients.** -/
theorem insCF_eq {ε : ℝ} (hε : 0 < ε) (M : ℝ) (p : Fin 4 → ℝ) (u : ℝ) (v : Fin 3 → ℝ) :
    insCF A B d₂ dm M ε p u v =
      -(insA5 A B d₂ dm ε p u v * insZ M ε p u v ^ (-(5 / 2 : ℂ)) +
        insA3 A B d₂ dm ε p u v * insZ M ε p u v ^ (-(3 / 2 : ℂ)) +
        insA1 A B d₂ dm * insZ M ε p u v ^ (-(1 / 2 : ℂ))) := by
  set z := insZ M ε p u v
  have hz0 : z ≠ 0 :=
    slitPlane_ne_zero (QED.OneLoop.VertexLimit.mem_slitPlane_neg_add_mul_I hε _)
  have e1 : z * z ^ (-(5 / 2 : ℂ)) = z ^ (-(3 / 2 : ℂ)) := by
    rw [cpow_mul_self hz0]; norm_num
  have e2 : z * z ^ (-(3 / 2 : ℂ)) = z ^ (-(1 / 2 : ℂ)) := by
    rw [cpow_mul_self hz0]; norm_num
  have hM := insZ_eq_zeta ε M p u v
  unfold insCF insA5 insA3 insA1
  rw [hM]
  set ζ := insZeta ε p u v
  set K3 := (energyConst 3 : ℂ)
  set K2 := ((energyConst 2 - energyConst 3 : ℝ) : ℂ)
  linear_combination (-(K3 * (-insP2 A B d₂ dm p (u * p 0) v - 2 * ζ * insP4 A B dm) +
      K3 * insP4 A B dm * z)) * e1 + (-(K3 * insP4 A B dm - K2 * insQ2 A B d₂ dm)) * e2

end Rewrite

/-! ### The Pauli–Villars sum -/

section PV

variable {A B : Mat} (d₂ dm : ℝ) {ε : ℝ} (hε : 0 < ε) (cs Ms : Fin 3 → ℝ)
  (hc : ∑ i, cs i = 0) (hcM : ∑ i, cs i * Ms i ^ 2 = 0) (hle : ∀ i, Ms 0 ^ 2 ≤ Ms i ^ 2)

/-- `S_σ = ∑ c_i z_i^{-σ}`. -/
noncomputable def insS (ε : ℝ) (cs Ms : Fin 3 → ℝ) (σ : ℝ) (p : Fin 4 → ℝ) (u : ℝ)
    (v : Fin 3 → ℝ) : ℂ :=
  ∑ i, (cs i : ℂ) * insZ (Ms i) ε p u v ^ (-(σ : ℂ))

include hε in
theorem sum_insCF_eq (p : Fin 4 → ℝ) (u : ℝ) (v : Fin 3 → ℝ) :
    ∑ i, (cs i : ℂ) * insCF A B d₂ dm (Ms i) ε p u v =
      -(insA5 A B d₂ dm ε p u v * insS ε cs Ms (5 / 2) p u v +
        insA3 A B d₂ dm ε p u v * insS ε cs Ms (3 / 2) p u v +
        insA1 A B d₂ dm * insS ε cs Ms (1 / 2) p u v) := by
  simp only [insCF_eq A B d₂ dm hε, insS, Fin.sum_univ_three]
  push_cast
  ring

/-- The Pauli–Villars constant `∑ |c_i| (M_i² - M_0²)²`. -/
noncomputable def insCPV (cs Ms : Fin 3 → ℝ) : ℝ := ∑ i, |cs i| * (Ms i ^ 2 - Ms 0 ^ 2) ^ 2

include hε hc hcM hle in
theorem norm_insS_le {σ : ℝ} (hσ : 0 ≤ σ) (p : Fin 4 → ℝ) (u : ℝ) (v : Fin 3 → ℝ) :
    ‖insS ε cs Ms σ p u v‖ ≤
      σ * (σ + 1) * insCPV cs Ms * (max ε (massW (Ms 0) (Ms 0) p u v)) ^ (-(σ + 2)) := by
  have hW : ∀ i, massW (Ms i) (Ms i) p u v = massW 0 0 p u v + Ms i ^ 2 := fun i => by
    have := QED.WickModel.VacuumPolarizationLimit.massW_sub_massW (Ms i) 0 p u v
    linarith
  have hcW : ∑ i, cs i * massW (Ms i) (Ms i) p u v = 0 := by
    simp only [hW, Fin.sum_univ_three] at hc hcM ⊢
    linear_combination (massW 0 0 p u v) * hc + hcM
  have h := QED.WickModel.VacuumPolarizationLimit.norm_sum_cpow_le_two hε hσ
    (W := fun i => massW (Ms i) (Ms i) p u v) hc hcW
    (fun i => by simp only [hW]; linarith [hle i])
  have hs : ∀ i, massW (Ms i) (Ms i) p u v - massW (Ms 0) (Ms 0) p u v = Ms i ^ 2 - Ms 0 ^ 2 :=
    fun i => by rw [hW, hW]; ring
  unfold insS insZ insCPV
  refine h.trans_eq ?_
  simp only [hs]

end PV

/-! ### The exponent count -/

/-- `Rⁿ (max ε W₀)^{-(σ+2)} ≤ C (1 + ‖p‖)⁸ (1 + ‖v⃗‖)⁻⁴` for `n ≤ 4`, `2σ = n + 1`. -/
theorem rpow_key {ε : ℝ} (hε : 0 < ε) (M : ℝ) (p : Fin 4 → ℝ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (v : Fin 3 → ℝ) {n : ℕ} (hn : n ≤ 4) {σ : ℝ} (hσ : 2 * σ = n + 1) :
    (1 + ‖p‖ + ‖v‖) ^ n * (max ε (massW M M p u v)) ^ (-(σ + 2)) ≤
      (5 ^ 4 * 4 ^ 4 * ε ^ (-(σ + 2)) + 2 ^ 4 * (2 / 9 : ℝ) ^ (-(σ + 2))) *
        (1 + ‖p‖) ^ 8 * ((1 + ‖v‖) ^ 4)⁻¹ := by
  set P := 1 + ‖p‖ with hP
  set w := 1 + ‖v‖ with hw
  set R := 1 + ‖p‖ + ‖v‖ with hR
  set lam := max ε (massW M M p u v)
  have hp0 := norm_nonneg p
  have hv0 := norm_nonneg v
  have hP1 : 1 ≤ P := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hw0 : 0 < w := by linarith
  have hlam : 0 < lam := lt_max_of_lt_left hε
  have hσ0 : 0 ≤ σ := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hE1 : 0 ≤ (5 : ℝ) ^ 4 * 4 ^ 4 * ε ^ (-(σ + 2)) := by positivity
  have hE2 : 0 ≤ (2 : ℝ) ^ 4 * (2 / 9 : ℝ) ^ (-(σ + 2)) := by positivity
  have hP8 : 1 ≤ P ^ 8 := one_le_pow₀ hP1
  have hw4 : 0 < (w ^ 4)⁻¹ := by positivity
  rcases le_or_gt (4 * ‖p‖ + 2) ‖v‖ with hv | hv
  · -- outside the ball
    have hlow : 2 / 9 * w ^ 2 ≤ lam :=
      (QED.TwoLoop.NestedVPFubiniBound.massW_ge_of_large M p hu hv).trans (le_max_right _ _)
    have h1 : lam ^ (-(σ + 2)) ≤ (2 / 9 * w ^ 2) ^ (-(σ + 2)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
    have h2 : (2 / 9 * w ^ 2) ^ (-(σ + 2)) =
        (2 / 9 : ℝ) ^ (-(σ + 2)) * w ^ (-(n : ℝ) - 5) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast w 2,
        ← Real.rpow_mul hw0.le]
      congr 2
      push_cast
      linarith
    have hRw : R ≤ 2 * w := by linarith
    have h3 : R ^ n ≤ 2 ^ 4 * w ^ (n : ℝ) := by
      rw [Real.rpow_natCast]
      calc R ^ n ≤ (2 * w) ^ n := pow_le_pow_left₀ (by linarith) hRw n
        _ = 2 ^ n * w ^ n := mul_pow _ _ _
        _ ≤ 2 ^ 4 * w ^ n := by
          gcongr
          norm_num
    have h4 : w ^ (n : ℝ) * w ^ (-(n : ℝ) - 5) ≤ (w ^ 4)⁻¹ := by
      rw [← Real.rpow_add hw0, show (n : ℝ) + (-(n : ℝ) - 5) = -5 by ring]
      calc w ^ (-5 : ℝ) ≤ w ^ (-4 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hw1 (by norm_num)
        _ = (w ^ 4)⁻¹ := by
          rw [Real.rpow_neg hw0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
    have hwn : 0 ≤ w ^ (n : ℝ) := by positivity
    have hwm : 0 ≤ w ^ (-(n : ℝ) - 5) := by positivity
    have h9 : 0 ≤ (2 / 9 : ℝ) ^ (-(σ + 2)) := by positivity
    calc R ^ n * lam ^ (-(σ + 2))
        ≤ (2 ^ 4 * w ^ (n : ℝ)) * ((2 / 9 : ℝ) ^ (-(σ + 2)) * w ^ (-(n : ℝ) - 5)) :=
          mul_le_mul h3 (h1.trans h2.le) (by positivity) (by positivity)
      _ = 2 ^ 4 * (2 / 9 : ℝ) ^ (-(σ + 2)) * (w ^ (n : ℝ) * w ^ (-(n : ℝ) - 5)) := by ring
      _ ≤ 2 ^ 4 * (2 / 9 : ℝ) ^ (-(σ + 2)) * (w ^ 4)⁻¹ := by gcongr
      _ ≤ 2 ^ 4 * (2 / 9 : ℝ) ^ (-(σ + 2)) * P ^ 8 * (w ^ 4)⁻¹ := by
          rw [mul_assoc _ (P ^ 8)]
          gcongr
          exact le_mul_of_one_le_left hw4.le hP8
      _ ≤ _ := by
          gcongr
          linarith
  · -- inside the ball
    have h1 : lam ^ (-(σ + 2)) ≤ ε ^ (-(σ + 2)) :=
      Real.rpow_le_rpow_of_nonpos hε (le_max_left _ _) (by linarith)
    have hR5 : R ≤ 5 * P := by linarith
    have h3 : R ^ n ≤ 5 ^ 4 * P ^ 4 := by
      calc R ^ n ≤ (5 * P) ^ n := pow_le_pow_left₀ (by linarith) hR5 n
        _ ≤ (5 * P) ^ 4 := pow_le_pow_right₀ (by linarith) hn
        _ = 5 ^ 4 * P ^ 4 := mul_pow _ _ _
    have hw4P : w ≤ 4 * P := by linarith
    have h4 : 1 ≤ 4 ^ 4 * P ^ 4 * (w ^ 4)⁻¹ := by
      rw [← mul_pow, le_mul_inv_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hw0.le hw4P 4
    have hεσ : 0 ≤ ε ^ (-(σ + 2)) := by positivity
    calc R ^ n * lam ^ (-(σ + 2)) ≤ (5 ^ 4 * P ^ 4) * ε ^ (-(σ + 2)) :=
          mul_le_mul h3 h1 (by positivity) (by positivity)
      _ ≤ (5 ^ 4 * P ^ 4) * ε ^ (-(σ + 2)) * (4 ^ 4 * P ^ 4 * (w ^ 4)⁻¹) :=
          le_mul_of_one_le_right (by positivity) h4
      _ = 5 ^ 4 * 4 ^ 4 * ε ^ (-(σ + 2)) * P ^ 8 * (w ^ 4)⁻¹ := by ring
      _ ≤ _ := by
          gcongr
          linarith

end QED.ChainProof.SetANest

end
