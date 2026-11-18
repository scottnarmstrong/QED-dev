/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.VacuumPolarizationEnergyFirst
import QED.Integration.LoopBounds
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A bound on the one-loop vacuum polarization energy integral, polynomial in the photon momentum

Part of the Fubini condition `hG` of the nested-equals-joint theorem
`QED.TwoLoop.NestedVP.contractionValue₂_VP_eq_nested_energyFirst` (obligation O2-8). Packet 6b
(`QED.WickModel.VacuumPolarizationLimit.integrable_spatialG`) bounds the energy integral
`spatialG P ε k μ ν v` by `K (1 + ‖v‖)⁻⁵` with a constant `K` that depends on `k` only through an
existential. Here the dependence on `k` is made explicit: for `ε > 0` and the Pauli–Villars
conditions,

`‖spatialG P ε k μ ν v‖ ≤ C (1 + ‖k‖)^{17/2} (1 + ‖v‖)^{-7/2}`

with `C` depending only on the parameters, `ε`, `μ`, `ν` (`exists_norm_spatialG_le_poly`). The
proof splits the spatial momenta at `‖v‖ = 4‖k‖ + 2`. Outside, the Feynman mass term satisfies
`W₀ ≥ (2/9) (1 + ‖v‖)²` (`massW_ge_of_large`), and the packet-6b bound `norm_timeSum_le` with
`c = 2/9` gives `(1 + ‖k‖)³ (1 + ‖v‖)⁻⁵`. Inside, `max ε W₀ ≥ ε` and the Pauli–Villars
cancellation bounds give `(1 + ‖k‖)³ (1 + ‖v‖)²`, and `1 + ‖v‖ ≤ 4 (1 + ‖k‖)`.

The exponent `17/2 < 9` matters: the outer factor of the class decays like `(1 + |t|)⁻¹⁰` in the
photon energy, so the product is integrable in `t`.

Also: joint continuity of the closed forms in the photon momentum (`continuous_timeSum_joint`).

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.TwoLoop.NestedVPFubiniBound

open QED.WickModel QED.WickModel.VacuumPolarizationLimit QED.OneLoop

/-! ### The constant of the bracket is cubic in `k` -/

/-- The constant `C_A` with `constA P k μ ν ≤ C_A (1 + ‖k‖)³`. -/
noncomputable def constAPoly (P : Params) (μ ν : Fin 4) : ℝ :=
  8 * |alpha μ ν| + |alpha μ ν| * P.mass 0 ^ 2 + 24 + 4 * P.mass 0 ^ 2

theorem constAPoly_nonneg (P : Params) (μ ν : Fin 4) : 0 ≤ constAPoly P μ ν := by
  unfold constAPoly; positivity

theorem constA_le (P : Params) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    constA P k μ ν ≤ constAPoly P μ ν * (1 + ‖k‖) ^ 3 := by
  set u := 1 + ‖k‖ with hu
  have hK := norm_nonneg k
  have hu1 : 1 ≤ u := by linarith
  have hdot : |Minkowski.dot k k| ≤ 4 * u ^ 2 := by
    refine (abs_dot_le k k).trans ?_
    nlinarith
  have h2 : u ^ 2 ≤ u ^ 3 := by nlinarith
  have h0 : 1 ≤ u ^ 3 := by nlinarith
  have hα := abs_nonneg (alpha μ ν)
  have hm := sq_nonneg (P.mass 0)
  unfold constA constAPoly
  rw [← hu]
  have e1 : |alpha μ ν| * (3 * u ^ 2 + P.mass 0 ^ 2 + |Minkowski.dot k k|)
      ≤ |alpha μ ν| * (7 * u ^ 3 + P.mass 0 ^ 2 * u ^ 3) := by
    have hm3 : P.mass 0 ^ 2 ≤ P.mass 0 ^ 2 * u ^ 3 := le_mul_of_one_le_right hm h0
    exact mul_le_mul_of_nonneg_left (by nlinarith) hα
  have e2 : |alpha μ ν| ≤ |alpha μ ν| * u ^ 3 := le_mul_of_one_le_right hα h0
  have e3 : 4 * (6 * u + P.mass 0 ^ 2) * u ^ 2 ≤ (24 + 4 * P.mass 0 ^ 2) * u ^ 3 := by
    have : P.mass 0 ^ 2 * u ^ 2 ≤ P.mass 0 ^ 2 * u ^ 3 := mul_le_mul_of_nonneg_left h2 hm
    nlinarith
  nlinarith

/-! ### The Feynman mass term at large spatial momentum -/

/-- `‖v‖ ≤ √S + ‖b‖` where `S = ∑ (v_i + b_i)²`. -/
theorem norm_le_sqrt_add (v b : Fin 3 → ℝ) :
    ‖v‖ ≤ Real.sqrt (∑ i, (v i + b i) ^ 2) + ‖b‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have hk : (v i + b i) ^ 2 ≤ ∑ i, (v i + b i) ^ 2 :=
    Finset.single_le_sum (f := fun i => (v i + b i) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h1 : |v i + b i| ≤ Real.sqrt (∑ i, (v i + b i) ^ 2) := Real.abs_le_sqrt hk
  have h2 : |b i| ≤ ‖b‖ := by
    have := norm_le_pi_norm b i
    rwa [Real.norm_eq_abs] at this
  rw [Real.norm_eq_abs]
  calc |v i| = |(v i + b i) - b i| := by ring_nf
    _ ≤ |v i + b i| + |b i| := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2

/-- **Outside the ball `‖v‖ < 4‖k‖ + 2`**, `W₀ ≥ (2/9) (1 + ‖v‖)²`, uniformly in `x ∈ [0, 1]`. -/
theorem massW_ge_of_large (M : ℝ) (k : Fin 4 → ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    {v : Fin 3 → ℝ} (hv : 4 * ‖k‖ + 2 ≤ ‖v‖) :
    2 / 9 * (1 + ‖v‖) ^ 2 ≤ SelfEnergyLimit.massW M M k x v := by
  set K := ‖k‖
  set u := ‖v‖
  have hK : 0 ≤ K := norm_nonneg k
  set S := ∑ i : Fin 3, (v i + x * k i.succ) ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq := norm_le_sqrt_add v (fun i : Fin 3 => x * k i.succ)
  have hb := norm_shift_le k hx
  have hsqrt : u - K ≤ Real.sqrt S := by
    change ‖v‖ ≤ Real.sqrt S + ‖(fun i : Fin 3 => x * k i.succ)‖ at hsq
    linarith
  have hS' : (u - K) ^ 2 ≤ S := by
    have h0 : 0 ≤ u - K := by linarith
    calc (u - K) ^ 2 ≤ Real.sqrt S ^ 2 := by gcongr
      _ = S := Real.sq_sqrt hS0
  have hD : -K ^ 2 ≤ selfEnergyFeynmanMass M M (Minkowski.dot k k) x := by
    have e : selfEnergyFeynmanMass M M (Minkowski.dot k k) x
        = M ^ 2 + x * (1 - x) * Minkowski.dot k k := by
      unfold selfEnergyFeynmanMass
      ring
    rw [e]
    have hx1 : 0 ≤ x * (1 - x) := by nlinarith [hx.1, hx.2]
    have hx2 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
    have hd := abs_dot_le k k
    have hd' : -(4 * K ^ 2) ≤ Minkowski.dot k k := by
      have := neg_abs_le (Minkowski.dot k k)
      nlinarith
    have h3 : x * (1 - x) * (-(4 * K ^ 2)) ≤ x * (1 - x) * Minkowski.dot k k :=
      mul_le_mul_of_nonneg_left hd' hx1
    nlinarith [sq_nonneg M, sq_nonneg K]
  have hW : (u - K) ^ 2 - K ^ 2 ≤ SelfEnergyLimit.massW M M k x v := by
    simp only [SelfEnergyLimit.massW]
    rw [← hS]
    linarith
  refine le_trans ?_ hW
  nlinarith

/-! ### The pointwise bound on the closed forms -/

/-- The constant of the polynomial bound on `timeSum`. -/
noncomputable def constT (P : Params) (ε : ℝ) (μ ν : Fin 4) : ℝ :=
  π / 2 * (constAPoly P μ ν * (1 + ε) *
        (3 / 2 * (3 / 2 + 1) * constS₂ P * ε ^ (-(3 / 2 + 2 : ℝ))) * (4 : ℝ) ^ (11 / 2 : ℝ)
      + 3 / 2 * constS₁ P μ ν * ε ^ (-(3 / 2 + 1 : ℝ)) * (4 : ℝ) ^ (7 / 2 : ℝ))
    + π / 2 * (constAPoly P μ ν *
        (3 / 2 * (3 / 2 + 1) * constS₂ P * (2 / 9 : ℝ) ^ (-(3 / 2 + 2 : ℝ)))
      + 3 / 2 * constS₁ P μ ν * (2 / 9 : ℝ) ^ (-(3 / 2 + 1 : ℝ))) * (1 + ε)

theorem constS₂_nonneg (P : Params) : 0 ≤ constS₂ P :=
  Finset.sum_nonneg fun f _ => by positivity

theorem constS₁_nonneg {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (μ ν : Fin 4) : 0 ≤ constS₁ P μ ν :=
  Finset.sum_nonneg fun f _ =>
    mul_nonneg (abs_nonneg _) (sub_nonneg.2 (mass_sq_le hm hM₁ hM₂ f))

/-- `a^r b^{r'}` monotonicity helper: `u^p ≤ (4 s)^p` for `0 ≤ u ≤ 4 s`, `p ≥ 0`. -/
theorem rpow_le_four_mul_rpow {u s p : ℝ} (hu : 0 ≤ u) (hus : u ≤ 4 * s) (hp : 0 ≤ p) :
    u ^ p ≤ (4 : ℝ) ^ p * s ^ p := by
  have hs : 0 ≤ s := by linarith
  rw [← Real.mul_rpow (by norm_num) hs]
  exact Real.rpow_le_rpow hu hus hp

/-- **The closed forms are bounded polynomially in `k`**: for `ε > 0`, the Pauli–Villars
conditions and `x ∈ [0, 1]`,
`‖timeSum P ε k μ ν x v‖ ≤ C (1 + ‖k‖)^{17/2} (1 + ‖v‖)^{-7/2}`. -/
theorem norm_timeSum_le_poly {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (μ ν : Fin 4) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (v : Fin 3 → ℝ) :
    ‖timeSum P ε k μ ν x v‖
      ≤ constT P ε μ ν * (1 + ‖k‖) ^ (17 / 2 : ℝ) * (1 + ‖v‖) ^ (-(7 / 2 : ℝ)) := by
  set s := 1 + ‖k‖ with hs
  set u := 1 + ‖v‖ with hu
  have hs1 : 1 ≤ s := by linarith [norm_nonneg k]
  have hu1 : 1 ≤ u := by linarith [norm_nonneg v]
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := by linarith
  have hS₂ := constS₂_nonneg P
  have hS₁ := constS₁_nonneg hm hM₁ hM₂ μ ν
  have hCA := constAPoly_nonneg P μ ν
  have hA3 := constA_le P k μ ν
  have hCA0 : 0 ≤ constA P k μ ν := by unfold constA; positivity
  have hu72 : 0 < u ^ (-(7 / 2 : ℝ)) := Real.rpow_pos_of_pos hu0 _
  have hs3 : s ^ (3 : ℝ) * s ^ (11 / 2 : ℝ) = s ^ (17 / 2 : ℝ) := by
    rw [← Real.rpow_add hs0]; norm_num
  have hs3' : s ^ 3 = s ^ (3 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  have hs72 : s ^ (7 / 2 : ℝ) ≤ s ^ (17 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num)
  have hs3le : s ^ (3 : ℝ) ≤ s ^ (17 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num)
  -- the two constants
  set a₁ := constAPoly P μ ν * (1 + ε) * (3 / 2 * (3 / 2 + 1) * constS₂ P *
    ε ^ (-(3 / 2 + 2 : ℝ))) * (4 : ℝ) ^ (11 / 2 : ℝ) with ha₁
  set b₁ := 3 / 2 * constS₁ P μ ν * ε ^ (-(3 / 2 + 1 : ℝ)) * (4 : ℝ) ^ (7 / 2 : ℝ) with hb₁
  set c₂ := constAPoly P μ ν * (3 / 2 * (3 / 2 + 1) * constS₂ P * (2 / 9 : ℝ) ^ (-(3 / 2 + 2 : ℝ)))
    + 3 / 2 * constS₁ P μ ν * (2 / 9 : ℝ) ^ (-(3 / 2 + 1 : ℝ)) with hc₂
  have ha₁0 : 0 ≤ a₁ := by positivity
  have hb₁0 : 0 ≤ b₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hT : constT P ε μ ν = π / 2 * (a₁ + b₁) + π / 2 * c₂ * (1 + ε) := rfl
  rcases le_or_gt (4 * ‖k‖ + 2) ‖v‖ with hv | hv
  · -- outside the ball: the packet-6b bound with `c = 2/9`
    have hlow : 2 / 9 * (1 + ‖v‖) ^ 2
        ≤ max ε (SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v) :=
      (massW_ge_of_large _ k hx hv).trans (le_max_right _ _)
    have h := norm_timeSum_le hm hM₁ hM₂ hPV₁ hPV₂ k μ ν (by norm_num : (0 : ℝ) < 2 / 9) hε hx v
      hlow
    have hK : constK P k μ ν (2 / 9) ≤ π / 2 * c₂ * s ^ (3 : ℝ) := by
      have h0 : constA P k μ ν *
            (3 / 2 * (3 / 2 + 1) * constS₂ P * (2 / 9 : ℝ) ^ (-(3 / 2 + 2 : ℝ)))
          ≤ constAPoly P μ ν * s ^ 3 * (3 / 2 * (3 / 2 + 1) * constS₂ P *
            (2 / 9 : ℝ) ^ (-(3 / 2 + 2 : ℝ))) := by gcongr
      have h1 : 3 / 2 * constS₁ P μ ν * (2 / 9 : ℝ) ^ (-(3 / 2 + 1 : ℝ))
          ≤ 3 / 2 * constS₁ P μ ν * (2 / 9 : ℝ) ^ (-(3 / 2 + 1 : ℝ)) * s ^ 3 :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hs1)
      unfold constK
      calc _ ≤ π / 2 * (constAPoly P μ ν * s ^ 3 * (3 / 2 * (3 / 2 + 1) * constS₂ P *
            (2 / 9 : ℝ) ^ (-(3 / 2 + 2 : ℝ))) +
            3 / 2 * constS₁ P μ ν * (2 / 9 : ℝ) ^ (-(3 / 2 + 1 : ℝ)) * s ^ 3) :=
            mul_le_mul_of_nonneg_left (add_le_add h0 h1) (by positivity)
        _ = _ := by rw [hc₂, ← hs3']; ring
    have hu5 : u ^ (-(5 : ℝ)) ≤ u ^ (-(7 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
    refine h.trans ?_
    rw [hT]
    calc constK P k μ ν (2 / 9) * (1 + ε) * u ^ (-(5 : ℝ))
        ≤ π / 2 * c₂ * s ^ (3 : ℝ) * (1 + ε) * u ^ (-(7 / 2 : ℝ)) := by
          gcongr
      _ ≤ π / 2 * c₂ * s ^ (17 / 2 : ℝ) * (1 + ε) * u ^ (-(7 / 2 : ℝ)) := by gcongr
      _ ≤ π / 2 * (a₁ + b₁) * s ^ (17 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ)) +
            π / 2 * c₂ * s ^ (17 / 2 : ℝ) * (1 + ε) * u ^ (-(7 / 2 : ℝ)) :=
          le_add_of_nonneg_left (by positivity)
      _ = _ := by ring
  · -- inside the ball: `max ε W₀ ≥ ε`
    have hus : u ≤ 4 * s := by rw [hu, hs]; linarith
    set lam := max ε (SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v)
    have hlam : ε ≤ lam := le_max_left _ _
    have hA := norm_bracketA_le P hε k μ ν hx v
    have b2 := norm_sum_loopCoeff_cpow_le hm hM₁ hM₂ hPV₁ hPV₂ hε k x v
    have b1 := norm_sum_loopCoeff_bracketB_cpow_le hm hM₁ hM₂ hPV₁ hPV₂ hε k μ ν x v
    have r2 : lam ^ (-(3 / 2 + 2 : ℝ)) ≤ ε ^ (-(3 / 2 + 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hε hlam (by norm_num)
    have r1 : lam ^ (-(3 / 2 + 1 : ℝ)) ≤ ε ^ (-(3 / 2 + 1 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hε hlam (by norm_num)
    have hlam0 : 0 < lam := hε.trans_le hlam
    -- `u² ≤ 4^{11/2} s^{11/2} u^{-7/2}` and `1 ≤ 4^{7/2} s^{7/2} u^{-7/2}`
    have hu2 : u ^ 2 ≤ (4 : ℝ) ^ (11 / 2 : ℝ) * s ^ (11 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ)) := by
      have e : u ^ 2 = u ^ (11 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ)) := by
        rw [← Real.rpow_add hu0, ← Real.rpow_natCast]; norm_num
      rw [e]
      gcongr
      exact rpow_le_four_mul_rpow hu0.le hus (by norm_num)
    have hu1' : 1 ≤ (4 : ℝ) ^ (7 / 2 : ℝ) * s ^ (7 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ)) := by
      have e : (1 : ℝ) = u ^ (7 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ)) := by
        rw [← Real.rpow_add hu0]; norm_num
      rw [e]
      gcongr
      exact rpow_le_four_mul_rpow hu0.le hus (by norm_num)
    rw [timeSum_eq, norm_mul, SelfEnergyLimit.norm_ofReal_div_two_pi]
    set Z₂ := ∑ f, (P.loopCoeff f : ℂ) *
      (-(SelfEnergyLimit.massW (P.mass f) (P.mass f) k x v : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))
    set Z₁ := ∑ f, ((P.loopCoeff f * bracketB P μ ν f : ℝ) : ℂ) *
      (-(SelfEnergyLimit.massW (P.mass f) (P.mass f) k x v : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))
    have hZ₂ : ‖Z₂‖ ≤ 3 / 2 * (3 / 2 + 1) * constS₂ P * ε ^ (-(3 / 2 + 2 : ℝ)) :=
      b2.trans (by gcongr)
    have hZ₁ : ‖Z₁‖ ≤ 3 / 2 * constS₁ P μ ν * ε ^ (-(3 / 2 + 1 : ℝ)) :=
      b1.trans (by gcongr)
    have hAZ : ‖bracketA P ε k μ ν x v * Z₂ + Z₁‖
        ≤ constAPoly P μ ν * s ^ 3 * (1 + ε) * u ^ 2 *
            (3 / 2 * (3 / 2 + 1) * constS₂ P * ε ^ (-(3 / 2 + 2 : ℝ)))
          + 3 / 2 * constS₁ P μ ν * ε ^ (-(3 / 2 + 1 : ℝ)) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ hZ₁)
      rw [norm_mul]
      refine mul_le_mul (hA.trans ?_) hZ₂ (norm_nonneg _) (by positivity)
      gcongr
    have hfin : constAPoly P μ ν * s ^ 3 * (1 + ε) * u ^ 2 *
            (3 / 2 * (3 / 2 + 1) * constS₂ P * ε ^ (-(3 / 2 + 2 : ℝ)))
          + 3 / 2 * constS₁ P μ ν * ε ^ (-(3 / 2 + 1 : ℝ))
        ≤ (a₁ + b₁) * s ^ (17 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ)) := by
      have X0 : 0 ≤ constAPoly P μ ν * s ^ 3 * (1 + ε) *
          (3 / 2 * (3 / 2 + 1) * constS₂ P * ε ^ (-(3 / 2 + 2 : ℝ))) := by positivity
      have Y0 : 0 ≤ 3 / 2 * constS₁ P μ ν * ε ^ (-(3 / 2 + 1 : ℝ)) := by positivity
      have e1 : constAPoly P μ ν * s ^ 3 * (1 + ε) * u ^ 2 *
            (3 / 2 * (3 / 2 + 1) * constS₂ P * ε ^ (-(3 / 2 + 2 : ℝ)))
          ≤ a₁ * s ^ (17 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ)) := by
        calc constAPoly P μ ν * s ^ 3 * (1 + ε) * u ^ 2 *
              (3 / 2 * (3 / 2 + 1) * constS₂ P * ε ^ (-(3 / 2 + 2 : ℝ)))
            = (constAPoly P μ ν * s ^ 3 * (1 + ε) *
              (3 / 2 * (3 / 2 + 1) * constS₂ P * ε ^ (-(3 / 2 + 2 : ℝ)))) * u ^ 2 := by ring
          _ ≤ (constAPoly P μ ν * s ^ 3 * (1 + ε) *
              (3 / 2 * (3 / 2 + 1) * constS₂ P * ε ^ (-(3 / 2 + 2 : ℝ)))) *
              ((4 : ℝ) ^ (11 / 2 : ℝ) * s ^ (11 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hu2 X0
          _ = a₁ * (s ^ (3 : ℝ) * s ^ (11 / 2 : ℝ)) * u ^ (-(7 / 2 : ℝ)) := by
            rw [ha₁, hs3']; ring
          _ = a₁ * s ^ (17 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ)) := by rw [hs3]
      have e2 : 3 / 2 * constS₁ P μ ν * ε ^ (-(3 / 2 + 1 : ℝ))
          ≤ b₁ * s ^ (17 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ)) := by
        calc 3 / 2 * constS₁ P μ ν * ε ^ (-(3 / 2 + 1 : ℝ))
            ≤ 3 / 2 * constS₁ P μ ν * ε ^ (-(3 / 2 + 1 : ℝ)) *
              ((4 : ℝ) ^ (7 / 2 : ℝ) * s ^ (7 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ))) :=
            le_mul_of_one_le_right Y0 hu1'
          _ = b₁ * s ^ (7 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ)) := by rw [hb₁]; ring
          _ ≤ b₁ * s ^ (17 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ)) := by gcongr
      linarith
    rw [hT]
    have hpi : 0 ≤ π / 2 := by positivity
    have hc : 0 ≤ π / 2 * c₂ * (1 + ε) * s ^ (17 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ)) := by positivity
    calc π / 2 * ‖bracketA P ε k μ ν x v * Z₂ + Z₁‖
        ≤ π / 2 * ((a₁ + b₁) * s ^ (17 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hAZ.trans hfin) hpi
      _ ≤ π / 2 * ((a₁ + b₁) * s ^ (17 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ))) +
            π / 2 * c₂ * (1 + ε) * s ^ (17 / 2 : ℝ) * u ^ (-(7 / 2 : ℝ)) :=
          le_add_of_nonneg_right hc
      _ = _ := by ring

theorem constT_nonneg {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    {ε : ℝ} (hε : 0 < ε) (μ ν : Fin 4) : 0 ≤ constT P ε μ ν := by
  have hS₂ := constS₂_nonneg P
  have hS₁ := constS₁_nonneg hm hM₁ hM₂ μ ν
  have hCA := constAPoly_nonneg P μ ν
  unfold constT
  positivity

/-- **The energy integral is bounded polynomially in the photon momentum**: for `ε > 0` and the
Pauli–Villars conditions there is `C ≥ 0`, depending only on the parameters, `ε`, `μ` and `ν`, with
`‖spatialG P ε k μ ν v‖ ≤ C (1 + ‖k‖)^{17/2} (1 + ‖v‖)^{-7/2}` for all `k`, `v`. -/
theorem exists_norm_spatialG_le_poly {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {ε : ℝ} (hε : 0 < ε) (μ ν : Fin 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin 4 → ℝ) (v : Fin 3 → ℝ),
      ‖spatialG P ε k μ ν v‖ ≤ C * (1 + ‖k‖) ^ (17 / 2 : ℝ) * (1 + ‖v‖) ^ (-(7 / 2 : ℝ)) := by
  set V := (volume.restrict (Ioc (0 : ℝ) 1)).real univ
  have hV : 0 ≤ V := measureReal_nonneg
  refine ⟨‖kappa P.e‖ * constT P ε μ ν * V,
    by have := constT_nonneg hm hM₁ hM₂ hε μ ν; positivity, fun k v => ?_⟩
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun x => kappa P.e * timeSum P ε k μ ν x v)
    (C := ‖kappa P.e‖ * (constT P ε μ ν * (1 + ‖k‖) ^ (17 / 2 : ℝ) * (1 + ‖v‖) ^ (-(7 / 2 : ℝ))))
    ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_timeSum_le_poly hm hM₁ hM₂ hPV₁ hPV₂ hε k μ ν
        (Ioc_subset_Icc_self hx) v) (norm_nonneg _))
  refine (show ‖spatialG P ε k μ ν v‖ ≤ _ from h).trans (le_of_eq ?_)
  ring

/-! ### Joint continuity in the photon momentum -/

/-- The numerator is jointly continuous in the photon and loop momenta. -/
theorem continuous_numer_joint (M : ℝ) (μ ν : Fin 4) :
    Continuous fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => numer M p.1 p.2 μ ν := by
  have hd := VertexLimit.continuous_dot_comp (f := fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => p.2 + p.1)
    (g := fun p => p.2) (by fun_prop) (by fun_prop)
  have h1 : Continuous fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => (p.2 + p.1) μ :=
    (continuous_apply μ).comp (by fun_prop)
  have h2 : Continuous fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => (p.2 + p.1) ν :=
    (continuous_apply ν).comp (by fun_prop)
  have h3 : Continuous fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => p.2 μ :=
    (continuous_apply μ).comp continuous_snd
  have h4 : Continuous fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => p.2 ν :=
    (continuous_apply ν).comp continuous_snd
  unfold numer
  fun_prop

/-- **The closed form is jointly continuous** in the photon momentum, the spatial loop momentum
and the Feynman parameter, for `ε > 0`. -/
theorem continuous_timeT_joint {ε : ℝ} (hε : 0 < ε) (M : ℝ) (μ ν : Fin 4) :
    Continuous fun q : (Fin 4 → ℝ) × (Fin 3 → ℝ) × ℝ => timeT M ε q.1 μ ν q.2.2 q.2.1 := by
  have hdk := VertexLimit.continuous_dot_comp
    (f := fun q : (Fin 4 → ℝ) × (Fin 3 → ℝ) × ℝ => q.1) (g := fun q => q.1)
    continuous_fst continuous_fst
  have hW : Continuous fun q : (Fin 4 → ℝ) × (Fin 3 → ℝ) × ℝ =>
      SelfEnergyLimit.massW M M q.1 q.2.2 q.2.1 := by
    simp only [SelfEnergyLimit.massW, selfEnergyFeynmanMass, Fin.sum_univ_three]
    have a0 : Continuous fun q : (Fin 4 → ℝ) × (Fin 3 → ℝ) × ℝ => q.2.1 0 :=
      (continuous_apply 0).comp (by fun_prop)
    have a1 : Continuous fun q : (Fin 4 → ℝ) × (Fin 3 → ℝ) × ℝ => q.2.1 1 :=
      (continuous_apply 1).comp (by fun_prop)
    have a2 : Continuous fun q : (Fin 4 → ℝ) × (Fin 3 → ℝ) × ℝ => q.2.1 2 :=
      (continuous_apply 2).comp (by fun_prop)
    have b0 : Continuous fun q : (Fin 4 → ℝ) × (Fin 3 → ℝ) × ℝ => q.1 (Fin.succ 0) :=
      (continuous_apply _).comp continuous_fst
    have b1 : Continuous fun q : (Fin 4 → ℝ) × (Fin 3 → ℝ) × ℝ => q.1 (Fin.succ 1) :=
      (continuous_apply _).comp continuous_fst
    have b2 : Continuous fun q : (Fin 4 → ℝ) × (Fin 3 → ℝ) × ℝ => q.1 (Fin.succ 2) :=
      (continuous_apply _).comp continuous_fst
    fun_prop
  have hX : Continuous fun q : (Fin 4 → ℝ) × (Fin 3 → ℝ) × ℝ =>
      (-(SelfEnergyLimit.massW M M q.1 q.2.2 q.2.1 : ℂ) + ε * I) := by fun_prop
  have h32 := hX.cpow (continuous_const (y := -(3 / 2 : ℂ)))
    (fun q => VertexLimit.mem_slitPlane_neg_add_mul_I hε _)
  have hk0 : Continuous fun q : (Fin 4 → ℝ) × (Fin 3 → ℝ) × ℝ => q.1 0 :=
    (continuous_apply 0).comp continuous_fst
  have hcons : Continuous fun q : (Fin 4 → ℝ) × (Fin 3 → ℝ) × ℝ =>
      (Fin.cons (-(q.2.2 * q.1 0)) q.2.1 : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) (by fun_prop) (by fun_prop)
  have hN := continuous_ofReal.comp ((continuous_numer_joint M μ ν).comp
    (continuous_fst.prodMk hcons))
  simp only [Function.comp_def] at hN
  unfold timeT
  fun_prop

/-- The Pauli–Villars sum of closed forms is jointly continuous, for `ε > 0`. -/
theorem continuous_timeSum_joint {ε : ℝ} (hε : 0 < ε) (P : Params) (μ ν : Fin 4) :
    Continuous fun q : (Fin 4 → ℝ) × (Fin 3 → ℝ) × ℝ => timeSum P ε q.1 μ ν q.2.2 q.2.1 := by
  unfold timeSum
  exact continuous_finsetSum _ fun f _ => continuous_const.mul (continuous_timeT_joint hε _ μ ν)

end QED.TwoLoop.NestedVPFubiniBound

end
