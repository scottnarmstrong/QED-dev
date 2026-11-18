/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroKinematics
import QED.Algebra.Spinor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Obligation O2-22 reduced to a one-variable limit

Part of obligation O2-22 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4): at fixed regulators the
Pauli component of the order-`e⁵` vertex limit should have a limit as `q² → 0⁺`, uniformly over
on-shell positive-energy pairs. Since the Pauli projection depends on the pair only through `q²`
(`QED.TwoLoop.PauliZero.formFactorProj₂_eq_of_dot_sub_eq`), the uniform statement is equivalent
to the limit of one function of one variable.

* `restMomentum m = (m, 0, 0, 0)` and `boostMomentum m Q = (m + Q/2m, √(Q + Q²/4m²), 0, 0)`: an
  on-shell positive-energy pair with `q² = Q` (`dot_boostMomentum_sub_restMomentum`).
* `pauliAt P e Q`: the Pauli projection `P₂` of the vertex limit at this pair.
* `formFactorProj₂_eq_pauliAt`: at every on-shell positive-energy pair with `q² = Q ≥ 0`, the
  Pauli projection of every vertex limit is `pauliAt P e Q`.
* `uniform_iff_tendsto_pauliAt`: **the uniform statement of O2-22 for the value `a` is equivalent
  to `pauliAt P e Q → a` as `Q → 0⁺`**, and `existsUnique_uniform_iff`: the `∃!` form.
* `uniform_isFormFactorPair_of_tendsto_pauliAt`: the same conclusion for the Pauli components of
  the form-factor pairs (G₀), for `e ≠ 0`.

## The `1/q²` of the projector

`P₂ V = m N(V)/(e Q D²)` with `N(V) = m D T₁ + (Q - 2m²) T₂`, `Q = q²`, `D = 4m² + Q`. At `q = 0`
(`p' = p`) the numerator vanishes for **every** matrix family `V`
(`formFactorProj₂_numerator_self`), since `(m - p̸) γ_μ (m - p̸) = 2 p_μ (m - p̸)` and
`(m - p̸)² = 2m (m - p̸)` give `T₂ = 2m T₁`. This is the zeroth order of the cancellation of the
`1/Q`. The limit `pauliAt P e Q` as `Q → 0⁺` is **not** proved here. On shell at `q = 0` the
vertex only shows `F₁ + F₂`, so the limit needs the momentum dependence of `V` to second order
along a curve of pairs: `N` vanishes at `q = 0`, its first order vanishes by the reflection in the
spatial direction of `q` (a spacelike reflection fixing `p`), and the limit is the second-order
coefficient divided by `4m²`. At the level of the parametric integrands this needs the projected
coefficients to be polynomial in the curve parameter (after clearing denominators) with
integrable coefficient functions; the class numerators are currently available only as loop
quartics at fixed external momenta (`exists_loopQuartic`), without that joint structure.
-/

@[expose] public section

open Complex Matrix Filter Topology

namespace QED.TwoLoop.PauliZero

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### The zeroth order of the cancellation -/

/-- `(m - p̸) γ_μ (m - p̸) = 2 p_μ (m - p̸)` on shell. -/
theorem mass_sub_slash_mul_gammaLower_mul (m : ℝ) (p : Fin 4 → ℝ)
    (hp : Minkowski.dot p p = -m ^ 2) (μ : Fin 4) :
    ((m : ℂ) • 𝟙 - slash p) * gammaLower μ * ((m : ℂ) • 𝟙 - slash p) =
      ((2 * Minkowski.lower p μ : ℝ) : ℂ) • ((m : ℂ) • 𝟙 - slash p) := by
  have ha := gammaLower_slash_anticomm μ p
  have hγ : gammaLower μ * ((m : ℂ) • 𝟙 - slash p) =
      ((m : ℂ) • 𝟙 + slash p) * gammaLower μ +
        ((2 * Minkowski.lower p μ : ℝ) : ℂ) • 𝟙 := by
    have e : gammaLower μ * slash p =
        ((-2 * Minkowski.lower p μ : ℝ) : ℂ) • 𝟙 - slash p * gammaLower μ := by
      rw [← ha]; abel
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, e, Matrix.add_mul, Matrix.smul_mul,
      Matrix.one_mul]
    push_cast
    module
  have hz : ((m : ℂ) • 𝟙 - slash p) * ((m : ℂ) • 𝟙 + slash p) = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, slash_mul_slash, hp]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
    push_cast
    module
  rw [Matrix.mul_assoc, hγ, Matrix.mul_add, ← Matrix.mul_assoc, hz, Matrix.zero_mul, zero_add,
    Matrix.mul_smul, Matrix.mul_one]

/-- At `p' = p`, `T₂ = 2m T₁` for every matrix family `V`. -/
theorem traceVecProj_self (m : ℝ) (p : Fin 4 → ℝ) (hp : Minkowski.dot p p = -m ^ 2)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    traceVecProj m p p (p + p) V = 2 * m * traceGammaProj m p p V := by
  unfold traceVecProj traceGammaProj
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h1 : trace (((m : ℂ) • 𝟙 - slash p) * V μ * ((m : ℂ) • 𝟙 - slash p) * gammaLower μ) =
      ((2 * Minkowski.lower p μ : ℝ) : ℂ) * trace (V μ * ((m : ℂ) • 𝟙 - slash p)) := by
    rw [show ((m : ℂ) • 𝟙 - slash p) * V μ * ((m : ℂ) • 𝟙 - slash p) * gammaLower μ =
        ((m : ℂ) • 𝟙 - slash p) * V μ * (((m : ℂ) • 𝟙 - slash p) * gammaLower μ) by
          simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, ← Matrix.mul_assoc, mass_sub_slash_mul_gammaLower_mul m p hp,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      Matrix.trace_mul_comm ((m : ℂ) • 𝟙 - slash p) (V μ)]
  have h2 : trace (((m : ℂ) • 𝟙 - slash p) * V μ * ((m : ℂ) • 𝟙 - slash p)) =
      (2 * m : ℂ) * trace (V μ * ((m : ℂ) • 𝟙 - slash p)) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, mass_sub_slash_sq m p hp, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm ((m : ℂ) • 𝟙 - slash p) (V μ)]
  rw [h1, h2]
  have hl : Minkowski.lower (p + p) μ = 2 * Minkowski.lower p μ := by
    rw [Minkowski.lower_eq, Minkowski.lower_eq]
    fin_cases μ <;> simp <;> ring
  rw [hl]
  push_cast
  ring

/-- **The numerator of the Pauli projector vanishes at `q = 0`**: for on-shell `p` and every
matrix family `V`, `m D T₁ + (Q - 2m²) T₂ = 0` at `p' = p`, where `Q = 0`, `D = 4m²`. -/
theorem formFactorProj₂_numerator_self (m : ℝ) (p : Fin 4 → ℝ) (hp : Minkowski.dot p p = -m ^ 2)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    (m : ℂ) * (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p - p) (p - p) : ℂ)) * traceGammaProj m p p V +
      ((Minkowski.dot (p - p) (p - p) : ℂ) - 2 * (m : ℂ) ^ 2) * traceVecProj m p p (p + p) V =
      0 := by
  rw [traceVecProj_self m p hp, sub_self]
  simp only [Minkowski.dot_eq, Pi.zero_apply]
  push_cast
  ring

/-! ### The canonical pairs -/

/-- The electron at rest, `(m, 0, 0, 0)`. -/
def restMomentum (m : ℝ) : Fin 4 → ℝ := ![m, 0, 0, 0]

/-- The outgoing momentum `(m + Q/2m, √(Q + Q²/4m²), 0, 0)`, with `q² = Q` against
`restMomentum m`. -/
noncomputable def boostMomentum (m Q : ℝ) : Fin 4 → ℝ :=
  ![m + Q / (2 * m), Real.sqrt (Q + Q ^ 2 / (4 * m ^ 2)), 0, 0]

section Canonical

variable {m : ℝ} (hm : 0 < m)
include hm

omit hm in
theorem dot_restMomentum : Minkowski.dot (restMomentum m) (restMomentum m) = -m ^ 2 := by
  simp [Minkowski.dot_eq, restMomentum]
  ring

theorem restMomentum_pos : 0 < restMomentum m 0 := by
  simpa [restMomentum] using hm

theorem sq_sqrt_boost {Q : ℝ} (hQ : 0 ≤ Q) :
    Real.sqrt (Q + Q ^ 2 / (4 * m ^ 2)) ^ 2 = Q + Q ^ 2 / (4 * m ^ 2) :=
  Real.sq_sqrt (by positivity)

theorem dot_boostMomentum {Q : ℝ} (hQ : 0 ≤ Q) :
    Minkowski.dot (boostMomentum m Q) (boostMomentum m Q) = -m ^ 2 := by
  simp only [Minkowski.dot_eq, boostMomentum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [Real.mul_self_sqrt (by positivity)]
  field_simp
  ring

theorem boostMomentum_pos {Q : ℝ} (hQ : 0 ≤ Q) : 0 < boostMomentum m Q 0 := by
  simp only [boostMomentum, Matrix.cons_val_zero]
  positivity

theorem dot_boostMomentum_sub_restMomentum {Q : ℝ} (hQ : 0 ≤ Q) :
    Minkowski.dot (boostMomentum m Q - restMomentum m) (boostMomentum m Q - restMomentum m) =
      Q := by
  simp only [Minkowski.dot_eq, boostMomentum, restMomentum, Pi.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, sub_zero]
  rw [Real.mul_self_sqrt (by positivity)]
  field_simp
  ring

end Canonical

/-! ### The Pauli projection as a function of `q²` -/

/-- The `ε → 0⁺` limit of the order-`e⁵` vertex, entrywise (`limUnder`). -/
noncomputable def vertexLimitAt (P : Params) (p' p : Fin 4 → ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun i j =>
    limUnder (𝓝[>] (0 : ℝ)) fun ε => vertexOrderFive { P with ε := ε } p' p μ i j

theorem isVertexOrderFiveLimit_vertexLimitAt (P : Params) {p' p : Fin 4 → ℝ}
    (h : ∃ V, IsVertexOrderFiveLimit P p' p V) :
    IsVertexOrderFiveLimit P p' p (vertexLimitAt P p' p) := by
  obtain ⟨V, hV⟩ := h
  intro μ i j
  simp only [vertexLimitAt, Matrix.of_apply]
  rw [(hV μ i j).limUnder_eq]
  exact hV μ i j

/-- **The Pauli projection of the vertex limit at the canonical pair with `q² = Q`.** -/
noncomputable def pauliAt (P : Params) (e Q : ℝ) : ℂ :=
  QED.OneLoop.formFactorProj₂ e P.m (boostMomentum P.m Q) (restMomentum P.m)
    (vertexLimitAt P (boostMomentum P.m Q) (restMomentum P.m))

section Reduction

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁)
  (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
  (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
include hm hmγ hΛ hM₁ hM₂ hc₁ hc₂

theorem isVertexOrderFiveLimit_pauliAt {Q : ℝ} (hQ : 0 ≤ Q) :
    IsVertexOrderFiveLimit P (boostMomentum P.m Q) (restMomentum P.m)
      (vertexLimitAt P (boostMomentum P.m Q) (restMomentum P.m)) :=
  isVertexOrderFiveLimit_vertexLimitAt P (VertexLimit.exists_isVertexOrderFiveLimit P hm hmγ hΛ
    hM₁ hM₂ hc₁ hc₂ (dot_restMomentum (m := P.m)) (dot_boostMomentum hm hQ) (restMomentum_pos hm)
    (boostMomentum_pos hm hQ) ((dot_boostMomentum_sub_restMomentum hm hQ).symm ▸ hQ))

/-- **The Pauli projection of every vertex limit is `pauliAt P e (q²)`**, at every on-shell
positive-energy pair with `q² ≥ 0`. -/
theorem formFactorProj₂_eq_pauliAt {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0) (hp0' : 0 < p' 0)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsVertexOrderFiveLimit P p' p V) (e : ℝ) :
    QED.OneLoop.formFactorProj₂ e P.m p' p V = pauliAt P e (Minkowski.dot (p' - p) (p' - p)) :=
  (formFactorProj₂_eq_of_dot_sub_eq P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hp0 hp0'
    (dot_restMomentum (m := P.m)) (dot_boostMomentum hm hq) (restMomentum_pos hm)
    (boostMomentum_pos hm hq) (dot_boostMomentum_sub_restMomentum hm hq) hq hV
    (isVertexOrderFiveLimit_pauliAt P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hq) e).symm

/-- The uniform statement of O2-22 for the value `a`, in terms of the Pauli projection: for every
`η > 0` there is `q₀ > 0` such that at every on-shell positive-energy pair with `0 < q² < q₀`,
every `ε → 0⁺` limit `V` of the order-`e⁵` vertex has `‖P₂ V - a‖ < η`. -/
def IsUniformPauliLimit (P : Params) (e : ℝ) (a : ℂ) : Prop :=
  ∀ η > 0, ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p p = -P.m ^ 2 →
    Minkowski.dot p' p' = -P.m ^ 2 → 0 < p 0 → 0 < p' 0 →
    0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
    ∀ V, IsVertexOrderFiveLimit P p' p V → ‖QED.OneLoop.formFactorProj₂ e P.m p' p V - a‖ < η

omit hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ in
theorem tendsto_nhdsWithin_Ioi_iff_uniform {f : ℝ → ℂ} {a : ℂ} :
    Tendsto f (𝓝[>] 0) (𝓝 a) ↔ ∀ η > 0, ∃ q₀ > 0, ∀ Q, 0 < Q → Q < q₀ → ‖f Q - a‖ < η := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  refine forall₂_congr fun η _ => exists_congr fun q₀ => and_congr_right fun _ =>
    ⟨fun h Q hQ hQ₀ => ?_, fun h Q hQ hQ₀ => ?_⟩
  · rw [← dist_eq_norm]
    exact h (Set.mem_Ioi.mpr hQ) (by rw [Real.dist_eq, sub_zero, abs_of_pos hQ]; exact hQ₀)
  · rw [dist_eq_norm]
    have hQ' : (0 : ℝ) < Q := hQ
    exact h Q hQ' (by rw [Real.dist_eq, sub_zero, abs_of_pos hQ'] at hQ₀; exact hQ₀)

/-- **O2-22 reduced to one variable**: the uniform statement for the value `a` holds if and only
if `pauliAt P e Q → a` as `Q → 0⁺`. -/
theorem uniform_iff_tendsto_pauliAt (e : ℝ) (a : ℂ) :
    IsUniformPauliLimit P e a ↔ Tendsto (pauliAt P e) (𝓝[>] 0) (𝓝 a) := by
  rw [tendsto_nhdsWithin_Ioi_iff_uniform]
  refine forall₂_congr fun η _ => ⟨fun ⟨q₀, hq₀, h⟩ => ⟨q₀, hq₀, fun Q hQ hQ₀ => ?_⟩,
    fun ⟨q₀, hq₀, h⟩ => ⟨q₀, hq₀, fun p' p hp hp' hp0 hp0' hq hq₀' V hV => ?_⟩⟩
  · have hd := dot_boostMomentum_sub_restMomentum hm hQ.le
    have := h (boostMomentum P.m Q) (restMomentum P.m) (dot_restMomentum (m := P.m))
      (dot_boostMomentum hm hQ.le) (restMomentum_pos hm) (boostMomentum_pos hm hQ.le)
      (hd.symm ▸ hQ) (hd.symm ▸ hQ₀) _
      (isVertexOrderFiveLimit_pauliAt P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hQ.le)
    exact this
  · rw [formFactorProj₂_eq_pauliAt P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hp0 hp0' hq.le hV]
    exact h _ hq hq₀'

/-- **The `∃!` form of O2-22 reduced to one variable**: there is exactly one `a` with the
uniform property if and only if `pauliAt P e` has a limit as `Q → 0⁺`. -/
theorem existsUnique_uniform_iff (e : ℝ) :
    (∃! a, IsUniformPauliLimit P e a) ↔ ∃ a, Tendsto (pauliAt P e) (𝓝[>] 0) (𝓝 a) := by
  simp only [uniform_iff_tendsto_pauliAt P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂]
  exact ⟨fun ⟨a, ha, _⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha, fun b hb => tendsto_nhds_unique hb ha⟩⟩

/-- **The uniform statement for the form-factor pairs**: if `pauliAt P P.e Q → a` as `Q → 0⁺` and
`e ≠ 0`, then for every `η > 0` there is `q₀ > 0` such that every form-factor pair (G₀) of every
vertex limit at every on-shell positive-energy pair with `0 < q² < q₀` has `‖F₂ - a‖ < η`. -/
theorem uniform_isFormFactorPair_of_tendsto_pauliAt (he : P.e ≠ 0) {a : ℂ}
    (ha : Tendsto (pauliAt P P.e) (𝓝[>] 0) (𝓝 a)) :
    ∀ η > 0, ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p p = -P.m ^ 2 →
      Minkowski.dot p' p' = -P.m ^ 2 → 0 < p 0 → 0 < p' 0 →
      0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
      ∀ V, IsVertexOrderFiveLimit P p' p V → ∀ F : ℂ × ℂ,
        QED.OneLoop.IsFormFactorPair P.e P.m p' p V F → ‖F.2 - a‖ < η := by
  intro η hη
  obtain ⟨q₀, hq₀, h⟩ := (uniform_iff_tendsto_pauliAt P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ P.e a).mpr ha η hη
  refine ⟨q₀, hq₀, fun p' p hp hp' hp0 hp0' hq hq₀' V hV F hF => ?_⟩
  rw [QED.OneLoop.eq_formFactorProj_of_isFormFactorPair he hm.ne' hp' hp hq hF]
  exact h p' p hp hp' hp0 hp0' hq hq₀' V hV

end Reduction

end QED.TwoLoop.PauliZero

end
