/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroLimitCt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The `δ₃` class at fixed `ε`: Pauli projection and partial fractions

Part of the nested-form identity of the VP unit (`QED.TwoLoop.UnitVPLink.VPUnitNested`, obligations
O2-13 and O2-14 for the `δ₃` insertion, `docs/TWO-LOOP-DERIVATION.md`, section 5.1). Pure algebra,
pointwise in the loop momentum `k` and at fixed `ε`.

* `photonNum_eq`: the photon numerator of the `δ₃` insertion is
  `-(δ₃/2)(Λ² - m_γ²)² (k² g_{νρ} - k_ν k_ρ)`.
* `pauliNum_longitudinal`: **the longitudinal part drops out of the Pauli projection**, exactly
  (no `O(ε)` defect): on shell, `(m - p̸') k̸ (m - p̸' - k̸) = ((p'+k)² + m²)(m - p̸')` and
  `(m - p̸ - k̸) k̸ (m - p̸) = ((p+k)² + m²)(m - p̸)`, so the sandwiched longitudinal chain is a
  multiple of `(m - p̸') γ^μ (m - p̸)`, which has no Pauli part.
* `pauliNum_numD3`: the Pauli projection of the `δ₃` numerator is
  `-(δ₃/2)(Λ² - m_γ²)² k² Pg(k)`, with `Pg` the Pauli projection of the Feynman-gauge chain
  (`pauliChain`).
* `pauliNum_vertexIntegrand`: the Pauli projection of the frozen one-loop integrand with photon
  masses `(a, x)` is `(x² - a²) Pg(k) / (D_{p'+k} D_{p+k} D_a D_x)`.
* `pf_four`: the partial fractions of `k²/(D_a D_b D_c D_d)` into Pauli–Villars pairs `(a, x)`,
  with the exact `iε` coefficients.
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.TwoLoop.VPUnitNested

open QED.Dirac QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit
open QED.TwoLoop.PauliZeroLimit

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### The Feynman-gauge chain and its Pauli projection -/

/-- The Feynman-gauge photon factor `g_{νρ}`. -/
noncomputable def gPhoton (ν ρ : Fin 4) : ℂ := ((Minkowski.metric ν ρ : ℝ) : ℂ)

/-- **The Pauli projection of the Feynman-gauge chain** `Pg(k)`: the Pauli numerator of
`vertexChain e μ (m - p̸' - k̸) (m - p̸ - k̸) g`. -/
noncomputable def pauliChain (e m : ℝ) (p' p k : Fin 4 → ℝ) : ℂ :=
  pauliNum m p' p fun μ =>
    vertexChain e μ (electronNumerator m (p' + k)) (electronNumerator m (p + k)) gPhoton

theorem pauliNum_add (m : ℝ) (p' p : Fin 4 → ℝ) (V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    pauliNum m p' p (fun μ => V μ + W μ) = pauliNum m p' p V + pauliNum m p' p W := by
  simp only [pauliNum_eq_sum, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

/-! ### The photon numerator of the `δ₃` insertion -/

theorem photonNum_eq (δ₃ mγ Λ : ℝ) (k : Fin 4 → ℝ) :
    photonNum δ₃ mγ Λ k = fun ν ρ =>
      (-(δ₃ / 2) * (Λ ^ 2 - mγ ^ 2) ^ 2 : ℂ) * (((Minkowski.dot k k : ℝ) : ℂ) * gPhoton ν ρ) +
        ((δ₃ / 2) * (Λ ^ 2 - mγ ^ 2) ^ 2 : ℂ) *
          (((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) := by
  funext ν ρ
  simp only [photonNum, pvPhotonNum, photonCtFactor, gPhoton, Minkowski.lower, Fin.sum_univ_four,
    Minkowski.metric]
  fin_cases ν <;> fin_cases ρ <;> simp <;> field_simp <;> ring_nf <;> simp only [I_sq] <;> ring

/-! ### The longitudinal part -/

theorem slash_eq_lower_sum (k : Fin 4 → ℝ) :
    slash k = ∑ ν, ((Minkowski.lower k ν : ℝ) : ℂ) • gamma ν := rfl

/-- The longitudinal chain is `κ k̸ A γ^μ B k̸`. -/
theorem vertexChain_longitudinal (e : ℝ) (μ : Fin 4) (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (k : Fin 4 → ℝ) :
    vertexChain e μ A B
        (fun ν ρ => ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) =
      ((I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) •
        (slash k * A * gamma μ * B * slash k) := by
  unfold vertexChain
  congr 1
  simp only [slash_eq_lower_sum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    smul_smul, Finset.smul_sum]

/-- `(m - p̸) (p̸ + m) = 0` on shell. -/
theorem mass_sub_slash_mul_slash_add {m : ℝ} {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2) :
    electronNumerator m p * (slash p + (m : ℂ) • 𝟙) = 0 := by
  simp only [electronNumerator, Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, slash_mul_slash, hp]
  push_cast
  module

/-- `(p̸ + m)(m - p̸) = 0` on shell. -/
theorem slash_add_mul_mass_sub_slash {m : ℝ} {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2) :
    (slash p + (m : ℂ) • 𝟙) * electronNumerator m p = 0 := by
  simp only [electronNumerator, Matrix.mul_sub, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, slash_mul_slash, hp]
  push_cast
  module

/-- `(q̸ + m)(m - q̸) = (q² + m²)`. -/
theorem slash_add_mul_electronNumerator (m : ℝ) (q : Fin 4 → ℝ) :
    (slash q + (m : ℂ) • 𝟙) * electronNumerator m q =
      ((Minkowski.dot q q + m ^ 2 : ℝ) : ℂ) • 𝟙 := by
  simp only [electronNumerator, Matrix.mul_sub, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, slash_mul_slash]
  push_cast
  module

/-- `(m - q̸)(q̸ + m) = (q² + m²)`. -/
theorem electronNumerator_mul_slash_add (m : ℝ) (q : Fin 4 → ℝ) :
    electronNumerator m q * (slash q + (m : ℂ) • 𝟙) =
      ((Minkowski.dot q q + m ^ 2 : ℝ) : ℂ) • 𝟙 := by
  simp only [electronNumerator, Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, slash_mul_slash]
  push_cast
  module

/-- **The line-by-line Ward identity on the outgoing side**:
`(m - p̸') k̸ (m - p̸' - k̸) = ((p'+k)² + m²)(m - p̸')` for on-shell `p'`. -/
theorem ward_out {m : ℝ} {p' : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (k : Fin 4 → ℝ) :
    electronNumerator m p' * slash k * electronNumerator m (p' + k) =
      ((Minkowski.dot (p' + k) (p' + k) + m ^ 2 : ℝ) : ℂ) • electronNumerator m p' := by
  have hk : slash k = (slash (p' + k) + (m : ℂ) • 𝟙) - (slash p' + (m : ℂ) • 𝟙) := by
    rw [slash_add]; abel
  rw [hk, Matrix.mul_sub, Matrix.sub_mul, mass_sub_slash_mul_slash_add hp', Matrix.zero_mul,
    sub_zero, Matrix.mul_assoc, slash_add_mul_electronNumerator, Matrix.mul_smul, Matrix.mul_one]

/-- **The line-by-line Ward identity on the incoming side**:
`(m - p̸ - k̸) k̸ (m - p̸) = ((p+k)² + m²)(m - p̸)` for on-shell `p`. -/
theorem ward_in {m : ℝ} {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2) (k : Fin 4 → ℝ) :
    electronNumerator m (p + k) * slash k * electronNumerator m p =
      ((Minkowski.dot (p + k) (p + k) + m ^ 2 : ℝ) : ℂ) • electronNumerator m p := by
  have hk : slash k = (slash (p + k) + (m : ℂ) • 𝟙) - (slash p + (m : ℂ) • 𝟙) := by
    rw [slash_add]; abel
  rw [hk, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc _ (slash p + (m : ℂ) • 𝟙),
    slash_add_mul_mass_sub_slash hp, Matrix.mul_zero, sub_zero, electronNumerator_mul_slash_add,
    Matrix.smul_mul, Matrix.one_mul]

/-- The sandwiched longitudinal chain is a multiple of the sandwiched `γ^μ`. -/
theorem sandwich_longitudinal (e : ℝ) {m : ℝ} {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (k : Fin 4 → ℝ)
    (μ : Fin 4) :
    electronNumerator m p' *
        vertexChain e μ (electronNumerator m (p' + k)) (electronNumerator m (p + k))
          (fun ν ρ => ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) *
        electronNumerator m p =
      (((I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) *
          ((Minkowski.dot (p' + k) (p' + k) + m ^ 2 : ℝ) : ℂ) *
          ((Minkowski.dot (p + k) (p + k) + m ^ 2 : ℝ) : ℂ)) •
        (electronNumerator m p' * gamma μ * electronNumerator m p) := by
  rw [vertexChain_longitudinal, Matrix.mul_smul, Matrix.smul_mul]
  have e1 : electronNumerator m p' *
      (slash k * electronNumerator m (p' + k) * gamma μ * electronNumerator m (p + k) * slash k) *
        electronNumerator m p =
      (electronNumerator m p' * slash k * electronNumerator m (p' + k)) * gamma μ *
        (electronNumerator m (p + k) * slash k * electronNumerator m p) := by
    simp only [Matrix.mul_assoc]
  rw [e1, ward_out hp', ward_in hp, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    smul_smul]

/-- **The longitudinal part has no Pauli component** (O2-14 for the `δ₃` insertion), exactly at
every loop momentum, for on-shell `p, p'` with `q² > 0`. -/
theorem pauliNum_longitudinal (e : ℝ) {m : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (k : Fin 4 → ℝ) :
    pauliNum m p' p (fun μ =>
      vertexChain e μ (electronNumerator m (p' + k)) (electronNumerator m (p + k))
        (fun ν ρ => ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ))) = 0 := by
  set c : ℂ := ((I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) *
    ((Minkowski.dot (p' + k) (p' + k) + m ^ 2 : ℝ) : ℂ) *
    ((Minkowski.dot (p + k) (p + k) + m ^ 2 : ℝ) : ℂ)
  have h := QED.OneLoop.formFactorProj_eq_of_mul_mul_eq (e := 1) one_ne_zero hp' hp hq
    (V := fun μ => vertexChain e μ (electronNumerator m (p' + k)) (electronNumerator m (p + k))
      (fun ν ρ => ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)))
    (α := c) (β := 0) (c := 0) (fun μ => by
      refine (sandwich_longitudinal e hp' hp k μ).trans ?_
      simp only [zero_mul, add_zero, zero_smul, Matrix.mul_smul, Matrix.smul_mul]
      rfl)
  have h2 := h.2.1
  rw [formFactorProj₂_eq_pauliNum] at h2
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hq' : (Minkowski.dot (p' - p) (p' - p) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hD : 4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 4 * m ^ 2 + Minkowski.dot (p' - p) (p' - p) := by positivity
    exact_mod_cast this.ne'
  simp only [mul_zero, neg_zero, zero_div, ofReal_one, one_mul] at h2
  rcases (div_eq_zero_iff.mp h2) with h3 | h3
  · exact (mul_eq_zero.mp h3).resolve_left hm'
  · exact absurd h3 (mul_ne_zero hq' (pow_ne_zero 2 hD))

/-! ### The Pauli projection of the `δ₃` numerator -/

/-- **The Pauli projection of the `δ₃` numerator**: `-(δ₃/2)(Λ² - m_γ²)² k² Pg(k)`. -/
theorem pauliNum_numD3 (P : Params) (hm : P.m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (k : Fin 4 → ℝ) :
    pauliNum P.m p' p (fun μ => numD3 P p' p μ k) =
      (-(P.δ₃ / 2) * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℂ) * ((Minkowski.dot k k : ℝ) : ℂ) *
        pauliChain P.e P.m p' p k := by
  simp only [numD3, photonNum_eq]
  simp only [vertexChain_add_photon, vertexChain_smul_photon, pauliNum_add, pauliNum_smul,
    pauliNum_longitudinal P.e hm hp' hp hq k, mul_zero, add_zero, pauliChain]
  ring

/-! ### The Pauli projection of the frozen one-loop integrand -/

theorem pvPhotonNum_eq (mγ Λ : ℝ) :
    pvPhotonNum mγ Λ = fun ν ρ => ((Λ ^ 2 - mγ ^ 2 : ℝ) : ℂ) * gPhoton ν ρ := by
  funext ν ρ
  simp only [pvPhotonNum, gPhoton]
  push_cast
  ring

/-- **The Pauli projection of the frozen one-loop integrand** with photon masses `(a, x)`:
`(x² - a²) Pg(k) / (D_{p'+k} D_{p+k} D_a D_x)`, for `ε ≠ 0`. -/
theorem pauliNum_vertexIntegrand (e m a x : ℝ) {ε : ℝ} (hε : ε ≠ 0) (p' p k : Fin 4 → ℝ) :
    pauliNum m p' p (fun μ => QED.OneLoop.vertexIntegrand e m a x ε p' p μ k) =
      ((x ^ 2 - a ^ 2 : ℝ) : ℂ) *
        ((propDenom m ε (p' + k))⁻¹ * (propDenom m ε (p + k))⁻¹ *
          ((propDenom a ε k)⁻¹ * (propDenom x ε k)⁻¹)) * pauliChain e m p' p k := by
  have h : (fun μ => QED.OneLoop.vertexIntegrand e m a x ε p' p μ k) = fun μ =>
      (((propDenom m ε (p' + k))⁻¹ * (propDenom m ε (p + k))⁻¹ *
          ((propDenom a ε k)⁻¹ * (propDenom x ε k)⁻¹)) * ((x ^ 2 - a ^ 2 : ℝ) : ℂ)) •
        vertexChain e μ (electronNumerator m (p' + k)) (electronNumerator m (p + k)) gPhoton := by
    funext μ
    rw [vertexIntegrand_eq_vertexChain, photonPropagator_eq_scalar _ _ hε, pvPhotonNum_eq,
      CountertermLimit.electronPropagator_eq_smul, CountertermLimit.electronPropagator_eq_smul,
      vertexChain_smul_out,
      vertexChain_smul_in]
    have e2 : (fun ν ρ => (propDenom a ε k)⁻¹ * (propDenom x ε k)⁻¹ *
        (((x ^ 2 - a ^ 2 : ℝ) : ℂ) * gPhoton ν ρ)) = fun ν ρ =>
          ((propDenom a ε k)⁻¹ * (propDenom x ε k)⁻¹ * ((x ^ 2 - a ^ 2 : ℝ) : ℂ)) *
            gPhoton ν ρ := by
      funext ν ρ; ring
    rw [e2, vertexChain_smul_photon, smul_smul, smul_smul]
    congr 1
    ring
  rw [h, pauliNum_smul, pauliChain]
  ring

/-! ### Partial fractions -/

/-- **Partial fractions of `k²/(D_a D_b D_c D_d)` into Pauli–Villars pairs.** With
`D_y = w + t_y`, `k² = w + e` and distinct `t`'s,
`k² ∏_y D_y⁻¹ = ∑_{x ∈ {b, c, d}} c_x (t_x - e) (t_x - t_a)/(D_a D_x)`,
`c_x = 1/∏_{y ≠ x} (t_y - t_x)`. -/
theorem pf_four {w e ta tb tc td : ℂ} (ha : w + ta ≠ 0) (hb : w + tb ≠ 0) (hc : w + tc ≠ 0)
    (hd : w + td ≠ 0) (hab : ta ≠ tb) (hac : ta ≠ tc) (had : ta ≠ td) (hbc : tb ≠ tc)
    (hbd : tb ≠ td) (hcd : tc ≠ td) :
    (w + e) * ((w + ta)⁻¹ * (w + tb)⁻¹ * (w + tc)⁻¹ * (w + td)⁻¹) =
      ((ta - tb) * (tc - tb) * (td - tb))⁻¹ * (tb - e) *
          ((tb - ta) * ((w + ta)⁻¹ * (w + tb)⁻¹)) +
        ((ta - tc) * (tb - tc) * (td - tc))⁻¹ * (tc - e) *
          ((tc - ta) * ((w + ta)⁻¹ * (w + tc)⁻¹)) +
        ((ta - td) * (tb - td) * (tc - td))⁻¹ * (td - e) *
          ((td - ta) * ((w + ta)⁻¹ * (w + td)⁻¹)) := by
  have h1 : ta - tb ≠ 0 := sub_ne_zero.2 hab
  have h2 : ta - tc ≠ 0 := sub_ne_zero.2 hac
  have h3 : ta - td ≠ 0 := sub_ne_zero.2 had
  have h4 : tb - tc ≠ 0 := sub_ne_zero.2 hbc
  have h5 : tb - td ≠ 0 := sub_ne_zero.2 hbd
  have h6 : tc - td ≠ 0 := sub_ne_zero.2 hcd
  have h4' : tc - tb ≠ 0 := sub_ne_zero.2 (Ne.symm hbc)
  have h5' : td - tb ≠ 0 := sub_ne_zero.2 (Ne.symm hbd)
  have h6' : td - tc ≠ 0 := sub_ne_zero.2 (Ne.symm hcd)
  field_simp
  ring

end QED.TwoLoop.VPUnitNested

end
