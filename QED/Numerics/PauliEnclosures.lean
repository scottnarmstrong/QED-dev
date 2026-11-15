/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Numerics.PauliExtension
public import QED.Numerics.Certificates.PauliTen
public import QED.Numerics.Certificates.PauliHundred
public import QED.Numerics.Certificates.PauliThousand
public import QED.OneLoop.FormFactorPair
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Certified enclosures of the one-loop Pauli coefficient (milestone NUM.CERTIFICATE)

Decision D-34 certifies the regulated one-loop Pauli coefficient at the regulator points
`m_γ = m/10ᵏ`, `Λ = m²/m_γ = 10ᵏ m` (`k = 1, 2, 3`) and `q² = m²/10⁴`. This module checks the
generated box partitions `QED.Numerics.Certificates.pauliTenPartition`, `pauliHundredPartition`,
`pauliThousandPartition` (data modules under `QED/Numerics/Certificates/`, written by
`scripts/numerics/gen_pauli_certificates.py`; see `certificates/README.md`) with the checker
`QED.Numerics.Quadrature.check` and the interval extension `QED.Numerics.Pauli.remExt`, by
`decide +kernel`, and turns the accepted checks into enclosures of the integral by
`QED.Numerics.Pauli.integral_pauliIntegrand_mem_of_check`.

## Main statements

* `QED.Numerics.Pauli.check_ten`, `check_hundred`, `check_thousand`: the kernel checks. Each
  claims `[1 - t_hi, 1 - t_lo]` for the integral of the remainder.
* `QED.Numerics.Pauli.integral_pauliIntegrand_ten`, `_hundred`, `_thousand`: for `m ≠ 0`,
  `∫ pauliIntegrand m (m/10ᵏ, 10ᵏ m, m²/10⁴)` lies in `[0.7668, 0.7673]`, `[0.9700, 0.9705]`
  and `[0.9966, 0.9971]` respectively.
* `QED.Numerics.Pauli.isFormFactorPair_vertexOneLoop_pauli_mem`: the reduction of an enclosure
  of the Pauli form factor of the one-loop vertex to an enclosure of this integral, through the
  existence and uniqueness of its form-factor pair.
-/

@[expose] public section

open MeasureTheory Set QED.Integration QED.OneLoop QED.OneLoop.VertexLimit
open QED.Numerics.Certificates

namespace QED.Numerics.Pauli

/-- The scale of the certificates: interval endpoints and cut heights are multiples of
`2⁻⁶⁴`. -/
abbrev scale : ℕ := 2 ^ 64

/-! ### The kernel checks -/

/-- The certificate at `m_γ = m/10`: `∫ remainder ∈ [0.2327, 0.2332]`. -/
theorem check_ten : Quadrature.check (S := scale)
    (remExt (Interval.ofRat (1 / 100)) (Interval.ofRat 100) (Interval.ofRat (1 / 10000)))
    pauliTenPartition (2327 / 10000) (2332 / 10000) = true := by
  decide +kernel

/-- The certificate at `m_γ = m/100`: `∫ remainder ∈ [0.0295, 0.0300]`. -/
theorem check_hundred : Quadrature.check (S := scale)
    (remExt (Interval.ofRat (1 / 10000)) (Interval.ofRat 10000) (Interval.ofRat (1 / 10000)))
    pauliHundredPartition (295 / 10000) (300 / 10000) = true := by
  decide +kernel

/-- The certificate at `m_γ = m/1000`: `∫ remainder ∈ [0.0029, 0.0034]`. -/
theorem check_thousand : Quadrature.check (S := scale)
    (remExt (Interval.ofRat (1 / 1000000)) (Interval.ofRat 1000000)
      (Interval.ofRat (1 / 10000)))
    pauliThousandPartition (29 / 10000) (34 / 10000) = true := by
  decide +kernel

/-! ### The enclosures -/

/-- `(m/n, n m, m²/10⁴) = (m (1/n), m n, m² (1/10⁴))`. -/
theorem regulator_eq (m n : ℝ) :
    ((m / n, n * m, m ^ 2 / 10000) : ℝ × ℝ × ℝ) = (m * (1 / n), m * n, m ^ 2 * (1 / 10000)) := by
  simp only [Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

/-- At `m_γ = m/10`, `Λ = 10 m`, `q² = m²/10⁴`: `∫ pauliIntegrand ∈ [0.7668, 0.7673]`. -/
theorem integral_pauliIntegrand_ten {m : ℝ} (hm : m ≠ 0) :
    ∫ z, pauliIntegrand m (m / 10, 10 * m, m ^ 2 / 10000) z ∂feynmanMeasure
      ∈ Icc (0.7668 : ℝ) 0.7673 := by
  rw [regulator_eq]
  obtain ⟨h1, h2⟩ := integral_pauliIntegrand_mem_of_check (a := 1 / 10) (b := 10)
    (c := 1 / 10000) hm (by norm_num) (by norm_num) (by norm_num)
    (Interval.mem_ofRat_of_eq (by norm_num)) (Interval.mem_ofRat_of_eq (by norm_num))
    (Interval.mem_ofRat_of_eq (by norm_num)) check_ten
  norm_num at h1 h2
  constructor <;> norm_num <;> linarith

/-- At `m_γ = m/100`, `Λ = 100 m`, `q² = m²/10⁴`: `∫ pauliIntegrand ∈ [0.9700, 0.9705]`. -/
theorem integral_pauliIntegrand_hundred {m : ℝ} (hm : m ≠ 0) :
    ∫ z, pauliIntegrand m (m / 100, 100 * m, m ^ 2 / 10000) z ∂feynmanMeasure
      ∈ Icc (0.9700 : ℝ) 0.9705 := by
  rw [regulator_eq]
  obtain ⟨h1, h2⟩ := integral_pauliIntegrand_mem_of_check (a := 1 / 100) (b := 100)
    (c := 1 / 10000) hm (by norm_num) (by norm_num) (by norm_num)
    (Interval.mem_ofRat_of_eq (by norm_num)) (Interval.mem_ofRat_of_eq (by norm_num))
    (Interval.mem_ofRat_of_eq (by norm_num)) check_hundred
  norm_num at h1 h2
  constructor <;> norm_num <;> linarith

/-- At `m_γ = m/1000`, `Λ = 1000 m`, `q² = m²/10⁴`: `∫ pauliIntegrand ∈ [0.9966, 0.9971]`. -/
theorem integral_pauliIntegrand_thousand {m : ℝ} (hm : m ≠ 0) :
    ∫ z, pauliIntegrand m (m / 1000, 1000 * m, m ^ 2 / 10000) z ∂feynmanMeasure
      ∈ Icc (0.9966 : ℝ) 0.9971 := by
  rw [regulator_eq]
  obtain ⟨h1, h2⟩ := integral_pauliIntegrand_mem_of_check (a := 1 / 1000) (b := 1000)
    (c := 1 / 10000) hm (by norm_num) (by norm_num) (by norm_num)
    (Interval.mem_ofRat_of_eq (by norm_num)) (Interval.mem_ofRat_of_eq (by norm_num))
    (Interval.mem_ofRat_of_eq (by norm_num)) check_thousand
  norm_num at h1 h2
  constructor <;> norm_num <;> linarith

/-! ### The form-factor pair -/

/-- For `e ≠ 0` and `q² > 0` the one-loop vertex has a form-factor pair, and every such pair
has Pauli component `F₂ = (e²/8π²) t` with `t = ∫ pauliIntegrand m (m_γ, Λ, q²)`; so an
enclosure of that integral encloses `F₂ / (e²/8π²)`. -/
theorem isFormFactorPair_vertexOneLoop_pauli_mem {e m mγ Λ lo hi : ℝ} (he : e ≠ 0)
    (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
    (h : ∫ z, pauliIntegrand m (mγ, Λ, Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure
      ∈ Icc lo hi) :
    (∃ F : ℂ × ℂ, IsFormFactorPair e m p' p
      (vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F) ∧
    ∀ F : ℂ × ℂ, IsFormFactorPair e m p' p
        (vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F →
      ∃ t ∈ Icc lo hi, F.2 = ((e ^ 2 / (8 * Real.pi ^ 2) * t : ℝ) : ℂ) := by
  refine ⟨⟨_, isFormFactorPair_vertexOneLoop hm hmγ hΛ hp' hp hp0' hp0⟩, fun F hF => ?_⟩
  rw [eq_of_isFormFactorPair_vertexOneLoop he hm hmγ hΛ hp' hp hp0' hp0 hq hF]
  exact ⟨_, h, by rw [formFactorB_eq hp' hp]⟩

end QED.Numerics.Pauli

end
