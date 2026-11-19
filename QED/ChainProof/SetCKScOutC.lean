/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutCId
public import QED.ChainProof.SetCKScOut
public import QED.ChainProof.SetCKCornIn

/-!
# Set (c), Stage K, group G4: the outer-massive corner unit

Helper level (no frozen statement). The two-loop part of the corner with the photon of mass²
`t > 0` outside the subdivergent subgraph and the inner photon massless is (no counterterm; the
corner counterterm is in `scOutS`)

`C(0, t) = 2 ∫₀¹ dY ∫₀^Y dy₃ ∫₀¹ dx cornerGm (√t) 0 y₃ (Y - y₃) x` (`scOutC`).

Numerically `scOutC 1 = 0.127357972370851755` and `scOutC 4 = 0.0346211391666207856`
(tanh–sinh, scratch `stageK/g4c/chkC2.py`, `chkC4.py`), against the set (c) plan values
`0.1273579723764830851` (level 12) and `0.034621139168420099969` (level 8) of the C(0, t)
two-loop part.

**The `(u + v)⁻²`-form per point** (**`scOutC_cornerGm_eq`**): with `u = Q(x) + t`,
`e = y₃ y₄`, `m = Y² + e Q(x)`, `ρ = x/(1-x)`, `s₀ = β/ρ - e ≥ 0` (`β = betaG`), and
`M = Y² - t e ≠ 0`, `cornerGm (√t) 0 y₃ y₄ x = ∫₀^∞ T(Y, y₃, x, v)/(u + v)² dv` with the
`t`-independent weight `T = scOutCTg` of `SetCKScOutCW` at these parameters (`scOutCT`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The outer-massive corner unit** `C(0, t)` (two-loop part). -/
noncomputable def scOutC (t : ℝ) : ℝ :=
  2 * ∫ Y in (0 : ℝ)..1, ∫ y3 in (0 : ℝ)..Y, ∫ x in (0 : ℝ)..1, cornerGm (√t) 0 y3 (Y - y3) x

/-- **The `Q`-derivative form of the Stieltjes identity for G4C.** -/
def IsScOutCHDensity (H : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → scOutC t = ∫ X in (0 : ℝ)..1, H X * (setCKdQ X / (setCKQ X + t) ^ 2)

/-- `m = Y² + e Q(x)`, `e = y₃ (Y - y₃)`. -/
noncomputable def scOutCm (Y y3 x : ℝ) : ℝ := Y ^ 2 + y3 * (Y - y3) * setCKQ x

/-- `s₀ = β/ρ - e`. -/
noncomputable def scOutCs (Y y3 x : ℝ) : ℝ :=
  betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x / scOutRho x - y3 * (Y - y3)

/-- **The `(u + v)⁻²`-weight of the outer-massive corner** at `(Y, y₃, x)`. -/
noncomputable def scOutCT (Y y3 x v : ℝ) : ℝ :=
  scOutCTg (cornerA0 x y3 (Y - y3)) (cornerA1 x y3 (Y - y3)) (cornerA2 x y3 (Y - y3))
    (cornerC0 x) (cornerC1 x y3 (Y - y3)) (cornerC2 x y3 (Y - y3)) (cornerC3 x y3 (Y - y3))
    (scOutCm Y y3 x) (y3 * (Y - y3)) (scOutRho x) (scOutCs Y y3 x) v

section

variable {t Y y3 x : ℝ}

theorem scOutCm_pos (hY : Y ∈ Ioo (0 : ℝ) 1) (h3 : y3 ∈ Ioo (0 : ℝ) Y)
    (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < scOutCm Y y3 x := by
  have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have : 0 < Y - y3 := by linarith [h3.2]
  have := h3.1
  have := hY.1
  unfold scOutCm
  positivity

theorem scOutCs_nonneg (hx : x ∈ Ioo (0 : ℝ) 1) : 0 ≤ scOutCs Y y3 x := by
  have hρ := scOutRho_pos hx
  have hb : y3 * (Y - y3) * x / (1 - x) ≤ betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x :=
    le_max_right _ _
  unfold scOutCs
  rw [sub_nonneg, le_div_iff₀ hρ]
  unfold scOutRho at hb ⊢
  calc y3 * (Y - y3) * (x / (1 - x)) = y3 * (Y - y3) * x / (1 - x) := by ring
    _ ≤ _ := hb

/-- **The `(u + v)⁻²`-representation of the outer-massive corner integrand** (`M ≠ 0`). -/
theorem scOutC_cornerGm_eq (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) (h3 : y3 ∈ Ioo (0 : ℝ) Y)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hM : Y ^ 2 - t * (y3 * (Y - y3)) ≠ 0) :
    cornerGm (√t) 0 y3 (Y - y3) x =
      ∫ v in Ioi 0, scOutCT Y y3 x v / (setCKQ x + t + v) ^ 2 := by
  have hρ := scOutRho_pos hx
  have he : 0 < y3 * (Y - y3) := mul_pos h3.1 (by linarith [h3.2])
  have hu : 0 < setCKQ x + t := by
    have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
    linarith
  have hβ : betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x =
      scOutRho x * (scOutCs Y y3 x + y3 * (Y - y3)) := by
    unfold scOutCs
    field_simp
    ring
  have hh : ladderInnerMass 1 (√t) x / x = (setCKQ x + t) / scOutRho x :=
    hOut_eq_div_scOutRho ht.le hx
  have hMm : cornerMass (√t) 0 y3 (Y - y3) =
      scOutCm Y y3 x - y3 * (Y - y3) * (setCKQ x + t) := by
    unfold cornerMass scOutCm
    rw [sq_sqrt ht.le]
    ring
  have hM' : scOutCm Y y3 x - y3 * (Y - y3) * (setCKQ x + t) ≠ 0 := by
    unfold scOutCm
    convert hM using 1
    ring
  unfold cornerGm
  rw [hβ, hh, hMm]
  exact scOutC_cForm_eq (scOutCm_pos hY h3 hx) he hρ hu (scOutCs_nonneg hx) hM' _ _ _ _
    _ _ _

end

end QED.ChainProof.SetCK

end
