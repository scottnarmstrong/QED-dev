/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutCW
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G4: the outer-massive corner `b`-integral as a `(u + v)⁻²`-transform

Helper level (no frozen statement). For `m, e, w, u > 0`, `s₀ ≥ 0`, `β = w (s₀ + e)`,
`h = u/w`, `M = m - e u ≠ 0` (so `M + β h = m + s₀ u > 0`) (**`scOutC_cForm_eq`**):

`cForm(a₀, a₁, a₂, c₀, c₁, c₂, c₃, β, h, M, log(M + β h), log(1 + M/(β h)))
  = ∫₀^∞ T(v)/(u + v)² dv`,

`T = scOutCTg` of `SetCKScOutCW`. Proof: on `S = {v > 0 : s₀ v < m}` the map
`z ↦ v = u m/(z - e u)` from `(z₀, ∞)`, `z₀ = β h = (s₀ + e) u`, onto `S` (`scOutC_cv`) turns
`k/(u + v)` and `κ/(u + v)²` into the `b`-integrands of `cForm` written in `z = b h`
(`scOutC_k_cv`, `scOutC_kap_cv`), whose integrals are the masters of `SetCKScOutCMast`; beyond
the threshold (`s₀ > 0`, `v ≥ m/s₀`) `k = -c₀ w/v` gives `-c₀ w log(1 + s₀ u/m)/u`, which with
the pole `P/u` is the large-`b` logarithm `-c₀ A/h`; finally `∫ K/(u + v)² = ∫ k/(u + v)`
(`scOutC_ibp`). Checked numerically (scratch `stageK/g4c/tK.py`, including `M < 0` and the
second branch of `betaG`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

section

variable {m e w s u : ℝ}

/-- The threshold set `S = {v > 0 : s v < m}`. -/
def scOutCS (m s : ℝ) : Set ℝ := {v | 0 < v ∧ s * v < m}

theorem measurableSet_scOutCS (m s : ℝ) : MeasurableSet (scOutCS m s) :=
  measurableSet_Ioi.inter (measurableSet_lt (measurable_const.mul measurable_id) measurable_const)

/-- The node map `z ↦ u m/(z - e u)`. -/
noncomputable def scOutCPhi (m e u z : ℝ) : ℝ := u * m / (z - e * u)

theorem scOutCPhi_image (hm : 0 < m) (hu : 0 < u) (hs : 0 ≤ s) :
    scOutCPhi m e u '' Ioi ((s + e) * u) = scOutCS m s := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : s * u < z - e * u := by rw [mem_Ioi] at hz; linarith
    have hpos : 0 < z - e * u := lt_of_le_of_lt (by positivity) hz'
    refine ⟨by unfold scOutCPhi; positivity, ?_⟩
    unfold scOutCPhi
    rw [mul_div_assoc', div_lt_iff₀ hpos]
    nlinarith [mul_lt_mul_of_pos_left hz' (mul_pos hu hm)]
  · rintro ⟨hv, hsv⟩
    refine ⟨e * u + u * m / v, ?_, ?_⟩
    · rw [mem_Ioi]
      have : s * u < u * m / v := by
        rw [lt_div_iff₀ hv]
        nlinarith
      linarith
    · unfold scOutCPhi
      have : e * u + u * m / v - e * u = u * m / v := by ring
      rw [this]
      field_simp

/-- **The node change of variables** onto the threshold set. -/
theorem scOutC_cv (hm : 0 < m) (hu : 0 < u) (hs : 0 ≤ s) (f : ℝ → ℝ) :
    (IntegrableOn f (scOutCS m s) ↔ IntegrableOn
      (fun z => u * m / (z - e * u) ^ 2 * f (scOutCPhi m e u z)) (Ioi ((s + e) * u))) ∧
      ∫ v in scOutCS m s, f v =
        ∫ z in Ioi ((s + e) * u), u * m / (z - e * u) ^ 2 * f (scOutCPhi m e u z) := by
  have hpos : ∀ z ∈ Ioi ((s + e) * u), 0 < z - e * u := fun z hz => by
    rw [mem_Ioi] at hz; nlinarith
  have hd : ∀ z ∈ Ioi ((s + e) * u), HasDerivWithinAt (scOutCPhi m e u)
      (-(u * m / (z - e * u) ^ 2)) (Ioi ((s + e) * u)) z := fun z hz => by
    have h0 := hpos z hz
    have := ((hasDerivAt_id z).sub_const (e * u)).inv h0.ne'
    have h2 := this.const_mul (u * m)
    refine (h2.congr_deriv ?_).hasDerivWithinAt.congr (fun y _ => ?_) ?_
    · simp only [id]; field_simp
    · simp [scOutCPhi, div_eq_mul_inv]
    · simp [scOutCPhi, div_eq_mul_inv]
  have hinj : InjOn (scOutCPhi m e u) (Ioi ((s + e) * u)) := fun a ha b hb hab => by
    have h1 := hpos a ha
    have h2 := hpos b hb
    unfold scOutCPhi at hab
    rw [div_eq_div_iff h1.ne' h2.ne'] at hab
    have : u * m ≠ 0 := by positivity
    have := mul_left_cancel₀ this hab
    linarith
  have habs : ∀ z ∈ Ioi ((s + e) * u), |-(u * m / (z - e * u) ^ 2)| = u * m / (z - e * u) ^ 2 :=
    fun z hz => by rw [abs_neg, abs_of_pos (by have := hpos z hz; positivity)]
  have hI := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd hinj f
  have hE := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj f
  rw [scOutCPhi_image hm hu hs] at hI hE
  refine ⟨hI.trans ⟨fun h => ?_, fun h => ?_⟩, hE.trans ?_⟩
  · refine h.congr_fun (fun z hz => ?_) measurableSet_Ioi
    simp only [smul_eq_mul, habs z hz]
  · refine h.congr_fun (fun z hz => ?_) measurableSet_Ioi
    simp only [smul_eq_mul, habs z hz]
  · refine setIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
    simp only [smul_eq_mul, habs z hz]

/-- The `k`-integrand in the variable `z = b h`. -/
theorem scOutC_k_cv (hm : 0 < m) (he : 0 < e) (hw : 0 < w) (hu : 0 < u) (hs : 0 ≤ s)
    (c₀ c₁ c₂ c₃ : ℝ) {z : ℝ} (hz : z ∈ Ioi ((s + e) * u)) :
    u * m / (z - e * u) ^ 2 * (scOutCk c₀ c₁ c₂ c₃ m e w s (scOutCPhi m e u z) /
      (u + scOutCPhi m e u z)) =
      c₁ * (1 / (z * (m - e * u + z))) + c₂ * (u / w) * (1 / (z ^ 2 * (m - e * u + z))) +
        c₃ * (u / w) ^ 2 * (1 / (z ^ 3 * (m - e * u + z))) := by
  have hmem : scOutCPhi m e u z ∈ scOutCS m s := by
    rw [← scOutCPhi_image hm hu hs]; exact ⟨z, hz, rfl⟩
  unfold scOutCk
  simp only [hmem.2, ↓reduceIte]
  obtain ⟨D, rfl⟩ : ∃ D, z = D + e * u := ⟨z - e * u, by ring⟩
  have hz' : (s + e) * u < D + e * u := hz
  have hsu : 0 ≤ s * u := mul_nonneg hs hu.le
  have hD : 0 < D := by nlinarith
  have hDe : 0 < D + e * u := by nlinarith [mul_pos he hu]
  have e1 : D + e * u - e * u = D := by ring
  have e2 : m - e * u + (D + e * u) = m + D := by ring
  unfold scOutCPhi
  rw [e1, e2]
  have em : m + e * (u * m / D) = m * (D + e * u) / D := by field_simp
  have eu : u + u * m / D = u * (m + D) / D := by field_simp; ring
  rw [em, eu]
  have := hDe.ne'
  have : m + D ≠ 0 := by positivity
  have := hm.ne'
  have := hw.ne'
  have := hu.ne'
  field_simp

/-- The `κ`-integrand in the variable `z = b h`. -/
theorem scOutC_kap_cv (hm : 0 < m) (he : 0 < e) (hw : 0 < w) (hu : 0 < u) (hs : 0 ≤ s)
    (a₀ a₁ a₂ : ℝ) {z : ℝ} (hz : z ∈ Ioi ((s + e) * u)) :
    u * m / (z - e * u) ^ 2 * (scOutCkap a₀ a₁ a₂ m e w s (scOutCPhi m e u z) /
      (u + scOutCPhi m e u z) ^ 2) =
      a₀ * (w / u) * (1 / (m - e * u + z) ^ 2) + a₁ * (1 / (z * (m - e * u + z) ^ 2)) +
        a₂ * (u / w) * (1 / (z ^ 2 * (m - e * u + z) ^ 2)) := by
  have hmem : scOutCPhi m e u z ∈ scOutCS m s := by
    rw [← scOutCPhi_image hm hu hs]; exact ⟨z, hz, rfl⟩
  unfold scOutCkap
  simp only [hmem.2, ↓reduceIte]
  obtain ⟨D, rfl⟩ : ∃ D, z = D + e * u := ⟨z - e * u, by ring⟩
  have hz' : (s + e) * u < D + e * u := hz
  have hsu : 0 ≤ s * u := mul_nonneg hs hu.le
  have hD : 0 < D := by nlinarith
  have hDe : 0 < D + e * u := by nlinarith [mul_pos he hu]
  have e1 : D + e * u - e * u = D := by ring
  have e2 : m - e * u + (D + e * u) = m + D := by ring
  unfold scOutCPhi
  rw [e1, e2]
  have em : m + e * (u * m / D) = m * (D + e * u) / D := by field_simp
  have eu : u + u * m / D = u * (m + D) / D := by field_simp; ring
  have er : u * m / D / (w * (m * (D + e * u) / D)) = u / (w * (D + e * u)) := by
    field_simp
  rw [em, eu, er]
  have := hDe.ne'
  have : m + D ≠ 0 := by positivity
  have := hm.ne'
  have := hw.ne'
  have := hu.ne'
  field_simp

end

end QED.ChainProof.SetCK

end
