/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValThreeHxPrim
public import QED.ThreeLoopD.SetDMastersI15KValThreeAs
public import QED.ThreeLoopD.SetDMastersI15KValThreeK
import QED.Polylog.HPLLowWeight
import QED.Polylog.HPLLyndon3
import QED.Polylog.HPLShuffle
import QED.Polylog.DilogPM
import QED.Polylog.Landen
import QED.Polylog.Reflection
import QED.Polylog.LiN

/-!
# Set (d), master `I₁₅`: the `x`-slices of `A₂₃,₃` are `h₃`

The primitive of `QED.ThreeLoopD.SetDMastersI15KValThreeHxPrim` gives
`∫₀¹ A₂₃,₃(x, u) dx = Φ(1⁻) - Φ(0⁺)`, a combination of `Li₃` and `Li₂` at `u`, `1 - u`,
`u/(1 + u)`, `1/(1 + u)`, `u²` and `1 - u²`. Rewriting these by reflection, duplication,
`Li₂ (u/(1 + u))`, `Li₂ (1/(1 + u))` and Landen's identity for `Li₃`, and the harmonic
polylogarithms of `h₃ = QED.ThreeLoopD.i15H3` by their closed forms, both sides become the same
polynomial in `Li₃ (±u)`, `Li₃ (1 - u)`, `Li₃ (1/(1 + u))`, `Li₃ (1 - u²)`, `Li₂ (±u)`,
logarithms, `π²` and `ζ(3)`. The only words of `h₃` mixing the letters `1` and `-1` enter as
`H(1, -1, 0) + H(-1, 1, 0)`, which is classical (`QED.ThreeLoopD.i15Hx_mixed`): by the shuffle
relations it is `-log u log (1 - u) log (1 + u) - log (1 + u) Li₂ u - H(1, 0, -1)`, and
`2 H(1, 0, -1) - H(1, -1, 0) - H(-1, 1, 0)` is classical (`QED.ThreeLoopD.i15K_mixed`).

This proves the inner identity of `QED.ThreeLoopD.integral_i15F_three_of_inner`, hence the
value of `∫∫ F₃`.

## Main results

* `QED.ThreeLoopD.i15Hx_mixed`: `H(1, -1, 0) + H(-1, 1, 0)` in classical polylogarithms.
* `QED.ThreeLoopD.i15HxPhi_sub_eq`: `Φ(1⁻) - Φ(0⁺) = h₃(u)`.
* `QED.ThreeLoopD.integral_i15A23k_three_inner`: `∫₀¹ A₂₃,₃(x, u) dx = h₃(u)`.
* `QED.ThreeLoopD.integral_i15F_three`:
  `∫∫ F₃ = -16 π² log 2 + 107 π²/8 + 61 ζ(3) - 1665/16`.
* `QED.ThreeLoopD.hasTruncLaurent_i15K_of_F4`: the expansion of `K` given `∫∫ F₄`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- **`H(1, -1, 0) + H(-1, 1, 0)` is classical.** -/
theorem i15Hx_mixed {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, negOne, zero] x + hpl [negOne, one, zero] x =
      -(2 / 3) * log x * log (1 - x) * log (1 + x) - 2 / 3 * log (1 + x) * Li₂ x -
        i15KR x / 3 := by
  have ha := hpl_one_negOne_zero hx
  have hb := hpl_negOne_one_zero hx
  have hd := hpl_negOne_zero_one hx
  have hK := i15K_mixed hx
  have he := hpl_mul_hpl [one] [negOne] hx
  simp [shuffle, shuffleAux, hpl_one hx, hpl_negOne hx] at he
  have he' : log x * (hpl [one, negOne] x + hpl [negOne, one] x) =
      -(log x * log (1 - x) * log (1 + x)) := by
    rw [← he]; ring
  rw [Li_two] at hd
  linear_combination (2 / 3) * ha + (2 / 3) * hb - (2 / 3) * hd - (1 / 3) * hK + (2 / 3) * he'

/-- **`Φ(1⁻) - Φ(0⁺) = h₃(u)`.** -/
theorem i15HxPhi_sub_eq {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    i15HxPhi1 u - i15HxPhi0 u = i15H3 u := by
  obtain ⟨h0, h1⟩ := hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  have hp : 0 < 1 + u := by linarith
  have hm : 0 < 1 - u := by linarith
  -- logarithms of the arguments
  have l1 : log (u / (1 + u)) = log u - log (1 + u) := log_div h0.ne' hp.ne'
  have l2 : log (1 / (1 + u)) = -log (1 + u) := by rw [one_div, log_inv]
  have l3 : log (u ^ 2) = 2 * log u := by rw [log_pow]; push_cast; ring
  have l4 : log ((1 - u) * (1 + u)) = log (1 - u) + log (1 + u) := log_mul hm.ne' hp.ne'
  -- dilogarithms
  have d1 : Li₂ (1 - u) = π ^ 2 / 6 - log u * log (1 - u) - Li₂ u := by
    have := Li₂_add_Li₂_one_sub h0.le h1.le; linarith
  have d2 : Li₂ (u / (1 + u)) = -Li₂ (-u) - log (1 + u) ^ 2 / 2 := Li_two_div_one_add hu'
  have d3 : Li₂ (1 / (1 + u)) =
      π ^ 2 / 6 + log u * log (1 + u) - log (1 + u) ^ 2 / 2 + Li₂ (-u) := Li_two_inv_one_add hu'
  have d4 : Li₂ (u ^ 2) = 2 * Li₂ u + 2 * Li₂ (-u) := by
    have := Li₂_add_Li₂_neg (x := u) (by rw [abs_of_pos h0]; exact h1.le); linarith
  have d5 : Li₂ ((1 - u) * (1 + u)) = π ^ 2 / 6 - 2 * log u * (log (1 - u) + log (1 + u)) -
      (2 * Li₂ u + 2 * Li₂ (-u)) := by
    have := Li₂_add_Li₂_one_sub (x := u ^ 2) (by positivity) (by nlinarith)
    rw [show (1 : ℝ) - u ^ 2 = (1 - u) * (1 + u) by ring, l3, l4, d4] at this
    linarith
  -- trilogarithms
  have t1 : Li₃ (u ^ 2) = 4 * Li₃ u + 4 * Li₃ (-u) := by
    have := Li₃_add_Li₃_neg (x := u) (by rw [abs_of_pos h0]; exact h1.le); linarith
  have t2 : Li₃ (u / (1 + u)) = zeta3 - log (1 + u) ^ 3 / 6 - π ^ 2 / 6 * log (1 + u) -
      log (1 + u) ^ 2 * (log u - log (1 + u)) / 2 - Li₃ (1 / (1 + u)) - Li₃ (-u) := by
    have h := Li₃_add_Li₃_one_sub_add_Li₃_one_sub_inv (x := 1 / (1 + u))
      (by rw [le_div_iff₀ hp]; linarith) (by rw [div_le_one hp]; linarith)
    rw [show (1 : ℝ) - 1 / (1 + u) = u / (1 + u) by field_simp; ring,
      show (1 : ℝ) - (1 / (1 + u))⁻¹ = -u by field_simp; ring, l2, l1] at h
    linarith
  have t3 : Li₃ ((1 - u) * (1 + u)) = Li₃ (1 - u ^ 2) := by
    rw [show (1 - u) * (1 + u) = 1 - u ^ 2 by ring]
  have hM : hpl [one, negOne, zero] u = -(2 / 3) * log u * log (1 - u) * log (1 + u) -
      2 / 3 * log (1 + u) * Li₂ u - i15KR u / 3 - hpl [negOne, one, zero] u := by
    have := i15Hx_mixed hu'; linarith
  unfold i15HxPhi1 i15HxPhi0 i15H3 i15H3S i15TG
  simp only [i15HxP0, i15HxP1, i15TPoly, i15TMono, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, log_one, log_zero, Li₂_one, Li₃_one, Li₂_zero, Li₃_zero, l1, l2, l3, l4, d1, d2,
    d3, d4, d5, t1, t2, t3, hM, i15KR, hpl_zero, hpl_zero_zero, hpl_one_zero hu',
    hpl_negOne_zero hu',
    hpl_zero_zero_zero, hpl_zero_one_zero hu', hpl_zero_negOne_zero hu', hpl_one_zero_zero hu',
    hpl_one_one_zero hu', hpl_negOne_zero_zero hu', hpl_negOne_negOne_zero hu',
    hpl_zero_one_one hu', hpl_zero_negOne_negOne hu', Li_two, Li_three]
  ring

/-- **`∫₀¹ A₂₃,₃(x, u) dx = h₃(u)`** for every integrable slice. -/
theorem integral_i15A23k_three_inner :
    ∀ u ∈ Ioo (0 : ℝ) 1, IntegrableOn (fun x => i15A23k 3 (x, u)) (Ioo 0 1) →
      ∫ x in Ioo (0 : ℝ) 1, i15A23k 3 (x, u) = i15H3 u :=
  fun _ hu hI => (integral_i15A23k_three_slice hu hI).trans (i15HxPhi_sub_eq hu)

/-- **`∫∫ F₃ = -16 π² log 2 + 107 π²/8 + 61 ζ(3) - 1665/16`.** -/
theorem integral_i15F_three :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 3 z =
      -16 * π ^ 2 * log 2 + 107 / 8 * π ^ 2 + 61 * zeta3 - 1665 / 16 :=
  integral_i15F_three_of_inner integral_i15A23k_three_inner

/-- **The target expansion of `K`** from the value of `∫∫ F₄`. -/
theorem hasTruncLaurent_i15K_of_F4
    (h4 : ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 4 z =
      384 * QED.Polylog.Li 4 (1 / 2) + 16 * Real.log 2 ^ 4
        + 32 * Real.pi ^ 2 * Real.log 2 ^ 2 - 72 * Real.pi ^ 2 * Real.log 2
        - 253 / 80 * Real.pi ^ 4 - 2 / 3 * Real.pi ^ 2 * QED.Polylog.zeta3
        + 2267 / 48 * Real.pi ^ 2 + 503 / 2 * QED.Polylog.zeta3 + 12 * QED.Polylog.zeta5
        - 10403 / 32) :
    HasTruncLaurent i15K i15KLaurent 5 :=
  hasTruncLaurent_i15K_of_inner_four integral_i15A23k_three_inner h4

end QED.ThreeLoopD
