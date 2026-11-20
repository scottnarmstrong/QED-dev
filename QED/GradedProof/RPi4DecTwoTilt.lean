/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecTwoAlg
public import QED.GradedProof.RPi4DecContF

/-!
# (R-Π₄) step L9: the tilt chain rule for second differences

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (second
differences in `s`). The tilted vector `k'(s) = tiltVec c s = (√(2c² - s), 0, c, c)` is the
point `decTiltU c S₀ S s` of the segment `lineK (tiltBase c S₀ S) (tiltDir c S₀ S)`; the
segment parameter `s ↦ decTiltU c S₀ S s` (a square root, an affine map and `upar`) is of class
`QED.GradedProof.RPi4.DecTwoReg` on `[S₀, S]`, so second-difference bounds along the segment
give second-difference bounds in `s` at the tilted vectors.

* `dec_twoReg_upar`: `upar` on `[-2/3, 2/3]`;
* `dec_twoReg_tiltU`: `decTiltU c S₀ S` on `[S₀, S]`;
* **`dec_twoReg_tilt`**: the chain rule.
-/

@[expose] public section

open Set

namespace QED.GradedProof.RPi4

open QED.GradedProof.SE2

/-- **`upar` is of class `DecTwoReg` on `[-2/3, 2/3]`.** -/
theorem dec_twoReg_upar : ∃ M L K : ℝ, DecTwoReg (-(2 / 3)) (2 / 3) upar M L K := by
  have hid := DecTwoReg.id (lo := -(2 / 3)) (hi := 2 / 3)
  have hφ := (DecTwoReg.const (lo := -(2 / 3)) (hi := 2 / 3) (1 : ℝ)).add
    ((DecTwoReg.const (4 : ℝ)).mul (hid.mul hid))
  have hlow : ∀ t ∈ Icc (-(2 / 3) : ℝ) (2 / 3), (1 : ℝ) ≤ 1 + 4 * (t * t) := fun t _ => by
    nlinarith [mul_self_nonneg t]
  have hs := hφ.sqrt one_pos hlow
  have hd := (DecTwoReg.const (lo := -(2 / 3)) (hi := 2 / 3) (1 : ℝ)).add hs
  have hdl : ∀ t ∈ Icc (-(2 / 3) : ℝ) (2 / 3), (1 : ℝ) ≤ ‖1 + Real.sqrt (1 + 4 * (t * t))‖ :=
    fun t _ => by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith [Real.sqrt_nonneg (1 + 4 * (t * t))]
  have hq := ((DecTwoReg.const (2 : ℝ)).mul hid).mul (hd.inv one_pos hdl)
  refine ⟨_, _, _, hq.congr fun t _ => ?_⟩
  simp only [upar, div_eq_mul_inv, sq]

/-- **The segment parameter of the tilted vectors is of class `DecTwoReg` on `[S₀, S]`.** -/
theorem dec_twoReg_tiltU {c S₀ S : ℝ} (hS₀S : S₀ < S) (hS : S < 2 * c ^ 2) :
    ∃ M L K : ℝ, DecTwoReg S₀ S (decTiltU c S₀ S) M L K := by
  set lo := Real.sqrt (2 * c ^ 2 - S)
  set hi := Real.sqrt (2 * c ^ 2 - S₀)
  have hlohi : lo < hi := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  set w := 3 / 4 * (hi - lo)
  have hw : 0 < w := by simp only [w]; linarith
  have hψ := (DecTwoReg.const (lo := S₀) (hi := S) (2 * c ^ 2 : ℝ)).sub
    DecTwoReg.id
  have hψl : ∀ s ∈ Icc S₀ S, 2 * c ^ 2 - S ≤ 2 * c ^ 2 - s := fun s hs => by linarith [hs.2]
  have hτ := hψ.sqrt (by linarith) hψl
  have ht := (hτ.sub (DecTwoReg.const ((lo + hi) / 2))).const_mul (1 / w)
  obtain ⟨Mu, Lu, Ku, hu⟩ := dec_twoReg_upar
  have hmap : ∀ s ∈ Icc S₀ S, 1 / w * (Real.sqrt (2 * c ^ 2 - s) - (lo + hi) / 2) ∈
      Icc (-(2 / 3) : ℝ) (2 / 3) := fun s hs => by
    have h1 : lo ≤ Real.sqrt (2 * c ^ 2 - s) := Real.sqrt_le_sqrt (by linarith [hs.2])
    have h2 : Real.sqrt (2 * c ^ 2 - s) ≤ hi := Real.sqrt_le_sqrt (by linarith [hs.1])
    have e : 1 / w * (Real.sqrt (2 * c ^ 2 - s) - (lo + hi) / 2) =
        (Real.sqrt (2 * c ^ 2 - s) - (lo + hi) / 2) / w := by ring
    rw [e]
    constructor
    · rw [le_div_iff₀ hw]; simp only [w]; linarith
    · rw [div_le_iff₀ hw]; simp only [w]; linarith
  refine ⟨_, _, _, (hu.comp ht hmap).congr fun s _ => ?_⟩
  simp only [decTiltU, lo, hi, w]
  congr 1
  ring

/-- **The tilt chain rule**: a second-difference bound along the tilted segment gives one in `s`
at the tilted vectors, on `[S₀, S]`. -/
theorem dec_twoReg_tilt {c S₀ S : ℝ} (hS₀S : S₀ < S) (hS : S < 2 * c ^ 2)
    {G : (Fin 4 → ℝ) → ℂ} {M L K : ℝ}
    (hG : DecTwoReg (-(1 / 2)) (1 / 2)
      (fun u => G (lineK (tiltBase c S₀ S) (tiltDir c S₀ S) u)) M L K) :
    ∃ L' K' : ℝ, DecTwoReg S₀ S (fun s => G (tiltVec c s)) M L' K' := by
  obtain ⟨Mu, Lu, Ku, hu⟩ := dec_twoReg_tiltU hS₀S hS
  have hmap : ∀ s ∈ Icc S₀ S, decTiltU c S₀ S s ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := fun s hs =>
    dec_mem_Icc_half.mpr (dec_tiltVec_eq_lineK hS₀S hS hs.1 hs.2).1
  refine ⟨_, _, (hG.comp hu hmap).congr fun s hs => ?_⟩
  simp only [← (dec_tiltVec_eq_lineK hS₀S hS hs.1 hs.2).2]

end QED.GradedProof.RPi4

end
