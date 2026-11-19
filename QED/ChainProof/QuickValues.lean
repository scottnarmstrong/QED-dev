/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.A1SixSetB
public import QED.Chain.VPChainSetBBounds

/-!
# The set (b) constant: enclosure and integral representation (C₆), (C₇)

Helper proofs of the Phase 5 Stage 1a theorem goals (C₆) `QED.VPChain.a1SixSetB_bounds` and
(C₇) `QED.VPChain.integral_chainTwo_eq_a1SixSetB` (decision D-53), from the helper-level results
`QED.Chain.aSetB_bounds`, `QED.Chain.integral_setB` and `QED.Chain.intervalIntegrable_setB`.

* `QED.ChainProof.Quick.a1SixSetB_eq_aSetB`: the frozen constant (C₅) is `QED.Chain.aSetB`, by
  `rfl`.
* `QED.ChainProof.a1SixSetB_bounds'`: the exact statement of (C₆).
* `QED.ChainProof.integral_chainTwo_eq_a1SixSetB'`: the exact statement of (C₇).
-/

@[expose] public section

namespace QED.ChainProof

/-- The frozen constant (C₅) is the helper constant `QED.Chain.aSetB`. -/
theorem Quick.a1SixSetB_eq_aSetB : QED.VPChain.a1SixSetB = QED.Chain.aSetB := rfl

/-- (C₆) **`A₁⁽⁶⁾(b)` to five significant digits.** -/
theorem a1SixSetB_bounds' :
    0.00255852 < QED.VPChain.a1SixSetB ∧ QED.VPChain.a1SixSetB < 0.00255853 := by
  rw [Quick.a1SixSetB_eq_aSetB]
  exact QED.Chain.aSetB_bounds

/-- (C₇) **`A₁⁽⁶⁾(b)` is the chain integral.** The integrand is `(1 - x) Π̂(x²/(1 - x))²` with
`Π̂ = QED.Chain.piHat` unfolded. -/
theorem integral_chainTwo_eq_a1SixSetB' :
    IntervalIntegrable (fun x : ℝ => (1 - x) * (2 * ∫ t in (0 : ℝ)..1,
        t * (1 - t) * Real.log (1 + t * (1 - t) * (x ^ 2 / (1 - x)))) ^ 2)
        MeasureTheory.volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - x) * (2 * ∫ t in (0 : ℝ)..1,
        t * (1 - t) * Real.log (1 + t * (1 - t) * (x ^ 2 / (1 - x)))) ^ 2 =
        QED.VPChain.a1SixSetB :=
  ⟨QED.Chain.intervalIntegrable_setB, QED.Chain.integral_setB.trans Quick.a1SixSetB_eq_aSetB.symm⟩

end QED.ChainProof

end
