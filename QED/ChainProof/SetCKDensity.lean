/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKLPair

/-!
# Set (c), Stage K: the closed-form fibre densities of the L pair

Helper level (no frozen statement). The fibre densities of the two placements of the ladder with
one photon of mass² `t` (`lInner`, `lOuter`), obtained from the exact finite-part formula
`ρ(X) = (2-X)/(X(1-X)) σ(Q(X)) - (finite one-loop part)`, `σ(N) = -(1/π) Im P(-N + i0)`, and
reconstructed exactly in the letters `X`, `1 - X`, `2 - X` (no dilogarithm, and the letter
`1 - X + X²` of the inner cut endpoint cancels in each placement separately):

* `rhoIn`: `ρ_in(1⁻) = 2/9`;
* `rhoOut`: `ρ_out(1⁻) = -1/12`;
* `rhoL = rhoIn + rhoOut`: `ρ_L(1⁻) = 5/36`, `ρ_L(X) = -2 log X + 3/2 - 4 log 2 + o(1)` at
  `X → 0`.

Numerically (scratch note), `setCKStieltjes rhoL t = lPair t` to 20 digits at `t = 1, 4`, and
per placement at `t = 1` to 15 digits. The targets are stated as `Prop`s (`IsLInnerDensity`,
`IsLOuterDensity`, `IsLPairDensity`); `isLPairDensity_rhoL` reduces the pilot to the two
placements, given interval integrability of the two Stieltjes integrands.
-/

@[expose] public section

namespace QED.ChainProof.SetCK

open Real MeasureTheory intervalIntegral Set

/-- The fibre density of the **inner** placement. -/
noncomputable def rhoIn (X : ℝ) : ℝ :=
  -(41 * X ^ 5 - 169 * X ^ 4 + 230 * X ^ 3 - 104 * X ^ 2 + 12 * X + 16) /
      (24 * X * (X - 2) * (X - 1) ^ 2) +
    (13 * X ^ 4 - 46 * X ^ 3 + 60 * X ^ 2 - 40 * X + 12) / (12 * (X - 1) ^ 3) * log X -
    (X - 1) * (13 * X ^ 4 - 46 * X ^ 3 + 36 * X ^ 2 - 8 * X - 4) / (6 * X ^ 2 * (X - 2) ^ 2) *
      log (1 - X) +
    (X ^ 4 - 4 * X ^ 3 + 6 * X ^ 2 - 4 * X + 2) / (X - 1) ^ 3 * log (2 - X)

/-- The fibre density of the **outer** placement. -/
noncomputable def rhoOut (X : ℝ) : ℝ :=
  (X - 3) * (5 * X ^ 3 - 4 * X + 4) / (24 * X * (X - 1) ^ 2) +
    (3 * X ^ 5 - 15 * X ^ 4 + 32 * X ^ 3 - 40 * X ^ 2 + 24 * X - 12) / (12 * (X - 1) ^ 4) *
      log X +
    (X - 1) * (4 * X ^ 2 - 3 * X + 2) / (6 * X) * log (1 - X) -
    (4 * X ^ 6 - 23 * X ^ 5 + 57 * X ^ 4 - 80 * X ^ 3 + 70 * X ^ 2 - 36 * X + 12) /
      (6 * (X - 1) ^ 4) * log (2 - X)

/-- The fibre density of the **L pair**. -/
noncomputable def rhoL (X : ℝ) : ℝ := rhoIn X + rhoOut X

/-- The collected form of `rhoL` (letters `X`, `1 - X`, `2 - X`). -/
theorem rhoL_eq {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    rhoL X =
      -(9 * X ^ 5 - 36 * X ^ 4 + 51 * X ^ 3 - 32 * X ^ 2 + 14 * X - 2) /
          (6 * X * (X - 2) * (X - 1) ^ 2) +
        (X - 2) * (8 * X ^ 4 - 21 * X ^ 3 + 27 * X ^ 2 - 16 * X + 6) / (6 * (X - 1) ^ 4) *
          log X +
        2 * (X - 1) * (X ^ 5 - 8 * X ^ 4 + 19 * X ^ 3 - 14 * X ^ 2 + 4 * X + 1) /
          (3 * X ^ 2 * (X - 2) ^ 2) * log (1 - X) -
        (X - 2) ^ 2 * (4 * X ^ 4 - 13 * X ^ 3 + 19 * X ^ 2 - 12 * X + 6) / (6 * (X - 1) ^ 4) *
          log (2 - X) := by
  have h0 : X ≠ 0 := hX.1.ne'
  have h1 : X - 1 ≠ 0 := by linarith [hX.2]
  have h2 : X - 2 ≠ 0 := by linarith [hX.2]
  unfold rhoL rhoIn rhoOut
  field_simp
  ring

/-- Per-placement target: the inner placement is the Stieltjes transform of `ρ`. -/
def IsLInnerDensity (ρ : ℝ → ℝ) : Prop := ∀ t : ℝ, 0 < t → lInner t = setCKStieltjes ρ t

/-- Per-placement target: the outer placement is the Stieltjes transform of `ρ`. -/
def IsLOuterDensity (ρ : ℝ → ℝ) : Prop := ∀ t : ℝ, 0 < t → lOuter t = setCKStieltjes ρ t

/-- The pilot (S_L) for `rhoL` follows from the two placements. -/
theorem isLPairDensity_rhoL (hin : IsLInnerDensity rhoIn) (hout : IsLOuterDensity rhoOut)
    (hint : ∀ t : ℝ, 0 < t →
      IntervalIntegrable (fun x => rhoIn x * (setCKQ x / (setCKQ x + t))) volume 0 1 ∧
        IntervalIntegrable (fun x => rhoOut x * (setCKQ x / (setCKQ x + t))) volume 0 1) :
    IsLPairDensity rhoL := by
  intro t ht
  rw [lPair, hin t ht, hout t ht]
  unfold setCKStieltjes
  rw [← intervalIntegral.integral_add (hint t ht).1 (hint t ht).2]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [rhoL]
  ring

end QED.ChainProof.SetCK
