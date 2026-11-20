/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXG2H2
public import QED.Polylog.Basic
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Set (c), Stage K, closed forms: the branch-2 `s`-integral of `I(X)`

Helper level (no frozen statement). Step 4 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
session 26+). With the rational coefficients of `SetCKFormXG2D` and `κ = formXkap`, the function

`G₂ = formXG2h + F_s (log s - log(1 - X)) + F̃ (1 - s)(log(1 - s) - log X) + F_u log(2 - X - s)
  + F_k log K₂ + κ log s (log K - log X - log(2 - X)) - κ Li₂(s) + κ Li₂(s/(2 - X))
  - κ Li₂((1 - X)s/K)`

(`formXG2`) is continuous on `[1 - X, 1]` (**`continuousOn_formXG2`**), has derivative
`formXJ2L` on `(1 - X, 1)` (**`hasDerivAt_formXG2`**), and so

**`integral_formXJ2_eq`**: if `formXJ2 X` is integrable on `(1 - X, 1)`, then
`∫_{(1-X,1)} formXJ2 X = G₂(1) - G₂(1 - X)`.
-/

@[expose] public section

open Real Set MeasureTheory QED.Polylog

namespace QED.ChainProof.SetCK

/-- **The branch-2 antiderivative** `G₂`. -/
noncomputable def formXG2 (X s : ℝ) : ℝ :=
  formXG2h X s + formXG2s X s * (log s - log (1 - X)) +
    formXG2t X s * ((1 - s) * log (1 - s) - (1 - s) * log X) +
    formXG2u X s * log (2 - X - s) + formXG2k X s * log (formXK2 X s) +
    formXkap X * log s * (log (formXK X) - log X - log (2 - X)) - formXkap X * Li₂ s +
    formXkap X * Li₂ (s / (2 - X)) - formXkap X * Li₂ ((1 - X) * s / formXK X)

/-- The derivative of `Li₂(cz/d)` for `0 < cs < d`. -/
theorem formX_hasDerivAt_li2 {c d s : ℝ} (hc : 0 < c) (hd : 0 < d) (hs : 0 < s)
    (h1 : c * s < d) : HasDerivAt (fun z => Li₂ (c * z / d)) (-log (1 - c * s / d) / s) s := by
  have hpos : 0 < c * s / d := by positivity
  have hlt : c * s / d < 1 := by rw [div_lt_one hd]; exact h1
  have h := (hasDerivAt_Li₂ (by rw [abs_lt]; constructor <;> linarith) hpos.ne').comp s
    (((hasDerivAt_id' s).const_mul c).div_const d)
  refine h.congr_deriv ?_
  field_simp

section

variable {X s : ℝ}

/-- **`G₂′ = J₂`** on `(1 - X, 1)`. -/
theorem hasDerivAt_formXG2 (hX : X ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (1 - X) 1) :
    HasDerivAt (formXG2 X) (formXJ2L X s) s := by
  obtain ⟨hX0, hX1⟩ := hX
  obtain ⟨hs0, hs1⟩ := hs
  have hs' : 0 < s := by linarith
  have h2X : 0 < 2 - X := by linarith
  have h2Xs : 0 < 2 - X - s := by linarith
  have h1X : 0 < 1 - X := by linarith
  have hK := formXK_pos X
  have hK2 := formXK2_pos (s := s) ⟨hX0, hX1⟩ (by linarith)
  have p0 := hasDerivAt_formXG2h ⟨hX0, hX1⟩ ⟨hs0, hs1⟩
  have p1 := (hasDerivAt_formXG2s ⟨hX0, hX1⟩ ⟨hs0, hs1⟩).mul
    ((hasDerivAt_log hs'.ne').sub_const (log (1 - X)))
  have p2 := hasDerivAt_formXG2t_piece ⟨hX0, hX1⟩ ⟨hs0, hs1⟩
  have p3 := hasDerivAt_formXG2u_piece ⟨hX0, hX1⟩ ⟨hs0, hs1⟩
  have p4 := hasDerivAt_formXG2k_piece ⟨hX0, hX1⟩ ⟨hs0, hs1⟩
  have p5 := ((hasDerivAt_log hs'.ne').const_mul (formXkap X)).mul_const
    (log (formXK X) - log X - log (2 - X))
  have p6 := (hasDerivAt_Li₂ (by rw [abs_lt]; constructor <;> linarith) hs'.ne').const_mul
    (formXkap X)
  have p7 := (formX_hasDerivAt_li2 one_pos h2X hs' (by linarith)).const_mul (formXkap X)
  have p8 := (formX_hasDerivAt_li2 h1X hK hs' (by
    unfold formXK; nlinarith)).const_mul (formXkap X)
  have e : formXG2 X = fun z => formXG2h X z + formXG2s X z * (log z - log (1 - X)) +
      formXG2t X z * ((1 - z) * log (1 - z) - (1 - z) * log X) +
      formXG2u X z * log (2 - X - z) + formXG2k X z * log (formXK2 X z) +
      formXkap X * log z * (log (formXK X) - log X - log (2 - X)) - formXkap X * Li₂ z +
      formXkap X * Li₂ (1 * z / (2 - X)) - formXkap X * Li₂ ((1 - X) * z / formXK X) := by
    funext z
    simp only [formXG2, one_mul]
  rw [e]
  refine ((((((((p0.add p1).add p2).add p3).add p4).add p5).sub p6).add p7).sub p8).congr_deriv ?_
  have l7 : log (1 - 1 * s / (2 - X)) = log (2 - X - s) - log (2 - X) := by
    rw [← log_div h2Xs.ne' h2X.ne']
    congr 1
    field_simp
  have l8 : log (1 - (1 - X) * s / formXK X) = log (formXK2 X s) - log (formXK X) := by
    rw [← log_div hK2.ne' hK.ne']
    congr 1
    field_simp
    unfold formXK2 formXK
    ring
  rw [l7, l8]
  unfold formXJ2L
  ring

/-- `G₂` is continuous on `[1 - X, 1]`. -/
theorem continuousOn_formXG2 (hX : X ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (formXG2 X) (Icc (1 - X) 1) := by
  obtain ⟨hX0, hX1⟩ := hX
  have hK := formXK_pos X
  have hK2 : ∀ s ∈ Icc (1 - X) 1, formXK2 X s ≠ 0 := fun s hs =>
    (formXK2_pos ⟨hX0, hX1⟩ (by linarith [hs.2])).ne'
  have hs0 : ∀ s ∈ Icc (1 - X) 1, s ≠ 0 := fun s hs => by linarith [hs.1]
  have hs2 : ∀ s ∈ Icc (1 - X) 1, s - 2 ≠ 0 := fun s hs => by linarith [hs.2]
  have hu : ∀ s ∈ Icc (1 - X) 1, 2 - X - s ≠ 0 := fun s hs => by linarith [hs.2]
  have hpol : ∀ {n : ℕ} (c : Fin n → ℝ) (D : ℝ) (a b : ℕ), D ≠ 0 →
      ContinuousOn (fun s => formXPol c s / (D * s ^ a * (s - 2) ^ b)) (Icc (1 - X) 1) := by
    intro n c D a b hD
    refine (continuous_formXPol c).continuousOn.div (by fun_prop) fun s hs => ?_
    exact mul_ne_zero (mul_ne_zero hD (pow_ne_zero _ (hs0 s hs))) (pow_ne_zero _ (hs2 s hs))
  have hX' : X ≠ 0 := hX0.ne'
  have hX1' : X - 1 ≠ 0 := by linarith
  have hX2 : X - 2 ≠ 0 := by linarith
  have cs : ContinuousOn (formXG2s X) (Icc (1 - X) 1) := by
    have := hpol (formXG2sN X) (formXG2sD X) 1 0 (by unfold formXG2sD; simp [*, hK.ne'])
    refine this.congr fun s _ => ?_
    unfold formXG2s; ring
  have ct : ContinuousOn (formXG2t X) (Icc (1 - X) 1) := by
    have := hpol (formXG2tN X) (formXG2tD X) 2 3 (by unfold formXG2tD; simp [*])
    exact this.congr fun s _ => rfl
  have cu : ContinuousOn (formXG2u X) (Icc (1 - X) 1) := by
    have := hpol (formXG2uN X) (formXG2uD X) 2 3 (by unfold formXG2uD; simp [*])
    exact this.congr fun s _ => rfl
  have ck : ContinuousOn (formXG2k X) (Icc (1 - X) 1) := by
    have := hpol (formXG2kN X) (formXG2kD X) 2 3 (by unfold formXG2kD; simp [*, hK.ne'])
    exact this.congr fun s _ => rfl
  have cK2 : ContinuousOn (formXK2 X) (Icc (1 - X) 1) := by
    unfold formXK2; fun_prop
  have ch : ContinuousOn (formXG2h X) (Icc (1 - X) 1) := by
    have := hpol (formXG2hRN X) (formXG2hRD X) 2 2 (by unfold formXG2hRD; simp [*, hK.ne'])
    exact (this.congr fun s _ => rfl).add (continuousOn_const.div cK2 hK2)
  have cl1 : Continuous fun s : ℝ => (1 - s) * log (1 - s) :=
    continuous_mul_log.comp (continuous_const.sub continuous_id)
  have cLi : ∀ {f : ℝ → ℝ}, Continuous f → MapsTo f (Icc (1 - X) 1) (Icc (-1) 1) →
      ContinuousOn (fun s => Li₂ (f s)) (Icc (1 - X) 1) := fun hf hm =>
    continuousOn_Li₂.comp hf.continuousOn hm
  have m1 : MapsTo (fun s : ℝ => s) (Icc (1 - X) 1) (Icc (-1) 1) := fun s hs =>
    ⟨by linarith [hs.1], hs.2⟩
  have m2 : MapsTo (fun s : ℝ => s / (2 - X)) (Icc (1 - X) 1) (Icc (-1) 1) := fun s hs => by
    have h2 : 0 < 2 - X := by linarith
    refine ⟨?_, ?_⟩
    · have : 0 ≤ s / (2 - X) := div_nonneg (by linarith [hs.1]) h2.le
      linarith
    · rw [div_le_one h2]; linarith [hs.2]
  have m3 : MapsTo (fun s : ℝ => (1 - X) * s / formXK X) (Icc (1 - X) 1) (Icc (-1) 1) :=
    fun s hs => by
    have h1 : 0 < 1 - X := by linarith
    refine ⟨?_, ?_⟩
    · have : 0 ≤ (1 - X) * s / formXK X :=
        div_nonneg (mul_nonneg h1.le (by linarith [hs.1])) hK.le
      linarith
    · rw [div_le_one hK]; unfold formXK; nlinarith [hs.2]
  have cL : ContinuousOn (fun s => log s) (Icc (1 - X) 1) :=
    continuousOn_log.mono fun s hs => hs0 s hs
  have cLu : ContinuousOn (fun s => log (2 - X - s)) (Icc (1 - X) 1) :=
    (continuousOn_log.comp (by fun_prop) fun s hs => hu s hs)
  have cLk : ContinuousOn (fun s => log (formXK2 X s)) (Icc (1 - X) 1) :=
    continuousOn_log.comp cK2 fun s hs => hK2 s hs
  have e : formXG2 X = fun s => formXG2h X s + formXG2s X s * (log s - log (1 - X)) +
      formXG2t X s * ((1 - s) * log (1 - s) - (1 - s) * log X) +
      formXG2u X s * log (2 - X - s) + formXG2k X s * log (formXK2 X s) +
      formXkap X * log s * (log (formXK X) - log X - log (2 - X)) - formXkap X * Li₂ s +
      formXkap X * Li₂ (s / (2 - X)) - formXkap X * Li₂ ((1 - X) * s / formXK X) := rfl
  rw [e]
  have cl1' := cl1.continuousOn (s := Icc (1 - X) 1)
  have cA := cLi continuous_id m1
  have cB := cLi (f := fun s : ℝ => s / (2 - X)) (by fun_prop) m2
  have cC := cLi (f := fun s : ℝ => (1 - X) * s / formXK X) (by fun_prop) m3
  fun_prop

end

/-- **The branch-2 integral** by the fundamental theorem of calculus. -/
theorem integral_formXJ2_eq {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1)
    (hint : IntegrableOn (formXJ2 X) (Ioo (1 - X) 1)) :
    ∫ s in Ioo (1 - X) 1, formXJ2 X s = formXG2 X 1 - formXG2 X (1 - X) := by
  have hab : 1 - X ≤ 1 := by linarith [hX.1]
  have e : EqOn (formXJ2 X) (formXJ2L X) (Ioo (1 - X) 1) := fun s hs => formXJ2_eq_L hX hs
  have hint' : IntegrableOn (formXJ2L X) (Ioo (1 - X) 1) := hint.congr_fun e measurableSet_Ioo
  rw [setIntegral_congr_fun measurableSet_Ioo e, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (continuousOn_formXG2 hX)
    (fun s hs => hasDerivAt_formXG2 hX hs) ?_
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  exact hint'

end QED.ChainProof.SetCK

end
