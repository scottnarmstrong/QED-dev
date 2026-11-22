/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI4P1SM
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Set (e), master I₄: the substitution `n ↦ t` at fixed `(a, b, l)`

In the electron-line gauge `a + b + c = 1` of `QED.ThreeLoopE.SetEMastersI4P1SM`, write
`λ = a + b`, `k = b + c` and

  `N = λ c + k l`,   `D = k (k l + λ (a + c))`.

Then `W = U₁ - U₂ = λ² n + D` and `λ² U₁ = (λ + l) W - N²`, `λ² U₂ = (λ c + l) W - N²`
(`QED.ThreeLoopE.i4SW_eq`). The substitution `s = N² / W`, `t = l - s`, i.e.

  `n = (N² / (l - t) - D) / λ²`,   `dn = N² / (λ² (l - t)²) dt`,

maps `t ∈ (l - N² / D, l)` onto `n > 0`, and turns `U₁`, `U₂` into
`(λ + t) N² / (λ² s)`, `(λ c + t) N² / (λ² s)`. The `m`-integrated density `i4SMVal U₁ U₂`
times the Jacobian becomes

  `λ² / (N² (λ + t)(λ c + t)) · (log (λ c + t) + 2 log N - log (l - t) - 2 log λ + 4
     + 3 λ² log (λ² / (λ + t)) / (λ c + t))`

(`QED.ThreeLoopE.i4STDens`), in which `l` enters only through `N` and `l - t`.

## Main definitions

* `QED.ThreeLoopE.i4SN`, `QED.ThreeLoopE.i4SD`, `QED.ThreeLoopE.i4STmin`,
  `QED.ThreeLoopE.i4SNofT`, `QED.ThreeLoopE.i4STJac`, `QED.ThreeLoopE.i4STDens`.

## Main results

* `QED.ThreeLoopE.i4ST_subst`: the change of variables for any integrand.
* `QED.ThreeLoopE.i4ST_dens`: the transformed density.
* `QED.ThreeLoopE.i4ST_fiber`: integrability and the integral at fixed `(a, b, l)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real

namespace QED.ThreeLoopE

/-- `N = λ c + k l` with `λ = a + b`, `k = b + c`. -/
def i4SN (a b c l : ℝ) : ℝ := (a + b) * c + (b + c) * l

/-- `D = k (k l + λ (a + c))`, the value of `W = U₁ - U₂` at `n = 0`. -/
def i4SD (a b c l : ℝ) : ℝ := (b + c) * ((b + c) * l + (a + b) * (a + c))

/-- The lower end `l - N² / D` of the `t`-range. -/
noncomputable def i4STmin (a b c l : ℝ) : ℝ := l - i4SN a b c l ^ 2 / i4SD a b c l

/-- The inverse substitution `n = (N² / (l - t) - D) / λ²`. -/
noncomputable def i4SNofT (a b c l t : ℝ) : ℝ :=
  (i4SN a b c l ^ 2 / (l - t) - i4SD a b c l) / (a + b) ^ 2

/-- The Jacobian `dn / dt = N² / (λ² (l - t)²)`. -/
noncomputable def i4STJac (a b c l t : ℝ) : ℝ :=
  i4SN a b c l ^ 2 / ((a + b) ^ 2 * (l - t) ^ 2)

/-- The density in `(l, t)`. -/
noncomputable def i4STDens (a b c l t : ℝ) : ℝ :=
  (a + b) ^ 2 / (i4SN a b c l ^ 2 * (a + b + t) * ((a + b) * c + t)) *
    (log ((a + b) * c + t) + 2 * log (i4SN a b c l) - log (l - t) - 2 * log (a + b) + 4 +
      3 * (a + b) ^ 2 * log ((a + b) ^ 2 / (a + b + t)) / ((a + b) * c + t))

/-- `W = U₁ - U₂ = λ² n + D`, and `λ² U₁ = (λ + l) W - N²`. -/
theorem i4SW_eq {a b c : ℝ} (habc : a + b + c = 1) (l n : ℝ) :
    i4SU1 a b c l n - i4SU2 a b c l n = (a + b) ^ 2 * n + i4SD a b c l ∧
      (a + b) ^ 2 * i4SU1 a b c l n =
        (a + b + l) * (i4SU1 a b c l n - i4SU2 a b c l n) - i4SN a b c l ^ 2 := by
  obtain rfl : c = 1 - a - b := by linarith
  unfold i4SU1 i4SU2 i4SD i4SN
  constructor <;> ring

theorem i4SN_pos {a b c l : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hl : 0 < l) :
    0 < i4SN a b c l := by
  unfold i4SN; positivity

theorem i4SD_pos {a b c l : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hl : 0 < l) :
    0 < i4SD a b c l := by
  unfold i4SD; positivity

/-- `U₁` and `U₂` at `n = i4SNofT t`. -/
theorem i4SU_NofT {a b c l t : ℝ} (ha : 0 < a) (hb : 0 < b) (habc : a + b + c = 1)
    (ht : t < l) :
    i4SU1 a b c l (i4SNofT a b c l t) =
        (a + b + t) * i4SN a b c l ^ 2 / ((a + b) ^ 2 * (l - t)) ∧
      i4SU2 a b c l (i4SNofT a b c l t) =
        ((a + b) * c + t) * i4SN a b c l ^ 2 / ((a + b) ^ 2 * (l - t)) := by
  obtain ⟨hW, h1⟩ := i4SW_eq habc l (i4SNofT a b c l t)
  have hs : l - t ≠ 0 := (sub_pos.2 ht).ne'
  have hab2 : (a + b) ^ 2 ≠ 0 := by positivity
  have hW' : i4SU1 a b c l (i4SNofT a b c l t) - i4SU2 a b c l (i4SNofT a b c l t) =
      i4SN a b c l ^ 2 / (l - t) := by
    rw [hW]; unfold i4SNofT; field_simp; ring
  rw [hW'] at h1
  have e1 : i4SU1 a b c l (i4SNofT a b c l t) =
      (a + b + t) * i4SN a b c l ^ 2 / ((a + b) ^ 2 * (l - t)) := by
    rw [eq_div_iff (mul_ne_zero hab2 hs), mul_comm, mul_assoc, mul_left_comm, h1]
    field_simp; ring
  refine ⟨e1, ?_⟩
  have e2 := hW'
  rw [e1] at e2
  have hc : c = 1 - a - b := by linarith
  rw [eq_div_iff (mul_ne_zero hab2 hs)]
  rw [eq_div_iff hs] at e2
  have : i4SU2 a b c l (i4SNofT a b c l t) =
      (a + b + t) * i4SN a b c l ^ 2 / ((a + b) ^ 2 * (l - t)) - i4SN a b c l ^ 2 / (l - t) := by
    rw [← e1, ← hW']; ring
  rw [this]
  field_simp
  rw [hc]; ring

/-- The substitution `n = i4SNofT t` maps `(i4STmin, l)` onto `n > 0`. -/
theorem i4SNofT_image {a b c l : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hl : 0 < l) :
    i4SNofT a b c l '' Ioo (i4STmin a b c l) l = Ioi 0 := by
  have hN := i4SN_pos ha hb hc hl
  have hD := i4SD_pos ha hb hc hl
  have hab2 : 0 < (a + b) ^ 2 := by positivity
  ext n
  constructor
  · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
    have hs : 0 < l - t := sub_pos.2 ht2
    have h1 : l - t < i4SN a b c l ^ 2 / i4SD a b c l := by unfold i4STmin at ht1; linarith
    rw [lt_div_iff₀ hD] at h1
    have h2 : i4SD a b c l < i4SN a b c l ^ 2 / (l - t) := by
      rw [lt_div_iff₀ hs]; linarith
    exact div_pos (sub_pos.2 h2) hab2
  · intro hn
    have hn : 0 < n := hn
    have hX : 0 < (a + b) ^ 2 * n + i4SD a b c l := by positivity
    refine ⟨l - i4SN a b c l ^ 2 / ((a + b) ^ 2 * n + i4SD a b c l), ⟨?_, ?_⟩, ?_⟩
    · unfold i4STmin
      have : i4SN a b c l ^ 2 / ((a + b) ^ 2 * n + i4SD a b c l) <
          i4SN a b c l ^ 2 / i4SD a b c l :=
        div_lt_div_of_pos_left (by positivity) hD (by linarith [mul_pos hab2 hn])
      linarith
    · have : 0 < i4SN a b c l ^ 2 / ((a + b) ^ 2 * n + i4SD a b c l) := by positivity
      linarith
    · unfold i4SNofT
      rw [sub_sub_cancel]
      field_simp
      ring

theorem i4SNofT_injOn {a b c l : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hl : 0 < l) :
    InjOn (i4SNofT a b c l) (Ioo (i4STmin a b c l) l) := by
  intro t₁ h₁ t₂ h₂ he
  have hN := (i4SN_pos ha hb hc hl).ne'
  have hab2 : (a + b) ^ 2 ≠ 0 := by positivity
  have hs₁ : l - t₁ ≠ 0 := (sub_pos.2 h₁.2).ne'
  have hs₂ : l - t₂ ≠ 0 := (sub_pos.2 h₂.2).ne'
  unfold i4SNofT at he
  rw [div_left_inj' hab2, sub_left_inj, div_eq_div_iff hs₁ hs₂] at he
  have := mul_left_cancel₀ (pow_ne_zero 2 hN) he
  linarith

theorem i4SNofT_hasDerivAt {a b c l t : ℝ} (ht : t < l) :
    HasDerivAt (i4SNofT a b c l) (i4STJac a b c l t) t := by
  have hs : l - t ≠ 0 := (sub_pos.2 ht).ne'
  have h := ((((hasDerivAt_id t).const_sub l).inv hs).const_mul (i4SN a b c l ^ 2)).sub_const
    (i4SD a b c l) |>.div_const ((a + b) ^ 2)
  have e : i4SNofT a b c l =
      fun t => (i4SN a b c l ^ 2 * (l - id t)⁻¹ - i4SD a b c l) / (a + b) ^ 2 := by
    funext t; simp [i4SNofT, div_eq_mul_inv]
  rw [e]
  convert h using 1
  unfold i4STJac
  simp only [id, neg_neg, one_div]
  rcases eq_or_ne ((a + b) ^ 2) 0 with h0 | h0
  · simp [h0]
  · field_simp

theorem i4STJac_pos {a b c l t : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hl : 0 < l)
    (ht : t < l) : 0 < i4STJac a b c l t := by
  have hN := i4SN_pos ha hb hc hl
  have hs : 0 < l - t := sub_pos.2 ht
  unfold i4STJac; positivity

/-- **The change of variables** `n = i4SNofT t` at fixed `(a, b, l)`, for any integrand. -/
theorem i4ST_subst {a b c l : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hl : 0 < l)
    (g : ℝ → ℝ) :
    (IntegrableOn g (Ioi 0) ↔ IntegrableOn
        (fun t => i4STJac a b c l t * g (i4SNofT a b c l t)) (Ioo (i4STmin a b c l) l)) ∧
      ∫ n in Ioi 0, g n =
        ∫ t in Ioo (i4STmin a b c l) l, i4STJac a b c l t * g (i4SNofT a b c l t) := by
  have hd : ∀ t ∈ Ioo (i4STmin a b c l) l,
      HasDerivWithinAt (i4SNofT a b c l) (i4STJac a b c l t) (Ioo (i4STmin a b c l) l) t :=
    fun t ht => (i4SNofT_hasDerivAt ht.2).hasDerivWithinAt
  have hJ : ∀ t ∈ Ioo (i4STmin a b c l) l,
      |i4STJac a b c l t| • g (i4SNofT a b c l t) =
        i4STJac a b c l t * g (i4SNofT a b c l t) := fun t ht => by
    rw [abs_of_pos (i4STJac_pos ha hb hc hl ht.2), smul_eq_mul]
  have hI := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hd
    (i4SNofT_injOn ha hb hc hl) g
  have hE := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd
    (i4SNofT_injOn ha hb hc hl) g
  rw [i4SNofT_image ha hb hc hl] at hI hE
  refine ⟨hI.trans (integrableOn_congr_fun hJ measurableSet_Ioo), ?_⟩
  rw [hE]
  exact setIntegral_congr_fun measurableSet_Ioo hJ

/-- **The transformed density**: the Jacobian times `i4SMVal U₁ U₂` at `n = i4SNofT t`. -/
theorem i4ST_dens {a b c l t : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a + b + c = 1) (hl : 0 < l) (ht : t ∈ Ioo (i4STmin a b c l) l) :
    i4STJac a b c l t *
        i4SMVal (i4SU1 a b c l (i4SNofT a b c l t)) (i4SU2 a b c l (i4SNofT a b c l t)) =
      i4STDens a b c l t := by
  have hn : 0 < i4SNofT a b c l t := by
    have := mem_image_of_mem (i4SNofT a b c l) ht
    rw [i4SNofT_image ha hb hc hl] at this
    exact this
  obtain ⟨hU1, hU2, -⟩ := i4SU_pos ha hb hc hl hn
  obtain ⟨e1, e2⟩ := i4SU_NofT ha hb habc ht.2
  set N := i4SN a b c l with hNdef
  have hN : 0 < N := i4SN_pos ha hb hc hl
  have hs : 0 < l - t := sub_pos.2 ht.2
  have hab2 : 0 < a + b := by positivity
  have hP : 0 < N ^ 2 / ((a + b) ^ 2 * (l - t)) := by positivity
  rw [e1] at hU1
  rw [e2] at hU2
  have h1 : 0 < a + b + t := by
    rw [mul_div_assoc] at hU1; exact pos_of_mul_pos_left hU1 hP.le
  have h2 : 0 < (a + b) * c + t := by
    rw [mul_div_assoc] at hU2; exact pos_of_mul_pos_left hU2 hP.le
  have hc' : c = 1 - a - b := by linarith
  have hR : 1 - ((a + b) * c + t) * N ^ 2 / ((a + b) ^ 2 * (l - t)) /
      ((a + b + t) * N ^ 2 / ((a + b) ^ 2 * (l - t))) = (a + b) ^ 2 / (a + b + t) := by
    field_simp; rw [hc']; ring
  have hL : log (((a + b) * c + t) * N ^ 2 / ((a + b) ^ 2 * (l - t))) =
      log ((a + b) * c + t) + 2 * log N - 2 * log (a + b) - log (l - t) := by
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity), log_pow, log_pow]
    push_cast; ring
  unfold i4SMVal i4STDens i4STJac
  rw [e1, e2, hR, hL, ← hNdef]
  generalize log ((a + b) ^ 2 / (a + b + t)) = L₁
  generalize log ((a + b) * c + t) = L₂
  generalize log N = L₃
  generalize log (a + b) = L₄
  generalize log (l - t) = L₅
  field_simp
  ring

/-- **The fiber at fixed `(a, b, l)`**: integrability and the value of the `n`-integral in the
variable `t`, for the density and for its absolute value. -/
theorem i4ST_fiber {a b c l : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a + b + c = 1) (hl : 0 < l) :
    (IntegrableOn (fun n => i4SMVal (i4SU1 a b c l n) (i4SU2 a b c l n)) (Ioi 0) ↔
        IntegrableOn (i4STDens a b c l) (Ioo (i4STmin a b c l) l)) ∧
      (∫ n in Ioi 0, i4SMVal (i4SU1 a b c l n) (i4SU2 a b c l n) =
        ∫ t in Ioo (i4STmin a b c l) l, i4STDens a b c l t) ∧
      ∫ n in Ioi 0, ‖i4SMVal (i4SU1 a b c l n) (i4SU2 a b c l n)‖ =
        ∫ t in Ioo (i4STmin a b c l) l, ‖i4STDens a b c l t‖ := by
  have hD := fun t (ht : t ∈ Ioo (i4STmin a b c l) l) => i4ST_dens ha hb hc habc hl ht
  obtain ⟨hI, hE⟩ := i4ST_subst ha hb hc hl
    (fun n => i4SMVal (i4SU1 a b c l n) (i4SU2 a b c l n))
  obtain ⟨-, hE'⟩ := i4ST_subst ha hb hc hl
    (fun n => ‖i4SMVal (i4SU1 a b c l n) (i4SU2 a b c l n)‖)
  refine ⟨hI.trans (integrableOn_congr_fun hD measurableSet_Ioo), ?_, ?_⟩
  · rw [hE]; exact setIntegral_congr_fun measurableSet_Ioo hD
  · rw [hE']
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    show _ = _
    rw [← hD t ht, norm_mul, Real.norm_of_nonneg (i4STJac_pos ha hb hc hl ht.2).le]

end QED.ThreeLoopE

end
