/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1At0

/-!
# Set (d), master `I₅`: the atoms of the primitive at `x = 1 - ξ`

Each atom of the primitive `QED.ThreeLoopD.i5C1PB` other than `log (1 - ξ - x)` has a limit as
`x → (1 - ξ)⁻`, in the normal form of `QED.ThreeLoopD.SetDMastersI5C1At0`
(`QED.ThreeLoopD.i5C1E_ty_0`, ...); the dilogarithms in the coefficient of `log (1 - ξ - x)` are
differentiable at `1 - ξ` (`QED.ThreeLoopD.i5C1E_dy_9`, ...).

## Main results

* `QED.ThreeLoopD.i5C1E_ty_0`, ..., `QED.ThreeLoopD.i5C1E_ty_53`.
-/

@[expose] public section

open Set Real Filter Topology QED.Polylog

namespace QED.ThreeLoopD

theorem i5C1E_ty_0 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => log x) (𝓝[<] (1 - ξ)) (𝓝 (log (1 - ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tlog (g := fun x => x) (p := (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 1 -
      ξ) (by fun_prop) (rfl)
    (by positivity) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_1 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => log (ξ * x + (1 - ξ))) (𝓝[<] (1 - ξ)) (𝓝 (log (1 - ξ) + log (1 + ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tlog (g := fun x => ξ * x + (1 - ξ)) (p := (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a :=
      (1 - ξ) * (1 + ξ)) (by fun_prop) (by ring)
    (by positivity) nhdsWithin_le_nhds
  rw [log_mul hy.ne' h1p.ne'] at h
  exact h

theorem i5C1E_ty_5 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => log (1 - x)) (𝓝[<] (1 - ξ)) (𝓝 (log ξ)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tlog (g := fun x => 1 - x) (p := (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a :=
      ξ) (by fun_prop) (by ring)
    (by positivity) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_6 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => log (ξ * x ^ 2 + (1 - ξ) ^ 2)) (𝓝[<] (1 - ξ)) (𝓝 (2 * log (1 - ξ) +
        log (1 + ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tlog (g := fun x => ξ * x ^ 2 + (1 - ξ) ^ 2) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := (1 - ξ) ^ 2 * (1 + ξ)) (by fun_prop) (by ring)
    (by positivity) nhdsWithin_le_nhds
  rw [log_mul (by positivity) h1p.ne', log_pow] at h
  push_cast at h
  exact h

theorem i5C1E_ty_7 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => log (ξ * x + (1 - ξ) ^ 2)) (𝓝[<] (1 - ξ)) (𝓝 (log (1 - ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tlog (g := fun x => ξ * x + (1 - ξ) ^ 2) (p := (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a :=
      1 - ξ) (by fun_prop) (by ring)
    (by positivity) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_9 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (x)) (𝓝[<] (1 - ξ)) (𝓝 (π ^ 2 / 6 - Li₂ ξ - log ξ * log (1 - ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => x) (p := (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 1 - ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by linarith, by linarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b9 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [i5C1N_oneSub hξ] at h
  exact h

theorem i5C1E_ty_10 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (x / (1 - ξ))) (𝓝[<] (1 - ξ)) (𝓝 (π ^ 2 / 6)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => x / (1 - ξ)) (p := (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b10 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₂_one] at h
  exact h

theorem i5C1E_ty_11 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (ξ / (1 - x))) (𝓝[<] (1 - ξ)) (𝓝 (π ^ 2 / 6)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => ξ / (1 - x)) (p := (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by simp only [sub_sub_cancel]; field_simp) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b11 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₂_one] at h
  exact h

theorem i5C1E_ty_12 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (ξ * (1 - x))) (𝓝[<] (1 - ξ)) (𝓝 (2 * Li₂ ξ + 2 * Li₂ (-ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => ξ * (1 - x)) (p := (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := ξ ^ 2)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by nlinarith, by nlinarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b12 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [i5C1N_sq hξ] at h
  exact h

theorem i5C1E_ty_13 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (-(ξ * x / (1 - ξ)))) (𝓝[<] (1 - ξ)) (𝓝 (Li₂ (-ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => -(ξ * x / (1 - ξ))) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := -ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp) ⟨by linarith, by linarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b13 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_14 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (x / (ξ * x + (1 - ξ)))) (𝓝[<] (1 - ξ)) (𝓝 (π ^ 2 / 6 + Li₂ (-ξ) +
        log (1 + ξ) ^ 2 / 2 + log (1 + ξ) * (log ξ - log (1 + ξ)))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => x / (ξ * x + (1 - ξ))) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := 1 / (1 + ξ))
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by have := div_pos one_pos h1p; linarith,
        by rw [div_le_one h1p]; linarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b14 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [i5C1N_inv hξ] at h
  exact h

theorem i5C1E_ty_15 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) (𝓝[<] (1 - ξ)) (𝓝 (Li₂ (-ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => -(ξ * x ^ 2 / (1 - ξ) ^ 2)) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := -ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp) ⟨by linarith, by linarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b15 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_16 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (ξ * (1 - ξ - x) / (1 - ξ))) (𝓝[<] (1 - ξ)) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => ξ * (1 - ξ - x) / (1 - ξ)) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b16 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₂_zero] at h
  exact h

theorem i5C1E_ty_17 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ)))) (𝓝[<] (1 - ξ)) (𝓝 (π ^ 2 / 6)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => (1 + ξ) * x / (ξ * x + (1 - ξ))) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b17 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₂_one] at h
  exact h

theorem i5C1E_ty_18 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (x / (ξ * x + (1 - ξ) ^ 2))) (𝓝[<] (1 - ξ)) (𝓝 (π ^ 2 / 6)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => x / (ξ * x + (1 - ξ) ^ 2)) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b18 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₂_one] at h
  exact h

theorem i5C1E_ty_19 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) (𝓝[<] (1 - ξ)) (𝓝 (-Li₂ (-ξ) -
        log (1 + ξ) ^ 2 / 2)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => ξ * (1 - ξ) / (ξ * x + (1 - ξ))) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := ξ / (1 + ξ))
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by have := div_pos h0 h1p; linarith, by rw [div_le_one h1p]; linarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b19 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [i5C1N_div hξ] at h
  exact h

theorem i5C1E_ty_20 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))))) (𝓝[<] (1 - ξ)) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => -(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b20 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₂_zero] at h
  exact h

theorem i5C1E_ty_21 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))) (𝓝[<] (1 -
        ξ)) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => -(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) (p :=
      (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b21 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₂_zero] at h
  exact h

theorem i5C1E_ty_22 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - x))) (𝓝[<] (1 - ξ)) (𝓝 (Li₃ ξ)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - x)) (p := (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by linarith, by linarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b22 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_23 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (x / (1 - ξ))) (𝓝[<] (1 - ξ)) (𝓝 (zeta3)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => x / (1 - ξ)) (p := (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b23 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_ty_24 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ / (1 - x))) (𝓝[<] (1 - ξ)) (𝓝 (zeta3)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ / (1 - x)) (p := (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by simp only [sub_sub_cancel]; field_simp) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b24 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_ty_25 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * (1 - x))) (𝓝[<] (1 - ξ)) (𝓝 (Li₃ (ξ ^ 2))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * (1 - x)) (p := (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := ξ ^ 2)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by nlinarith, by nlinarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b25 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_26 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (-(ξ * x / (1 - ξ)))) (𝓝[<] (1 - ξ)) (𝓝 (Li₃ (-ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => -(ξ * x / (1 - ξ))) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := -ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp) ⟨by linarith, by linarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b26 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_27 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((ξ * x + (1 - ξ)))) (𝓝[<] (1 - ξ)) (𝓝 (Li₃ (1 - ξ ^ 2))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (ξ * x + (1 - ξ))) (p := (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a :=
      1 - ξ ^ 2)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by nlinarith, by nlinarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b27 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_28 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - ξ - x) / (1 - x))) (𝓝[<] (1 - ξ)) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - ξ - x) / (1 - x)) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b28 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_ty_29 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) (𝓝[<] (1 - ξ)) (𝓝 (Li₃ (-ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => -(ξ * x ^ 2 / (1 - ξ) ^ 2)) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := -ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp) ⟨by linarith, by linarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b29 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_30 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - ξ - x) / (1 - ξ))) (𝓝[<] (1 - ξ)) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - ξ - x) / (1 - ξ)) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b30 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_ty_31 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * (1 - ξ - x) / (1 - ξ))) (𝓝[<] (1 - ξ)) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * (1 - ξ - x) / (1 - ξ)) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b31 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_ty_32 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 + ξ) * x / (ξ * x + (1 - ξ)))) (𝓝[<] (1 - ξ)) (𝓝 (zeta3)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 + ξ) * x / (ξ * x + (1 - ξ))) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b32 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_ty_33 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) (𝓝[<] (1 -
        ξ)) (𝓝 (Li₃ (ξ / (1 + ξ)))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * (1 - ξ) / (ξ * x + (1 - ξ))) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := ξ / (1 + ξ))
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by have := div_pos h0 h1p; linarith, by rw [div_le_one h1p]; linarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b33 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_34 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - ξ - x) / (ξ * x + (1 - ξ)))) (𝓝[<] (1 - ξ)) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - ξ - x) / (ξ * x + (1 - ξ))) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b34 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_ty_35 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))))) (𝓝[<] (1 - ξ)) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => -(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b35 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_ty_36 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - ξ) * (1 - x) / (ξ * x + (1 - ξ)))) (𝓝[<] (1 -
        ξ)) (𝓝 (Li₃ (ξ / (1 + ξ)))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - ξ) * (1 - x) / (ξ * x + (1 - ξ))) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := ξ / (1 + ξ))
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by have := div_pos h0 h1p; linarith, by rw [div_le_one h1p]; linarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b36 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_37 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((ξ * x + (1 - ξ) ^ 2) / (1 - ξ))) (𝓝[<] (1 - ξ)) (𝓝 (zeta3)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (ξ * x + (1 - ξ) ^ 2) / (1 - ξ)) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b37 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_ty_38 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)))) (𝓝[<] (1 -
        ξ)) (𝓝 (Li₃ (1 / (1 + ξ)))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))) (p :=
      (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 1 / (1 + ξ))
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by have := div_pos one_pos h1p; linarith,
        by rw [div_le_one h1p]; linarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b38 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_39 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2))) (𝓝[<] (1 -
        ξ)) (𝓝 (Li₃ (1 - ξ ^ 2))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2)) (p :=
      (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 1 - ξ ^ 2)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by nlinarith, by nlinarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b39 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_40 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * x / (ξ * x + (1 - ξ)))) (𝓝[<] (1 - ξ)) (𝓝 (Li₃ (ξ / (1 + ξ)))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * x / (ξ * x + (1 - ξ))) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := ξ / (1 + ξ))
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by have := div_pos h0 h1p; linarith, by rw [div_le_one h1p]; linarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b40 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_41 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * (1 - ξ - x) / ((1 - ξ) * (1 + ξ)))) (𝓝[<] (1 - ξ)) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * (1 - ξ - x) / ((1 - ξ) * (1 + ξ))) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b41 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_ty_42 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ ^ 2 * (1 - ξ - x) / (ξ * x + (1 - ξ)))) (𝓝[<] (1 - ξ)) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ ^ 2 * (1 - ξ - x) / (ξ * x + (1 - ξ))) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b42 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_ty_43 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2))) (𝓝[<] (1 -
        ξ)) (𝓝 (Li₃ (ξ / (1 + ξ)))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2)) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := ξ / (1 + ξ))
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by have := div_pos h0 h1p; linarith, by rw [div_le_one h1p]; linarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b43 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_44 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2))) (𝓝[<] (1 -
        ξ)) (𝓝 (Li₃ (1 - ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2)) (p := (1 - ξ)) (l :=
      𝓝[<] (1 - ξ)) (a := 1 - ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by linarith, by linarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b44 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_45 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - ξ - x) / ((1 - ξ) * (1 + ξ) * (1 - x)))) (𝓝[<] (1 -
        ξ)) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - ξ - x) / ((1 - ξ) * (1 + ξ) * (1 - x))) (p :=
      (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b45 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_ty_46 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ))))) (𝓝[<] (1 -
        ξ)) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ)))) (p :=
      (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b46 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_ty_47 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x)))) (𝓝[<] (1 -
        ξ)) (𝓝 (zeta3)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x))) (p :=
      (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by simp only [sub_sub_cancel]; field_simp; ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b47 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_ty_48 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) (𝓝[<] (1 -
        ξ)) (𝓝 (zeta3)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) (p :=
      (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b48 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_ty_49 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (-(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))) (𝓝[<] (1 -
        ξ)) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => -(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) (p :=
      (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b49 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_ty_50 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) (𝓝[<] (1 -
        ξ)) (𝓝 (Li₃ (ξ / (1 + ξ)))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) (p :=
      (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := ξ / (1 + ξ))
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by have := div_pos h0 h1p; linarith, by rw [div_le_one h1p]; linarith⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b50 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_ty_51 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 + ξ) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)))) (𝓝[<] (1 -
        ξ)) (𝓝 (zeta3)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 + ξ) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))) (p :=
      (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b51 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_ty_52 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * (ξ * x ^ 2 + (1 - ξ) ^ 2) / ((1 - ξ) * (ξ * x + (1 - ξ)) *
        (1 - x)))) (𝓝[<] (1 - ξ)) (𝓝 (zeta3)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * (ξ * x ^ 2 + (1 - ξ) ^ 2) / ((1 - ξ) *
      (ξ * x + (1 - ξ)) * (1 - x))) (p := (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by simp only [sub_sub_cancel]; field_simp) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b52 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_ty_53 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((ξ * x + (1 - ξ)) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))
        (𝓝[<] (1 - ξ)) (𝓝 (zeta3)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (ξ * x + (1 - ξ)) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 +
      (1 - ξ) ^ 2)) (p := (1 - ξ)) (l := 𝓝[<] (1 - ξ)) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_evy hξ).mono fun x hx => i5C1E_b53 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_dy_9 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun x => Li₂ (x)) (1 - ξ) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hg : DifferentiableAt ℝ (fun x => x) (1 - ξ) := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have hv : |(1 - ξ)| < 1 := by
    rw [abs_of_pos hy]; linarith
  exact (hasDerivAt_Li₂_tsum hv).differentiableAt.comp (1 - ξ) hg

theorem i5C1E_dy_12 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun x => Li₂ (ξ * (1 - x))) (1 - ξ) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hg : DifferentiableAt ℝ (fun x => ξ * (1 - x)) (1 - ξ) := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have hv : |ξ * (1 - (1 - ξ))| < 1 := by
    rw [show ξ * (1 - (1 - ξ)) = ξ ^ 2 by ring]
    rw [abs_of_pos (by positivity)]; nlinarith
  exact (hasDerivAt_Li₂_tsum hv).differentiableAt.comp (1 - ξ) hg

theorem i5C1E_dy_13 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun x => Li₂ (-(ξ * x / (1 - ξ)))) (1 - ξ) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hg : DifferentiableAt ℝ (fun x => -(ξ * x / (1 - ξ))) (1 - ξ) := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have hv : |-(ξ * (1 - ξ) / (1 - ξ))| < 1 := by
    rw [show -(ξ * (1 - ξ) / (1 - ξ)) = -ξ by field_simp]
    rw [abs_neg, abs_of_pos h0]; exact h1
  exact (hasDerivAt_Li₂_tsum hv).differentiableAt.comp (1 - ξ) hg

theorem i5C1E_dy_14 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun x => Li₂ (x / (ξ * x + (1 - ξ)))) (1 - ξ) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hg : DifferentiableAt ℝ (fun x => x / (ξ * x + (1 - ξ))) (1 - ξ) := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have hv : |(1 - ξ) / (ξ * (1 - ξ) + (1 - ξ))| < 1 := by
    rw [show (1 - ξ) / (ξ * (1 - ξ) + (1 - ξ)) = 1 / (1 + ξ) by field_simp; ring]
    rw [abs_of_pos (by positivity), div_lt_one h1p]; linarith
  exact (hasDerivAt_Li₂_tsum hv).differentiableAt.comp (1 - ξ) hg

theorem i5C1E_dy_19 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun x => Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) (1 - ξ) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hg : DifferentiableAt ℝ (fun x => ξ * (1 - ξ) / (ξ * x + (1 - ξ))) (1 - ξ) := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have hv : |ξ * (1 - ξ) / (ξ * (1 - ξ) + (1 - ξ))| < 1 := by
    rw [show ξ * (1 - ξ) / (ξ * (1 - ξ) + (1 - ξ)) = ξ / (1 + ξ) by field_simp; ring]
    rw [abs_of_pos (by positivity), div_lt_one h1p]; linarith
  exact (hasDerivAt_Li₂_tsum hv).differentiableAt.comp (1 - ξ) hg

end QED.ThreeLoopD
