/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Bnd
public import QED.Polylog.ExtraIntegrals

/-!
# Set (d), master `I₅`: the atoms of the primitive at `x = 0`

The primitive `QED.ThreeLoopD.i5C1PB` of `I(x)` is a polynomial in logarithms of the letters,
dilogarithms and trilogarithms ("atoms"). Each atom other than `log x` has a limit as `x → 0⁺`,
stated in the normal form in `log ξ`, `log (1 - ξ)`, `log (1 + ξ)`, `Li₂ (±ξ)`, `π` and the
trilogarithms at `ξ, -ξ, 1 - ξ, ξ/(1+ξ), 1/(1+ξ), 1 - ξ², ξ²` and `1`
(`QED.ThreeLoopD.i5C1E_t0_1`, ...). The dilogarithms in the coefficients of `log x` are
differentiable at `0` (`QED.ThreeLoopD.i5C1E_d0_10`, ...).

## Main results

* `QED.ThreeLoopD.i5C1E_tLi₂`, `QED.ThreeLoopD.i5C1E_tLi₃`, `QED.ThreeLoopD.i5C1E_tlog`: limits
  of `Li₂ ∘ g`, `Li₃ ∘ g`, `log ∘ g` from continuity of `g` and the bound `|g| < 1`.
* `QED.ThreeLoopD.i5C1E_t0_1`, ..., `QED.ThreeLoopD.i5C1E_t0_53`.
-/

@[expose] public section

open Set Real Filter Topology QED.Polylog

namespace QED.ThreeLoopD

theorem i5C1E_ev0 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : ∀ᶠ x in 𝓝[>] 0, x ∈ Ioo 0 (1 - ξ) :=
  Ioo_mem_nhdsGT (by linarith [hξ.2])

theorem i5C1E_evy {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ x in 𝓝[<] (1 - ξ), x ∈ Ioo 0 (1 - ξ) :=
  Ioo_mem_nhdsLT (by linarith [hξ.2])

/-- `Li₂ (g x) → Li₂ a` along `l ≤ 𝓝 p` when `g` is continuous at `p`, `g p = a ∈ [-1, 1]` and
eventually `|g x| < 1`. -/
theorem i5C1E_tLi₂ {g : ℝ → ℝ} {p a : ℝ} {l : Filter ℝ} (hg : ContinuousAt g p) (hp : g p = a)
    (ha : a ∈ Icc (-1 : ℝ) 1) (hb : ∀ᶠ x in l, |g x| < 1) (hl : l ≤ 𝓝 p) :
    Tendsto (fun x => Li₂ (g x)) l (𝓝 (Li₂ a)) :=
  tendsto_Li₂_comp ha (by rw [← hp]; exact hg.tendsto.mono_left hl)
    (hb.mono fun _ hx => ⟨(abs_lt.mp hx).1.le, (abs_lt.mp hx).2.le⟩)

/-- `Li₃ (g x) → Li₃ a` along `l ≤ 𝓝 p` when `g` is continuous at `p`, `g p = a ∈ [-1, 1]` and
eventually `|g x| < 1`. -/
theorem i5C1E_tLi₃ {g : ℝ → ℝ} {p a : ℝ} {l : Filter ℝ} (hg : ContinuousAt g p) (hp : g p = a)
    (ha : a ∈ Icc (-1 : ℝ) 1) (hb : ∀ᶠ x in l, |g x| < 1) (hl : l ≤ 𝓝 p) :
    Tendsto (fun x => Li₃ (g x)) l (𝓝 (Li₃ a)) :=
  tendsto_Li₃_comp ha (by rw [← hp]; exact hg.tendsto.mono_left hl)
    (hb.mono fun _ hx => ⟨(abs_lt.mp hx).1.le, (abs_lt.mp hx).2.le⟩)

/-- `log (g x) → log a` along `l ≤ 𝓝 p` when `g` is continuous at `p` and `g p = a ≠ 0`. -/
theorem i5C1E_tlog {g : ℝ → ℝ} {p a : ℝ} {l : Filter ℝ} (hg : ContinuousAt g p) (hp : g p = a)
    (ha : a ≠ 0) (hl : l ≤ 𝓝 p) : Tendsto (fun x => log (g x)) l (𝓝 (log a)) := by
  rw [← hp] at ha ⊢
  exact (hg.log ha).tendsto.mono_left hl

theorem i5C1E_t0_1 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => log (ξ * x + (1 - ξ))) (𝓝[>] 0) (𝓝 (log (1 - ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tlog (g := fun x => ξ * x + (1 - ξ)) (p := 0) (l := 𝓝[>] 0) (a := 1 -
      ξ) (by fun_prop) (by ring)
    (by positivity) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_3 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => log (1 - ξ - x)) (𝓝[>] 0) (𝓝 (log (1 - ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tlog (g := fun x => 1 - ξ - x) (p := 0) (l := 𝓝[>] 0) (a := 1 -
      ξ) (by fun_prop) (by ring)
    (by positivity) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_5 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => log (1 - x)) (𝓝[>] 0) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tlog (g := fun x => 1 - x) (p := 0) (l := 𝓝[>] 0) (a := 1) (by fun_prop) (by ring)
    (by positivity) nhdsWithin_le_nhds
  rw [log_one] at h
  exact h

theorem i5C1E_t0_6 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => log (ξ * x ^ 2 + (1 - ξ) ^ 2)) (𝓝[>] 0) (𝓝 (2 * log (1 - ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tlog (g := fun x => ξ * x ^ 2 + (1 - ξ) ^ 2) (p := 0) (l := 𝓝[>] 0) (a :=
      (1 - ξ) ^ 2) (by fun_prop) (by ring)
    (by positivity) nhdsWithin_le_nhds
  rw [log_pow] at h
  push_cast at h
  exact h

theorem i5C1E_t0_7 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => log (ξ * x + (1 - ξ) ^ 2)) (𝓝[>] 0) (𝓝 (2 * log (1 - ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tlog (g := fun x => ξ * x + (1 - ξ) ^ 2) (p := 0) (l := 𝓝[>] 0) (a :=
      (1 - ξ) ^ 2) (by fun_prop) (by ring)
    (by positivity) nhdsWithin_le_nhds
  rw [log_pow] at h
  push_cast at h
  exact h

theorem i5C1E_t0_9 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (x)) (𝓝[>] 0) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => x) (p := 0) (l := 𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b9 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₂_zero] at h
  exact h

theorem i5C1E_t0_10 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (x / (1 - ξ))) (𝓝[>] 0) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => x / (1 - ξ)) (p := 0) (l := 𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b10 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₂_zero] at h
  exact h

theorem i5C1E_t0_11 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (ξ / (1 - x))) (𝓝[>] 0) (𝓝 (Li₂ ξ)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => ξ / (1 - x)) (p := 0) (l := 𝓝[>] 0) (a := ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b11 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_12 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (ξ * (1 - x))) (𝓝[>] 0) (𝓝 (Li₂ ξ)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => ξ * (1 - x)) (p := 0) (l := 𝓝[>] 0) (a := ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b12 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_13 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (-(ξ * x / (1 - ξ)))) (𝓝[>] 0) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => -(ξ * x / (1 - ξ))) (p := 0) (l := 𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b13 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₂_zero] at h
  exact h

theorem i5C1E_t0_14 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (x / (ξ * x + (1 - ξ)))) (𝓝[>] 0) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => x / (ξ * x + (1 - ξ))) (p := 0) (l := 𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b14 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₂_zero] at h
  exact h

theorem i5C1E_t0_15 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) (𝓝[>] 0) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => -(ξ * x ^ 2 / (1 - ξ) ^ 2)) (p := 0) (l := 𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b15 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₂_zero] at h
  exact h

theorem i5C1E_t0_16 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (ξ * (1 - ξ - x) / (1 - ξ))) (𝓝[>] 0) (𝓝 (Li₂ ξ)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => ξ * (1 - ξ - x) / (1 - ξ)) (p := 0) (l := 𝓝[>] 0) (a := ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b16 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_17 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ)))) (𝓝[>] 0) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => (1 + ξ) * x / (ξ * x + (1 - ξ))) (p := 0) (l :=
      𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b17 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₂_zero] at h
  exact h

theorem i5C1E_t0_18 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (x / (ξ * x + (1 - ξ) ^ 2))) (𝓝[>] 0) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => x / (ξ * x + (1 - ξ) ^ 2)) (p := 0) (l := 𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b18 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₂_zero] at h
  exact h

theorem i5C1E_t0_19 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) (𝓝[>] 0) (𝓝 (Li₂ ξ)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => ξ * (1 - ξ) / (ξ * x + (1 - ξ))) (p := 0) (l :=
      𝓝[>] 0) (a := ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b19 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_20 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))))) (𝓝[>] 0) (𝓝 (Li₂ (-ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => -(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) (p := 0) (l :=
      𝓝[>] 0) (a := -ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b20 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_21 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))) (𝓝[>] 0) (𝓝 (Li₂ (-ξ)))
        := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₂ (g := fun x => -(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) (p :=
      0) (l := 𝓝[>] 0) (a := -ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b21 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_22 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - x))) (𝓝[>] 0) (𝓝 (zeta3)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - x)) (p := 0) (l := 𝓝[>] 0) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b22 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_t0_23 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (x / (1 - ξ))) (𝓝[>] 0) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => x / (1 - ξ)) (p := 0) (l := 𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b23 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_t0_24 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ / (1 - x))) (𝓝[>] 0) (𝓝 (Li₃ ξ)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ / (1 - x)) (p := 0) (l := 𝓝[>] 0) (a := ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b24 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_25 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * (1 - x))) (𝓝[>] 0) (𝓝 (Li₃ ξ)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * (1 - x)) (p := 0) (l := 𝓝[>] 0) (a := ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b25 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_26 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (-(ξ * x / (1 - ξ)))) (𝓝[>] 0) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => -(ξ * x / (1 - ξ))) (p := 0) (l := 𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b26 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_t0_27 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((ξ * x + (1 - ξ)))) (𝓝[>] 0) (𝓝 (Li₃ (1 - ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (ξ * x + (1 - ξ))) (p := 0) (l := 𝓝[>] 0) (a := 1 - ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b27 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_28 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - ξ - x) / (1 - x))) (𝓝[>] 0) (𝓝 (Li₃ (1 - ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - ξ - x) / (1 - x)) (p := 0) (l := 𝓝[>] 0) (a := 1 - ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b28 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_29 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) (𝓝[>] 0) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => -(ξ * x ^ 2 / (1 - ξ) ^ 2)) (p := 0) (l := 𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b29 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_t0_30 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - ξ - x) / (1 - ξ))) (𝓝[>] 0) (𝓝 (zeta3)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - ξ - x) / (1 - ξ)) (p := 0) (l := 𝓝[>] 0) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b30 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_t0_31 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * (1 - ξ - x) / (1 - ξ))) (𝓝[>] 0) (𝓝 (Li₃ ξ)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * (1 - ξ - x) / (1 - ξ)) (p := 0) (l := 𝓝[>] 0) (a := ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b31 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_32 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 + ξ) * x / (ξ * x + (1 - ξ)))) (𝓝[>] 0) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 + ξ) * x / (ξ * x + (1 - ξ))) (p := 0) (l :=
      𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b32 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_t0_33 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) (𝓝[>] 0) (𝓝 (Li₃ ξ)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * (1 - ξ) / (ξ * x + (1 - ξ))) (p := 0) (l :=
      𝓝[>] 0) (a := ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b33 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_34 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - ξ - x) / (ξ * x + (1 - ξ)))) (𝓝[>] 0) (𝓝 (zeta3)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - ξ - x) / (ξ * x + (1 - ξ))) (p := 0) (l :=
      𝓝[>] 0) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b34 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_t0_35 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))))) (𝓝[>] 0) (𝓝 (Li₃ (-ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => -(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) (p := 0) (l :=
      𝓝[>] 0) (a := -ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b35 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_36 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - ξ) * (1 - x) / (ξ * x + (1 - ξ)))) (𝓝[>] 0) (𝓝 (zeta3)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - ξ) * (1 - x) / (ξ * x + (1 - ξ))) (p := 0) (l :=
      𝓝[>] 0) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b36 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_t0_37 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((ξ * x + (1 - ξ) ^ 2) / (1 - ξ))) (𝓝[>] 0) (𝓝 (Li₃ (1 - ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (ξ * x + (1 - ξ) ^ 2) / (1 - ξ)) (p := 0) (l := 𝓝[>] 0) (a :=
      1 - ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b37 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_38 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)))) (𝓝[>] 0) (𝓝 (Li₃ (1 - ξ)))
        := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))) (p := 0) (l :=
      𝓝[>] 0) (a := 1 - ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b38 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_39 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2))) (𝓝[>] 0) (𝓝 (zeta3))
        := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2)) (p :=
      0) (l := 𝓝[>] 0) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b39 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_t0_40 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * x / (ξ * x + (1 - ξ)))) (𝓝[>] 0) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * x / (ξ * x + (1 - ξ))) (p := 0) (l := 𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b40 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_t0_41 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * (1 - ξ - x) / ((1 - ξ) * (1 + ξ)))) (𝓝[>] 0) (𝓝 (Li₃ (ξ / (1 + ξ))))
        := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * (1 - ξ - x) / ((1 - ξ) * (1 + ξ))) (p := 0) (l :=
      𝓝[>] 0) (a := ξ / (1 + ξ))
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by have := div_pos h0 h1p; linarith, by rw [div_le_one h1p]; linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b41 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_42 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ ^ 2 * (1 - ξ - x) / (ξ * x + (1 - ξ)))) (𝓝[>] 0) (𝓝 (Li₃ (ξ ^ 2)))
        := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ ^ 2 * (1 - ξ - x) / (ξ * x + (1 - ξ))) (p := 0) (l :=
      𝓝[>] 0) (a := ξ ^ 2)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by nlinarith, by nlinarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b42 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_43 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2))) (𝓝[>] 0) (𝓝 (0)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2)) (p := 0) (l :=
      𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b43 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_t0_44 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2))) (𝓝[>] 0) (𝓝 (zeta3)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2)) (p := 0) (l :=
      𝓝[>] 0) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b44 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_t0_45 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - ξ - x) / ((1 - ξ) * (1 + ξ) * (1 - x)))) (𝓝[>] 0)
        (𝓝 (Li₃ (1 / (1 + ξ)))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - ξ - x) / ((1 - ξ) * (1 + ξ) * (1 - x))) (p := 0) (l :=
      𝓝[>] 0) (a := 1 / (1 + ξ))
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by have := div_pos one_pos h1p; linarith,
        by rw [div_le_one h1p]; linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b45 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_46 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ))))) (𝓝[>] 0) (𝓝 (0))
        := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ)))) (p :=
      0) (l := 𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b46 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_t0_47 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x)))) (𝓝[>] 0)
        (𝓝 (Li₃ (ξ / (1 + ξ)))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x))) (p :=
      0) (l := 𝓝[>] 0) (a := ξ / (1 + ξ))
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by have := div_pos h0 h1p; linarith, by rw [div_le_one h1p]; linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b47 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_48 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) (𝓝[>] 0) (𝓝 (0))
        := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) (p :=
      0) (l := 𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b48 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_t0_49 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (-(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))) (𝓝[>] 0) (𝓝 (0))
        := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => -(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) (p :=
      0) (l := 𝓝[>] 0) (a := 0)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b49 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_zero] at h
  exact h

theorem i5C1E_t0_50 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) (𝓝[>] 0) (𝓝 (zeta3))
        := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) (p :=
      0) (l := 𝓝[>] 0) (a := 1)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by norm_num, by norm_num⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b50 hξ hx.1 hx.2) nhdsWithin_le_nhds
  rw [Li₃_one] at h
  exact h

theorem i5C1E_t0_51 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((1 + ξ) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)))) (𝓝[>] 0)
        (𝓝 (Li₃ (1 - ξ ^ 2))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (1 + ξ) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))) (p :=
      0) (l := 𝓝[>] 0) (a := 1 - ξ ^ 2)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by nlinarith, by nlinarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b51 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_52 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ (ξ * (ξ * x ^ 2 + (1 - ξ) ^ 2) / ((1 - ξ) * (ξ * x + (1 - ξ)) *
        (1 - x)))) (𝓝[>] 0) (𝓝 (Li₃ ξ)) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => ξ * (ξ * x ^ 2 + (1 - ξ) ^ 2) / ((1 - ξ) *
      (ξ * x + (1 - ξ)) * (1 - x))) (p := 0) (l := 𝓝[>] 0) (a := ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b52 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_t0_53 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Li₃ ((ξ * x + (1 - ξ)) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))
        (𝓝[>] 0) (𝓝 (Li₃ (1 - ξ))) := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have h := i5C1E_tLi₃ (g := fun x => (ξ * x + (1 - ξ)) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 +
      (1 - ξ) ^ 2)) (p := 0) (l := 𝓝[>] 0) (a := 1 - ξ)
    (by fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity)))
    (by field_simp; ring) ⟨by linarith, by linarith⟩
    ((i5C1E_ev0 hξ).mono fun x hx => i5C1E_b53 hξ hx.1 hx.2) nhdsWithin_le_nhds
  exact h

theorem i5C1E_d0_10 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun x => Li₂ (x / (1 - ξ))) 0 := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hg : DifferentiableAt ℝ (fun x => x / (1 - ξ)) 0 := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have hv : |0 / (1 - ξ)| < 1 := by
    rw [show 0 / (1 - ξ) = 0 by ring]
    norm_num
  exact (hasDerivAt_Li₂_tsum hv).differentiableAt.comp 0 hg

theorem i5C1E_d0_15 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun x => Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) 0 := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hg : DifferentiableAt ℝ (fun x => -(ξ * x ^ 2 / (1 - ξ) ^ 2)) 0 := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have hv : |-(ξ * 0 ^ 2 / (1 - ξ) ^ 2)| < 1 := by
    rw [show -(ξ * 0 ^ 2 / (1 - ξ) ^ 2) = 0 by ring]
    norm_num
  exact (hasDerivAt_Li₂_tsum hv).differentiableAt.comp 0 hg

theorem i5C1E_d0_17 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun x => Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ)))) 0 := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hg : DifferentiableAt ℝ (fun x => (1 + ξ) * x / (ξ * x + (1 - ξ))) 0 := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have hv : |(1 + ξ) * 0 / (ξ * 0 + (1 - ξ))| < 1 := by
    rw [show (1 + ξ) * 0 / (ξ * 0 + (1 - ξ)) = 0 by ring]
    norm_num
  exact (hasDerivAt_Li₂_tsum hv).differentiableAt.comp 0 hg

theorem i5C1E_d0_20 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun x => Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))))) 0 := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hg : DifferentiableAt ℝ (fun x => -(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) 0 := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have hv : |-(ξ * (1 - ξ - 0) / (ξ * 0 + (1 - ξ)))| < 1 := by
    rw [show -(ξ * (1 - ξ - 0) / (ξ * 0 + (1 - ξ))) = -ξ by field_simp; ring]
    rw [abs_neg, abs_of_pos h0]; exact h1
  exact (hasDerivAt_Li₂_tsum hv).differentiableAt.comp 0 hg

theorem i5C1E_d0_21 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun x => Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))) 0 := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hg : DifferentiableAt ℝ (fun x => -(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) 0 := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have hv : |-(ξ * (1 - ξ - 0) ^ 2 / (ξ * 0 + (1 - ξ)) ^ 2)| < 1 := by
    rw [show -(ξ * (1 - ξ - 0) ^ 2 / (ξ * 0 + (1 - ξ)) ^ 2) = -ξ by field_simp; ring]
    rw [abs_neg, abs_of_pos h0]; exact h1
  exact (hasDerivAt_Li₂_tsum hv).differentiableAt.comp 0 hg

end QED.ThreeLoopD
