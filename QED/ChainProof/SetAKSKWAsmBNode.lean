/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWAsmBGen
public import QED.ChainProof.SetAKSKWAsmDef
public import QED.ChainProof.SetAKSKUVBRem

/-!
# Set (a), stage D: the `VB` finite part at a fixed node in the spectral variables

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. At unit
mass and a node `(ρ, β, w)` of the open cube, write `a = w(1-w)`, `b = β(1-β)`,
`Y = ksDYmax β w`, and the three thresholds

  `q = 1/a` (`A_w = 0`), `r = 1/b` (`A_β = 0`), `p = (l r + q)/(1 + l)` (`D = 0`),

`l = ρYb/((1-ρ)a)`. Then `A_w = 1 + σ/q`, `A_β = 1 + σ/r`, `D = D₀(1 + σ/p)`,
`D₀ = 1 - ρ + ρY`, and the argument of `K` is `z(σ) = l(r + σ)/(q + σ)`. In these variables
the finite part `ksUb0 1 σ ρ β w` is a combination of the nodes `log(1 + σ/x)`,
`log²(1 + σ/x)`, `(G₀(σ)/A_β) log(1 + z)` and `K(z)` (`ksWB_ksUb0_eq`).
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetAKS

/-- The threshold `q = 1/(w(1-w))` of `A_w`. -/
noncomputable def ksWBq (w : ℝ) : ℝ := (w * (1 - w))⁻¹

/-- The threshold `r = 1/(β(1-β))` of `A_β`. -/
noncomputable def ksWBr (β : ℝ) : ℝ := (β * (1 - β))⁻¹

/-- The ratio `l = ρYb/((1-ρ)a)`. -/
noncomputable def ksWBl (ρ β w : ℝ) : ℝ :=
  ρ * ksDYmax β w * (β * (1 - β)) / ((1 - ρ) * (w * (1 - w)))

/-- The threshold `p = (l r + q)/(1 + l)` of `D`. -/
noncomputable def ksWBp (ρ β w : ℝ) : ℝ :=
  (ksWBl ρ β w * ksWBr β + ksWBq w) / (1 + ksWBl ρ β w)

/-- `D₀ = 1 - ρ + ρY`. -/
noncomputable def ksWBD0 (ρ β w : ℝ) : ℝ := 1 - ρ + ρ * ksDYmax β w

/-- `G₀(σ) = g₀ + g₁σ`: the constant term. -/
noncomputable def ksWBg0 (ρ β w : ℝ) : ℝ :=
  ksDEc 1 (ksUPtB ρ β) w 0 - ksDHc (ksUPtB ρ β) w 0 / 2

/-- `G₀(σ) = g₀ + g₁σ`: the slope. -/
noncomputable def ksWBg1 (ρ β w : ℝ) : ℝ := -(ksDHc (ksUPtB ρ β) w 0 * (w * (1 - w)) / 2)

section Node

variable {ρ β w : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1)
include hρ hβ hw

theorem ksWB_basic :
    0 < ksWBq w ∧ 4 ≤ ksWBq w ∧ 0 < ksWBr β ∧ 4 ≤ ksWBr β ∧ 0 < ksWBl ρ β w ∧
      0 < ksDYmax β w ∧ ksDYmax β w ≤ 1 ∧ 0 < ksWBD0 ρ β w := by
  have ha : 0 < w * (1 - w) := mul_pos hw.1 (by linarith [hw.2])
  have hb : 0 < β * (1 - β) := mul_pos hβ.1 (by linarith [hβ.2])
  have ha4 : w * (1 - w) ≤ 1 / 4 := by nlinarith [sq_nonneg (w - 1 / 2)]
  have hb4 : β * (1 - β) ≤ 1 / 4 := by nlinarith [sq_nonneg (β - 1 / 2)]
  have hY := ksU_ksDYmax_pos hβ hw
  have hY1 := ksU_ksDYmax_le_one (w := w) hβ
  have h1 : 0 < 1 - ρ := by linarith [hρ.2]
  refine ⟨inv_pos.2 ha, ?_, inv_pos.2 hb, ?_, ?_, hY, hY1, ?_⟩
  · rw [ksWBq, le_inv_comm₀ (by norm_num) ha]; linarith
  · rw [ksWBr, le_inv_comm₀ (by norm_num) hb]; linarith
  · unfold ksWBl; have := hρ.1; positivity
  · unfold ksWBD0; have := hρ.1; nlinarith

/-- **The finite part of `VB` in the spectral variables** (unit mass, `σ > -4`). -/
theorem ksWB_ksUb0_eq {σ : ℝ} (hσ : -4 < σ) :
    ksUb0 1 σ ρ β w =
      (ksWBg0 ρ β w + ksWBg1 ρ β w * σ) / ρ * (ksWBr β / (ksWBr β + σ)) *
          log (1 + ksWBl ρ β w * (ksWBr β + σ) / (ksWBq w + σ)) +
        ksUq ρ β w * ksDYmax β w / 2 *
          (log ((1 - ρ) * ksDYmax β w / (ρ * ksWBD0 ρ β w)) - log (1 + σ / ksWBp ρ β w)) +
        (1 - ρ)⁻¹ * ksUf0 β w * (log (ksDYmax β w / (ρ * ksWBD0 ρ β w)) +
          log (1 + σ / ksWBr β) - log (1 + σ / ksWBp ρ β w)) +
        ρ * ksUcB w * ((log (ksDYmax β w / ρ) - log (1 + σ / ksWBq w)) ^ 2 / 2 + 2 * ksUK 1 -
          ksUK (ksWBl ρ β w * (ksWBr β + σ) / (ksWBq w + σ))) +
        ksUf0 β w * (log (1 + σ / ksWBr β) ^ 2 / 2 + 2 * ksUK 1) := by
  obtain ⟨hq0, hq4, hr0, hr4, hl0, hY, hY1, hD0⟩ := ksWB_basic hρ hβ hw
  have hρ0 := hρ.1
  have h1 : 0 < 1 - ρ := by linarith [hρ.2]
  have ha : 0 < w * (1 - w) := mul_pos hw.1 (by linarith [hw.2])
  have hb : 0 < β * (1 - β) := mul_pos hβ.1 (by linarith [hβ.2])
  have hσ' : -(4 * (1 : ℝ) ^ 2) < σ := by norm_num; linarith
  have hAw := ksD_ksDA_pos one_pos hσ' (Ioo_subset_Icc_self hw)
  have hAb := ksD_ksDA_pos one_pos hσ' (Ioo_subset_Icc_self hβ)
  set Y := ksDYmax β w with hYdef
  set Aw := ksDA 1 σ w with hAwdef
  set Ab := ksDA 1 σ β with hAbdef
  have eAw : 1 + σ / ksWBq w = Aw := by
    simp only [hAwdef, ksDA, ksWBq, div_inv_eq_mul]; ring
  have eAb : 1 + σ / ksWBr β = Ab := by
    simp only [hAbdef, ksDA, ksWBr, div_inv_eq_mul]; ring
  have hD0' : 1 - ρ + ρ * Y ≠ 0 := hD0.ne'
  have h1' : 1 - ρ ≠ 0 := h1.ne'
  have eD : ksWBD0 ρ β w * (1 + σ / ksWBp ρ β w) = (1 - ρ) * Aw + ρ * Ab * Y := by
    simp only [ksWBD0, ksWBp, ksWBl, ksWBq, ksWBr, hAwdef, hAbdef, ksDA, ← hYdef]
    generalize w * (1 - w) = a at *
    generalize β * (1 - β) = b at *
    field_simp
    ring
  have ez : ksWBl ρ β w * (ksWBr β + σ) / (ksWBq w + σ) = ρ * Ab * Y / ((1 - ρ) * Aw) := by
    simp only [ksWBl, ksWBq, ksWBr, hAwdef, hAbdef, ksDA, ← hYdef]
    generalize w * (1 - w) = a at *
    generalize β * (1 - β) = b at *
    field_simp
  have er : ksWBr β / (ksWBr β + σ) = Ab⁻¹ := by
    rw [← eAb]; field_simp
  have hDpos : 0 < (1 - ρ) * Aw + ρ * Ab * Y := by positivity
  have hp1 : 0 < 1 + σ / ksWBp ρ β w := by
    have := eD ▸ hDpos
    exact pos_of_mul_pos_right this hD0.le
  have hb₀ : ksDbB 1 0 (ksUPtB ρ β) σ = ρ * Ab / (1 - ρ) := ksU_ksDbB_zero_ptB hρ
  have hG : ksUG0 1 σ ρ β w = ksWBg0 ρ β w + ksWBg1 ρ β w * σ := by
    simp only [ksUG0, ksUGc, ksWBg0, ksWBg1, ksDA, Fin.val_zero, Nat.cast_zero]
    ring
  have hYρD : 0 < ρ * ksWBD0 ρ β w := mul_pos hρ0 hD0
  have L1 : log ((Aw + ρ * Ab / (1 - ρ) * Y) / Aw) =
      log (1 + ksWBl ρ β w * (ksWBr β + σ) / (ksWBq w + σ)) := by
    rw [ez]; congr 1; field_simp
  have L2 : log ((1 - ρ) * (Y / (ρ * ((1 - ρ) * Aw + ρ * Ab * Y)))) =
      log ((1 - ρ) * Y / (ρ * ksWBD0 ρ β w)) - log (1 + σ / ksWBp ρ β w) := by
    rw [← eD, ← log_div (by positivity) hp1.ne']
    congr 1
    field_simp
  have L3 : log ((1 - ρ) * (Y / (ρ * ((1 - ρ) * Aw + ρ * Ab * Y))) / ((1 - ρ) / Ab)) =
      log (Y / (ρ * ksWBD0 ρ β w)) + log (1 + σ / ksWBr β) - log (1 + σ / ksWBp ρ β w) := by
    rw [← eD, eAb, ← log_mul (by positivity) hAb.ne', ← log_div (by positivity) hp1.ne']
    congr 1
    field_simp
  have L4 : log (Y / (ρ * Aw)) = log (Y / ρ) - log (1 + σ / ksWBq w) := by
    rw [eAw, ← log_div (by positivity) hAw.ne']
    congr 1
    field_simp
  have L5 : ρ * Ab / (1 - ρ) * Y / Aw = ksWBl ρ β w * (ksWBr β + σ) / (ksWBq w + σ) := by
    rw [ez]; field_simp
  have L6 : log Ab⁻¹ ^ 2 = log (1 + σ / ksWBr β) ^ 2 := by rw [log_inv, neg_sq, eAb]
  rw [ksUb0, ksUl3, hb₀, hG]
  simp only [ksDJ1, ksUR, ← hYdef, ← hAwdef, ← hAbdef]
  rw [L1, L2, L3, L4, L5, L6, er]
  field_simp

omit hρ hβ hw in
theorem ksWB_ksDA_w (σ : ℝ) : ksDA 1 σ w = 1 + σ / ksWBq w := by
  simp only [ksDA, ksWBq, div_inv_eq_mul]; ring

omit hρ hβ hw in
theorem ksWB_ksDA_β (σ : ℝ) : ksDA 1 σ β = 1 + σ / ksWBr β := by
  simp only [ksDA, ksWBr, div_inv_eq_mul]; ring

theorem ksWB_D_eq (σ : ℝ) :
    (1 - ρ) * ksDA 1 σ w + ρ * ksDYmax β w * ksDA 1 σ β =
      ksWBD0 ρ β w * (1 + σ / ksWBp ρ β w) := by
  obtain ⟨-, -, -, -, hl0, hY, -, hD0⟩ := ksWB_basic hρ hβ hw
  have h1 : 1 - ρ ≠ 0 := by linarith [hρ.2]
  have ha : 0 < w * (1 - w) := mul_pos hw.1 (by linarith [hw.2])
  have hb : 0 < β * (1 - β) := mul_pos hβ.1 (by linarith [hβ.2])
  have hD0' : 1 - ρ + ρ * ksDYmax β w ≠ 0 := hD0.ne'
  have hX : (1 - ρ) * (w * (1 - w)) + ρ * ksDYmax β w * (β * (1 - β)) ≠ 0 := by
    have := hρ.1; have : 0 < 1 - ρ := by linarith [hρ.2]
    positivity
  simp only [ksWBD0, ksWBp, ksWBl, ksWBq, ksWBr, ksDA]
  generalize w * (1 - w) = a at *
  generalize β * (1 - β) = b at *
  have hu := inv_mul_cancel₀ hD0'
  field_simp
  linear_combination (-(σ * ((1 - ρ) * a + ρ * ksDYmax β w * b))) * hu

omit hρ hβ hw in
theorem ksWB_ksUG0 (σ : ℝ) : ksUG0 1 σ ρ β w = ksWBg0 ρ β w + ksWBg1 ρ β w * σ := by
  simp only [ksUG0, ksUGc, ksWBg0, ksWBg1, ksDA, Fin.val_zero, Nat.cast_zero]
  ring

theorem ksWB_z_eq {σ : ℝ} (hσ : ksWBq w + σ ≠ 0) :
    ρ * ksDYmax β w * ksDA 1 σ β / ((1 - ρ) * ksDA 1 σ w) =
      ksWBl ρ β w * (ksWBr β + σ) / (ksWBq w + σ) := by
  have h1 : 1 - ρ ≠ 0 := by linarith [hρ.2]
  have ha : 0 < w * (1 - w) := mul_pos hw.1 (by linarith [hw.2])
  have hb : 0 < β * (1 - β) := mul_pos hβ.1 (by linarith [hβ.2])
  have hA : ksDA 1 σ w ≠ 0 := by
    have hqne : ksWBq w ≠ 0 := (inv_pos.2 ha).ne'
    rw [ksWB_ksDA_w, show 1 + σ / ksWBq w = (ksWBq w + σ) / ksWBq w by
      rw [add_div, div_self hqne]]
    exact div_ne_zero hσ hqne
  rw [ksWB_ksDA_w] at hA ⊢
  rw [ksWB_ksDA_β]
  simp only [ksWBl, ksWBq, ksWBr] at hA hσ ⊢
  generalize w * (1 - w) = a at *
  generalize β * (1 - β) = b at *
  field_simp

theorem ksWB_p_pos : 0 < ksWBp ρ β w := by
  obtain ⟨hq0, -, hr0, -, hl0, -⟩ := ksWB_basic hρ hβ hw
  unfold ksWBp
  positivity

theorem ksWB_p_sub :
    ksWBp ρ β w - ksWBq w = ksWBl ρ β w * (ksWBr β - ksWBq w) / (1 + ksWBl ρ β w) ∧
      ksWBp ρ β w - ksWBr β = (ksWBq w - ksWBr β) / (1 + ksWBl ρ β w) := by
  obtain ⟨-, -, -, -, hl0, -⟩ := ksWB_basic hρ hβ hw
  have : 1 + ksWBl ρ β w ≠ 0 := by linarith
  constructor <;> (simp only [ksWBp]; field_simp; ring)

/-- **The `VB` node density in the spectral variables**, off the three thresholds. -/
theorem ksWB_ksWnB_eq {T : ℝ} (hTp : T ≠ ksWBp ρ β w) (hTq : T ≠ ksWBq w)
    (hTr : T ≠ ksWBr β) :
    ksWnB ρ β w T =
      ((ksWBg0 ρ β w - ksWBg1 ρ β w * T) / ρ * (ksWBr β / (ksWBr β - T)) -
          ρ * ksUcB w * (log (ksWBl ρ β w * (ksWBr β - T)) - log (T - ksWBq w))) *
        ((if ksWBp ρ β w < T then 1 else 0) - (if ksWBq w < T then 1 else 0)) -
      ksUq ρ β w * ksDYmax β w / 2 * (if ksWBp ρ β w < T then 1 else 0) +
      (1 - ρ)⁻¹ * ksUf0 β w *
        ((if ksWBr β < T then 1 else 0) - (if ksWBp ρ β w < T then 1 else 0)) -
      ρ * ksUcB w * log (ksDYmax β w / ρ) * (if ksWBq w < T then 1 else 0) +
      ρ * ksUcB w * log ((T - ksWBq w) / ksWBq w) * (if ksWBq w < T then 1 else 0) +
      ksUf0 β w * log ((T - ksWBr β) / ksWBr β) * (if ksWBr β < T then 1 else 0) := by
  obtain ⟨hq0, hq4, hr0, hr4, hl0, hY, hY1, hD0⟩ := ksWB_basic hρ hβ hw
  have hρ0 := hρ.1
  have h1 : 0 < 1 - ρ := by linarith [hρ.2]
  have ha : 0 < w * (1 - w) := mul_pos hw.1 (by linarith [hw.2])
  have hb : 0 < β * (1 - β) := mul_pos hβ.1 (by linarith [hβ.2])
  obtain ⟨hpq, hpr⟩ := ksWB_p_sub hρ hβ hw
  set q := ksWBq w with hqdef
  set r := ksWBr β with hrdef
  set l := ksWBl ρ β w with hldef
  set p := ksWBp ρ β w with hpdef
  set Y := ksDYmax β w with hYdef
  have hTq' : T - q ≠ 0 := sub_ne_zero.2 hTq
  have hqT : q - T ≠ 0 := sub_ne_zero.2 (Ne.symm hTq)
  have hrT : r - T ≠ 0 := sub_ne_zero.2 (Ne.symm hTr)
  have hAw := ksWB_ksDA_w (w := w) (-T)
  have hAb := ksWB_ksDA_β (β := β) (-T)
  rw [← hqdef] at hAw
  rw [← hrdef] at hAb
  have hcw : ksDA 1 (-T) w < 0 ↔ q < T := by
    rw [hAw, show 1 + -T / q = (q - T) / q by field_simp; ring, div_neg_iff]
    constructor
    · rintro (⟨h, h'⟩ | ⟨h, -⟩) <;> linarith
    · intro h; exact Or.inr ⟨by linarith, hq0⟩
  have hcb : ksDA 1 (-T) β < 0 ↔ r < T := by
    rw [hAb, show 1 + -T / r = (r - T) / r by field_simp; ring, div_neg_iff]
    constructor
    · rintro (⟨h, h'⟩ | ⟨h, -⟩) <;> linarith
    · intro h; exact Or.inr ⟨by linarith, hr0⟩
  have hp0 : 0 < p := ksWB_p_pos hρ hβ hw
  have hcD : (1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β < 0 ↔ p < T := by
    rw [ksWB_D_eq hρ hβ hw, ← hpdef, show 1 + -T / p = (p - T) / p by field_simp; ring]
    constructor
    · intro h
      have := (mul_neg_iff.1 h)
      rcases this with ⟨-, h'⟩ | ⟨h', -⟩
      · rw [div_neg_iff] at h'
        rcases h' with ⟨-, h''⟩ | ⟨h'', -⟩ <;> linarith
      · linarith
    · intro h
      exact mul_neg_of_pos_of_neg hD0 (div_neg_of_neg_of_pos (by linarith) hp0)
  have hlw : log (-ksDA 1 (-T) w) = log ((T - q) / q) := by
    rw [hAw]; congr 1; field_simp; ring
  have hlb : log (-ksDA 1 (-T) β) = log ((T - r) / r) := by
    rw [hAb]; congr 1; field_simp; ring
  have hG' : ksUG0 1 (-T) ρ β w / (ρ * ksDA 1 (-T) β) =
      (ksWBg0 ρ β w - ksWBg1 ρ β w * T) / ρ * (r / (r - T)) := by
    have hrT' : -T + r ≠ 0 := by intro h; exact hrT (by linarith)
    rw [ksWB_ksUG0, hAb, show 1 + -T / r = (r - T) / r by field_simp; ring]
    field_simp
    ring
  have hz : ρ * ksDYmax β w * ksDA 1 (-T) β / ((1 - ρ) * ksDA 1 (-T) w) =
      l * (r - T) / (q - T) := by
    rw [ksWB_z_eq hρ hβ hw (by rw [← hqdef]; intro h; exact hqT (by linarith)), ← hqdef,
      ← hrdef, ← hldef, ← sub_eq_add_neg, ← sub_eq_add_neg]
  have hK : (if l * (r - T) / (q - T) < -1 then
      ρ * ksUcB w * ((if w * (1 - w) < β * (1 - β) then 1 else -1) *
        log (-(l * (r - T) / (q - T)))) else 0) =
      ρ * ksUcB w * (log (l * (r - T)) - log (T - q)) *
        ((if p < T then 1 else 0) - (if q < T then 1 else 0)) := by
    have hlr : l * (r - T) ≠ 0 := mul_ne_zero hl0.ne' hrT
    have hneg : -(l * (r - T) / (q - T)) = l * (r - T) / (T - q) := by
      rw [← div_neg, neg_sub]
    rw [hneg, log_div hlr hTq']
    have hz1 : l * (r - T) / (q - T) + 1 = (1 + l) * (p - T) / (q - T) := by
      rw [hpdef, ksWBp, ← hqdef, ← hrdef, ← hldef]
      have : 1 + l ≠ 0 := by linarith
      field_simp
      ring
    have hzc : l * (r - T) / (q - T) < -1 ↔ (1 + l) * (p - T) / (q - T) < 0 := by
      rw [← hz1]; constructor <;> intro h <;> linarith
    have hε : w * (1 - w) < β * (1 - β) ↔ r < q := by
      rw [hqdef, hrdef, ksWBq, ksWBr, inv_lt_inv₀ hb ha]
    have hl1 : 0 < 1 + l := by linarith
    simp only [hzc, hε]
    rcases lt_or_gt_of_ne hTp with h₁ | h₁ <;> rcases lt_or_gt_of_ne hTq with h₂ | h₂
    · have : ¬ (1 + l) * (p - T) / (q - T) < 0 :=
        not_lt.2 (div_nonneg (mul_nonneg hl1.le (by linarith)) (by linarith))
      simp [this, not_lt.2 h₁.le, not_lt.2 h₂.le]
    · have hc : (1 + l) * (p - T) / (q - T) < 0 :=
        div_neg_of_pos_of_neg (mul_pos hl1 (by linarith)) (by linarith)
      have hqr : ¬ r < q := by
        intro h
        have : l * (r - q) / (1 + l) < 0 := div_neg_of_neg_of_pos (by nlinarith) hl1
        linarith
      simp [hc, hqr, not_lt.2 h₁.le, h₂]
      ring
    · have hc : (1 + l) * (p - T) / (q - T) < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hl1 (by linarith)) (by linarith)
      have hqr : r < q := by
        by_contra h
        have : 0 ≤ l * (r - q) / (1 + l) := div_nonneg (mul_nonneg hl0.le (by linarith)) hl1.le
        linarith
      simp [hc, hqr, h₁, not_lt.2 h₂.le]
    · have : ¬ (1 + l) * (p - T) / (q - T) < 0 :=
        not_lt.2 (div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hl1.le (by linarith))
          (by linarith))
      simp [this, h₁, h₂]
  unfold ksWnB
  simp only [hcw, hcb, hcD, hlw, hlb, hG', hz]
  rw [hK]
  split_ifs <;> ring

end Node

end QED.ChainProof.SetAKS

end
