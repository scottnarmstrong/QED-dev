/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecCore

/-!
# (R-Π₄) step L9: decay of a per-flavour function of scaling form

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9. By dimensional
analysis the photon-regulator limit of one flavour of mass `M` in the block of the lepton of mass
`μ` has the scaling form
`T μ x s = G(s/x) + κ log(x/μ²) φ(s/x)`, `x = M²`:
`G` is the per-flavour renormalized two-loop form factor and the second term is the mismatch of
the on-shell mass insertion, read at the lepton mass `μ` instead of at `M` (`κ = -3/4` in the
units of the design numerics). If `G` and `φ` vanish at `0` and are Lipschitz near `0`, this
function decouples (`DecDecay`), with rate `x^{-1/2}`.

* `decT G φ κ`: the scaling form;
* `dec_log_le_two_mul_sqrt`: `log z ≤ 2 √z`;
* `dec_decay_decT`: **`DecDecay (decT G φ κ) μ`** for every `μ > 0`;
* `DecScal`: the representation of `asmPolLim` by a scaling form with such `G`, `φ`;
* `dec_asmDecoupling_of_scal`: **`DecScal → AsmDecoupling`**;
* `dec_core`: `AsmFaceIds → DecScal → AsmMajorant → Core`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

section Scal

/-- **The scaling form of a per-flavour function**: `G(s/x) + κ log(x/μ²) φ(s/x)`. -/
noncomputable def decT (G φ : ℝ → ℂ) (κ : ℂ) (μ x s : ℝ) : ℂ :=
  G (s / x) + κ * (Real.log (x / μ ^ 2) : ℂ) * φ (s / x)

theorem dec_log_le_two_mul_sqrt {z : ℝ} (hz : 0 < z) : Real.log z ≤ 2 * Real.sqrt z := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hz)
  rw [Real.log_sqrt hz.le] at h
  linarith

/-- A function vanishing at `0` and `L`-Lipschitz on `[-δ, δ]` is bounded by `L K / x` at
`s / x` for `|s| ≤ K ≤ δ x`. -/
theorem dec_norm_le_of_lip {G : ℝ → ℂ} {δ L K s x : ℝ}
    (hG0 : G 0 = 0) (hG : ∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ → ‖G σ - G σ'‖ ≤ L * |σ - σ'|)
    (hx : 0 < x) (hs : |s| ≤ K) (hK : K ≤ δ * x) (hL : 0 ≤ L) :
    ‖G (s / x)‖ ≤ L * K / x := by
  have hδ : |s / x| ≤ δ := by
    rw [abs_div, abs_of_pos hx, div_le_iff₀ hx]
    linarith
  have h0 : |(0 : ℝ)| ≤ δ := by
    rw [abs_zero]
    exact (abs_nonneg _).trans hδ
  have := hG (s / x) 0 hδ h0
  rw [hG0, sub_zero, sub_zero, abs_div, abs_of_pos hx] at this
  calc _ ≤ L * (|s| / x) := this
    _ ≤ L * (K / x) := by gcongr
    _ = L * K / x := by ring

variable {G φ : ℝ → ℂ} {κ : ℂ} {δ L : ℝ}

/-- **Decay of the scaling form**: if `G` and `φ` vanish at `0` and are `L`-Lipschitz on
`[-δ, δ]`, then `decT G φ κ μ` satisfies `DecDecay` for every `μ > 0`. -/
theorem dec_decay_decT (hδ : 0 < δ) (hL : 0 ≤ L) (hG0 : G 0 = 0) (hφ0 : φ 0 = 0)
    (hG : ∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ → ‖G σ - G σ'‖ ≤ L * |σ - σ'|)
    (hφ : ∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ → ‖φ σ - φ σ'‖ ≤ L * |σ - σ'|)
    {μ : ℝ} (hμ : 0 < μ) : DecDecay (decT G φ κ) μ := by
  intro S₀ S η hη
  set K : ℝ := |S₀| + |S| + 1 with hK
  have hK0 : 0 < K := by positivity
  set C : ℝ := L * K * (2 + ‖κ‖ + 2 * ‖κ‖ / μ) with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨max (max 1 (μ ^ 2)) (max (K / δ) ((C / η) ^ 2)), fun s h₀ h₁ x y hx hxy => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxμ : μ ^ 2 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxK : K / δ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxC : (C / η) ^ 2 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hx0 : 0 < x := one_pos.trans_le hx1
  have hy0 : 0 < y := hx0.trans_le hxy
  have hs : |s| ≤ K := by
    rw [hK, abs_le]
    constructor <;> linarith [abs_nonneg S₀, abs_nonneg S, neg_abs_le S₀, le_abs_self S]
  have hKx : K ≤ δ * x := by rwa [div_le_iff₀ hδ, mul_comm] at hxK
  have hKy : K ≤ δ * y := hKx.trans (by gcongr)
  have hμ2 : 0 < μ ^ 2 := by positivity
  -- square roots and logs
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsxy : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have hxsx : Real.sqrt x ≤ x := by
    rw [Real.sqrt_le_iff]
    exact ⟨hx0.le, by nlinarith⟩
  have hinvx : 1 / x ≤ 1 / Real.sqrt x := one_div_le_one_div_of_le hsx hxsx
  have hηsx : C / Real.sqrt x ≤ η := by
    rw [div_le_iff₀ hsx]
    have h1 : C / η ≤ Real.sqrt x := by
      rw [show C / η = Real.sqrt ((C / η) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hxC
    rw [div_le_iff₀ hη] at h1
    linarith
  have hlogx : 0 ≤ Real.log (x / μ ^ 2) := Real.log_nonneg (by rwa [le_div_iff₀ hμ2, one_mul])
  have hlogy : 0 ≤ Real.log (y / μ ^ 2) :=
    Real.log_nonneg (by rw [le_div_iff₀ hμ2, one_mul]; linarith)
  have hsqrtμ : ∀ z : ℝ, 0 < z → Real.sqrt (z / μ ^ 2) = Real.sqrt z / μ := fun z hz => by
    rw [Real.sqrt_div' _ hμ2.le, Real.sqrt_sq hμ.le]
  have hlx : Real.log (x / μ ^ 2) ≤ 2 * Real.sqrt x / μ := by
    have := dec_log_le_two_mul_sqrt (div_pos hx0 hμ2)
    rw [hsqrtμ x hx0] at this
    linarith [mul_div_assoc 2 (Real.sqrt x) μ]
  have hly : Real.log (y / μ ^ 2) ≤ 2 * Real.sqrt y / μ := by
    have := dec_log_le_two_mul_sqrt (div_pos hy0 hμ2)
    rw [hsqrtμ y hy0] at this
    linarith [mul_div_assoc 2 (Real.sqrt y) μ]
  -- values at `s / x`, `s / y`
  have bGx := dec_norm_le_of_lip hG0 hG hx0 hs hKx hL
  have bφx := dec_norm_le_of_lip hφ0 hφ hx0 hs hKx hL
  have hδx : |s / x| ≤ δ := by
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]; linarith
  have hδy : |s / y| ≤ δ := by
    rw [abs_div, abs_of_pos hy0, div_le_iff₀ hy0]; linarith
  have hdiff : |s / y - s / x| ≤ K * ((y - x) / (x * y)) := by
    have e : s / y - s / x = s * ((x - y) / (x * y)) := by
      field_simp
    have h2 : |(x - y) / (x * y)| = (y - x) / (x * y) := by
      rw [abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)]
    rw [e, abs_mul, h2]
    exact mul_le_mul_of_nonneg_right hs (div_nonneg (by linarith) (mul_pos hx0 hy0).le)
  have dG := (hG _ _ hδy hδx).trans (mul_le_mul_of_nonneg_left hdiff hL)
  have dφ := (hφ _ _ hδy hδx).trans (mul_le_mul_of_nonneg_left hdiff hL)
  have hq : 0 ≤ (y - x) / x := div_nonneg (by linarith) hx0.le
  -- `(y - x) / (x y) ≤ ((y - x) / x) / √x`
  have hxy' : (y - x) / (x * y) ≤ (y - x) / x * (1 / Real.sqrt x) := by
    rw [show (y - x) / (x * y) = (y - x) / x * (1 / y) by field_simp]
    exact mul_le_mul_of_nonneg_left ((one_div_le_one_div_of_le hx0 hxy).trans hinvx) hq
  have hlogdiff : Real.log (y / μ ^ 2) - Real.log (x / μ ^ 2) ≤ (y - x) / x := by
    rw [← Real.log_div (div_pos hy0 hμ2).ne' (div_pos hx0 hμ2).ne',
      show y / μ ^ 2 / (x / μ ^ 2) = y / x by field_simp]
    have := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [show y / x - 1 = (y - x) / x by field_simp] at this
    exact this
  have hlogdiff0 : 0 ≤ Real.log (y / μ ^ 2) - Real.log (x / μ ^ 2) := by
    rw [sub_nonneg]
    exact Real.log_le_log (div_pos hx0 hμ2) (div_le_div_of_nonneg_right hxy hμ2.le)
  have hκ := norm_nonneg κ
  have hsx_x : Real.sqrt x / x ≤ 1 / Real.sqrt x := by
    rw [div_le_div_iff₀ hx0 hsx, one_mul, Real.mul_self_sqrt hx0.le]
  have hsy_x : Real.sqrt y / y ≤ 1 / Real.sqrt x := by
    rw [div_le_div_iff₀ hy0 hsx, one_mul]
    calc Real.sqrt y * Real.sqrt x ≤ Real.sqrt y * Real.sqrt y := by gcongr
      _ = y := Real.mul_self_sqrt hy0.le
  have hLK : 0 ≤ L * K := by positivity
  constructor
  · -- the bound
    simp only [decT]
    calc _ ≤ ‖G (s / x)‖ + ‖κ‖ * Real.log (x / μ ^ 2) * ‖φ (s / x)‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlogx]
      _ ≤ L * K / x + ‖κ‖ * (2 * Real.sqrt x / μ) * (L * K / x) := by gcongr
      _ = L * K * (1 / x) + ‖κ‖ * (2 / μ) * (L * K) * (Real.sqrt x / x) := by ring
      _ ≤ L * K * (1 / Real.sqrt x) + ‖κ‖ * (2 / μ) * (L * K) * (1 / Real.sqrt x) :=
          add_le_add (mul_le_mul_of_nonneg_left hinvx hLK)
            (mul_le_mul_of_nonneg_left hsx_x (by positivity))
      _ ≤ C / Real.sqrt x := by
          have e : C / Real.sqrt x = L * K * (1 / Real.sqrt x) +
              ‖κ‖ * (2 / μ) * (L * K) * (1 / Real.sqrt x) +
              L * K * (1 + ‖κ‖) * (1 / Real.sqrt x) := by
            rw [hC]
            field_simp
            ring
          have : 0 ≤ L * K * (1 + ‖κ‖) * (1 / Real.sqrt x) := by positivity
          linarith
      _ ≤ η := hηsx
  · -- the Lipschitz bound
    simp only [decT]
    set a := Real.log (x / μ ^ 2)
    set b := Real.log (y / μ ^ 2)
    have e : G (s / y) + κ * (b : ℂ) * φ (s / y) - (G (s / x) + κ * (a : ℂ) * φ (s / x)) =
        (G (s / y) - G (s / x)) + κ * ((b : ℂ) * (φ (s / y) - φ (s / x)) +
          ((b - a : ℝ) : ℂ) * φ (s / x)) := by
      push_cast
      ring
    rw [e]
    have hb' : b ≤ 2 * Real.sqrt y / μ := hly
    have t2 : ‖(b : ℂ) * (φ (s / y) - φ (s / x))‖ ≤
        2 * L * K / μ * ((y - x) / x * (1 / Real.sqrt x)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlogy]
      calc b * ‖φ (s / y) - φ (s / x)‖ ≤ (2 * Real.sqrt y / μ) * (L * (K * ((y - x) / (x * y))))
            := mul_le_mul hb' dφ (norm_nonneg _) (by positivity)
        _ = 2 * L * K / μ * ((y - x) / x) * (Real.sqrt y / y) := by
            field_simp
        _ ≤ 2 * L * K / μ * ((y - x) / x) * (1 / Real.sqrt x) :=
            mul_le_mul_of_nonneg_left hsy_x (by positivity)
        _ = _ := by ring
    have t3 : ‖((b - a : ℝ) : ℂ) * φ (s / x)‖ ≤ L * K * ((y - x) / x * (1 / Real.sqrt x)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlogdiff0]
      calc (b - a) * ‖φ (s / x)‖ ≤ (y - x) / x * (L * K / x) :=
            mul_le_mul hlogdiff bφx (norm_nonneg _) hq
        _ = L * K * ((y - x) / x * (1 / x)) := by ring
        _ ≤ L * K * ((y - x) / x * (1 / Real.sqrt x)) := by gcongr
    have t1 : ‖G (s / y) - G (s / x)‖ ≤ L * K * ((y - x) / x * (1 / Real.sqrt x)) := by
      calc _ ≤ L * (K * ((y - x) / (x * y))) := dG
        _ = L * K * ((y - x) / (x * y)) := by ring
        _ ≤ _ := by gcongr
    set w := (y - x) / x * (1 / Real.sqrt x)
    have hw : 0 ≤ w := by positivity
    have hsum : ‖(b : ℂ) * (φ (s / y) - φ (s / x)) + ((b - a : ℝ) : ℂ) * φ (s / x)‖ ≤
        2 * L * K / μ * w + L * K * w := (norm_add_le _ _).trans (add_le_add t2 t3)
    have hκs : ‖κ * ((b : ℂ) * (φ (s / y) - φ (s / x)) + ((b - a : ℝ) : ℂ) * φ (s / x))‖ ≤
        ‖κ‖ * (2 * L * K / μ * w + L * K * w) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hsum hκ
    have hCw : L * K * w + ‖κ‖ * (2 * L * K / μ * w + L * K * w) ≤ C * w := by
      have e : C * w = L * K * w + ‖κ‖ * (2 * L * K / μ * w + L * K * w) + L * K * w := by
        rw [hC]
        ring
      have : 0 ≤ L * K * w := by positivity
      linarith
    have hfin : C * w = (C / Real.sqrt x) * ((y - x) / x) := by
      simp only [w]
      ring
    calc _ ≤ ‖G (s / y) - G (s / x)‖ +
          ‖κ * ((b : ℂ) * (φ (s / y) - φ (s / x)) + ((b - a : ℝ) : ℂ) * φ (s / x))‖ :=
          norm_add_le _ _
      _ ≤ L * K * w + ‖κ‖ * (2 * L * K / μ * w + L * K * w) := add_le_add t1 hκs
      _ ≤ C * w := hCw
      _ = (C / Real.sqrt x) * ((y - x) / x) := hfin
      _ ≤ η * ((y - x) / x) := mul_le_mul_of_nonneg_right hηsx hq

end Scal

section Rep

variable {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)

/-- **(L9, open) the scaling representation of the photon-regulator limit**: there are
functions `G`, `φ` vanishing at `0` and Lipschitz near `0`, and a constant `κ`, such that
`asmPolLim` of the frozen flavours is, block by block, the block sum of
`decT G φ κ μ x s = G(s/x) + κ log(x/μ²) φ(s/x)`. -/
def DecScal : Prop :=
  ∃ (G φ : ℝ → ℂ) (κ : ℂ) (δ L : ℝ), 0 < δ ∧ 0 ≤ L ∧ G 0 = 0 ∧ φ 0 = 0 ∧
    (∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ → ‖G σ - G σ'‖ ≤ L * |σ - σ'|) ∧
    (∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ → ‖φ σ - φ σ'‖ ≤ L * |σ - σ'|) ∧
    DecRep P₀ mH (decT G φ κ)

/-- **L9 from the scaling representation**: `DecScal → AsmDecoupling`, with
`Π_∞(s) = G(s/m²) + ∑_ℓ G(s/m_ℓ²)`. -/
theorem dec_asmDecoupling_of_scal (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (h : DecScal P₀ mH) : AsmDecoupling P₀ mH := by
  obtain ⟨G, φ, κ, δ, L, hδ, hL, hG0, hφ0, hG, hφ, hrep⟩ := h
  exact dec_asmDecoupling_of_rep P₀ mH hm hmH _ hrep (dec_decay_decT hδ hL hG0 hφ0 hG hφ hm)
    fun ℓ => dec_decay_decT hδ hL hG0 hφ0 hG hφ (hm.trans (hmH ℓ))

/-- **The analytic core from the face-limit identity (L6d3), the scaling representation (L9) and
the majorant (L10).** -/
theorem dec_core (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hId : AsmFaceIds P₀ mH) (hScal : DecScal P₀ mH) (hMaj : AsmMajorant P₀ mH) :
    Core P₀ mH :=
  asm_core P₀ mH he hm hmH hId (dec_asmDecoupling_of_scal P₀ mH hm hmH hScal) hMaj

end Rep

end QED.GradedProof.RPi4

end
