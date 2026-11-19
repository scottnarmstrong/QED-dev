/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutSBd
public import QED.ChainProof.SetCKScOut
public import QED.ChainProof.SetCKCornInCV
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G4: the self-energy kernel weight, its size, the node map

Helper level (no frozen statement). For the outer-massive self-energy part `scOutS` of G4 the
kernel weight at `(Y, x)` combines twice the weight `scOutST` of `SetCKScOut` with the
counterterm coefficient `A(x)` (`scOutSW`): since `scOutTg` is affine in `(α, β, p)`,
`2 T + A` is again a weight `scOutTg (2α) (2β) V (2p + A)`, and
`∫₀^∞ (2T + A)/(u + v)² dv = 2 ∫₀^∞ T/(u + v)² dv + A/u` (`scOutTg_integral_two_mul_add`).

**The bound** (`scOutSW_abs_integral_le`): for `t > 0` and `Y, x ∈ (0, 1)`, with
`u = Q(x) + t`,
`∫₀^∞ |2T + A|/(u + v)² dv ≤ 40 (1 + 1/t)(1 - log Y - log x)` (`scOutSDom`), from
`scOutTg_abs_integral_le` and `|2α| ≤ 3`, `|2β| ≤ 2u`, `|2p + A| ≤ 8 - 6 log Y`,
`log(1 + u/V) ≤ u - log Y - log x` (as `1 + u/V ≤ (1 + u)/(Y x)`), `u ≥ t`.

**The node map** (`scOut_cv`): `X ↦ Q(X) - Q(x)` maps `(x, 1)` onto `(0, ∞)` with derivative
`Q'(X)`; since `u + (Q(X) - Q(x)) = Q(X) + t`, a `(u + v)⁻²`-integral becomes the node integral
`∫_x^1 k(Q(X) - Q(x)) Q'(X)/(Q(X) + t)² dX` (`scOutS_section`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

section

variable {α β V p u : ℝ}

/-- The full `(u + v)⁻²`-integral of the weight in closed form. -/
theorem scOutTg_integral (hu : 0 < u) (hV : 0 < V) :
    ∫ v in Ioi 0, scOutTg α β V p v / (u + v) ^ 2 =
      (α / (2 * V ^ 2) * V + ((β / V ^ 2 - 2 * α / V) - 2 * (α / (2 * V ^ 2)) * u) *
          (log (u + V) - log u) -
          ((p - 2 * β / V) - (β / V ^ 2 - 2 * α / V) * u + α / (2 * V ^ 2) * u ^ 2) *
            (1 / (u + V) - 1 / u)) +
        ((p - 3 / 2 * α) * (1 / (u + V)) + -α * (log (1 + u / V) / u) +
          -β * (log (1 + u / V) / u ^ 2 - 1 / (u * (u + V)))) := by
  have hint := integrableOn_scOutTg (α := α) (β := β) (p := p) hu hV
  rw [← Ioc_union_Ioi_eq_Ioi hV.le] at hint ⊢
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set subset_union_left) (hint.mono_set subset_union_right),
    (scOutTg_Ioc hu hV).2, (scOutTg_Ioi hu hV).2]

/-- `∫₀^∞ (2T + A)/(u + v)² dv = 2 ∫₀^∞ T/(u + v)² dv + A/u`. -/
theorem scOutTg_integral_two_mul_add (hu : 0 < u) (hV : 0 < V) (A : ℝ) :
    ∫ v in Ioi 0, scOutTg (2 * α) (2 * β) V (2 * p + A) v / (u + v) ^ 2 =
      2 * (∫ v in Ioi 0, scOutTg α β V p v / (u + v) ^ 2) + A / u := by
  rw [scOutTg_integral hu hV, scOutTg_integral hu hV]
  have := hu.ne'
  have := hV.ne'
  have : u + V ≠ 0 := by positivity
  field_simp
  ring

end

/-- The node map `v_x(X) = Q(X) - Q(x)`. -/
noncomputable def scOutVX (x X : ℝ) : ℝ := setCKQ X - setCKQ x

section

variable {x t : ℝ}

theorem scOutVX_image (hx : x ∈ Ioo (0 : ℝ) 1) : scOutVX x '' Ioo x 1 = Ioi 0 := by
  have h1 : 0 < 1 - x := by linarith [hx.2]
  refine Subset.antisymm ?_ fun w hw => ?_
  · rintro _ ⟨X, hX, rfl⟩
    exact sub_pos.2 (setCKQ_lt hx.1.le hX.1 hX.2)
  have hw' : (1 - x) * w ∈ cornInWX x '' Ioo x 1 := by
    rw [cornInWX_image hx]
    exact mul_pos h1 hw
  obtain ⟨X, hX, hXw⟩ := hw'
  refine ⟨X, hX, ?_⟩
  unfold cornInWX at hXw
  unfold scOutVX
  exact mul_left_cancel₀ h1.ne' hXw

/-- **The node change of variables** `v = Q(X) - Q(x)`, with integrability. -/
theorem scOut_cv (hx : x ∈ Ioo (0 : ℝ) 1) (f : ℝ → ℝ) :
    (IntegrableOn f (Ioi 0) ↔
      IntegrableOn (fun X => setCKdQ X * f (scOutVX x X)) (Ioo x 1)) ∧
      ∫ v in Ioi 0, f v = ∫ X in Ioo x 1, setCKdQ X * f (scOutVX x X) := by
  have hd : ∀ X ∈ Ioo x 1, HasDerivWithinAt (scOutVX x) (setCKdQ X) (Ioo x 1) X :=
    fun X hX => ((hasDerivAt_setCKQ hX.2).sub_const (setCKQ x)).hasDerivWithinAt
  have hinj : InjOn (scOutVX x) (Ioo x 1) := (show StrictMonoOn (scOutVX x) (Ioo x 1) from
    fun a ha b hb hab => sub_lt_sub_right (setCKQ_lt (hx.1.le.trans ha.1.le) hab hb.2) _).injOn
  have habs : ∀ X ∈ Ioo x 1, |setCKdQ X| = setCKdQ X := fun X hX =>
    abs_of_pos (setCKdQ_pos ⟨hx.1.trans hX.1, hX.2⟩)
  have hI := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hd hinj f
  have hE := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj f
  rw [scOutVX_image hx] at hI hE
  refine ⟨hI.trans ⟨fun h => ?_, fun h => ?_⟩, hE.trans ?_⟩
  · refine h.congr_fun (fun X hX => ?_) measurableSet_Ioo
    simp only [smul_eq_mul, habs X hX]
  · refine h.congr_fun (fun X hX => ?_) measurableSet_Ioo
    simp only [smul_eq_mul, habs X hX]
  · refine setIntegral_congr_fun measurableSet_Ioo fun X hX => ?_
    simp only [smul_eq_mul, habs X hX]

/-- **A section of the self-energy kernel** by the node change of variables. -/
theorem scOutS_section (hx : x ∈ Ioo (0 : ℝ) 1) {k : ℝ → ℝ}
    (hk : IntegrableOn (fun v => k v / (setCKQ x + t + v) ^ 2) (Ioi 0)) :
    Integrable (fun X => (if x < X then k (scOutVX x X) else 0) *
        (setCKdQ X / (setCKQ X + t) ^ 2)) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
      ∫ X in Ioo (0 : ℝ) 1, (if x < X then k (scOutVX x X) else 0) *
        (setCKdQ X / (setCKQ X + t) ^ 2) = ∫ v in Ioi 0, k v / (setCKQ x + t + v) ^ 2 := by
  obtain ⟨hiff, hval⟩ := scOut_cv hx (fun v => k v / (setCKQ x + t + v) ^ 2)
  set g : ℝ → ℝ := fun X => k (scOutVX x X) * (setCKdQ X / (setCKQ X + t) ^ 2) with hgdef
  have hg : ∀ X ∈ Ioo x 1,
      setCKdQ X * (k (scOutVX x X) / (setCKQ x + t + scOutVX x X) ^ 2) = g X := by
    intro X _
    simp only [hgdef, scOutVX]
    ring_nf
  have hgi : IntegrableOn g (Ioo x 1) := (hiff.1 hk).congr_fun hg measurableSet_Ioo
  have he : ∀ X ∈ Ioo (0 : ℝ) 1, (if x < X then k (scOutVX x X) else 0) *
      (setCKdQ X / (setCKQ X + t) ^ 2) = (Ioo x 1).indicator g X := by
    intro X hX
    by_cases h : x < X
    · simp only [h, ↓reduceIte]
      rw [indicator_of_mem (show X ∈ Ioo x 1 from ⟨h, hX.2⟩)]
    · simp only [h, ↓reduceIte, zero_mul]
      rw [indicator_of_notMem (show X ∉ Ioo x 1 from fun h' => h h'.1)]
  have hsub : Ioo (0 : ℝ) 1 ∩ Ioo x 1 = Ioo x 1 :=
    inter_eq_right.2 (Ioo_subset_Ioo_left hx.1.le)
  refine ⟨?_, ?_⟩
  · have := (hgi.integrable_indicator measurableSet_Ioo).integrableOn (s := Ioo (0 : ℝ) 1)
    exact this.congr_fun (fun X hX => (he X hX).symm) measurableSet_Ioo
  · rw [setIntegral_congr_fun measurableSet_Ioo he, setIntegral_indicator measurableSet_Ioo,
      hsub, hval]
    exact (setIntegral_congr_fun measurableSet_Ioo hg).symm

end

/-- **The self-energy kernel weight** `2 T(Y, x, v) + A(x)` at `(Y, x)`. -/
noncomputable def scOutSW (Y x v : ℝ) : ℝ :=
  scOutTg (2 * (selfK1 Y x * scOutRho x)) (2 * (selfK2 Y x * scOutRho x ^ 2))
    (Y ^ 2 * scOutRho x / (Y * (1 - Y)))
    (2 * -(selfK1 Y x * scOutRho x * log (Y ^ 2)) + scOutSA x) v

/-- The dominating function `40 (1 + 1/t)(1 - log Y - log x)` of the self-energy kernel. -/
noncomputable def scOutSDom (t Y x : ℝ) : ℝ := 40 * (1 + 1 / t) * (1 + -log Y + -log x)

section

variable {t Y x : ℝ}

theorem scOutSV_pos (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < Y ^ 2 * scOutRho x / (Y * (1 - Y)) := by
  have := scOutRho_pos hx
  have : 0 < 1 - Y := by linarith [hY.2]
  have := hY.1
  positivity

theorem scOutSu_pos (ht : 0 < t) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < setCKQ x + t := by
  have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  linarith

theorem integrableOn_scOutSW (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun v => scOutSW Y x v / (setCKQ x + t + v) ^ 2) (Ioi 0) :=
  integrableOn_scOutTg (scOutSu_pos ht hx) (scOutSV_pos hY hx)

/-- The node integral of the kernel weight: `2 (scOutSG + k₂ρ² log Y²/u²) + A/u`. -/
theorem scOutSW_integral (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ v in Ioi 0, scOutSW Y x v / (setCKQ x + t + v) ^ 2 =
      2 * (scOutSG t Y x + selfK2 Y x * scOutRho x ^ 2 * log (Y ^ 2) / (setCKQ x + t) ^ 2) +
        scOutSA x / (setCKQ x + t) := by
  unfold scOutSW
  rw [scOutTg_integral_two_mul_add (scOutSu_pos ht hx) (scOutSV_pos hY hx), scOutSG_eq ht hY hx]
  unfold scOutST
  ring

/-- `1 + u/V ≤ (1 + u)/(Y x)`. -/
theorem scOutS_one_add_div_le (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) {u : ℝ}
    (hu : 0 < u) : 1 + u / (Y ^ 2 * scOutRho x / (Y * (1 - Y))) ≤ (1 + u) / (Y * x) := by
  have h1 : 0 < 1 - Y := by linarith [hY.2]
  have h2 : 0 < 1 - x := by linarith [hx.2]
  have hY0 := hY.1
  have hx0 := hx.1
  have e : 1 + u / (Y ^ 2 * scOutRho x / (Y * (1 - Y))) =
      (Y * x + u * ((1 - Y) * (1 - x))) / (Y * x) := by
    unfold scOutRho
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : Y * x ≤ 1 := by nlinarith
  have : (1 - Y) * (1 - x) ≤ 1 := by nlinarith
  nlinarith

/-- `log(1 + u/V)/u ≤ 1 + (-log Y - log x)/t`. -/
theorem scOutS_log_div_le (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    log (1 + (setCKQ x + t) / (Y ^ 2 * scOutRho x / (Y * (1 - Y)))) / (setCKQ x + t) ≤
      1 + (-log Y + -log x) * (1 / t) := by
  set u := setCKQ x + t with hu_def
  have hu : 0 < u := scOutSu_pos ht hx
  have htu : t ≤ u := by have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩; linarith
  have hV := scOutSV_pos hY hx
  have hY0 := hY.1
  have hx0 := hx.1
  have hlY : 0 ≤ -log Y := neg_nonneg.2 (log_nonpos hY0.le hY.2.le)
  have hlx : 0 ≤ -log x := neg_nonneg.2 (log_nonpos hx0.le hx.2.le)
  have hlog : log (1 + u / (Y ^ 2 * scOutRho x / (Y * (1 - Y)))) ≤ u + (-log Y + -log x) := by
    calc _ ≤ log ((1 + u) / (Y * x)) :=
          log_le_log (by positivity) (scOutS_one_add_div_le hY hx hu)
      _ = log (1 + u) - log Y - log x := by
          rw [log_div (by positivity) (by positivity), log_mul hY0.ne' hx0.ne']
          ring
      _ ≤ u + (-log Y + -log x) := by
          have := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + u)
          linarith
  rw [div_le_iff₀ hu]
  have hL : 0 ≤ -log Y + -log x := by linarith
  have hs : 1 ≤ u / t := by rw [le_div_iff₀ ht]; linarith
  have h1 : -log Y + -log x ≤ (-log Y + -log x) * (1 / t) * u := by
    calc -log Y + -log x = (-log Y + -log x) * 1 := by ring
      _ ≤ (-log Y + -log x) * (u / t) := mul_le_mul_of_nonneg_left hs hL
      _ = (-log Y + -log x) * (1 / t) * u := by ring
  have e : (1 + (-log Y + -log x) * (1 / t)) * u = u + (-log Y + -log x) * (1 / t) * u := by
    ring
  linarith

/-- **The size of the self-energy kernel weight.** -/
theorem scOutSW_abs_integral_le (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ v in Ioi 0, |scOutSW Y x v / (setCKQ x + t + v) ^ 2| ≤ scOutSDom t Y x := by
  have hu : 0 < setCKQ x + t := scOutSu_pos ht hx
  have hV := scOutSV_pos hY hx
  have hQ := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hY0 := hY.1
  have hx0 := hx.1
  have hY1 := hY.2
  have hx1 := hx.2
  have h1x : 0 < 1 - x := by linarith
  have hlY : 0 ≤ -log Y := neg_nonneg.2 (log_nonpos hY0.le hY1.le)
  have hlx : 0 ≤ -log x := neg_nonneg.2 (log_nonpos hx0.le hx1.le)
  have hlog := scOutS_log_div_le ht hY hx
  unfold scOutSW
  refine (scOutTg_abs_integral_le hu hV).trans ?_
  set u := setCKQ x + t with hu_def
  set V := Y ^ 2 * scOutRho x / (Y * (1 - Y)) with hV_def
  set ℓ := log (1 + u / V) with hℓ_def
  set L := -log Y + -log x with hL_def
  set s := 1 / t with hs_def
  have ea : 2 * (selfK1 Y x * scOutRho x) = x ^ 2 * (Y * (2 * x + 1) + 2 * (1 - x)) := by
    unfold selfK1 scOutRho
    field_simp
    ring
  have eb : 2 * (selfK2 Y x * scOutRho x ^ 2) =
      -(setCKQ x * (x ^ 2 * (3 - x - Y * (1 - x)) / 2)) := by
    unfold selfK2 scOutRho setCKQ
    field_simp
    ring
  have ep : 2 * -(selfK1 Y x * scOutRho x * log (Y ^ 2)) + scOutSA x =
      2 * (2 * (selfK1 Y x * scOutRho x)) * -log Y + scOutSA x := by
    rw [log_pow]
    push_cast
    ring
  rw [ep, ea, eb]
  have ha : |x ^ 2 * (Y * (2 * x + 1) + 2 * (1 - x))| ≤ 3 := by
    have c0 : 0 ≤ Y * (2 * x + 1) + 2 * (1 - x) := by positivity
    have c1 : Y * (2 * x + 1) + 2 * (1 - x) ≤ 3 := by nlinarith
    have : x ^ 2 ≤ 1 := by nlinarith
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hb : |-(setCKQ x * (x ^ 2 * (3 - x - Y * (1 - x)) / 2))| ≤ 2 * u := by
    have c0 : 0 ≤ 3 - x - Y * (1 - x) := by nlinarith
    have c1 : x ^ 2 * (3 - x - Y * (1 - x)) / 2 ≤ 2 := by
      have : x ^ 2 ≤ 1 := by nlinarith
      have : 3 - x - Y * (1 - x) ≤ 3 := by nlinarith
      have : x ^ 2 * (3 - x - Y * (1 - x)) ≤ 1 * 3 :=
        mul_le_mul (by assumption) this c0 zero_le_one
      linarith
    rw [abs_neg, abs_of_nonneg (by positivity)]
    nlinarith
  have hA : |scOutSA x| ≤ 8 := by
    unfold scOutSA
    rw [abs_le]
    constructor <;> nlinarith
  set a := x ^ 2 * (Y * (2 * x + 1) + 2 * (1 - x)) with ha_def
  set b := -(setCKQ x * (x ^ 2 * (3 - x - Y * (1 - x)) / 2)) with hb_def
  have hp : |2 * a * -log Y + scOutSA x| ≤ 8 + 6 * -log Y := by
    calc _ ≤ |2 * a * -log Y| + |scOutSA x| := abs_add_le _ _
      _ = 2 * |a| * -log Y + |scOutSA x| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hlY]
          norm_num
      _ ≤ 2 * 3 * -log Y + 8 := by gcongr
      _ = 8 + 6 * -log Y := by ring
  set p := 2 * a * -log Y + scOutSA x with hp_def
  have hsu : 1 / u ≤ s := by
    rw [hs_def]
    exact one_div_le_one_div_of_le ht (by linarith)
  have hsuV : 1 / (u + V) ≤ s := by
    rw [hs_def]
    exact one_div_le_one_div_of_le ht (by linarith)
  have hs0 : 0 ≤ s := by positivity
  have huV : 0 ≤ u / V := by positivity
  have hℓ0 : 0 ≤ ℓ := log_nonneg (by linarith)
  have hbu : |b| / u ≤ 2 := by rw [div_le_iff₀ hu]; linarith
  have t1 : (5 / 2 * |a| + |p|) / u ≤ (15.5 + 6 * -log Y) * s := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hsu (by positivity) (by positivity)
  have t2 : 3 * |b| / u ^ 2 ≤ 6 * s := by
    have : 3 * |b| / u ^ 2 = 3 * (|b| / u) * (1 / u) := by
      field_simp
    rw [this]
    calc 3 * (|b| / u) * (1 / u) ≤ 3 * 2 * s := by gcongr
      _ = 6 * s := by ring
  have t3 : (3 / 2 * |a| + |p|) / (u + V) ≤ (12.5 + 6 * -log Y) * s := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hsuV (by positivity) (by positivity)
  have hℓu : 0 ≤ ℓ / u := by positivity
  have t4 : |a| * (ℓ / u) ≤ 3 * (1 + L * s) := mul_le_mul ha hlog hℓu (by norm_num)
  have t5 : |b| * (ℓ / u ^ 2) ≤ 2 * (1 + L * s) := by
    have e : |b| * (ℓ / u ^ 2) = (|b| / u) * (ℓ / u) := by
      field_simp
    rw [e]
    exact mul_le_mul hbu hlog hℓu (by norm_num)
  have hLs : 0 ≤ -log Y * s := mul_nonneg hlY hs0
  have hLs' : 0 ≤ -log x * s := mul_nonneg hlx hs0
  rw [hL_def] at t4 t5
  have e4 : 3 * (1 + (-log Y + -log x) * s) = 3 + 3 * (-log Y * s) + 3 * (-log x * s) := by
    ring
  have e5 : 2 * (1 + (-log Y + -log x) * s) = 2 + 2 * (-log Y * s) + 2 * (-log x * s) := by
    ring
  have e1 : (15.5 + 6 * -log Y) * s = 15.5 * s + 6 * (-log Y * s) := by ring
  have e3 : (12.5 + 6 * -log Y) * s = 12.5 * s + 6 * (-log Y * s) := by ring
  rw [e4] at t4
  rw [e5] at t5
  rw [e1] at t1
  rw [e3] at t3
  have e : scOutSDom t Y x = 40 + 40 * s + 40 * -log Y + 40 * -log x + 40 * (-log Y * s) +
      40 * (-log x * s) := by
    unfold scOutSDom
    rw [← hs_def]
    ring
  rw [e]
  linarith

end

end QED.ChainProof.SetCK

end
