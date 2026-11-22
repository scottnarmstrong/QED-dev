/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWQDisp
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Set (a), stage D: the `x`-integral of the `VA` node density

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. At a
fixed fraction `σ ∈ (0, 1)` and `a = Tσ(1-σ) - 1 > 0`, the node density `ksWnAa x σ a` is, in
`x ∈ (0, 1)`, of the form `(p + qx) log x + r + sx` below the second threshold
`x < c = a/(a + 1 - σ)` and `(p' + q'x) log x + m(1-x) log(1-x) + e/x + r' + s'x` above it,
so its `x`-integral is elementary (`ksWRMx`). The threshold weight `C̄(σ) = ∫₀¹ ksWCA x σ dx`
is `4σ(1-σ)(11 - 16σ)`.

Main results:

* `ksWR_integral_high`, `ksWR_integral_low`, `ksWR_integral_full`: the three elementary
  `x`-integrals;
* **`ksWR_integral_ksWnAa`**: `∫₀¹ ksWnAa x σ a dx = ksWRMx σ a`;
* **`ksWR_integral_ksWCA`**: `∫₀¹ ksWCA x σ dx = 4σ(1-σ)(11 - 16σ)`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace QED.ChainProof.SetAKS

/-! ### Three elementary integrals -/

/-- The value of `∫₀^c (p + qx) log x + r + sx`. -/
noncomputable def ksWRH (c p q r s : ℝ) : ℝ :=
  (p * c + q * c ^ 2 / 2) * log c - (p * c + q * c ^ 2 / 4) + r * c + s * c ^ 2 / 2

/-- The value of `∫_c^1 (p + qx) log x + m(1-x) log(1-x) + e/x + r + sx`. -/
noncomputable def ksWRL (c p q m e r s : ℝ) : ℝ :=
  -p - q / 4 - ((p * c + q * c ^ 2 / 2) * log c - p * c - q * c ^ 2 / 4) +
    m * ((1 - c) ^ 2 / 2 * log (1 - c) - (1 - c) ^ 2 / 4) - e * log c + r * (1 - c) +
    s * (1 - c ^ 2) / 2

theorem ksWR_hasDerivAt_mulLog {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y => y * log y) (log x + 1) x := by
  have h := (hasDerivAt_id x).mul (hasDerivAt_log hx)
  simp only [id, one_mul] at h
  refine h.congr_deriv ?_
  field_simp

theorem ksWR_hasDerivAt_mulLog_one {x : ℝ} (hx : 1 - x ≠ 0) :
    HasDerivAt (fun y => (1 - y) * log (1 - y)) (-log (1 - x) - 1) x := by
  have h := (ksWR_hasDerivAt_mulLog hx).comp x ((hasDerivAt_id x).const_sub 1)
  refine h.congr_deriv ?_
  ring

theorem ksWR_continuous_mulLog_one : Continuous fun y : ℝ => (1 - y) * log (1 - y) :=
  continuous_mul_log.comp (continuous_const.sub continuous_id)

theorem ksWR_intervalIntegrable_linLog (p q a b : ℝ) :
    IntervalIntegrable (fun x => (p + q * x) * log x) volume a b :=
  intervalIntegrable_log'.continuousOn_mul (by fun_prop)

theorem ksWR_intervalIntegrable_log_one (a b : ℝ) :
    IntervalIntegrable (fun x => log (1 - x)) volume a b := by
  have h := (intervalIntegrable_log' (a := 1 - a) (b := 1 - b)).comp_sub_left 1
  simp only [sub_sub_cancel] at h
  exact h

/-- **`∫₀^c (p + qx) log x + r + sx`** for `c > 0`. -/
theorem ksWR_integral_high {c : ℝ} (hc : 0 < c) (p q r s : ℝ) :
    ∫ x in (0 : ℝ)..c, ((p + q * x) * log x + (r + s * x)) = ksWRH c p q r s := by
  set F : ℝ → ℝ := fun x => (p + q * x / 2) * (x * log x) - (p * x + q * x ^ 2 / 4) +
    r * x + s * x ^ 2 / 2 with hF
  have hcont : ContinuousOn F (Icc 0 c) := by
    refine Continuous.continuousOn ?_
    simp only [hF]
    have := continuous_mul_log
    fun_prop
  have hder : ∀ x ∈ Ioo 0 c, HasDerivAt F ((p + q * x) * log x + (r + s * x)) x := by
    intro x hx
    have h1 := ksWR_hasDerivAt_mulLog hx.1.ne'
    have h := ((((hasDerivAt_id x).const_mul q).div_const 2).const_add p).mul h1
    have h2 := ((((hasDerivAt_id x).const_mul p).add (((hasDerivAt_pow 2 x).const_mul q).div_const
      4)))
    have h3 := (hasDerivAt_id x).const_mul r
    have h4 := ((hasDerivAt_pow 2 x).const_mul s).div_const 2
    refine (((h.sub h2).add h3).add h4).congr_deriv ?_
    simp only [id]
    push_cast
    ring
  have hint : IntervalIntegrable (fun x => (p + q * x) * log x + (r + s * x)) volume 0 c :=
    (ksWR_intervalIntegrable_linLog p q 0 c).add (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [integral_eq_sub_of_hasDerivAt_of_le hc.le hcont hder hint]
  simp only [hF, ksWRH, log_zero]
  ring

/-- **`∫_c^1 (p + qx) log x + m(1-x) log(1-x) + e/x + r + sx`** for `0 < c < 1`. -/
theorem ksWR_integral_low {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (p q m e r s : ℝ) :
    ∫ x in c..1, ((p + q * x) * log x + m * ((1 - x) * log (1 - x)) + e / x + (r + s * x)) =
      ksWRL c p q m e r s := by
  set F : ℝ → ℝ := fun x => (p + q * x / 2) * (x * log x) - (p * x + q * x ^ 2 / 4) +
    m * (-((1 - x) / 2) * ((1 - x) * log (1 - x)) + (1 - x) ^ 2 / 4) + e * log x + r * x +
    s * x ^ 2 / 2 with hF
  have hcont : ContinuousOn F (Icc c 1) := by
    have hl : ContinuousOn log (Icc c 1) :=
      continuousOn_log.mono fun x hx => (hc.trans_le hx.1).ne'
    have := continuous_mul_log
    have := ksWR_continuous_mulLog_one
    simp only [hF]
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add ?_ (hl.const_smul e)) ?_) ?_
    · exact Continuous.continuousOn (by fun_prop)
    · exact Continuous.continuousOn (by fun_prop)
    · exact Continuous.continuousOn (by fun_prop)
  have hder : ∀ x ∈ Ioo c 1, HasDerivAt F
      ((p + q * x) * log x + m * ((1 - x) * log (1 - x)) + e / x + (r + s * x)) x := by
    intro x hx
    have hx0 : x ≠ 0 := (hc.trans hx.1).ne'
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have h1 := ksWR_hasDerivAt_mulLog hx0
    have h := ((((hasDerivAt_id x).const_mul q).div_const 2).const_add p).mul h1
    have h2 := ((((hasDerivAt_id x).const_mul p).add (((hasDerivAt_pow 2 x).const_mul q).div_const
      4)))
    have g1 := ksWR_hasDerivAt_mulLog_one hx1
    have g2 := ((((hasDerivAt_id x).const_sub 1).div_const 2).neg.mul g1).add
      ((((hasDerivAt_id x).const_sub 1).pow 2).div_const 4)
    have g3 := g2.const_mul m
    have h5 := (hasDerivAt_log hx0).const_mul e
    have h3 := (hasDerivAt_id x).const_mul r
    have h4 := ((hasDerivAt_pow 2 x).const_mul s).div_const 2
    refine (((((h.sub h2).add g3).add h5).add h3).add h4).congr_deriv ?_
    simp only [id, Pi.neg_apply]
    push_cast
    field_simp
    ring
  have hint : IntervalIntegrable
      (fun x => (p + q * x) * log x + m * ((1 - x) * log (1 - x)) + e / x + (r + s * x))
      volume c 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hc1.le]
    have hl : ContinuousOn log (Icc c 1) :=
      continuousOn_log.mono fun x hx => (hc.trans_le hx.1).ne'
    have hi : ContinuousOn (fun x : ℝ => e / x) (Icc c 1) :=
      continuousOn_const.div continuousOn_id fun x hx => (hc.trans_le hx.1).ne'
    have hm := ksWR_continuous_mulLog_one
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add ?_ ?_) hi) ?_
    · exact (Continuous.continuousOn (by fun_prop)).mul hl
    · exact Continuous.continuousOn (by fun_prop)
    · exact Continuous.continuousOn (by fun_prop)
  rw [integral_eq_sub_of_hasDerivAt_of_le hc1.le hcont hder hint]
  simp only [hF, ksWRL, log_one, sub_self, mul_zero, log_zero]
  ring

/-- **`∫₀¹ (p + qx) log x + (n + m(1-x)) log(1-x) = -p - q/4 - n - m/4`**. -/
theorem ksWR_integral_full (p q n m : ℝ) :
    ∫ x in (0 : ℝ)..1, ((p + q * x) * log x + (n + m * (1 - x)) * log (1 - x)) =
      -p - q / 4 - n - m / 4 := by
  set F : ℝ → ℝ := fun x => (p + q * x / 2) * (x * log x) - (p * x + q * x ^ 2 / 4) +
    n * (-((1 - x) * log (1 - x)) - x) +
    m * (-((1 - x) / 2) * ((1 - x) * log (1 - x)) + (1 - x) ^ 2 / 4) with hF
  have hcont : ContinuousOn F (Icc 0 1) := by
    refine Continuous.continuousOn ?_
    have := continuous_mul_log
    have := ksWR_continuous_mulLog_one
    simp only [hF]
    fun_prop
  have hder : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F
      ((p + q * x) * log x + (n + m * (1 - x)) * log (1 - x)) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have h1 := ksWR_hasDerivAt_mulLog hx0
    have h := ((((hasDerivAt_id x).const_mul q).div_const 2).const_add p).mul h1
    have h2 := ((((hasDerivAt_id x).const_mul p).add (((hasDerivAt_pow 2 x).const_mul q).div_const
      4)))
    have g1 := ksWR_hasDerivAt_mulLog_one hx1
    have g0 := (g1.neg.sub (hasDerivAt_id x)).const_mul n
    have g2 := ((((hasDerivAt_id x).const_sub 1).div_const 2).neg.mul g1).add
      ((((hasDerivAt_id x).const_sub 1).pow 2).div_const 4)
    have g3 := g2.const_mul m
    refine (((h.sub h2).add g0).add g3).congr_deriv ?_
    simp only [id, Pi.neg_apply]
    push_cast
    field_simp
    ring
  have hint : IntervalIntegrable
      (fun x => (p + q * x) * log x + (n + m * (1 - x)) * log (1 - x)) volume 0 1 :=
    (ksWR_intervalIntegrable_linLog p q 0 1).add
      ((ksWR_intervalIntegrable_log_one 0 1).continuousOn_mul (by fun_prop))
  rw [integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hder hint]
  simp only [hF, log_one, log_zero, sub_self, sub_zero, mul_zero]
  ring

/-! ### The `x`-integral of the node density -/

/-- `ksDa1 x σ = k(σ)(1 - x)`, `k(σ) = -8σ(4σ - 3)`. -/
def ksWRk (σ : ℝ) : ℝ := -8 * σ * (4 * σ - 3)

/-- The constant `g₀` of the numerator `g = g₀ + g₁x` above the second threshold. -/
def ksWRg0 (σ a : ℝ) : ℝ :=
  48 * σ * (1 - σ) - 16 * σ ^ 2 + (2 * ksWRk σ - 16 * σ ^ 2) * a

/-- The slope `g₁` of the numerator `g = g₀ + g₁x` above the second threshold. -/
def ksWRg1 (σ a : ℝ) : ℝ := 16 * σ * (1 - σ) + 16 * σ ^ 2 + (16 * σ ^ 2 - 2 * ksWRk σ) * a

/-- **The `x`-integral of the `VA` node density** at `(σ, a)`, `c = a/(a + 1 - σ)`. -/
noncomputable def ksWRMx (σ a : ℝ) : ℝ :=
  ksWRH (a / (a + (1 - σ))) (2 * ksWRk σ * (1 - σ)) (-(2 * ksWRk σ * (1 - σ)))
      (-2 * ksWRk σ * (1 - σ) * (log (1 - σ) - log a) +
        (48 * σ * (1 - σ) - 16 * σ ^ 2) * (1 - σ) / a - 16 * σ ^ 2 * (1 - σ) +
        2 * ksWRk σ * (1 - σ))
      (2 * ksWRk σ * (1 - σ) * (log (1 - σ) - log a) +
        (16 * σ * (1 - σ) + 16 * σ ^ 2) * (1 - σ) / a + 16 * σ ^ 2 * (1 - σ) -
        2 * ksWRk σ * (1 - σ)) +
    ksWRL (a / (a + (1 - σ))) (4 * ksWRk σ * (1 - σ)) (-(4 * ksWRk σ * (1 - σ)))
      (-(2 * ksWRk σ * (1 - σ))) (ksWRg0 σ a) (ksWRg1 σ a - ksWRg0 σ a) (-ksWRg1 σ a)

theorem ksWR_branch_iff {x σ a : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ < 1) (ha : 0 < a) :
    x / (1 - x) * (1 - σ) < a ↔ x < a / (a + (1 - σ)) := by
  have h1 : 0 < 1 - x := by linarith [hx.2]
  have h2 : 0 < a + (1 - σ) := by linarith
  rw [div_mul_eq_mul_div, div_lt_iff₀ h1, lt_div_iff₀ h2]
  constructor <;> intro h <;> nlinarith

/-- The node density is interval integrable on the two pieces `(0, c)`, `(c, 1)`. -/
theorem ksWR_intervalIntegrable_ksWnAa {σ a : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) :
    IntervalIntegrable (fun x => ksWnAa x σ a) volume 0 (a / (a + (1 - σ))) ∧
      IntervalIntegrable (fun x => ksWnAa x σ a) volume (a / (a + (1 - σ))) 1 := by
  have hY : 0 < 1 - σ := by linarith [hσ.2]
  set c := a / (a + (1 - σ)) with hc
  have hc0 : 0 < c := div_pos ha (by linarith)
  have hc1 : c < 1 := (div_lt_one (by linarith)).2 (by linarith)
  set k := ksWRk σ
  have hk : ∀ x, ksDa1 x σ = k * (1 - x) := fun x => by simp only [ksDa1, k, ksWRk]; ring
  -- the two branches
  have eH : EqOn (fun x => ksWnAa x σ a) (fun x => (2 * k * (1 - σ) + -(2 * k * (1 - σ)) * x) *
      log x + ((-2 * k * (1 - σ) * (log (1 - σ) - log a) +
        (48 * σ * (1 - σ) - 16 * σ ^ 2) * (1 - σ) / a - 16 * σ ^ 2 * (1 - σ) +
        2 * k * (1 - σ)) + (2 * k * (1 - σ) * (log (1 - σ) - log a) +
        (16 * σ * (1 - σ) + 16 * σ ^ 2) * (1 - σ) / a + 16 * σ ^ 2 * (1 - σ) -
        2 * k * (1 - σ)) * x)) (Ioo 0 c) := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hc1⟩
    have hb := (ksWR_branch_iff hx' hσ.2 ha).2 hx.2
    simp only [ksWnAa, hb, ↓reduceIte, hk, ksWal, ksWbe]
    field_simp
    ring
  have eL : EqOn (fun x => ksWnAa x σ a) (fun x => (4 * k * (1 - σ) + -(4 * k * (1 - σ)) * x) *
      log x + -(2 * k * (1 - σ)) * ((1 - x) * log (1 - x)) + ksWRg0 σ a / x +
      ((ksWRg1 σ a - ksWRg0 σ a) + -ksWRg1 σ a * x)) (Ioo c 1) := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hc0.trans hx.1, hx.2⟩
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hb : ¬(x / (1 - x) * (1 - σ) < a) := fun h =>
      (lt_asymm ((ksWR_branch_iff hx' hσ.2 ha).1 h)) hx.1
    have hlog : log (x / (1 - x) * (1 - σ) / a) = log x - log (1 - x) + log (1 - σ) - log a := by
      rw [log_div (mul_pos (div_pos hx'.1 hx1) hY).ne' ha.ne',
        log_mul (div_pos hx'.1 hx1).ne' hY.ne',
        log_div hx'.1.ne' hx1.ne']
    simp only [ksWnAa, hb, ↓reduceIte, hk, ksWal, ksWbe, hlog, ksWRg0, ksWRg1, k]
    have : x ≠ 0 := hx'.1.ne'
    field_simp
    ring
  -- integrability of the two pieces
  have iH : IntervalIntegrable (fun x => ksWnAa x σ a) volume 0 c := by
    refine IntervalIntegrable.congr_uIoo ?_
      (fun x hx => (eH (by rwa [uIoo_of_le hc0.le] at hx)).symm)
    exact (ksWR_intervalIntegrable_linLog _ _ 0 c).add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  have iL : IntervalIntegrable (fun x => ksWnAa x σ a) volume c 1 := by
    refine IntervalIntegrable.congr_uIoo ?_
      (fun x hx => (eL (by rwa [uIoo_of_le hc1.le] at hx)).symm)
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hc1.le]
    have hl : ContinuousOn log (Icc c 1) :=
      continuousOn_log.mono fun x hx => (hc0.trans_le hx.1).ne'
    have hi : ContinuousOn (fun x : ℝ => ksWRg0 σ a / x) (Icc c 1) :=
      continuousOn_const.div continuousOn_id fun x hx => (hc0.trans_le hx.1).ne'
    have hm := ksWR_continuous_mulLog_one
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add ?_ ?_) hi) ?_
    · exact (Continuous.continuousOn (by fun_prop)).mul hl
    · exact Continuous.continuousOn (by fun_prop)
    · exact Continuous.continuousOn (by fun_prop)
  exact ⟨iH, iL⟩

/-- **`∫₀¹ ksWnAa x σ a dx = ksWRMx σ a`** for `σ ∈ (0, 1)`, `a > 0`. -/
theorem ksWR_integral_ksWnAa {σ a : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) :
    ∫ x in (0 : ℝ)..1, ksWnAa x σ a = ksWRMx σ a := by
  have hY : 0 < 1 - σ := by linarith [hσ.2]
  set c := a / (a + (1 - σ)) with hc
  have hc0 : 0 < c := div_pos ha (by linarith)
  have hc1 : c < 1 := (div_lt_one (by linarith)).2 (by linarith)
  set k := ksWRk σ
  have hk : ∀ x, ksDa1 x σ = k * (1 - x) := fun x => by simp only [ksDa1, k, ksWRk]; ring
  -- the two branches
  have eH : EqOn (fun x => ksWnAa x σ a) (fun x => (2 * k * (1 - σ) + -(2 * k * (1 - σ)) * x) *
      log x + ((-2 * k * (1 - σ) * (log (1 - σ) - log a) +
        (48 * σ * (1 - σ) - 16 * σ ^ 2) * (1 - σ) / a - 16 * σ ^ 2 * (1 - σ) +
        2 * k * (1 - σ)) + (2 * k * (1 - σ) * (log (1 - σ) - log a) +
        (16 * σ * (1 - σ) + 16 * σ ^ 2) * (1 - σ) / a + 16 * σ ^ 2 * (1 - σ) -
        2 * k * (1 - σ)) * x)) (Ioo 0 c) := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hc1⟩
    have hb := (ksWR_branch_iff hx' hσ.2 ha).2 hx.2
    simp only [ksWnAa, hb, ↓reduceIte, hk, ksWal, ksWbe]
    field_simp
    ring
  have eL : EqOn (fun x => ksWnAa x σ a) (fun x => (4 * k * (1 - σ) + -(4 * k * (1 - σ)) * x) *
      log x + -(2 * k * (1 - σ)) * ((1 - x) * log (1 - x)) + ksWRg0 σ a / x +
      ((ksWRg1 σ a - ksWRg0 σ a) + -ksWRg1 σ a * x)) (Ioo c 1) := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hc0.trans hx.1, hx.2⟩
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hb : ¬(x / (1 - x) * (1 - σ) < a) := fun h =>
      (lt_asymm ((ksWR_branch_iff hx' hσ.2 ha).1 h)) hx.1
    have hlog : log (x / (1 - x) * (1 - σ) / a) = log x - log (1 - x) + log (1 - σ) - log a := by
      rw [log_div (mul_pos (div_pos hx'.1 hx1) hY).ne' ha.ne',
        log_mul (div_pos hx'.1 hx1).ne' hY.ne',
        log_div hx'.1.ne' hx1.ne']
    simp only [ksWnAa, hb, ↓reduceIte, hk, ksWal, ksWbe, hlog, ksWRg0, ksWRg1, k]
    have : x ≠ 0 := hx'.1.ne'
    field_simp
    ring
  -- integrability of the two pieces
  have iH : IntervalIntegrable (fun x => ksWnAa x σ a) volume 0 c := by
    refine IntervalIntegrable.congr_uIoo ?_
      (fun x hx => (eH (by rwa [uIoo_of_le hc0.le] at hx)).symm)
    exact (ksWR_intervalIntegrable_linLog _ _ 0 c).add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  have iL : IntervalIntegrable (fun x => ksWnAa x σ a) volume c 1 := by
    refine IntervalIntegrable.congr_uIoo ?_
      (fun x hx => (eL (by rwa [uIoo_of_le hc1.le] at hx)).symm)
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hc1.le]
    have hl : ContinuousOn log (Icc c 1) :=
      continuousOn_log.mono fun x hx => (hc0.trans_le hx.1).ne'
    have hi : ContinuousOn (fun x : ℝ => ksWRg0 σ a / x) (Icc c 1) :=
      continuousOn_const.div continuousOn_id fun x hx => (hc0.trans_le hx.1).ne'
    have hm := ksWR_continuous_mulLog_one
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add ?_ ?_) hi) ?_
    · exact (Continuous.continuousOn (by fun_prop)).mul hl
    · exact Continuous.continuousOn (by fun_prop)
    · exact Continuous.continuousOn (by fun_prop)
  rw [← integral_add_adjacent_intervals iH iL, integral_congr_Ioo_of_le hc0.le eH,
    integral_congr_Ioo_of_le hc1.le eL, ksWR_integral_high hc0, ksWR_integral_low hc0 hc1]
  rfl

/-- **The threshold weight**: `∫₀¹ ksWCA x σ dx = 4σ(1-σ)(11 - 16σ)`. -/
theorem ksWR_integral_ksWCA (σ : ℝ) :
    ∫ x in (0 : ℝ)..1, ksWCA x σ = 4 * σ * (1 - σ) * (11 - 16 * σ) := by
  have e : EqOn (fun x => ksWCA x σ) (fun x => (-2 * (48 * σ * (1 - σ) - 16 * σ ^ 2) * (1 - σ) +
      -2 * (16 * σ * (1 - σ) + 16 * σ ^ 2) * (1 - σ) * x) * log x +
      ((64 * σ * (1 - σ) * (1 - σ)) + -(16 * σ * (1 - σ) + 16 * σ ^ 2) * (1 - σ) * (1 - x)) *
        log (1 - x)) (Ioo 0 1) := by
    intro x hx
    have h1 : 0 < 1 - x := by linarith [hx.2]
    simp only [ksWCA, ksWal]
    rw [log_div h1.ne' (by positivity [hx.1]), log_pow]
    push_cast
    ring
  rw [integral_congr_Ioo_of_le zero_le_one e, ksWR_integral_full]
  ring

end QED.ChainProof.SetAKS

end
