/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCAh

/-!
# Set (c), Stage K, closed forms: a bound for `S_A = ∂_v Â`

Helper level (no frozen statement). Step 3 of the `ρ_oC` route (Stage K notes, Session 29+).
The derivative `S_A = formOCSA` of the regularized `κ`-part has no sign pointwise in the `Y`
representation, so its integrability on the node triangle needs a bound. In the scaled form
every coefficient of `S_A` is a polynomial in `v` over `K Dᵏ` with `D ≥ 1`, continuous on the
compact box `[0, 1] × [0, X] × [0, V]` of `(a, x, v)` (`continuousOn_formOCSAG`); the
remaining factors `Y_c`, `x Y_c'` and `x a/E` lie in `[0, 1]`.
Hence (**`formOC_SA_bound`**) for `X < 1`, `V > 0` there is `C` with

`|S_A(a, x, v)| ≤ C (1 + |log a| + |log x| + |log v|)`, `a ∈ (0, 1)`, `x ∈ (0, X]`, `v ∈ (0, V]`.

Consequently `S_A` is integrable on `(0, V]` (**`formOC_integrableOn_SA`**), the scaled form
`formOCAhR` is continuous on `[0, ∞)` (**`continuousOn_formOCAhR`**), and
(**`formOC_AhR_ftc`**) `∫₀^V S_A = Â(V) - Â(0)` in the scaled form.
-/

@[expose] public section

open Real Set Filter MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

theorem formOC_continuousOn_rat {n : ℕ} {s : Set (ℝ × ℝ × ℝ)} (c : ℝ × ℝ × ℝ → Fin n → ℝ)
    (hc : ∀ i, ContinuousOn (fun p => c p i) s) {K : ℝ × ℝ × ℝ → ℝ} (hK : ContinuousOn K s)
    (k : ℕ) {D : ℝ × ℝ × ℝ → ℝ} (hD : ContinuousOn D s) (h0 : ∀ p ∈ s, K p * D p ^ k ≠ 0) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => formOCRat (c p) (K p) k (D p) p.2.2) s := by
  unfold formOCRat formXPol
  refine ContinuousOn.div ?_ (hK.mul (hD.pow k)) h0
  exact continuousOn_finsetSum _ fun i _ => (hc i).mul (continuous_snd.snd.pow _).continuousOn

theorem formOC_continuousOn_ratD {n : ℕ} {s : Set (ℝ × ℝ × ℝ)}
    (c : ℝ × ℝ × ℝ → Fin (n + 1) → ℝ) (hc : ∀ i, ContinuousOn (fun p => c p i) s)
    {K : ℝ × ℝ × ℝ → ℝ} (hK : ContinuousOn K s) (k : ℕ) {D δ : ℝ × ℝ × ℝ → ℝ}
    (hD : ContinuousOn D s) (hδ : ContinuousOn δ s) (h0 : ∀ p ∈ s, K p * D p ^ (k + 1) ≠ 0) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => formOCRatD (c p) (K p) k (D p) (δ p) p.2.2) s := by
  unfold formOCRatD formXPol formXPolD
  refine ContinuousOn.div ?_ (hK.mul (hD.pow (k + 1))) h0
  refine ContinuousOn.sub ?_ ?_
  · refine ContinuousOn.mul ?_ hD
    exact continuousOn_finsetSum _ fun i _ =>
      (continuousOn_const.mul (hc i.succ)).mul (continuous_snd.snd.pow _).continuousOn
  · exact (continuousOn_const.mul hδ).mul
      (continuousOn_finsetSum _ fun i _ => (hc i).mul (continuous_snd.snd.pow _).continuousOn)

/-- The atoms `(x, a, Q(x), D₀)` of the coefficient vectors, continuous where `x ≠ 1`. -/
theorem formOC_continuousOn_atoms {s : Set (ℝ × ℝ × ℝ)} (hs : ∀ p ∈ s, p.2.1 < 1) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => (p.2.1, p.1, setCKQ p.2.1, formOCD0 p.1 p.2.1)) s := by
  have hQ : ContinuousOn (fun p : ℝ × ℝ × ℝ => setCKQ p.2.1) s := by
    unfold setCKQ
    exact ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp => by linarith [hs p hp]
  refine continuous_snd.fst.continuousOn.prodMk (continuous_fst.continuousOn.prodMk
    (hQ.prodMk ?_))
  unfold formOCD0
  exact continuousOn_const.add ((continuous_fst.mul (continuous_const.sub
    continuous_fst)).continuousOn.mul hQ)

theorem formOC_continuousOn_vec {n : ℕ} {s : Set (ℝ × ℝ × ℝ)} (hs : ∀ p ∈ s, p.2.1 < 1)
    (c : ℝ → ℝ → ℝ → ℝ → Fin n → ℝ)
    (hc : ∀ i, Continuous fun r : ℝ × ℝ × ℝ × ℝ => c r.1 r.2.1 r.2.2.1 r.2.2.2 i) (i : Fin n) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => c p.2.1 p.1 (setCKQ p.2.1) (formOCD0 p.1 p.2.1) i) s :=
  (hc i).comp_continuousOn (formOC_continuousOn_atoms hs)

theorem formOC_cont_R0N (i : Fin 3) :
    Continuous fun r : ℝ × ℝ × ℝ × ℝ => formOCR0N r.1 r.2.1 r.2.2.1 r.2.2.2 i := by
  fin_cases i <;> simp [formOCR0N] <;> fun_prop

theorem formOC_cont_P0xN (i : Fin 3) :
    Continuous fun r : ℝ × ℝ × ℝ × ℝ => formOCP0xN r.1 r.2.1 r.2.2.1 r.2.2.2 i := by
  fin_cases i <;> simp [formOCP0xN] <;> fun_prop

theorem formOC_cont_P1xN (i : Fin 2) :
    Continuous fun r : ℝ × ℝ × ℝ × ℝ => formOCP1xN r.1 r.2.1 r.2.2.1 r.2.2.2 i := by
  fin_cases i <;> simp [formOCP1xN] <;> fun_prop

theorem formOC_cont_N1xN (i : Fin 3) :
    Continuous fun r : ℝ × ℝ × ℝ × ℝ => formOCN1xN r.1 r.2.1 r.2.2.1 r.2.2.2 i := by
  fin_cases i <;> simp [formOCN1xN] <;> fun_prop

theorem formOC_cont_m1N (i : Fin 2) :
    Continuous fun r : ℝ × ℝ × ℝ × ℝ => formOCm1N r.1 r.2.1 r.2.2.1 r.2.2.2 i := by
  fin_cases i <;> simp [formOCm1N] <;> fun_prop

/-- The box `[0, 1] × [0, X] × [0, V]` of `(a, x, v)`. -/
def formOCBox (X V : ℝ) : Set (ℝ × ℝ × ℝ) := Icc 0 1 ×ˢ (Icc 0 X ×ˢ Icc 0 V)

theorem isCompact_formOCBox (X V : ℝ) : IsCompact (formOCBox X V) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

/-- The sum of the absolute values of the coefficient functions of `S_A`. -/
noncomputable def formOCSAG (p : ℝ × ℝ × ℝ) : ℝ :=
  |formOCdR0 p.1 p.2.1 p.2.2| + |formOCdP0x p.1 p.2.1 p.2.2| + |formOCP0x p.1 p.2.1 p.2.2| +
    |formOCdP1x p.1 p.2.1 p.2.2| + |formOCP1x p.1 p.2.1 p.2.2| + |formOCdN1x p.1 p.2.1 p.2.2| +
    |formOCN1x p.1 p.2.1 p.2.2| + |formOCm1 p.1 p.2.1 p.2.2| + |formOCdm1 p.1 p.2.1 p.2.2|

theorem continuousOn_formOCSAG {X V : ℝ} (hX : X < 1) :
    ContinuousOn formOCSAG (formOCBox X V) := by
  set s := formOCBox X V
  have hs : ∀ p ∈ s, p.2.1 < 1 := fun p hp => lt_of_le_of_lt hp.2.1.2 hX
  have hQ : ContinuousOn (fun p : ℝ × ℝ × ℝ => setCKQ p.2.1) s := by
    unfold setCKQ
    exact ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp => by linarith [hs p hp]
  have hD0 : ContinuousOn (fun p : ℝ × ℝ × ℝ => formOCD0 p.1 p.2.1) s := by
    unfold formOCD0
    exact continuousOn_const.add ((continuous_fst.mul (continuous_const.sub
      continuous_fst)).continuousOn.mul hQ)
  have hD : ContinuousOn (fun p : ℝ × ℝ × ℝ => formOCD p.1 p.2.1 p.2.2) s := by
    unfold formOCD
    exact continuousOn_const.add ((continuous_fst.mul (continuous_const.sub
      continuous_fst)).continuousOn.mul (hQ.add continuous_snd.snd.continuousOn))
  have hδ : ContinuousOn (fun p : ℝ × ℝ × ℝ => p.1 * (1 - p.1)) s := by fun_prop
  have hpos : ∀ p ∈ s, 0 < formOCD p.1 p.2.1 p.2.2 ∧ 0 < formOCD0 p.1 p.2.1 ∧
      p.2.1 - 1 ≠ 0 := by
    intro p hp
    have hq := setCKQ_nonneg ⟨hp.2.1.1, (hs p hp).le⟩
    have h1 : 0 ≤ p.1 * (1 - p.1) := mul_nonneg hp.1.1 (by linarith [hp.1.2])
    refine ⟨?_, ?_, by linarith [hs p hp]⟩
    · unfold formOCD
      have := hp.2.2.1
      positivity
    · unfold formOCD0
      positivity
  have hK : ∀ (c : ℝ) (k : ℕ), c ≠ 0 → ∀ p ∈ s,
      c * formOCD0 p.1 p.2.1 * (p.2.1 - 1) * formOCD p.1 p.2.1 p.2.2 ^ k ≠ 0 := by
    intro c k hc p hp
    obtain ⟨h1, h2, h3⟩ := hpos p hp
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc h2.ne') h3) (pow_ne_zero _ h1.ne')
  have hK' : ∀ (c : ℝ) (k : ℕ), c ≠ 0 → ∀ p ∈ s,
      c * formOCD0 p.1 p.2.1 * formOCD p.1 p.2.1 p.2.2 ^ k ≠ 0 := by
    intro c k hc p hp
    obtain ⟨h1, h2, -⟩ := hpos p hp
    exact mul_ne_zero (mul_ne_zero hc h2.ne') (pow_ne_zero _ h1.ne')
  have hKc : ∀ c : ℝ, ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      c * formOCD0 p.1 p.2.1 * (p.2.1 - 1)) s := fun c =>
    (continuousOn_const.mul hD0).mul (continuous_snd.fst.continuousOn.sub continuousOn_const)
  have hKc' : ∀ c : ℝ, ContinuousOn (fun p : ℝ × ℝ × ℝ => c * formOCD0 p.1 p.2.1) s :=
    fun c => continuousOn_const.mul hD0
  have vR0 := formOC_continuousOn_vec hs formOCR0N formOC_cont_R0N
  have vP0 := formOC_continuousOn_vec hs formOCP0xN formOC_cont_P0xN
  have vP1 := formOC_continuousOn_vec hs formOCP1xN formOC_cont_P1xN
  have vN1 := formOC_continuousOn_vec hs formOCN1xN formOC_cont_N1xN
  have vm1 := formOC_continuousOn_vec hs formOCm1N formOC_cont_m1N
  have cdR0 := formOC_continuousOn_ratD _ vR0 (hKc 8) 2 hD hδ (hK 8 3 (by norm_num))
  have cdP0 := formOC_continuousOn_ratD _ vP0 (hKc 2) 2 hD hδ (hK 2 3 (by norm_num))
  have cP0 := formOC_continuousOn_rat _ vP0 (hKc 2) 2 hD (hK 2 2 (by norm_num))
  have cdP1 := formOC_continuousOn_ratD _ vP1 (hKc' 2) 1 hD hδ (hK' 2 2 (by norm_num))
  have cP1 := formOC_continuousOn_rat _ vP1 (hKc' 2) 1 hD (hK' 2 1 (by norm_num))
  have cdN1 := formOC_continuousOn_ratD _ vN1 (hKc 4) 2 hD hδ (hK 4 3 (by norm_num))
  have cN1 := formOC_continuousOn_rat _ vN1 (hKc 4) 2 hD (hK 4 2 (by norm_num))
  have cm1 := formOC_continuousOn_rat _ vm1 (hKc 4) 2 hD (hK 4 2 (by norm_num))
  have cdm1 := formOC_continuousOn_ratD _ vm1 (hKc 4) 2 hD hδ (hK 4 3 (by norm_num))
  unfold formOCSAG formOCdR0 formOCdP0x formOCP0x formOCdP1x formOCP1x formOCdN1x formOCN1x
    formOCm1 formOCdm1
  exact ((((((((cdR0.abs.add cdP0.abs).add cP0.abs).add cdP1.abs).add cP1.abs).add
    cdN1.abs).add cN1.abs).add cm1.abs).add cdm1.abs)

theorem formOC_abs_mul_le {u w G : ℝ} (hu : |u| ≤ G) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    |u * w| ≤ G := by
  rw [abs_mul, abs_of_nonneg hw0]
  nlinarith [abs_nonneg u]

section

variable {a x v X V : ℝ}

theorem formOC_x_dc_le (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 ≤ v) :
    0 ≤ x * formOCdc a x v ∧ x * formOCdc a x v ≤ 1 := by
  have hE := formOCE_pos ha hx hv
  have hq := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hL : 0 < 1 - a * x := by nlinarith [ha.1, ha.2, hx.1, hx.2]
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have hxq : 0 ≤ x + a * setCKQ x := by have := ha.1; have := hx.1; positivity
  have hE1 : x + a * setCKQ x ≤ formOCE a x v := by
    unfold formOCE; nlinarith [ha.1]
  have hE2 : x ≤ formOCE a x v := by linarith [mul_nonneg ha.1.le hq]
  unfold formOCdc
  constructor
  · have := ha.1; have := hx.1; positivity
  · rw [mul_div_assoc', div_le_one (by positivity)]
    have h3 : x * (x + a * setCKQ x) ≤ formOCE a x v ^ 2 := by
      rw [sq]; exact mul_le_mul hE2 hE1 hxq hE.le
    have h4 : a * (1 - x) ≤ 1 - a * x := by nlinarith [ha.2]
    calc x * (a * (1 - x) * (x + a * setCKQ x))
        = (a * (1 - x)) * (x * (x + a * setCKQ x)) := by ring
      _ ≤ (1 - a * x) * formOCE a x v ^ 2 :=
        mul_le_mul h4 h3 (mul_nonneg hx.1.le hxq) hL.le

theorem formOC_x_aE_le (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 ≤ v) :
    0 ≤ x * (a / formOCE a x v) ∧ x * (a / formOCE a x v) ≤ 1 := by
  have hE := formOCE_pos ha hx hv
  have hq := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hE2 : x ≤ formOCE a x v := by
    unfold formOCE; nlinarith [mul_nonneg ha.1.le hq, mul_nonneg ha.1.le hv]
  constructor
  · have := ha.1; have := hx.1; positivity
  · rw [mul_div_assoc', div_le_one hE]
    nlinarith [ha.2, hx.1]

theorem formOC_abs_log_lam_le (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioc (0 : ℝ) X) (hX : X < 1)
    (hv : v ∈ Ioc (0 : ℝ) V) :
    |log (formOClam a x v)| ≤
      |log a| + |log x| + (2 * -log (1 - X) + log (1 + setCKQ X + V)) := by
  have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_lt hx.2 hX⟩
  have hE := formOCE_pos ha hx' hv.1.le
  have hq := setCKQ_nonneg ⟨hx.1.le, hx'.2.le⟩
  have hqX : setCKQ x ≤ setCKQ X := by
    rcases hx.2.lt_or_eq with h | h
    · exact (setCKQ_lt hx.1.le h hX).le
    · rw [h]
  have h1x : 0 < 1 - x := by linarith [hx'.2]
  have hL : 0 < 1 - a * x := by nlinarith [ha.1, ha.2, hx'.1, hx'.2]
  have hlam : log (formOClam a x v) =
      log a + log (1 - x) - log (1 - a * x) - log (formOCE a x v) := by
    unfold formOClam
    rw [log_div (mul_pos ha.1 h1x).ne' (mul_pos hL hE).ne', log_mul ha.1.ne' h1x.ne',
      log_mul hL.ne' hE.ne']
    ring
  have h1X : 0 < 1 - X := by linarith
  have hl1 : |log (1 - x)| ≤ -log (1 - X) := by
    rw [abs_of_nonpos (log_nonpos h1x.le (by linarith [hx.1]))]
    exact neg_le_neg (log_le_log h1X (by linarith [hx.2]))
  have hl2 : |log (1 - a * x)| ≤ -log (1 - X) := by
    rw [abs_of_nonpos (log_nonpos hL.le (by nlinarith [ha.1, hx.1]))]
    exact neg_le_neg (log_le_log h1X (by nlinarith [ha.2, hx.2, hx.1]))
  have hE1 : formOCE a x v ≤ 1 + setCKQ X + V := by
    have h5 : a * (setCKQ x + v) ≤ setCKQ x + v := by
      nlinarith [ha.2, add_nonneg hq hv.1.le]
    unfold formOCE
    linarith [hx'.2, hv.2]
  have hE2 : x ≤ formOCE a x v := by
    unfold formOCE; nlinarith [mul_nonneg ha.1.le (add_nonneg hq hv.1.le)]
  have hl3 : |log (formOCE a x v)| ≤ |log x| + log (1 + setCKQ X + V) := by
    have hu : log (formOCE a x v) ≤ log (1 + setCKQ X + V) := log_le_log hE hE1
    have hd : log x ≤ log (formOCE a x v) := log_le_log hx.1 hE2
    have h0 : 0 ≤ log (1 + setCKQ X + V) := log_nonneg (by linarith [hv.1, hv.2, hq, hqX])
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (log x)]
    · linarith [abs_nonneg (log x)]
  rw [hlam]
  have t1 := abs_add_le (log a) (log (1 - x))
  have t2 := abs_sub (log a + log (1 - x)) (log (1 - a * x))
  have t3 := abs_sub (log a + log (1 - x) - log (1 - a * x)) (log (formOCE a x v))
  linarith

theorem formOCSAG_ge (p : ℝ × ℝ × ℝ) :
    |formOCdR0 p.1 p.2.1 p.2.2| ≤ formOCSAG p ∧ |formOCdP0x p.1 p.2.1 p.2.2| ≤ formOCSAG p ∧
      |formOCP0x p.1 p.2.1 p.2.2| ≤ formOCSAG p ∧ |formOCdP1x p.1 p.2.1 p.2.2| ≤ formOCSAG p ∧
      |formOCP1x p.1 p.2.1 p.2.2| ≤ formOCSAG p ∧ |formOCdN1x p.1 p.2.1 p.2.2| ≤ formOCSAG p ∧
      |formOCN1x p.1 p.2.1 p.2.2| ≤ formOCSAG p ∧ |formOCm1 p.1 p.2.1 p.2.2| ≤ formOCSAG p ∧
      |formOCdm1 p.1 p.2.1 p.2.2| ≤ formOCSAG p := by
  have := abs_nonneg (formOCdR0 p.1 p.2.1 p.2.2)
  have := abs_nonneg (formOCdP0x p.1 p.2.1 p.2.2)
  have := abs_nonneg (formOCP0x p.1 p.2.1 p.2.2)
  have := abs_nonneg (formOCdP1x p.1 p.2.1 p.2.2)
  have := abs_nonneg (formOCP1x p.1 p.2.1 p.2.2)
  have := abs_nonneg (formOCdN1x p.1 p.2.1 p.2.2)
  have := abs_nonneg (formOCN1x p.1 p.2.1 p.2.2)
  have := abs_nonneg (formOCm1 p.1 p.2.1 p.2.2)
  have := abs_nonneg (formOCdm1 p.1 p.2.1 p.2.2)
  unfold formOCSAG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **The bound for `S_A`.** -/
theorem formOC_SA_bound (hX : X < 1) (hV : 0 < V) :
    ∃ C, 0 ≤ C ∧ ∀ a ∈ Ioo (0 : ℝ) 1, ∀ x ∈ Ioc (0 : ℝ) X, ∀ v ∈ Ioc (0 : ℝ) V,
      |formOCSA a x v| ≤ C * (1 + |log a| + |log x| + |log v|) := by
  obtain ⟨G0, hG0⟩ := (isCompact_formOCBox X V).exists_bound_of_continuousOn
    (continuousOn_formOCSAG (V := V) hX)
  set C1 := 2 * -log (1 - X) + log (1 + setCKQ X + V) with hC1
  set G1 := max G0 0 with hG1
  have hG10 : 0 ≤ G1 := le_max_right _ _
  refine ⟨G1 * (8 + |C1| + V), by positivity, fun a ha x hx v hv => ?_⟩
  have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_lt hx.2 hX⟩
  have hp : (a, x, v) ∈ formOCBox X V :=
    ⟨⟨ha.1.le, ha.2.le⟩, ⟨hx.1.le, hx.2⟩, ⟨hv.1.le, hv.2⟩⟩
  have hG : formOCSAG (a, x, v) ≤ G1 := by
    have := hG0 _ hp
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := formOCSAG_ge (a, x, v)
  have hc0 := formOCYc_pos ha hx' hv.1
  have hc1 := formOCYc_lt_one ha hx' hv.1
  obtain ⟨hd0, hd1⟩ := formOC_x_dc_le ha hx' hv.1.le
  obtain ⟨he0, he1⟩ := formOC_x_aE_le ha hx' hv.1.le
  have hl := formOC_abs_log_lam_le ha hx hX hv
  set c := formOCYc a x v
  set dc := formOCdc a x v
  have b2 : |x * (formOCdP0x a x v * c + formOCP0x a x v * dc)| ≤ G1 + G1 := by
    have e : x * (formOCdP0x a x v * c + formOCP0x a x v * dc) =
        formOCdP0x a x v * (x * c) + formOCP0x a x v * (x * dc) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact formOC_abs_mul_le (g2.trans hG) (mul_nonneg hx'.1.le hc0.le) (by nlinarith [hx'.2])
    · exact formOC_abs_mul_le (g3.trans hG) hd0 hd1
  have b3 : |x * (formOCdP1x a x v * c ^ 2 / 2 + formOCP1x a x v * c * dc)| ≤ G1 + G1 := by
    have e : x * (formOCdP1x a x v * c ^ 2 / 2 + formOCP1x a x v * c * dc) =
        formOCdP1x a x v * (x * c ^ 2 / 2) + formOCP1x a x v * (c * (x * dc)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine formOC_abs_mul_le (g4.trans hG) (by have := hx'.1; positivity) ?_
      nlinarith [hx'.2, mul_lt_mul'' hc1 hc1 hc0.le hc0.le]
    · exact formOC_abs_mul_le (g5.trans hG) (mul_nonneg hc0.le hd0) (by nlinarith)
  have b4 : |x * formOCdN1x a x v * log (formOClam a x v)| ≤ G1 * |log (formOClam a x v)| := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [mul_comm]
    exact formOC_abs_mul_le (g6.trans hG) hx'.1.le hx'.2.le
  have b5 : |x * formOCN1x a x v * (a / formOCE a x v)| ≤ G1 := by
    have e : x * formOCN1x a x v * (a / formOCE a x v) =
        formOCN1x a x v * (x * (a / formOCE a x v)) := by ring
    rw [e]
    exact formOC_abs_mul_le (g7.trans hG) he0 he1
  have b6 : |(formOCm1 a x v + v * formOCdm1 a x v) * log v| ≤ G1 * (1 + V) * |log v| := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hv.1]
    nlinarith [g8.trans hG, g9.trans hG, abs_nonneg (formOCdm1 a x v), hv.2]
  have b1 := g1.trans hG
  have b7 := g8.trans hG
  have htot : |formOCSA a x v| ≤
      7 * G1 + G1 * |log (formOClam a x v)| + G1 * (1 + V) * |log v| := by
    unfold formOCSA
    obtain ⟨l1, u1⟩ := abs_le.1 b1
    obtain ⟨l2, u2⟩ := abs_le.1 b2
    obtain ⟨l3, u3⟩ := abs_le.1 b3
    obtain ⟨l4, u4⟩ := abs_le.1 b4
    obtain ⟨l5, u5⟩ := abs_le.1 b5
    obtain ⟨l6, u6⟩ := abs_le.1 b6
    obtain ⟨l7, u7⟩ := abs_le.1 b7
    rw [abs_le]
    constructor <;> linarith
  have hA := abs_nonneg (log a)
  have hB := abs_nonneg (log x)
  have hCv := abs_nonneg (log v)
  have key : 7 + (|log a| + |log x| + C1) + (1 + V) * |log v| ≤
      (8 + |C1| + V) * (1 + |log a| + |log x| + |log v|) := by
    nlinarith [le_abs_self C1, abs_nonneg C1]
  calc |formOCSA a x v| ≤ 7 * G1 + G1 * |log (formOClam a x v)| + G1 * (1 + V) * |log v| :=
        htot
    _ ≤ G1 * (7 + (|log a| + |log x| + C1) + (1 + V) * |log v|) := by
        nlinarith [mul_le_mul_of_nonneg_left hl hG10]
    _ ≤ G1 * ((8 + |C1| + V) * (1 + |log a| + |log x| + |log v|)) :=
        mul_le_mul_of_nonneg_left key hG10
    _ = _ := by ring

end

theorem formOC_continuousOn_rat1 {n : ℕ} (c : Fin n → ℝ) (K : ℝ) (k : ℕ) {D : ℝ → ℝ}
    (hD : Continuous D) {s : Set ℝ} (h0 : ∀ v ∈ s, K * D v ^ k ≠ 0) :
    ContinuousOn (fun v => formOCRat c K k (D v) v) s := by
  unfold formOCRat formXPol
  exact ContinuousOn.div (by fun_prop) (by fun_prop) h0

section

variable {a x V : ℝ}

theorem formOC_continuous_D (a x : ℝ) : Continuous (formOCD a x) := by
  unfold formOCD
  fun_prop

/-- **The scaled form of `Â` is continuous on `[0, ∞)`.** -/
theorem continuousOn_formOCAhR (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (formOCAhR a x) (Ici 0) := by
  have hD0 := (formOCD0_pos ha hx).ne'
  have hx1 : x - 1 ≠ 0 := by linarith [hx.2]
  have hDv : ∀ v ∈ Ici (0 : ℝ), formOCD a x v ^ 1 ≠ 0 ∧ formOCD a x v ^ 2 ≠ 0 := fun v hv =>
    ⟨pow_ne_zero _ (formOCD_pos' ha hx hv).ne', pow_ne_zero _ (formOCD_pos' ha hx hv).ne'⟩
  have cD := formOC_continuous_D a x
  have hR0 : ContinuousOn (formOCR0 a x) (Ici 0) :=
    formOC_continuousOn_rat1 _ _ 2 cD fun v hv => mul_ne_zero (by positivity) (hDv v hv).2
  have hP0 : ContinuousOn (formOCP0x a x) (Ici 0) :=
    formOC_continuousOn_rat1 _ _ 2 cD fun v hv => mul_ne_zero (by positivity) (hDv v hv).2
  have hP1 : ContinuousOn (formOCP1x a x) (Ici 0) :=
    formOC_continuousOn_rat1 _ _ 1 cD fun v hv => mul_ne_zero (by positivity) (hDv v hv).1
  have hN1 : ContinuousOn (formOCN1x a x) (Ici 0) :=
    formOC_continuousOn_rat1 _ _ 2 cD fun v hv => mul_ne_zero (by positivity) (hDv v hv).2
  have hm1 : ContinuousOn (formOCm1 a x) (Ici 0) :=
    formOC_continuousOn_rat1 _ _ 2 cD fun v hv => mul_ne_zero (by positivity) (hDv v hv).2
  have hL : 1 - a * x ≠ 0 := by nlinarith [ha.1, ha.2, hx.1, hx.2]
  have hYc : ContinuousOn (formOCYc a x) (Ici 0) := by
    unfold formOCYc
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun v hv => mul_ne_zero hL ?_
    exact (formOCE_pos ha hx hv).ne'
  have hlam : ContinuousOn (fun v => log (formOClam a x v)) (Ici 0) := by
    refine ContinuousOn.log ?_ fun v hv => (formOClam_pos ha hx hv).ne'
    unfold formOClam formOCE
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun v hv => mul_ne_zero hL ?_
    exact (formOCE_pos ha hx hv).ne'
  unfold formOCAhR
  exact ((((hR0.sub ((continuousOn_const.mul hP0).mul hYc)).sub
    (((continuousOn_const.mul hP1).mul (hYc.pow 2)).div_const 2)).sub
    ((continuousOn_const.mul hN1).mul hlam)).sub
    (hm1.mul Real.continuous_mul_log.continuousOn))

/-- **`S_A` is integrable on `(0, V]`** (from `formOC_SA_bound`). -/
theorem formOC_integrableOn_SA (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hV : 0 < V) :
    IntegrableOn (formOCSA a x) (Ioc 0 V) := by
  obtain ⟨C, hC0, hC⟩ := formOC_SA_bound (X := x) (V := V) hx.2 hV
  have hlog : IntegrableOn (fun v => |log v|) (Ioc 0 V) :=
    ((intervalIntegral.intervalIntegrable_log' (a := 0) (b := V)).1).abs
  have hg : IntegrableOn (fun v => C * (1 + |log a| + |log x| + |log v|)) (Ioc 0 V) := by
    refine Integrable.const_mul ?_ C
    exact (integrableOn_const (by simp)).add hlog
  have hm : AEStronglyMeasurable (formOCSA a x) (volume.restrict (Ioc 0 V)) := by
    refine (measurable_deriv (formOCAhR a x)).aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact (hasDerivAt_formOCAhR ha hx hv.1).deriv
  refine Integrable.mono' hg hm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  rw [Real.norm_eq_abs]
  exact hC a ha x ⟨hx.1, le_rfl⟩ v hv

/-- **FTC for `Â`**: `Â(V) - Â(0) = ∫₀^V S_A`, in the scaled form. -/
theorem formOC_AhR_ftc (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hV : 0 < V) :
    ∫ v in Ioc 0 V, formOCSA a x v = formOCAhR a x V - formOCAhR a x 0 := by
  rw [← intervalIntegral.integral_of_le hV.le]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hV.le
    ((continuousOn_formOCAhR ha hx).mono Icc_subset_Ici_self)
    (fun v hv => hasDerivAt_formOCAhR ha hx hv.1) ?_
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hV.le).2 (formOC_integrableOn_SA ha hx hV)

end

end QED.ChainProof.SetCK

end
