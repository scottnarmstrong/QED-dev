/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.OneLoopClosedForm
public import QED.DimReg.Continuation
public import QED.Algebra.IBPCertPilot
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Meromorphic.Complex

/-!
# The one-loop on-shell self-energy: the certified IBP reduction for the actual integrals

End to end for the checker's pilot family `QED.Algebra.IBPCert.Pilot.oneLoopSE`: the IBP
relations proved for the Schwinger integral inside its region of convergence
(`QED.DimReg.OneLoopSchwinger.schw_rel₀₀`, `schw_rel₀₁`; B1 + B2) are continued to the integer
labels the checker uses (B4), and then fed to the landed certificate
`QED.Algebra.IBPCert.Pilot.oneLoop_reduction₁₁`.

**The values.** `val ν d = (-1)^{ν₀+ν₁} φ(ν₀, ν₁; d)` for `ν ∈ ℤ²`, where
`φ = Γ(a + b - d/2) Γ(d - 2a - b) / (Γ(b) Γ(d - a - b))` equals the Γ-normalized Schwinger
integral wherever that converges (`QED.DimReg.OneLoopSchwinger.schw_eq_phi`) and is meromorphic
in each variable: `val` is the analytically regularized integral of the Minkowski family.

**Continuation (B4).** Fix integers `(n₀, n₁)` and `d ∉ ℤ`. On the complex line
`λ ↦ (n₀ + 2λ, n₁ + 6λ, d + 15λ)` every label of both relations converges once
`re λ > lineBound`, since the three convergence conditions have slopes `2`, `1/2`, `5`. There the
relation holds by B1 + B2; it is a meromorphic function of `λ`, continuous at `λ = 0` because
`d ∉ ℤ` keeps every Γ argument off the poles, so `QED.DimReg.Meromorphic.eq_of_eqOn` gives it at
`λ = 0` (`phi_rel₀₀`, `phi_rel₀₁`). Hence `val` satisfies **all** relations,
`oneLoopSE.IBPHolds val d` (`ibpHolds_val`), not just those at the seeds.

**Scaleless sector (R3).** The declared zero sector `ν₁ ≤ 0` is a theorem about the
continuation: `φ` carries the entire factor `Γ(ν₁)⁻¹`, which vanishes at `ν₁ ∈ {0, -1, …}`
(`zeroSectors_val`). No convention is used. For the certificate `oneLoopCert₁₁` the one
scaleless label `(1, 0)` occurs only with coefficient `-2ν₀ = 0` at its seed.

## Main results

* `QED.DimReg.OneLoopSchwinger.ibpHolds_val`, `zeroSectors_val`: the checker's hypotheses.
* `QED.DimReg.OneLoopSchwinger.val_reduction₁₁`: `I(1, 1) = (d - 2)/(2(d - 3)) · I(0, 1)` for
  `d ∉ ℤ`, from the kernel-checked certificate.
* `QED.DimReg.OneLoopSchwinger.integral_kernel_eq`: for `3 < re d < 4`,
  `∫_{(0,∞)²} U^{-d/2} e^{-F/U} dx = -(d - 2)/(2(d - 3)) · Γ(1 - d/2)`, with
  `Γ(1 - d/2) = ∫₀^∞ S(0, x₁) dx₁` for `re d < 2` (`integral_kernel_face`).
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology

namespace QED.DimReg.OneLoopSchwinger

/-! ### `phi` along analytic curves -/

theorem meromorphicAt_phi_comp {f g h : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hg : AnalyticAt ℂ g z) (hh : AnalyticAt ℂ h z) :
    MeromorphicAt (fun s => phi (f s) (g s) (h s)) z := by
  have hG : ∀ {k : ℂ → ℂ}, AnalyticAt ℂ k z → MeromorphicAt (fun s => Gamma (k s)) z :=
    fun hk => (Meromorphic.Gamma _).comp_analyticAt hk
  have hI : ∀ {k : ℂ → ℂ}, AnalyticAt ℂ k z → MeromorphicAt (fun s => (Gamma (k s))⁻¹) z :=
    fun hk => ((differentiable_one_div_Gamma.analyticAt _).comp hk).meromorphicAt
  unfold phi
  exact (((hG (by fun_prop)).mul (hG (by fun_prop))).mul (hI hg)).mul (hI (by fun_prop))

theorem continuousAt_phi_comp {f g h : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z)
    (hg : ContinuousAt g z) (hh : ContinuousAt h z)
    (h₁ : ∀ m : ℕ, f z + g z - h z / 2 ≠ -m) (h₂ : ∀ m : ℕ, h z - 2 * f z - g z ≠ -m) :
    ContinuousAt (fun s => phi (f s) (g s) (h s)) z := by
  have hI : ∀ {k : ℂ → ℂ}, ContinuousAt k z → ContinuousAt (fun s => (Gamma (k s))⁻¹) z :=
    fun hk => differentiable_one_div_Gamma.continuous.continuousAt.comp hk
  have h1 : ContinuousAt (fun s => Gamma (f s + g s - h s / 2)) z :=
    (differentiableAt_Gamma _ h₁).continuousAt.comp
      (f := fun s => f s + g s - h s / 2) (by fun_prop)
  have h2 : ContinuousAt (fun s => Gamma (h s - 2 * f s - g s)) z :=
    (differentiableAt_Gamma _ h₂).continuousAt.comp
      (f := fun s => h s - 2 * f s - g s) (by fun_prop)
  unfold phi
  exact ((h1.mul h2).mul (hI hg)).mul (hI (by fun_prop))

/-! ### The relations off the region of convergence (B4) -/

/-- The bound beyond which the line `λ ↦ (n₀ + 2λ, n₁ + 6λ, d + 15λ)` lies in the region where
all labels of both relations converge. -/
noncomputable def lineBound (n₀ n₁ : ℤ) (d : ℂ) : ℝ := 2 * (|(n₀ : ℝ)| + |(n₁ : ℝ)| + |d.re|) + 4

theorem line_good {n₀ n₁ : ℤ} {d l : ℂ} (hl : lineBound n₀ n₁ d < l.re) {a' b' : ℂ}
    (ha : |(a' - (n₀ + l * 2)).re| ≤ 1) (hb : |(b' - (n₁ + l * 6)).re| ≤ 1) :
    0 < a'.re ∧ 0 < (a' + b' - (d + l * 15) / 2).re ∧ 0 < (d + l * 15 - 2 * a' - b').re := by
  unfold lineBound at hl
  rw [abs_le] at ha hb
  simp only [sub_re, add_re, mul_re, intCast_re, re_ofNat, im_ofNat, mul_zero,
    sub_zero, div_ofNat_re] at ha hb ⊢
  have e₀ := le_abs_self (n₀ : ℝ)
  have e₁ := neg_abs_le (n₀ : ℝ)
  have e₂ := le_abs_self (n₁ : ℝ)
  have e₃ := neg_abs_le (n₁ : ℝ)
  have e₄ := le_abs_self d.re
  have e₅ := neg_abs_le d.re
  refine ⟨by linarith, by linarith, by linarith⟩

theorem line_gt_one {n₀ n₁ : ℤ} {d l : ℂ} (hl : lineBound n₀ n₁ d < l.re) :
    1 < ((n₀ : ℂ) + l * 2).re ∧ 1 < ((n₁ : ℂ) + l * 6).re := by
  unfold lineBound at hl
  simp only [add_re, mul_re, intCast_re, re_ofNat, im_ofNat, mul_zero, sub_zero]
  have e₁ := neg_abs_le (n₀ : ℝ)
  have e₃ := neg_abs_le (n₁ : ℝ)
  have := abs_nonneg d.re
  have := abs_nonneg (n₀ : ℝ)
  have := abs_nonneg (n₁ : ℝ)
  constructor <;> linarith

theorem nonempty_lineRegion (n₀ n₁ : ℤ) (d : ℂ) :
    {l : ℂ | lineBound n₀ n₁ d < l.re}.Nonempty :=
  ⟨(lineBound n₀ n₁ d + 1 : ℝ), by simp⟩

theorem isOpen_lineRegion (n₀ n₁ : ℤ) (d : ℂ) : IsOpen {l : ℂ | lineBound n₀ n₁ d < l.re} :=
  isOpen_lt continuous_const continuous_re

/-- The Γ arguments of `phi` at an integer label avoid the poles when `d ∉ ℤ`. -/
theorem phi_args {d : ℂ} (hd : ∀ n : ℤ, d ≠ n) (a b : ℤ) :
    (∀ m : ℕ, (a : ℂ) + b - d / 2 ≠ -m) ∧ (∀ m : ℕ, d - 2 * a - b ≠ -m) := by
  constructor
  · intro m h
    apply hd (2 * (a + b + m))
    push_cast
    linear_combination -2 * h
  · intro m h
    apply hd (2 * a + b - m)
    push_cast
    linear_combination h

/-- The line `λ ↦ m + 2λ` in the first exponent. -/
def lineA (m : ℤ) (l : ℂ) : ℂ := m + l * 2

/-- The line `λ ↦ m + 6λ` in the second exponent. -/
def lineB (m : ℤ) (l : ℂ) : ℂ := m + l * 6

/-- The line `λ ↦ d + 15λ` in the dimension. -/
def lineD (d l : ℂ) : ℂ := d + l * 15

/-- `phi` along the line through the integer label `(m₀, m₁)` at dimension `d`. -/
noncomputable def phiLine (m₀ m₁ : ℤ) (d l : ℂ) : ℂ := phi (lineA m₀ l) (lineB m₁ l) (lineD d l)

theorem meromorphic_phiLine (m₀ m₁ : ℤ) (d : ℂ) : Meromorphic (phiLine m₀ m₁ d) := fun z =>
  meromorphicAt_phi_comp (by unfold lineA; fun_prop) (by unfold lineB; fun_prop)
    (by unfold lineD; fun_prop)

theorem continuousAt_phiLine (m₀ m₁ : ℤ) {d : ℂ} (hd : ∀ n : ℤ, d ≠ n) :
    ContinuousAt (phiLine m₀ m₁ d) 0 := by
  obtain ⟨h₁, h₂⟩ := phi_args hd m₀ m₁
  exact continuousAt_phi_comp (by unfold lineA; fun_prop) (by unfold lineB; fun_prop)
    (by unfold lineD; fun_prop) (by simpa [lineA, lineB, lineD] using h₁)
    (by simpa [lineA, lineB, lineD] using h₂)

theorem phiLine_zero (m₀ m₁ : ℤ) (d : ℂ) : phiLine m₀ m₁ d 0 = phi m₀ m₁ d := by
  simp [phiLine, lineA, lineB, lineD]

theorem conv_near {n₀ n₁ : ℤ} {d l : ℂ} (hl : lineBound n₀ n₁ d < l.re) {a' b' : ℂ}
    (ha : |(a' - lineA n₀ l).re| ≤ 1) (hb : |(b' - lineB n₁ l).re| ≤ 1) :
    Conv a' b' (lineD d l) :=
  have h := line_good hl ha hb
  conv_of_re h.1 h.2.1 h.2.2

theorem phi_near {n₀ n₁ : ℤ} {d l : ℂ} (hl : lineBound n₀ n₁ d < l.re) {a' b' : ℂ}
    (ha : |(a' - lineA n₀ l).re| ≤ 1) (hb : |(b' - lineB n₁ l).re| ≤ 1) :
    phi a' b' (lineD d l) = schw a' b' (lineD d l) :=
  have h := line_good hl ha hb
  (schw_eq_phi h.1 h.2.1 h.2.2).symm

theorem lineA_add (m k : ℤ) (l : ℂ) : lineA (m + k) l = lineA m l + k := by
  simp only [lineA]; push_cast; ring

theorem lineB_add (m k : ℤ) (l : ℂ) : lineB (m + k) l = lineB m l + k := by
  simp only [lineB]; push_cast; ring

/-- **The `∂/∂k · k` relation for the continued integral at integer labels.** For `d ∉ ℤ`,
`(2d - 4n₀ - 2n₁) φ(n₀, n₁) - 2n₁ φ(n₀ - 1, n₁ + 1) = 0`. Proof: on the line
`λ ↦ (n₀ + 2λ, n₁ + 6λ, d + 15λ)` the relation is meromorphic, and for `re λ` large every
label converges, so it vanishes there by `schw_rel₀₀` and `schw_eq_phi`; the identity theorem
(`QED.DimReg.Meromorphic.eq_of_eqOn`) gives it at `λ = 0`. -/
theorem phi_rel₀₀ (n₀ n₁ : ℤ) {d : ℂ} (hd : ∀ n : ℤ, d ≠ n) :
    (2 * d - 4 * n₀ - 2 * n₁) * phi n₀ n₁ d - 2 * n₁ * phi (n₀ + (-1 : ℤ)) (n₁ + (1 : ℤ)) d =
      0 := by
  let R : ℂ → ℂ := fun l => (2 * lineD d l - 4 * lineA n₀ l - 2 * lineB n₁ l) *
    phiLine n₀ n₁ d l - 2 * lineB n₁ l * phiLine (n₀ + -1) (n₁ + 1) d l
  have hmer : Meromorphic R := fun z =>
    ((by unfold lineA lineB lineD; fun_prop : AnalyticAt ℂ
      (fun l => 2 * lineD d l - 4 * lineA n₀ l - 2 * lineB n₁ l) z).meromorphicAt.mul
      (meromorphic_phiLine n₀ n₁ d z)).sub
      ((by unfold lineB; fun_prop : AnalyticAt ℂ (fun l => 2 * lineB n₁ l) z).meromorphicAt.mul
        (meromorphic_phiLine _ _ d z))
  have hcont : ContinuousAt R 0 :=
    ((by unfold lineA lineB lineD; fun_prop : ContinuousAt
      (fun l => 2 * lineD d l - 4 * lineA n₀ l - 2 * lineB n₁ l) 0).mul
      (continuousAt_phiLine n₀ n₁ hd)).sub
      ((by unfold lineB; fun_prop : ContinuousAt (fun l => 2 * lineB n₁ l) 0).mul
        (continuousAt_phiLine _ _ hd))
  have heq : EqOn R 0 {l : ℂ | lineBound n₀ n₁ d < l.re} := by
    intro l hl
    have hl : lineBound n₀ n₁ d < l.re := hl
    obtain ⟨g₀, g₁⟩ := line_gt_one hl
    simp only [R, phiLine, Pi.zero_apply, lineA_add, lineB_add]
    push_cast
    rw [phi_near hl (by simp) (by simp), phi_near hl (by simp) (by simp)]
    rw [← sub_eq_add_neg]
    exact schw_rel₀₀ g₀ g₁ (conv_near hl (by simp) (by simp)) (conv_near hl (by simp) (by simp))
      (conv_near hl (by simp) (by simp)) (conv_near hl (by simp) (by simp))
  have h0 := Meromorphic.eq_of_eqOn (g := fun _ => (0 : ℂ)) hmer
    (fun z => analyticAt_const.meromorphicAt)
    (isOpen_lineRegion n₀ n₁ d) (nonempty_lineRegion n₀ n₁ d) heq hcont continuousAt_const
  simpa [R, phiLine_zero, lineA, lineB, lineD] using h0

/-- **The `∂/∂k · p` relation for the continued integral at integer labels** (Euclidean
signs), for `d ∉ ℤ`. -/
theorem phi_rel₀₁ (n₀ n₁ : ℤ) {d : ℂ} (hd : ∀ n : ℤ, d ≠ n) :
    2 * n₀ * phi n₀ n₁ d - 2 * n₀ * phi (n₀ + (1 : ℤ)) (n₁ + (-1 : ℤ)) d +
      2 * n₁ * phi (n₀ + (-1 : ℤ)) (n₁ + (1 : ℤ)) d - 2 * n₁ * phi n₀ n₁ d +
      4 * n₁ * phi n₀ (n₁ + (1 : ℤ)) d = 0 := by
  let R : ℂ → ℂ := fun l => 2 * lineA n₀ l * phiLine n₀ n₁ d l -
    2 * lineA n₀ l * phiLine (n₀ + 1) (n₁ + -1) d l +
    2 * lineB n₁ l * phiLine (n₀ + -1) (n₁ + 1) d l - 2 * lineB n₁ l * phiLine n₀ n₁ d l +
    4 * lineB n₁ l * phiLine n₀ (n₁ + 1) d l
  have hA : ∀ z, AnalyticAt ℂ (lineA n₀) z := fun z => by unfold lineA; fun_prop
  have hB : ∀ z, AnalyticAt ℂ (lineB n₁) z := fun z => by unfold lineB; fun_prop
  have hmer : Meromorphic R := fun z => by
    have m := fun m₀ m₁ => meromorphic_phiLine m₀ m₁ d z
    have a := (hA z).meromorphicAt
    have b := (hB z).meromorphicAt
    exact (((((MeromorphicAt.const 2 z).mul a).mul (m _ _)).sub
      (((MeromorphicAt.const 2 z).mul a).mul (m _ _))).add
      (((MeromorphicAt.const 2 z).mul b).mul (m _ _))).sub
      (((MeromorphicAt.const 2 z).mul b).mul (m _ _)) |>.add
      (((MeromorphicAt.const 4 z).mul b).mul (m _ _))
  have hcont : ContinuousAt R 0 := by
    have m := fun m₀ m₁ => continuousAt_phiLine m₀ m₁ hd
    have a := (hA 0).continuousAt
    have b := (hB 0).continuousAt
    exact (((((continuousAt_const (y := (2 : ℂ))).mul a).mul (m _ _)).sub
      (((continuousAt_const (y := (2 : ℂ))).mul a).mul (m _ _))).add
      (((continuousAt_const (y := (2 : ℂ))).mul b).mul (m _ _))).sub
      (((continuousAt_const (y := (2 : ℂ))).mul b).mul (m _ _)) |>.add
      (((continuousAt_const (y := (4 : ℂ))).mul b).mul (m _ _))
  have heq : EqOn R (fun _ => 0) {l : ℂ | lineBound n₀ n₁ d < l.re} := by
    intro l hl
    have hl : lineBound n₀ n₁ d < l.re := hl
    obtain ⟨g₀, g₁⟩ := line_gt_one hl
    simp only [R, phiLine, lineA_add, lineB_add]
    push_cast
    rw [phi_near hl (by simp) (by simp), phi_near hl (by simp) (by simp),
      phi_near hl (by simp) (by simp), phi_near hl (by simp) (by simp)]
    rw [← sub_eq_add_neg, ← sub_eq_add_neg]
    exact schw_rel₀₁ g₀ g₁ (conv_near hl (by simp) (by simp)) (conv_near hl (by simp) (by simp))
      (conv_near hl (by simp) (by simp)) (conv_near hl (by simp) (by simp))
      (conv_near hl (by simp) (by simp))
  have h0 := Meromorphic.eq_of_eqOn (g := fun _ => (0 : ℂ)) hmer
    (fun z => analyticAt_const.meromorphicAt)
    (isOpen_lineRegion n₀ n₁ d) (nonempty_lineRegion n₀ n₁ d) heq hcont continuousAt_const
  simpa [R, phiLine_zero, lineA, lineB, lineD] using h0

/-! ### The integer-label values and the checker's hypotheses -/

open QED.Algebra.IBPCert QED.Algebra.IBPCert.Pilot

/-- **The one-loop on-shell self-energy integrals of `oneLoopSE` at integer labels**:
`(-1)^{ν₀ + ν₁} φ(ν₀, ν₁; d)`, the sign being the Wick-rotation sign of the Minkowski family
and `φ` the meromorphic continuation of the Γ-normalized Schwinger integral
(`QED.DimReg.OneLoopSchwinger.schw_eq_phi`). -/
noncomputable def val (ν : Fin 2 → ℤ) (d : ℂ) : ℂ := (-1 : ℂ) ^ (ν 0 + ν 1) * phi (ν 0) (ν 1) d

theorem val_add (ν : Fin oneLoopSE.nProp → ℤ) (l : List ℤ) (d : ℂ) :
    val (ν + toVec oneLoopSE.nProp l) d =
      (-1 : ℂ) ^ (ν (0 : Fin 2) + ν (1 : Fin 2)) * ((-1 : ℂ) ^ (l.getD 0 0 + l.getD 1 0) *
      phi ((ν (0 : Fin 2) : ℂ) + (l.getD 0 0 : ℤ)) ((ν (1 : Fin 2) : ℂ) + (l.getD 1 0 : ℤ)) d) := by
  have e0 : (ν + toVec oneLoopSE.nProp l) (0 : Fin 2) = ν (0 : Fin 2) + l.getD 0 0 := rfl
  have e1 : (ν + toVec oneLoopSE.nProp l) (1 : Fin 2) = ν (1 : Fin 2) + l.getD 1 0 := rfl
  simp only [val]
  rw [e0, e1, show ν (0 : Fin 2) + l.getD 0 0 + (ν (1 : Fin 2) + l.getD 1 0) =
    (ν (0 : Fin 2) + ν (1 : Fin 2)) + (l.getD 0 0 + l.getD 1 0) by ring, zpow_add₀ (by norm_num)]
  push_cast
  ring

/-- **`IBPHolds` for the continued integrals**: for `d ∉ ℤ`, the integer-label values `val`
satisfy every IBP relation of `oneLoopSE` (all `i`, `j`, `ν ∈ ℤ²`). -/
theorem ibpHolds_val {d : ℂ} (hd : ∀ n : ℤ, d ≠ n) : oneLoopSE.IBPHolds val d := by
  intro i hi j hj ν
  have hi0 : i = 0 := by simp [oneLoopSE] at hi; omega
  subst hi0
  rw [← Family.tmplAt_eq_template tmplOk_oneLoopSE (by decide) hj]
  have hj' : j < 2 := hj
  interval_cases j
  · have r := phi_rel₀₀ (ν (0 : Fin 2)) (ν (1 : Fin 2)) hd
    push_cast at r
    simp only [val_add]
    simp [Family.tmplAt, oneLoopSE, Term.coeff, vecGet]
    linear_combination (-1 : ℂ) ^ (ν (0 : Fin 2) + ν (1 : Fin 2)) * r
  · have r := phi_rel₀₁ (ν (0 : Fin 2)) (ν (1 : Fin 2)) hd
    push_cast at r
    simp only [val_add]
    simp [Family.tmplAt, oneLoopSE, Term.coeff, vecGet]
    linear_combination (-1 : ℂ) ^ (ν (0 : Fin 2) + ν (1 : Fin 2)) * r

/-- **The scaleless sector vanishes, as a value of the continuation**: `val ν d = 0` when
`ν₁ ≤ 0`, because `φ` carries the entire factor `Γ(ν₁)⁻¹`. No convention is involved. -/
theorem zeroSectors_val (d : ℂ) : oneLoopSE.ZeroSectors val d := by
  intro S hS ν hν
  simp only [oneLoopSE, List.mem_singleton] at hS
  subst hS
  have h1 : ν (1 : Fin 2) ≤ 0 := by simpa [vecGet, oneLoopSE] using hν 1 (by simp)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ν (1 : Fin 2) = -m := ⟨(-ν (1 : Fin 2)).toNat, by omega⟩
  simp only [val, phi, hm]
  push_cast
  rw [Gamma_neg_nat_eq_zero, inv_zero]
  ring

/-! ### The certified reduction as a statement about the integrals -/

/-- **The landed certificate applied to the actual integrals.** For `d ∉ ℤ`,
`I(1, 1) = (d - 2) / (2(d - 3)) · I(0, 1)` for the continued Schwinger integrals of
`oneLoopSE`, from `QED.Algebra.IBPCert.Pilot.oneLoop_reduction₁₁`. -/
theorem val_reduction₁₁ {d : ℂ} (hd : ∀ n : ℤ, d ≠ n) :
    val ![1, 1] d = (d - 2) / (2 * (d - 3)) * val ![0, 1] d :=
  oneLoop_reduction₁₁ val d (ibpHolds_val hd) (zeroSectors_val d)
    (by simpa using hd 3)

/-- The same reduction in closed form: `φ(1, 1) = -(d - 2) / (2(d - 3)) · Γ(1 - d/2)`, the
tadpole `Γ(1 - d/2) = φ(0, 1)` being the master. -/
theorem phi_one_one {d : ℂ} (hd : ∀ n : ℤ, d ≠ n) :
    phi 1 1 d = -((d - 2) / (2 * (d - 3))) * Gamma (1 - d / 2) := by
  have h := val_reduction₁₁ hd
  have hg : Gamma (d - 1) ≠ 0 :=
    Gamma_ne_zero fun m hm => hd (1 - m) (by push_cast; linear_combination hm)
  simp only [val, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  norm_num at h
  have hp : phi 0 1 d = Gamma (1 - d / 2) := by
    simp only [phi]
    rw [show (0 : ℂ) + 1 - d / 2 = 1 - d / 2 by ring, show d - 2 * 0 - 1 = d - 1 by ring,
      show d - 0 - 1 = d - 1 by ring, Gamma_one, inv_one, mul_one, mul_assoc,
      mul_inv_cancel₀ hg, mul_one]
  rw [h, hp]
  ring

/-- **The one-loop on-shell self-energy integral, reduced.** For `3 < re d < 4`, where it
converges absolutely,
`∫_{(0,∞)²} U^{-d/2} e^{-F/U} dx = -(d - 2) / (2(d - 3)) · Γ(1 - d/2)`. The left side is the
Schwinger integral of `I(1, 1)`; the factor `Γ(1 - d/2)` is the master `I(0, 1)`
(`integral_kernel_face`); the sign is the Wick-rotation sign `(-1)^{|ν|}`. -/
theorem integral_kernel_eq {d : ℂ} (h3 : 3 < d.re) (h4 : d.re < 4) :
    ∫ x in quad, kernel d x = -((d - 2) / (2 * (d - 3))) * Gamma (1 - d / 2) := by
  have hd : ∀ n : ℤ, d ≠ n := by
    intro n hn
    have h := congrArg Complex.re hn
    simp only [intCast_re] at h
    rw [h] at h3 h4
    have : (3 : ℤ) < n := by exact_mod_cast h3
    have : n < (4 : ℤ) := by exact_mod_cast h4
    omega
  rw [← phi_one_one hd, ← schw_eq_phi (by simp) (by simp; linarith) (by simp; linarith), schw,
    Gamma_one, mul_one, div_one, mellin₂]
  refine setIntegral_congr_fun measurableSet_quad fun x hx => ?_
  simp [integrand]

/-- **The master `I(0, 1)` is the `x₀ = 0` face integral.** For `re d < 2`,
`∫₀^∞ S(0, x₁) dx₁ = Γ(1 - d/2) = φ(0, 1; d)`: the label `ν₀ = 0` restricts the Schwinger
integral to the face `x₀ = 0` (the limit of `x₀^{ν₀-1}/Γ(ν₀)` as `ν₀ → 0`). -/
theorem integral_kernel_face {d : ℂ} (h2 : d.re < 2) :
    ∫ x in Ioi (0 : ℝ), kernel d (0, x) = Gamma (1 - d / 2) := by
  rw [Gamma_eq_integral (by simp; linarith), GammaIntegral]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : x ≠ 0 := hx.out.ne'
  simp only [kernel, zero_add]
  rw [show x ^ 2 / x = x by field_simp, show 1 - d / 2 - 1 = -(d / 2) by ring, ofReal_exp,
    ofReal_neg]
  ring

end QED.DimReg.OneLoopSchwinger
