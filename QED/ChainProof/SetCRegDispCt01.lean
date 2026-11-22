/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtVP
import QED.TwoLoop.WardIdentity
import QED.TwoLoop.WardIdentityParametric
import QED.GradedProof.LevelOneElectron

/-!
# Set (c): the counterterm classes `CBₖ + CDₖ,₀ + CDₖ,₁`, `k = 0, 1`: the kernel

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtCB` of
`QED.ChainProof.SetCRegDisp.setCRegLimitDisp_of_pieces`, placements `k = 0, 1` (the hypothesis
`hlow` of `isDispPV_CB_of_low`).

For `k < 2` the class `CBₖ` carries the level-`0` electron counterterm `-(δ₂ p̸ - δ_m m)` on the
open line `d` (`d = 1` for `k = 0`, `d = 0` for `k = 1`) of the two-loop VP class. By the merge
of the inserted line (`QED.ChainProof.SetCPauli.electronInsertion_merge`), with
`Y = δ₂ A + b`, `c = -2 m b`, `b = (δ₂ - δ_m) m` (`mergeY`, `mergeC`),

`S̃ X S̃ = D⁻¹ Y + D⁻² c A = δ₂ S + b ∂S/∂m_d`,

the propagator `S = A/D` of the line `d` with its own mass `m_d`. So `CBₖ + CDₖ,₀ + CDₖ,₁` is
`δ₂(0)` times the subtracted bubble half (as for `k ≥ 2`, with `δ₁(0) = δ₂(0)` by the one-loop
Ward identity) plus `b` times its derivative in the mass of the line `d`. In the spectral form,
the second part is the superposition of the `m_d`-derivatives of the one-loop Pauli values with
the photon function `k⁴/(k² + T) D(k²)²`. For a photon of mass² `λ` (unit mass) that derivative
is `W(λ) = λ ∫₀¹ x(1-x)²/(x² + (1-x)λ)² dx`, the same for `d = 0, 1`; for a photon function
`R(k²) = ∫ dσ(λ)/(k² + λ)` it is `∫₀¹ x (K R(K))' dx` at `K = x²/(1-x)`
(`wKer`, `vpInsertW`; scripts `scratchpad/setCreg3/ins.py`, `w2.py`, `disp.py`).

## Main statements

* `wKer`, `vpInsertW`, **`abs_vpInsertW_le`**: `|vpInsertW c a b| ≤ 6/c` for `0 < a < b`,
  `0 < c`;
* **`integrableOn_rho_vpInsertW`**: each flavour of the derivative part is integrable;
* `isDispPV_of_flavours`: a flavour sum `K (g(1) + c₁ g(M₁/m) + c₂ g(M₂/m))`, `g` the
  `ρ`-integral of a real kernel, is in dispersion form;
* `cb01Ker`: the kernel for `k = 0, 1`,
  `cbVPKer + i e⁴/(16π⁴) (δ₂(0) - δ_m(0)) vpInsertW(T, m_γ²/m², Λ²/m²)`;
* `setCAdm_onShell_zero`, `onShellδ₂_lzParams`: the level-`0` electron counterterms at an
  admissible datum are the on-shell values at `m, m_γ, Λ`, and `δ₂(0) = -A₀ = δ₁(0)`;
* `cbLoVal`, `CBLoEq`: the expected explicit value of `CBₖ + CDₖ,₀ + CDₖ,₁`, `k < 2`,
  `i e⁴/(16π⁴) ∑_f c_f (-A₀ vpFlavour + (δ₂(0) - δ_m(0)) vpFlavourW)` at unit masses;
* **`isDispPV_cbLoVal`**: that value is in dispersion form with kernel `cb01Ker`;
* **`isDispPV_CB_lo_of_eq`**, **`isDispPV_CB_of_lo_eq`**: `hlow`, hence `hCtCB` for all `k`
  (kernels `uCBOf P₀ (fun _ => cb01Ker P₀)`), from `CBLoEq`.

## What remains

`CBLoEq` itself, the analogue of `ctPauliAll_CB_hi_eq` for the δ₂(0)/δ_m(0)-inserted shapes, is
**not proved**. Its `δ₂` part reduces to the sealed subtracted bubble half once the once-merged
pieces with `Y = δ₂ A` are identified with those of `VP`; its `b` part needs the fixed-`q`
spectral route of Phase 4 for the vertex with `∂S/∂m_d` on one open line. The normalization of
the `b` part (sign included) follows the merge identity and the `k ≥ 2` normalization; it is
checked numerically for the one-loop derivative kernel only.
-/

@[expose] public section

open Complex Real Set Filter Topology MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCK QED.ChainProof.SetCPauli
open QED.ChainProof.SetAPauli (regParams regFlavors)
open QED.TwoLoop.VPUnit (vpInsert vpFlavour)
open QED.OneLoop.VertexLimit (chargeA0)

/-! ### The kernel of the mass-derivative part -/

/-- `(K R(K))'` for `R(K) = K²/(K + c) (1/(K + a) - 1/(K + b))²`. -/
noncomputable def wKerK (c a b K : ℝ) : ℝ :=
  (3 * K ^ 2 * (1 / (K + a) - 1 / (K + b)) ^ 2 +
      2 * K ^ 3 * (1 / (K + a) - 1 / (K + b)) * (1 / (K + b) ^ 2 - 1 / (K + a) ^ 2)) / (K + c) -
    K ^ 3 * (1 / (K + a) - 1 / (K + b)) ^ 2 / (K + c) ^ 2

/-- The kernel of `vpInsertW`: `x (K R(K))'` at `K = x²/(1-x)`. -/
noncomputable def wKer (c a b x : ℝ) : ℝ := x * wKerK c a b (x ^ 2 / (1 - x))

/-- **The unit-mass derivative of the Pauli value in the mass of one open line**, for the photon
function `k⁴/(k² + c) (1/(k² + a) - 1/(k² + b))²`. -/
noncomputable def vpInsertW (c a b : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, wKer c a b x

theorem abs_wKerK_le {a b c K : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hK : 0 ≤ K) :
    |wKerK c a b K| ≤ 6 / (K + c) := by
  have hKa : 0 < K + a := by linarith
  have hKb : 0 < K + b := by linarith
  have hKc : 0 < K + c := by linarith
  set u := K * (1 / (K + a) - 1 / (K + b)) with hu
  set w := K ^ 2 * (1 / (K + b) ^ 2 - 1 / (K + a) ^ 2) with hw
  have hD : 1 / (K + a) - 1 / (K + b) = (b - a) / ((K + a) * (K + b)) := by
    field_simp
    ring
  have hu0 : 0 ≤ u := by
    rw [hu, hD]
    exact mul_nonneg hK (div_nonneg (by linarith) (by positivity))
  have hu1 : u ≤ 1 := by
    rw [hu, hD, mul_div_assoc', div_le_one (by positivity)]
    nlinarith
  have hw0 : w ≤ 0 := by
    rw [hw]
    refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.2 ?_)
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hKa.le (by linarith) 2)
  have hw1 : -1 ≤ w := by
    have h1 : K ^ 2 * (1 / (K + a) ^ 2) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]
      exact pow_le_pow_left₀ hK (by linarith) 2
    have h2 : 0 ≤ K ^ 2 * (1 / (K + b) ^ 2) := by positivity
    rw [hw, mul_sub]
    linarith
  have hk : K / (K + c) ≤ 1 := (div_le_one hKc).2 (by linarith)
  have hk0 : 0 ≤ K / (K + c) := div_nonneg hK hKc.le
  have e : wKerK c a b K =
      (3 * u ^ 2 + 2 * u * w) / (K + c) - u ^ 2 * (K / (K + c)) / (K + c) := by
    rw [wKerK, hu, hw]
    field_simp
  rw [e]
  have h1 : |3 * u ^ 2 + 2 * u * w| ≤ 5 := by
    rw [abs_le]
    constructor <;> nlinarith
  have h2 : |u ^ 2 * (K / (K + c))| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    calc u ^ 2 * (K / (K + c)) ≤ 1 * 1 := by
          gcongr
          · nlinarith
      _ = 1 := by ring
  calc |(3 * u ^ 2 + 2 * u * w) / (K + c) - u ^ 2 * (K / (K + c)) / (K + c)|
      ≤ |(3 * u ^ 2 + 2 * u * w) / (K + c)| + |u ^ 2 * (K / (K + c)) / (K + c)| := abs_sub _ _
    _ = |3 * u ^ 2 + 2 * u * w| / (K + c) + |u ^ 2 * (K / (K + c))| / (K + c) := by
        rw [abs_div, abs_div, abs_of_pos hKc]
    _ ≤ 5 / (K + c) + 1 / (K + c) := by gcongr
    _ = 6 / (K + c) := by ring

theorem abs_wKer_le {a b c x : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hx : x ∈ Icc (0 : ℝ) 1) :
    |wKer c a b x| ≤ 6 / c := by
  have hK : 0 ≤ x ^ 2 / (1 - x) := div_nonneg (sq_nonneg x) (by linarith [hx.2])
  have h := abs_wKerK_le ha hab hc hK
  rw [wKer, abs_mul, abs_of_nonneg hx.1]
  calc x * |wKerK c a b (x ^ 2 / (1 - x))| ≤ 1 * (6 / (x ^ 2 / (1 - x) + c)) := by
        gcongr
        exact hx.2
    _ ≤ 6 / c := by
        rw [one_mul]
        exact div_le_div_of_nonneg_left (by norm_num) hc (by linarith)

/-- **`|vpInsertW c a b| ≤ 6/c`.** -/
theorem abs_vpInsertW_le {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) :
    |vpInsertW c a b| ≤ 6 / c := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := 6 / c) (f := wKer c a b) fun x hx => by
      rw [uIoc_of_le zero_le_one] at hx
      exact abs_wKer_le ha hab hc ⟨hx.1.le, hx.2⟩
  simpa [vpInsertW] using h

theorem measurable_wKer_uncurry (a b : ℝ) :
    Measurable (Function.uncurry fun c x => wKer c a b x) := by
  unfold wKer wKerK
  fun_prop

theorem measurable_vpInsertW (a b : ℝ) : Measurable fun c => vpInsertW c a b := by
  have h := (measurable_wKer_uncurry a b).stronglyMeasurable.integral_prod_right
    (ν := (volume : Measure ℝ).restrict (Ioc 0 1))
  have e : (fun c => vpInsertW c a b) = fun c => ∫ x in Ioc (0 : ℝ) 1, wKer c a b x := by
    funext c
    simp only [vpInsertW, intervalIntegral.integral_of_le zero_le_one]
  rw [e]
  exact h.measurable

/-- **One flavour of the derivative part is integrable** on `(0, 1)`. -/
theorem integrableOn_rho_vpInsertW {M a b : ℝ} (hM : M ≠ 0) (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun v => setCKSpecRho v * vpInsertW (M ^ 2 * setCKSpecMass v) a b)
      (Ioo 0 1) := by
  refine Measure.integrableOn_of_bounded (M := 2 / M ^ 2) (by simp) ?_ ?_
  · refine (Measurable.mul ?_ ((measurable_vpInsertW a b).comp ?_)).aestronglyMeasurable
    · unfold setCKSpecRho
      fun_prop
    · unfold setCKSpecMass
      fun_prop
  · rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun v hv => ?_
    have hv2 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
    have hM2 : 0 < M ^ 2 := by positivity
    have hc : 0 < M ^ 2 * setCKSpecMass v := by
      unfold setCKSpecMass
      positivity
    have hW := abs_vpInsertW_le ha hab hc
    have hρ : 0 ≤ setCKSpecRho v := by
      unfold setCKSpecRho
      have : 0 ≤ 1 - v ^ 2 / 3 := by nlinarith [hv.2]
      positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ]
    calc setCKSpecRho v * |vpInsertW (M ^ 2 * setCKSpecMass v) a b|
        ≤ setCKSpecRho v * (6 / (M ^ 2 * setCKSpecMass v)) := by gcongr
      _ = 6 * v ^ 2 * (1 - v ^ 2 / 3) / (4 * M ^ 2) := by
          unfold setCKSpecRho setCKSpecMass
          field_simp
      _ ≤ 2 / M ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) hM2]
          have h1 : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
          have h2 : 0 ≤ v ^ 2 := sq_nonneg v
          have h3 : 6 * v ^ 2 * (1 - v ^ 2 / 3) ≤ 8 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right h3 hM2.le]

/-! ### Flavour sums in dispersion form -/

/-- **A flavour sum of `ρ`-integrals of one real kernel is in dispersion form.** -/
theorem isDispPV_of_flavours {m M₁ M₂ c₁ c₂ : ℝ} (hm : 0 < m) (hM₁ : m ≤ M₁) (hM₂ : m ≤ M₂)
    (K : ℂ) (f : ℝ → ℝ)
    (hint : ∀ M : ℝ, m ≤ M → IntegrableOn
      (fun v => setCKSpecRho v * f ((M / m) ^ 2 * setCKSpecMass v)) (Ioo 0 1)) :
    IsDispPV m M₁ M₂ c₁ c₂ (fun T => K * (f T : ℂ))
      (K * (((∫ v in Ioo (0 : ℝ) 1, setCKSpecRho v * f ((1 : ℝ) ^ 2 * setCKSpecMass v)) +
        c₁ * (∫ v in Ioo (0 : ℝ) 1, setCKSpecRho v * f ((M₁ / m) ^ 2 * setCKSpecMass v)) +
        c₂ * ∫ v in Ioo (0 : ℝ) 1, setCKSpecRho v * f ((M₂ / m) ^ 2 * setCKSpecMass v) : ℝ) :
          ℂ)) := by
  set g : ℝ → ℝ → ℝ := fun M v => setCKSpecRho v * f (M ^ 2 * setCKSpecMass v) with hg
  have h0 := hint m le_rfl
  rw [div_self hm.ne'] at h0
  have h1 := hint M₁ hM₁
  have h2 := hint M₂ hM₂
  have hF : dispPVF m M₁ M₂ c₁ c₂ (fun T => K * (f T : ℂ)) = fun v =>
      K * ((g 1 v + c₁ * g (M₁ / m) v + c₂ * g (M₂ / m) v : ℝ) : ℂ) := by
    funext v
    have e1 : M₁ ^ 2 / m ^ 2 * setCKSpecMass v = (M₁ / m) ^ 2 * setCKSpecMass v := by
      rw [div_pow]
    have e2 : M₂ ^ 2 / m ^ 2 * setCKSpecMass v = (M₂ / m) ^ 2 * setCKSpecMass v := by
      rw [div_pow]
    simp only [dispPVF, hg, e1, e2, one_pow, one_mul]
    push_cast
    ring
  have h0' : IntegrableOn (fun v => g 1 v) (Ioo 0 1) := h0
  have h1' : IntegrableOn (fun v => g (M₁ / m) v) (Ioo 0 1) := h1
  have h2' : IntegrableOn (fun v => g (M₂ / m) v) (Ioo 0 1) := h2
  have hI : IntegrableOn (fun v => g 1 v + c₁ * g (M₁ / m) v + c₂ * g (M₂ / m) v)
      (Ioo 0 1) := (h0'.add (h1'.const_mul c₁)).add (h2'.const_mul c₂)
  have hR : ∫ v in Ioo (0 : ℝ) 1, (g 1 v + c₁ * g (M₁ / m) v + c₂ * g (M₂ / m) v) =
      (∫ v in Ioo (0 : ℝ) 1, g 1 v) + c₁ * (∫ v in Ioo (0 : ℝ) 1, g (M₁ / m) v) +
        c₂ * ∫ v in Ioo (0 : ℝ) 1, g (M₂ / m) v := by
    have h01 : IntegrableOn (fun v => g 1 v + c₁ * g (M₁ / m) v) (Ioo 0 1) :=
      h0'.add (h1'.const_mul c₁)
    rw [integral_add h01 (h2'.const_mul c₂), integral_add h0' (h1'.const_mul c₁),
      integral_const_mul, integral_const_mul]
  refine ⟨?_, ?_⟩
  · rw [hF]
    exact hI.ofReal.const_mul K
  · rw [hF, integral_const_mul, integral_complex_ofReal, hR]

/-! ### The kernel for `k = 0, 1` -/

/-- The level-`0` parameters at `m_γ, Λ`: those of `P₀` with the photon regulators replaced. -/
def lzParams (P₀ : Params) (mγ Λ : ℝ) : Params := { P₀ with mγ := mγ, Λ := Λ }

/-- The coefficient `b/m = δ₂(0) - δ_m(0)` of the mass-derivative part. -/
noncomputable def cb01B (P₀ : Params) (mγ Λ : ℝ) : ℝ :=
  QED.WickModel.onShellδ₂ (lzParams P₀ mγ Λ) - QED.WickModel.onShellδm (lzParams P₀ mγ Λ)

/-- **The kernel of `CBₖ + CDₖ,₀ + CDₖ,₁`, `k = 0, 1`**: the kernel `cbVPKer` of `k ≥ 2`
(`δ₂(0) = δ₁(0)`) plus `i e⁴/(16π⁴) (δ₂(0) - δ_m(0)) vpInsertW(T, m_γ²/m², Λ²/m²)`. -/
noncomputable def cb01Ker (P₀ : Params) (mγ Λ T : ℝ) : ℂ :=
  cbVPKer P₀ mγ Λ T + I * ((P₀.e ^ 4 / (16 * π ^ 4) * cb01B P₀ mγ Λ *
    vpInsertW T ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2) : ℝ) : ℂ)

/-- One flavour of the mass-derivative part at unit mass. -/
noncomputable def vpFlavourW (M mγ Λ : ℝ) : ℝ :=
  ∫ v in Ioo (0 : ℝ) 1, setCKSpecRho v * vpInsertW (M ^ 2 * setCKSpecMass v) (mγ ^ 2) (Λ ^ 2)

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

/-! ### The level-`0` electron counterterms -/

theorem setCAdm_onShell_zero (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) :
    P₀.e ^ 2 * D.d₂ (.inl 0) 0 = QED.WickModel.onShellδ₂ (lzParams P₀ mγ Λ) ∧
      P₀.e ^ 2 * D.dm (.inl 0) 0 = QED.WickModel.onShellδm (lzParams P₀ mγ Λ) := by
  obtain ⟨-, -, -, -, hmγ, hΛ, -, hm2, hD, -⟩ := hA
  have hm : 0 < P₀.m := by linarith
  obtain ⟨h1, -⟩ := hD.2 1 le_rfl (by norm_num)
  have hc := (h1 (.inl 0) rfl).1
  have hc' := (QED.GradedProof.isOnShellAt_one_iff' (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (.inl 0) hm hmγ hΛ).1 hc
  exact (QED.TwoLoop.Ward.isElectronOnShell_iff _ _ _ _).1 hc'

/-- **`δ₂(0) = -A₀ = δ₁(0)`** (the one-loop Ward identity in the form
`QED.TwoLoop.Ward.chargeA0_eq_neg_onShellδ₂`). -/
theorem onShellδ₂_lzParams (hm : 0 < P₀.m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    QED.WickModel.onShellδ₂ (lzParams P₀ mγ Λ) = -chargeA0 P₀.e P₀.m mγ Λ := by
  have h := QED.TwoLoop.Ward.chargeA0_eq_neg_onShellδ₂ (lzParams P₀ mγ Λ) hm hmγ hΛ
  exact (neg_eq_iff_eq_neg.1 h.symm)

/-! ### `hlow` from the explicit value -/

/-- The real kernel `e⁴/(16π⁴) (-A₀ vpInsert + (δ₂(0) - δ_m(0)) vpInsertW)` of `cb01Ker`. -/
noncomputable def cb01F (P₀ : Params) (mγ Λ T : ℝ) : ℝ :=
  P₀.e ^ 4 / (16 * π ^ 4) * (-chargeA0 P₀.e P₀.m mγ Λ *
    vpInsert T ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2) +
      cb01B P₀ mγ Λ * vpInsertW T ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2))

theorem cb01Ker_eq (P₀ : Params) (mγ Λ T : ℝ) : cb01Ker P₀ mγ Λ T = I * (cb01F P₀ mγ Λ T : ℂ) := by
  simp only [cb01Ker, cbVPKer, cb01F]
  push_cast
  ring

/-- One flavour of the explicit value: `e⁴/(16π⁴) (-A₀ vpFlavour + (δ₂(0) - δ_m(0)) vpFlavourW)`
at unit mass. -/
noncomputable def cbLoFl (P₀ : Params) (mγ Λ M : ℝ) : ℝ :=
  P₀.e ^ 4 / (16 * π ^ 4) * (-chargeA0 P₀.e P₀.m mγ Λ * vpFlavour M (mγ / P₀.m) (Λ / P₀.m) +
    cb01B P₀ mγ Λ * vpFlavourW M (mγ / P₀.m) (Λ / P₀.m))

/-- **The expected value of `CBₖ + CDₖ,₀ + CDₖ,₁`, `k = 0, 1`**: `i` times the flavour sum of
`cbLoFl` over the unit masses `1, M₁/m, M₂/m`. -/
noncomputable def cbLoVal (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) : ℂ :=
  I * ((cbLoFl P₀ mγ Λ 1 + c₁ * cbLoFl P₀ mγ Λ (M₁ / P₀.m) + c₂ * cbLoFl P₀ mγ Λ (M₂ / P₀.m) :
    ℝ) : ℂ)

/-- **The explicit value of `CBₖ + CDₖ,₀ + CDₖ,₁` for `k = 0, 1`** (the analogue of
`ctPauliAll_CB_hi_eq`; open, not proved here). -/
def CBLoEq (P₀ : Params) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5, k < 2 →
    ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s =
      cbLoVal P₀ M₁ M₂ c₁ c₂ mγ Λ

section Lo

variable (hm : 0 < P₀.m) (hmγ : 0 < mγ) (hmΛ : mγ < Λ) (hm2 : mγ < 2 * P₀.m)
include hm hmγ hmΛ hm2

theorem integrableOn_rho_cb01F {M : ℝ} (hM : P₀.m ≤ M) :
    IntegrableOn (fun v => setCKSpecRho v * cb01F P₀ mγ Λ ((M / P₀.m) ^ 2 * setCKSpecMass v))
      (Ioo 0 1) := by
  have ha : 0 < (mγ / P₀.m) ^ 2 := by positivity
  have hab : (mγ / P₀.m) ^ 2 < (Λ / P₀.m) ^ 2 :=
    pow_lt_pow_left₀ (div_lt_div_of_pos_right hmΛ hm) (by positivity) two_ne_zero
  have hM0 : M / P₀.m ≠ 0 := (div_pos (hm.trans_le hM) hm).ne'
  have hlt : mγ / P₀.m < 2 * (M / P₀.m) := by
    rw [mul_div_assoc', div_lt_div_iff_of_pos_right hm]
    linarith
  have haM : (mγ / P₀.m) ^ 2 < 4 * (M / P₀.m) ^ 2 := by
    have := pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
    linarith [show (2 * (M / P₀.m)) ^ 2 = 4 * (M / P₀.m) ^ 2 by ring]
  have h1 : IntegrableOn (fun v => setCKSpecRho v *
      vpInsert ((M / P₀.m) ^ 2 * setCKSpecMass v) ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2))
      (Ioo 0 1) :=
    (integrableOn_rho_vpInsert hM0 ha hab haM).mono_set Ioo_subset_Ioc_self
  have h2 := integrableOn_rho_vpInsertW hM0 ha hab.le
  have h : IntegrableOn (fun v =>
      P₀.e ^ 4 / (16 * π ^ 4) * -chargeA0 P₀.e P₀.m mγ Λ * (setCKSpecRho v *
        vpInsert ((M / P₀.m) ^ 2 * setCKSpecMass v) ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2)) +
      P₀.e ^ 4 / (16 * π ^ 4) * cb01B P₀ mγ Λ * (setCKSpecRho v *
        vpInsertW ((M / P₀.m) ^ 2 * setCKSpecMass v) ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2)))
      (Ioo 0 1) :=
    (h1.const_mul (P₀.e ^ 4 / (16 * π ^ 4) * -chargeA0 P₀.e P₀.m mγ Λ)).add
      (h2.const_mul (P₀.e ^ 4 / (16 * π ^ 4) * cb01B P₀ mγ Λ))
  have e : (fun v => setCKSpecRho v * cb01F P₀ mγ Λ ((M / P₀.m) ^ 2 * setCKSpecMass v)) =
      fun v => P₀.e ^ 4 / (16 * π ^ 4) * -chargeA0 P₀.e P₀.m mγ Λ * (setCKSpecRho v *
        vpInsert ((M / P₀.m) ^ 2 * setCKSpecMass v) ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2)) +
      P₀.e ^ 4 / (16 * π ^ 4) * cb01B P₀ mγ Λ * (setCKSpecRho v *
        vpInsertW ((M / P₀.m) ^ 2 * setCKSpecMass v) ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2)) := by
    funext v
    simp only [cb01F]
    ring
  rw [e]
  exact h

theorem integral_rho_cb01F {M : ℝ} (hM : P₀.m ≤ M) :
    ∫ v in Ioo (0 : ℝ) 1, setCKSpecRho v * cb01F P₀ mγ Λ ((M / P₀.m) ^ 2 * setCKSpecMass v) =
      cbLoFl P₀ mγ Λ (M / P₀.m) := by
  have ha : 0 < (mγ / P₀.m) ^ 2 := by positivity
  have hab : (mγ / P₀.m) ^ 2 < (Λ / P₀.m) ^ 2 :=
    pow_lt_pow_left₀ (div_lt_div_of_pos_right hmΛ hm) (by positivity) two_ne_zero
  have hM0 : M / P₀.m ≠ 0 := (div_pos (hm.trans_le hM) hm).ne'
  have hlt : mγ / P₀.m < 2 * (M / P₀.m) := by
    rw [mul_div_assoc', div_lt_div_iff_of_pos_right hm]
    linarith
  have haM : (mγ / P₀.m) ^ 2 < 4 * (M / P₀.m) ^ 2 := by
    have := pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
    linarith [show (2 * (M / P₀.m)) ^ 2 = 4 * (M / P₀.m) ^ 2 by ring]
  have h1 : IntegrableOn (fun v => setCKSpecRho v *
      vpInsert ((M / P₀.m) ^ 2 * setCKSpecMass v) ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2))
      (Ioo 0 1) :=
    (integrableOn_rho_vpInsert hM0 ha hab haM).mono_set Ioo_subset_Ioc_self
  have h2 := integrableOn_rho_vpInsertW hM0 ha hab.le
  set A := P₀.e ^ 4 / (16 * π ^ 4) * -chargeA0 P₀.e P₀.m mγ Λ
  set B := P₀.e ^ 4 / (16 * π ^ 4) * cb01B P₀ mγ Λ
  have e : (fun v => setCKSpecRho v * cb01F P₀ mγ Λ ((M / P₀.m) ^ 2 * setCKSpecMass v)) =
      fun v => A * (setCKSpecRho v *
        vpInsert ((M / P₀.m) ^ 2 * setCKSpecMass v) ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2)) +
        B * (setCKSpecRho v *
          vpInsertW ((M / P₀.m) ^ 2 * setCKSpecMass v) ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2)) := by
    funext v
    simp only [cb01F, A, B]
    ring
  rw [e, integral_add (h1.const_mul A) (h2.const_mul B), integral_const_mul, integral_const_mul,
    ← vpFlavour_eq_Ioo]
  simp only [cbLoFl, vpFlavourW, A, B, div_pow]
  ring

/-- **`CBₖ + CDₖ,₀ + CDₖ,₁` for `k = 0, 1` is in dispersion form** with kernel `cb01Ker`, given
its explicit value. -/
theorem isDispPV_cbLoVal (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂) :
    IsDispPV P₀.m M₁ M₂ c₁ c₂ (cb01Ker P₀ mγ Λ) (cbLoVal P₀ M₁ M₂ c₁ c₂ mγ Λ) := by
  have h := isDispPV_of_flavours (c₁ := c₁) (c₂ := c₂) hm hM₁.le hM₂.le I (cb01F P₀ mγ Λ)
    fun M hM => integrableOn_rho_cb01F hm hmγ hmΛ hm2 hM
  have e : (fun T => I * (cb01F P₀ mγ Λ T : ℂ)) = cb01Ker P₀ mγ Λ := by
    funext T
    rw [cb01Ker_eq]
  have h0 := integral_rho_cb01F hm hmγ hmΛ hm2 (M := P₀.m) le_rfl
  rw [div_self hm.ne'] at h0
  rw [e, h0, integral_rho_cb01F hm hmγ hmΛ hm2 hM₁.le,
    integral_rho_cb01F hm hmγ hmΛ hm2 hM₂.le] at h
  exact h

end Lo

/-- **`hlow` from the explicit value.** -/
theorem isDispPV_CB_lo_of_eq (hval : CBLoEq P₀) :
    ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5, k < 2 →
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (cb01Ker P₀ mγ Λ) (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA k hk
  rw [hval M₁ M₂ c₁ c₂ mγ Λ D s hA k hk]
  obtain ⟨hM₁, hM₂, -, -, hmγ, -, hmΛ, hm2, -, -⟩ := hA
  have hm : 0 < P₀.m := by linarith
  exact isDispPV_cbLoVal hm hmγ hmΛ hm2 hM₁ hM₂

/-- **`hCtCB` from the explicit value `CBLoEq`**, with the kernels
`uCBOf P₀ (fun _ => cb01Ker P₀)`. -/
theorem isDispPV_CB_of_lo_eq (he : P₀.e ≠ 0) (hval : CBLoEq P₀) :
    ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uCBOf P₀ (fun _ => cb01Ker P₀) k mγ Λ)
        (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
          ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
          ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s) :=
  isDispPV_CB_of_low he (isDispPV_CB_lo_of_eq hval)

end QED.ChainProof.SetCRegDisp

end
