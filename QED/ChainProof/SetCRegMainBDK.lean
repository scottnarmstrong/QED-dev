/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegMainBDKDesc
public import QED.ChainProof.SetCRegMainBDT

/-!
# Set (c), a main placement: the longitudinal dispersive part in the spectral variable

Helper level for the input `hMainBD` of `QED.ChainProof.SetCRegDisp.setCRegLimitDisp_of_pieces`.
The Pauli limit of the longitudinal dispersive part `kkLimB` of `repB i` is
`Z = -2c w_K ∑_f ∫₀¹ w_f(x) kkLimP(M_f, x) dx` (`piecePauli_kkLimB_val`: dominated convergence in
`x` with the explicit limit). By `QED.ChainProof.SetCMainB.kkLimP_descale`,
`kkLimP(M, x) = (x(1-x))⁻¹ kerK(M²/(m² x(1-x)))` with `kerK(T) = kkLimP(√(m² T)/2, 1/2)/4`, so
the change of variables of `QED/ChainProof/SetCRegMainBDT.lean` puts `-Z/(64 e m⁵)` in
dispersion form, and with the transverse part and the subtraction by the `δ₃` classes
(`QED/ChainProof/SetCRegMainBDSum.lean`) the main placement is in dispersion form: `hMainBD`.

* `integrableOn_mul_limUnder`, **`tendsto_evenQuot_setIntegral_val`**: dominated convergence in
  `x` with the value `∫₀¹ w(x) lim_u … dx` and its integrability;
* **`piecePauli_kkLimB_val`**: the Pauli limit of `kkLimB` with its explicit value;
* `isDispPV_of_flavours'`: a flavour sum `a ∑_f c_f ∫ ρ g(M_f² t_v/m²)` in dispersion form;
* `kerK`, `uBDK`, **`isDispPV_dispK`**: `-Z/(64 e m⁵)` with kernel `uBDK i`;
* `uBD`, **`isDispPV_mainBD`**: the input `hMainBD` with the kernels `uBD i = uBDT i + uBDK i`
  and the values `βᴮ i = clsPauliLim mainFam P₀ (.inl i)`.
-/

@[expose] public section

open Complex Real Set Filter Topology MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.ChainProof.SetCPauli QED.ChainProof.SetCK QED.TwoLoop.Enumeration
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### Dominated convergence in `x` with the explicit value -/

section DCT

variable {T : ℝ → ℝ → ℂ} {w : ℝ → ℂ}

theorem eventually_small_ne :
    ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ≠ 0 ∧ |u| ≤ 1 / 2 := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Icc_mem_nhds
    (by norm_num : (-(1 / 2) : ℝ) < 0) (by norm_num : (0 : ℝ) < 1 / 2))] with u hu0 hu
  exact ⟨hu0, abs_le.mpr hu⟩

theorem mul_evenQuot_eq (u : ℝ) : (fun x => w x * evenQuot (T x) u) =
    fun x => (w x * T x u + w x * T x (-u)) / (2 * (u : ℂ) ^ 2) := funext fun x => by
  simp only [evenQuot]; ring

/-- The limit integrand `w(x) lim_u evenQuot(T x)(u)` is integrable on `(0, 1)`. -/
theorem integrableOn_mul_limUnder (hT : KKPauliX T) (hw : IntegrableOn w (Ioo 0 1))
    (hint : ∀ u ∈ Ioo (-1 : ℝ) 1, IntegrableOn (fun x => w x * T x u) (Ioo 0 1)) :
    IntegrableOn (fun x => w x * limUnder (𝓝[≠] (0 : ℝ)) (evenQuot (T x))) (Ioo 0 1) := by
  obtain ⟨hL, B, hB⟩ := hT
  have hmeas : AEStronglyMeasurable (fun x => w x * limUnder (𝓝[≠] (0 : ℝ)) (evenQuot (T x)))
      (volume.restrict (Ioo 0 1)) := by
    refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℝ))
      (f := fun u x => if u ∈ Ioo (-1 : ℝ) 1 then w x * evenQuot (T x) u else 0)
      (fun u => ?_) ?_
    · by_cases hu : u ∈ Ioo (-1 : ℝ) 1
      · simp only [hu, ite_true]
        rw [mul_evenQuot_eq u]
        exact (((hint u hu).add (hint (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩)).div_const
          _).aestronglyMeasurable
      · simp only [hu, ite_false]
        exact aestronglyMeasurable_const
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
      refine ((tendsto_nhds_limUnder (hL x hx)).const_mul (w x)).congr' ?_
      filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1))] with u hu
      simp only [hu, ite_true]
  refine Integrable.mono' (hw.norm.mul_const B) hmeas
    ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_))
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_of_tendsto (tendsto_nhds_limUnder (hL x hx)).norm ?_
  filter_upwards [eventually_small_ne] with u hu
  exact hB u hu.1 hu.2 x hx

/-- **Dominated convergence in the Feynman parameter, with the value**: the even quotient of
`u ↦ ∫₀¹ w(x) T(x, u) dx` tends to `∫₀¹ w(x) lim_u evenQuot(T x)(u) dx`. -/
theorem tendsto_evenQuot_setIntegral_val (hT : KKPauliX T) (hw : IntegrableOn w (Ioo 0 1))
    (hint : ∀ u ∈ Ioo (-1 : ℝ) 1, IntegrableOn (fun x => w x * T x u) (Ioo 0 1)) :
    Tendsto (evenQuot fun u => ∫ x in Ioo (0 : ℝ) 1, w x * T x u) (𝓝[≠] 0)
      (𝓝 (∫ x in Ioo (0 : ℝ) 1, w x * limUnder (𝓝[≠] (0 : ℝ)) (evenQuot (T x)))) := by
  obtain ⟨hL, B, hB⟩ := hT
  refine (tendsto_integral_filter_of_dominated_convergence
    (F := fun u x => w x * evenQuot (T x) u) (fun x => ‖w x‖ * B) ?_ ?_
    (hw.norm.mul_const _) ?_).congr' ?_
  · filter_upwards [eventually_small_ne] with u hu'
    have hu1 := mem_Ioo_of_abs_le_half hu'.2
    have hu1' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu1.2], by linarith [hu1.1]⟩
    rw [mul_evenQuot_eq u]
    exact (((hint u hu1).add (hint (-u) hu1')).div_const _).aestronglyMeasurable
  · filter_upwards [eventually_small_ne] with u hu'
    obtain ⟨hu0, hu⟩ := hu'
    refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB u hu0 hu x hx) (norm_nonneg _)
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
    exact (tendsto_nhds_limUnder (hL x hx)).const_mul (w x)
  · filter_upwards [eventually_small_ne] with u hu'
    have hu1 := mem_Ioo_of_abs_le_half hu'.2
    have hu1' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu1.2], by linarith [hu1.1]⟩
    rw [mul_evenQuot_eq u, integral_div, integral_add (hint u hu1) (hint (-u) hu1')]
    rfl

end DCT

/-! ### The Pauli limit of `kkLimB` with its value -/

section KK

variable {i : Fin 12} {R : Params} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)
include hm hγ hγΛ

theorem integrableOn_kkPT {t : ℝ} (ht : R.m ≤ t) {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1))
    {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    IntegrableOn (fun x => w x * kkPT R i t x u) (Ioo 0 1) := by
  have e : (fun x => w x * kkPT R i t x u) = fun x => ∑ j : Idx,
      pauliWt R.m (curveMomentum R.m u) (restMomentum R.m) j.1 j.2.1 j.2.2 * (w x *
        kkLimX (kkH i R (restMomentum R.m) (curveMomentum R.m u) t j.1 j.2.1 j.2.2) x) :=
    funext fun x => by
      simp only [kkPT, kkPW]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  exact integrable_finsetSum _ fun j _ => ((kkVal_dKUnit (i := i) j.1 j.2.1 j.2.2 hm hγ hγΛ
    (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu)
    ((dot_curveMomentum_sub R.m hu).symm ▸ curveQ_nonneg R.m hu) ht hw).integrableOn_limX).const_mul
      _

/-- The limit integrand `w(x) kkLimP(t, x)` is integrable on `(0, 1)`. -/
theorem integrableOn_mul_kkLimP {t : ℝ} (ht : R.m ≤ t) {w : ℝ → ℂ}
    (hw : IntegrableOn w (Ioo 0 1)) :
    IntegrableOn (fun x => w x * kkLimP R i t x) (Ioo 0 1) :=
  integrableOn_mul_limUnder (T := kkPT R i t) (kkPauliW_kkH hm hγ hγΛ ht) hw
    fun _ hu => integrableOn_kkPT hm hγ hγΛ ht hw hu

/-- The Pauli limit of one dispersion integral of the pointwise limit, with its value. -/
theorem piecePauli_kkDisp_val (f : Fin 3) (hMf : R.m ≤ R.mass f) :
    PiecePauli R.m (fun p' p μ =>
      dispMat (dispWt R f) (fun x μ => Matrix.of fun a b => kkLimX (kkH i R p p' (R.mass f) μ a b)
        x) μ) (∫ x in Ioo (0 : ℝ) 1, dispWt R f x * kkLimP R i (R.mass f) x) := by
  have hZ := tendsto_evenQuot_setIntegral_val (T := kkPT R i (R.mass f))
    (kkPauliW_kkH hm hγ hγΛ hMf) (integrableOn_dispWt R f)
    fun _ hu => integrableOn_kkPT hm hγ hγΛ hMf (integrableOn_dispWt R f) hu
  refine hZ.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1))] with u hu
  exact evenQuot_congr (fun v hv => (pauliNum_kkDisp hm hγ hγΛ hMf f hv).symm) hu

/-- **The Pauli limit of the longitudinal dispersive part with its value**:
`Z = -2c w_K ∑_f ∫₀¹ w_f(x) kkLimP(M_f, x) dx`. -/
theorem piecePauli_kkLimB_val (hMf : ∀ f, R.m ≤ R.mass f) :
    PiecePauli R.m (kkLimB R i) ((-2 * vpCst R * wKD R 1) *
      ∑ f, ∫ x in Ioo (0 : ℝ) 1, dispWt R f x * kkLimP R i (R.mass f) x) := by
  rw [kkLimB_fun i]
  exact (PiecePauli.sum fun f => piecePauli_kkDisp_val hm hγ hγΛ f (hMf f)).smul _

end KK

/-! ### The longitudinal kernel -/

/-- A flavour sum in dispersion form: `a ∑_f c_f ∫₀¹ ρ(v) g(M_f² t_v/m²) dv` with kernel `a g`. -/
theorem isDispPV_of_flavours' (R : Params) (hm : R.m ≠ 0) (g : ℝ → ℂ) (a : ℂ)
    (hI : ∀ f, IntegrableOn (fun v => (setCKSpecRho v : ℂ) *
      g (R.mass f ^ 2 / R.m ^ 2 * setCKSpecMass v)) (Ioo 0 1)) :
    IsDispPV R.m R.M₁ R.M₂ R.c₁ R.c₂ (fun T => a * g T) (a * ∑ f, (R.loopCoeff f : ℂ) *
      ∫ v in Ioo (0 : ℝ) 1, (setCKSpecRho v : ℂ) *
        g (R.mass f ^ 2 / R.m ^ 2 * setCKSpecMass v)) := by
  set X : Fin 3 → ℝ → ℂ := fun f v => (setCKSpecRho v : ℂ) *
    g (R.mass f ^ 2 / R.m ^ 2 * setCKSpecMass v) with hX
  have hX0 : IntegrableOn (X 0) (Ioo 0 1) := hI 0
  have hX1 : IntegrableOn (fun v => (R.c₁ : ℂ) * X 1 v) (Ioo 0 1) := (hI 1).const_mul _
  have hX2 : IntegrableOn (fun v => (R.c₂ : ℂ) * X 2 v) (Ioo 0 1) := (hI 2).const_mul _
  have hX01 : IntegrableOn (fun v => X 0 v + (R.c₁ : ℂ) * X 1 v) (Ioo 0 1) := hX0.add hX1
  have hS : IntegrableOn (fun v => a * (X 0 v + (R.c₁ : ℂ) * X 1 v + (R.c₂ : ℂ) * X 2 v))
      (Ioo 0 1) := (hX01.add hX2).const_mul a
  have h0 : R.mass 0 ^ 2 / R.m ^ 2 = 1 := by
    rw [show R.mass 0 = R.m from rfl, div_self (pow_ne_zero 2 hm)]
  have e : ∀ v, dispPVF R.m R.M₁ R.M₂ R.c₁ R.c₂ (fun T => a * g T) v =
      a * (X 0 v + (R.c₁ : ℂ) * X 1 v + (R.c₂ : ℂ) * X 2 v) := fun v => by
    simp only [hX, dispPVF, h0, one_mul]
    rw [show R.mass 1 = R.M₁ from rfl, show R.mass 2 = R.M₂ from rfl]
    ring
  refine ⟨hS.congr_fun (fun v _ => (e v).symm) measurableSet_Ioo, ?_⟩
  simp only [e]
  rw [integral_const_mul, integral_add hX01 hX2, integral_add hX0 hX1, integral_const_mul,
    integral_const_mul, Fin.sum_univ_three]
  rw [show R.loopCoeff 0 = 1 from rfl, show R.loopCoeff 1 = R.c₁ from rfl,
    show R.loopCoeff 2 = R.c₂ from rfl]
  push_cast
  ring

/-- The longitudinal kernel: the Pauli limit at `x = 1/2` with the spectral mass `√(m² T)/2`,
divided by `4`. -/
noncomputable def kerK (P₀ : Params) (i : Fin 12) (mγ Λ T : ℝ) : ℂ :=
  1 / 4 * kkLimP { P₀ with mγ := mγ, Λ := Λ } i (√(P₀.m ^ 2 * T) / 2) (1 / 2)

theorem kkHalfMass_eq {m M x : ℝ} (hm : m ≠ 0) (hM : 0 ≤ M) (hx : x ∈ Ioo (0 : ℝ) 1) :
    kkHalfMass M x = √(m ^ 2 * (M ^ 2 / m ^ 2 * (1 / (x * (1 - x))))) / 2 := by
  have h0 := QED.TwoLoop.VPHalfAtAssembly.mem_Ioo_mul_pos hx
  have hs : 0 < √(x * (1 - x)) := Real.sqrt_pos.2 h0
  have e : m ^ 2 * (M ^ 2 / m ^ 2 * (1 / (x * (1 - x)))) = (M / √(x * (1 - x))) ^ 2 := by
    rw [div_pow, Real.sq_sqrt h0.le]
    field_simp
  rw [e, Real.sqrt_sq (div_nonneg hM hs.le), kkHalfMass]
  field_simp

/-- **The descaled Pauli limit is the kernel**: `kkLimP(M, x) = (x(1-x))⁻¹ kerK(M²/(m² x(1-x)))`. -/
theorem kkLimP_eq_kerK {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} (i : Fin 12) (hm : 0 < P₀.m)
    (hγ : 0 < mγ) (hγΛ : mγ ≤ Λ) {M : ℝ} (hM : P₀.m ≤ M) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    kkLimP (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) i M x =
      ((x * (1 - x) : ℝ) : ℂ)⁻¹ * kerK P₀ i mγ Λ (M ^ 2 / P₀.m ^ 2 * (1 / (x * (1 - x)))) := by
  rw [kkLimP_descale (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ hM hx,
    kkHalfMass_eq hm.ne' (hm.le.trans hM) hx]
  have e : kkLimP (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) i
      (√(P₀.m ^ 2 * (M ^ 2 / P₀.m ^ 2 * (1 / (x * (1 - x))))) / 2) (1 / 2) =
      kkLimP { P₀ with mγ := mγ, Λ := Λ } i
        (√(P₀.m ^ 2 * (M ^ 2 / P₀.m ^ 2 * (1 / (x * (1 - x))))) / 2) (1 / 2) := rfl
  rw [e, kerK, Complex.ofReal_mul, mul_inv]
  push_cast
  ring

/-- The kernel of the longitudinal dispersive part of the main placement `i`:
`-(c w_K/(64 e m⁵)) kerK`. -/
noncomputable def uBDK (P₀ : Params) (i : Fin 12) (mγ Λ T : ℝ) : ℂ :=
  -(vpCst P₀ * wKD { P₀ with mγ := mγ, Λ := Λ } 1 / (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5)) *
    kerK P₀ i mγ Λ T

/-- **The longitudinal dispersive part of a main placement is in dispersion form**: its Pauli
limit `Z` exists and `-Z/(64 e m⁵)` has the kernel `uBDK i`. -/
theorem isDispPV_dispK {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}
    (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (i : Fin 12) :
    ∃ Z : ℂ, PiecePauli P₀.m (kkLimB (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) i) Z ∧
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uBDK P₀ i mγ Λ) (-Z / (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5)) := by
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  have hMf := setCAdm_mass hA
  set R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ
  have hwc : Continuous fun x => (bubWt x : ℂ) := by unfold bubWt; fun_prop
  have hw : IntegrableOn (fun x => (bubWt x : ℂ)) (Ioo 0 1) :=
    hwc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hf : ∀ f : Fin 3, IntegrableOn (fun v => (setCKSpecRho v : ℂ) *
        kerK P₀ i mγ Λ (R.mass f ^ 2 / R.m ^ 2 * setCKSpecMass v)) (Ioo 0 1) ∧
      ∫ x in Ioo (0 : ℝ) 1, (bubWt x : ℂ) * kkLimP R i (R.mass f) x =
        -(1 / 2) * ∫ v in Ioo (0 : ℝ) 1, (setCKSpecRho v : ℂ) *
          kerK P₀ i mγ Λ (R.mass f ^ 2 / R.m ^ 2 * setCKSpecMass v) := fun f =>
    integral_bubWt_eq (g := fun t => kerK P₀ i mγ Λ (R.mass f ^ 2 / R.m ^ 2 * t))
      (integrableOn_mul_kkLimP (R := R) hm hγ hγΛ (hMf f) hw)
      fun x hx => kkLimP_eq_kerK i hm hγ hγΛ (hMf f) hx
  refine ⟨_, piecePauli_kkLimB_val (R := R) hm hγ hγΛ hMf, ?_⟩
  have h : IsDispPV P₀.m M₁ M₂ c₁ c₂ (uBDK P₀ i mγ Λ) _ :=
    isDispPV_of_flavours' R hm.ne' (kerK P₀ i mγ Λ)
      (-(vpCst P₀ * wKD { P₀ with mγ := mγ, Λ := Λ } 1 / (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5)))
      fun f => (hf f).1
  refine ⟨h.1, ?_⟩
  rw [← h.2]
  have hv : vpCst R = vpCst P₀ := rfl
  have hw' : wKD R 1 = wKD { P₀ with mγ := mγ, Λ := Λ } 1 := rfl
  simp only [dispWt_eq, mul_assoc, integral_const_mul, (hf _).2, hv, hw']
  simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

/-! ### The main placements in dispersion form -/

/-- The kernel of the main placement `i`: transverse plus longitudinal. -/
noncomputable def uBD (P₀ : Params) (i : Fin 12) (mγ Λ T : ℝ) : ℂ :=
  uBDT P₀ i mγ Λ T + uBDK P₀ i mγ Λ T

/-- **The input `hMainBD`**: at the set (c) data, `repB i + repD i 0 + repD i 1` (canonical
Pauli values) is in dispersion form with the kernel `uBD P₀ i`. -/
theorem isDispPV_mainBD {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}
    (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (i : Fin 12) :
    IsDispPV P₀.m M₁ M₂ c₁ c₂ (uBD P₀ i mγ Λ)
      (clsPauliLim mainFam P₀ (.inl i) M₁ M₂ c₁ c₂ mγ Λ D s +
        clsPauliLim mainFam P₀ (.inr (i, 0)) M₁ M₂ c₁ c₂ mγ Λ D s +
        clsPauliLim mainFam P₀ (.inr (i, 1)) M₁ M₂ c₁ c₂ mγ Λ D s) := by
  obtain ⟨Z, hZ, hK⟩ := isDispPV_dispK hA i
  have h : IsDispPV P₀.m M₁ M₂ c₁ c₂ (uBD P₀ i mγ Λ) _ := (isDispPV_dispD hA i).add hK
  refine ⟨h.1, ?_⟩
  rw [clsPauliLim_mainBD_eq hA i hZ, ← h.2]
  ring

end QED.ChainProof.SetCRegDisp

end
