/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispMain
public import QED.TwoLoop.VacuumPolarizationUnitLimit
public import QED.TwoLoop.UnitVPLink
public import QED.TwoLoop.MassScalingUnits
public import QED.OneLoop.ChargeCondition
import QED.TwoLoop.VPHalfAtAssemblyMatch
import QED.TwoLoop.MassScalingCt
import QED.TwoLoop.MassScalingVP
import QED.TwoLoop.MassScalingCounterterm
import QED.TwoLoop.VPUnitNestedD3
import QED.LeptonProof.HMPhoton
import QED.GradedProof.LevelOneCharge
import QED.GradedProof.LevelOnePhoton

/-!
# Set (c): the counterterm classes `CBₖ + CDₖ,₀ + CDₖ,₁`, `k ≥ 2`, in dispersion form

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtCB` of
`QED.ChainProof.SetCRegDisp.setCRegLimitDisp_of_pieces`. For `k ≥ 2` the class `CBₖ` is the
level-`0` vertex counterterm `δ₁(0)` times the two-loop VP class, and the two classes `CDₖ,ₜ` are
`δ₁(0)` times the two `δ₃` classes at the level-`0` photon counterterm. Their sum is
`δ₁(0) (-vpZero + 2 d3Zero)/(64 e m⁵)`, the subtracted bubble half of the Phase 4 VP unit:

* the level-`0` data at an admissible datum: `e² d₁(0) = Z₁ - 1 = -A₀(e, m, m_γ, Λ)` by the
  charge condition (`setCAdm_d1_zero`) and `e² d₃(0) = Π_loop(0)` by the photon condition
  (`setCAdm_d3_zero`);
* at unit mass (`QED.TwoLoop.MassScaling.unitMass`), the sealed subtracted bubble half
  `QED.TwoLoop.VPHalfAtAssembly.vpHalfSub_of_assembly` gives
  `-vpZero - 2 d3Zero(δ₃ = -Π_loop(0)) = 64 i e⁵/(16π⁴) ∑_f c_f vpFlavour M_f`, and the two
  `δ₃` values at `±Π_loop(0)` are opposite (`d3Zero_unit_neg`, from
  `QED.TwoLoop.VPUnitNested.unit_d3Zero`);
* `vpFlavour M = ∫₀¹ ρ(v) vpInsert(M² t_v, m_γ², Λ²) dv` with `t_v = 4/(1-v²)`
  (`vpFlavour_eq_Ioo`), each flavour integrable (`integrableOn_rho_vpInsert`).

## Main statements

* `cbVPKer P₀ m_γ Λ T = -A₀(e, m, m_γ, Λ) · i e⁴/(16π⁴) · vpInsert(T, m_γ²/m², Λ²/m²)`: the
  kernel, `δ₁(0)` times the unit-mass Pauli value of the one-loop vertex with photon function
  `k⁴/(k² + T)(1/(k² + m_γ²) - 1/(k² + Λ²))²`;
* **`ctPauliAll_CB_hi_eq`**: the explicit value of `CBₖ + CDₖ,₀ + CDₖ,₁`, `k ≥ 2`;
* **`isDispPV_CB_hi`**: it is `IsDispPV` with kernel `cbVPKer P₀ m_γ Λ`;
* `uCBOf`, **`isDispPV_CB_of_low`**: `hCtCB` with kernels `uCBOf P₀ u` from the dispersion form
  of the two placements `k = 0, 1` alone (kernels `u 0`, `u 1`).
-/

@[expose] public section

open Complex Real Set Filter Topology MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCK QED.ChainProof.SetCPauli
open QED.ChainProof.SetAPauli (regParams regFlavors)
open QED.TwoLoop.VPUnit (vpInsert vpFlavour rho regKernel)
open QED.TwoLoop.UnitVPLink (outerF2 photonD flavKernel)
open QED.TwoLoop.PauliZeroExplicit (vpZero d3Zero ctZero)
open QED.TwoLoop.MassScaling (unitMass)
open QED.OneLoop.VertexLimit (chargeA0 chargeZ)

/-- **The kernel of `CBₖ + CDₖ,₀ + CDₖ,₁`, `k ≥ 2`**: `δ₁(0)` (`= -A₀(m, m_γ, Λ)`) times the
unit-mass Pauli value `vpInsert(T, m_γ²/m², Λ²/m²)` of the one-loop vertex with the photon
function `k⁴/(k² + T)(1/(k² + m_γ²) - 1/(k² + Λ²))²`, normalized `i e⁴/(16π⁴)`. -/
noncomputable def cbVPKer (P₀ : Params) (mγ Λ T : ℝ) : ℂ :=
  -(chargeA0 P₀.e P₀.m mγ Λ : ℂ) * I *
    ((P₀.e ^ 4 / (16 * π ^ 4) * vpInsert T ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2) : ℝ) : ℂ)

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

/-! ### The level-`0` counterterms at an admissible datum -/

/-- **The level-`0` vertex counterterm** at an admissible datum: `1 + e² d₁(e⁻, 0) = Z₁`, the
unique solution `chargeZ = 1 - A₀` of the one-loop charge condition at `m, m_γ, Λ`. -/
theorem setCAdm_d1_zero (he : P₀.e ≠ 0) (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) :
    1 + P₀.e ^ 2 * D.d₁ (.inl 0) 0 =
      QED.OneLoop.VertexLimit.chargeZ P₀.e P₀.m mγ Λ := by
  obtain ⟨-, -, -, -, hmγ, hΛ, -, hm2, hD, -⟩ := hA
  have hm : 0 < P₀.m := by linarith
  obtain ⟨h1, -⟩ := hD.2 1 le_rfl (by norm_num)
  have hc := (h1 (.inl 0) rfl).2
  have hc' := (QED.GradedProof.isChargeNormalizedAt_one_iff' (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (.inl 0) hm hmγ hΛ).1 hc
  exact QED.OneLoop.VertexLimit.eq_chargeZ_of_isChargeNormalized he hm hmγ hΛ hc'

/-- **The level-`0` photon counterterm** at an admissible datum: `e² d₃(0) = Π_loop(0)`, the
flavour-summed loop function of the regulated parameters at `k² = 0`. -/
theorem setCAdm_d3_zero (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) :
    P₀.e ^ 2 * D.d₃ 0 =
      QED.WickModel.vacuumPolarizationLoop (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) 0 := by
  obtain ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, -, -, hm2, hD, -⟩ := hA
  have hm : 0 < P₀.m := by linarith
  obtain ⟨-, hph⟩ := hD.2 1 le_rfl (by norm_num)
  rw [QED.GradedProof.isPhotonOnShellAt_one_iff'] at hph
  have hok : QED.Lepton.Proof.HM.AuxOK (Fin.elim0 : Fin 0 → QED.Lepton.HeavyLepton)
      (Fin.elim0 : Fin 0 → ℝ) P₀.m :=
    ⟨fun ℓ => ℓ.elim0, fun ℓ => ℓ.elim0, fun ℓ => ℓ.elim0, fun ℓ => ℓ.elim0⟩
  have hgt : QED.Lepton.Proof.HM.AuxGt (Fin.elim0 : Fin 0 → QED.Lepton.HeavyLepton)
      (Fin.elim0 : Fin 0 → ℝ) P₀.m :=
    ⟨fun ℓ => ℓ.elim0, fun ℓ => ℓ.elim0⟩
  have h := (QED.Lepton.Proof.HM.isPhotonOnShell_leptonFlavors_iff_t1
    { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with δ₃ := P₀.e ^ 2 * D.d₃ 0 } hm hM₁ hM₂ hPV₁ hPV₂
    hok hgt).1 hph
  have h' := (QED.TwoLoop.Scaling.isPhotonOnShell_iff
    { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with δ₃ := P₀.e ^ 2 * D.d₃ 0 - ∑ ℓ : Fin 0, 0 } hm hM₁ hM₂
    hPV₁ hPV₂).1 h
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero] at h'
  exact h'

/-- One flavour of the subtracted bubble, at mass `M ≠ 0` and squared photon masses
`0 < a < b`, `a < 4M²`: `v ↦ ρ(v) vpInsert(M² t_v, a, b)` is integrable on `(0, 1)`. -/
theorem integrableOn_rho_vpInsert {M a b : ℝ} (hM : M ≠ 0) (ha : 0 < a) (hab : a < b)
    (haM : a < 4 * M ^ 2) :
    IntegrableOn (fun v => rho v * vpInsert (M ^ 2 * (4 / (1 - v ^ 2))) a b) (Ioc 0 1) := by
  have hb : 0 < b := ha.trans hab
  have hI := (QED.TwoLoop.UnitVPLink.integrable_flavKernel (M := M) hM ha.le hab.le)
  have h := hI.integral_prod_left
  refine Integrable.congr h ?_
  set S : Set ℝ := {1, √(1 - 4 * M ^ 2 / b)}
  have hS : ∀ᵐ v ∂(volume : Measure ℝ), v ∉ S :=
    measure_eq_zero_iff_ae_notMem.1 ((Set.toFinite S).measure_zero volume)
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hS] with v hvS hv
  have hv1 : v < 1 := lt_of_le_of_ne hv.2 fun h => hvS (by simp [S, h])
  have hc := QED.TwoLoop.VPUnit.specMass_pos (M := M) hM hv.1.le hv1
  have hca : 4 * M ^ 2 / (1 - v ^ 2) ≠ a :=
    (lt_of_lt_of_le haM (QED.TwoLoop.VPUnit.le_specMass hv.1.le hv1)).ne'
  have hcb : 4 * M ^ 2 / (1 - v ^ 2) ≠ b := by
    intro h
    have hs : 0 < 1 - v ^ 2 := by nlinarith [hv.1]
    have : v ^ 2 = 1 - 4 * M ^ 2 / b := by
      field_simp
      field_simp at h
      linarith
    apply hvS
    have : v = √(1 - 4 * M ^ 2 / b) := by rw [← this, sqrt_sq hv.1.le]
    simp [S, this]
  have e : M ^ 2 * (4 / (1 - v ^ 2)) = 4 * M ^ 2 / (1 - v ^ 2) := by ring
  simp only [flavKernel]
  rw [integral_const_mul, e, QED.TwoLoop.VPUnit.vpInsert_eq_integral ha hb hc hca hcb hab.ne,
    intervalIntegral.integral_of_le zero_le_one]

/-- `vpFlavour` as an integral over `(0, 1)` against the set (c) spectral data. -/
theorem vpFlavour_eq_Ioo (M mγ Λ : ℝ) :
    vpFlavour M mγ Λ = ∫ v in Ioo (0 : ℝ) 1, SetCK.setCKSpecRho v *
      vpInsert (M ^ 2 * SetCK.setCKSpecMass v) (mγ ^ 2) (Λ ^ 2) := by
  rw [vpFlavour, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun v _ => ?_
  simp only [SetCK.setCKSpecRho, SetCK.setCKSpecMass, rho]
  ring_nf

/-- `outerF2` is odd. -/
theorem outerF2_neg (R : ℝ → ℝ) : outerF2 (fun s => -R s) = -outerF2 R := by
  simp only [outerF2, mul_neg, intervalIntegral.integral_neg]


/-- At unit mass, the `δ₃` class value is odd in `δ₃` and depends only on `e, m_γ, Λ, δ₃`
(`QED.TwoLoop.VPUnitNested.unit_d3Zero`). -/
theorem d3Zero_unit_neg {X Y : Params} (hX : X.m = 1) (hY : Y.m = 1) (he : X.e = Y.e)
    (hmγ : X.mγ = Y.mγ) (hΛ : X.Λ = Y.Λ) (hδ : X.δ₃ = -Y.δ₃) (hmγ0 : 0 < X.mγ)
    (hΛ0 : 0 < X.Λ) : d3Zero X = -d3Zero Y := by
  have h1 := QED.TwoLoop.VPUnitNested.unit_d3Zero X hX hmγ0 hΛ0
  have h2 := QED.TwoLoop.VPUnitNested.unit_d3Zero Y hY (hmγ ▸ hmγ0) (hΛ ▸ hΛ0)
  have e : (fun s => -X.δ₃ * s * photonD X.mγ X.Λ s ^ 2) =
      fun s => -(-Y.δ₃ * s * photonD Y.mγ Y.Λ s ^ 2) := by
    funext s
    rw [hδ, hmγ, hΛ]
    ring
  rw [e, outerF2_neg, he, hX] at h1
  rw [hY] at h2
  have h3 : (1 : ℂ) / (64 * ((1 : ℝ) : ℂ) ^ 5) * ((1 / I) * (2 * d3Zero X)) =
      -((1 : ℂ) / (64 * ((1 : ℝ) : ℂ) ^ 5) * ((1 / I) * (2 * d3Zero Y))) := by
    rw [h1, h2]
    push_cast
    ring
  have hI : (1 / I : ℂ) ≠ 0 := by simp
  have h4 : (1 / I : ℂ) * (d3Zero X + d3Zero Y) = 0 := by
    push_cast at h3
    linear_combination 32 * h3
  rcases mul_eq_zero.1 h4 with h | h
  · exact absurd h hI
  · linear_combination h

/-- **The value of `CBₖ + CDₖ,₀ + CDₖ,₁`, `k ≥ 2`**: `-A₀ · i e⁴/(16π⁴) ∑_f c_f vpFlavour`,
the flavours at unit mass. -/
theorem ctPauliAll_CB_hi_eq (he : P₀.e ≠ 0) (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (k : Fin 5)
    (hk : 2 ≤ k) :
    ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s =
      -(chargeA0 P₀.e P₀.m mγ Λ : ℂ) * I * ((P₀.e ^ 4 / (16 * π ^ 4) *
        ∑ f, (unitMass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)).loopCoeff f *
          vpFlavour ((unitMass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)).mass f)
            (unitMass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)).mγ
            (unitMass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)).Λ : ℝ) : ℂ) := by
  have hd1 := setCAdm_d1_zero he hA
  have hd3 := setCAdm_d3_zero hA
  obtain ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, hΛ, hmΛ, hm2, -, -⟩ := hA
  have hm : 0 < P₀.m := by linarith
  set R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ
  set cd := cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s
  set U := unitMass R with hU
  have hUm : U.m = 1 := QED.TwoLoop.MassScaling.unitMass_m hm.ne'
  have hmi : 0 < P₀.m⁻¹ := inv_pos.2 hm
  -- mass scaling
  have hvp : vpZero U = (P₀.m⁻¹ : ℂ) ^ 5 * vpZero R := by
    have := QED.TwoLoop.MassScaling.vpZero_massScale R hm hmγ hΛ hM₁.le hM₂.le hmi
    push_cast at this
    exact this
  have hd3s : d3Zero (unitMass cd) = (P₀.m⁻¹ : ℂ) ^ 5 * d3Zero cd := by
    have := QED.TwoLoop.MassScaling.d3Zero_massScale cd hm hmγ hΛ hmi
    push_cast at this
    exact this
  -- the subtracted bubble half at unit mass
  have hU₁ : 1 < U.M₁ := by
    show 1 < P₀.m⁻¹ * M₁
    rw [inv_mul_eq_div, one_lt_div hm]; exact hM₁
  have hU₂ : 1 < U.M₂ := by
    show 1 < P₀.m⁻¹ * M₂
    rw [inv_mul_eq_div, one_lt_div hm]; exact hM₂
  have hUγ : 0 < U.mγ := mul_pos hmi hmγ
  have hUΛ : U.mγ < U.Λ := mul_lt_mul_of_pos_left hmΛ hmi
  have hU2 : U.mγ < 2 := by
    show P₀.m⁻¹ * mγ < 2
    rw [inv_mul_eq_div, div_lt_iff₀ hm]; linarith
  have hUc₂ : U.m ^ 2 + U.c₁ * U.M₁ ^ 2 + U.c₂ * U.M₂ ^ 2 = 0 := by
    show (P₀.m⁻¹ * P₀.m) ^ 2 + c₁ * (P₀.m⁻¹ * M₁) ^ 2 + c₂ * (P₀.m⁻¹ * M₂) ^ 2 = 0
    have : (P₀.m⁻¹ * P₀.m) ^ 2 + c₁ * (P₀.m⁻¹ * M₁) ^ 2 + c₂ * (P₀.m⁻¹ * M₂) ^ 2 =
        P₀.m⁻¹ ^ 2 * (P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2) := by ring
    rw [this, hPV₂, mul_zero]
  have hsub := QED.TwoLoop.VPHalfAtAssembly.vpHalfSub_of_assembly U hUm hU₁ hU₂ hUγ hUΛ hU2
    hPV₁ hUc₂
  -- the two `δ₃` classes against the subtraction
  have hpos : ∀ f, R.mass f ≠ 0 := by
    intro f
    fin_cases f
    · exact hm.ne'
    · exact (hm.trans hM₁).ne'
    · exact (hm.trans hM₂).ne'
  have hPi := QED.TwoLoop.MassScaling.vacuumPolarizationLoop_massScale R hpos hPV₁
    (inv_ne_zero hm.ne')
  have hneg : d3Zero (unitMass cd) =
      -d3Zero (QED.TwoLoop.VPHalf.subtractedParams U) := by
    refine d3Zero_unit_neg (QED.TwoLoop.MassScaling.unitMass_m hm.ne') hUm rfl rfl rfl ?_ hUγ
      (mul_pos hmi (hmγ.trans hmΛ))
    show P₀.e ^ (2 * (0 + 1)) * D.d₃ 0 = -(-QED.WickModel.vacuumPolarizationLoop U 0)
    rw [neg_neg, hU, unitMass, hPi, ← hd3]
  have hw : cbW P₀ D s = -(chargeA0 P₀.e P₀.m mγ Λ : ℂ) := by
    show ((P₀.e ^ 2 * D.d₁ (.inl 0) 0 : ℝ) : ℂ) = _
    have : P₀.e ^ 2 * D.d₁ (.inl 0) 0 = -chargeA0 P₀.e P₀.m mγ Λ := by
      rw [chargeZ] at hd1; linarith
    rw [this]; push_cast; ring
  have hδ₁ : (cd.δ₁ : ℂ) = cbW P₀ D s := by
    show ((P₀.e ^ (2 * (0 + 1)) * D.d₁ (.inl 0) 0 : ℝ) : ℂ) = ((P₀.e ^ 2 * D.d₁ (.inl 0) 0 : ℝ) : ℂ)
    norm_num
  -- assemble
  have hct0 : ctZero (d3Cls 0) (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) = d3Zero cd := rfl
  have hct1 : ctZero (d3Cls 1) (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) = d3Zero cd := rfl
  simp only [ctPauliAll, ctPauliVal, hk, ite_true]
  rw [hct0, hct1]
  rw [hδ₁, hw]
  unfold QED.TwoLoop.VPHalf.VPHalfSub at hsub
  rw [hUm] at hsub
  set r : ℂ := ((P₀.e ^ 5 / (16 * π ^ 4) * ∑ f, U.loopCoeff f * vpFlavour (U.mass f) U.mγ U.Λ :
    ℝ) : ℂ) with hr
  have key : -vpZero U - 2 * d3Zero (QED.TwoLoop.VPHalf.subtractedParams U) = 64 * I * r := by
    have h := hsub
    field_simp at h
    have hUe : U.e = P₀.e := rfl
    rw [h, hr, hUe]
    push_cast
    ring
  rw [hvp, ← neg_neg (d3Zero (QED.TwoLoop.VPHalf.subtractedParams U)), ← hneg, hd3s] at key
  have hm0 : (P₀.m : ℂ) ≠ 0 := ofReal_ne_zero.2 hm.ne'
  have he0 : (P₀.e : ℂ) ≠ 0 := ofReal_ne_zero.2 he
  have hr' : r = (P₀.e : ℂ) * ((P₀.e ^ 4 / (16 * π ^ 4) *
      ∑ f, U.loopCoeff f * vpFlavour (U.mass f) U.mγ U.Λ : ℝ) : ℂ) := by
    rw [hr]; push_cast; ring
  rw [hr'] at key
  field_simp
  field_simp at key
  linear_combination (-(chargeA0 P₀.e P₀.m mγ Λ : ℂ)) * key

/-- **`CBₖ + CDₖ,₀ + CDₖ,₁`, `k ≥ 2`, is a flavour-summed dispersion integral** with kernel
`cbVPKer`. -/
theorem isDispPV_CB_hi (he : P₀.e ≠ 0) (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (k : Fin 5)
    (hk : 2 ≤ k) :
    IsDispPV P₀.m M₁ M₂ c₁ c₂ (cbVPKer P₀ mγ Λ)
      (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s) := by
  rw [ctPauliAll_CB_hi_eq he hA k hk]
  obtain ⟨hM₁, hM₂, -, -, hmγ, hΛ, hmΛ, hm2, -, -⟩ := hA
  have hm : 0 < P₀.m := by linarith
  set K : ℂ := -(chargeA0 P₀.e P₀.m mγ Λ : ℂ) * I * ((P₀.e ^ 4 / (16 * π ^ 4) : ℝ) : ℂ) with hK
  set g : ℝ → ℝ → ℝ := fun M v => setCKSpecRho v *
    vpInsert (M ^ 2 * setCKSpecMass v) ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2) with hg
  have ha : 0 < (mγ / P₀.m) ^ 2 := by positivity
  have hab : (mγ / P₀.m) ^ 2 < (Λ / P₀.m) ^ 2 :=
    pow_lt_pow_left₀ (div_lt_div_of_pos_right hmΛ hm) (by positivity) two_ne_zero
  have hint : ∀ M : ℝ, P₀.m ≤ M → IntegrableOn (g (M / P₀.m)) (Ioo 0 1) := by
    intro M hM
    have hM0 : M / P₀.m ≠ 0 := (div_pos (hm.trans_le hM) hm).ne'
    have hlt : mγ / P₀.m < 2 * (M / P₀.m) := by
      rw [mul_div_assoc', div_lt_div_iff_of_pos_right hm]
      linarith
    have haM : (mγ / P₀.m) ^ 2 < 4 * (M / P₀.m) ^ 2 := by
      have := pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
      linarith [show (2 * (M / P₀.m)) ^ 2 = 4 * (M / P₀.m) ^ 2 by ring]
    exact (integrableOn_rho_vpInsert hM0 ha hab haM).mono_set Ioo_subset_Ioc_self
  have h0 := hint P₀.m le_rfl
  rw [div_self hm.ne'] at h0
  have h1 := hint M₁ hM₁.le
  have h2 := hint M₂ hM₂.le
  have hF : dispPVF P₀.m M₁ M₂ c₁ c₂ (cbVPKer P₀ mγ Λ) = fun v =>
      K * ((g 1 v + c₁ * g (M₁ / P₀.m) v + c₂ * g (M₂ / P₀.m) v : ℝ) : ℂ) := by
    funext v
    have e1 : M₁ ^ 2 / P₀.m ^ 2 * setCKSpecMass v = (M₁ / P₀.m) ^ 2 * setCKSpecMass v := by
      rw [div_pow]
    have e2 : M₂ ^ 2 / P₀.m ^ 2 * setCKSpecMass v = (M₂ / P₀.m) ^ 2 * setCKSpecMass v := by
      rw [div_pow]
    simp only [dispPVF, cbVPKer, hg, hK, e1, e2, one_pow, one_mul]
    push_cast
    ring
  have hI : IntegrableOn (fun v => g 1 v + c₁ * g (M₁ / P₀.m) v + c₂ * g (M₂ / P₀.m) v)
      (Ioo 0 1) := (h0.add (h1.const_mul c₁)).add (h2.const_mul c₂)
  have hR : ∫ v in Ioo (0 : ℝ) 1, (g 1 v + c₁ * g (M₁ / P₀.m) v + c₂ * g (M₂ / P₀.m) v) =
      (∫ v in Ioo (0 : ℝ) 1, g 1 v) + c₁ * (∫ v in Ioo (0 : ℝ) 1, g (M₁ / P₀.m) v) +
        c₂ * ∫ v in Ioo (0 : ℝ) 1, g (M₂ / P₀.m) v := by
    have h01 : IntegrableOn (fun v => g 1 v + c₁ * g (M₁ / P₀.m) v) (Ioo 0 1) :=
      h0.add (h1.const_mul c₁)
    rw [integral_add h01 (h2.const_mul c₂), integral_add h0 (h1.const_mul c₁),
      integral_const_mul, integral_const_mul]
  refine ⟨?_, ?_⟩
  · rw [hF]
    exact hI.ofReal.const_mul K
  · rw [hF, integral_const_mul, integral_complex_ofReal, hR]
    have hv : ∀ M : ℝ, vpFlavour (P₀.m⁻¹ * M) (P₀.m⁻¹ * mγ) (P₀.m⁻¹ * Λ) =
        ∫ v in Ioo (0 : ℝ) 1, g (M / P₀.m) v := by
      intro M
      rw [vpFlavour_eq_Ioo]
      simp only [hg, inv_mul_eq_div]
    have hv1 := hv P₀.m
    rw [div_self hm.ne'] at hv1
    simp only [Fin.sum_univ_three, QED.WickModel.Params.loopCoeff, QED.WickModel.Params.mass,
      unitMass, QED.TwoLoop.MassScaling.massScale, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [hv1, hv M₁, hv M₂, hK]
    push_cast
    ring


/-! ### `hCtCB` from the two placements `k = 0, 1` -/

/-- The kernels of `hCtCB`: `cbVPKer` for `k ≥ 2`, `u k` for `k = 0, 1`. -/
noncomputable def uCBOf (P₀ : Params) (u : Fin 5 → ℝ → ℝ → ℝ → ℂ) (k : Fin 5) :
    ℝ → ℝ → ℝ → ℂ :=
  if 2 ≤ k then cbVPKer P₀ else u k

/-- **`hCtCB` from the placements `k = 0, 1`**: if `CBₖ + CDₖ,₀ + CDₖ,₁` is in dispersion form
with kernel `u k` for `k < 2`, then it is for every `k`, with kernel `uCBOf P₀ u k`. -/
theorem isDispPV_CB_of_low (he : P₀.e ≠ 0) {u : Fin 5 → ℝ → ℝ → ℝ → ℂ}
    (hlow : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5, k < 2 →
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (u k mγ Λ) (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s)) :
    ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uCBOf P₀ u k mγ Λ) (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA k
  by_cases hk : 2 ≤ k
  · simp only [uCBOf, hk, ite_true]
    exact isDispPV_CB_hi he hA k hk
  · simp only [uCBOf, hk, ite_false]
    exact hlow M₁ M₂ c₁ c₂ mγ Λ D s hA k (not_le.mp hk)

end QED.ChainProof.SetCRegDisp

end
