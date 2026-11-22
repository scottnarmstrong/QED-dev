/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCt01
public import QED.ChainProof.SetCRegDispCtLoLin
import QED.TwoLoop.VPHalfAtAssemblyMatch
import QED.TwoLoop.MassScalingCt
import QED.TwoLoop.MassScalingVP
import QED.TwoLoop.MassScalingCounterterm
import QED.TwoLoop.VPUnitNestedD3

/-!
# Set (c): `CBₖ + CDₖ,₀ + CDₖ,₁`, `k = 0, 1`: the `δ₂` part, and the corrected value

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtCB`
of `QED.ChainProof.SetCRegDisp.setCRegLimitDisp_of_pieces`, placements `k = 0, 1`.

**The sign.** By `QED.ChainProof.SetCRegDisp.cb01Zero_split` and `cdOutZero_split`, the
`δ₂` part of `CBₖ + CDₖ,₀ + CDₖ,₁` (`k < 2`) is `δ₂(0) (vpZero - 2 d3Zero)/(64 e m⁵)`, while the
classes `k ≥ 2` are `-δ₁(0) (vpZero - 2 d3Zero)/(64 e m⁵)`: a self-energy insertion on a line
and a vertex insertion enter with **opposite** signs (`3 δ₁ - 2 δ₂ = δ₁` over the five
placements). With `δ₂(0) = -A₀ = δ₁(0)` the `δ₂` part is `-cbVPKer`, not `cbVPKer`. The mass
part `b ∂S/∂m_d` enters with the same sign as the `δ₂` part (`Y = δ₂ A + b`), so the value
expected in `QED.ChainProof.SetCRegDisp.CBLoEq` has the wrong overall sign: the corrected value
is `cbLoValC = -cbLoVal`, kernel `cb01KerC = -cb01Ker`.

## Main statements

* **`vpSub_unit_eq`**: `(vpZero - 2 d3Zero(δ₃(0)))/(64 e m⁵) = -i e⁴/(16π⁴) ∑_f c_f vpFlavour`
  at unit masses (the subtracted bubble half, `vpHalfSub_of_assembly`);
* `cbLoB`: the mass part, the Phase 4 values at `cbBParams`; `cbLoW`: its expected value
  `-i e⁴/(16π⁴) (δ₂(0) - δ_m(0)) ∑_f c_f vpFlavourW`;
* **`ctPauliAll_CB_lo_eq`**: `CBₖ + CDₖ,₀ + CDₖ,₁ = i e⁴/(16π⁴) A₀ ∑_f c_f vpFlavour + cbLoB`
  for `k < 2`, unconditionally;
* `cbLoValC`, `CBLoEqC`, `CBLoBEq`; **`cbLoEqC_iff`**: `CBLoEqC ↔ CBLoBEq`;
* `cb01KerC`, **`isDispPV_cbLoValC`**, **`isDispPV_CB_of_lo_eqC`**: `hCtCB` for all `k` from
  `CBLoEqC` (kernels `uCBOf P₀ (fun _ => cb01KerC P₀)`).

## What remains

`CBLoBEq`, the mass-derivative part: the vertex with `∂S/∂m_d` on one open line.
-/

@[expose] public section

open Complex Real Set Filter Topology MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCK QED.ChainProof.SetCPauli
open QED.ChainProof.SetAPauli (regParams regFlavors)
open QED.TwoLoop.VPUnit (vpInsert vpFlavour)
open QED.TwoLoop.PauliZeroExplicit (vpZero d3Zero ctZero)
open QED.TwoLoop.MassScaling (unitMass)
open QED.OneLoop.VertexLimit (chargeA0 chargeZ)

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

/-! ### The subtracted bubble half at unit mass -/

/-- **The subtracted bubble half**: `(vpZero - 2 d3Zero)/(64 e m⁵)` at the regulated parameters
and the level-`0` photon counterterm is `-i e⁴/(16π⁴) ∑_f c_f vpFlavour` at unit masses. -/
theorem vpSub_unit_eq (he : P₀.e ≠ 0) (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) :
    (vpZero (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) -
        2 * d3Zero (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s)) / (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5) =
      -I * ((P₀.e ^ 4 / (16 * π ^ 4) *
        ∑ f, (unitMass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)).loopCoeff f *
          vpFlavour ((unitMass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)).mass f)
            (unitMass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)).mγ
            (unitMass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)).Λ : ℝ) : ℂ) := by
  have hd3 := setCAdm_d3_zero hA
  obtain ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, hΛ, hmΛ, hm2, -, -⟩ := hA
  have hm : 0 < P₀.m := by linarith
  set R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ
  set cd := cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s
  set U := unitMass R with hU
  have hUm : U.m = 1 := QED.TwoLoop.MassScaling.unitMass_m hm.ne'
  have hmi : 0 < P₀.m⁻¹ := inv_pos.2 hm
  have hvp : vpZero U = (P₀.m⁻¹ : ℂ) ^ 5 * vpZero R := by
    have := QED.TwoLoop.MassScaling.vpZero_massScale R hm hmγ hΛ hM₁.le hM₂.le hmi
    push_cast at this
    exact this
  have hd3s : d3Zero (unitMass cd) = (P₀.m⁻¹ : ℂ) ^ 5 * d3Zero cd := by
    have := QED.TwoLoop.MassScaling.d3Zero_massScale cd hm hmγ hΛ hmi
    push_cast at this
    exact this
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
  unfold QED.TwoLoop.VPHalf.VPHalfSub at hsub
  rw [hUm] at hsub
  set S : ℝ := P₀.e ^ 4 / (16 * π ^ 4) *
    ∑ f, U.loopCoeff f * vpFlavour (U.mass f) U.mγ U.Λ with hS
  have key : -vpZero U - 2 * d3Zero (QED.TwoLoop.VPHalf.subtractedParams U) =
      64 * I * ((P₀.e : ℂ) * (S : ℂ)) := by
    have h := hsub
    field_simp at h
    have hUe : U.e = P₀.e := rfl
    rw [h, hS, hUe]
    push_cast
    ring
  rw [hvp, ← neg_neg (d3Zero (QED.TwoLoop.VPHalf.subtractedParams U)), ← hneg, hd3s] at key
  have hm0 : (P₀.m : ℂ) ≠ 0 := ofReal_ne_zero.2 hm.ne'
  have he0 : (P₀.e : ℂ) ≠ 0 := ofReal_ne_zero.2 he
  have hm5 : (P₀.m : ℂ) ^ 5 * ((P₀.m : ℂ)⁻¹) ^ 5 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hm0, one_pow]
  rw [div_eq_iff (by simp [hm0, he0])]
  linear_combination (-(P₀.m : ℂ) ^ 5) * key -
    (vpZero R - 2 * d3Zero cd) * hm5

/-- The unit-mass flavour sum in the variables of `cbLoVal`. -/
theorem sum_unitMass_flavour (g : ℝ → ℝ → ℝ → ℝ) (hm : 0 < P₀.m) :
    ∑ f, (unitMass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)).loopCoeff f *
        g ((unitMass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)).mass f)
          (unitMass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)).mγ
          (unitMass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)).Λ =
      g 1 (mγ / P₀.m) (Λ / P₀.m) + c₁ * g (M₁ / P₀.m) (mγ / P₀.m) (Λ / P₀.m) +
        c₂ * g (M₂ / P₀.m) (mγ / P₀.m) (Λ / P₀.m) := by
  simp only [Fin.sum_univ_three, QED.WickModel.Params.loopCoeff, QED.WickModel.Params.mass,
    unitMass, QED.TwoLoop.MassScaling.massScale, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, inv_mul_eq_div]
  rw [div_self hm.ne']
  simp only [one_mul]

/-! ### The mass part and the corrected value -/

/-- **The mass part of `CBₖ + CDₖ,₀ + CDₖ,₁`, `k < 2`**: the Phase 4 values of `CBₖ` and of
the two `CDₖ t` at the parameters `cbBParams` (`Y = (δ₂ - δ_m) m`, `c = 2m (δ_m - δ₂) m`),
divided by `64 e m⁵` (`0` off the positivity conditions). -/
noncomputable def cbLoB (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt) (s : ℝ × ℝ × ℝ)
    (k : Fin 5) : ℂ :=
  if h : 0 < P₀.m ∧ 0 < mγ ∧ 0 < Λ ∧ P₀.m ≤ M₁ ∧ P₀.m ≤ M₂ then
    (cb01Zero (cbBParams (cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0)) h.1 h.2.1 h.2.2.1 h.2.2.2.1
        h.2.2.2.2 P₀.m (if k = 0 then 1 else 0) +
      2 * (if k = 0 then cdOutZero (cbBParams (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s))
        else cdInZero (cbBParams (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s)))) /
      (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5)
  else 0

/-- The flavour sum `∑_f c_f vpFlavourW(M_f/m, m_γ/m, Λ/m)` of the mass part. -/
noncomputable def cbLoWSum (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) : ℝ :=
  vpFlavourW 1 (mγ / P₀.m) (Λ / P₀.m) + c₁ * vpFlavourW (M₁ / P₀.m) (mγ / P₀.m) (Λ / P₀.m) +
    c₂ * vpFlavourW (M₂ / P₀.m) (mγ / P₀.m) (Λ / P₀.m)

/-- The expected value of the mass part: `-i e⁴/(16π⁴) (δ₂(0) - δ_m(0)) ∑_f c_f vpFlavourW`. -/
noncomputable def cbLoW (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) : ℂ :=
  -I * ((P₀.e ^ 4 / (16 * π ^ 4) * cb01B P₀ mγ Λ * cbLoWSum P₀ M₁ M₂ c₁ c₂ mγ Λ : ℝ) : ℂ)

/-- **The mass part identity** (open). -/
def CBLoBEq (P₀ : Params) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5, k < 2 →
    cbLoB P₀ M₁ M₂ c₁ c₂ mγ Λ D s k = cbLoW P₀ M₁ M₂ c₁ c₂ mγ Λ

/-- The `δ₂` part: `i e⁴/(16π⁴) A₀ ∑_f c_f vpFlavour(M_f/m, m_γ/m, Λ/m)`. -/
noncomputable def cbLoD (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) : ℂ :=
  I * ((P₀.e ^ 4 / (16 * π ^ 4) * chargeA0 P₀.e P₀.m mγ Λ *
    (vpFlavour 1 (mγ / P₀.m) (Λ / P₀.m) + c₁ * vpFlavour (M₁ / P₀.m) (mγ / P₀.m) (Λ / P₀.m) +
      c₂ * vpFlavour (M₂ / P₀.m) (mγ / P₀.m) (Λ / P₀.m)) : ℝ) : ℂ)

/-- **`CBₖ + CDₖ,₀ + CDₖ,₁`, `k < 2`, is the `δ₂` part plus the mass part.** -/
theorem ctPauliAll_CB_lo_eq (he : P₀.e ≠ 0) (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (k : Fin 5)
    (hk : k < 2) :
    ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s =
      cbLoD P₀ M₁ M₂ c₁ c₂ mγ Λ + cbLoB P₀ M₁ M₂ c₁ c₂ mγ Λ D s k := by
  have hU := vpSub_unit_eq he hA
  have hon := setCAdm_onShell_zero hA
  obtain ⟨hM₁, hM₂, -, -, hmγ, hΛ, hmΛ, hm2, -, -⟩ := id hA
  have hm : 0 < P₀.m := by linarith
  have hk' : ¬ 2 ≤ k := not_le.mpr hk
  set Pc := cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0
  set cd := cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s
  set d : Fin 2 := if k = 0 then 1 else 0
  set K : ℂ := 64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5
  have hδ : ∀ x : ℝ, x = P₀.e ^ 2 * D.d₂ (.inl 0) 0 → (x : ℂ) = -(chargeA0 P₀.e P₀.m mγ Λ : ℂ) :=
    fun x hx => by rw [hx, hon.1, onShellδ₂_lzParams hm hmγ hΛ]; push_cast; ring
  have hPc : (Pc.δ₂ : ℂ) = -(chargeA0 P₀.e P₀.m mγ Λ : ℂ) := hδ _ rfl
  have hcd : (cd.δ₂ : ℂ) = -(chargeA0 P₀.e P₀.m mγ Λ : ℂ) := hδ _ (by
    show P₀.e ^ (2 * (0 + 1)) * D.d₂ (.inl 0) 0 = _
    norm_num)
  have hvp : vpZero Pc = vpZero (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) := rfl
  have hCB : ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s =
      ((Pc.δ₂ : ℂ) * vpZero Pc +
        cb01Zero (cbBParams Pc) hm hmγ hΛ hM₁.le hM₂.le P₀.m d) / K := by
    simp only [ctPauliAll, ctPauliVal, hk', ite_false, ctPauliX]
    rw [clsPauliLim_cb01_eq hA k hk hm hmγ hΛ]
    exact congrArg (· / K) (cb01Zero_split Pc hm hmγ hΛ hM₁.le hM₂.le d)
  have hX : (if k = 0 then cdOutZero cd else cdInZero cd) =
      -(cd.δ₂ : ℂ) * d3Zero cd +
        (if k = 0 then cdOutZero (cbBParams cd) else cdInZero (cbBParams cd)) := by
    split_ifs
    · exact cdOutZero_split cd hm hmγ hΛ
    · exact cdInZero_split cd hm hmγ hΛ
  have hCD : ∀ t : Fin 2, ctPauliAll P₀ (.inr (.inl (k, t))) M₁ M₂ c₁ c₂ mγ Λ D s =
      (-(cd.δ₂ : ℂ) * d3Zero cd +
        (if k = 0 then cdOutZero (cbBParams cd) else cdInZero (cbBParams cd))) / K := by
    intro t
    simp only [ctPauliAll, ctPauliVal, hk', ite_false, ctPauliX, cd01PauliVal]
    exact congrArg (· / K) hX
  have hB : cbLoB P₀ M₁ M₂ c₁ c₂ mγ Λ D s k =
      (cb01Zero (cbBParams Pc) hm hmγ hΛ hM₁.le hM₂.le P₀.m d +
        2 * (if k = 0 then cdOutZero (cbBParams cd) else cdInZero (cbBParams cd))) / K := by
    rw [cbLoB, dite_eq_left ⟨hm, hmγ, hΛ, hM₁.le, hM₂.le⟩]
  have hD : cbLoD P₀ M₁ M₂ c₁ c₂ mγ Λ = -(chargeA0 P₀.e P₀.m mγ Λ : ℂ) *
      ((vpZero (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) - 2 * d3Zero cd) / K) := by
    rw [hU, sum_unitMass_flavour (fun M a b => vpFlavour M a b) hm, cbLoD]
    push_cast
    ring
  rw [hCB, hCD 0, hCD 1, hB, hD, hPc, hcd, hvp]
  ring

/-- **The corrected value of `CBₖ + CDₖ,₀ + CDₖ,₁`, `k = 0, 1`**: `-cbLoVal`. -/
noncomputable def cbLoValC (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) : ℂ :=
  -cbLoVal P₀ M₁ M₂ c₁ c₂ mγ Λ

/-- **The explicit value of `CBₖ + CDₖ,₀ + CDₖ,₁` for `k = 0, 1`**, corrected sign. -/
def CBLoEqC (P₀ : Params) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5, k < 2 →
    ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s =
      cbLoValC P₀ M₁ M₂ c₁ c₂ mγ Λ

theorem cbLoValC_eq (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) :
    cbLoValC P₀ M₁ M₂ c₁ c₂ mγ Λ = cbLoD P₀ M₁ M₂ c₁ c₂ mγ Λ + cbLoW P₀ M₁ M₂ c₁ c₂ mγ Λ := by
  simp only [cbLoValC, cbLoVal, cbLoFl, cbLoD, cbLoW, cbLoWSum]
  push_cast
  ring

/-- **The corrected value identity is exactly the mass part identity.** -/
theorem cbLoEqC_iff (he : P₀.e ≠ 0) : CBLoEqC P₀ ↔ CBLoBEq P₀ := by
  constructor
  · intro h M₁ M₂ c₁ c₂ mγ Λ D s hA k hk
    have e := h M₁ M₂ c₁ c₂ mγ Λ D s hA k hk
    rw [ctPauliAll_CB_lo_eq he hA k hk, cbLoValC_eq] at e
    exact add_left_cancel e
  · intro h M₁ M₂ c₁ c₂ mγ Λ D s hA k hk
    rw [ctPauliAll_CB_lo_eq he hA k hk, cbLoValC_eq, h M₁ M₂ c₁ c₂ mγ Λ D s hA k hk]

/-! ### `hCtCB` from the corrected value -/

/-- **The corrected kernel for `k = 0, 1`**: `-cb01Ker`. -/
noncomputable def cb01KerC (P₀ : Params) (mγ Λ T : ℝ) : ℂ := -cb01Ker P₀ mγ Λ T

section Lo

variable (hm : 0 < P₀.m) (hmγ : 0 < mγ) (hmΛ : mγ < Λ) (hm2 : mγ < 2 * P₀.m)
include hm hmγ hmΛ hm2

/-- **The corrected value is in dispersion form** with kernel `cb01KerC`. -/
theorem isDispPV_cbLoValC (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂) :
    IsDispPV P₀.m M₁ M₂ c₁ c₂ (cb01KerC P₀ mγ Λ) (cbLoValC P₀ M₁ M₂ c₁ c₂ mγ Λ) := by
  have h := isDispPV_of_flavours (c₁ := c₁) (c₂ := c₂) hm hM₁.le hM₂.le (-I) (cb01F P₀ mγ Λ)
    fun M hM => integrableOn_rho_cb01F hm hmγ hmΛ hm2 hM
  have e : (fun T => -I * (cb01F P₀ mγ Λ T : ℂ)) = cb01KerC P₀ mγ Λ := by
    funext T
    rw [cb01KerC, cb01Ker_eq]
    ring
  have h0 := integral_rho_cb01F hm hmγ hmΛ hm2 (M := P₀.m) le_rfl
  rw [div_self hm.ne'] at h0
  rw [e, h0, integral_rho_cb01F hm hmγ hmΛ hm2 hM₁.le,
    integral_rho_cb01F hm hmγ hmΛ hm2 hM₂.le] at h
  have e2 : cbLoValC P₀ M₁ M₂ c₁ c₂ mγ Λ = -I * ((cbLoFl P₀ mγ Λ 1 +
      c₁ * cbLoFl P₀ mγ Λ (M₁ / P₀.m) + c₂ * cbLoFl P₀ mγ Λ (M₂ / P₀.m) : ℝ) : ℂ) := by
    rw [cbLoValC, cbLoVal]
    ring
  rw [e2]
  exact h

end Lo

/-- **`hlow` from the corrected value.** -/
theorem isDispPV_CB_lo_of_eqC (hval : CBLoEqC P₀) :
    ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5, k < 2 →
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (cb01KerC P₀ mγ Λ)
        (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
          ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
          ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA k hk
  rw [hval M₁ M₂ c₁ c₂ mγ Λ D s hA k hk]
  obtain ⟨hM₁, hM₂, -, -, hmγ, -, hmΛ, hm2, -, -⟩ := hA
  have hm : 0 < P₀.m := by linarith
  exact isDispPV_cbLoValC hm hmγ hmΛ hm2 hM₁ hM₂

/-- **`hCtCB` from the corrected value `CBLoEqC`**, with the kernels
`uCBOf P₀ (fun _ => cb01KerC P₀)`. -/
theorem isDispPV_CB_of_lo_eqC (he : P₀.e ≠ 0) (hval : CBLoEqC P₀) :
    ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uCBOf P₀ (fun _ => cb01KerC P₀) k mγ Λ)
        (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
          ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
          ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s) :=
  isDispPV_CB_of_low he (isDispPV_CB_lo_of_eqC hval)

/-- **`hCtCB` from the mass part identity `CBLoBEq`.** -/
theorem isDispPV_CB_of_loB (he : P₀.e ≠ 0) (hB : CBLoBEq P₀) :
    ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uCBOf P₀ (fun _ => cb01KerC P₀) k mγ Λ)
        (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
          ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
          ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s) :=
  isDispPV_CB_of_lo_eqC he ((cbLoEqC_iff he).2 hB)

end QED.ChainProof.SetCRegDisp

end
