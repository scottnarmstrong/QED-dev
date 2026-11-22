/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegMainBDSum
public import QED.ChainProof.SetCRegDispMain

/-!
# Set (c), a main placement: from the Feynman parameter of the bubble to the spectral variable

Helper level for the input `hMainBD` of `QED.ChainProof.SetCRegDisp.setCRegLimitDisp_of_pieces`.
The dispersive parts of the bubble class `repB i` are integrals over the Feynman parameter `x`
of the bubble with the weight `w(x) = (1 - 2x)(x²/2 - x³/3)` (`dispWt`, flavour coefficient
`c_f`), of values with the spectral line `x(1-x) k² + M²` that descale to `(x(1-x))⁻¹` times a
function of `M²/(x(1-x))`. The substitution `x = (1 ∓ v)/2` (so `x(1-x) = (1 - v²)/4`,
`1/(x(1-x)) = t_v`) folds the two halves of `(0, 1)` onto `v ∈ (0, 1)`, and
`w((1-v)/2) + w((1+v)/2) = -v²(1 - v²/3)/4`, so
`∫₀¹ w(x) (x(1-x))⁻¹ g(1/(x(1-x))) dx = -(1/2) ∫₀¹ ρ(v) g(t_v) dv`.

* `bubWt`, `dispWt_eq`; `integral_fold`: the folding of `(0, 1)` at `1/2`;
* **`integral_bubWt_eq`**: the change of variables, with the integrability of the result;
* `kerT`: the transverse `repB` Pauli value with an unscaled dispersion line of mass² `m² T`;
* **`unitMDispPauliRepB_eq`**: `unitMDispPauliRepB(w_f, M) = c_f (-1/2) ∫₀¹ ρ(v) kerT(M² t_v/m²)`;
* `uBDT`, **`isDispPV_dispD`**: the transverse dispersive part `-Z_D/(64 e m⁵)` of the main
  placement `i` is in dispersion form with kernel `uBDT i`.
-/

@[expose] public section

open Complex Real Set Filter Topology MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.ChainProof.SetCPauli QED.ChainProof.SetCK QED.TwoLoop.Enumeration
open QED.TwoLoop.ClassIntegrable (openClasses)
open QED.ChainProof.SetAPauli (regParams regFlavors)
open QED.TwoLoop.VPHalfAtAssembly (specMu)

/-! ### The change of variables -/

/-- The weight of the dispersive parts: `w(x) = (1 - 2x)(x²/2 - x³/3)`. -/
noncomputable def bubWt (x : ℝ) : ℝ := (1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3)

theorem dispWt_eq (R : Params) (f : Fin 3) (x : ℝ) :
    dispWt R f x = (R.loopCoeff f : ℂ) * (bubWt x : ℂ) := rfl

theorem image_fold_left : (fun v : ℝ => (1 - v) / 2) '' Ioo 0 1 = Ioo 0 (1 / 2) := by
  ext x
  constructor
  · rintro ⟨v, ⟨h0, h1⟩, rfl⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h0, h1⟩
    exact ⟨1 - 2 * x, ⟨by linarith, by linarith⟩, by ring⟩

theorem image_fold_right : (fun v : ℝ => (1 + v) / 2) '' Ioo 0 1 = Ioo (1 / 2) 1 := by
  ext x
  constructor
  · rintro ⟨v, ⟨h0, h1⟩, rfl⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h0, h1⟩
    exact ⟨2 * x - 1, ⟨by linarith, by linarith⟩, by ring⟩

/-- **Folding `(0, 1)` at `1/2`**: if `F((1-v)/2) + F((1+v)/2) = G(v)` on `(0, 1)` and `F` is
integrable on `(0, 1)`, then `G` is integrable on `(0, 1)` and `∫₀¹ F = (1/2) ∫₀¹ G`. -/
theorem integral_fold {F G : ℝ → ℂ} (hF : IntegrableOn F (Ioo 0 1))
    (hFG : ∀ v ∈ Ioo (0 : ℝ) 1, F ((1 - v) / 2) + F ((1 + v) / 2) = G v) :
    IntegrableOn G (Ioo 0 1) ∧ ∫ x in Ioo (0 : ℝ) 1, F x = 1 / 2 * ∫ v in Ioo (0 : ℝ) 1, G v := by
  have hd₁ : ∀ v ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun v : ℝ => (1 - v) / 2) ((fun _ => -1 / 2) v) (Ioo 0 1) v :=
    fun v _ => (((hasDerivAt_id v).const_sub 1).div_const 2).hasDerivWithinAt
  have hd₂ : ∀ v ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun v : ℝ => (1 + v) / 2) ((fun _ => 1 / 2) v) (Ioo 0 1) v :=
    fun v _ => (((hasDerivAt_id v).const_add 1).div_const 2).hasDerivWithinAt
  have hi₁ : InjOn (fun v : ℝ => (1 - v) / 2) (Ioo 0 1) := fun a _ b _ h => by
    simp only at h
    linarith
  have hi₂ : InjOn (fun v : ℝ => (1 + v) / 2) (Ioo 0 1) := fun a _ b _ h => by
    simp only at h
    linarith
  have hF₁ : IntegrableOn F ((fun v : ℝ => (1 - v) / 2) '' Ioo 0 1) := by
    rw [image_fold_left]
    exact hF.mono_set (Ioo_subset_Ioo_right (by norm_num))
  have hF₂ : IntegrableOn F ((fun v : ℝ => (1 + v) / 2) '' Ioo 0 1) := by
    rw [image_fold_right]
    exact hF.mono_set (Ioo_subset_Ioo_left (by norm_num))
  have hA := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hd₁ hi₁ F).1
    hF₁
  have hB := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hd₂ hi₂ F).1
    hF₂
  have eA : ∀ v, |(fun _ : ℝ => (-1 / 2 : ℝ)) v| • F ((1 - v) / 2) =
      (1 / 2 : ℂ) * F ((1 - v) / 2) := fun v => by
    simp only [abs_div, abs_neg, abs_one, abs_two, Complex.real_smul]
    push_cast
    ring
  have eB : ∀ v, |(fun _ : ℝ => (1 / 2 : ℝ)) v| • F ((1 + v) / 2) =
      (1 / 2 : ℂ) * F ((1 + v) / 2) := fun v => by
    simp only [abs_div, abs_one, abs_two, Complex.real_smul]
    push_cast
    ring
  simp only [eA, eB] at hA hB
  have hG : EqOn (fun v => (2 : ℂ) * ((1 / 2 : ℂ) * F ((1 - v) / 2) +
      (1 / 2 : ℂ) * F ((1 + v) / 2))) G (Ioo 0 1) := fun v hv => by
    simp only
    rw [← hFG v hv]
    ring
  have hAB : IntegrableOn (fun v => (2 : ℂ) * ((1 / 2 : ℂ) * F ((1 - v) / 2) +
      (1 / 2 : ℂ) * F ((1 + v) / 2))) (Ioo 0 1) := (hA.add hB).const_mul 2
  refine ⟨hAB.congr_fun hG measurableSet_Ioo, ?_⟩
  have hsplit : ∫ x in Ioo (0 : ℝ) 1, F x =
      (∫ x in Ioo (0 : ℝ) (1 / 2), F x) + ∫ x in Ioo (1 / 2 : ℝ) 1, F x := by
    rw [← Ioc_union_Ioo_eq_Ioo (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1),
      setIntegral_union (Set.disjoint_left.2 fun x hx hx' => by linarith [hx.2, hx'.1])
        measurableSet_Ioo
        (hF.mono_set (Ioc_subset_Ioo_right (by norm_num)))
        (hF.mono_set (Ioo_subset_Ioo_left (by norm_num))), integral_Ioc_eq_integral_Ioo]
  rw [hsplit, ← image_fold_left, ← image_fold_right,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd₁ hi₁,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd₂ hi₂]
  simp only [eA, eB]
  rw [← setIntegral_congr_fun measurableSet_Ioo hG, integral_const_mul (2 : ℂ),
    integral_add hA hB]
  ring

theorem bubWt_fold (v : ℝ) :
    bubWt ((1 - v) / 2) + bubWt ((1 + v) / 2) = -(v ^ 2 * (1 - v ^ 2 / 3)) / 4 := by
  unfold bubWt
  ring

theorem fold_mul_one_sub (v : ℝ) :
    (1 - v) / 2 * (1 - (1 - v) / 2) = (1 - v ^ 2) / 4 ∧
      (1 + v) / 2 * (1 - (1 + v) / 2) = (1 - v ^ 2) / 4 := ⟨by ring, by ring⟩

theorem mem_Ioo_fold {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    (1 - v) / 2 ∈ Ioo (0 : ℝ) 1 ∧ (1 + v) / 2 ∈ Ioo (0 : ℝ) 1 :=
  ⟨⟨by linarith [hv.2], by linarith [hv.1]⟩, ⟨by linarith [hv.1], by linarith [hv.2]⟩⟩

/-- **The change of variables `x ↦ v`**: for `H(x) = (x(1-x))⁻¹ g(1/(x(1-x)))` on `(0, 1)` with
`w H` integrable, `ρ(v) g(t_v)` is integrable on `(0, 1)` and
`∫₀¹ w(x) H(x) dx = -(1/2) ∫₀¹ ρ(v) g(t_v) dv`. -/
theorem integral_bubWt_eq {H g : ℝ → ℂ} (hF : IntegrableOn (fun x => (bubWt x : ℂ) * H x) (Ioo 0 1))
    (hH : ∀ x ∈ Ioo (0 : ℝ) 1, H x = ((x * (1 - x) : ℝ) : ℂ)⁻¹ * g (1 / (x * (1 - x)))) :
    IntegrableOn (fun v => (setCKSpecRho v : ℂ) * g (setCKSpecMass v)) (Ioo 0 1) ∧
      ∫ x in Ioo (0 : ℝ) 1, (bubWt x : ℂ) * H x =
        -(1 / 2) * ∫ v in Ioo (0 : ℝ) 1, (setCKSpecRho v : ℂ) * g (setCKSpecMass v) := by
  have hFG : ∀ v ∈ Ioo (0 : ℝ) 1, (bubWt ((1 - v) / 2) : ℂ) * H ((1 - v) / 2) +
      (bubWt ((1 + v) / 2) : ℂ) * H ((1 + v) / 2) =
        -((setCKSpecRho v : ℂ) * g (setCKSpecMass v)) := fun v hv => by
    obtain ⟨h₁, h₂⟩ := mem_Ioo_fold hv
    obtain ⟨e₁, e₂⟩ := fold_mul_one_sub v
    have hv2 : 1 - v ^ 2 ≠ 0 := by nlinarith [hv.1, hv.2]
    have ht : 1 / ((1 - v ^ 2) / 4) = setCKSpecMass v := by
      unfold setCKSpecMass
      field_simp
    rw [hH _ h₁, hH _ h₂, e₁, e₂, ht]
    have hw := bubWt_fold v
    have hρ : (setCKSpecRho v : ℂ) = ((v ^ 2 * (1 - v ^ 2 / 3) / (1 - v ^ 2) : ℝ) : ℂ) := rfl
    have hc : (((1 - v ^ 2) / 4 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast div_ne_zero hv2 four_ne_zero
    have hv2c : ((1 - v ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hv2
    rw [hρ]
    have hsum : (bubWt ((1 - v) / 2) : ℂ) + (bubWt ((1 + v) / 2) : ℂ) =
        ((-(v ^ 2 * (1 - v ^ 2 / 3)) / 4 : ℝ) : ℂ) := by exact_mod_cast hw
    calc (bubWt ((1 - v) / 2) : ℂ) * ((((1 - v ^ 2) / 4 : ℝ) : ℂ)⁻¹ * g (setCKSpecMass v)) +
          (bubWt ((1 + v) / 2) : ℂ) * ((((1 - v ^ 2) / 4 : ℝ) : ℂ)⁻¹ * g (setCKSpecMass v))
        = ((bubWt ((1 - v) / 2) : ℂ) + (bubWt ((1 + v) / 2) : ℂ)) *
            (((1 - v ^ 2) / 4 : ℝ) : ℂ)⁻¹ * g (setCKSpecMass v) := by ring
      _ = _ := by
          rw [hsum]
          push_cast
          field_simp
  obtain ⟨hI, he⟩ := integral_fold hF hFG
  refine ⟨by simpa using hI.neg, ?_⟩
  rw [he, integral_neg]
  ring

/-! ### The transverse dispersive part -/

/-- The transverse `repB` Pauli value with an unscaled dispersion line of mass² `m² T`. -/
noncomputable def kerT (c : Class5) (P : Params) (s : Fin 8) (mγ Λ T : ℝ) : ℂ :=
  unitMPauliZeroPow c P s (fun _ => 1)
    (unitMMasses P.m mγ Λ mγ Λ (repBExtra √(P.m ^ 2 * T) mγ Λ)) 2

theorem specMu_eq_sqrt {m M x : ℝ} (hm : m ≠ 0) :
    specMu M x = √(m ^ 2 * (M ^ 2 / m ^ 2 * (1 / (x * (1 - x))))) := by
  unfold specMu
  congr 1
  field_simp

/-- **One flavour of the transverse dispersive part in the spectral variable**:
`unitMDispPauliRepB(w_f, M) = c_f (-1/2) ∫₀¹ ρ(v) kerT(M² t_v/m²) dv`, the integrand integrable. -/
theorem unitMDispPauliRepB_eq {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {mγ Λ M : ℝ} (hM : μ₀ ≤ M)
    (hmγ : μ₀ ≤ mγ) (hΛ : μ₀ ≤ Λ) (f : Fin 3) :
    IntegrableOn (fun v => (setCKSpecRho v : ℂ) *
        kerT c P s mγ Λ (M ^ 2 / P.m ^ 2 * setCKSpecMass v)) (Ioo 0 1) ∧
      unitMDispPauliRepB c P s (dispWt P f) M mγ Λ = (P.loopCoeff f : ℂ) * (-(1 / 2) *
        ∫ v in Ioo (0 : ℝ) 1, (setCKSpecRho v : ℂ) *
          kerT c P s mγ Λ (M ^ 2 / P.m ^ 2 * setCKSpecMass v)) := by
  have hwc : Continuous fun x => (bubWt x : ℂ) := by unfold bubWt; fun_prop
  have hint := integrableOn_unitMPauliZeroPow_repB_mul hc P hm hs hμ₀
    (w := fun x => (bubWt x : ℂ)) (hwc.integrableOn_Icc.mono_set Ioo_subset_Icc_self) hM hmγ hΛ
  have hH : ∀ x ∈ Ioo (0 : ℝ) 1, unitMPauliZeroPow c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) 2 = ((x * (1 - x) : ℝ) : ℂ)⁻¹ *
      (fun t => kerT c P s mγ Λ (M ^ 2 / P.m ^ 2 * t)) (1 / (x * (1 - x))) := fun x hx => by
    simp only [kerT]
    rw [unitMPauliZeroPow_repB_eq hc P hm hs hμ₀ hmγ hΛ hx hM, specMu_eq_sqrt hm.ne']
  obtain ⟨hI, he⟩ := integral_bubWt_eq (g := fun t => kerT c P s mγ Λ (M ^ 2 / P.m ^ 2 * t))
    hint hH
  refine ⟨hI, ?_⟩
  unfold unitMDispPauliRepB
  simp only [dispWt_eq, mul_assoc]
  rw [integral_const_mul]
  exact congrArg _ he

/-- The kernel of the transverse dispersive part of the main placement `i`:
`-(c w_D/(64 e m⁵)) kerT`. -/
noncomputable def uBDT (P₀ : Params) (i : Fin 12) (mγ Λ T : ℝ) : ℂ :=
  -(vpCst P₀ * wD { P₀ with mγ := mγ, Λ := Λ } 1 / (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5)) *
    kerT (repBClass i) { P₀ with mγ := mγ, Λ := Λ } (repBSlot i) mγ Λ T

/-- **The transverse dispersive part of a main placement is in dispersion form**:
`-Z_D/(64 e m⁵)` with kernel `uBDT i`, `Z_D = -2c w_D ∑_f unitMDispPauliRepB(w_f, M_f)`. -/
theorem isDispPV_dispD {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}
    (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (i : Fin 12) :
    IsDispPV P₀.m M₁ M₂ c₁ c₂ (uBDT P₀ i mγ Λ)
      (-((-2 * vpCst (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) * wD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) 1) *
          ∑ f, unitMDispPauliRepB (repBClass i) (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (repBSlot i)
            (dispWt (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) f)
            ((regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).mass f) mγ Λ) /
        (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5)) := by
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  have hMf := setCAdm_mass hA
  set R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ
  have hμ₀ : 0 < min mγ P₀.m := lt_min hγ hm
  have hf := fun f : Fin 3 => unitMDispPauliRepB_eq (repBClass_mem i) R hm (four_le_repBSlot i)
    hμ₀ ((min_le_right _ _).trans (hMf f)) (min_le_left _ _) ((min_le_left _ _).trans hγΛ) f
  have hK : ∀ T, kerT (repBClass i) R (repBSlot i) mγ Λ T =
      kerT (repBClass i) { P₀ with mγ := mγ, Λ := Λ } (repBSlot i) mγ Λ T := fun T => rfl
  have hK₀ : ∀ v, kerT (repBClass i) R (repBSlot i) mγ Λ (R.mass 0 ^ 2 / P₀.m ^ 2 * v) =
      kerT (repBClass i) R (repBSlot i) mγ Λ v := fun v => by
    have : R.mass 0 = P₀.m := rfl
    rw [this, div_self (pow_ne_zero 2 hm.ne'), one_mul]
  set a : ℂ := -(vpCst P₀ * wD { P₀ with mγ := mγ, Λ := Λ } 1 /
    (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5))
  set X : Fin 3 → ℝ → ℂ := fun f v => (setCKSpecRho v : ℂ) *
    kerT (repBClass i) R (repBSlot i) mγ Λ (R.mass f ^ 2 / P₀.m ^ 2 * setCKSpecMass v) with hX
  have hX0 : IntegrableOn (X 0) (Ioo 0 1) := (hf 0).1
  have hX1 : IntegrableOn (fun v => (c₁ : ℂ) * X 1 v) (Ioo 0 1) := (hf 1).1.const_mul _
  have hX2 : IntegrableOn (fun v => (c₂ : ℂ) * X 2 v) (Ioo 0 1) := (hf 2).1.const_mul _
  have hX01 : IntegrableOn (fun v => X 0 v + (c₁ : ℂ) * X 1 v) (Ioo 0 1) := hX0.add hX1
  have hS : IntegrableOn (fun v => a * (X 0 v + (c₁ : ℂ) * X 1 v + (c₂ : ℂ) * X 2 v))
      (Ioo 0 1) := (hX01.add hX2).const_mul a
  have e : ∀ v, dispPVF P₀.m M₁ M₂ c₁ c₂ (uBDT P₀ i mγ Λ) v =
      a * (X 0 v + (c₁ : ℂ) * X 1 v + (c₂ : ℂ) * X 2 v) := fun v => by
    simp only [hX, dispPVF, uBDT, ← hK, hK₀]
    have h1 : R.mass 1 = M₁ := rfl
    have h2 : R.mass 2 = M₂ := rfl
    rw [h1, h2]
    ring
  refine ⟨hS.congr_fun (fun v _ => (e v).symm) measurableSet_Ioo, ?_⟩
  simp only [e]
  rw [integral_const_mul, integral_add hX01 hX2, integral_add hX0 hX1, integral_const_mul,
    integral_const_mul, Fin.sum_univ_three, (hf 0).2, (hf 1).2, (hf 2).2]
  have hc0 : R.loopCoeff 0 = 1 := rfl
  have hc1 : R.loopCoeff 1 = c₁ := rfl
  have hc2 : R.loopCoeff 2 = c₂ := rfl
  have hv : vpCst R = vpCst P₀ := rfl
  have hw : wD R 1 = wD { P₀ with mγ := mγ, Λ := Λ } 1 := rfl
  rw [hc0, hc1, hc2, hv, hw]
  simp only [a]
  push_cast
  ring

end QED.ChainProof.SetCRegDisp

end
