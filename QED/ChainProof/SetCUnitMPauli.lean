/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMCov
public import QED.ChainProof.SetCUnitPauli

/-!
# Multi-denominator two-loop vertex units: the `q² → 0⁺` Pauli value

Helper level for set (c) (stage L2). The curve engine
`QED.TwoLoop.PauliZeroExplicit.tendsto_piece_explicit` is generic in the lines, so it runs on the
multi-denominator unit (`r + 8` lines) exactly as on the two-mass unit
(`QED/ChainProof/SetCUnitPauli.lean`). Along the curve `p'(u)`, `p = (m, 0, 0, 0)`:

* `unitMCurve`: the parametric data of the unit along the curve;
* `unitMPauliZero = ∫_{Δ_{r+7}} c₂[N(x, ·)] / V(x)^{r+4} dx`, the second Taylor coefficient of the
  Pauli-projected parametric numerator over the power of `V` at `q = 0`;
* **`tendsto_unitM_explicit`**: `(S(u) + S(-u))/(2u²) → unitMPauliZero` at `n = 0`;
* `unitMPauliS_neg`: `S` is even for every power `n` (reflection covariance, `unitMLimitV_map`);
* **`tendsto_unitMPauliS_div`**: `S(u)/u² → unitMPauliZero` at `n = 0`;
* **`tendsto_unitMPauliS_div_pow`**: for every `n` with the last `n` extra lines unscaled,
  `S_n(u)/u²` converges, to `unitMPauliZeroPow` (`unitMPauliZeroPow_zero`: at `n = 0` it is
  `unitMPauliZero`; `unitMPauliZeroPow_succ`: the recursion `Z_{n+1} = Z_n(init) - μ² Z_n`);
* **`tendsto_formFactorProj₂_unitM`**: the Pauli projection of the limit `L_n` at the canonical
  pair with `q² = Q` tends, as `Q → 0⁺`, to `unitMPauliZeroPow / (64 e m⁵)`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set MeasureTheory
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.Dirac QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.ChainProof.SetCUnit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix class5LoopMatrixPV
  symanzikV symanzikU pvLines)

variable {r : ℕ}

/-- The parametric data of the multi-denominator unit along the curve. -/
noncomputable def unitMCurve {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {κ cs : Fin r → ℝ} (hX : ExtraGe μ₀ κ cs) : CurveData where
  m := r + 7
  α := unitMMatrix c s κ
  mom u := unitMMomenta c s κ (restMomentum P.m) (curveMomentum P.m u)
  M := unitMMasses P.m a A b B cs
  E := unitME r
  hm := by omega
  hcrit := noSubdivergenceRefined_unitM hc s hX.ne_zero
  c := unitConst P.m μ₀
  hc := unitConst_pos hm hμ₀
  hV := fun u hu _ hz hz1 hU => symanzikV_unitM_ge hc hs hμ₀ hM hX
    (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
    ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) hz hz1 hU
  hmom := fun i μ => by
    have h := isUPoly_ext_curve (ι := Fin (r + 7) → ℝ) P.m
      (fun p' => extMomenta c (restMomentum P.m) p' (pvLines (mLine s i))) (by
        rcases extMomenta_cases c (restMomentum P.m) (pvLines (mLine s i)) with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)) μ
    refine (h.const_mul fun _ => ((mScale κ i : ℝ) : ℂ)).congr fun _ u _ => ?_
    simp only [unitMMomenta, pvMomentaE, Pi.smul_apply, smul_eq_mul, ofReal_mul]
    ring
  hVeven := fun u z => by
    have h := QED.TwoLoop.ReflCovariance.isSpinLift_reflect (K := axisOne)
      (by rw [dot_axisOne]; exact one_ne_zero)
    have e := QED.TwoLoop.ReflCovariance.symanzikV_map h (unitMMatrix c s κ)
      (unitMMomenta c s κ (restMomentum P.m) (curveMomentum P.m u))
      (unitMMasses P.m a A b B cs) z
    rw [← unitMMomenta_map, reflectMatrix_restMomentum, reflectMatrix_curveMomentum] at e
    exact e

/-- The Pauli-projected parametric numerator of the multi-denominator unit along the curve. -/
noncomputable def unitMPauliNum (c : Class5) (P : Params) (s : Fin 8) (κ : Fin r → ℝ)
    (M : Fin (r + 8) → ℝ) (x : Fin (r + 7) → ℝ) (u : ℝ) : ℂ :=
  ∑ j : Idx, pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
    (-((π : ℂ) ^ 4) * paramNumOf (openF c P (curveMomentum P.m u) j) (unitMMatrix c s κ)
      (unitMMomenta c s κ (restMomentum P.m) (curveMomentum P.m u)) M x)

/-- The second Symanzik function of the multi-denominator unit at `q = 0`. -/
noncomputable def unitMV0 (c : Class5) (P : Params) (s : Fin 8) (κ : Fin r → ℝ)
    (M : Fin (r + 8) → ℝ) (x : Fin (r + 7) → ℝ) : ℝ :=
  symanzikV (unitMMatrix c s κ) (unitMMomenta c s κ (restMomentum P.m) (restMomentum P.m)) M
    (simplexPoint x)

/-- **The `q → 0` value of the multi-denominator unit** at `n = 0`:
`∫_{Δ_{r+7}} c₂[N(x, ·)] / V(x)^{r+4} dx`. -/
noncomputable def unitMPauliZero (c : Class5) (P : Params) (s : Fin 8) (κ : Fin r → ℝ)
    (M : Fin (r + 8) → ℝ) : ℂ :=
  ∫ x in simplexSet (r + 7), secondCoeff (unitMPauliNum c P s κ M x) /
    ((unitMV0 c P s κ M x : ℝ) : ℂ) ^ (r + 4)

/-- The Pauli numerator of the limit `L_n` along the curve. -/
noncomputable def unitMPauliS (c : Class5) (P : Params) (s : Fin 8) (κ : Fin r → ℝ)
    (M : Fin (r + 8) → ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
    (unitMLimitV c P s κ M (restMomentum P.m) (curveMomentum P.m u) n)

/-- **The `q → 0` value of the multi-denominator unit with the power `(k²)ⁿ`**: the limit of
`S_n(u)/u²` (it exists, `tendsto_unitMPauliS_div_pow`). -/
noncomputable def unitMPauliZeroPow (c : Class5) (P : Params) (s : Fin 8) (κ : Fin r → ℝ)
    (M : Fin (r + 8) → ℝ) (n : ℕ) : ℂ :=
  limUnder (𝓝[≠] (0 : ℝ)) fun u => unitMPauliS c P s κ M n u / (u : ℂ) ^ 2

theorem pauliNum_sub_smul (m : ℝ) (p' p : Fin 4 → ℝ) (V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (a : ℂ) :
    pauliNum m p' p (fun μ => V μ - a • W μ) = pauliNum m p' p V - a * pauliNum m p' p W := by
  simp only [pauliNum_eq_sum_idx, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

section Pauli

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
include hc hm hs hμ₀ hM

/-- **The explicit second-order limit of the multi-denominator unit** (`n = 0`). -/
theorem tendsto_unitM_explicit {κ cs : Fin r → ℝ} (hX : ExtraGe μ₀ κ cs) :
    Tendsto (fun u : ℝ =>
      (unitMPauliS c P s κ (unitMMasses P.m a A b B cs) 0 u +
        unitMPauliS c P s κ (unitMMasses P.m a A b B cs) 0 (-u)) / (2 * (u : ℂ) ^ 2)) (𝓝[≠] 0)
      (𝓝 (unitMPauliZero c P s κ (unitMMasses P.m a A b B cs))) := by
  have hF : ∀ (p' : Fin 4 → ℝ) (j : Idx),
      (fun ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m) p' j.1 ℓ) j.2.1 j.2.2) =
        fun ℓ => twoLoopNorm * classNumeratorE c P (fun _ => p') (fun _ => restMomentum P.m)
          (fun _ => p' - restMomentum P.m) (fun _ => j.2.1) (fun _ => j.2.2) (fun _ => j.1) ℓ :=
    fun p' j => funext fun ℓ => by simp only [Matrix.smul_apply, classNumM, Matrix.of_apply,
      smul_eq_mul]
  have hB : ∀ (p' : Fin 4 → ℝ) (j : Idx), RefinedBound (unitMMatrix c s κ) (unitME r) 4
      (fun ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m) p' j.1 ℓ) j.2.1 j.2.2) :=
    fun p' j => by
      rw [hF]
      exact refinedBound_unitM hc P s κ _ _ _ _ _
  have hL := tendsto_piece_explicit (unitMCurve hc P hm hs hμ₀ hM hX) (J := Idx) (D := 8)
    (n := 4) (r := 4) (Dω := 8)
    (fun u j ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m) (curveMomentum P.m u) j.1 ℓ)
      j.2.1 j.2.2)
    (fun j => by
      have h := isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
        (G := fun ℓ y => twoLoopNorm * classNumeratorE c P (fun _ => y 0)
          (fun _ => restMomentum P.m) (fun _ => y 0 - restMomentum P.m) (fun _ => j.2.1)
          (fun _ => j.2.2) (fun _ => j.1) ℓ)
        (fun ℓ => (isLoopPoly_classNumeratorE_out hc P _ _ _ _ ℓ).const_mul _)
        (ℓ := fun _ u => fun _ => curveMomentum P.m u) fun _ ν => isUPoly_curveMomentum P.m ν
      refine h.congr fun ℓ u _ => ?_
      simp only [Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul])
    (fun u _ j => by
      rw [hF]
      exact ((isLoopPoly_classNumeratorE hc P _ _ _ _ _ _).const_mul _).exists_loopQuartic)
    (fun u _ j => hB _ j)
    (fun u j => unitMLimitV c P s κ (unitMMasses P.m a A b B cs) (restMomentum P.m)
      (curveMomentum P.m u) 0 j.1 j.2.1 j.2.2)
    (fun u hu j => by
      obtain ⟨Q, hQ, -, hv⟩ := exists_quartic_unitMLimitV hc P hm hs hμ₀ hM
        (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
        ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) hX j.1 j.2.1 j.2.2
      exact ⟨Q, hQ, hB _ j, hv⟩)
    (fun u j => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2)
    (fun j => isUPoly_pauliWt P.m j) (sum_pauliWt_zero P.m)
  have hval : (∫ x in simplexSet (unitMCurve hc P hm hs hμ₀ hM hX).m,
      secondCoeff (projNum (unitMCurve hc P hm hs hμ₀ hM hX)
        (fun u (j : Idx) ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m)
          (curveMomentum P.m u) j.1 ℓ) j.2.1 j.2.2)
        (fun u (j : Idx) => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2)
        x) /
        (((unitMCurve hc P hm hs hμ₀ hM hX).vfun x 0 : ℝ) : ℂ) ^
          ((unitMCurve hc P hm hs hμ₀ hM hX).m - 3)) =
      unitMPauliZero c P s κ (unitMMasses P.m a A b B cs) := by
    simp only [unitMPauliZero, unitMV0, CurveData.vfun, unitMCurve, curveMomentum_zero]
    rfl
  rw [hval] at hL
  exact hL.congr fun u => by simp only [unitMPauliS, pauliNum_eq_sum_idx]

/-- **The Pauli numerator of `L_n` along the curve is even in `u`**, every power `n` with the last
`n ≤ r` extra lines unscaled. -/
theorem unitMPauliS_neg {n : ℕ} {κ cs : Fin r → ℝ} (hnr : n ≤ r) (hT : TrailOne n κ)
    (hX : ExtraGe μ₀ κ cs) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    unitMPauliS c P s κ (unitMMasses P.m a A b B cs) n (-u) =
      unitMPauliS c P s κ (unitMMasses P.m a A b B cs) n u := by
  have h := QED.TwoLoop.ReflCovariance.isSpinLift_reflect (K := axisOne)
    (by rw [dot_axisOne]; exact one_ne_zero)
  have hW := unitMLimitV_map hc P hm hs hμ₀ hM (dot_restMomentum (m := P.m))
    (dot_curveMomentum P.m hu) ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) h n
    hnr hT hX
  have e := pauliNum_map h P.m (curveMomentum P.m u) (restMomentum P.m) hW
  rw [reflectMatrix_curveMomentum, reflectMatrix_restMomentum] at e
  exact e

/-- `S(u)/u² → unitMPauliZero` as `u → 0`, `u ≠ 0` (`n = 0`). -/
theorem tendsto_unitMPauliS_div {κ cs : Fin r → ℝ} (hX : ExtraGe μ₀ κ cs) :
    Tendsto (fun u => unitMPauliS c P s κ (unitMMasses P.m a A b B cs) 0 u / (u : ℂ) ^ 2)
      (𝓝[≠] 0) (𝓝 (unitMPauliZero c P s κ (unitMMasses P.m a A b B cs))) := by
  refine (tendsto_unitM_explicit hc P hm hs hμ₀ hM hX).congr' ?_
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [h0] with u hu
  rw [unitMPauliS_neg hc P hm hs hμ₀ hM (le_refl 0 |>.trans (Nat.zero_le r))
    (fun j hj => by omega) hX hu]
  by_cases hu0 : (u : ℂ) = 0
  · simp [hu0]
  · field_simp
    ring

/-- **The `q → 0` limit with powers of `k²`**: for every `n` with the last `n ≤ r` extra lines
unscaled, `S_n(u)/u²` converges as `u → 0`, `u ≠ 0`, to `unitMPauliZeroPow`. -/
theorem tendsto_unitMPauliS_div_pow (n : ℕ) :
    ∀ {r : ℕ} {κ cs : Fin r → ℝ}, n ≤ r → TrailOne n κ → ExtraGe μ₀ κ cs →
      Tendsto (fun u => unitMPauliS c P s κ (unitMMasses P.m a A b B cs) n u / (u : ℂ) ^ 2)
        (𝓝[≠] 0) (𝓝 (unitMPauliZeroPow c P s κ (unitMMasses P.m a A b B cs) n)) := by
  suffices h : ∀ {r : ℕ} {κ cs : Fin r → ℝ}, n ≤ r → TrailOne n κ → ExtraGe μ₀ κ cs →
      ∃ Z, Tendsto (fun u => unitMPauliS c P s κ (unitMMasses P.m a A b B cs) n u / (u : ℂ) ^ 2)
        (𝓝[≠] 0) (𝓝 Z) by
    intro r κ cs hnr hT hX
    obtain ⟨Z, hZ⟩ := h hnr hT hX
    unfold unitMPauliZeroPow
    rw [hZ.limUnder_eq]
    exact hZ
  induction n with
  | zero =>
    intro r κ cs _ _ hX
    exact ⟨_, tendsto_unitMPauliS_div hc P hm hs hμ₀ hM hX⟩
  | succ n ih =>
    intro r κ cs hnr hT hX
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨Z₁, h₁⟩ := ih (by omega) hT.init hX.init
    obtain ⟨Z₂, h₂⟩ := ih (by omega) hT.of_succ hX
    refine ⟨Z₁ - ((cs (Fin.last r) ^ 2 : ℝ) : ℂ) * Z₂, (h₁.sub (h₂.const_mul _)).congr' ?_⟩
    have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
      nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
    filter_upwards [h0] with u hu
    have hq := (dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu
    have e : unitMPauliS c P s κ (unitMMasses P.m a A b B cs) (n + 1) u =
        unitMPauliS c P s (Fin.init κ) (unitMMasses P.m a A b B (Fin.init cs)) n u -
          ((cs (Fin.last r) ^ 2 : ℝ) : ℂ) * unitMPauliS c P s κ (unitMMasses P.m a A b B cs) n u
        := by
      unfold unitMPauliS
      rw [← pauliNum_sub_smul]
      congr 1
      funext ν
      exact unitMLimitV_succ_mat hc P hm hs hμ₀ hM (dot_restMomentum (m := P.m))
        (dot_curveMomentum P.m hu) hq hnr hT hX ν
    rw [e, sub_div, mul_div_assoc]

theorem unitMPauliZeroPow_zero {κ cs : Fin r → ℝ} (hX : ExtraGe μ₀ κ cs) :
    unitMPauliZeroPow c P s κ (unitMMasses P.m a A b B cs) 0 =
      unitMPauliZero c P s κ (unitMMasses P.m a A b B cs) :=
  (tendsto_unitMPauliS_div hc P hm hs hμ₀ hM hX).limUnder_eq

/-- **The recursion of the `q → 0` values**: `Z_{n+1} = Z_n(init) - μ² Z_n`. -/
theorem unitMPauliZeroPow_succ {n : ℕ} {κ cs : Fin (r + 1) → ℝ} (hnr : n + 1 ≤ r + 1)
    (hT : TrailOne (n + 1) κ) (hX : ExtraGe μ₀ κ cs) :
    unitMPauliZeroPow c P s κ (unitMMasses P.m a A b B cs) (n + 1) =
      unitMPauliZeroPow c P s (Fin.init κ) (unitMMasses P.m a A b B (Fin.init cs)) n -
        ((cs (Fin.last r) ^ 2 : ℝ) : ℂ) *
          unitMPauliZeroPow c P s κ (unitMMasses P.m a A b B cs) n := by
  have hS := tendsto_unitMPauliS_div_pow hc P hm hs hμ₀ hM (n + 1) hnr hT hX
  have h₁ := tendsto_unitMPauliS_div_pow hc P hm hs hμ₀ hM n (by omega) hT.init hX.init
  have h₂ := tendsto_unitMPauliS_div_pow hc P hm hs hμ₀ hM n (by omega) hT.of_succ hX
  refine tendsto_nhds_unique hS ((h₁.sub (h₂.const_mul _)).congr' ?_)
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [h0] with u hu
  have hq := (dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu
  unfold unitMPauliS
  rw [mul_div_assoc', ← sub_div, ← pauliNum_sub_smul]
  congr 2
  funext ν
  exact (unitMLimitV_succ_mat hc P hm hs hμ₀ hM (dot_restMomentum (m := P.m))
    (dot_curveMomentum P.m hu) hq hnr hT hX ν).symm

/-- **The `q² → 0⁺` Pauli value of the multi-denominator unit**: at the canonical pair with
`q² = Q`, the Pauli projection of `L_n` tends to `unitMPauliZeroPow / (64 e m⁵)` as `Q → 0⁺`. -/
theorem tendsto_formFactorProj₂_unitM {n : ℕ} {κ cs : Fin r → ℝ} (hnr : n ≤ r)
    (hT : TrailOne n κ) (hX : ExtraGe μ₀ κ cs) (e : ℝ) :
    Tendsto (fun Q => QED.OneLoop.formFactorProj₂ e P.m (boostMomentum P.m Q) (restMomentum P.m)
        (unitMLimitV c P s κ (unitMMasses P.m a A b B cs) (restMomentum P.m)
          (boostMomentum P.m Q) n))
      (𝓝[>] 0) (𝓝 (unitMPauliZeroPow c P s κ (unitMMasses P.m a A b B cs) n /
        (64 * (e : ℂ) * (P.m : ℂ) ^ 5))) :=
  tendsto_formFactorProj₂_of hm e
    (fun p' => unitMLimitV c P s κ (unitMMasses P.m a A b B cs) (restMomentum P.m) p' n)
    (tendsto_unitMPauliS_div_pow hc P hm hs hμ₀ hM n hnr hT hX)

end Pauli

end QED.ChainProof.SetCUnitM

end
