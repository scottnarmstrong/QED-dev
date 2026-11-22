/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMDispBd

/-!
# Multi-denominator units: the `q → 0` Pauli value of `repB` as a dispersion integral

Helper level for set (c) (stage L2). The `q → 0` value of the transverse unit of `repB` at the
Feynman parameter `x` is `(x(1-x))⁻¹` times that of the unscaled unit with the dispersion line of
mass `μ_x` (`QED.ChainProof.SetCUnitM.unitMPauliZeroPow_repB_eq`). The partial fraction of
`QED/ChainProof/SetCUnitMDisp.lean` holds for the Pauli values, and the heavy-line bound of
`QED/ChainProof/SetCUnitMDispBd.lean` bounds the second term uniformly in `μ_x`, so the value
decays like `μ_x⁻²` and the dispersion integral converges.

* `unitMPauliS_perm`, `unitMPauliZeroPow_perm`, `sum_sq_unitMMasses_perm`: the order of the
  extra lines does not matter;
* **`unitMPauliS_pf`**, **`unitMPauliZeroPow_pf`**: the partial fraction against the element
  line, along the curve and for the `q → 0` values;
* **`norm_unitMPauliZeroPow_repB_disp_le`**: `‖Z(x)‖ ≤ C (1 + ∑ᵢ Mᵢ²)⁵ / M²` uniformly in
  `x ∈ (0, 1)`, `Mᵢ` the masses of the ten lines other than the dispersion line;
* `continuousOn_unitMPauliS_repB`, `aestronglyMeasurable_unitMPauliZeroPow_repB`: measurability
  in `x` (a pointwise limit of continuous functions);
* `unitMDispPauliRepB`, **`integrableOn_unitMPauliZeroPow_repB_mul`**,
  **`norm_unitMDispPauliRepB_le`**: the dispersion integral `∫₀¹ w(x) Z(x) dx` and its bound.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.Dirac QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable QED.TwoLoop.ClassLimit QED.ChainProof.SetCUnit
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.VPHalfAtAssembly (specMu mem_Ioo_mul_pos)

/-! ### Permuting the extra lines -/

section Perm

variable {r : ℕ}

theorem unitMPauliS_perm (c : Class5) (P : Params) (s : Fin 8) (σ : Equiv.Perm (Fin r))
    (κ : Fin r → ℝ) (m a A b B : ℝ) (cs : Fin r → ℝ) (n : ℕ) (u : ℝ) :
    unitMPauliS c P s (κ ∘ σ) (unitMMasses m a A b B (cs ∘ σ)) n u =
      unitMPauliS c P s κ (unitMMasses m a A b B cs) n u := by
  unfold unitMPauliS
  rw [unitMLimitV_perm]

theorem unitMPauliZeroPow_perm (c : Class5) (P : Params) (s : Fin 8) (σ : Equiv.Perm (Fin r))
    (κ : Fin r → ℝ) (m a A b B : ℝ) (cs : Fin r → ℝ) (n : ℕ) :
    unitMPauliZeroPow c P s (κ ∘ σ) (unitMMasses m a A b B (cs ∘ σ)) n =
      unitMPauliZeroPow c P s κ (unitMMasses m a A b B cs) n := by
  unfold unitMPauliZeroPow
  simp only [unitMPauliS_perm]

theorem sum_sq_unitMMasses_perm (σ : Equiv.Perm (Fin r)) (m a A b B : ℝ) (cs : Fin r → ℝ) :
    ∑ i, unitMMasses m a A b B (cs ∘ σ) i ^ 2 = ∑ i, unitMMasses m a A b B cs i ^ 2 :=
  Fintype.sum_equiv (extPerm σ) _ _ fun i => by
    simp only [unitMMasses]
    rw [mExt_comp_perm]

end Perm

/-! ### Partial fractions for the Pauli values -/

section PF

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
include hc hm hs hμ₀ hM

/-- **Partial fractions along the curve**:
`S(cs)(u) = (t² - μ_s²)⁻¹ (S(init cs)(u) - S'(init cs)(u))`, `S'` with the mass of line `s`
replaced by the last extra mass `t`. -/
theorem unitMPauliS_pf {r n : ℕ} {κ cs : Fin (r + 1) → ℝ} (hnr : n ≤ r)
    (hT : TrailOne n (Fin.init κ)) (hκ : κ (Fin.last r) = 1) (hX : ExtraGe μ₀ κ cs)
    (ht : cs (Fin.last r) ^ 2 ≠ unitMasses P.m a A b B s ^ 2) {u : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) :
    unitMPauliS c P s κ (unitMMasses P.m a A b B cs) n u =
      ((cs (Fin.last r) ^ 2 - unitMasses P.m a A b B s ^ 2 : ℝ) : ℂ)⁻¹ *
        (unitMPauliS c P s (Fin.init κ) (unitMMasses P.m a A b B (Fin.init cs)) n u -
          unitMPauliS c P s (Fin.init κ)
            (unitMMasses P.m (slotMa s (cs (Fin.last r)) a) (slotMA s (cs (Fin.last r)) A)
              (slotMb s (cs (Fin.last r)) b) (slotMB s (cs (Fin.last r)) B) (Fin.init cs))
            n u) := by
  have hq := (dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu
  unfold unitMPauliS
  simp only [pauliNum_eq_sum_idx, unitMLimitV_pf hc P hm hs hμ₀ hM (dot_restMomentum (m := P.m))
    (dot_curveMomentum P.m hu) hq hnr hT hκ hX ht]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Partial fractions for the `q → 0` values**:
`Z(cs) = (t² - μ_s²)⁻¹ (Z(init cs) - Z'(init cs))`. -/
theorem unitMPauliZeroPow_pf {r n : ℕ} {κ cs : Fin (r + 1) → ℝ} (hnr : n ≤ r)
    (hT : TrailOne n (Fin.init κ)) (hκ : κ (Fin.last r) = 1) (hX : ExtraGe μ₀ κ cs)
    (ht : cs (Fin.last r) ^ 2 ≠ unitMasses P.m a A b B s ^ 2) :
    unitMPauliZeroPow c P s κ (unitMMasses P.m a A b B cs) n =
      ((cs (Fin.last r) ^ 2 - unitMasses P.m a A b B s ^ 2 : ℝ) : ℂ)⁻¹ *
        (unitMPauliZeroPow c P s (Fin.init κ) (unitMMasses P.m a A b B (Fin.init cs)) n -
          unitMPauliZeroPow c P s (Fin.init κ)
            (unitMMasses P.m (slotMa s (cs (Fin.last r)) a) (slotMA s (cs (Fin.last r)) A)
              (slotMb s (cs (Fin.last r)) b) (slotMB s (cs (Fin.last r)) B) (Fin.init cs))
            n) := by
  have hM' := massesGe_slot (s := s) hM (hX (Fin.last r)).2.2
  have h₁ := tendsto_unitMPauliS_div_pow hc P hm hs hμ₀ hM n hnr hT hX.init
  have h₂ := tendsto_unitMPauliS_div_pow hc P hm hs hμ₀ hM' n hnr hT hX.init
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  set k : ℂ := (((cs (Fin.last r) ^ 2 - unitMasses P.m a A b B s ^ 2 : ℝ) : ℂ))⁻¹
  have hlim : Tendsto (fun u => unitMPauliS c P s κ (unitMMasses P.m a A b B cs) n u /
      (u : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (k * (unitMPauliZeroPow c P s (Fin.init κ)
        (unitMMasses P.m a A b B (Fin.init cs)) n - unitMPauliZeroPow c P s (Fin.init κ)
          (unitMMasses P.m (slotMa s (cs (Fin.last r)) a) (slotMA s (cs (Fin.last r)) A)
            (slotMb s (cs (Fin.last r)) b) (slotMB s (cs (Fin.last r)) B) (Fin.init cs)) n))) := by
    refine ((h₁.sub h₂).const_mul k).congr' ?_
    filter_upwards [h0] with u hu
    rw [unitMPauliS_pf hc P hm hs hμ₀ hM hnr hT hκ hX ht hu]
    ring
  exact hlim.limUnder_eq

end PF

/-! ### The Pauli value of `repB` -/

theorem unitMPauliZeroPow_repBExtra_rot (c : Class5) (P : Params) (s : Fin 8)
    (m a A b B t mγ Λ : ℝ) (n : ℕ) :
    unitMPauliZeroPow c P s (fun _ : Fin 3 => (1 : ℝ)) (unitMMasses m a A b B (repBExtra t mγ Λ))
        n =
      unitMPauliZeroPow c P s (fun _ : Fin 3 => (1 : ℝ)) (unitMMasses m a A b B ![mγ, Λ, t]) n := by
  rw [← repBExtra_rot]
  exact unitMPauliZeroPow_perm c P s (finRotate 3).symm (fun _ => 1) m a A b B ![mγ, Λ, t] n

theorem sum_sq_unitMMasses_repBExtra (m a A b B t mγ Λ : ℝ) :
    ∑ i, unitMMasses m a A b B (repBExtra t mγ Λ) i ^ 2 =
      ∑ i, unitMMasses m a A b B (![mγ, Λ] : Fin 2 → ℝ) i ^ 2 + t ^ 2 := by
  rw [← repBExtra_rot, sum_sq_unitMMasses_perm, sum_sq_unitMMasses_succ]
  rfl

/-- **The decay of the `repB` Pauli value in the dispersion mass**: one constant `C` with
`‖Z(x)‖ ≤ C (1 + ∑ᵢ Mᵢ²)⁵ / M²` for all `x ∈ (0, 1)` and all masses `≥ μ₀`, `Mᵢ` the masses of
the ten lines of the unit without the dispersion line. -/
theorem norm_unitMPauliZeroPow_repB_disp_le {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    ∃ C : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1, ∀ M mγ Λ : ℝ, μ₀ ≤ M → μ₀ ≤ mγ → μ₀ ≤ Λ →
      ‖unitMPauliZeroPow c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) 2‖ ≤
        C * (1 + ∑ i, unitMMasses P.m mγ Λ mγ Λ (![mγ, Λ] : Fin 2 → ℝ) i ^ 2) ^ 5 / M ^ 2 := by
  obtain ⟨C₁, hC₁⟩ := norm_unitMPauliZeroPow_le hc P hm hs hμ₀ 2 (r := 2) (κ := fun _ => 1)
    le_rfl (fun _ _ => rfl) fun _ => ⟨one_pos, le_rfl⟩
  obtain ⟨C₂, hC₂⟩ := norm_unitMPauliZeroPow_slot_le hc P hm hs hμ₀ 2 (r := 2)
    (κ := fun _ => 1) le_rfl (fun _ _ => rfl) fun _ => ⟨one_pos, le_rfl⟩
  obtain ⟨C₃, hC₃⟩ := norm_unitMPauliZeroPow_repB_le hc P hm hs hμ₀
  refine ⟨2 * (|C₁| + |C₂|) + 162 * |C₃|, fun x hx M mγ Λ hM hmγ hΛ => ?_⟩
  have hw := mem_Ioo_mul_pos hx
  have hM0 : 0 < M := hμ₀.trans_le hM
  have hM2 : 0 < M ^ 2 := by positivity
  set w := x * (1 - x) with hwdef
  set μ' := specMu M x with hμdef
  have hμ2 : μ' ^ 2 = M ^ 2 / w := Real.sq_sqrt (div_nonneg (sq_nonneg M) hw.le)
  have hwμ : w * μ' ^ 2 = M ^ 2 := by rw [hμ2]; field_simp
  have hμ'0 : μ₀ ≤ μ' := hM.trans (QED.TwoLoop.VPHalfAtAssembly.specMu_ge hM0 hx)
  have hMg := massesGe_repB hmγ hΛ
  set S₀ := ∑ i, unitMMasses P.m mγ Λ mγ Λ (![mγ, Λ] : Fin 2 → ℝ) i ^ 2 with hS₀
  have hS₀0 : 0 ≤ S₀ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set μs := unitMasses P.m mγ Λ mγ Λ s with hμs
  have hμs0 : μ₀ ≤ μs := le_unitMasses hs hMg
  have hμsS : μs ^ 2 ≤ S₀ := by
    have h := Finset.single_le_sum (f := fun i => unitMMasses P.m mγ Λ mγ Λ
      (![mγ, Λ] : Fin 2 → ℝ) i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ (mEmb 2 s))
    simpa only [unitMMasses_mEmb] using h
  have hT1 : 1 ≤ 1 + S₀ := by linarith
  have hfin4 : (1 + S₀) ^ 4 ≤ (1 + S₀) ^ 5 := pow_le_pow_right₀ hT1 (by norm_num)
  rw [unitMPauliZeroPow_repB_eq hc P hm hs hμ₀ hmγ hΛ hx hM, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hw.le]
  by_cases hcase : 2 * μs ^ 2 ≤ μ' ^ 2
  · -- partial fractions
    have hμs2p : 0 < μs ^ 2 := pow_pos (hμ₀.trans_le hμs0) 2
    have hne : (![mγ, Λ, μ'] : Fin 3 → ℝ) (Fin.last 2) ^ 2 ≠ μs ^ 2 := by
      change μ' ^ 2 ≠ μs ^ 2
      intro h; linarith
    have hX : ExtraGe μ₀ (fun _ : Fin 3 => (1 : ℝ)) ![mγ, Λ, μ'] := fun j =>
      ⟨one_pos, le_rfl, by fin_cases j <;> assumption⟩
    have hle : μs ≤ μ' := by
      have h0 : 0 ≤ μs := hμ₀.le.trans hμs0
      nlinarith
    have hinit : Fin.init (![mγ, Λ, μ'] : Fin 3 → ℝ) = ![mγ, Λ] := by
      funext j; fin_cases j <;> rfl
    rw [unitMPauliZeroPow_repBExtra_rot, unitMPauliZeroPow_pf hc P hm hs hμ₀ hMg le_rfl
      (fun _ _ => rfl) rfl hX hne, hinit]
    change w⁻¹ * ‖(((μ' ^ 2 - μs ^ 2 : ℝ) : ℂ))⁻¹ * (unitMPauliZeroPow c P s (fun _ => 1)
      (unitMMasses P.m mγ Λ mγ Λ ![mγ, Λ]) 2 - unitMPauliZeroPow c P s (fun _ => 1)
        (unitMMasses P.m (slotMa s μ' mγ) (slotMA s μ' Λ) (slotMb s μ' mγ) (slotMB s μ' Λ)
          ![mγ, Λ]) 2)‖ ≤ _
    have h1 := hC₁ mγ Λ mγ Λ ![mγ, Λ] hMg fun j => by fin_cases j <;> assumption
    have h2 := hC₂ mγ Λ mγ Λ μ' ![mγ, Λ] hMg (fun j => by fin_cases j <;> assumption) hle
    have hd : 0 < μ' ^ 2 - μs ^ 2 := by linarith
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hd.le]
    have hsub := (norm_sub_le _ _).trans (add_le_add h1 h2)
    have hC : C₁ * (1 + S₀) ^ (2 + 2) + C₂ * (1 + S₀) ^ (2 + 2) ≤
        (|C₁| + |C₂|) * (1 + S₀) ^ 5 := by
      have hX0 : 0 ≤ (1 + S₀) ^ (2 + 2) := by positivity
      calc C₁ * (1 + S₀) ^ (2 + 2) + C₂ * (1 + S₀) ^ (2 + 2)
          ≤ |C₁| * (1 + S₀) ^ (2 + 2) + |C₂| * (1 + S₀) ^ (2 + 2) :=
            add_le_add (mul_le_mul_of_nonneg_right (le_abs_self _) hX0)
              (mul_le_mul_of_nonneg_right (le_abs_self _) hX0)
        _ = (|C₁| + |C₂|) * (1 + S₀) ^ 4 := by ring
        _ ≤ (|C₁| + |C₂|) * (1 + S₀) ^ 5 := mul_le_mul_of_nonneg_left hfin4 (by positivity)
    have hinv : (μ' ^ 2 - μs ^ 2)⁻¹ ≤ 2 / μ' ^ 2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ hd (by linarith)]
      linarith
    have hK0 : 0 ≤ (|C₁| + |C₂|) * (1 + S₀) ^ 5 := by positivity
    calc w⁻¹ * ((μ' ^ 2 - μs ^ 2)⁻¹ * ‖_‖)
        ≤ w⁻¹ * (2 / μ' ^ 2 * ((|C₁| + |C₂|) * (1 + S₀) ^ 5)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hinv (hsub.trans hC) (norm_nonneg _)
            (by positivity)) (by positivity)
      _ = 2 * (|C₁| + |C₂|) * (1 + S₀) ^ 5 / M ^ 2 := by
          rw [← hwμ]; field_simp
      _ ≤ (2 * (|C₁| + |C₂|) + 162 * |C₃|) * (1 + S₀) ^ 5 / M ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
            (by linarith [abs_nonneg C₃]) (by positivity)) hM2.le
  · -- the dispersion mass is light
    push Not at hcase
    have h3 := hC₃ μ' mγ Λ hμ'0 hmγ hΛ
    rw [sum_sq_unitMMasses_repBExtra, ← hS₀] at h3
    have hμ2ne : μ' ^ 2 ≠ 0 := fun h => by rw [h, mul_zero] at hwμ; linarith
    have hwinv : w⁻¹ ≤ 2 * (1 + S₀) / M ^ 2 := by
      have e : w⁻¹ = μ' ^ 2 / M ^ 2 := by
        rw [← hwμ, mul_comm, ← div_div, div_self hμ2ne, one_div]
      rw [e]
      exact div_le_div_of_nonneg_right (by linarith) hM2.le
    have hB : C₃ * (1 + (S₀ + μ' ^ 2)) ^ (2 + 2) ≤ |C₃| * (3 * (1 + S₀)) ^ 4 := by
      refine (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
      exact pow_le_pow_left₀ (by positivity) (by nlinarith) 4
    calc w⁻¹ * ‖_‖ ≤ w⁻¹ * (|C₃| * (3 * (1 + S₀)) ^ 4) :=
          mul_le_mul_of_nonneg_left (h3.trans hB) (by positivity)
      _ ≤ (2 * (1 + S₀) / M ^ 2) * (|C₃| * (3 * (1 + S₀)) ^ 4) :=
          mul_le_mul_of_nonneg_right hwinv (by positivity)
      _ = 162 * |C₃| * (1 + S₀) ^ 5 / M ^ 2 := by ring
      _ ≤ (2 * (|C₁| + |C₂|) + 162 * |C₃|) * (1 + S₀) ^ 5 / M ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
            (by linarith [abs_nonneg C₁, abs_nonneg C₂]) (by positivity)) hM2.le

/-! ### The dispersion integral of the Pauli values -/

section Disp

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ M mγ Λ : ℝ} (hμ₀ : 0 < μ₀) (hM : μ₀ ≤ M) (hmγ : μ₀ ≤ mγ)
  (hΛ : μ₀ ≤ Λ)
include hc hm hs hμ₀ hM hmγ hΛ

/-- Along the curve, the Pauli numerator of the transverse `repB` unit is continuous in the
Feynman parameter `x ∈ (0, 1)`. -/
theorem continuousOn_unitMPauliS_repB {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    ContinuousOn (fun x => unitMPauliS c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) 2 u) (Ioo 0 1) := by
  have hq := (dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu
  unfold unitMPauliS
  simp only [pauliNum_eq_sum_idx]
  exact continuousOn_finsetSum _ fun j _ => continuousOn_const.mul
    (continuousOn_unitMLimitV_repB hc P hm hs hμ₀ hM hmγ hΛ (dot_restMomentum (m := P.m))
      (dot_curveMomentum P.m hu) hq j.1 j.2.1 j.2.2)

omit hc hm hs hμ₀ hM hmγ hΛ in
theorem tendsto_curveParam : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1) / 2) atTop (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
  · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  · exact Set.mem_compl_singleton_iff.2 (by positivity)

omit hc hm hs hμ₀ hM hmγ hΛ in
theorem curveParam_mem (k : ℕ) : 1 / ((k : ℝ) + 1) / 2 ∈ Ioo (-1 : ℝ) 1 := by
  have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
  have h0 : 0 < 1 / ((k : ℝ) + 1) := by positivity
  exact ⟨by linarith, by linarith⟩

/-- **Measurability in the Feynman parameter** of the `repB` Pauli value: it is the pointwise limit
on `(0, 1)` of the continuous functions `S(uₖ)/uₖ²`, `uₖ → 0`. -/
theorem aestronglyMeasurable_unitMPauliZeroPow_repB :
    AEStronglyMeasurable (fun x => unitMPauliZeroPow c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) 2) (volume.restrict (Ioo 0 1)) := by
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun (k : ℕ) x =>
    unitMPauliS c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) 2
      (1 / ((k : ℝ) + 1) / 2) / ((1 / ((k : ℝ) + 1) / 2 : ℝ) : ℂ) ^ 2)
    (fun k => ((continuousOn_unitMPauliS_repB hc P hm hs hμ₀ hM hmγ hΛ
      (curveParam_mem k)).div_const _).aestronglyMeasurable measurableSet_Ioo) ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
  exact (tendsto_unitMPauliS_div_pow hc P hm hs hμ₀ (massesGe_repB hmγ hΛ) 2 (by norm_num)
    (trailOne_repBKappa x) (extraGe_repB hx hM hmγ hΛ)).comp
    tendsto_curveParam

end Disp

/-- **The dispersion integral of the `repB` Pauli values** against a weight `w` on `(0, 1)`:
`∫₀¹ w(x) Z(x) dx`. -/
noncomputable def unitMDispPauliRepB (c : Class5) (P : Params) (s : Fin 8) (w : ℝ → ℂ)
    (M mγ Λ : ℝ) : ℂ :=
  ∫ x in Ioo (0 : ℝ) 1, w x *
    unitMPauliZeroPow c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) 2

/-- **Integrability of the Pauli dispersion integrand** for every weight integrable on
`(0, 1)`. -/
theorem integrableOn_unitMPauliZeroPow_repB_mul {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {w : ℝ → ℂ}
    (hw : IntegrableOn w (Ioo 0 1)) {M mγ Λ : ℝ} (hM : μ₀ ≤ M) (hmγ : μ₀ ≤ mγ)
    (hΛ : μ₀ ≤ Λ) :
    IntegrableOn (fun x => w x * unitMPauliZeroPow c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) 2) (Ioo 0 1) := by
  obtain ⟨C, hC⟩ := norm_unitMPauliZeroPow_repB_disp_le hc P hm hs hμ₀
  refine Integrable.mul_bdd (c := C * (1 + ∑ i, unitMMasses P.m mγ Λ mγ Λ (![mγ, Λ] : Fin 2 → ℝ)
    i ^ 2) ^ 5 / M ^ 2) hw
    (aestronglyMeasurable_unitMPauliZeroPow_repB hc P hm hs hμ₀ hM hmγ hΛ) ?_
  exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx =>
    hC x hx M mγ Λ hM hmγ hΛ)

/-- **The bound of the Pauli dispersion integral**: one constant `C` with
`‖∫₀¹ w Z‖ ≤ C (1 + ∑ᵢ Mᵢ²)⁵ / M² ∫₀¹ ‖w‖` for every integrable weight and all masses `≥ μ₀`. -/
theorem norm_unitMDispPauliRepB_le {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    ∃ C : ℝ, ∀ w : ℝ → ℂ, IntegrableOn w (Ioo 0 1) → ∀ M mγ Λ : ℝ, μ₀ ≤ M → μ₀ ≤ mγ →
      μ₀ ≤ Λ → ‖unitMDispPauliRepB c P s w M mγ Λ‖ ≤
        C * (1 + ∑ i, unitMMasses P.m mγ Λ mγ Λ (![mγ, Λ] : Fin 2 → ℝ) i ^ 2) ^ 5 / M ^ 2 *
          ∫ x in Ioo (0 : ℝ) 1, ‖w x‖ := by
  obtain ⟨C, hC⟩ := norm_unitMPauliZeroPow_repB_disp_le hc P hm hs hμ₀
  refine ⟨C, fun w hw M mγ Λ hM hmγ hΛ => ?_⟩
  unfold unitMDispPauliRepB
  rw [mul_comm _ (∫ x in Ioo (0 : ℝ) 1, ‖w x‖), ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hw.norm.mul_const _) ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC x hx M mγ Λ hM hmγ hΛ) (norm_nonneg _)

end QED.ChainProof.SetCUnitM

end
