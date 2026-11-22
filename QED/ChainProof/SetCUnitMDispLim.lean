/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMDispPauli

/-!
# Multi-denominator units: the `q² → 0⁺` Pauli limit of the `repB` dispersion integral

Helper level for set (c) (stage L2). The Pauli projection of the dispersion integral
`∫₀¹ w(x) L(x) dx` of the transverse `repB` unit tends, as `q² → 0⁺`, to
`∫₀¹ w(x) Z(x) dx / (64 e m⁵)`: the `q → 0` limit and the integral over the Feynman parameter
commute. The domination is a bound on the quotients `S_x(u)/u²` along the curve, uniform in `x`
and in `0 < |u| ≤ 1/2`, obtained as for the values: the partial fraction against the element line
and the heavy-line bound of `QED/ChainProof/SetCUnitMDispBd.lean`, now at fixed `u`.

* `unitMMasses_slot_self`: replacing the mass of line `s` by itself changes nothing;
* `unitMPauliS_succ`: the recursion `S_{n+1} = S_n(init) - μ² S_n` along the curve;
* **`norm_unitMPauliQuotPow_slot_le`**, **`norm_unitMPauliQuotPow_le`**: `‖S_n(u)/u²‖ ≤
  C (1 + ∑ᵢ Mᵢ²)ⁿ⁺²` for `0 < |u| ≤ 1/2`, uniformly in a heavy mass on line `s`;
* `unitMPauliS_repB_eq`, **`norm_unitMPauliS_repB_div_le`**: the `repB` quotients are bounded
  by `C (1 + ∑ᵢ Mᵢ²)⁵ / M²`, uniformly in `x ∈ (0, 1)` and `0 < |u| ≤ 1/2`;
* `pauliNum_unitMDispRepB`: the Pauli numerator of the dispersion integral is the integral of
  the Pauli numerators;
* **`tendsto_formFactorProj₂_unitMDispRepB`**: the `q² → 0⁺` Pauli limit of the dispersion
  integral is `unitMDispPauliRepB / (64 e m⁵)`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.Dirac QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable QED.TwoLoop.ClassLimit QED.ChainProof.SetCUnit
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.VPHalfAtAssembly (specMu mem_Ioo_mul_pos)

variable {r : ℕ}

theorem unitMMasses_slot_self {s : Fin 8} (hs : 4 ≤ (s : ℕ)) (m a A b B : ℝ) (cs : Fin r → ℝ) :
    unitMMasses m (slotMa s (unitMasses m a A b B s) a) (slotMA s (unitMasses m a A b B s) A)
        (slotMb s (unitMasses m a A b B s) b) (slotMB s (unitMasses m a A b B s) B) cs =
      unitMMasses m a A b B cs := by
  funext i
  by_cases hi : i = mEmb r s
  · subst hi
    simp only [unitMMasses_mEmb, unitMasses_slot hs, ite_true]
  · exact unitMMasses_slot hs m a A b B _ cs i hi

/-- **The recursion along the curve**: `S_{n+1}(u) = S_n(init)(u) - μ² S_n(u)`. -/
theorem unitMPauliS_succ {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {n : ℕ} {κ cs : Fin (r + 1) → ℝ} (hnr : n + 1 ≤ r + 1) (hT : TrailOne (n + 1) κ)
    (hX : ExtraGe μ₀ κ cs) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    unitMPauliS c P s κ (unitMMasses P.m a A b B cs) (n + 1) u =
      unitMPauliS c P s (Fin.init κ) (unitMMasses P.m a A b B (Fin.init cs)) n u -
        ((cs (Fin.last r) ^ 2 : ℝ) : ℂ) * unitMPauliS c P s κ (unitMMasses P.m a A b B cs) n u := by
  have hq := (dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu
  unfold unitMPauliS
  rw [← pauliNum_sub_smul]
  congr 1
  funext ν
  exact unitMLimitV_succ_mat hc P hm hs hμ₀ hM (dot_restMomentum (m := P.m))
    (dot_curveMomentum P.m hu) hq hnr hT hX ν

theorem mem_Ioo_of_abs_le_half {u : ℝ} (hu : |u| ≤ 1 / 2) : u ∈ Ioo (-1 : ℝ) 1 := by
  rw [abs_le] at hu
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- **The quotients with powers and a heavy element line**: if the last `n ≤ r` extra lines are
unscaled, one constant `C` with `‖S_n(u)/u²‖ ≤ C (1 + ∑ᵢ Mᵢ²)ⁿ⁺²` for `0 < |u| ≤ 1/2`, uniformly in
the mass `t ≥ μ_s` of line `s` (`Mᵢ` the masses before the replacement). -/
theorem norm_unitMPauliQuotPow_slot_le {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) (n : ℕ) :
    ∀ {r : ℕ} {κ : Fin r → ℝ}, n ≤ r → TrailOne n κ → (∀ j, 0 < κ j ∧ κ j ≤ 1) →
    ∃ C : ℝ, ∀ (a A b B t : ℝ) (cs : Fin r → ℝ), MassesGe μ₀ a A b B → (∀ j, μ₀ ≤ cs j) →
      unitMasses P.m a A b B s ≤ t → ∀ u : ℝ, u ≠ 0 → |u| ≤ 1 / 2 →
      ‖unitMPauliS c P s κ (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b)
          (slotMB s t B) cs) n u / (u : ℂ) ^ 2‖ ≤
        C * (1 + ∑ i, unitMMasses P.m a A b B cs i ^ 2) ^ (n + 2) := by
  induction n with
  | zero =>
    intro r κ _ hT hκ
    obtain ⟨C, hC⟩ := norm_unitMPauliQuot_slot_le hc P hm hs hμ₀ hκ
    refine ⟨C, fun a A b B t cs hM hcs ht u hu0 hu => ?_⟩
    have hX : ExtraGe μ₀ κ cs := fun j => ⟨(hκ j).1, (hκ j).2, hcs j⟩
    have hM' := massesGe_slot (s := s) hM ((le_unitMasses (m := P.m) hs hM).trans ht)
    have h := hC a A b B t cs hM hcs ht u hu0 hu
    rw [unitMPauliS_neg hc P hm hs hμ₀ hM' (Nat.zero_le r) hT hX (mem_Ioo_of_abs_le_half hu)]
      at h
    have hu2 : (u : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (ofReal_ne_zero.mpr hu0)
    rw [show ∀ z : ℂ, (z + z) / (2 * (u : ℂ) ^ 2) = z / (u : ℂ) ^ 2 from fun z => by
      field_simp; ring] at h
    exact h
  | succ n ih =>
    intro r κ hnr hT hκ
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨C₁, hC₁⟩ := ih (r := r) (κ := Fin.init κ) (by omega) hT.init fun j => hκ _
    obtain ⟨C₂, hC₂⟩ := ih (r := r + 1) (κ := κ) (by omega) hT.of_succ hκ
    refine ⟨|C₁| + |C₂|, fun a A b B t cs hM hcs ht u hu0 hu => ?_⟩
    have hX : ExtraGe μ₀ κ cs := fun j => ⟨(hκ j).1, (hκ j).2, hcs j⟩
    have hM' := massesGe_slot (s := s) hM ((le_unitMasses (m := P.m) hs hM).trans ht)
    rw [unitMPauliS_succ hc P hm hs hμ₀ hM' hnr hT hX (mem_Ioo_of_abs_le_half hu), sub_div,
      mul_div_assoc]
    set S := ∑ i, unitMMasses P.m a A b B cs i ^ 2 with hS
    have hS₁ := sum_sq_unitMMasses_succ P.m a A b B cs
    rw [← hS] at hS₁
    have hS₁0 : 0 ≤ ∑ i, unitMMasses P.m a A b B (Fin.init cs) i ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have hl0 : 0 ≤ cs (Fin.last r) ^ 2 := sq_nonneg _
    have h1 := hC₁ a A b B t (Fin.init cs) hM (fun j => hcs _) ht u hu0 hu
    have h2 := hC₂ a A b B t cs hM hcs ht u hu0 hu
    have hpow₁ : (1 + ∑ i, unitMMasses P.m a A b B (Fin.init cs) i ^ 2) ^ (n + 2) ≤
        (1 + S) ^ (n + 2) := pow_le_pow_left₀ (by positivity) (by linarith) _
    have hpow : (1 + S) ^ (n + 2) ≤ (1 + S) ^ (n + 1 + 2) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hP0 : 0 ≤ (1 + S) ^ (n + 2) := pow_nonneg (by linarith) _
    have hn1 := h1.trans ((mul_le_mul_of_nonneg_left hpow₁ (abs_nonneg _)).trans'
        (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (by positivity) _)) |>.trans
        (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)))
    have hn2 : ‖((cs (Fin.last r) ^ 2 : ℝ) : ℂ) * (unitMPauliS c P s κ
        (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) cs) n u /
          (u : ℂ) ^ 2)‖ ≤ |C₂| * (1 + S) ^ (n + 1 + 2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0,
        show n + 1 + 2 = n + 2 + 1 by omega, pow_succ]
      have h3 : C₂ * (1 + S) ^ (n + 2) ≤ |C₂| * (1 + S) ^ (n + 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hP0
      have h4 : cs (Fin.last r) ^ 2 ≤ 1 + S := by linarith
      calc cs (Fin.last r) ^ 2 * ‖unitMPauliS c P s κ
            (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) cs) n u /
              (u : ℂ) ^ 2‖
          ≤ (1 + S) * (|C₂| * (1 + S) ^ (n + 2)) :=
            mul_le_mul h4 (h2.trans h3) (norm_nonneg _) (by linarith)
        _ = |C₂| * ((1 + S) ^ (n + 2) * (1 + S)) := by ring
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ |C₁| * (1 + S) ^ (n + 1 + 2) + |C₂| * (1 + S) ^ (n + 1 + 2) := add_le_add hn1 hn2
      _ = (|C₁| + |C₂|) * (1 + S) ^ (n + 1 + 2) := by ring

/-- **The quotients with powers**: `‖S_n(u)/u²‖ ≤ C (1 + ∑ᵢ Mᵢ²)ⁿ⁺²` for `0 < |u| ≤ 1/2`, for all
photon and extra masses `≥ μ₀`. -/
theorem norm_unitMPauliQuotPow_le {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) (n : ℕ) {r : ℕ}
    {κ : Fin r → ℝ} (hnr : n ≤ r) (hT : TrailOne n κ) (hκ : ∀ j, 0 < κ j ∧ κ j ≤ 1) :
    ∃ C : ℝ, ∀ (a A b B : ℝ) (cs : Fin r → ℝ), MassesGe μ₀ a A b B → (∀ j, μ₀ ≤ cs j) →
      ∀ u : ℝ, u ≠ 0 → |u| ≤ 1 / 2 →
      ‖unitMPauliS c P s κ (unitMMasses P.m a A b B cs) n u / (u : ℂ) ^ 2‖ ≤
        C * (1 + ∑ i, unitMMasses P.m a A b B cs i ^ 2) ^ (n + 2) := by
  obtain ⟨C, hC⟩ := norm_unitMPauliQuotPow_slot_le hc P hm hs hμ₀ n hnr hT hκ
  refine ⟨C, fun a A b B cs hM hcs u hu0 hu => ?_⟩
  have h := hC a A b B _ cs hM hcs le_rfl u hu0 hu
  rwa [unitMMasses_slot_self hs] at h

/-! ### The `repB` quotients, uniformly in the Feynman parameter -/

theorem unitMPauliS_repBExtra_rot (c : Class5) (P : Params) (s : Fin 8) (m a A b B t mγ Λ : ℝ)
    (n : ℕ) (u : ℝ) :
    unitMPauliS c P s (fun _ : Fin 3 => (1 : ℝ)) (unitMMasses m a A b B (repBExtra t mγ Λ)) n u =
      unitMPauliS c P s (fun _ : Fin 3 => (1 : ℝ)) (unitMMasses m a A b B ![mγ, Λ, t]) n u := by
  rw [← repBExtra_rot]
  exact unitMPauliS_perm c P s (finRotate 3).symm (fun _ => 1) m a A b B ![mγ, Λ, t] n u

/-- **The dispersion form along the curve**: `S_x(u) = (x(1-x))⁻¹ S(u)` with the unscaled unit
of extra masses `[specMu M x, m_γ, Λ]`. -/
theorem unitMPauliS_repB_eq {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ mγ Λ : ℝ} (hμ₀ : 0 < μ₀) (hmγ : μ₀ ≤ mγ) (hΛ : μ₀ ≤ Λ)
    {x M : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hM : μ₀ ≤ M) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    unitMPauliS c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) 2 u =
      ((x * (1 - x) : ℝ) : ℂ)⁻¹ * unitMPauliS c P s (fun _ => 1)
        (unitMMasses P.m mγ Λ mγ Λ (repBExtra (specMu M x) mγ Λ)) 2 u := by
  have h0 := mem_Ioo_mul_pos hx
  rw [unitMPauliS_descale hc P hm hs hμ₀ (massesGe_repB hmγ hΛ) (by norm_num)
    (trailOne_repBKappa x) (extraGe_repB hx hM hmγ hΛ) 0 hu, update_repBKappa]
  have hk : repBKappa x 0 = √(x * (1 - x)) := rfl
  have hc0 : repBExtra M mγ Λ 0 = M := rfl
  rw [hk, hc0, Real.sq_sqrt h0.le, div_sqrt_eq_specMu (hμ₀.le.trans hM) hx, update_repBExtra]

/-- **The `repB` quotients, bounded uniformly in the Feynman parameter**: one constant `C` with
`‖S_x(u)/u²‖ ≤ C (1 + ∑ᵢ Mᵢ²)⁵ / M²` for all `x ∈ (0, 1)`, `0 < |u| ≤ 1/2` and masses `≥ μ₀`
(`Mᵢ` the masses of the ten lines other than the dispersion line). -/
theorem norm_unitMPauliS_repB_div_le {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    ∃ C : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1, ∀ M mγ Λ : ℝ, μ₀ ≤ M → μ₀ ≤ mγ → μ₀ ≤ Λ →
      ∀ u : ℝ, u ≠ 0 → |u| ≤ 1 / 2 →
      ‖unitMPauliS c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) 2 u /
          (u : ℂ) ^ 2‖ ≤
        C * (1 + ∑ i, unitMMasses P.m mγ Λ mγ Λ (![mγ, Λ] : Fin 2 → ℝ) i ^ 2) ^ 5 / M ^ 2 := by
  obtain ⟨C₁, hC₁⟩ := norm_unitMPauliQuotPow_le hc P hm hs hμ₀ 2 (r := 2) (κ := fun _ => 1)
    le_rfl (fun _ _ => rfl) fun _ => ⟨one_pos, le_rfl⟩
  obtain ⟨C₂, hC₂⟩ := norm_unitMPauliQuotPow_slot_le hc P hm hs hμ₀ 2 (r := 2)
    (κ := fun _ => 1) le_rfl (fun _ _ => rfl) fun _ => ⟨one_pos, le_rfl⟩
  obtain ⟨C₃, hC₃⟩ := norm_unitMPauliQuotPow_le hc P hm hs hμ₀ 2 (r := 3) (κ := fun _ => 1)
    (by norm_num) (fun _ _ => rfl) fun _ => ⟨one_pos, le_rfl⟩
  refine ⟨2 * (|C₁| + |C₂|) + 162 * |C₃|, fun x hx M mγ Λ hM hmγ hΛ u hu0 hu => ?_⟩
  have hu1 := mem_Ioo_of_abs_le_half hu
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
  rw [unitMPauliS_repB_eq hc P hm hs hμ₀ hmγ hΛ hx hM hu1, mul_div_assoc, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hw.le]
  by_cases hcase : 2 * μs ^ 2 ≤ μ' ^ 2
  · have hμs2p : 0 < μs ^ 2 := pow_pos (hμ₀.trans_le hμs0) 2
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
    rw [unitMPauliS_repBExtra_rot, unitMPauliS_pf hc P hm hs hμ₀ hMg le_rfl
      (fun _ _ => rfl) rfl hX hne hu1, hinit, mul_div_assoc, sub_div]
    change w⁻¹ * ‖(((μ' ^ 2 - μs ^ 2 : ℝ) : ℂ))⁻¹ * (unitMPauliS c P s (fun _ => 1)
      (unitMMasses P.m mγ Λ mγ Λ ![mγ, Λ]) 2 u / (u : ℂ) ^ 2 - unitMPauliS c P s (fun _ => 1)
        (unitMMasses P.m (slotMa s μ' mγ) (slotMA s μ' Λ) (slotMb s μ' mγ) (slotMB s μ' Λ)
          ![mγ, Λ]) 2 u / (u : ℂ) ^ 2)‖ ≤ _
    have h1 := hC₁ mγ Λ mγ Λ ![mγ, Λ] hMg (fun j => by fin_cases j <;> assumption) u hu0 hu
    have h2 := hC₂ mγ Λ mγ Λ μ' ![mγ, Λ] hMg (fun j => by fin_cases j <;> assumption) hle u
      hu0 hu
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
    calc w⁻¹ * ((μ' ^ 2 - μs ^ 2)⁻¹ * ‖_‖)
        ≤ w⁻¹ * (2 / μ' ^ 2 * ((|C₁| + |C₂|) * (1 + S₀) ^ 5)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hinv (hsub.trans hC) (norm_nonneg _)
            (by positivity)) (by positivity)
      _ = 2 * (|C₁| + |C₂|) * (1 + S₀) ^ 5 / M ^ 2 := by
          rw [← hwμ]; field_simp
      _ ≤ (2 * (|C₁| + |C₂|) + 162 * |C₃|) * (1 + S₀) ^ 5 / M ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
            (by linarith [abs_nonneg C₃]) (by positivity)) hM2.le
  · push Not at hcase
    have h3 := hC₃ mγ Λ mγ Λ (repBExtra μ' mγ Λ) hMg
      (fun j => by fin_cases j <;> assumption) u hu0 hu
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

/-! ### The Pauli limit of the dispersion integral -/

section Lim

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ M mγ Λ : ℝ} (hμ₀ : 0 < μ₀) (hM : μ₀ ≤ M) (hmγ : μ₀ ≤ mγ)
  (hΛ : μ₀ ≤ Λ) {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1))
include hc hm hs hμ₀ hM hmγ hΛ hw

/-- **The Pauli numerator of the dispersion integral** along the curve is the dispersion integral
of the Pauli numerators. -/
theorem pauliNum_unitMDispRepB {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
        (unitMDispRepB c P s w M mγ Λ (restMomentum P.m) (curveMomentum P.m u)) =
      ∫ x in Ioo (0 : ℝ) 1, w x * unitMPauliS c P s (repBKappa x)
        (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) 2 u := by
  have hq := (dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu
  have hI : ∀ j : Idx, IntegrableOn (fun x => w x * unitMLimitV c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) (restMomentum P.m) (curveMomentum P.m u) 2
        j.1 j.2.1 j.2.2) (Ioo 0 1) := fun j =>
    integrableOn_unitMLimitV_repB_mul hc P hm hs hμ₀ (dot_restMomentum (m := P.m))
      (dot_curveMomentum P.m hu) hq hw hM hmγ hΛ j.1 j.2.1 j.2.2
  simp only [pauliNum_eq_sum_idx, unitMDispRepB, Matrix.of_apply, unitMPauliS]
  have hpt : ∀ x, w x * ∑ j : Idx, pauliWt P.m (curveMomentum P.m u) (restMomentum P.m)
      j.1 j.2.1 j.2.2 * unitMLimitV c P s (repBKappa x)
        (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) (restMomentum P.m) (curveMomentum P.m u) 2
          j.1 j.2.1 j.2.2 =
      ∑ j : Idx, pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
        (w x * unitMLimitV c P s (repBKappa x)
          (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) (restMomentum P.m)
            (curveMomentum P.m u) 2 j.1 j.2.1 j.2.2) := fun x => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [hpt]
  rw [integral_finsetSum _ fun j _ => (hI j).const_mul _]
  simp only [integral_const_mul]

/-- **The `q² → 0⁺` Pauli limit of the `repB` dispersion integral**: the Pauli projection of
`∫₀¹ w(x) L(x) dx` tends to `∫₀¹ w(x) Z(x) dx / (64 e m⁵)`, the dispersion integral of the
Pauli values. -/
theorem tendsto_formFactorProj₂_unitMDispRepB (e : ℝ) :
    Tendsto (fun Q => QED.OneLoop.formFactorProj₂ e P.m (boostMomentum P.m Q) (restMomentum P.m)
        (unitMDispRepB c P s w M mγ Λ (restMomentum P.m) (boostMomentum P.m Q)))
      (𝓝[>] 0) (𝓝 (unitMDispPauliRepB c P s w M mγ Λ / (64 * (e : ℂ) * (P.m : ℂ) ^ 5))) := by
  refine tendsto_formFactorProj₂_of hm e
    (fun p' => unitMDispRepB c P s w M mγ Λ (restMomentum P.m) p') ?_
  obtain ⟨C, hC⟩ := norm_unitMPauliS_repB_div_le hc P hm hs hμ₀
  set B := C * (1 + ∑ i, unitMMasses P.m mγ Λ mγ Λ (![mγ, Λ] : Fin 2 → ℝ) i ^ 2) ^ 5 / M ^ 2
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ≠ 0 ∧ |u| ≤ 1 / 2 := by
    have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), |u| ≤ 1 / 2 :=
      Filter.Eventually.mono (nhdsWithin_le_nhds (Icc_mem_nhds
        (by norm_num : (-(1 / 2) : ℝ) < 0) (by norm_num : (0 : ℝ) < 1 / 2)))
        fun u hu => abs_le.2 hu
    filter_upwards [h1, self_mem_nhdsWithin] with u hu (hu0 : u ≠ 0)
    exact ⟨hu0, hu⟩
  have hlim : Tendsto (fun u => ∫ x in Ioo (0 : ℝ) 1, w x * (unitMPauliS c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) 2 u / (u : ℂ) ^ 2)) (𝓝[≠] 0)
      (𝓝 (unitMDispPauliRepB c P s w M mγ Λ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖w x‖ * B) ?_ ?_
      (hw.norm.mul_const _) ?_
    · filter_upwards [h0] with u hu
      exact hw.aestronglyMeasurable.mul (((continuousOn_unitMPauliS_repB hc P hm hs hμ₀ hM hmγ
        hΛ (mem_Ioo_of_abs_le_half hu.2)).div_const _).aestronglyMeasurable measurableSet_Ioo)
    · filter_upwards [h0] with u hu
      refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC x hx M mγ Λ hM hmγ hΛ u hu.1 hu.2) (norm_nonneg _)
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
      exact (tendsto_unitMPauliS_div_pow hc P hm hs hμ₀ (massesGe_repB hmγ hΛ) 2 (by norm_num)
        (trailOne_repBKappa x) (extraGe_repB hx hM hmγ hΛ)).const_mul _
  refine hlim.congr' ?_
  filter_upwards [h0] with u hu
  rw [pauliNum_unitMDispRepB hc P hm hs hμ₀ hM hmγ hΛ hw (mem_Ioo_of_abs_le_half hu.2),
    ← integral_div]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

end Lim

end QED.ChainProof.SetCUnitM

end
