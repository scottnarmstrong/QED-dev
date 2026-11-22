/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegFinal

/-!
# Set (c): the regulator limit with measurability only where it is used

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The input
`hReg : IsRegPiece (setCKerRe P₀ (uBD P₀)) setCKKernelPairSum` of
`QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit_of_shell_cbLo` asks for the measurability
of `T ↦ setCKerRe P₀ (uBD P₀) mγ Λ T` at **every** `(mγ, Λ)` and on all of `ℝ`. The class
kernels are `limUnder` values (`unitMPauliZeroPow`, `kkLimP`) whose limits are known to exist
only at positive photon masses `0 < mγ ≤ Λ`; at degenerate regulators the clause concerns a
choice value and cannot be established. The dominated convergence in the spectral variable
evaluates the kernel only at `T = s t_v ≥ 4` and only eventually in `(mγ, Λ)`, so the clause can
be weakened to that range.

* `IsRegPieceE a A`: as `IsRegPiece a A`, with the measurability clause replaced by: eventually
  in `(mγ, Λ) → (0⁺, ∞)`, `T ↦ a mγ Λ (max T 4)` is measurable;
* `IsRegPiece.isRegPieceE`, `IsRegPieceE.add`;
* `regCut`, `isRegPiece_regCut`: the cut-off kernel `a mγ Λ (max T 4)` (`0` where it is not
  measurable) is a regulated piece in the original sense;
* **`tendsto_jDisp_of_E`**: the dominated convergence of `tendsto_jDisp` under `IsRegPieceE`;
* **`setCRegLimitDisp_of_kernelsE`**, **`setCRegLimitB_of_shell_cbLoE`**;
* **`QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit_of_shell_cbLoE`**: the proposition of
  (HS₆) from `hS`, `hB` and `hReg : IsRegPieceE (setCKerRe P₀ (uBD P₀)) setCKKernelPairSum`.
-/

@[expose] public section

open Complex Real Set Filter Topology MeasureTheory
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCK QED.ChainProof.SetCPauli QED.ChainProof.SetCMain

/-! ### Regulated pieces with eventual measurability on `[4, ∞)` -/

/-- **A regulated piece, measurable where it is used**: `a mγ Λ T → A T` for every `T ≥ 4` as
`(mγ, Λ) → (0⁺, ∞)`, eventually `T ↦ a mγ Λ (max T 4)` measurable, and `|a mγ Λ T| ≤ C/√T`
uniformly for small `mγ`, large `Λ`. -/
structure IsRegPieceE (a : ℝ → ℝ → ℝ → ℝ) (A : ℝ → ℝ) : Prop where
  meas : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, Measurable fun T => a p.1 p.2 (max T 4)
  lim : ∀ T, 4 ≤ T → Tendsto (fun p : ℝ × ℝ => a p.1 p.2 T) (𝓝[>] 0 ×ˢ atTop) (𝓝 (A T))
  bound : ∃ C δ Λ₀ : ℝ, 0 < δ ∧ ∀ mγ Λ, 0 < mγ → mγ < δ → Λ₀ < Λ → ∀ T, 4 ≤ T →
    |a mγ Λ T| ≤ C / √T

variable {a a' : ℝ → ℝ → ℝ → ℝ} {A A' : ℝ → ℝ}

theorem IsRegPiece.isRegPieceE (h : IsRegPiece a A) : IsRegPieceE a A where
  meas := Eventually.of_forall fun p => (h.meas p.1 p.2).comp (measurable_id.max measurable_const)
  lim := h.lim
  bound := h.bound

theorem IsRegPieceE.add (h : IsRegPieceE a A) (h' : IsRegPieceE a' A') :
    IsRegPieceE (fun mγ Λ T => a mγ Λ T + a' mγ Λ T) (fun T => A T + A' T) where
  meas := by
    filter_upwards [h.meas, h'.meas] with p hp hp'
    exact hp.add hp'
  lim T hT := (h.lim T hT).add (h'.lim T hT)
  bound := by
    obtain ⟨C, δ, Λ₀, hδ, hC⟩ := h.bound
    obtain ⟨C', δ', Λ₀', hδ', hC'⟩ := h'.bound
    refine ⟨C + C', min δ δ', max Λ₀ Λ₀', lt_min hδ hδ', fun mγ Λ h0 h1 h2 T hT => ?_⟩
    have b₁ := hC mγ Λ h0 (h1.trans_le (min_le_left _ _)) ((le_max_left _ _).trans_lt h2) T hT
    have b₂ := hC' mγ Λ h0 (h1.trans_le (min_le_right _ _)) ((le_max_right _ _).trans_lt h2) T hT
    rw [add_div]
    exact (abs_add_le _ _).trans (add_le_add b₁ b₂)

open Classical in
/-- The cut-off kernel: `a mγ Λ (max T 4)` where this is measurable in `T`, else `0`. -/
noncomputable def regCut (a : ℝ → ℝ → ℝ → ℝ) (mγ Λ T : ℝ) : ℝ :=
  if Measurable (fun T => a mγ Λ (max T 4)) then a mγ Λ (max T 4) else 0

theorem measurable_regCut (a : ℝ → ℝ → ℝ → ℝ) (mγ Λ : ℝ) : Measurable (regCut a mγ Λ) := by
  by_cases h : Measurable (fun T => a mγ Λ (max T 4))
  · have e : regCut a mγ Λ = fun T => a mγ Λ (max T 4) := funext fun T => ite_eq_left h
    rw [e]
    exact h
  · have e : regCut a mγ Λ = fun _ => 0 := funext fun T => ite_eq_right h
    rw [e]
    exact measurable_const

theorem regCut_eq {mγ Λ : ℝ} (h : Measurable (fun T => a mγ Λ (max T 4))) {T : ℝ}
    (hT : 4 ≤ T) : regCut a mγ Λ T = a mγ Λ T := by
  rw [regCut, ite_eq_left h, max_eq_left hT]

/-- **The cut-off kernel is a regulated piece in the original sense.** -/
theorem isRegPiece_regCut (h : IsRegPieceE a A) : IsRegPiece (regCut a) A where
  meas := measurable_regCut a
  lim T hT := by
    refine (h.lim T hT).congr' ?_
    filter_upwards [h.meas] with p hp
    exact (regCut_eq hp hT).symm
  bound := by
    obtain ⟨C, δ, Λ₀, hδ, hC⟩ := h.bound
    refine ⟨C, δ, Λ₀, hδ, fun mγ Λ h0 h1 h2 T hT => ?_⟩
    have hb := hC mγ Λ h0 h1 h2 T hT
    by_cases hm : Measurable (fun T => a mγ Λ (max T 4))
    · rw [regCut_eq hm hT]
      exact hb
    · rw [regCut, ite_eq_right hm, abs_zero]
      exact (abs_nonneg _).trans hb

theorem jDisp_regCut {mγ Λ : ℝ} (h : Measurable (fun T => a mγ Λ (max T 4))) {s₁ s₂ : ℝ}
    (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (c₁ c₂ : ℝ) :
    jDisp (regCut a) s₁ s₂ c₁ c₂ mγ Λ = jDisp a s₁ s₂ c₁ c₂ mγ Λ := by
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  have h₀ : 4 ≤ setCKSpecMass v := by
    have := four_le_mul_setCKSpecMass le_rfl hv
    rwa [one_mul] at this
  rw [regCut_eq h h₀, regCut_eq h (four_le_mul_setCKSpecMass hs₁ hv),
    regCut_eq h (four_le_mul_setCKSpecMass hs₂ hv)]

/-- **Dominated convergence in the spectral variable under `IsRegPieceE`.** -/
theorem tendsto_jDisp_of_E (h : IsRegPieceE a setCKKernelPairSum) {s₁ s₂ : ℝ} (hs₁ : 1 ≤ s₁)
    (hs₂ : 1 ≤ s₂) (c₁ c₂ : ℝ) :
    Tendsto (fun p : ℝ × ℝ => jDisp a s₁ s₂ c₁ c₂ p.1 p.2) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (kDisp 1 + c₁ * kDisp s₁ + c₂ * kDisp s₂)) := by
  refine (tendsto_jDisp (isRegPiece_regCut h) hs₁ hs₂ c₁ c₂).congr' ?_
  filter_upwards [h.meas] with p hp
  exact jDisp_regCut hp hs₁ hs₂ c₁ c₂

/-! ### The regulator limit of set (c) -/

section Kernels

variable {P₀ : Params} {βM : MainIdx → ClsPauliVal} {uBD : Fin 12 → ℝ → ℝ → ℝ → ℂ}
  {uCB uS : Fin 5 → ℝ → ℝ → ℝ → ℂ}

/-- **The regulator limit from the dispersion form of the class values and the regulator limit
of the real part of the total kernel**, with measurability only where it is used. -/
theorem setCRegLimitDisp_of_kernelsE (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hMainBD : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ i : Fin 12,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uBD i mγ Λ) (βM (.inl i) M₁ M₂ c₁ c₂ mγ Λ D s +
        βM (.inr (i, 0)) M₁ M₂ c₁ c₂ mγ Λ D s + βM (.inr (i, 1)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hCtCB : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uCB k mγ Λ) (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hCtS : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uS k mγ Λ) (ctPauliAll P₀ (.inr (.inr k)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hReg : IsRegPieceE (kerRe P₀ uBD uCB uS) setCKKernelPairSum) :
    SetCRegLimitDisp P₀ (setCPauliB P₀ βM) := by
  refine setCRegLimitDisp_of_fixLim hm fun M₁ M₂ c₁ c₂ hM₁ hM₂ hc hc' η hη => ?_
  set K : ℝ := P₀.e ^ 6 / (64 * π ^ 6) with hK
  have hlim := (tendsto_jDisp_of_E hReg (one_le_sq_div hm hM₁) (one_le_sq_div hm hM₂) c₁
    c₂).const_mul K
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := exists_of_eventually_regRange (Metric.tendsto_nhds.1 hlim η hη)
  refine ⟨min δ (min 1 (2 * P₀.m)), lt_min hδ (lt_min one_pos (by linarith)), max Λ₀ 1,
    fun mγ Λ h0 h1 h2 => ?_⟩
  have hδ' : mγ < δ := h1.trans_le (min_le_left _ _)
  have h1' : mγ < 1 := h1.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h2m : mγ < 2 * P₀.m := h1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hΛ : Λ₀ < Λ := (le_max_left _ _).trans_lt h2
  have hmΛ : mγ < Λ := h1'.trans ((le_max_right _ _).trans_lt h2)
  have hd := hΛ₀ mγ Λ h0 hδ' hΛ
  rw [Real.dist_eq] at hd
  rw [setCPauliB_eq_kerRe hMainBD hCtCB hCtS he hM₁ hM₂ hc hc' h0 hmΛ h2m]
  have e : P₀.e ^ 6 * kDispPV P₀.m M₁ M₂ c₁ c₂ / (64 * π ^ 6) =
      K * (kDisp 1 + c₁ * kDisp (M₁ ^ 2 / P₀.m ^ 2) + c₂ * kDisp (M₂ ^ 2 / P₀.m ^ 2)) := by
    rw [hK, kDispPV]
    ring
  rw [e]
  exact hd

end Kernels

/-- **The regulator limit of set (c) from the counterterm leaves and the Stage L limit**, with
measurability only where it is used. -/
theorem setCRegLimitB_of_shell_cbLoE {P₀ : Params} (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hS : ShellDisp P₀ (shellKer₀ P₀) (shellKer₁C P₀)) (hB : CBLoBEq P₀)
    (hReg : IsRegPieceE (setCKerRe P₀ (uBD P₀)) setCKKernelPairSum) :
    SetCRegLimitB P₀ (setCPauliB P₀ (setCBetaM P₀ fun i => clsPauliLim mainFam P₀ (.inl i))) :=
  setCRegLimitB_of_disp (setCRegLimitDisp_of_kernelsE he hm
    (βM := setCBetaM P₀ fun i => clsPauliLim mainFam P₀ (.inl i))
    (fun _ _ _ _ _ _ _ _ hA i => isDispPV_mainBD hA i)
    (isDispPV_CB_of_loB he hB) (isDispPV_S_of_shell he hS) hReg)

end QED.ChainProof.SetCRegDisp

namespace QED.ThreeLoop

open QED.ChainProof.SetCRegDisp QED.ChainProof.SetCK

/-- **(HS₆) from the counterterm leaves and the Stage L limit**, with the measurability of the
total kernel required only eventually in the regulators and on `[4, ∞)`. -/
theorem isFormFactorPair_vertexSetC_pauli_limit_of_shell_cbLoE (P₀ : Params)
    (hS : ShellDisp P₀ (shellKer₀ P₀) (shellKer₁C P₀))
    (hB : CBLoBEq P₀) (hReg : IsRegPieceE (setCKerRe P₀ (uBD P₀)) setCKKernelPairSum)
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2) ∧
        ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2 →
          (∃ s : ℝ × ℝ × ℝ, IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s) ∧
          ∀ s : ℝ × ℝ × ℝ, IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - (a1SixSetC : ℂ)‖ < η :=
  isFormFactorPair_vertexSetC_pauli_limit_of_regB P₀
    (setCRegLimitB_of_shell_cbLoE he hm hS hB hReg) he hm η hη

end QED.ThreeLoop

end
