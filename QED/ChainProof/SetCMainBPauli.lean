/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBPauliParts
public import QED.ChainProof.SetCMainBRestLink
public import QED.ChainProof.SetCPauliRepB

/-!
# Set (c), the bubble classes: covariance, Pauli and `♯` links from the kk link

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, inputs `hBc`,
`hPB`, `hSB` of `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit_of_repB`. The limit of
`repB i` is the piece `pieceB R i K = -(c L₀/3 · (dG + dK) + disp + K)`, `K` the limit of the
longitudinal dispersive part `kkB`; the first three parts have the three properties
(`QED/ChainProof/SetCMainBPauliParts.lean`).

* `MainBKKLinkP P₀ i` (open, strengthens `QED.ChainProof.SetCMainB.MainBKKLink`): at the set (c)
  data, the limits of `kkB` form a piece `K` that is covariant, `♯`-odd and has a Pauli limit;
  `mainBKKLink_of_P`;
* `tendsto_restB_of_kk`, **`isClassLimC_inl`**: the class limit is `pieceB R i K`;
* **`isPieceClass_inl`**, `setCClassLim_inl`, **`setCClassCov_inl`**, **`setCClassPauli_inl`**
  (value `clsPauliLim mainFam P₀ (.inl i)`), **`setCClassSharp_inl`**;
* `clsPauliLim_inl_eq`: that value is `-(c L₀/3 · (Z_G + Z_K) + Z_D + Z_kk) / (64 e m⁵)`;
* **`isFormFactorPair_vertexSetC_pauli_limit_of_kkLinkP`**: (HS₆) from `MainBKKLinkP` for the
  twelve orbits and the regulator limit.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCLink QED.ChainProof.SetALink QED.ChainProof.SetCMain
open QED.ChainProof.SetCUnitM QED.ChainProof.SetCPauli
open QED.ChainProof.SetCUnitM (jointEnergyFirstIntegrable_sub_mul)
open QED.ChainProof.SetAPauli (regParams regFlavors)
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit

variable {P₀ : Params}

/-- **The strengthened longitudinal dispersive link of `repB i`** (open): at the set (c) data the
`ε → 0⁺` limits of the value of the longitudinal dispersive part `kkB` at the pairs `IsPairQ`
form a piece `K` that is covariant (`PieceCov`), `♯`-odd (`PieceSharp`) and has a Pauli limit
`Z` (`PiecePauli`). -/
def MainBKKLinkP (P₀ : Params) (i : Fin 12) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∃ (K : Piece) (Z : ℂ),
    (∀ p' p, IsPairQ P₀.m p' p → ∀ μ α β,
      Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
        (kkB { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
          i p p' μ α β)) (𝓝[>] 0) (𝓝 (K p' p μ α β))) ∧
      PieceCov P₀.m K ∧ PieceSharp P₀.m K ∧ PiecePauli P₀.m K Z

theorem mainBKKLink_of_P {i : Fin 12} (hK : MainBKKLinkP P₀ i) : MainBKKLink P₀ i := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq
  obtain ⟨K, -, hK, -⟩ := hK M₁ M₂ c₁ c₂ mγ Λ D s hA
  exact ⟨K p' p, hK p' p hpq⟩

section Lim

variable {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ} {i : Fin 12} {p' p : Fin 4 → ℝ}
  {Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}

/-- **The rest converges to the limit of the longitudinal dispersive part** (the `ε S_ε` part
tends to zero). -/
theorem tendsto_restB_of_kk (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (hpq : IsPairQ P₀.m p' p)
    (hY : ∀ μ α β, Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
      (kkB { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        i p p' μ α β)) (𝓝[>] 0) (𝓝 (Y μ α β))) (μ α β : Fin 4) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
      (restB { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        i p p' μ α β)) (𝓝[>] 0) (𝓝 (Y μ α β)) := by
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  have hpq' := hpq
  obtain ⟨hp', hp, -, -, hq⟩ := hpq'
  set R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with hRdef
  have hMf : ∀ f, R.m ≤ R.mass f := setCAdm_mass hA
  have hMp : ∀ f, 0 < R.mass f := fun f => hm.trans_le (hMf f)
  have hS := tendsto_sB (R := R) hm hγ hγΛ hp hp' hq.le (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) rfl hMf
    i μ α β
  refine (((hY μ α β).sub (hS.const_mul 1)).congr' ?_).trans (by simp)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  obtain ⟨-, hO⟩ := mainBOuterLink P₀ i M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq ε hε μ α β
  have hR := (jointEnergyFirstIntegral_outerBub_split { R with ε := ε } R
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) rfl rfl rfl rfl i p p' μ α β hε hMp hO).1
  have hSi := (jointEnergyFirstIntegral_sB { R with ε := ε } R (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (hm := rfl) (he := rfl) (hγ := rfl) (hΛ := rfl) i p p' μ α β hε hMp).1
  have ekk : kkB { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) i p p' μ α β = fun ℓ =>
      restB { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) i p p' μ α β ℓ -
        (-1) * sB { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) i p p' μ α β ℓ :=
    funext fun ℓ => by rw [restB_eq]; ring
  have hKi := (jointEnergyFirstIntegrable_sub_mul hR hSi (-1)).1
  rw [← ekk] at hKi
  have erest : restB { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) i p p' μ α β =
      fun ℓ => kkB { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) i p p' μ α β ℓ -
        1 * sB { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) i p p' μ α β ℓ :=
    funext fun ℓ => by rw [restB_eq]; ring
  rw [erest, (jointEnergyFirstIntegrable_sub_mul hKi hSi 1).2]

/-- **The explicit limit of `repB i`**: `-(c L₀/3 · (dG + dK) + disp + K)`. -/
noncomputable def pieceB (R : Params) (i : Fin 12) (K : Piece) : Piece := fun p' p μ =>
  -(logW R 0 • (pieceG R i p' p μ + pieceK R i p' p μ) + pieceD R i p' p μ + K p' p μ)

/-- **The class limit of `repB i` is `pieceB`.** -/
theorem isClassLimC_inl (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (hpq : IsPairQ P₀.m p' p)
    {K : Piece} (hK : ∀ μ α β, Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
      (kkB { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        i p p' μ α β)) (𝓝[>] 0) (𝓝 (K p' p μ α β))) :
    IsClassLimC mainFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inl i) p' p
      (pieceB (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) i K p' p) := by
  intro μ α β
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  have hY := tendsto_restB_of_kk hA hpq hK μ α β
  have hpq' := hpq
  obtain ⟨hp', hp, -, -, hq⟩ := hpq'
  set R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with hRdef
  have hMf : ∀ f, R.m ≤ R.mass f := setCAdm_mass hA
  have hMp : ∀ f, 0 < R.mass f := fun f => hm.trans_le (hMf f)
  have hv : Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
      (dKIntegrand { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) 1 (repD i 0)
        (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ)))
      (𝓝[>] 0) (𝓝 (wKD R 1 * dKLimB R i p' p μ α β)) :=
    ((hasLimJ_dKLimB (R := R) hm hγ hγΛ i hp hp' hq.le μ α β).2.const_mul (wKD R 1)).congr fun ε =>
      (dK_repD_value { R with ε := ε } R (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) rfl rfl rfl rfl 1 i 0
        p p' μ α β).symm
  have e : pieceB R i K p' p μ α β = -(logW R 0 * (dGLimD R 1 i p p' μ α β +
      wKD R 1 * dKLimB R i p' p μ α β) + -2 * vpCst R * wD R 1 * ∑ f, unitMDispRepB
        (repBClass i) R (repBSlot i) (dispWt R f) (R.mass f) R.mγ R.Λ p p' μ α β +
      K p' p μ α β) := by
    simp only [pieceB, pieceK, pieceD, Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sum_apply, smul_eq_mul]
  rw [e]
  have hI := (tendsto_logW R hMp).mul ((tendsto_dG_repD (R := R) hm hγ hγΛ hp hp' hq.le
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) rfl 1 i 0 μ α β).add hv)
  have hII := tendsto_dispVal (R := R) hm hγ hγΛ hp hp' hq.le hMf i μ α β
  refine (((hI.add hII).add hY).neg).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  obtain ⟨hnest, hO⟩ := mainBOuterLink P₀ i M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq ε hε μ α β
  have hval := (jointEnergyFirstIntegral_outerBub_split { R with ε := ε } R
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) rfl rfl rfl rfl i p p' μ α β hε hMp hO).2
  have hcv := contractionValue_repB_eq { R with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (shareCt D s) hε.ne' (flavorsLoop_lepton _) i (pOut := fun _ => p') (pIn := fun _ => p)
    (kIn := fun _ => p' - p) (by simp) (fun _ => α) (fun _ => β) (fun _ => μ)
  simp only [mainFam, mainVal, clsVal, Matrix.neg_apply, Matrix.of_apply]
  rw [hcv, hnest, hval]
  simp only [vpCst, wD, dispWt, QED.WickModel.Params.mass, QED.WickModel.Params.loopCoeff]

end Lim

/-! ### The class links -/

/-- **The class limits of `repB i` are a piece with the three properties**, given the
strengthened kk link. -/
theorem isPieceClass_inl {i : Fin 12} (hK : MainBKKLinkP P₀ i) :
    IsPieceClass mainFam P₀ (.inl i) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  have hMf := setCAdm_mass hA
  obtain ⟨K, Z, hKl, hKc, hKs, hKp⟩ := hK M₁ M₂ c₁ c₂ mγ Λ D s hA
  set R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ
  obtain ⟨ZK, hZK⟩ := exists_piecePauli_K (R := R) hm hγ hγΛ i
  have hC := (((((pieceCov_G (R := R) hm hγ hγΛ i).add (pieceCov_K (R := R) hm hγ hγΛ i)).smul
    (logW R 0)).add (pieceCov_D (R := R) hm hγ hγΛ hMf i)).add hKc).neg
  have hS := (((((pieceSharp_G (R := R) hm hγ hγΛ i).add
    (pieceSharp_K (R := R) hm hγ hγΛ i)).smul (conj_logW_zero R)).add
    (pieceSharp_D (R := R) hm hγ hγΛ hMf i)).add hKs).neg
  have hP := (((((piecePauli_G (R := R) hm hγ hγΛ i).add hZK).smul (logW R 0)).add
    (piecePauli_D (R := R) hm hγ hγΛ hMf i)).add hKp).neg
  exact ⟨pieceB R i K, _, fun p' p hpq => isClassLimC_inl hA hpq (hKl p' p hpq), hC, hS, hP⟩

theorem setCClassLim_inl {i : Fin 12} (hK : MainBKKLinkP P₀ i) :
    SetCClassLim mainFam P₀ (.inl i) :=
  setCClassLim_inl_of_kk (mainBKKLink_of_P hK)

/-- **The covariance link of `repB i`** from the strengthened kk link. -/
theorem setCClassCov_inl {i : Fin 12} (hK : MainBKKLinkP P₀ i) :
    SetCClassCov mainFam P₀ (.inl i) :=
  setCClassCov_of_piece (isPieceClass_inl hK)

/-- **The canonical Pauli link of `repB i`** from the strengthened kk link, with the value
`clsPauliLim mainFam P₀ (.inl i)`. -/
theorem setCClassPauli_inl {i : Fin 12} (hK : MainBKKLinkP P₀ i) :
    SetCClassPauli mainFam P₀ (.inl i) (clsPauliLim mainFam P₀ (.inl i)) :=
  setCClassPauli_of_piece (isPieceClass_inl hK)

/-- **The `♯`-law of `repB i`** from the strengthened kk link. -/
theorem setCClassSharp_inl {i : Fin 12} (hK : MainBKKLinkP P₀ i) :
    SetCClassSharp mainFam P₀ (.inl i) :=
  setCClassSharp_of_piece (isPieceClass_inl hK)

/-- **The canonical Pauli value of `repB i`**: `-(c L₀/3 · (Z_G + Z_K) + Z_D + Z) / (64 e m⁵)`,
`Z_G = wD 1 · unitMPauliZeroPow … 1`, `Z_K` the Pauli limit of the longitudinal part (`kZInt`,
`kZExt`), `Z_D = -2c wD 1 ∑_f unitMDispPauliRepB(w_f, M_f)`, `Z` that of the kk limit. -/
theorem clsPauliLim_inl_eq {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ} {i : Fin 12}
    (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) {K : Piece} {Z ZK : ℂ}
    (hKl : ∀ p' p, IsPairQ P₀.m p' p → ∀ μ α β,
      Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
        (kkB { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
          i p p' μ α β)) (𝓝[>] 0) (𝓝 (K p' p μ α β)))
    (hKp : PiecePauli P₀.m K Z)
    (hZK : PiecePauli P₀.m (pieceK (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) i) ZK) :
    clsPauliLim mainFam P₀ (.inl i) M₁ M₂ c₁ c₂ mγ Λ D s =
      -(logW (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) 0 *
          (wD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) 1 * unitMPauliZeroPow (repBClass i)
            (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (repBSlot i) ![1, 1]
            (dkMasses (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)) 1 + ZK) +
        (-2 * vpCst (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) * wD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) 1) *
          ∑ f, unitMDispPauliRepB (repBClass i) (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (repBSlot i)
            (dispWt (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) f)
            ((regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).mass f) mγ Λ + Z) /
        (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5) := by
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  have hMf := setCAdm_mass hA
  exact clsPauliLim_of_piece hm (fun p' p hpq => isClassLimC_inl hA hpq (hKl p' p hpq))
    (((((piecePauli_G (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ i).add hZK).smul _).add
      (piecePauli_D (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ hMf i)).add hKp).neg

end QED.ChainProof.SetCMainB

namespace QED.ThreeLoop

open QED.ChainProof.SetCPauli (mainFam clsPauliLim SetCRegLimitB setCPauliB)
open QED.ChainProof.SetCMain (setCBetaM)
open QED.ChainProof.SetCMainB (MainBKKLinkP setCClassLim_inl setCClassCov_inl
  setCClassPauli_inl setCClassSharp_inl)

/-- **(HS₆) from the strengthened kk links of the twelve `repB` classes** and the regulator
limit of `b = setCPauliB P₀ (setCBetaM P₀ βᴮ)`, `βᴮ i = clsPauliLim mainFam P₀ (.inl i)`. -/
theorem isFormFactorPair_vertexSetC_pauli_limit_of_kkLinkP (P₀ : Params)
    (hK : ∀ i, MainBKKLinkP P₀ i)
    (hreg : SetCRegLimitB P₀
      (setCPauliB P₀ (setCBetaM P₀ fun i => clsPauliLim mainFam P₀ (.inl i))))
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
  isFormFactorPair_vertexSetC_pauli_limit_of_repB P₀ (fun i => setCClassLim_inl (hK i))
    (fun i => setCClassCov_inl (hK i)) (fun i => setCClassPauli_inl (hK i))
    (fun i => setCClassSharp_inl (hK i)) hreg he hm η hη

end QED.ThreeLoop

end
