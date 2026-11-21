/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkShareTree
public import QED.Frozen.Graded.IsRenormalizedThrough

/-!
# Set (c), model link: the VP share from its analytic inputs

Helper for (G-ex-s) `QED.ThreeLoop.existsUnique_isVPShareOnShell` and (WI-s)
`QED.ThreeLoop.isVPShareOnShell_d₁_eq_d₂` (decision D-58), the algebraic half, as
`QED.GradedProof.GEx2.existsUnique_withLevel_one_of_inputs` and `WI2.d₁_eq_d₂_one'` are for
(G-ex₂) and (WI₂). With `D₀ = D.withLevel 1 0 (D.d₃ 1)` and `M` the open-line mass:

* `isOnShellSelAt_two_iff`: if the selected order-`4` self-energy of `D₀` has the covariant limit
  `A₀ p̸ + B₀ M` near the shell (`SELimitSel`) with real shell value `σ₀` and slope `σ₁`, the
  family on-shell condition of (Sc₂) at the share `s` is `e⁴ s₂ = σ₁ ∧ e⁴ s_m M = σ₀ + σ₁ M`;
* `isChargeNormalizedSelAt_two_iff`: if the selected order-`5` vertex of `D₀` tends to `c γ^μ`
  between on-shell spinors at `q = 0` (`VLimitSel`), the family charge condition is
  `c + e⁵ s₁ = 0`;
* **`existsUnique_isVPShareOnShell_of_inputs`**: the two inputs give (G-ex-s);
* **`isVPShareOnShell_d₁_eq_d₂_of_inputs`**: with the family Ward identity `c = -e σ₁` as a
  third input (`VPWardInput`), (WI-s).

The inputs are the restrictions to the vacuum-polarization classes (`V`, `P0`, `P1` of the
self-energy; `VP`, `d3Slot0`, `d3Slot1` of the vertex) of the Stage 2 inputs `GEx2.SEReal`,
`GEx2.VertexZeroInput` and `WI2.charge_eq_neg_e_mul_slope`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.ChainProof.SetCLink

open QED.Graded QED.GradedProof
open QED.WickModel (Params)

/-- The open-line data with the level-`1` fermion counterterms removed. -/
def dZero {F : Type} (D : Counterterms F) : Counterterms F :=
  D.withLevel 1 (fun _ => (0, 0, 0)) (D.d₃ 1)

/-- The limit property of (Gs₂) for the selected order-`4` self-energy on the region of radius
`r`. -/
def SELimitSel (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (r : ℝ) (A B : ℝ → ℂ) : Prop :=
  ∀ p : Fin 4 → ℝ, -(Φ.mass Φ.openLine + r) ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
    Tendsto (fun ε : ℝ => selfEnergySelPart { P with ε := ε } Φ D selSE Φ.openLine 2 p α β)
      (𝓝[>] 0) (𝓝 ((A (Minkowski.dot p p) • Dirac.slash p
        + (B (Minkowski.dot p p) * Φ.mass Φ.openLine) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))

/-- The `q = 0` limit `c γ^μ` of the selected order-`5` vertex between on-shell spinors. -/
def VLimitSel (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (c : ℝ) : Prop :=
  ∀ p : Fin 4 → ℝ, Minkowski.dot p p = -Φ.mass Φ.openLine ^ 2 → 0 < p 0 → ∀ (μ : Fin 4)
    (u w : Fin 4 → ℂ), Dirac.slash p *ᵥ u = -((Φ.mass Φ.openLine : ℂ) • u) →
    w ᵥ* Dirac.slash p = -((Φ.mass Φ.openLine : ℂ) • w) →
    Tendsto (fun ε : ℝ => w ⬝ᵥ (familyVertex { P with ε := ε } Φ D selV 5 p p μ *ᵥ u))
      (𝓝[>] 0) (𝓝 ((c : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u))))

/-- **Input (I1)**: the selected order-`4` self-energy of `D` has a covariant limit near the
shell with real shell value and slope. -/
def VPSEInput (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) : Prop :=
  ∃ r > 0, ∃ A B : ℝ → ℂ, SELimitSel P Φ D r A B ∧ ∃ σ₀ σ₁ : ℝ,
    A (-Φ.mass Φ.openLine ^ 2) * ((-Φ.mass Φ.openLine : ℝ) : ℂ) +
      B (-Φ.mass Φ.openLine ^ 2) * Φ.mass Φ.openLine = σ₀ ∧
    HasDerivAt (GEx2.shellFun A B (Φ.mass Φ.openLine)) σ₁ (-Φ.mass Φ.openLine)

/-- **Input (I2)**: the selected order-`5` vertex of `D` at `q = 0` is `c γ^μ`, `c` real. -/
def VPVInput (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) : Prop :=
  ∃ c : ℝ, VLimitSel P Φ D c

/-- **Input (I3)**: the family Ward identity, the vertex charge is `-e` times the shell slope. -/
def VPWardInput (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) : Prop :=
  ∀ r > 0, ∀ A B : ℝ → ℂ, SELimitSel P Φ D r A B → ∀ σ₁ : ℝ,
    HasDerivAt (GEx2.shellFun A B (Φ.mass Φ.openLine)) σ₁ (-Φ.mass Φ.openLine) →
    ∀ c : ℝ, VLimitSel P Φ D c → c = -(P.e * σ₁)

/-- **The family on-shell conditions as two affine equations.** -/
theorem isOnShellSelAt_two_iff (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D₀ : Counterterms F) (h₁ : ∀ g, D.d₁ g 0 = D₀.d₁ g 0)
    (h₂ : ∀ g, D.d₂ g 0 = D₀.d₂ g 0) (hm : ∀ g, D.dm g 0 = D₀.dm g 0) (h₃ : D.d₃ 0 = D₀.d₃ 0)
    (h0₂ : D₀.d₂ Φ.openLine 1 = 0) (h0m : D₀.dm Φ.openLine 1 = 0) (hM : 0 < Φ.mass Φ.openLine)
    {r₀ : ℝ} (hr₀ : 0 < r₀) {A₀ B₀ : ℝ → ℂ} (hlim₀ : SELimitSel P Φ D₀ r₀ A₀ B₀) {σ₀ σ₁ : ℝ}
    (hσ₀ : A₀ (-Φ.mass Φ.openLine ^ 2) * ((-Φ.mass Φ.openLine : ℝ) : ℂ) +
      B₀ (-Φ.mass Φ.openLine ^ 2) * Φ.mass Φ.openLine = σ₀)
    (hσ₁ : HasDerivAt (GEx2.shellFun A₀ B₀ (Φ.mass Φ.openLine)) σ₁ (-Φ.mass Φ.openLine)) :
    IsOnShellSelAt P Φ D selSE Φ.openLine 2 ↔
      (P.e ^ 4 * D.d₂ Φ.openLine 1 = σ₁ ∧
        P.e ^ 4 * D.dm Φ.openLine 1 * Φ.mass Φ.openLine = σ₀ + σ₁ * Φ.mass Φ.openLine) := by
  set f := Φ.openLine with hf
  set M := Φ.mass f with hMdef
  set a : ℝ := P.e ^ 4 * D.d₂ f 1 with ha
  set b : ℝ := P.e ^ 4 * D.dm f 1 with hb
  set A₁ : ℝ → ℂ := fun s => A₀ s - a
  set B₁ : ℝ → ℂ := fun s => B₀ s - b
  have hSig : ∀ ε p α β, selfEnergySelPart { P with ε := ε } Φ D selSE f 2 p α β =
      selfEnergySelPart { P with ε := ε } Φ D₀ selSE f 2 p α β -
        ((a : ℂ) • Dirac.slash p + ((b * M : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β := by
    intro ε p α β
    have h := selfEnergySelPart_two_sub { P with ε := ε } Φ D D₀ h₁ h₂ hm h₃ f p α β
    simp only [GEx2.seTree, h0₂, h0m, mul_zero, zero_mul, Complex.ofReal_zero, zero_smul,
      add_zero, Matrix.zero_apply] at h
    rw [← h]
    simp only [a, b, M]
    ring
  have hlim₁ : SELimitSel P Φ D r₀ A₁ B₁ := by
    intro p hp α β
    have h := (hlim₀ p hp α β).sub (tendsto_const_nhds (x :=
      ((a : ℂ) • Dirac.slash p + ((b * M : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))
    have h' := h.congr fun ε => (hSig ε p α β).symm
    convert h' using 2
    simp only [A₁, B₁, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hS : GEx2.shellFun A₁ B₁ M =
      fun z => GEx2.shellFun A₀ B₀ M z - ((a : ℂ) * z + (b * M : ℝ)) := by
    funext z
    simp only [GEx2.shellFun, A₁, B₁]
    push_cast
    ring
  have hd₁ : HasDerivAt (GEx2.shellFun A₁ B₁ M) ((σ₁ : ℂ) - a) (-M) := by
    rw [hS]
    refine hσ₁.sub ?_
    simpa using ((hasDerivAt_id (-M)).ofReal_comp.const_mul (a : ℂ)).add_const
      (((b * M : ℝ) : ℂ))
  have hcond : (A₁ (-M ^ 2) * ((-M : ℝ) : ℂ) + B₁ (-M ^ 2) * M = 0 ∧
      HasDerivAt (GEx2.shellFun A₁ B₁ M) 0 (-M)) ↔ (a = σ₁ ∧ b * M = σ₀ + σ₁ * M) := by
    have hv : A₁ (-M ^ 2) * ((-M : ℝ) : ℂ) + B₁ (-M ^ 2) * M =
        ((σ₀ + a * M - b * M : ℝ) : ℂ) := by
      simp only [A₁, B₁]
      push_cast
      rw [← hσ₀]
      push_cast
      ring
    rw [hv]
    constructor
    · rintro ⟨h0, hd⟩
      have h1 : (σ₁ : ℂ) - a = 0 := hd₁.unique hd
      have h1' : a = σ₁ := by
        have : ((σ₁ - a : ℝ) : ℂ) = 0 := by push_cast; exact h1
        have := Complex.ofReal_eq_zero.1 this
        linarith
      have h0' : σ₀ + a * M - b * M = 0 := by exact_mod_cast h0
      refine ⟨h1', ?_⟩
      rw [← h1']
      linarith
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have : σ₀ + a * M - b * M = 0 := by rw [h1]; linarith
        rw [this]
        simp
      · convert hd₁ using 1
        rw [h1, sub_self]
  constructor
  · rintro ⟨r, hr, A, B, hlim, hval, hder⟩
    have hev := eventuallyEq_of_tendsto hM hr hr₀ hlim hlim₁
    exact hcond.1 ((onShell_congr hev).1 ⟨hval, hder⟩)
  · intro h
    exact ⟨r₀, hr₀, A₁, B₁, hlim₁, hcond.2 h⟩

/-- **The family charge condition as one affine equation.** -/
theorem isChargeNormalizedSelAt_two_iff (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D₀ : Counterterms F) (h₁ : ∀ g, D.d₁ g 0 = D₀.d₁ g 0)
    (h₂ : ∀ g, D.d₂ g 0 = D₀.d₂ g 0) (hm : ∀ g, D.dm g 0 = D₀.dm g 0) (h₃ : D.d₃ 0 = D₀.d₃ 0)
    (h0 : D₀.d₁ Φ.openLine 1 = 0) (hM : 0 < Φ.mass Φ.openLine) {c : ℝ}
    (hc : VLimitSel P Φ D₀ c) :
    IsChargeNormalizedSelAt P Φ D selV Φ.openLine 2 ↔ c + P.e ^ 5 * D.d₁ Φ.openLine 1 = 0 := by
  set f := Φ.openLine with hf
  have hΦ : ({ Φ with openLine := f } : Lepton.Flavors F) = Φ := rfl
  have hlim : VLimitSel P Φ D (c + P.e ^ 5 * D.d₁ f 1) := by
    intro p hp hp0 μ u w hu hw
    have h := (hc p hp hp0 μ u w hu hw).add (tendsto_const_nhds (x :=
      ((P.e ^ 5 * D.d₁ f 1 : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u))))
    have h' : Tendsto (fun ε : ℝ => w ⬝ᵥ (familyVertex { P with ε := ε } Φ D₀ selV 5 p p μ *ᵥ u) +
        ((P.e ^ 5 * D.d₁ f 1 : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u))) (𝓝[>] 0)
        (𝓝 (((c + P.e ^ 5 * D.d₁ f 1 : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)))) := by
      convert h using 2
      push_cast
      ring
    refine h'.congr fun ε => ?_
    rw [familyVertex_five_sub { P with ε := ε } Φ D D₀ (h₁ f) (h₂ f) (hm f) h₃ h₁ h₂ hm, h0,
      Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    push_cast
    ring
  unfold IsChargeNormalizedSelAt
  rw [hΦ, show 2 * 2 + 1 = 5 from rfl]
  constructor
  · intro h
    set pr : Fin 4 → ℝ := Pi.single 0 (Φ.mass f)
    have hpr : Minkowski.dot pr pr = -Φ.mass f ^ 2 := by simp [pr, Minkowski.dot_eq]; ring
    have hpr0 : 0 < pr 0 := by simp [pr, hM]
    obtain ⟨u, w, hu, hw, hne⟩ :=
      QED.OneLoop.VertexLimit.exists_sandwich_gamma_zero_ne_zero hM hpr hpr0
    have := tendsto_nhds_unique (hlim pr hpr hpr0 0 u w hu hw) (h pr hpr hpr0 0 u w hu hw)
    exact_mod_cast (mul_eq_zero.1 this).resolve_right hne
  · intro h p hp hp0 μ u w hu hw
    simpa [h] using hlim p hp hp0 μ u w hu hw

/-- The level-`0` and level-`1` entries of `D.withLevel 1 (fun _ => s) y`. -/
theorem withLevel_one_entries {F : Type} (D : Counterterms F) (s : ℝ × ℝ × ℝ) (y : ℝ) :
    (∀ g, (D.withLevel 1 (fun _ => s) y).d₁ g 0 = (dZero D).d₁ g 0) ∧
    (∀ g, (D.withLevel 1 (fun _ => s) y).d₂ g 0 = (dZero D).d₂ g 0) ∧
    (∀ g, (D.withLevel 1 (fun _ => s) y).dm g 0 = (dZero D).dm g 0) ∧
    (D.withLevel 1 (fun _ => s) y).d₃ 0 = (dZero D).d₃ 0 ∧
    (∀ g, (D.withLevel 1 (fun _ => s) y).d₁ g 1 = s.1) ∧
    (∀ g, (D.withLevel 1 (fun _ => s) y).d₂ g 1 = s.2.1) ∧
    (∀ g, (D.withLevel 1 (fun _ => s) y).dm g 1 = s.2.2) ∧
    (∀ g, (dZero D).d₁ g 1 = 0 ∧ (dZero D).d₂ g 1 = 0 ∧ (dZero D).dm g 1 = 0) := by
  simp [Counterterms.withLevel, dZero]

/-- **(Sc₂) as three affine equations**, from the inputs (I1), (I2) at `dZero D`. -/
theorem isVPShareOnShell_iff (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (hM : 0 < Φ.mass Φ.openLine) {r₀ : ℝ}
    (hr₀ : 0 < r₀) {A₀ B₀ : ℝ → ℂ} (hlim₀ : SELimitSel P Φ (dZero D) r₀ A₀ B₀) {σ₀ σ₁ : ℝ}
    (hσ₀ : A₀ (-Φ.mass Φ.openLine ^ 2) * ((-Φ.mass Φ.openLine : ℝ) : ℂ) +
      B₀ (-Φ.mass Φ.openLine ^ 2) * Φ.mass Φ.openLine = σ₀)
    (hσ₁ : HasDerivAt (GEx2.shellFun A₀ B₀ (Φ.mass Φ.openLine)) σ₁ (-Φ.mass Φ.openLine))
    {c : ℝ} (hc : VLimitSel P Φ (dZero D) c) (s : ℝ × ℝ × ℝ) :
    ThreeLoop.IsVPShareOnShell P Φ D s ↔
      ((P.e ^ 4 * s.2.1 = σ₁ ∧
        P.e ^ 4 * s.2.2 * Φ.mass Φ.openLine = σ₀ + σ₁ * Φ.mass Φ.openLine) ∧
        c + P.e ^ 5 * s.1 = 0) := by
  obtain ⟨l1, l2, lm, l3, v1, v2, vm, z⟩ := withLevel_one_entries D s (D.d₃ 1)
  have eS := isOnShellSelAt_two_iff P Φ (D.withLevel 1 (fun _ => s) (D.d₃ 1)) (dZero D) l1 l2 lm
    l3 (z _).2.1 (z _).2.2 hM hr₀ hlim₀ hσ₀ hσ₁
  have eV := isChargeNormalizedSelAt_two_iff P Φ (D.withLevel 1 (fun _ => s) (D.d₃ 1))
    (dZero D) l1 l2 lm l3 (z _).1 hM hc
  rw [v2, vm] at eS
  rw [v1] at eV
  exact and_congr eS eV

/-- **(G-ex-s) from the inputs (I1), (I2).** -/
theorem existsUnique_isVPShareOnShell_of_inputs (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (he : P.e ≠ 0)
    (hM : 0 < Φ.mass Φ.openLine) (hSE : VPSEInput P Φ (dZero D)) (hV : VPVInput P Φ (dZero D)) :
    ∃! s : ℝ × ℝ × ℝ, ThreeLoop.IsVPShareOnShell P Φ D s := by
  obtain ⟨r, hr, A, B, hlim, σ₀, σ₁, hσ₀, hσ₁⟩ := hSE
  obtain ⟨c, hc⟩ := hV
  have hiff := isVPShareOnShell_iff P Φ D hM hr hlim hσ₀ hσ₁ hc
  have he4 : P.e ^ 4 ≠ 0 := pow_ne_zero _ he
  have he5 : P.e ^ 5 ≠ 0 := pow_ne_zero _ he
  have hM0 := hM.ne'
  refine ⟨(-c / P.e ^ 5, σ₁ / P.e ^ 4,
    (σ₀ + σ₁ * Φ.mass Φ.openLine) / (P.e ^ 4 * Φ.mass Φ.openLine)), ?_, ?_⟩
  · refine (hiff _).2 ⟨⟨?_, ?_⟩, ?_⟩
    · field_simp
    · field_simp
    · field_simp
      ring
  · rintro ⟨s₁, s₂, s₃⟩ hs
    obtain ⟨⟨e2, e3⟩, e1⟩ := (hiff _).1 hs
    simp only at e1 e2 e3
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> field_simp <;> linarith

/-- **(WI-s) from the inputs (I1), (I2), (I3).** -/
theorem isVPShareOnShell_d₁_eq_d₂_of_inputs (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (he : P.e ≠ 0)
    (hM : 0 < Φ.mass Φ.openLine) (hSE : VPSEInput P Φ (dZero D)) (hV : VPVInput P Φ (dZero D))
    (hW : VPWardInput P Φ (dZero D)) (s : ℝ × ℝ × ℝ) (hs : ThreeLoop.IsVPShareOnShell P Φ D s) :
    s.1 = s.2.1 := by
  obtain ⟨r, hr, A, B, hlim, σ₀, σ₁, hσ₀, hσ₁⟩ := hSE
  obtain ⟨c, hc⟩ := hV
  obtain ⟨⟨e2, -⟩, e1⟩ := (isVPShareOnShell_iff P Φ D hM hr hlim hσ₀ hσ₁ hc s).1 hs
  have hcw := hW r hr A B hlim σ₁ hσ₁ c hc
  have h5 : P.e ^ 5 * (s.1 - s.2.1) = 0 := by
    rw [hcw, ← e2] at e1
    linear_combination e1
  exact sub_eq_zero.1 ((mul_eq_zero.1 h5).resolve_left (pow_ne_zero 5 he))

end QED.ChainProof.SetCLink

end
