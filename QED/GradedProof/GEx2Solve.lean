/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.GEx2Affine
public import QED.Frozen.Graded.IsOnShellAt
public import QED.Frozen.Graded.IsChargeNormalizedAt
public import QED.Frozen.Graded.IsPhotonOnShellAt
public import QED.OneLoop.ChargeRenormalization
public import QED.LeptonProof.HMPhoton

/-!
# The order-`e⁴` conditions as affine equations in the level-`1` data

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57). Let `D₀` agree with `D` at level `0` and have zero level-`1` data on the relevant
flavour (respectively photon). Given the limits of the order-`e⁴` (order-`e⁵`) parts of `D₀`
with **real** on-shell values, each condition of (G₁₂) at order `4` is one affine equation in the
level-`1` data of `D`, with coefficient `e⁴` (`e⁵`):

* `isOnShellAt_two_iff`: (G₉) at `n = 2` iff `e⁴ d₂ f 1 = σ₁` and `e⁴ d_m f 1 M_f = σ₀ + σ₁ M_f`,
  with `σ₀ = Σ₀(-M_f)`, `σ₁ = Σ₀'(-M_f)` for the order-`4` self-energy `Σ₀` of `D₀`;
* `isPhotonOnShellAt_two_iff`: (G₁₁) at `n = 2` iff `e⁴ d₃ 1 = -π₀`, where `π₀ k^μ k^ν` is the
  limit of the order-`4` vacuum polarization of `D₀` at lightlike `k`;
* `isChargeNormalizedAt_two_iff`: (G₁₀) at `n = 2` iff `c + e⁵ d₁ f 1 = 0`, where `c w γ^μ u` is
  the limit of the sandwiched order-`5` vertex of `D₀` at `q = 0`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.GEx2

open QED.Graded
open QED.WickModel (Params)

/-! ### The self-energy -/

/-- The on-shell function `Σ(z) = A(-z²) z + B(-z²) M` of (Z₄). -/
noncomputable def shellFun (A B : ℝ → ℂ) (M : ℝ) (z : ℝ) : ℂ :=
  A (-z ^ 2) * (z : ℂ) + B (-z ^ 2) * M

/-- The limit property of (G₉) for the order-`4` self-energy on the region of radius `r`. -/
def SELimit (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (f : F) (r : ℝ) (A B : ℝ → ℂ) : Prop :=
  ∀ p : Fin 4 → ℝ, -(Φ.mass f + r) ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
    Tendsto (fun ε : ℝ => selfEnergyPart { P with ε := ε } Φ D f 2 p α β) (𝓝[>] 0)
      (𝓝 ((A (Minkowski.dot p p) • Dirac.slash p
        + (B (Minkowski.dot p p) * Φ.mass f) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))

theorem isOnShellAt_two_iff_exists (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) :
    IsOnShellAt P Φ D f 2 ↔ ∃ r > 0, ∃ A B : ℝ → ℂ, SELimit P Φ D f r A B ∧
      A (-Φ.mass f ^ 2) * ((-Φ.mass f : ℝ) : ℂ) + B (-Φ.mass f ^ 2) * Φ.mass f = 0 ∧
      HasDerivAt (shellFun A B (Φ.mass f)) 0 (-Φ.mass f) := Iff.rfl

/-- **The order-`4` on-shell conditions of flavour `f` as two affine equations.** -/
theorem isOnShellAt_two_iff (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D₀ : Counterterms F) (f : F) (h₁ : ∀ g, D.d₁ g 0 = D₀.d₁ g 0)
    (h₂ : ∀ g, D.d₂ g 0 = D₀.d₂ g 0) (hm : ∀ g, D.dm g 0 = D₀.dm g 0) (h₃ : D.d₃ 0 = D₀.d₃ 0)
    (h0₂ : D₀.d₂ f 1 = 0) (h0m : D₀.dm f 1 = 0) (hM : 0 < Φ.mass f) {r₀ : ℝ} (hr₀ : 0 < r₀)
    {A₀ B₀ : ℝ → ℂ} (hlim₀ : SELimit P Φ D₀ f r₀ A₀ B₀) {σ₀ σ₁ : ℝ}
    (hσ₀ : A₀ (-Φ.mass f ^ 2) * ((-Φ.mass f : ℝ) : ℂ) + B₀ (-Φ.mass f ^ 2) * Φ.mass f = σ₀)
    (hσ₁ : HasDerivAt (shellFun A₀ B₀ (Φ.mass f)) σ₁ (-Φ.mass f)) :
    IsOnShellAt P Φ D f 2 ↔
      (P.e ^ 4 * D.d₂ f 1 = σ₁ ∧ P.e ^ 4 * D.dm f 1 * Φ.mass f = σ₀ + σ₁ * Φ.mass f) := by
  set M := Φ.mass f with hMdef
  set a : ℝ := P.e ^ 4 * D.d₂ f 1 with ha
  set b : ℝ := P.e ^ 4 * D.dm f 1 with hb
  set A₁ : ℝ → ℂ := fun s => A₀ s - a
  set B₁ : ℝ → ℂ := fun s => B₀ s - b
  have hSig : ∀ ε p α β, selfEnergyPart { P with ε := ε } Φ D f 2 p α β =
      selfEnergyPart { P with ε := ε } Φ D₀ f 2 p α β -
        ((a : ℂ) • Dirac.slash p + ((b * M : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β := by
    intro ε p α β
    have h := selfEnergyPart_two_add_tree { P with ε := ε } Φ D D₀ h₁ h₂ hm h₃ f p α β
    simp only [seTree, h0₂, h0m, mul_zero, zero_mul, Complex.ofReal_zero, zero_smul,
      add_zero, Matrix.zero_apply] at h
    rw [← h]
    simp only [a, b, M]
    ring
  have hlim₁ : SELimit P Φ D f r₀ A₁ B₁ := by
    intro p hp α β
    have h := (hlim₀ p hp α β).sub (tendsto_const_nhds (x :=
      ((a : ℂ) • Dirac.slash p + ((b * M : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))
    simp only [← hSig] at h
    convert h using 2
    simp only [A₁, B₁, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hS : shellFun A₁ B₁ M = fun z => shellFun A₀ B₀ M z - ((a : ℂ) * z + (b * M : ℝ)) := by
    funext z
    simp only [shellFun, A₁, B₁]
    push_cast
    ring
  have hd₁ : HasDerivAt (shellFun A₁ B₁ M) ((σ₁ : ℂ) - a) (-M) := by
    rw [hS]
    refine hσ₁.sub ?_
    simpa using ((hasDerivAt_id (-M)).ofReal_comp.const_mul (a : ℂ)).add_const
      (((b * M : ℝ) : ℂ))
  have hcond : (A₁ (-M ^ 2) * ((-M : ℝ) : ℂ) + B₁ (-M ^ 2) * M = 0 ∧
      HasDerivAt (shellFun A₁ B₁ M) 0 (-M)) ↔ (a = σ₁ ∧ b * M = σ₀ + σ₁ * M) := by
    have hv : A₁ (-M ^ 2) * ((-M : ℝ) : ℂ) + B₁ (-M ^ 2) * M = ((σ₀ + a * M - b * M : ℝ) : ℂ) := by
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
  rw [isOnShellAt_two_iff_exists]
  constructor
  · rintro ⟨r, hr, A, B, hlim, hval, hder⟩
    have hev := eventuallyEq_of_tendsto hM hr hr₀ hlim hlim₁
    exact hcond.1 ((onShell_congr hev).1 ⟨hval, hder⟩)
  · intro h
    exact ⟨r₀, hr₀, A₁, B₁, hlim₁, hcond.2 h⟩

/-! ### The vacuum polarization -/

/-- **The order-`4` photon condition as one affine equation.** -/
theorem isPhotonOnShellAt_two_iff (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D₀ : Counterterms F) (h₁ : ∀ g, D.d₁ g 0 = D₀.d₁ g 0)
    (h₂ : ∀ g, D.d₂ g 0 = D₀.d₂ g 0) (hm : ∀ g, D.dm g 0 = D₀.dm g 0) (h₃ : D.d₃ 0 = D₀.d₃ 0)
    (h0 : D₀.d₃ 1 = 0) {π₀ : ℝ}
    (hπ : ∀ k : Fin 4 → ℝ, Minkowski.dot k k = 0 → ∀ μ ν : Fin 4,
      Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D₀ 2 k μ ν) (𝓝[>] 0)
        (𝓝 ((π₀ * (k μ * k ν) : ℝ) : ℂ))) :
    IsPhotonOnShellAt P Φ D 2 ↔ P.e ^ 4 * D.d₃ 1 = -π₀ := by
  have hlim : ∀ k : Fin 4 → ℝ, Minkowski.dot k k = 0 → ∀ μ ν : Fin 4,
      Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D 2 k μ ν) (𝓝[>] 0)
        (𝓝 (((π₀ + P.e ^ 4 * D.d₃ 1) * (k μ * k ν) : ℝ) : ℂ)) := by
    intro k hk μ ν
    have h := (hπ k hk μ ν).add (tendsto_const_nhds (x :=
      ((P.e ^ 4 * D.d₃ 1 * (k μ * k ν) : ℝ) : ℂ)))
    have h' : Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D₀ 2 k μ ν +
        ((P.e ^ 4 * D.d₃ 1 * (k μ * k ν) : ℝ) : ℂ)) (𝓝[>] 0)
        (𝓝 (((π₀ + P.e ^ 4 * D.d₃ 1) * (k μ * k ν) : ℝ) : ℂ)) := by
      convert h using 2
      push_cast
      ring
    refine h'.congr fun ε => ?_
    have h' := vacuumPolarizationPart_two_add_tree { P with ε := ε } Φ D D₀ h₁ h₂ hm h₃ k μ ν
    simp only [h0, vpT, hk, mul_zero, zero_mul, Complex.ofReal_zero, add_zero] at h'
    rw [← h']
    push_cast
    ring
  constructor
  · intro h
    have hk := QED.Lepton.Proof.HM.dot_lightlike
    have := tendsto_nhds_unique (hlim _ hk 0 0) (h _ hk 0 0)
    have h1 : (π₀ + P.e ^ 4 * D.d₃ 1) * (1 * 1) = 0 := by
      have := Complex.ofReal_eq_zero.1 this
      simpa using this
    linarith
  · intro h k hk μ ν
    have h1 : π₀ + P.e ^ 4 * D.d₃ 1 = 0 := by linarith
    simpa [h1] using hlim k hk μ ν

/-! ### The vertex -/

/-- **The order-`5` charge condition of flavour `f` as one affine equation.** -/
theorem isChargeNormalizedAt_two_iff (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D₀ : Counterterms F) (f : F) (h₁ : D.d₁ f 0 = D₀.d₁ f 0)
    (h₂ : D.d₂ f 0 = D₀.d₂ f 0) (hm : D.dm f 0 = D₀.dm f 0) (h₃ : D.d₃ 0 = D₀.d₃ 0)
    (h0 : D₀.d₁ f 1 = 0) (hM : 0 < Φ.mass f) {c : ℝ}
    (hc : ∀ p : Fin 4 → ℝ, Minkowski.dot p p = -Φ.mass f ^ 2 → 0 < p 0 → ∀ (μ : Fin 4)
      (u w : Fin 4 → ℂ), Dirac.slash p *ᵥ u = -((Φ.mass f : ℂ) • u) →
      w ᵥ* Dirac.slash p = -((Φ.mass f : ℂ) • w) →
      Tendsto (fun ε : ℝ => w ⬝ᵥ (vertexPart { P with ε := ε } Φ D₀ f 2 p p μ *ᵥ u)) (𝓝[>] 0)
        (𝓝 ((c : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u))))) :
    IsChargeNormalizedAt P Φ D f 2 ↔ c + P.e ^ 5 * D.d₁ f 1 = 0 := by
  have hlim : ∀ p : Fin 4 → ℝ, Minkowski.dot p p = -Φ.mass f ^ 2 → 0 < p 0 → ∀ (μ : Fin 4)
      (u w : Fin 4 → ℂ), Dirac.slash p *ᵥ u = -((Φ.mass f : ℂ) • u) →
      w ᵥ* Dirac.slash p = -((Φ.mass f : ℂ) • w) →
      Tendsto (fun ε : ℝ => w ⬝ᵥ (vertexPart { P with ε := ε } Φ D f 2 p p μ *ᵥ u)) (𝓝[>] 0)
        (𝓝 (((c + P.e ^ 5 * D.d₁ f 1 : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)))) := by
    intro p hp hp0 μ u w hu hw
    have h := (hc p hp hp0 μ u w hu hw).add (tendsto_const_nhds (x :=
      ((P.e ^ 5 * D.d₁ f 1 : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u))))
    have h' : Tendsto (fun ε : ℝ => w ⬝ᵥ (vertexPart { P with ε := ε } Φ D₀ f 2 p p μ *ᵥ u) +
        ((P.e ^ 5 * D.d₁ f 1 : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u))) (𝓝[>] 0)
        (𝓝 (((c + P.e ^ 5 * D.d₁ f 1 : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)))) := by
      convert h using 2
      push_cast
      ring
    refine h'.congr fun ε => ?_
    rw [vertexPart_two_sub { P with ε := ε } Φ D D₀ f h₁ h₂ hm h₃, h0, Matrix.add_mulVec,
      dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    push_cast
    ring
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

end QED.GradedProof.GEx2

end
