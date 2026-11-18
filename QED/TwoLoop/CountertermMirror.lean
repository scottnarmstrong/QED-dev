/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.LimitMirrorVertex
public import QED.TwoLoop.CountertermLimit
public import QED.Integration.EnergyFirstShift

/-!
# Charge conjugation of the counterterm classes

Part of obligation O2-21 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4), for the four counterterm
classes with a two-point counterterm vertex (`QED.TwoLoop.Relabel.CtClass`). Their values are
energy-first integrals of the one-loop vertex chain (`QED.TwoLoop.Insertion.vertexChain`) with an
inserted line (`QED.TwoLoop.Insertion.contractionValue₂_repD2In`, …). With `X ↦ C Xᵀ C`
(`ccT`):

* `C γ^μᵀ C = -γ^μ`, so `C (vertexChain A B D)ᵀ C = -vertexChain (C Bᵀ C) (C Aᵀ C) Dᵀ`
  (`ccT_vertexChain`);
* `C S̃(k)ᵀ C = S̃(-k)` and, for the `fermionCt` vertex `δ₂ k̸ + δ_m m`, whose momentum reverses with
  the line, `C (δ₂ k̸ + δ_m m)ᵀ C = δ₂ (-k)̸ + δ_m m`; hence the inserted electron line satisfies
  `C S̃_ins(k)ᵀ C = S̃_ins(-k)` (`ccT_electronInsertion`);
* the photon line with the `photonCt` insertion is symmetric and even (`photonInsertion_neg_swap`).

After `ℓ ↦ -ℓ` in the energy-first integral, charge conjugation exchanges `δ₂` on the incoming
line with `δ₂` on the outgoing line, and maps each `δ₃` class to itself, at every prescription
`ε` (`isCtChargeConjPair_d2In_d2Out`, `isCtChargeConjPair_d3Slot0`, `isCtChargeConjPair_d3Slot1`).
The limits `ε → 0⁺` at `(p', p)` then determine those at `(-p, -p')`
(`chargeConj_ctLimit_of_pair`); unlike `QED.TwoLoop.LimitMirror.chargeConj_classLimit_of_pair`, the
existence of the limit at `(-p, -p')` (negative energies) is a consequence, not a hypothesis. Given
the covariance of the limits under the reflection `R_K` (`IsReflCovariantAt`), the pair
`δ₂ in + δ₂ out` and each `δ₃` class are mirror symmetric (`isMirrorSymmetric_ctLimit_pair`,
`isMirrorSymmetric_ctLimit_self`).
-/

@[expose] public section

open Matrix Complex Filter Topology

namespace QED.TwoLoop.CountertermMirror

open QED.WickModel QED.TwoLoop.Relabel QED.TwoLoop.Insertion QED.TwoLoop.LimitMirror QED.Dirac
  QED.OneLoop

/-! ### `X ↦ C Xᵀ C` -/

/-- Charge conjugation of a matrix, `X ↦ C Xᵀ C`. -/
def ccT (X : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  chargeConj * Xᵀ * chargeConj

theorem ccT_mul (X Y : Matrix (Fin 4) (Fin 4) ℂ) : ccT (X * Y) = ccT Y * ccT X := by
  simp only [ccT, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc chargeConj chargeConj, chargeConj_mul_self, Matrix.one_mul]

theorem ccT_add (X Y : Matrix (Fin 4) (Fin 4) ℂ) : ccT (X + Y) = ccT X + ccT Y := by
  simp only [ccT, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem ccT_smul (c : ℂ) (X : Matrix (Fin 4) (Fin 4) ℂ) : ccT (c • X) = c • ccT X := by
  simp only [ccT, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem ccT_neg (X : Matrix (Fin 4) (Fin 4) ℂ) : ccT (-X) = -ccT X := by
  simp only [ccT, Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul]

theorem ccT_sub (X Y : Matrix (Fin 4) (Fin 4) ℂ) : ccT (X - Y) = ccT X - ccT Y := by
  simp only [ccT, Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem ccT_one : ccT 1 = 1 := by
  simp only [ccT, Matrix.transpose_one, Matrix.mul_one, chargeConj_mul_self]

theorem ccT_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin 4) (Fin 4) ℂ) :
    ccT (∑ i ∈ s, f i) = ∑ i ∈ s, ccT (f i) := by
  simp only [ccT, Matrix.transpose_sum, Finset.mul_sum, Finset.sum_mul]

theorem ccT_gamma (μ : Fin 4) : ccT (gamma μ) = -gamma μ :=
  chargeConj_mul_transpose_gamma_mul_chargeConj μ

theorem ccT_slash (v : Fin 4 → ℝ) : ccT (slash v) = -slash v :=
  chargeConj_mul_transpose_slash_mul_chargeConj v

/-- Entrywise, `(C Xᵀ C)_{ab} = s(a) s(b) X_{p(b) p(a)}`. -/
theorem ccT_apply (X : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    ccT X a b = ccSign a * ccSign b * X (ccIdx b) (ccIdx a) :=
  chargeConj_transpose_apply X a b

theorem dot_neg_neg (k : Fin 4 → ℝ) : Minkowski.dot (-k) (-k) = Minkowski.dot k k := by
  simp [Minkowski.dot]

/-- `C S̃(k)ᵀ C = S̃(-k)`. -/
theorem ccT_electronPropagator (m ε : ℝ) (k : Fin 4 → ℝ) :
    ccT (electronPropagator m ε k) = electronPropagator m ε (-k) := by
  unfold electronPropagator
  rw [ccT_smul, ccT_sub, ccT_smul, ccT_one, ccT_slash, dot_neg_neg, slash_neg, sub_neg_eq_add]

/-- The `fermionCt` vertex reverses its momentum: `C (δ₂ k̸ + δ_m m)ᵀ C = δ₂ (-k)̸ + δ_m m`. -/
theorem ccT_fermionCtMatrix (δ₂ δm m : ℝ) (k : Fin 4 → ℝ) :
    ccT (fermionCtMatrix δ₂ δm m k) = fermionCtMatrix δ₂ δm m (-k) := by
  unfold fermionCtMatrix
  rw [ccT_add, ccT_smul, ccT_smul, ccT_one, ccT_slash, slash_neg, smul_neg]

/-- The electron line with the `fermionCt` insertion: `C S̃_ins(k)ᵀ C = S̃_ins(-k)`. -/
theorem ccT_electronInsertion (m ε δ₂ δm : ℝ) (k : Fin 4 → ℝ) :
    ccT (electronInsertion m ε δ₂ δm k) = electronInsertion m ε δ₂ δm (-k) := by
  unfold electronInsertion
  rw [ccT_neg, ccT_mul, ccT_mul, ccT_electronPropagator, ccT_fermionCtMatrix, Matrix.mul_assoc]

/-- **Charge conjugation of the vertex chain**:
`C (vertexChain A B D)ᵀ C = -vertexChain (C Bᵀ C) (C Aᵀ C) Dᵀ`. -/
theorem ccT_vertexChain (e : ℝ) (μ : Fin 4) (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (D : Fin 4 → Fin 4 → ℂ) :
    ccT (vertexChain e μ A B D) = -vertexChain e μ (ccT B) (ccT A) (fun ν ρ => D ρ ν) := by
  unfold vertexChain
  rw [ccT_smul, ccT_sum, ← smul_neg, ← Finset.sum_neg_distrib]
  simp_rw [← Finset.sum_neg_distrib]
  conv_rhs => rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [ccT_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [ccT_smul, ccT_mul, ccT_mul, ccT_mul, ccT_mul, ccT_gamma, ccT_gamma, ccT_gamma, ← smul_neg]
  congr 1
  noncomm_ring

/-! ### The photon lines -/

theorem photonPropagator_neg (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    photonPropagator mγ Λ ε (-k) μ ν = photonPropagator mγ Λ ε k μ ν := by
  simp only [photonPropagator, dot_neg_neg]

theorem photonPropagator_comm (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    photonPropagator mγ Λ ε k μ ν = photonPropagator mγ Λ ε k ν μ := by
  simp only [photonPropagator, Minkowski.metric_symm μ ν]

/-- The photon line with the `photonCt` insertion is symmetric and even. -/
theorem photonInsertion_neg_swap (δ₃ mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    photonInsertion δ₃ mγ Λ ε (-k) ρ ν = photonInsertion δ₃ mγ Λ ε k ν ρ := by
  unfold photonInsertion
  simp only [photonPropagator_neg, photonCtFactor_neg]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [photonCtFactor_comm δ₃ k b a, photonPropagator_comm mγ Λ ε k ρ b,
    photonPropagator_comm mγ Λ ε k ν a]
  ring

/-! ### The values at fixed `ε` -/

/-- The values (T₁₀) of the counterterm classes `c` and `c'` are exchanged by charge conjugation:
at every parameter set and prescription `ε`, the value of `c'` at `(-p, -p')` with indices
`(a, b)` is `-s(a) s(b)` times the value of `c` at `(p', p)` with indices `(p(b), p(a))`. -/
def IsCtChargeConjPair (c c' : CtClass) : Prop :=
  ∀ (P : Params) (p' p : Fin 4 → ℝ) (μ a b : Fin 4) (ε : ℝ),
    ctValue c' P (-p) (-p') μ a b ε =
      -(ccSign a * ccSign b) * ctValue c P p' p μ (ccIdx b) (ccIdx a) ε

theorem IsCtChargeConjPair.symm {c c' : CtClass} (h : IsCtChargeConjPair c c') :
    IsCtChargeConjPair c' c := by
  intro P p' p μ a b ε
  have e := h P (-p) (-p') μ (ccIdx b) (ccIdx a) ε
  simp only [neg_neg, ccIdx_ccIdx] at e
  rw [e, ccSign_ccIdx, ccSign_ccIdx]
  linear_combination (-(ctValue c P (-p) (-p') μ a b ε)) *
    (ccSign_mul_self a * ccSign b * ccSign b + ccSign_mul_self b)

theorem hmom_neg (p' p : Fin 4 → ℝ) :
    (fun _ : Fin 1 => -p) 0 = (fun _ : Fin 1 => -p') 0 + (fun _ : Fin 1 => -p - -p') 0 := by
  simp

theorem hmom_pos (p' p : Fin 4 → ℝ) :
    (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
  simp

/-- The integrand of the `δ₂`, `δ_m` class on the incoming line. -/
noncomputable def chainD2In (P : Params) (ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  vertexChain P.e μ (electronPropagator P.m ε (p' + ℓ)) (electronInsertion P.m ε P.δ₂ P.δm (p + ℓ))
    (photonPropagator P.mγ P.Λ ε ℓ)

/-- The integrand of the `δ₂`, `δ_m` class on the outgoing line. -/
noncomputable def chainD2Out (P : Params) (ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  vertexChain P.e μ (electronInsertion P.m ε P.δ₂ P.δm (p' + ℓ)) (electronPropagator P.m ε (p + ℓ))
    (photonPropagator P.mγ P.Λ ε ℓ)

/-- The integrand of the `δ₃` classes. -/
noncomputable def chainD3 (P : Params) (ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  vertexChain P.e μ (electronPropagator P.m ε (p' + ℓ)) (electronPropagator P.m ε (p + ℓ))
    (photonInsertion P.δ₃ P.mγ P.Λ ε ℓ)

theorem ctValue_d2In (P : Params) (p' p : Fin 4 → ℝ) (μ a b : Fin 4) (ε : ℝ) :
    ctValue .d2In P p' p μ a b ε = energyFirstIntegral fun ℓ => chainD2In P ε p' p μ ℓ a b :=
  contractionValue₂_repD2In { P with ε := ε } (hmom_pos p' p) (fun _ => a) (fun _ => b)
    (fun _ => μ)

theorem ctValue_d2Out (P : Params) (p' p : Fin 4 → ℝ) (μ a b : Fin 4) (ε : ℝ) :
    ctValue .d2Out P p' p μ a b ε = energyFirstIntegral fun ℓ => chainD2Out P ε p' p μ ℓ a b :=
  contractionValue₂_repD2Out { P with ε := ε } (hmom_pos p' p) (fun _ => a) (fun _ => b)
    (fun _ => μ)

theorem ctValue_d3Slot0 (P : Params) (p' p : Fin 4 → ℝ) (μ a b : Fin 4) (ε : ℝ) :
    ctValue .d3Slot0 P p' p μ a b ε = energyFirstIntegral fun ℓ => chainD3 P ε p' p μ ℓ a b :=
  contractionValue₂_repD3Slot0 { P with ε := ε } (hmom_pos p' p) (fun _ => a) (fun _ => b)
    (fun _ => μ)

theorem ctValue_d3Slot1 (P : Params) (p' p : Fin 4 → ℝ) (μ a b : Fin 4) (ε : ℝ) :
    ctValue .d3Slot1 P p' p μ a b ε = ctValue .d3Slot0 P p' p μ a b ε :=
  (contractionValue₂_d3Slot0_eq_d3Slot1 { P with ε := ε } (hmom_pos p' p) (fun _ => a)
    (fun _ => b) (fun _ => μ)).symm

theorem chainD2Out_neg (P : Params) (ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    chainD2Out P ε (-p) (-p') μ ℓ = -ccT (chainD2In P ε p' p μ (-ℓ)) := by
  unfold chainD2Out chainD2In
  rw [ccT_vertexChain, neg_neg, ccT_electronInsertion, ccT_electronPropagator]
  have e1 : -(p + -ℓ) = -p + ℓ := by abel
  have e2 : -(p' + -ℓ) = -p' + ℓ := by abel
  have e3 : (fun ν ρ => photonPropagator P.mγ P.Λ ε (-ℓ) ρ ν) = photonPropagator P.mγ P.Λ ε ℓ := by
    funext ν ρ
    exact photonPropagator_neg_swap _ _ _ _ _ _
  rw [e1, e2, e3]

theorem chainD3_neg (P : Params) (ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    chainD3 P ε (-p) (-p') μ ℓ = -ccT (chainD3 P ε p' p μ (-ℓ)) := by
  unfold chainD3
  rw [ccT_vertexChain, neg_neg, ccT_electronPropagator, ccT_electronPropagator]
  have e1 : -(p + -ℓ) = -p + ℓ := by abel
  have e2 : -(p' + -ℓ) = -p' + ℓ := by abel
  have e3 : (fun ν ρ => photonInsertion P.δ₃ P.mγ P.Λ ε (-ℓ) ρ ν) =
      photonInsertion P.δ₃ P.mγ P.Λ ε ℓ := by
    funext ν ρ
    exact photonInsertion_neg_swap _ _ _ _ _ _ _
  rw [e1, e2, e3]

/-- From a pointwise charge-conjugation identity of the integrands to the values. -/
theorem energyFirstIntegral_of_neg_ccT {F G : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    (h : ∀ ℓ, G ℓ = -ccT (F (-ℓ))) (a b : Fin 4) :
    energyFirstIntegral (fun ℓ => G ℓ a b) =
      -(ccSign a * ccSign b) * energyFirstIntegral (fun ℓ => F ℓ (ccIdx b) (ccIdx a)) := by
  calc energyFirstIntegral (fun ℓ => G ℓ a b)
      = energyFirstIntegral (fun ℓ => -(ccSign a * ccSign b) * F (-ℓ) (ccIdx b) (ccIdx a)) := by
        congr 1
        funext ℓ
        rw [h ℓ, Matrix.neg_apply, ccT_apply]
        ring
    _ = energyFirstIntegral (fun ℓ => -(ccSign a * ccSign b) * F ℓ (ccIdx b) (ccIdx a)) :=
        energyFirstIntegral_neg_eq_self (fun ℓ => -(ccSign a * ccSign b) * F ℓ (ccIdx b) (ccIdx a))
    _ = _ := energyFirstIntegral_const_mul' _ _

/-- **Charge conjugation exchanges `δ₂` on the incoming and on the outgoing line.** -/
theorem isCtChargeConjPair_d2In_d2Out : IsCtChargeConjPair .d2In .d2Out := by
  intro P p' p μ a b ε
  rw [ctValue_d2Out, ctValue_d2In]
  exact energyFirstIntegral_of_neg_ccT (chainD2Out_neg P ε p' p μ) a b

/-- **Charge conjugation maps the `δ₃` class (slot `0`) to itself.** -/
theorem isCtChargeConjPair_d3Slot0 : IsCtChargeConjPair .d3Slot0 .d3Slot0 := by
  intro P p' p μ a b ε
  rw [ctValue_d3Slot0, ctValue_d3Slot0]
  exact energyFirstIntegral_of_neg_ccT (chainD3_neg P ε p' p μ) a b

/-- **Charge conjugation maps the `δ₃` class (slot `1`) to itself.** -/
theorem isCtChargeConjPair_d3Slot1 : IsCtChargeConjPair .d3Slot1 .d3Slot1 := by
  intro P p' p μ a b ε
  rw [ctValue_d3Slot1, ctValue_d3Slot1]
  exact isCtChargeConjPair_d3Slot0 P p' p μ a b ε

/-! ### The limits -/

/-- The values of a counterterm class converge as `ε → 0⁺` at `(p', p)`, for all indices. -/
def HasCtLimit (c : CtClass) (P : Params) (p' p : Fin 4 → ℝ) : Prop :=
  ∀ μ a b, ∃ L, Tendsto (ctValue c P p' p μ a b) (𝓝[>] 0) (𝓝 L)

theorem tendsto_ctLimit {c : CtClass} {P : Params} {p' p : Fin 4 → ℝ} (h : HasCtLimit c P p' p)
    (μ a b : Fin 4) :
    Tendsto (ctValue c P p' p μ a b) (𝓝[>] 0) (𝓝 (ctLimit c P p' p μ a b)) := by
  obtain ⟨L, hL⟩ := h μ a b
  exact tendsto_nhds_limUnder ⟨L, hL⟩

/-- **Every counterterm class has a limit** at on-shell positive-energy `(p', p)` with `q² ≥ 0`. -/
theorem hasCtLimit (c : CtClass) (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp0 : 0 < p 0) (hp0' : 0 < p' 0) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) :
    HasCtLimit c P p' p := fun μ a b =>
  CountertermLimit.exists_tendsto_contractionValue₂_ctClass c P hm hmγ hΛ
    (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) (hmom_pos p' p) hp hp' hp0
    hp0' hq (fun _ => a) (fun _ => b) (fun _ => μ)

/-- The limit at `(-p, -p')` exists if the one at `(p', p)` does, for a charge-conjugate pair. -/
theorem HasCtLimit.neg {c c' : CtClass} (hcc : IsCtChargeConjPair c c') {P : Params}
    {p' p : Fin 4 → ℝ} (h : HasCtLimit c P p' p) : HasCtLimit c' P (-p) (-p') := fun μ a b => by
  obtain ⟨L, hL⟩ := h μ (ccIdx b) (ccIdx a)
  exact ⟨_, (hL.const_mul (-(ccSign a * ccSign b))).congr fun ε => (hcc P p' p μ a b ε).symm⟩

/-- **Charge conjugation of the counterterm limits**: for a charge-conjugate pair `(c, c')` whose
values converge at `(p', p)`, `C W_c(p', p)ᵀ C = -W_{c'}(-p, -p')`. -/
theorem chargeConj_ctLimit_of_pair {c c' : CtClass} (hcc : IsCtChargeConjPair c c') (P : Params)
    {p' p : Fin 4 → ℝ} (h : HasCtLimit c P p' p) (μ : Fin 4) :
    chargeConj * (ctLimit c P p' p μ)ᵀ * chargeConj = -ctLimit c' P (-p) (-p') μ := by
  ext a b
  rw [chargeConj_transpose_apply, Matrix.neg_apply]
  have hlim := (tendsto_ctLimit h μ (ccIdx b) (ccIdx a)).const_mul (-(ccSign a * ccSign b))
  have e : ctValue c' P (-p) (-p') μ a b = fun ε =>
      -(ccSign a * ccSign b) * ctValue c P p' p μ (ccIdx b) (ccIdx a) ε :=
    funext fun ε => hcc P p' p μ a b ε
  rw [← e] at hlim
  have huniq := tendsto_nhds_unique hlim (tendsto_ctLimit (h.neg hcc) μ a b)
  rw [← huniq]
  ring

/-! ### The mirror identity from covariance -/

section OnShell

variable (P : Params) {m : ℝ} {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
  (hp : Minkowski.dot p p = -m ^ 2) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
include hp' hp hq

/-- **A charge-conjugate pair of counterterm classes is mirror symmetric**, given limits at
`(p', p)` and the covariance of the two limits under the reflection `R_K`. -/
theorem isMirrorSymmetric_ctLimit_pair {c c' : CtClass} (hcc : IsCtChargeConjPair c c')
    (h : HasCtLimit c P p' p) (h' : HasCtLimit c' P p' p)
    (hcov : IsReflCovariantAt (ctLimit c P) p' p) (hcov' : IsReflCovariantAt (ctLimit c' P) p' p) :
    IsMirrorSymmetric p' p (ctLimit c P p' p + ctLimit c' P p' p) := by
  obtain ⟨hRp, hRp', -⟩ := reflect_add_self hp' hp hq
  refine isMirrorSymmetric_of_chargeConj (W' := ctLimit c' P (-p) (-p') +
    ctLimit c P (-p) (-p')) (fun μ => ?_) (fun μ => ?_)
  · rw [Pi.add_apply, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
      chargeConj_ctLimit_of_pair hcc P h μ, chargeConj_ctLimit_of_pair hcc.symm P h' μ,
      Pi.add_apply, neg_add]
  · have h1 := hcov μ
    have h2 := hcov' μ
    rw [hRp, hRp'] at h1 h2
    rw [Pi.add_apply, Matrix.mul_add, Matrix.add_mul, h1, h2, vecAct_add', add_comm]

/-- **A self-conjugate counterterm class is mirror symmetric**, given its limit at `(p', p)` and
the covariance of the limit under the reflection `R_K`. -/
theorem isMirrorSymmetric_ctLimit_self {c : CtClass} (hcc : IsCtChargeConjPair c c)
    (h : HasCtLimit c P p' p) (hcov : IsReflCovariantAt (ctLimit c P) p' p) :
    IsMirrorSymmetric p' p (ctLimit c P p' p) := by
  obtain ⟨hRp, hRp', -⟩ := reflect_add_self hp' hp hq
  refine isMirrorSymmetric_of_chargeConj (W' := ctLimit c P (-p) (-p'))
    (fun μ => chargeConj_ctLimit_of_pair hcc P h μ) (fun μ => ?_)
  have h1 := hcov μ
  rwa [hRp, hRp'] at h1

end OnShell

/-- The two `δ₃` classes have the same limit at every point. -/
theorem ctLimit_d3Slot1 (P : Params) (p' p : Fin 4 → ℝ) :
    ctLimit .d3Slot1 P p' p = ctLimit .d3Slot0 P p' p := by
  funext μ
  ext a b
  simp only [ctLimit, Matrix.of_apply]
  congr 1
  funext ε
  exact ctValue_d3Slot1 P p' p μ a b ε

end QED.TwoLoop.CountertermMirror

end
