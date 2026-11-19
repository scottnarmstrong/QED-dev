/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtGenSpec
public import QED.TwoLoop.VPHalfAtGenFubini
public import QED.TwoLoop.VPHalfAtAssemblyLimit

/-!
# One inserted vacuum polarization on any list of photon-type denominators

Helper level. The assembly of `QED/TwoLoop/VPHalfAtAssembly*.lean` treats the Pauli-projected outer
integrand of the two-loop vacuum-polarization class, the one-loop vertex with photon factor
`P₄(k) (i Π̂_ε(k²) k² + ε S_ε(k²))`, `P₄` with the masses `(m_γ, Λ, m_γ, Λ)`. This file does the
same for **any** list `Ms` of at least four photon-type denominators with prescription `ε`
(`hIntG`), as needed by the bubble–`δ₃` classes of set (b), where one or two extra photon lines
appear.

* `hIntG_eq`: after the integration by parts in the Feynman parameter `x`,
  `hIntG = (i c₁ L_ε/6) k² P_Ms + ε c₂ L_ε P_Ms - ∫₀¹ gIntG x dx`.
* `gIntG_eq`: `gIntG x = ∑_f c_f (u(x) specInt 2 + v_ε(x) specInt 1)` with one spectral insertion
  of flavour mass `M_f` (`QED.TwoLoop.VPHalfAtGen.specInt`).
* `exists_good_gIntG`: one constant for all `ε ∈ (0, 1]` and `x ∈ (0, 1)`.
* `efi_hIntG_eq`: the energy-first integral commutes with `∫₀¹ dx`.
* **`tendsto_efi_hIntG`**: the energy-first integral of `hIntG` tends, as `ε → 0⁺`, to
  `(i c₁ L₀/6) powLimit 1 Ms - ∫₀¹ phiZeroG x dx`, with
  `phiZeroG x = ∑_f c_f u(x) specLimit 2 Ms (M_f, x)`; the `ε S_ε` and `ε`-weighted spectral terms
  vanish.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPHalfAtGen

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.WickModel
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtAssembly
open QED.TwoLoop.VPHalfAt

/-! ### Definitions -/

/-- The photon-type product with all prescriptions `ε`, numerator `pauliChain`. -/
noncomputable def PG (P : Params) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    ℂ :=
  prodIntegrand (pauliChain P.e P.m p' p) P.m Ms (fun _ => ε) ε p' p ℓ

/-- `P_Ms(k) (i Π̂_ε(k²) k² + ε S_ε(k²))`. -/
noncomputable def hIntG (P : Params) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    ℂ :=
  PG P Ms ε p' p ℓ * (I * vpLoopEps P ε (Minkowski.dot ℓ ℓ) * (Minkowski.dot ℓ ℓ : ℂ) +
    (ε : ℂ) * vpExtraEps P ε (Minkowski.dot ℓ ℓ))

/-- The `x`-integrand of `hIntG`. -/
noncomputable def gIntG (P : Params) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (ε : ℝ) (p' p : Fin 4 → ℝ)
    (x : ℝ) (ℓ : Fin 4 → ℝ) : ℂ :=
  PG P Ms ε p' p ℓ * vpRatSum P ε (Minkowski.dot ℓ ℓ) x *
    (I * cOne P * wOne x * (Minkowski.dot ℓ ℓ : ℂ) + (ε : ℂ) * cTwo P * (x : ℂ))

/-- The pointwise limit of the `x`-integrand. -/
noncomputable def phiZeroG (P : Params) (α : ℂ) (p' p : Fin 4 → ℝ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (x : ℝ) : ℂ :=
  ∑ f, (P.loopCoeff f : ℂ) * (uCoef P x *
    specLimit α (pauliChain P.e P.m p' p) P.m p' p 2 1 Ms ![P.mass f] ![x])

theorem powInt_eq_PG (P : Params) (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (ε : ℝ)
    (p' p ℓ : Fin 4 → ℝ) :
    powInt (pauliChain P.e P.m p' p) P.m j Ms (fun _ => ε) ε p' p ℓ =
      ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ j * PG P Ms ε p' p ℓ := rfl

/-! ### The decomposition -/

/-- **The outer integrand split into its constant part and the `x`-integral.** -/
theorem hIntG_eq (P : Params) {k : ℕ} (Ms : Fin (k + 2) → ℝ) {ε : ℝ} (hε : 0 < ε)
    (p' p ℓ : Fin 4 → ℝ) :
    hIntG P Ms ε p' p ℓ =
      (I * cOne P * (1 / 6) * logSum P ε) *
          powInt (pauliChain P.e P.m p' p) P.m 1 Ms (fun _ => ε) ε p' p ℓ +
        ((ε : ℂ) * cTwo P * logSum P ε) *
          powInt (pauliChain P.e P.m p' p) P.m 0 Ms (fun _ => ε) ε p' p ℓ -
        ∫ x in (0 : ℝ)..1, gIntG P Ms ε p' p x ℓ := by
  set s := Minkowski.dot ℓ ℓ
  set Q := PG P Ms ε p' p ℓ
  have i1 : IntervalIntegrable (fun x => vpRatSum P ε s x * wOne x) volume 0 1 :=
    ((continuous_vpRatSum P hε s).mul (by unfold wOne; fun_prop)).intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun x => vpRatSum P ε s x * (x : ℂ)) volume 0 1 :=
    ((continuous_vpRatSum P hε s).mul (by fun_prop)).intervalIntegrable 0 1
  have hg : ∫ x in (0 : ℝ)..1, gIntG P Ms ε p' p x ℓ =
      Q * (I * cOne P * s) * (∫ x in (0 : ℝ)..1, vpRatSum P ε s x * wOne x) +
        Q * ((ε : ℂ) * cTwo P) * ∫ x in (0 : ℝ)..1, vpRatSum P ε s x * (x : ℂ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (i1.const_mul _) (i2.const_mul _)]
    congr 1
    funext x
    simp only [gIntG, Q, s]
    ring
  unfold hIntG
  rw [vpLoopEps_eq_spectral P hε, vpExtraEps_eq_spectral P hε, hg, powInt_eq_PG, powInt_eq_PG]
  simp only [cOne, cTwo, logSum, wOne, Q, s]
  ring

/-- **`gIntG` in terms of one spectral insertion.** -/
theorem gIntG_eq (P : Params) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (ε : ℝ) (p' p : Fin 4 → ℝ) (x : ℝ)
    (ℓ : Fin 4 → ℝ) :
    gIntG P Ms ε p' p x ℓ = ∑ f, (P.loopCoeff f : ℂ) *
      (uCoef P x * specInt (pauliChain P.e P.m p' p) P.m 2 Ms (fun _ => ε) ![P.mass f] ![x] ε
          p' p ℓ +
        vCoef P ε x * specInt (pauliChain P.e P.m p' p) P.m 1 Ms (fun _ => ε) ![P.mass f] ![x]
          ε p' p ℓ) := by
  simp only [gIntG, vpRatSum, specInt, powInt_eq_PG, Fin.prod_univ_one, Matrix.cons_val_zero,
    fDen, uCoef, vCoef, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun f _ => ?_
  push_cast
  ring

/-! ### Uniform bounds -/

/-- A uniform bound for the shifts of the first photon-type denominators at `ε ≤ 1`. -/
theorem norm_massShift_le_T {k : ℕ} (Ms : Fin (k + 2) → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (i : Fin (k + 2)) : ‖massShift (Ms i) ε‖ ≤ ∑ j, Ms j ^ 2 + 1 := by
  refine (norm_massShift_le hε).trans ?_
  have := Finset.single_le_sum (f := fun j => Ms j ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)
  linarith

/-- **The pieces of `hIntG` are `Good` uniformly**: one constant for all `ε ∈ (0, 1]` and
`x ∈ (0, 1)`, for at least four photon-type denominators of masses `≥ M₀`, `M₀ ≤ m`. -/
theorem exists_good_gIntG (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    {M₀ : ℝ} (hM₀ : 0 < M₀) (hM₀m : M₀ ≤ P.m) {k : ℕ} (hk : 2 ≤ k) (Ms : Fin (k + 2) → ℝ)
    (hMs : ∀ i, M₀ ≤ Ms i) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ G : (Fin 3 → ℝ) → ℝ, (∀ v, 0 ≤ G v) ∧
      Good (powInt (pauliChain P.e P.m p' p) P.m 0 Ms (fun _ => ε) ε p' p) C G ∧
      Good (powInt (pauliChain P.e P.m p' p) P.m 1 Ms (fun _ => ε) ε p' p) C G ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, Good (gIntG P Ms ε p' p x) C G := by
  obtain ⟨α, hα⟩ := pauliChain_quadratic P.e P.m p' p
  obtain ⟨CN, hCN⟩ := pauliChain_bound P.e P.m p' p
  have hNc := continuous_pauliChain P.e P.m p' p
  obtain ⟨K0, hK0, g0⟩ := exists_good_powInt hm hM₀ hp' hp hp0' hp0 hNc hα hCN 0 k (by omega)
  obtain ⟨K1, hK1, g1⟩ := exists_good_powInt hm hM₀ hp' hp hp0' hp0 hNc hα hCN 1 k (by omega)
  obtain ⟨K2, hK2, s2⟩ := exists_good_specInt hm hM₀ hp' hp hp0' hp0 hNc hα hCN hM₀m 1 2 k
    (by omega) (by omega)
  obtain ⟨K3, hK3, s1⟩ := exists_good_specInt hm hM₀ hp' hp hp0' hp0 hNc hα hCN hM₀m 1 1 k
    (by omega) (by omega)
  set T : ℝ := ∑ j, Ms j ^ 2 + 1
  have hT : 0 ≤ T := by positivity
  set R : ℝ := P.e ^ 2 / (2 * π ^ 2) + P.e ^ 2 / (4 * π ^ 2)
  have hR : 0 ≤ R := by positivity
  set S : ℝ := ‖(P.loopCoeff 0 : ℂ)‖ + ‖(P.loopCoeff 1 : ℂ)‖ + ‖(P.loopCoeff 2 : ℂ)‖
  have hS : 0 ≤ S := by positivity
  set B : ℝ := (1 + T) ^ 3 * (K0 + K1 + K2 + K3)
  have hB : 0 ≤ B := by positivity
  refine ⟨(1 + S * R) * B, by positivity, fun ε hε hε1 => ?_⟩
  obtain ⟨G0, hG0, h0⟩ := g0 ε ε hε hε
  obtain ⟨G1, hG1, h1⟩ := g1 ε ε hε hε
  obtain ⟨G2, hG2, h2⟩ := s2 ε ε hε hε le_rfl
  obtain ⟨G3, hG3, h3⟩ := s1 ε ε hε hε le_rfl
  set Gs : (Fin 3 → ℝ) → ℝ := fun v => (1 + T) ^ 3 * (G0 v + G1 v + G2 v + G3 v)
  have hGs : ∀ v, 0 ≤ Gs v := fun v => by
    have := hG0 v; have := hG1 v; have := hG2 v; have := hG3 v; positivity
  have hTs : ∀ i : Fin (k + 2), ‖massShift (Ms i) ε‖ ≤ T := norm_massShift_le_T Ms hε.le hε1
  have hT1 : 1 ≤ 1 + T := by linarith
  have pw : ∀ n, n ≤ 3 → (1 + T) ^ n ≤ (1 + T) ^ 3 := fun n hn => pow_le_pow_right₀ hT1 hn
  have hSR : 1 ≤ 1 + S * R := by nlinarith
  -- each piece is `Good B Gs`
  have up : ∀ {F : (Fin 4 → ℝ) → ℂ} {n : ℕ} {Kx : ℝ} {Gx : (Fin 3 → ℝ) → ℝ}, n ≤ 3 → 0 ≤ Kx →
      (∀ v, 0 ≤ Gx v) → Kx ≤ K0 + K1 + K2 + K3 → (∀ v, Gx v ≤ G0 v + G1 v + G2 v + G3 v) →
      Good F ((1 + T) ^ n * Kx) (fun v => (1 + T) ^ n * Gx v) → Good F B Gs := by
    intro F n Kx Gx hn hKx hGx hK hG hF
    refine hF.mono ?_ fun v => ?_
    · exact mul_le_mul (pw n hn) hK hKx (by positivity)
    · exact mul_le_mul (pw n hn) (hG v) (hGx v) (by positivity)
  have a0 := up (by norm_num) hK0 hG0 (by linarith) (fun v => by
      have := hG1 v; have := hG2 v; have := hG3 v; linarith)
    (h0 T hT Ms (fun _ => ε) hMs (fun _ => le_rfl) (fun i _ => hTs i))
  have a1 := up (by norm_num) hK1 hG1 (by linarith) (fun v => by
      have := hG0 v; have := hG2 v; have := hG3 v; linarith)
    (h1 T hT Ms (fun _ => ε) hMs (fun _ => le_rfl) (fun i _ => hTs i))
  refine ⟨fun v => (1 + S * R) * Gs v, fun v => by have := hGs v; positivity,
    a0.mono (le_mul_of_one_le_left hB hSR) (fun v => le_mul_of_one_le_left (hGs v) hSR),
    a1.mono (le_mul_of_one_le_left hB hSR) (fun v => le_mul_of_one_le_left (hGs v) hSR),
    fun x hx => ?_⟩
  have hin : ∀ f, Good (fun ℓ => uCoef P x *
      specInt (pauliChain P.e P.m p' p) P.m 2 Ms (fun _ => ε) ![P.mass f] ![x] ε p' p ℓ +
        vCoef P ε x *
          specInt (pauliChain P.e P.m p' p) P.m 1 Ms (fun _ => ε) ![P.mass f] ![x] ε p' p ℓ)
      (R * B) (fun v => R * Gs v) := by
    intro f
    have hf : P.m ≤ P.mass f := mass_ge hM₁ hM₂ f
    have q2 := up (by norm_num) hK2 hG2 (by linarith) (fun v => by
        have := hG0 v; have := hG1 v; have := hG3 v; linarith)
      (h2 T hT Ms (fun _ => ε) hMs (fun _ => le_rfl) (fun i _ => hTs i) ![P.mass f] ![x]
        (fun i => by fin_cases i; simpa using hf) (fun i => by fin_cases i; simpa using hx))
    have q1 := up (by norm_num) hK3 hG3 (by linarith) (fun v => by
        have := hG0 v; have := hG1 v; have := hG2 v; linarith)
      (h3 T hT Ms (fun _ => ε) hMs (fun _ => le_rfl) (fun i _ => hTs i) ![P.mass f] ![x]
        (fun i => by fin_cases i; simpa using hf) (fun i => by fin_cases i; simpa using hx))
    have h := (q2.mul_le (norm_uCoef_le P hx)).add (q1.mul_le (norm_vCoef_le P hε hε1 hx))
    refine h.mono (le_of_eq ?_) (fun v => le_of_eq ?_)
    · simp only [R]; ring
    · simp only [R]; ring
  have h0' := (hin 0).mul_le (c := (P.loopCoeff 0 : ℂ)) le_rfl
  have h1' := (hin 1).mul_le (c := (P.loopCoeff 1 : ℂ)) le_rfl
  have h2' := (hin 2).mul_le (c := (P.loopCoeff 2 : ℂ)) le_rfl
  have h := (h0'.add h1').add h2'
  refine (h.congr fun ℓ => ?_).mono ?_ ?_
  · rw [gIntG_eq, Fin.sum_univ_three]
  · have : S * (R * B) ≤ (1 + S * R) * B := by nlinarith
    simp only [S] at this ⊢
    linarith
  · intro v
    have hv := hGs v
    have : S * (R * Gs v) ≤ (1 + S * R) * Gs v := by nlinarith
    simp only [S] at this ⊢
    linarith

theorem measurable_gIntG (P : Params) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (ε : ℝ)
    (p' p : Fin 4 → ℝ) :
    Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      gIntG P Ms ε p' p q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := by
  have hℓ : Continuous fun q : ((Fin 3 → ℝ) × ℝ) × ℝ => (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_snd continuous_fst.fst
  have hs : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      Minkowski.dot (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) :=
    (VertexLimit.continuous_dot_comp hℓ hℓ).measurable
  have hx : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ => q.1.2 := measurable_fst.snd
  have hN := ((continuous_pauliChain P.e P.m p' p).comp hℓ).measurable
  have hD : ∀ (M e : ℝ) (c : Fin 4 → ℝ), Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      denom M e (c + (Fin.cons q.2 q.1.1 : Fin 4 → ℝ)) := fun M e c =>
    (continuous_denom_joint continuous_const continuous_const (continuous_const.add hℓ)).measurable
  have hD0 : ∀ (M e : ℝ), Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      denom M e (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := fun M e =>
    (continuous_denom_joint continuous_const continuous_const hℓ).measurable
  have hc : ∀ {r : ((Fin 3 → ℝ) × ℝ) × ℝ → ℝ}, Measurable r →
      Measurable fun q => ((r q : ℝ) : ℂ) := fun hr => Complex.measurable_ofReal.comp hr
  have hA : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      PG P Ms ε p' p (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := by
    unfold PG prodIntegrand
    exact hN.mul (((hD P.m ε p').mul (hD P.m ε p)).inv.mul
      (Finset.measurable_prod _ fun j _ => (hD0 _ _).inv))
  have hB : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      vpRatSum P ε (Minkowski.dot (Fin.cons q.2 q.1.1 : Fin 4 → ℝ)
        (Fin.cons q.2 q.1.1 : Fin 4 → ℝ)) q.1.2 := by
    unfold vpRatSum vacuumPolarizationFeynmanMass
    refine Finset.measurable_sum _ fun f _ => ?_
    refine (measurable_const.mul (hc ((measurable_const.sub (hx.const_mul 2)).mul hs))).div
      ((hc (measurable_const.add ((hx.mul (measurable_const.sub hx)).mul hs))).sub
        measurable_const)
  have hC : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      I * cOne P * wOne q.1.2 * ((Minkowski.dot (Fin.cons q.2 q.1.1 : Fin 4 → ℝ)
        (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) : ℝ) : ℂ) + (ε : ℂ) * cTwo P * ((q.1.2 : ℝ) : ℂ) := by
    unfold wOne
    exact ((measurable_const.mul (hc (((hx.pow_const 2).div_const 2).sub
      ((hx.pow_const 3).div_const 3)))).mul (hc hs)).add (measurable_const.mul (hc hx))
  exact (hA.mul hB).mul hC

/-! ### Fubini in `x` -/

theorem ae_Ioc_good {F : ℝ → Prop} (h : ∀ x ∈ Ioo (0 : ℝ) 1, F x) :
    ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), F x := by
  filter_upwards [ae_Ioc_mem_Ioo] with x hx using h x hx

/-- **The energy-first integral of `hIntG` after Fubini in `x`.** -/
theorem efi_hIntG_eq (P : Params) {k : ℕ} (Ms : Fin (k + 2) → ℝ) {ε : ℝ} (hε : 0 < ε)
    (p' p : Fin 4 → ℝ) {C : ℝ} {G : (Fin 3 → ℝ) → ℝ}
    (h0 : Good (powInt (pauliChain P.e P.m p' p) P.m 0 Ms (fun _ => ε) ε p' p) C G)
    (h1 : Good (powInt (pauliChain P.e P.m p' p) P.m 1 Ms (fun _ => ε) ε p' p) C G)
    (hg : ∀ x ∈ Ioo (0 : ℝ) 1, Good (gIntG P Ms ε p' p x) C G) :
    energyFirstIntegral (hIntG P Ms ε p' p) =
      (I * cOne P * (1 / 6) * logSum P ε) *
          energyFirstIntegral (powInt (pauliChain P.e P.m p' p) P.m 1 Ms (fun _ => ε) ε p' p) +
        ((ε : ℂ) * cTwo P * logSum P ε) *
          energyFirstIntegral (powInt (pauliChain P.e P.m p' p) P.m 0 Ms (fun _ => ε) ε p' p) -
        ∫ x in (0 : ℝ)..1, energyFirstIntegral (gIntG P Ms ε p' p x) := by
  obtain ⟨hI, hE⟩ := efi_integral_eq_of_good (ν := volume.restrict (Ioc (0 : ℝ) 1))
    (gIntG P Ms ε p' p) (measurable_gIntG P Ms ε p' p) (ae_Ioc_good hg)
  simp only [intervalIntegral.integral_of_le zero_le_one]
  have e : hIntG P Ms ε p' p = fun ℓ =>
      ((I * cOne P * (1 / 6) * logSum P ε) *
          powInt (pauliChain P.e P.m p' p) P.m 1 Ms (fun _ => ε) ε p' p ℓ +
        ((ε : ℂ) * cTwo P * logSum P ε) *
          powInt (pauliChain P.e P.m p' p) P.m 0 Ms (fun _ => ε) ε p' p ℓ) -
        ∫ x in Ioc (0 : ℝ) 1, gIntG P Ms ε p' p x ℓ := by
    funext ℓ
    rw [hIntG_eq P Ms hε p' p ℓ, intervalIntegral.integral_of_le zero_le_one]
  rw [e, efi_sub ((h1.1.1.const_mul _).add (h0.1.1.const_mul _)) hI,
    efi_add (h1.1.1.const_mul _) (h0.1.1.const_mul _), efi_const_mul, efi_const_mul, hE]

/-! ### The limit -/

/-- **The pointwise limit of the `x`-integrand**, for `0 < x < 1`. -/
theorem tendsto_efi_gIntG (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    {M₀ : ℝ} (hM₀ : 0 < M₀) (hM₀m : M₀ ≤ P.m) {k : ℕ} (hk : 2 ≤ k) (Ms : Fin (k + 2) → ℝ)
    (hMs : ∀ i, M₀ ≤ Ms i) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {α : ℂ}
    (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      pauliChain P.e P.m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun ε => energyFirstIntegral (gIntG P Ms ε p' p x)) (𝓝[>] 0)
      (𝓝 (phiZeroG P α p' p Ms x)) := by
  obtain ⟨CN, hCN⟩ := pauliChain_bound P.e P.m p' p
  have hNc := continuous_pauliChain P.e P.m p' p
  set N := pauliChain P.e P.m p' p
  obtain ⟨C0, hC0, hC⟩ := exists_good_gIntG P hm hM₁ hM₂ hM₀ hM₀m hk Ms hMs hp' hp hp0' hp0
  obtain ⟨K3, hK3, s1⟩ := exists_good_specInt hm hM₀ hp' hp hp0' hp0 hNc hα hCN hM₀m 1 1 k
    (by omega) (by omega)
  obtain ⟨K2, hK2, s2⟩ := exists_good_specInt hm hM₀ hp' hp hp0' hp0 hNc hα hCN hM₀m 1 2 k
    (by omega) (by omega)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := ev_pos_le_one
  set T : ℝ := ∑ j, Ms j ^ 2 + 1
  have hT : 0 ≤ T := by positivity
  have hsp : ∀ f, ∀ i : Fin 1, P.m ≤ (![P.mass f] : Fin 1 → ℝ) i := fun f i => by
    fin_cases i; simpa using mass_ge hM₁ hM₂ f
  have hxs : ∀ i : Fin 1, (![x] : Fin 1 → ℝ) i ∈ Ioo (0 : ℝ) 1 := fun i => by
    fin_cases i; simpa using hx
  have good : ∀ ε, 0 < ε → ε ≤ 1 → ∀ f j, j = 1 ∨ j = 2 → ∃ K G,
      Good (specInt N P.m j Ms (fun _ => ε) ![P.mass f] ![x] ε p' p) K G := by
    intro ε hε hε1 f j hj
    rcases hj with rfl | rfl
    · obtain ⟨G, -, h⟩ := s1 ε ε hε hε le_rfl
      exact ⟨_, _, h T hT Ms _ hMs (fun _ => le_rfl)
        (fun i _ => norm_massShift_le_T Ms hε.le hε1 i) _ _ (hsp f) hxs⟩
    · obtain ⟨G, -, h⟩ := s2 ε ε hε hε le_rfl
      exact ⟨_, _, h T hT Ms _ hMs (fun _ => le_rfl)
        (fun i _ => norm_massShift_le_T Ms hε.le hε1 i) _ _ (hsp f) hxs⟩
  -- the `specInt 2` pieces converge by the engine
  have hq2 : ∀ f, Tendsto (fun ε => energyFirstIntegral
      (specInt N P.m 2 Ms (fun _ => ε) ![P.mass f] ![x] ε p' p)) (𝓝[>] 0)
      (𝓝 (specLimit α N P.m p' p 2 1 Ms ![P.mass f] ![x])) := fun f =>
    tendsto_efi_specInt hm hM₀ hp' hp hp0' hp0 hNc hα hCN tendsto_id 2 1 k (by omega) Ms
      (fun ε _ => ε) ![P.mass f] ![x] hMs (fun i => hM₀m.trans (hsp f i)) hxs
      (fun _ => tendsto_id)
  -- the `ε specInt 1` pieces vanish
  have hq1 : ∀ f, Tendsto (fun ε => vCoef P ε x * energyFirstIntegral
      (specInt N P.m 1 Ms (fun _ => ε) ![P.mass f] ![x] ε p' p)) (𝓝[>] 0) (𝓝 0) := by
    intro f
    refine tendsto_mul_of_le_eps (K := P.e ^ 2 / (4 * π ^ 2))
      (B := (1 + T) ^ 2 * K3 * I5) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact norm_vCoef_le_eps P hε hx
    · filter_upwards [hev] with ε ⟨hε, hε1⟩
      obtain ⟨G, -, h⟩ := s1 ε ε hε hε le_rfl
      exact (h T hT Ms _ hMs (fun _ => le_rfl) (fun i _ => norm_massShift_le_T Ms hε.le hε1 i)
        _ _ (hsp f) hxs).1.norm_efi_le
  have hlim : Tendsto (fun ε => ∑ f, (P.loopCoeff f : ℂ) *
      (uCoef P x * energyFirstIntegral (specInt N P.m 2 Ms (fun _ => ε) ![P.mass f] ![x] ε p' p) +
        vCoef P ε x *
          energyFirstIntegral (specInt N P.m 1 Ms (fun _ => ε) ![P.mass f] ![x] ε p' p)))
      (𝓝[>] 0) (𝓝 (∑ f, (P.loopCoeff f : ℂ) * (uCoef P x *
        specLimit α N P.m p' p 2 1 Ms ![P.mass f] ![x] + 0))) :=
    tendsto_finsetSum _ fun f _ => tendsto_const_nhds.mul
      ((tendsto_const_nhds.mul (hq2 f)).add (hq1 f))
  simp only [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev] with ε ⟨hε, hε1⟩
  have i2 : ∀ f, EFInt (specInt N P.m 2 Ms (fun _ => ε) ![P.mass f] ![x] ε p' p) := fun f => by
    obtain ⟨_, _, h⟩ := good ε hε hε1 f 2 (Or.inr rfl); exact h.1.1
  have i1 : ∀ f, EFInt (specInt N P.m 1 Ms (fun _ => ε) ![P.mass f] ![x] ε p' p) := fun f => by
    obtain ⟨_, _, h⟩ := good ε hε hε1 f 1 (Or.inl rfl); exact h.1.1
  have hI : ∀ f, EFInt (fun ℓ => (P.loopCoeff f : ℂ) *
      (uCoef P x * specInt N P.m 2 Ms (fun _ => ε) ![P.mass f] ![x] ε p' p ℓ +
        vCoef P ε x * specInt N P.m 1 Ms (fun _ => ε) ![P.mass f] ![x] ε p' p ℓ)) := fun f =>
    (((i2 f).const_mul _).add ((i1 f).const_mul _)).const_mul _
  have e : gIntG P Ms ε p' p x = fun ℓ => ∑ f, (P.loopCoeff f : ℂ) *
      (uCoef P x * specInt N P.m 2 Ms (fun _ => ε) ![P.mass f] ![x] ε p' p ℓ +
        vCoef P ε x * specInt N P.m 1 Ms (fun _ => ε) ![P.mass f] ![x] ε p' p ℓ) :=
    funext fun ℓ => gIntG_eq P Ms ε p' p x ℓ
  rw [e, efi_sum _ fun f _ => hI f]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [efi_const_mul, efi_add ((i2 f).const_mul _) ((i1 f).const_mul _), efi_const_mul,
    efi_const_mul]

/-- **The `ε → 0⁺` limit of the energy-first integral of `hIntG`**, for at least four
photon-type denominators of masses `≥ M₀ > 0`, `M₀ ≤ m`. -/
theorem tendsto_efi_hIntG (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    {M₀ : ℝ} (hM₀ : 0 < M₀) (hM₀m : M₀ ≤ P.m) {k : ℕ} (hk : 2 ≤ k) (Ms : Fin (k + 2) → ℝ)
    (hMs : ∀ i, M₀ ≤ Ms i) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {α : ℂ}
    (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      pauliChain P.e P.m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ) :
    Tendsto (fun ε => energyFirstIntegral (hIntG P Ms ε p' p)) (𝓝[>] 0)
      (𝓝 ((I * cOne P * (1 / 6) * logSum P 0) *
          powLimit α (pauliChain P.e P.m p' p) P.m p' p 1 Ms -
        ∫ x in (0 : ℝ)..1, phiZeroG P α p' p Ms x)) := by
  obtain ⟨CN, hCN⟩ := pauliChain_bound P.e P.m p' p
  have hNc := continuous_pauliChain P.e P.m p' p
  set N := pauliChain P.e P.m p' p
  obtain ⟨C, hC0, hC⟩ := exists_good_gIntG P hm hM₁ hM₂ hM₀ hM₀m hk Ms hMs hp' hp hp0' hp0
  have hmass : ∀ f, P.mass f ≠ 0 := fun f => (hm.trans_le (mass_ge hM₁ hM₂ f)).ne'
  have hev := ev_pos_le_one
  have T1 : Tendsto (fun ε : ℝ => energyFirstIntegral (powInt N P.m 1 Ms (fun _ => ε) ε p' p))
      (𝓝[>] 0) (𝓝 (powLimit α N P.m p' p 1 Ms)) :=
    tendsto_efi_powInt hm hM₀ hp' hp hp0' hp0 hNc hα hCN tendsto_id 1 k (by omega) Ms
      (fun ε _ => ε) hMs (fun _ => tendsto_id)
  have T2 : Tendsto (fun ε : ℝ => ((ε : ℂ) * cTwo P * logSum P ε) *
      energyFirstIntegral (powInt N P.m 0 Ms (fun _ => ε) ε p' p)) (𝓝[>] 0) (𝓝 0) := by
    have hL := tendsto_logSum P hmass
    have hLb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖logSum P ε‖ ≤ ‖logSum P 0‖ + 1 := by
      have := hL.norm
      exact this.eventually (eventually_le_nhds (by linarith))
    refine tendsto_mul_of_le_eps (K := ‖cTwo P‖ * (‖logSum P 0‖ + 1)) (B := C * I5) ?_ ?_
    · filter_upwards [hLb, self_mem_nhdsWithin] with ε h1 (h2 : 0 < ε)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2]
      calc ε * ‖cTwo P‖ * ‖logSum P ε‖ ≤ ε * ‖cTwo P‖ * (‖logSum P 0‖ + 1) := by gcongr
        _ = ‖cTwo P‖ * (‖logSum P 0‖ + 1) * ε := by ring
    · filter_upwards [hev] with ε ⟨hε, hε1⟩
      obtain ⟨G, -, h0, -, -⟩ := hC ε hε hε1
      exact h0.1.norm_efi_le
  have T3 : Tendsto (fun ε : ℝ => ∫ x in (0 : ℝ)..1, energyFirstIntegral (gIntG P Ms ε p' p x))
      (𝓝[>] 0) (𝓝 (∫ x in (0 : ℝ)..1, phiZeroG P α p' p Ms x)) := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    refine tendsto_integral_efi_of_good (fun ε => gIntG P Ms ε p' p) _ (C := C)
      (Eventually.of_forall fun ε => measurable_gIntG P Ms ε p' p) ?_ ?_
    · filter_upwards [hev] with ε ⟨hε, hε1⟩
      obtain ⟨G, -, -, -, hg⟩ := hC ε hε hε1
      exact ⟨G, ae_Ioc_good hg⟩
    · exact ae_Ioc_good fun x hx =>
        tendsto_efi_gIntG P hm hM₁ hM₂ hM₀ hM₀m hk Ms hMs hp' hp hp0' hp0 hα hx
  have hlim := (((tendsto_logSum P hmass).const_mul (I * cOne P * (1 / 6))).mul T1).add T2
    |>.sub T3
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev] with ε ⟨hε, hε1⟩
  obtain ⟨G, -, h0, h1, hg⟩ := hC ε hε hε1
  rw [efi_hIntG_eq P Ms hε p' p h0 h1 hg]

/-- **The pointwise limit `phiZeroG` is integrable on `(0, 1]`.** -/
theorem intervalIntegrable_phiZeroG (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) {M₀ : ℝ} (hM₀ : 0 < M₀) (hM₀m : M₀ ≤ P.m) {k : ℕ} (hk : 2 ≤ k)
    (Ms : Fin (k + 2) → ℝ) (hMs : ∀ i, M₀ ≤ Ms i) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) {α : ℂ}
    (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      pauliChain P.e P.m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ) :
    IntervalIntegrable (phiZeroG P α p' p Ms) volume 0 1 := by
  obtain ⟨C, hC0, hC⟩ := exists_good_gIntG P hm hM₁ hM₂ hM₀ hM₀m hk Ms hMs hp' hp hp0' hp0
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine integrable_of_tendsto_efi_of_good (ν := volume.restrict (Ioc (0 : ℝ) 1))
    (l := 𝓝[>] (0 : ℝ)) (fun ε => gIntG P Ms ε p' p) _ (C := C)
    (fun ε => measurable_gIntG P Ms ε p' p) ?_ ?_
  · filter_upwards [ev_pos_le_one] with ε ⟨hε, hε1⟩
    obtain ⟨G, -, -, -, hg⟩ := hC ε hε hε1
    exact ⟨G, ae_Ioc_good hg⟩
  · exact ae_Ioc_good fun x hx =>
      tendsto_efi_gIntG P hm hM₁ hM₂ hM₀ hM₀m hk Ms hMs hp' hp hp0' hp0 hα hx

/-- Integrability of `hIntG` in both stages at fixed `ε ∈ (0, 1]`. -/
theorem efInt_hIntG (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    {M₀ : ℝ} (hM₀ : 0 < M₀) (hM₀m : M₀ ≤ P.m) {k : ℕ} (hk : 2 ≤ k) (Ms : Fin (k + 2) → ℝ)
    (hMs : ∀ i, M₀ ≤ Ms i) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) : EFInt (hIntG P Ms ε p' p) := by
  obtain ⟨C, hC0, hC⟩ := exists_good_gIntG P hm hM₁ hM₂ hM₀ hM₀m hk Ms hMs hp' hp hp0' hp0
  obtain ⟨G, -, h0, h1, hg⟩ := hC ε hε hε1
  obtain ⟨hI, -⟩ := efi_integral_eq_of_good (ν := volume.restrict (Ioc (0 : ℝ) 1))
    (gIntG P Ms ε p' p) (measurable_gIntG P Ms ε p' p) (ae_Ioc_good hg)
  have h := ((h1.1.1.const_mul (I * cOne P * (1 / 6) * logSum P ε)).add
    (h0.1.1.const_mul ((ε : ℂ) * cTwo P * logSum P ε))).add (hI.const_mul (-1))
  have e : (fun ℓ => ((I * cOne P * (1 / 6) * logSum P ε) *
        powInt (pauliChain P.e P.m p' p) P.m 1 Ms (fun _ => ε) ε p' p ℓ +
      ((ε : ℂ) * cTwo P * logSum P ε) *
        powInt (pauliChain P.e P.m p' p) P.m 0 Ms (fun _ => ε) ε p' p ℓ) +
      -1 * ∫ x in Ioc (0 : ℝ) 1, gIntG P Ms ε p' p x ℓ) = hIntG P Ms ε p' p := by
    funext ℓ
    rw [hIntG_eq P Ms hε p' p ℓ, intervalIntegral.integral_of_le zero_le_one]
    ring
  rw [← e]
  exact h

end QED.TwoLoop.VPHalfAtGen

end
