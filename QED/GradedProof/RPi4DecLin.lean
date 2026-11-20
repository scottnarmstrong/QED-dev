/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4AsmCore

/-!
# (R-Π₄) step L9, D1: the photon-regulator limit is linear in the loop coefficients

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
part D1. At fixed masses, every ingredient of the class sum `qPair` is a sum over flavours of
`c_f` times a function of `M_f` and of the counterterm mass `M_{rep f}`; the `ε → 0` limits
exist for every Pauli–Villars-closed coefficient vector. Hence:

* `DecSameMeas`, `dec_qPair_congr`, `dec_asmPolLim_congr`: `qPair` and `asmPolLim` depend on the
  flavours only through the sums `∑_f c_f g(M_f, M_{rep f})` (no hypotheses);
* `decWith Φ c`, `DecPV`: the flavours with the coefficients replaced by `c`; the PV conditions;
* `dec_qPair_lin`: `qPair` is linear in PV-closed coefficient vectors (photon pair fixed);
* `DecFaceGen e`: the face-limit identity `FaceLimitId` for every PV-closed flavour set (the
  generic L6d3 statement, a named hypothesis here);
* `dec_tendsto_asmPolLim`: under `DecFaceGen`, `asmPolLim` is the true diagonal limit (L8);
* `dec_asmPolLim_lin`, `dec_asmPolLim_zero`, `dec_asmPolLim_sum`, `dec_asmPolLim_smul`:
  **`asmPolLim` is linear in PV-closed coefficient vectors**, under `DecFaceGen`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded
open QED.GradedProof.VP2
open QED.GradedProof.SE2 (canonVec dot_canonVec nullVec dot_nullVec)

namespace QED.GradedProof.RPi4

/-- **(L6d3, generic form) the face-limit identity for every PV-closed flavour set** (the
statement the generic face-identification result delivers through `faceId_faceLimitId`). -/
def DecFaceGen (e : ℝ) : Prop :=
  ∀ (F : Type) [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) (m₀ : ℝ),
    0 < m₀ → (∀ g, m₀ ≤ Φ.mass g) → (∀ f, rep (rep f) = rep f) →
    (∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0) →
    (∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0) →
    ∀ c s : ℝ, 0 < c → -(4 * m₀ ^ 2) < s → s < 2 * c ^ 2 → FaceLimitId Φ rep e m₀ c s

section Lin

variable {F : Type} [Fintype F] [DecidableEq F]

/-- The flavour set `Φ` with its loop coefficients replaced by `c` (same masses, same open
line). -/
def decWith (Φ : Lepton.Flavors F) (c : F → ℝ) : Lepton.Flavors F :=
  ⟨Φ.mass, c, Φ.openLine⟩

/-- **Same block measure**: the two flavour sets give the same sums
`∑_f c_f g(M_f, M_{rep f})` for every test function `g`. -/
def DecSameMeas {F' : Type} [Fintype F'] (Φ : Lepton.Flavors F) (rep : F → F)
    (Ψ : Lepton.Flavors F') (rep' : F' → F') : Prop :=
  ∀ g : ℝ → ℝ → ℂ, ∑ f, (Φ.coeff f : ℂ) * g (Φ.mass f) (Φ.mass (rep f)) =
    ∑ f, (Ψ.coeff f : ℂ) * g (Ψ.mass f) (Ψ.mass (rep' f))

omit [DecidableEq F] in
/-- **The class sum depends on the flavours only through the block measure.** -/
theorem dec_qPair_congr {F' : Type} [Fintype F'] [DecidableEq F'] {Φ : Lepton.Flavors F}
    {rep : F → F} {Ψ : Lepton.Flavors F'} {rep' : F' → F'} (h : DecSameMeas Φ rep Ψ rep')
    (e a b s : ℝ) : qPair Φ rep e a b s = qPair Ψ rep' e a b s := by
  have hv : ∀ (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
      (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ),
      wV Φ e A base c a b = wV Ψ e A base c a b := by
    intro A base c
    unfold wV
    congr 1
    funext ε k μ ν
    congr 1
    funext ℓ
    exact h fun x _ => gH base c (vNum e a b A base c) a b x ε k ℓ μ ν
  have hf : fLim Φ rep e (fun g => ctPair e (Φ.mass g) a b) =
      fLim Ψ rep' e (fun g => ctPair e (Ψ.mass g) a b) := by
    unfold fLim dBlockD
    congr 1
    funext ε k μ ν
    congr 1
    funext q
    have := h fun x y => ((ctPair e y a b * x : ℝ) : ℂ) * dBubbleW e x ε k q μ ν
    simpa only [mul_assoc] using this
  simp only [qPair, hv, hf]

omit [DecidableEq F] in
/-- **`asmPolLim` depends on the flavours only through the block measure.** -/
theorem dec_asmPolLim_congr {F' : Type} [Fintype F'] [DecidableEq F'] {Φ : Lepton.Flavors F}
    {rep : F → F} {Ψ : Lepton.Flavors F'} {rep' : F' → F'} (h : DecSameMeas Φ rep Ψ rep')
    (e s : ℝ) : asmPolLim Φ rep e s = asmPolLim Ψ rep' e s := by
  simp only [asmPolLim, dec_qPair_congr h]

/-- A limit of a linear combination. -/
theorem dec_limT_lin {G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} {g₁ g₂ : ℝ → ℂ}
    {k : Fin 4 → ℝ} {μ ν : Fin 4} {L₁ L₂ : ℂ} (r : ℂ) (h₁ : Tendsto g₁ (𝓝[>] 0) (𝓝 L₁))
    (h₂ : Tendsto g₂ (𝓝[>] 0) (𝓝 L₂)) (h : ∀ ε : ℝ, 0 < ε → G ε k μ ν = r * g₁ ε + g₂ ε) :
    limT G k μ ν = r * L₁ + L₂ := by
  refine limT_eq (((h₁.const_mul r).add h₂).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (h ε hε).symm

/-- The transverse projection is linear. -/
theorem dec_projS_lin {X Y Z : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} {T : ℝ} (hT : 0 < T) (r : ℂ)
    (h : ∀ k : Fin 4 → ℝ, -T < Minkowski.dot k k → ∀ μ ν, X k μ ν = r * Y k μ ν + Z k μ ν)
    {s : ℝ} (hs : -T < s) : projS X s = r * projS Y s + projS Z s := by
  unfold projS
  split_ifs with h0
  · have e := h nullVec (by rw [dot_nullVec]; linarith)
    simp only [nProj, e 0 1]
    ring
  · have e := h (canonVec s) (by rwa [dot_canonVec])
    simp only [trProj, e, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    ring

/-- The rate `C (√(Λ⁻¹) + Λ⁻¹)` of L8 along the diagonal tends to `0`. -/
theorem dec_tendsto_rate (C : ℝ) :
    Tendsto (fun Λ : ℝ => C * (Real.sqrt Λ⁻¹ + Λ⁻¹)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun Λ : ℝ => Real.sqrt Λ⁻¹) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp tendsto_inv_atTop_zero
    rwa [Real.sqrt_zero] at this
  have := (h1.add tendsto_inv_atTop_zero).const_mul C
  rwa [add_zero, mul_zero] at this

variable (Φ : Lepton.Flavors F) (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)

/-- The Pauli–Villars conditions of a coefficient vector, block by block. -/
def DecPV (c : F → ℝ) : Prop :=
  (∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), c f = 0) ∧
    ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), c f * Φ.mass f ^ 2 = 0

variable {Φ rep}

theorem DecPV.zero : DecPV Φ rep fun _ => 0 :=
  ⟨fun _ _ => by simp, fun _ _ => by simp⟩

theorem DecPV.sum {ι : Type*} (S : Finset ι) {v : ι → F → ℝ} (hv : ∀ i ∈ S, DecPV Φ rep (v i)) :
    DecPV Φ rep fun f => ∑ i ∈ S, v i f := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i hi => (hv i hi).1 b hb
  · simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i hi => (hv i hi).2 b hb

theorem DecPV.lin {c d : F → ℝ} (hc : DecPV Φ rep c) (hd : DecPV Φ rep d) (r : ℝ) :
    DecPV Φ rep fun f => r * c f + d f := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hc.1 b hb, hd.1 b hb]
    ring
  · simp only [add_mul, mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hc.2 b hb, hd.2 b hb]
    ring

include hm₀ hmass hrep

/-- **The class sum is linear in the loop coefficients** (at fixed masses, on PV-closed
coefficient vectors), at every photon pair and every `s > -4m₀²`. -/
theorem dec_qPair_lin (P : Params) (he : P.e ≠ 0) {c d : F → ℝ} (hc : DecPV Φ rep c)
    (hd : DecPV Φ rep d) (r : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {s : ℝ}
    (hs : -(4 * m₀ ^ 2) < s) :
    qPair (decWith Φ fun f => r * c f + d f) rep P.e a b s =
      r * qPair (decWith Φ c) rep P.e a b s + qPair (decWith Φ d) rep P.e a b s := by
  have hrc := DecPV.lin hc (⟨fun _ _ => by simp, fun _ _ => by simp⟩ : DecPV Φ rep fun _ => 0) r
  simp only [add_zero] at hrc
  have hT : (0 : ℝ) < 4 * m₀ ^ 2 := by positivity
  -- the three classes
  have hW : ∀ (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
      (base : Fin 5 → Fin 2 → ℤ) (cl : Fin 5 → ℝ),
      (∀ c' : F → ℝ, DecPV Φ rep c' →
        VPJ (2 * m₀) (vSumF (decWith Φ c') P.e A base cl a b)) →
      ∀ k : Fin 4 → ℝ, -(4 * m₀ ^ 2) < Minkowski.dot k k → ∀ μ ν,
        wV (decWith Φ fun f => r * c f + d f) P.e A base cl a b k μ ν =
          (r : ℂ) * wV (decWith Φ c) P.e A base cl a b k μ ν +
            wV (decWith Φ d) P.e A base cl a b k μ ν := by
    intro A base cl hV k hk μ ν
    have hk' : -(2 * m₀) ^ 2 < Minkowski.dot k k := by nlinarith
    refine dec_limT_lin (r : ℂ) (tendsto_wV _ _ _ _ _ (hV c hc) hk' μ ν)
      (tendsto_wV _ _ _ _ _ (hV d hd) hk' μ ν) fun ε hε => ?_
    have i1 := (hV _ hrc).2 ε hε k μ ν
    have i2 := (hV d hd).2 ε hε k μ ν
    rw [← QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]
    calc _ = QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
          vSumF (decWith Φ fun f => r * c f) P.e A base cl a b ε k ℓ μ ν +
            vSumF (decWith Φ d) P.e A base cl a b ε k ℓ μ ν) := by
          congr 1
          funext ℓ
          simp only [vSumF, decWith, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun f _ => ?_
          push_cast
          ring
      _ = _ := QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add i1 i2
      _ = _ := by
          congr 2
          funext ℓ
          simp only [vSumF, decWith, Finset.mul_sum]
          refine Finset.sum_congr rfl fun f _ => ?_
          push_cast
          ring
  have hpv : ∀ c' : F → ℝ, DecPV Φ rep c' → ∀ b', rep b' = b' →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b'), (decWith Φ c').coeff f = 0 :=
    fun c' h => h.1
  have hpv₂ : ∀ c' : F → ℝ, DecPV Φ rep c' → ∀ b', rep b' = b' →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b'),
        (decWith Φ c').coeff f * (decWith Φ c').mass f ^ 2 = 0 :=
    fun c' h => h.2
  have hA := hW aVA baseVA cVA fun c' h =>
    vpj_VA (decWith Φ c') rep hm₀ hmass hrep (hpv c' h) (hpv₂ c' h) P.e ha hb
  have hB := hW aVB baseVB cVB fun c' h =>
    vpj_VB (decWith Φ c') rep hm₀ hmass hrep (hpv c' h) (hpv₂ c' h) P.e ha hb
  have hC := hW aVC baseVC cVC fun c' h =>
    vpj_VC (decWith Φ c') rep hm₀ hmass hrep (hpv c' h) (hpv₂ c' h) P.e ha hb
  -- the mass insertion
  have hF : ∀ k : Fin 4 → ℝ, -(4 * m₀ ^ 2) < Minkowski.dot k k → ∀ μ ν,
      fLim (decWith Φ fun f => r * c f + d f) rep P.e (fun g => ctPair P.e (Φ.mass g) a b) k
          μ ν =
        (r : ℂ) * fLim (decWith Φ c) rep P.e (fun g => ctPair P.e (Φ.mass g) a b) k μ ν +
          fLim (decWith Φ d) rep P.e (fun g => ctPair P.e (Φ.mass g) a b) k μ ν := by
    intro k hk μ ν
    have t1 := tendsto_fLim (decWith Φ c) rep hm₀ hmass hrep hc.1 hc.2 P he
      (fun g => ctPair P.e (Φ.mass g) a b) hk μ ν
    have t2 := tendsto_fLim (decWith Φ d) rep hm₀ hmass hrep hd.1 hd.2 P he
      (fun g => ctPair P.e (Φ.mass g) a b) hk μ ν
    refine dec_limT_lin (r : ℂ) t1 t2 fun ε hε => ?_
    have i1 := (vpf_dBlockD (decWith Φ fun f => r * c f) rep hm₀ hmass hrep hrc.1 hrc.2 P he
      (fun g => ctPair P.e (Φ.mass g) a b)).2 ε hε k μ ν
    have i2 := (vpf_dBlockD (decWith Φ d) rep hm₀ hmass hrep hd.1 hd.2 P he
      (fun g => ctPair P.e (Φ.mass g) a b)).2 ε hε k μ ν
    rw [← QED.OneLoop.energyFirstIntegral_const_mul]
    calc _ = QED.OneLoop.energyFirstIntegral (fun q =>
          dBlockD (decWith Φ fun f => r * c f) rep P.e (fun g => ctPair P.e (Φ.mass g) a b) ε k
              q μ ν +
            dBlockD (decWith Φ d) rep P.e (fun g => ctPair P.e (Φ.mass g) a b) ε k q μ ν) := by
          congr 1
          funext q
          simp only [dBlockD, decWith, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun f _ => ?_
          push_cast
          ring
      _ = _ := efi_add i1 i2
      _ = _ := by
          congr 2
          funext q
          simp only [dBlockD, decWith, Finset.mul_sum]
          refine Finset.sum_congr rfl fun f _ => ?_
          push_cast
          ring
  have hT' : (0 : ℝ) < 4 * m₀ ^ 2 := hT
  unfold qPair
  have eA := dec_projS_lin hT' (r : ℂ) hA hs
  have eB := dec_projS_lin hT' (r : ℂ) hB hs
  have eC := dec_projS_lin hT' (r : ℂ) hC hs
  have eF := dec_projS_lin hT' (r : ℂ) hF hs
  simp only [decWith] at eA eB eC eF ⊢
  rw [eA, eB, eC, eF]
  ring

/-- **The diagonal limit `asmPolLim` is a true limit**, given the face-limit identity (L8). -/
theorem dec_tendsto_asmPolLim (P : Params) (he : P.e ≠ 0)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hF : DecFaceGen P.e) {s : ℝ} (hs : -(4 * m₀ ^ 2) < s) :
    Tendsto (fun Λ : ℝ => qPair Φ rep P.e Λ⁻¹ Λ s - qPair Φ rep P.e Λ⁻¹ Λ 0) atTop
      (𝓝 (asmPolLim Φ rep P.e s)) := by
  have h00 : -(4 * m₀ ^ 2) < 0 := by nlinarith
  obtain ⟨C, hC⟩ := asm_exists_norm_sub_polLim_le Φ rep P hm₀ hmass hrep hPV₁ hPV₂ he
    (S₀ := s) (S := s) hs fun s' h₀ h₁ =>
      hF F Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ _ s' (by positivity)
        ((lt_min hs h00).trans_le h₀) (h₁.trans_lt (asm_max_lt_two_mul_sq s))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (dec_tendsto_rate C)
  filter_upwards [eventually_ge_atTop 1] with Λ hΛ
  exact hC s le_rfl le_rfl Λ⁻¹ Λ (inv_pos.2 (zero_lt_one.trans_le hΛ)) (inv_le_one_of_one_le₀ hΛ)
    hΛ

/-- **`asmPolLim` is linear in the loop coefficients** (PV-closed coefficient vectors at fixed
masses), given the face-limit identity. -/
theorem dec_asmPolLim_lin (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e) {c d : F → ℝ}
    (hc : DecPV Φ rep c) (hd : DecPV Φ rep d) (r : ℝ) {s : ℝ} (hs : -(4 * m₀ ^ 2) < s) :
    asmPolLim (decWith Φ fun f => r * c f + d f) rep P.e s =
      r * asmPolLim (decWith Φ c) rep P.e s + asmPolLim (decWith Φ d) rep P.e s := by
  have h00 : -(4 * m₀ ^ 2) < 0 := by nlinarith
  have t1 := dec_tendsto_asmPolLim (Φ := decWith Φ c) (rep := rep) hm₀ hmass hrep P he hc.1
    hc.2 hF hs
  have t2 := dec_tendsto_asmPolLim (Φ := decWith Φ d) (rep := rep) hm₀ hmass hrep P he hd.1
    hd.2 hF hs
  refine Tendsto.limUnder_eq (((t1.const_mul (r : ℂ)).add t2).congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with Λ hΛ
  rw [dec_qPair_lin hm₀ hmass hrep P he hc hd r (inv_pos.2 hΛ) hΛ hs,
    dec_qPair_lin hm₀ hmass hrep P he hc hd r (inv_pos.2 hΛ) hΛ h00]
  ring

/-- The zero coefficient vector has `asmPolLim = 0`. -/
theorem dec_asmPolLim_zero (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e) {s : ℝ}
    (hs : -(4 * m₀ ^ 2) < s) : asmPolLim (decWith Φ fun _ => 0) rep P.e s = 0 := by
  have h := dec_asmPolLim_lin hm₀ hmass hrep P he hF DecPV.zero DecPV.zero 1 hs
  simp only [mul_zero, add_zero, Complex.ofReal_one, one_mul] at h
  linear_combination -h

/-- **`asmPolLim` of a finite sum of PV-closed coefficient vectors.** -/
theorem dec_asmPolLim_sum (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e) {s : ℝ}
    (hs : -(4 * m₀ ^ 2) < s) {ι : Type*} [DecidableEq ι] (S : Finset ι) {v : ι → F → ℝ}
    (hv : ∀ i ∈ S, DecPV Φ rep (v i)) :
    asmPolLim (decWith Φ fun f => ∑ i ∈ S, v i f) rep P.e s =
      ∑ i ∈ S, asmPolLim (decWith Φ (v i)) rep P.e s := by
  induction S using Finset.induction_on with
  | empty => simpa using dec_asmPolLim_zero hm₀ hmass hrep P he hF hs
  | insert a S ha ih =>
    have hvS : ∀ i ∈ S, DecPV Φ rep (v i) := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have e : (fun f => ∑ i ∈ insert a S, v i f) = fun f => 1 * v a f + ∑ i ∈ S, v i f := by
      funext f
      rw [Finset.sum_insert ha, one_mul]
    rw [e, dec_asmPolLim_lin hm₀ hmass hrep P he hF (hv a (Finset.mem_insert_self a S))
      (DecPV.sum S hvS) 1 hs, ih hvS, Finset.sum_insert ha, Complex.ofReal_one, one_mul]

/-- **Scaling the coefficients.** -/
theorem dec_asmPolLim_smul (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e) {s : ℝ}
    (hs : -(4 * m₀ ^ 2) < s) {c : F → ℝ} (hc : DecPV Φ rep c) (r : ℝ) :
    asmPolLim (decWith Φ fun f => r * c f) rep P.e s = r * asmPolLim (decWith Φ c) rep P.e s := by
  have h := dec_asmPolLim_lin hm₀ hmass hrep P he hF hc DecPV.zero r hs
  rw [dec_asmPolLim_zero hm₀ hmass hrep P he hF hs, add_zero] at h
  simpa only [add_zero] using h

end Lin

end QED.GradedProof.RPi4

end
