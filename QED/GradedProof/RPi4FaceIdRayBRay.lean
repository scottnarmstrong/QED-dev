/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRayBDil
public import QED.GradedProof.RPi4InstPiece

/-!
# (R-Π₄) step L10, T2.UV: the rate of one piece along the ray, with a polynomial constant

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (the rate input
(B) of `QED.GradedProof.RPi4.faceIdRay_of_size_rate`). Along the ray `k'(s) = tiltVec √s s =
√s (1, 0, 1, 1)` the dilation `QED.GradedProof.RPi4.faceIdRayB_pieceF_dilateQ` (`r = √s`) turns
the collapsed integrand of a merged piece into a constant times the integrand at the fixed
momentum `(1, 0, 1, 1)`, masses `M / √s` and photon mass `u / s`; P0 gives `V₀ ≥ (m₀² / s) ferSum`
there, and `QED.GradedProof.RPi4.faceIdRayB_piece_rate` gives the rate in `u / s ≥ 1` with the
constant `C (1 + s / m₀²)^N`. Hence a rate `B s^p u^{-1/2}` for `u ≥ s ≥ 1`:

* `faceIdRayB_vhat`, `faceIdRayB_tiltVec_eq`: the ray;
* `FaceIdRayRateB` (input (B) of `faceIdRay_of_size_rate`), `.add/.const_mul/.zero/.sum/.congr`;
* **`faceIdRayB_vpPiece`**: `FaceIdRayRateB` of one merged piece, given normalized quartic
  representatives `Q₁ s`, `Q₀ s` of the numerator at `k'(s)` (`ℓ ↦ s^{-D/2} N(k'(s))(√s ℓ)`),
  bounded uniformly in `s ≥ 1`.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.MassScaling
open QED.GradedProof.WI2 (dbl)
open QED.Integration.Feynman (simplexSet simplexPoint simplexPoint_mem_stdSimplex)
open QED.TwoLoop.Bridge (IsLoopPoly)

/-! ### The ray vector -/

/-- The direction `(1, 0, 1, 1)` of the ray. -/
noncomputable def faceIdRayB_vhat : Fin 4 → ℝ := ![1, 0, 1, 1]

theorem faceIdRayB_tiltVec_eq {s : ℝ} (hs : 0 ≤ s) :
    tiltVec (Real.sqrt s) s = Real.sqrt s • faceIdRayB_vhat := by
  have e : 2 * Real.sqrt s ^ 2 - s = s := by rw [Real.sq_sqrt hs]; ring
  funext i
  fin_cases i <;> simp [tiltVec, faceIdRayB_vhat, e]

/-! ### The rate with a polynomial constant along the ray -/

/-- **The rate along the ray with a polynomial constant** (input (B) of
`faceIdRay_of_size_rate`): `‖u G(u, k'(s)) - L(s)‖ ≤ B s^p u^{-1/2}` for `u ≥ s ≥ 1`, `p ≥ 1`. -/
def FaceIdRayRateB (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ B p : ℝ, 1 ≤ p ∧ ∃ L : ℝ → ℂ, ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
    ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s) - L s‖ ≤ B * s ^ p * u ^ (-(1 / 2) : ℝ)

namespace FaceIdRayRateB

variable {G H : ℝ → (Fin 4 → ℝ) → ℂ}

theorem mono_exp {B p q s u : ℝ} (hpq : p ≤ q) (hs : 1 ≤ s) (hu : 0 < u) :
    |B| * s ^ p * u ^ (-(1 / 2) : ℝ) ≤ |B| * s ^ q * u ^ (-(1 / 2) : ℝ) :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hs hpq) (abs_nonneg _)) (Real.rpow_nonneg hu.le _)

theorem add (hG : FaceIdRayRateB G) (hH : FaceIdRayRateB H) :
    FaceIdRayRateB fun u k => G u k + H u k := by
  obtain ⟨B, p, hp, L, hL⟩ := hG
  obtain ⟨B', p', -, L', hL'⟩ := hH
  refine ⟨|B| + |B'|, max p p', hp.trans (le_max_left _ _), fun s => L s + L' s,
    fun s hs u hu => ?_⟩
  have hu0 : 0 < u := (one_pos.trans_le hs).trans_le hu
  have e : (u : ℂ) * (G u (tiltVec (Real.sqrt s) s) + H u (tiltVec (Real.sqrt s) s)) -
      (L s + L' s) = ((u : ℂ) * G u (tiltVec (Real.sqrt s) s) - L s) +
        ((u : ℂ) * H u (tiltVec (Real.sqrt s) s) - L' s) := by ring
  rw [e]
  have h1 := (hL s hs u hu).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (le_abs_self B) (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg hu0.le _))
  have h2 := (hL' s hs u hu).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (le_abs_self B') (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg hu0.le _))
  have g1 := mono_exp (B := B) (le_max_left p p') hs hu0
  have g2 := mono_exp (B := B') (le_max_right p p') hs hu0
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ |B| * s ^ max p p' * u ^ (-(1 / 2) : ℝ) + |B'| * s ^ max p p' * u ^ (-(1 / 2) : ℝ) := by
        linarith
    _ = _ := by ring

theorem const_mul (hG : FaceIdRayRateB G) (r : ℂ) :
    FaceIdRayRateB fun u k => r * G u k := by
  obtain ⟨B, p, hp, L, hL⟩ := hG
  refine ⟨‖r‖ * B, p, hp, fun s => r * L s, fun s hs u hu => ?_⟩
  have e : (u : ℂ) * (r * G u (tiltVec (Real.sqrt s) s)) - r * L s =
      r * ((u : ℂ) * G u (tiltVec (Real.sqrt s) s) - L s) := by ring
  rw [e, norm_mul, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((hL s hs u hu).trans (le_of_eq (by ring))) (norm_nonneg _)

theorem zero : FaceIdRayRateB fun _ _ => 0 :=
  ⟨0, 1, le_rfl, fun _ => 0, fun _ _ u _ => by simp⟩

theorem sum {ι : Type*} (t : Finset ι) {G : ι → ℝ → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ t, FaceIdRayRateB (G i)) : FaceIdRayRateB fun u k => ∑ i ∈ t, G i u k := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (zero : FaceIdRayRateB fun _ _ => 0)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem congr (hG : FaceIdRayRateB G)
    (e : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
      G u (tiltVec (Real.sqrt s) s) = H u (tiltVec (Real.sqrt s) s)) :
    FaceIdRayRateB H := by
  obtain ⟨B, p, hp, L, hL⟩ := hG
  exact ⟨B, p, hp, L, fun s hs u hu => by rw [← e s hs u hu]; exact hL s hs u hu⟩

end FaceIdRayRateB

/-! ### One piece along the ray -/

section Piece

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])

include hflow hrow hrow4

/-- **The rate of one merged piece along the ray, with a polynomial constant.** The numerator at
`k'(s)` is `ℓ ↦ s^{D/2} Q₁(s)(ℓ / √s)` with `Q₁`, `Q₀` bounded families of representatives of
the same polynomial, of degree `≤ d₁` along loop `1`, `≤ d₀` along loop `0` (no quartic part
for `m = 5`); the other hypotheses are those of `heavyRate_vpPiece`. -/
theorem faceIdRayB_vpPiece {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : ∀ k, IsLoopPoly 2 (m + 1 - 3) (N k))
    (hB : ∀ k, RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 (N k))
    (D : ℕ) (Q₁ Q₀ : {s : ℝ // 1 ≤ s} → LoopQuartic) {B₁ B₀ : ℝ} (hQ₁ : LQBdd Q₁ B₁)
    (hQ₀ : LQBdd Q₀ B₀)
    (he₁ : ∀ s : {s : ℝ // 1 ≤ s}, (dilateQ ((Real.sqrt s.1 : ℂ) ^ D)
      (((Real.sqrt s.1)⁻¹ : ℝ) : ℂ) (Q₁ s)).eval = N (tiltVec (Real.sqrt s.1) s.1))
    (he₀ : ∀ s, (Q₀ s).eval = (Q₁ s).eval) {d₁ d₀ : ℕ}
    (hQd₁ : ∀ s, LoopDegLe 1 d₁ (Q₁ s)) (hQd₀ : ∀ s, LoopDegLe 0 d₀ (Q₀ s))
    (hq : m = 6 ∨ ∀ s, (Q₁ s).quart = 0 ∧ (Q₀ s).quart = 0)
    (hd₁ : d₁ ≤ 3) (hd₀ : d₀ ≤ 3)
    (hA1 : 2 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card)
    (hd11 : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card = 2 →
      d₁ ≤ 1)
    (hR1 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![1, 0])
    (hA0 : 2 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card)
    (hd01 : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card = 2 →
      d₀ ≤ 1)
    (hR0 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![0, 1])
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ) (hMs : Ms (Fin.last m) = 0)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l) :
    FaceIdRayRateB fun t k => pairDens (N k)
      (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
      (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) t := by
  classical
  have hm0 : 0 < m := by omega
  set γ₀ := Fin.last m with hγ₀
  set α := castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc) with hα_def
  set cs : Fin (m + 1) → ℝ := fun l => c (sh l.castSucc) with hcs
  have hrows := castLoopMatrix_rows base hrow hrow4 fun l : Fin (m + 1) => sh l.castSucc
  have hne : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 ↔ l ≠ γ₀ := fun l => by
    rw [Ne, hsh, Ne, Fin.ext_iff]
    simp only [Fin.val_castSucc, γ₀, Fin.val_last]
    have := l.isLt
    omega
  have hr10 : (![1, 0] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
    have := congrFun h 1; simp at this
  have hr01 : (![0, 1] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
    have := congrFun h 0; simp at this
  have huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀ := fun l => by
    constructor
    · intro h
      by_contra hl
      rcases (hrows l).1 ((hne l).2 hl) with h' | h'
      · exact hr10 (h'.symm.trans h)
      · exact hr01 (h'.symm.trans h)
    · intro hl
      exact (hrows l).2 (not_not.1 fun h => (hne l).1 h hl)
  have hrow3 : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1] := fun l => by
    by_cases h4 : sh l.castSucc = 4
    · exact Or.inr (Or.inr ((hrows l).2 h4))
    · rcases (hrows l).1 h4 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hf10 : (Finset.univ.filter fun l => α l ≠ ![1, 0]) =
      Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0] := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, α]
    exact not_congr (castLoopMatrix_eq_row10_iff _ l)
  have hf01 : (Finset.univ.filter fun l => α l ≠ ![0, 1]) =
      Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1] := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, α]
    exact not_congr (castLoopMatrix_eq_row01_iff _ l)
  -- the ray, the scaled masses and the unscaled quartics
  let ι := {s : ℝ // 1 ≤ s}
  set rr : ι → ℝ := fun s => Real.sqrt s.1 with hrr
  have hr1 : ∀ s : ι, 1 ≤ rr s := fun s => Real.one_le_sqrt.2 s.2
  have hr0 : ∀ s : ι, 0 < rr s := fun s => one_pos.trans_le (hr1 s)
  have hrs : ∀ s : ι, rr s ^ 2 = s.1 := fun s => Real.sq_sqrt (one_pos.le.trans s.2)
  set kk : ι → Fin 4 → ℝ := fun s => tiltVec (rr s) s.1 with hkk
  have hkv : ∀ s : ι, kk s = rr s • faceIdRayB_vhat := fun s =>
    faceIdRayB_tiltVec_eq (one_pos.le.trans s.2)
  set Mh : ι → Fin (m + 1) → ℝ := fun s => (rr s)⁻¹ • Ms with hMh
  have hMsc : ∀ s : ι, rr s • Mh s = Ms := fun s => by
    simp only [hMh, smul_smul, mul_inv_cancel₀ (hr0 s).ne', one_smul]
  have hpsc : ∀ s : ι, (fun i => cs i • kk s) = rr s • fun i => cs i • faceIdRayB_vhat :=
    fun s => by
      funext i
      simp only [hkv, Pi.smul_apply, smul_smul, mul_comm]
  set Qu : ι → LoopQuartic := fun s =>
    dilateQ ((rr s : ℂ) ^ D) (((rr s)⁻¹ : ℝ) : ℂ) (Q₁ s) with hQu
  have hferF : ∀ z : Fin (m + 1) → ℝ, ferSum α z =
      ∑ i ∈ Finset.univ.filter (fun i => sh (Fin.castSucc i) ≠ 4), z i := fun z => by
    simp only [ferSum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Ne, huniq l, hne l]
  -- P0 at the unscaled momenta (`k'(s)` is spacelike)
  have hVu : ∀ (s : ι) (z : Fin (m + 1) → ℝ), (∀ l, 0 ≤ z l) → ∑ l, z l = 1 →
      symanzikU α z ≠ 0 → m₀ ^ 2 * ferSum α z ≤ symanzikV α (fun i => cs i • kk s) Ms z := by
    intro s z hz _ hU
    have hdot : Minkowski.dot (kk s) (kk s) = s.1 := dot_tiltVec (by
      rw [hrs s]; linarith [s.2])
    have hP0 := symanzikV_vp_ge_fermion base c y₁ y₂ hflow (fun l : Fin (m + 1) => sh l.castSucc)
      Ms hm₀ hf (k := kk s) (by rw [hdot]; nlinarith [s.2]) hz hU
    rw [← hferF] at hP0
    have hs' : 0 ≤ s.1 / (2 * m₀) ^ 2 := by have := s.2; positivity
    have hmin : min 1 (1 + Minkowski.dot (kk s) (kk s) / (2 * m₀) ^ 2) = 1 := by
      rw [hdot]
      exact min_eq_left (by linarith)
    rw [hmin, one_mul] at hP0
    exact hP0
  have hc₀u : 0 < m₀ ^ 2 := by positivity
  -- P0 at the scaled data
  have hVs : ∀ (s : ι) (z : Fin (m + 1) → ℝ), (∀ l, 0 ≤ z l) → ∑ l, z l = 1 →
      symanzikU α z ≠ 0 → m₀ ^ 2 / s.1 * ferSum α z ≤
        symanzikV α (fun i => cs i • faceIdRayB_vhat) (Mh s) z := by
    intro s z hz hz1 hU
    have h := hVu s z hz hz1 hU
    rw [hpsc s, ← hMsc s, symanzikV_smul, hrs s] at h
    have hs0 : 0 < s.1 := one_pos.trans_le s.2
    rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
    linarith
  -- the rate of the scaled family
  have hn : m + 1 = 7 ∨ (m + 1 = 6 ∧ ∀ s, (Q₁ s).quart = 0 ∧ (Q₁ s).quart = 0 ∧
      (Q₀ s).quart = 0) := by
    rcases hm with h5 | h6
    · refine Or.inr ⟨by omega, fun s => ?_⟩
      rcases hq with h | h
      · omega
      · exact ⟨(h s).1, (h s).1, (h s).2⟩
    · exact Or.inl (by omega)
  have hMb : ∀ (s : ι) l, |Mh s l| ≤ ∑ j, |Ms j| := fun s l => by
    have h1 : |Mh s l| ≤ |Ms l| := by
      simp only [hMh, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos (hr0 s)]
      exact mul_le_of_le_one_left (abs_nonneg _) (inv_le_one_of_one_le₀ (hr1 s))
    exact h1.trans (Finset.single_le_sum (f := fun j => |Ms j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ l))
  obtain ⟨C, N', L, hC⟩ := faceIdRayB_piece_rate (n := m + 1) (by omega) α γ₀ huniq hrow3
    (by rwa [hf10])
    (by obtain ⟨l, hl⟩ := hR1; exact ⟨l, (castLoopMatrix_eq_row10_iff _ l).2 hl⟩)
    (by rwa [hf01])
    (by obtain ⟨l, hl⟩ := hR0; exact ⟨l, (castLoopMatrix_eq_row01_iff _ l).2 hl⟩)
    cs (fun _ => faceIdRayB_vhat) Mh Q₁ Q₁ Q₀ hQ₁ hQ₁ hQ₀ (fun _ => rfl) he₀
    (fun s => (hQd₁ s).mono hd₁)
    (fun h s => (hQd₁ s).mono (hd11 (by rwa [hf10] at h))) (fun s => (hQd₀ s).mono hd₀)
    (fun h s => (hQd₀ s).mono (hd01 (by rwa [hf01] at h))) hn (fun _ => le_rfl) hMb
    (fun s => m₀ ^ 2 / s.1) (fun s => by have := one_pos.trans_le s.2; positivity) hVs
  -- integrability of the collapsed integrand at every `t ≥ 1`
  have hl : sh (Fin.last (m + 1)) = sh (Fin.last m).castSucc := by
    rw [(hsh _).2 (by simp), (hsh _).2 (by simp)]
  have hαd : castLoopMatrix (fun l => base (sh l)) = dbl γ₀ α :=
    comp_eq_dbl sh hl fun r s => (base r s : ℝ)
  have hcrit' : NoSubdivergenceRefined 2 E (dbl γ₀ α) :=
    hαd ▸ (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).2 hcrit
  have hint : ∀ (s : ι) (t : ℝ), 1 ≤ t → IntegrableOn
      (fun x => pieceF (m + 1) (Qu s) α (fun i => cs i • kk s) Ms γ₀ t (simplexPoint x))
      (simplexSet m) := by
    intro s t ht
    set p : Fin (m + 1) → Fin 4 → ℝ := fun i => cs i • kk s
    have hpd : (fun l => c (sh l) • kk s) = dbl γ₀ p := comp_eq_dbl sh hl fun r => c r • kk s
    obtain ⟨Qg, hq, hBQ, hQg⟩ := good_of_poly (n := m + 1) (by omega) (hpoly (kk s))
      (hαd ▸ hB (kk s))
    have hcoef : IntegrableOn (coeffOne Qg (dbl γ₀ α) (dbl γ₀ p)) (simplexSet (m + 1)) ∧
        IntegrableOn (coeffTwo Qg (dbl γ₀ α) (dbl γ₀ p)) (simplexSet (m + 1)) ∧
        IntegrableOn (coeffThree Qg (dbl γ₀ α)) (simplexSet (m + 1)) := by
      rcases hq with h7 | hq0
      · exact integrableOn_coeff Qg (dbl γ₀ α) (dbl γ₀ p) h7 hcrit' hBQ
      · exact integrableOn_coeff_cubic Qg (dbl γ₀ α) (dbl γ₀ p) hq0 (by omega) hcrit' hBQ
    have k1 := integrableOn_mul_of_dbl hm0 γ₀ (f := cOneAt (m + 1) Qg (dbl γ₀ α) (dbl γ₀ p))
      (g := cOneAt (m + 1) Qg α p) (cOneAt_dbl _ Qg α p · γ₀) hcoef.1
    have k2 := integrableOn_mul_of_dbl hm0 γ₀ (f := cTwoAt (m + 1) Qg (dbl γ₀ α) (dbl γ₀ p))
      (g := cTwoAt (m + 1) Qg α p) (cTwoAt_dbl _ Qg α p · γ₀) hcoef.2.1
    have k3 := integrableOn_mul_of_dbl hm0 γ₀ (f := cThreeAt (m + 1) Qg (dbl γ₀ α))
      (g := cThreeAt (m + 1) Qg α) (cThreeAt_dbl _ Qg α · γ₀) hcoef.2.2
    have hIg := integrableOn_pieceF (n := m + 1) (Q := Qg) (pp := p) (M := Ms) (u := t)
      (lt_min hc₀u one_pos) k1 k2 k3 fun y hy hU => by
        have hz := simplexPoint_mem_stdSimplex hy
        have h1 := hVu s _ hz.1 hz.2 hU
        rw [ferSum_eq_one_sub huniq hz.2] at h1
        have hzγ := hz.1 γ₀
        have hzγ1 : simplexPoint y γ₀ ≤ 1 := by
          rw [← hz.2]
          exact Finset.single_le_sum (fun j _ => hz.1 j) (Finset.mem_univ γ₀)
        have e1 := mul_le_mul_of_nonneg_right (min_le_left (m₀ ^ 2) 1) (sub_nonneg.2 hzγ1)
        have e2 := mul_le_mul_of_nonneg_right (min_le_right (m₀ ^ 2) 1) hzγ
        have e3 := mul_le_mul_of_nonneg_left ht hzγ
        nlinarith
    refine hIg.congr_fun (fun x _ => ?_) (QED.Integration.Feynman.measurableSet_simplexSet m)
    simp only [pieceF, hQu, hrr, paramAtV_congr (hQg.trans (he₁ s).symm)]
  -- the dilation
  set κ : ι → ℂ := fun s => (rr s : ℂ) ^ D * (((rr s)⁻¹ : ℝ) : ℂ) ^ (2 * (m + 1 - 3)) with hκ
  have hdil : ∀ (s : ι) (t : ℝ) (z : Fin (m + 1) → ℝ),
      pieceF (m + 1) (Qu s) α (fun i => cs i • kk s) Ms γ₀ t z =
        κ s * pieceF (m + 1) (Q₁ s) α (fun i => cs i • faceIdRayB_vhat) (Mh s) γ₀
          (t / s.1) z := by
    intro s t z
    have e := faceIdRayB_pieceF_dilateQ (m + 1) (Q₁ s) ((rr s : ℂ) ^ D) (hr0 s).ne' α
      (fun i => cs i • faceIdRayB_vhat) z (by omega) (Mh s) γ₀ (t / s.1)
    have ht : rr s ^ 2 * (t / s.1) = t := by
      rw [hrs s]; field_simp [(one_pos.trans_le s.2).ne']
    rw [ht, ← hpsc s, hMsc s] at e
    rw [hQu]
    exact e
  have hκ0 : ∀ s, κ s ≠ 0 := fun s => by
    have := (hr0 s).ne'
    simp only [hκ]
    exact mul_ne_zero (pow_ne_zero _ (ofReal_ne_zero.2 this))
      (pow_ne_zero _ (ofReal_ne_zero.2 (inv_ne_zero this)))
  have hκb : ∀ s : ι, ‖κ s‖ ≤ s.1 ^ D := fun s => by
    have h1 : ‖(rr s : ℂ) ^ D‖ ≤ s.1 ^ D := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (hr0 s).le]
      refine pow_le_pow_left₀ (hr0 s).le ?_ D
      have := hr1 s
      nlinarith [hrs s]
    have h2 : ‖(((rr s)⁻¹ : ℝ) : ℂ) ^ (2 * (m + 1 - 3))‖ ≤ 1 := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (hr0 s).le)]
      exact pow_le_one₀ (inv_nonneg.2 (hr0 s).le) (inv_le_one_of_one_le₀ (hr1 s))
    simp only [hκ, norm_mul]
    calc _ ≤ s.1 ^ D * 1 := mul_le_mul h1 h2 (norm_nonneg _) (by have := s.2; positivity)
      _ = _ := mul_one _
  -- assembly
  set W : ℝ := 1 + (m₀ ^ 2)⁻¹
  refine ⟨π ^ 4 * |C| * W ^ N', ((D + N' + 2 : ℕ) : ℝ), by norm_cast; omega,
    fun s => if h : 1 ≤ s then -((π : ℂ) ^ 4) * κ ⟨s, h⟩ * (s : ℂ) * L ⟨s, h⟩ else 0,
    fun s hs u hu => ?_⟩
  set s' : ι := ⟨s, hs⟩
  have hs0 : 0 < s := one_pos.trans_le hs
  have hu0 : 0 < u := hs0.trans_le hu
  have hu1 : 1 ≤ u / s := by rw [le_div_iff₀ hs0]; linarith
  have hMu : Function.update Ms γ₀ 0 = Ms := by
    rw [Function.update_eq_self_iff]; exact hMs.symm
  have hI := hint s' u (hs.trans hu)
  have hd' : ∀ z, pieceF (m + 1) (Qu s') α (fun i => cs i • kk s') Ms γ₀ u z =
      κ s' * pieceF (m + 1) (Q₁ s') α (fun i => cs i • faceIdRayB_vhat) (Mh s') γ₀ (u / s) z :=
    fun z => hdil s' u z
  have hIs : IntegrableOn (fun x => pieceF (m + 1) (Q₁ s') α (fun i => cs i • faceIdRayB_vhat)
      (Mh s') γ₀ (u / s) (simplexPoint x)) (simplexSet m) := by
    refine IntegrableOn.congr_fun (Integrable.const_mul hI (κ s')⁻¹) (fun x _ => ?_)
      (QED.Integration.Feynman.measurableSet_simplexSet m)
    simp only [hd', ← mul_assoc, inv_mul_cancel₀ (hκ0 s'), one_mul]
  have hpd : pairDens (N (tiltVec (Real.sqrt s) s)) α
      (fun l => c (sh l.castSucc) • tiltVec (Real.sqrt s) s) Ms γ₀ u =
      -((π : ℂ) ^ 4) * (κ s' * ∫ x in simplexSet m, pieceF (m + 1) (Q₁ s') α
        (fun i => cs i • faceIdRayB_vhat) (Mh s') γ₀ (u / s) (simplexPoint x)) := by
    rw [pairDens_eq (he₁ s'), hMu]
    congr 1
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (QED.Integration.Feynman.measurableSet_simplexSet m)
      fun x _ => ?_
    rw [← hd']
    rfl
  simp only [hs, dite_true]
  rw [hpd]
  set J := ∫ x in simplexSet m, pieceF (m + 1) (Q₁ s') α (fun i => cs i • faceIdRayB_vhat)
    (Mh s') γ₀ (u / s) (simplexPoint x)
  have e : (u : ℂ) * (-((π : ℂ) ^ 4) * (κ s' * J)) - -((π : ℂ) ^ 4) * κ s' * (s : ℂ) * L s' =
      -((π : ℂ) ^ 4) * κ s' * (s : ℂ) * ((u / s) • J - L s') := by
    have hsC : (s : ℂ) ≠ 0 := ofReal_ne_zero.2 hs0.ne'
    rw [Complex.real_smul]
    push_cast
    field_simp
    ring
  rw [e]
  have hR := hC s' (u / s) hu1 hIs
  have hm2 : 0 ≤ (m₀ ^ 2)⁻¹ := by positivity
  have hW1 : 1 ≤ W := by simp only [W]; linarith
  have hWs : 1 + (m₀ ^ 2 / s)⁻¹ ≤ W * s := by
    rw [inv_div]
    have : s / m₀ ^ 2 = (m₀ ^ 2)⁻¹ * s := by ring
    simp only [W]; nlinarith
  have hpow : (1 + (m₀ ^ 2 / s)⁻¹) ^ N' ≤ W ^ N' * s ^ N' := by
    rw [← mul_pow]
    have h0 : 0 ≤ (m₀ ^ 2 / s)⁻¹ := by positivity
    exact pow_le_pow_left₀ (by linarith) hWs N'
  have hus : (u / s) ^ (-(1 / 2) : ℝ) ≤ s * u ^ (-(1 / 2) : ℝ) := by
    rw [Real.div_rpow hu0.le hs0.le, div_eq_mul_inv, ← Real.rpow_neg hs0.le, neg_neg, mul_comm]
    have h12 : s ^ (1 / 2 : ℝ) ≤ s := by
      simpa using Real.rpow_le_rpow_of_exponent_le hs (by norm_num : (1 / 2 : ℝ) ≤ 1)
    exact mul_le_mul_of_nonneg_right (by simpa using h12) (Real.rpow_nonneg hu0.le _)
  have hR' : ‖(u / s) • J - L s'‖ ≤ |C| * (W ^ N' * s ^ N') * (s * u ^ (-(1 / 2) : ℝ)) := by
    change ‖(u / s) • J - L s'‖ ≤ C * (1 + (m₀ ^ 2 / s)⁻¹) ^ N' * (u / s) ^ (-(1 / 2) : ℝ)
      at hR
    have h0 : 0 ≤ (1 + (m₀ ^ 2 / s)⁻¹) ^ N' := by positivity
    have h1 : 0 ≤ (u / s) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by positivity) _
    refine hR.trans ?_
    calc C * (1 + (m₀ ^ 2 / s)⁻¹) ^ N' * (u / s) ^ (-(1 / 2) : ℝ)
        ≤ |C| * (1 + (m₀ ^ 2 / s)⁻¹) ^ N' * (u / s) ^ (-(1 / 2) : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) h0) h1
      _ ≤ |C| * (W ^ N' * s ^ N') * (s * u ^ (-(1 / 2) : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)) hus h1
            (by positivity)
  have hκs : ‖κ s'‖ ≤ s ^ D := hκb s'
  rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg hs0.le]
  have hsp : s ^ (((D + N' + 2 : ℕ)) : ℝ) = s ^ D * s ^ N' * s * s := by
    rw [Real.rpow_natCast]; ring
  rw [hsp]
  have hX : 0 ≤ ‖(u / s) • J - L s'‖ := norm_nonneg _
  calc π ^ 4 * ‖κ s'‖ * s * ‖(u / s) • J - L s'‖
      ≤ π ^ 4 * s ^ D * s * (|C| * (W ^ N' * s ^ N') * (s * u ^ (-(1 / 2) : ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκs (by positivity))
          hs0.le) hR' hX (by positivity)
    _ = _ := by ring

end Piece

end QED.GradedProof.RPi4

end
