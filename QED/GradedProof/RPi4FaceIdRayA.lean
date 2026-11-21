/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRayInt

/-!
# (R-Π₄) step L10, T2.UV: the size bound with a gain along the ray

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.UV, input
(A) of `QED.GradedProof.RPi4.faceIdRay_of_size_rate`). Along `k'(s) = tiltVec √s s`, `u ≥ s ≥ 1`,
input (A) is the size bound `‖u G(u, k'(s))‖ ≤ A s^{1-δ}`, `δ > 0` (`FaceIdRayA`). It is enough
to prove it with a loss `u^a` for every `a > 0` (`FaceIdRayAPow`; a loss `(1 + log u)^N` is a
special case, `FaceIdRayALog`): together with the rate (B) `‖u G - L(s)‖ ≤ B s^p u^{-1/2}`, the
loss is only seen for `u ≤ s^{2p}`, where `u^a ≤ s^{δ/2}` for `a = δ/(4p)`, and for `u ≥ s^{2p}`
the rate bounds `u G` by `‖L(s)‖ + |B|`. The power-loss form is closed under finite sums and
constant multiples, so for a class density it reduces to the merged pieces of
`QED.GradedProof.RPi4.triDens`, one flavour at a time (no cancellation between flavours is
used).

* `FaceIdRayA`, `FaceIdRayALog`, `FaceIdRayAPow`; `faceIdRayA_one_add_log_le`,
  `faceIdRayA_log_pow_le`, `FaceIdRayA.log`, `FaceIdRayALog.pow`;
* **`faceIdRayA_of_pow_rate`**: `FaceIdRayAPow` and (B) give `FaceIdRayA`;
* **`faceIdRay_of_pow_rate`**: `FaceIdRayAPow` and (B) give `FaceIdRateRay`;
* `FaceIdRayAPow.zero`, `.mono`, `.add`, `.const_mul`, `.sum`, `.congr`;
* `faceIdRayAPieceA`, `faceIdRayAPieceB`, `faceIdRayAPieceP`, `faceIdRayA_triDens_eq`,
  `FaceIdRayAPieces`, `faceIdRayA_triDens_of_pieces`;
* **`faceIdRayA_vDens_of_pieces`**: the merged pieces at every flavour give `FaceIdRayAPow` of a
  class density;
* **`faceIdRate_cfg4_of_pow_rate`**: `MajFaceRate` at `decCfg 1 4` from `FaceIdRayAPow` and
  (B) of the three class densities.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.RPi4

open QED.WickModel (Params)
open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

/-- **Input (A)**: the size bound with a gain along the ray, `‖u G(u, k'(s))‖ ≤ A s^{1-δ}` for
`u ≥ s ≥ 1`, in the form `QED.GradedProof.RPi4.faceIdRay_of_size_rate` consumes. -/
def FaceIdRayA (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ A δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
    ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s)‖ ≤ A * s ^ (1 - δ)

/-- **Input (A) with a log loss**: `‖u G(u, k'(s))‖ ≤ A s^{1-δ} (1 + log u)^N` for
`u ≥ s ≥ 1`. -/
def FaceIdRayALog (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ A δ : ℝ, ∃ N : ℕ, 0 < δ ∧ ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
    ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s)‖ ≤ A * s ^ (1 - δ) * (1 + Real.log u) ^ N

theorem FaceIdRayA.log {G : ℝ → (Fin 4 → ℝ) → ℂ} (h : FaceIdRayA G) : FaceIdRayALog G := by
  obtain ⟨A, δ, hδ, hA⟩ := h
  exact ⟨A, δ, 0, hδ, fun s hs u hu => by simpa using hA s hs u hu⟩

/-- `1 + log x ≤ (1 + 1/ε) x^ε` for `x ≥ 1`, `ε > 0`. -/
theorem faceIdRayA_one_add_log_le {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    1 + Real.log x ≤ (1 + 1 / ε) * x ^ ε := by
  have hx0 : 0 < x := by linarith
  have hxe : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have hl : Real.log (x ^ ε) ≤ x ^ ε - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_rpow hx0] at hl
  have h1 : Real.log x ≤ x ^ ε / ε := by
    rw [le_div_iff₀ hε]
    linarith [mul_comm ε (Real.log x)]
  have h2 : x ^ ε / ε = 1 / ε * x ^ ε := by ring
  nlinarith

/-- **Input (A) with a power loss in `u`**: some `δ > 0` such that for every `a > 0`,
`‖u G(u, k'(s))‖ ≤ A_a s^{1-δ} u^a` for `u ≥ s ≥ 1`. -/
def FaceIdRayAPow (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, 0 < a → ∃ A : ℝ, ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
    ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s)‖ ≤ A * s ^ (1 - δ) * u ^ a

/-- `(1 + log u)^N ≤ (1 + (N + 1)/a)^N u^a` for `u ≥ 1`, `a > 0`. -/
theorem faceIdRayA_log_pow_le {u a : ℝ} (N : ℕ) (hu : 1 ≤ u) (ha : 0 < a) :
    (1 + Real.log u) ^ N ≤ (1 + 1 / (a / (N + 1))) ^ N * u ^ a := by
  have hu0 : 0 < u := by linarith
  have hε : 0 < a / (N + 1) := by positivity
  have h1 := faceIdRayA_one_add_log_le hu hε
  have h2 : (1 + Real.log u) ^ N ≤ ((1 + 1 / (a / (N + 1))) * u ^ (a / (N + 1))) ^ N :=
    pow_le_pow_left₀ (by linarith [Real.log_nonneg hu]) h1 N
  have h3 : (u ^ (a / (N + 1))) ^ N ≤ u ^ a := by
    rw [← Real.rpow_mul_natCast hu0.le]
    refine faceIdRay_rpow_mono hu ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  rw [mul_pow] at h2
  exact h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))

theorem FaceIdRayALog.pow {G : ℝ → (Fin 4 → ℝ) → ℂ} (h : FaceIdRayALog G) :
    FaceIdRayAPow G := by
  obtain ⟨A, δ, N, hδ, hA⟩ := h
  refine ⟨δ, hδ, fun a ha => ⟨|A| * (1 + 1 / (a / (N + 1))) ^ N, fun s hs u hsu => ?_⟩⟩
  have hu : 1 ≤ u := hs.trans hsu
  have hl : 0 ≤ 1 + Real.log u := by linarith [Real.log_nonneg hu]
  calc _ ≤ A * s ^ (1 - δ) * (1 + Real.log u) ^ N := hA s hs u hsu
    _ ≤ |A| * s ^ (1 - δ) * (1 + Real.log u) ^ N := by gcongr; exact le_abs_self A
    _ ≤ |A| * s ^ (1 - δ) * ((1 + 1 / (a / (N + 1))) ^ N * u ^ a) := by
        gcongr; exact faceIdRayA_log_pow_le N hu ha
    _ = _ := by ring

/-- **(A) from its power-loss form and the rate (B).** -/
theorem faceIdRayA_of_pow_rate {G : ℝ → (Fin 4 → ℝ) → ℂ} {L : ℝ → ℂ} {B p : ℝ} (hp : 1 ≤ p)
    (hA : FaceIdRayAPow G)
    (hB : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
      ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s) - L s‖ ≤ B * s ^ p * u ^ (-(1 / 2) : ℝ)) :
    FaceIdRayA G := by
  obtain ⟨δ, hδ, hA⟩ := hA
  obtain ⟨A, hA⟩ := hA (δ / (4 * p)) (by positivity)
  set δ' : ℝ := min δ 1 / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hδ'δ : δ' ≤ δ / 2 := by
    have := min_le_left δ 1
    rw [hδ']; linarith
  have hδ'1 : δ' ≤ 1 / 2 := by
    have := min_le_right δ 1
    rw [hδ']; linarith
  set K : ℝ := |A| with hK
  have hK0 : 0 ≤ K := abs_nonneg A
  -- below `s^{2p}`
  have hlow : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u → u ≤ s ^ (2 * p) →
      ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s)‖ ≤ K * s ^ (1 - δ') := fun s hs u hsu hu => by
    have hs0 : 0 < s := by linarith
    have hu0 : 0 < u := hs0.trans_le hsu
    have ha : 0 ≤ δ / (4 * p) := by positivity
    have h3 : u ^ (δ / (4 * p)) ≤ s ^ (δ / 2) := by
      calc u ^ (δ / (4 * p)) ≤ (s ^ (2 * p)) ^ (δ / (4 * p)) :=
            Real.rpow_le_rpow hu0.le hu ha
        _ = s ^ (δ / 2) := by
            rw [← Real.rpow_mul hs0.le]
            congr 1
            field_simp
            ring
    have h4 : s ^ (1 - δ) * s ^ (δ / 2) ≤ s ^ (1 - δ') := by
      rw [← Real.rpow_add hs0]
      exact faceIdRay_rpow_mono hs (by linarith)
    calc _ ≤ A * s ^ (1 - δ) * u ^ (δ / (4 * p)) := hA s hs u hsu
      _ ≤ |A| * s ^ (1 - δ) * u ^ (δ / (4 * p)) := by gcongr; exact le_abs_self A
      _ ≤ |A| * s ^ (1 - δ) * s ^ (δ / 2) := by gcongr
      _ = K * (s ^ (1 - δ) * s ^ (δ / 2)) := by rw [hK]; ring
      _ ≤ K * s ^ (1 - δ') := by gcongr
  refine ⟨K + 2 * |B|, δ', hδ'0, fun s hs u hsu => ?_⟩
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s ^ (1 - δ') := Real.one_le_rpow hs (by linarith)
  have hss : s ≤ s ^ (2 * p) := by
    conv_lhs => rw [← Real.rpow_one s]
    exact faceIdRay_rpow_mono hs (by linarith)
  rcases le_or_gt u (s ^ (2 * p)) with hu | hu
  · have := hlow s hs u hsu hu
    have : 0 ≤ 2 * |B| * s ^ (1 - δ') := by positivity
    nlinarith
  · -- above `s^{2p}`: `‖u G‖ ≤ ‖u G - L‖ + ‖u₀ G(u₀) - L‖ + ‖u₀ G(u₀)‖`, `u₀ = s^{2p}`
    set u₀ := s ^ (2 * p) with hu₀
    have hu₀0 : 0 < u₀ := Real.rpow_pos_of_pos hs0 _
    have hrt : s ^ p * u₀ ^ (-(1 / 2) : ℝ) = 1 := by
      rw [hu₀, ← Real.rpow_mul hs0.le, ← Real.rpow_add hs0]
      norm_num
      ring_nf
      exact Real.rpow_zero s
    have hB' : ∀ v : ℝ, u₀ ≤ v → B * s ^ p * v ^ (-(1 / 2) : ℝ) ≤ |B| := fun v hv => by
      have h1 : v ^ (-(1 / 2) : ℝ) ≤ u₀ ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hu₀0 hv (by norm_num)
      calc B * s ^ p * v ^ (-(1 / 2) : ℝ) ≤ |B| * (s ^ p * v ^ (-(1 / 2) : ℝ)) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_abs_self B)
              (mul_nonneg (Real.rpow_nonneg hs0.le _)
                (Real.rpow_nonneg (hu₀0.le.trans hv) _))
        _ ≤ |B| * (s ^ p * u₀ ^ (-(1 / 2) : ℝ)) := by gcongr
        _ = |B| := by rw [hrt, mul_one]
    have e1 := (hB s hs u hsu).trans (hB' u hu.le)
    have e2 := (hB s hs u₀ hss).trans (hB' u₀ le_rfl)
    have e3 := hlow s hs u₀ hss le_rfl
    set a := (u : ℂ) * G u (tiltVec (Real.sqrt s) s)
    set b := (u₀ : ℂ) * G u₀ (tiltVec (Real.sqrt s) s)
    have : ‖a‖ ≤ ‖a - L s‖ + ‖b - L s‖ + ‖b‖ := by
      have h := norm_sub_le (a - L s) (b - L s)
      have h' : a - L s - (b - L s) = a - b := by ring
      rw [h'] at h
      have := norm_le_norm_sub_add a b
      linarith
    have : 0 ≤ 2 * |B| * (s ^ (1 - δ') - 1) := mul_nonneg (by positivity) (by linarith)
    nlinarith

/-- **The ray face rate from (A) with a power loss and the rate (B).** -/
theorem faceIdRay_of_pow_rate {G : ℝ → (Fin 4 → ℝ) → ℂ} {L : ℝ → ℂ} {B p : ℝ} (hp : 1 ≤ p)
    (hA : FaceIdRayAPow G)
    (hB : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
      ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s) - L s‖ ≤ B * s ^ p * u ^ (-(1 / 2) : ℝ)) :
    FaceIdRateRay G := by
  obtain ⟨A, δ, hδ, hA'⟩ := faceIdRayA_of_pow_rate hp hA hB
  exact faceIdRay_of_size_rate hδ hp hA' hB

/-! ### Closure of the power-loss form -/

namespace FaceIdRayAPow

variable {G H : ℝ → (Fin 4 → ℝ) → ℂ}

theorem zero : FaceIdRayAPow fun _ _ => 0 :=
  ⟨1, one_pos, fun _ _ => ⟨0, fun s _ u _ => by simp⟩⟩

/-- The bound with `|A|` and the smaller gain. -/
theorem mono {A δ δ' a s u : ℝ} (hs : 1 ≤ s) (hsu : s ≤ u) (hδ : δ' ≤ δ) :
    A * s ^ (1 - δ) * u ^ a ≤ |A| * s ^ (1 - δ') * u ^ a := by
  have hu0 : 0 ≤ u ^ a := Real.rpow_nonneg (by linarith) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self A)
    (faceIdRay_rpow_mono hs (by linarith)) (Real.rpow_nonneg (by linarith) _)
    (abs_nonneg A)) hu0

theorem add (hG : FaceIdRayAPow G) (hH : FaceIdRayAPow H) :
    FaceIdRayAPow fun u k => G u k + H u k := by
  obtain ⟨δ, hδ, hG⟩ := hG
  obtain ⟨δ', hδ', hH⟩ := hH
  refine ⟨min δ δ', lt_min hδ hδ', fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := hG a ha
  obtain ⟨B, hB⟩ := hH a ha
  refine ⟨|A| + |B|, fun s hs u hu => ?_⟩
  rw [mul_add, add_mul, add_mul]
  exact (norm_add_le _ _).trans (add_le_add
    ((hA s hs u hu).trans (mono hs hu (min_le_left _ _)))
    ((hB s hs u hu).trans (mono hs hu (min_le_right _ _))))

theorem const_mul (hG : FaceIdRayAPow G) (r : ℂ) : FaceIdRayAPow fun u k => r * G u k := by
  obtain ⟨δ, hδ, hG⟩ := hG
  refine ⟨δ, hδ, fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := hG a ha
  refine ⟨‖r‖ * A, fun s hs u hu => ?_⟩
  rw [mul_left_comm, norm_mul, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hA s hs u hu) (norm_nonneg _)

theorem sum {ι : Type*} (t : Finset ι) {G : ι → ℝ → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ t, FaceIdRayAPow (G i)) : FaceIdRayAPow fun u k => ∑ i ∈ t, G i u k := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (zero : FaceIdRayAPow fun _ _ => 0)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr (hG : FaceIdRayAPow G)
    (e : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
      G u (tiltVec (Real.sqrt s) s) = H u (tiltVec (Real.sqrt s) s)) : FaceIdRayAPow H := by
  obtain ⟨δ, hδ, hG⟩ := hG
  refine ⟨δ, hδ, fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := hG a ha
  exact ⟨A, fun s hs u hu => by rw [← e s hs u hu]; exact hA s hs u hu⟩

end FaceIdRayAPow

/-! ### A class density from its merged pieces -/

section Pieces

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
  (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
  (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (M X Y : ℝ) (μ ν : Fin 4)

/-- The merged piece with seven lines `(i, j)` of `triDens` (fermion lines `i`, `j` doubled). -/
noncomputable def faceIdRayAPieceA (i j : Fin 4) (u : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  pairDens (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      Num M k ℓ μ ν)
    (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc))
    (fun l => c (shA i j l.castSucc) • k)
    ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0]
    (Fin.last 6) u

/-- The merged piece with six lines `i` of `triDens` (fermion line `i` doubled). -/
noncomputable def faceIdRayAPieceB (i : Fin 4) (u : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  pairDens (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν))
    (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
    (fun l => c (shB i l.castSucc) • k)
    ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] (Fin.last 5) u

/-- The padded merged piece of `triDens`. -/
noncomputable def faceIdRayAPieceP (u : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  pairDens (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν *
      propDenom Y 0 (fm base (ppc c k) 0 ℓ))
    (castLoopMatrix fun l : Fin 6 => base (shB 0 l.castSucc))
    (fun l => c (shB 0 l.castSucc) • k) ![Y, Y, Y, Y, Y, 0] (Fin.last 5) u

theorem faceIdRayA_triDens_eq (u : ℝ) (k : Fin 4 → ℝ) :
    triDens base c Num E4 M X Y u k μ ν =
      (∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then faceIdRayAPieceA base c Num M X Y μ ν i j u k
        else 0) + ∑ i : Fin 4, faceIdRayAPieceB base c Num M X Y μ ν i u k +
        faceIdRayAPieceP base c E4 M X Y μ ν u k :=
  rfl

/-- **(A) with a power loss for the merged pieces** of the combination with masses `(M, X, Y)`. -/
def FaceIdRayAPieces : Prop :=
  (∀ i j : Fin 4, i ≤ j → FaceIdRayAPow (faceIdRayAPieceA base c Num M X Y μ ν i j)) ∧
    (∀ i : Fin 4, FaceIdRayAPow (faceIdRayAPieceB base c Num M X Y μ ν i)) ∧
      FaceIdRayAPow (faceIdRayAPieceP base c E4 M X Y μ ν)

theorem faceIdRayA_triDens_of_pieces (h : FaceIdRayAPieces base c Num E4 M X Y μ ν) :
    FaceIdRayAPow fun u k => triDens base c Num E4 M X Y u k μ ν := by
  obtain ⟨hA, hB, hP⟩ := h
  have hA' : ∀ i j : Fin 4, FaceIdRayAPow fun u k =>
      if i ≤ j then faceIdRayAPieceA base c Num M X Y μ ν i j u k else 0 := fun i j => by
    by_cases hij : i ≤ j
    · simpa only [hij, ite_true] using hA i j hij
    · simpa only [hij, ite_false] using (FaceIdRayAPow.zero : FaceIdRayAPow fun _ _ => 0)
  exact ((FaceIdRayAPow.sum Finset.univ fun i _ =>
    FaceIdRayAPow.sum Finset.univ fun j _ => hA' i j).add
    (FaceIdRayAPow.sum Finset.univ fun i _ => hB i)).add hP

end Pieces

/-- **A class density from its merged pieces, one flavour at a time**: if the merged pieces of
the combination `(M_f, X, X + 1)` of the normalized class numerator satisfy (A) with a power
loss for every flavour `f`, so does `vDens`. -/
theorem faceIdRayA_vDens_of_pieces
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) {F : Type} [Fintype F] (Φ : Lepton.Flavors F)
    (e m₀ : ℝ) (μ ν : Fin 4)
    (h : ∀ f, FaceIdRayAPieces base c (vNum e 0 1 A base c) (vNumE4 e 0 1 A) (Φ.mass f)
      (blockX Φ m₀) (blockX Φ m₀ + 1) μ ν) :
    FaceIdRayAPow fun u k => vDens A base c Φ e m₀ u k μ ν :=
  FaceIdRayAPow.sum Finset.univ fun f _ =>
    (faceIdRayA_triDens_of_pieces base c _ _ _ _ _ μ ν (h f)).const_mul (Φ.coeff f : ℂ)

/-- **`MajFaceRate` at `decCfg 1 4` from (A) with a power loss and the rate (B)** of the three
class densities. -/
theorem faceIdRate_cfg4_of_pow_rate (P : Params) (he : P.e ≠ 0)
    {L : Fin 3 → ℝ → ℂ} {B p : Fin 3 → ℝ} (hp : ∀ i, 1 ≤ p i)
    (hA : FaceIdRayAPow fun u k => vDens aVA baseVA cVA (decCfg 1 4) P.e 1 u k 2 3)
    (hB : FaceIdRayAPow fun u k => vDens aVB baseVB cVB (decCfg 1 4) P.e 1 u k 2 3)
    (hC : FaceIdRayAPow fun u k => vDens aVC baseVC cVC (decCfg 1 4) P.e 1 u k 2 3)
    (rA : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
      ‖(u : ℂ) * vDens aVA baseVA cVA (decCfg 1 4) P.e 1 u (tiltVec (Real.sqrt s) s) 2 3 -
        L 0 s‖ ≤ B 0 * s ^ p 0 * u ^ (-(1 / 2) : ℝ))
    (rB : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
      ‖(u : ℂ) * vDens aVB baseVB cVB (decCfg 1 4) P.e 1 u (tiltVec (Real.sqrt s) s) 2 3 -
        L 1 s‖ ≤ B 1 * s ^ p 1 * u ^ (-(1 / 2) : ℝ))
    (rC : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
      ‖(u : ℂ) * vDens aVC baseVC cVC (decCfg 1 4) P.e 1 u (tiltVec (Real.sqrt s) s) 2 3 -
        L 2 s‖ ≤ B 2 * s ^ p 2 * u ^ (-(1 / 2) : ℝ)) :
    MajFaceRate (decCfg 1 4) (fun _ => 0) P.e 1 :=
  faceIdRate_cfg4_of_ray P he (faceIdRay_of_pow_rate (hp 0) hA rA)
    (faceIdRay_of_pow_rate (hp 1) hB rB) (faceIdRay_of_pow_rate (hp 2) hC rC)

end QED.GradedProof.RPi4

end
