/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutCPt
public import QED.TwoLoop.UnitSCLimitCMasters
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G4: the per-point identity of the outer-massive corner

Helper level (no frozen statement). Assembles `SetCKScOutCPt` into
**`scOutC_cForm_eq`**: for `m, e, w, u > 0`, `s ≥ 0` and `M = m - e u ≠ 0`,

`cForm(a₀, a₁, a₂, c₀, c₁, c₂, c₃, w (s + e), u/w, M, log(M + β h), log(1 + M/(β h)))
  = ∫₀^∞ T(v)/(u + v)² dv`

with `T = scOutCTg a₀ a₁ a₂ c₀ c₁ c₂ c₃ m e w s` (`β h = (s + e) u`). The `(0, ∞)` splits into
the threshold set `S = {s v < m}` (`scOutCS`) and its complement `R = {m ≤ s v}` (`scOutCR`,
empty when `s = 0`); on `S` the node change of variables gives the masters, on `R` the weight is
`-c₀ w/v` (`scOutC_k_R`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit

/-- The complement `R = {v > 0 : m ≤ s v}` of the threshold set. -/
def scOutCR (m s : ℝ) : Set ℝ := {v | 0 < v ∧ m ≤ s * v}

section

variable {m e w s u : ℝ}

theorem measurableSet_scOutCR (m s : ℝ) : MeasurableSet (scOutCR m s) :=
  measurableSet_Ioi.inter (measurableSet_le measurable_const (measurable_const.mul measurable_id))

theorem scOutCS_union : scOutCS m s ∪ scOutCR m s = Ioi 0 := by
  ext v
  simp only [scOutCS, scOutCR, mem_union, mem_ofPred_eq, mem_Ioi]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    by_cases h' : s * v < m
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, not_lt.1 h'⟩

theorem scOutCS_disjoint : Disjoint (scOutCS m s) (scOutCR m s) :=
  Set.disjoint_left.2 fun _ h h' => absurd h.2 (not_lt.2 h'.2)

/-- The `k`-part beyond the threshold: `-c₀ w (log(m + s u) - log m)/u`. -/
theorem scOutC_k_R (hm : 0 < m) (hu : 0 < u) (hs : 0 ≤ s) (c₀ c₁ c₂ c₃ : ℝ) :
    IntegrableOn (fun v => scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)) (scOutCR m s) ∧
      ∫ v in scOutCR m s, scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v) =
        -(c₀ * w) * ((log (m + s * u) - log m) / u) := by
  rcases hs.eq_or_lt with hs0 | hs0
  · subst hs0
    have : scOutCR m 0 = ∅ := by
      ext v; simp only [scOutCR, zero_mul, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => absurd h.2 (not_le.2 hm)
    rw [this]
    simp
  · have hR : scOutCR m s = Ici (m / s) := by
      ext v
      simp only [scOutCR, mem_ofPred_eq, mem_Ici]
      constructor
      · rintro ⟨-, h⟩; rw [div_le_iff₀ hs0]; linarith
      · intro h
        have hV : 0 < m / s := div_pos hm hs0
        refine ⟨hV.trans_le h, ?_⟩
        rw [div_le_iff₀ hs0] at h; linarith
    have hV : 0 < m / s := div_pos hm hs0
    obtain ⟨i1, v1⟩ := cornInIoi1 hu hV
    have hcg : EqOn (fun v => scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v))
        (fun v => -(c₀ * w) * (1 / (v * (u + v)))) (Ioi (m / s)) := fun v hv => by
      have hv0 : 0 < v := hV.trans hv
      have h' : ¬ s * v < m := by
        rw [mem_Ioi, div_lt_iff₀ hs0] at hv; linarith
      simp only [scOutCk, h', ↓reduceIte]
      have : u + v ≠ 0 := by positivity
      have := hv0.ne'
      field_simp
    rw [hR, integrableOn_Ici_iff_integrableOn_Ioi, integral_Ici_eq_integral_Ioi]
    have i1' : IntegrableOn (fun v => -(c₀ * w) * (1 / (v * (u + v)))) (Ioi (m / s)) :=
      i1.const_mul _
    refine ⟨i1'.congr_fun hcg.symm measurableSet_Ioi, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi hcg, integral_const_mul, v1]
    have e1 : 1 + u / (m / s) = (m + s * u) / m := by field_simp
    rw [e1, log_div (by positivity) hm.ne']

/-- Three integrable summands. -/
theorem scOutC_add3 {S : Set ℝ} {f₁ f₂ f₃ : ℝ → ℝ} (h₁ : IntegrableOn f₁ S)
    (h₂ : IntegrableOn f₂ S) (h₃ : IntegrableOn f₃ S) :
    IntegrableOn (fun x => f₁ x + f₂ x + f₃ x) S ∧
      ∫ x in S, (f₁ x + f₂ x + f₃ x) = (∫ x in S, f₁ x) + (∫ x in S, f₂ x) + ∫ x in S, f₃ x := by
  have h12 : IntegrableOn (fun x => f₁ x + f₂ x) S := h₁.add h₂
  refine ⟨h12.add h₃, ?_⟩
  rw [integral_add h12 h₃, integral_add h₁ h₂]

/-- The `k`-part on the threshold set, by the masters. -/
theorem scOutC_k_S (hm : 0 < m) (he : 0 < e) (hw : 0 < w) (hu : 0 < u) (hs : 0 ≤ s)
    (hM : m - e * u ≠ 0) (c₀ c₁ c₂ c₃ : ℝ) :
    IntegrableOn (fun v => scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)) (scOutCS m s) ∧
      ∫ v in scOutCS m s, scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v) =
        c₁ * (log (1 + (m - e * u) / ((s + e) * u)) / (m - e * u)) +
          c₂ * (u / w) * (1 / ((m - e * u) * ((s + e) * u)) -
            log (1 + (m - e * u) / ((s + e) * u)) / (m - e * u) ^ 2) +
          c₃ * (u / w) ^ 2 * (1 / (2 * (m - e * u) * ((s + e) * u) ^ 2) -
            1 / ((m - e * u) ^ 2 * ((s + e) * u)) +
              log (1 + (m - e * u) / ((s + e) * u)) / (m - e * u) ^ 3) := by
  have hc : 0 < (s + e) * u := by positivity
  have hMc : 0 < m - e * u + (s + e) * u := by nlinarith [mul_nonneg hs hu.le]
  obtain ⟨j1, w1⟩ := scOutCJ1 hM hc hMc
  obtain ⟨j2, w2⟩ := scOutCJ2 hM hc hMc
  obtain ⟨j3, w3⟩ := scOutCJ3 hM hc hMc
  obtain ⟨hiff, hval⟩ := scOutC_cv hm hu hs (fun v => scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v))
  have hcg := fun z (hz : z ∈ Ioi ((s + e) * u)) => scOutC_k_cv hm he hw hu hs c₀ c₁ c₂ c₃ hz
  obtain ⟨i3, e3⟩ := scOutC_add3 (j1.const_mul c₁) (j2.const_mul (c₂ * (u / w)))
    (j3.const_mul (c₃ * (u / w) ^ 2))
  refine ⟨hiff.2 (i3.congr_fun (fun z hz => (hcg z hz).symm) measurableSet_Ioi), ?_⟩
  calc _ = ∫ z in Ioi ((s + e) * u), (c₁ * (1 / (z * (m - e * u + z))) +
        c₂ * (u / w) * (1 / (z ^ 2 * (m - e * u + z))) +
          c₃ * (u / w) ^ 2 * (1 / (z ^ 3 * (m - e * u + z)))) := by
        rw [hval]; exact setIntegral_congr_fun measurableSet_Ioi hcg
    _ = _ := e3
    _ = _ := by rw [integral_const_mul, integral_const_mul, integral_const_mul, w1, w2, w3]

/-- The `κ`-part, by the masters (`κ = 0` beyond the threshold). -/
theorem scOutC_kap_int (hm : 0 < m) (he : 0 < e) (hw : 0 < w) (hu : 0 < u) (hs : 0 ≤ s)
    (hM : m - e * u ≠ 0) (a₀ a₁ a₂ : ℝ) :
    IntegrableOn (fun v => scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2) (Ioi 0) ∧
      ∫ v in Ioi 0, scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2 =
        a₀ * (w / u) * (1 / (m - e * u + (s + e) * u)) +
          a₁ * (log (1 + (m - e * u) / ((s + e) * u)) / (m - e * u) ^ 2 -
            1 / ((m - e * u) * (m - e * u + (s + e) * u))) +
          a₂ * (u / w) * (1 / ((m - e * u) ^ 2 * ((s + e) * u)) -
            2 * log (1 + (m - e * u) / ((s + e) * u)) / (m - e * u) ^ 3 +
              1 / ((m - e * u) ^ 2 * (m - e * u + (s + e) * u))) := by
  have hc : 0 < (s + e) * u := by positivity
  have hMc : 0 < m - e * u + (s + e) * u := by nlinarith [mul_nonneg hs hu.le]
  obtain ⟨j0, w0⟩ := scOutCI0 hMc
  obtain ⟨j1, w1⟩ := scOutCI1 hM hc hMc
  obtain ⟨j2, w2⟩ := scOutCI2 hM hc hMc
  obtain ⟨hiff, hval⟩ := scOutC_cv hm hu hs
    (fun v => scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2)
  have hcg := fun z (hz : z ∈ Ioi ((s + e) * u)) => scOutC_kap_cv hm he hw hu hs a₀ a₁ a₂ hz
  obtain ⟨i3, e3⟩ := scOutC_add3 (j0.const_mul (a₀ * (w / u))) (j1.const_mul a₁)
    (j2.const_mul (a₂ * (u / w)))
  have hS : IntegrableOn (fun v => scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2) (scOutCS m s) :=
    hiff.2 (i3.congr_fun (fun z hz => (hcg z hz).symm) measurableSet_Ioi)
  have hR0 : EqOn (fun v => scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2) 0 (scOutCR m s) :=
    fun v hv => by
      have h' : ¬ s * v < m := not_lt.2 hv.2
      simp [scOutCkap, h']
  have hR : IntegrableOn (fun v => scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2)
      (scOutCR m s) := integrableOn_zero.congr_fun hR0.symm (measurableSet_scOutCR m s)
  rw [← scOutCS_union]
  refine ⟨hS.union hR, ?_⟩
  rw [setIntegral_union scOutCS_disjoint (measurableSet_scOutCR m s) hS hR,
    setIntegral_congr_fun (measurableSet_scOutCR m s) hR0]
  simp only [Pi.zero_apply, integral_zero, add_zero]
  calc _ = ∫ z in Ioi ((s + e) * u), (a₀ * (w / u) * (1 / (m - e * u + z) ^ 2) +
        a₁ * (1 / (z * (m - e * u + z) ^ 2)) +
          a₂ * (u / w) * (1 / (z ^ 2 * (m - e * u + z) ^ 2))) := by
        rw [hval]; exact setIntegral_congr_fun measurableSet_Ioi hcg
    _ = _ := e3
    _ = _ := by rw [integral_const_mul, integral_const_mul, integral_const_mul, w0, w1, w2]

/-- The `k`-part on `(0, ∞)`. -/
theorem scOutC_k_int (hm : 0 < m) (he : 0 < e) (hw : 0 < w) (hu : 0 < u) (hs : 0 ≤ s)
    (hM : m - e * u ≠ 0) (c₀ c₁ c₂ c₃ : ℝ) :
    IntegrableOn (fun v => scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)) (Ioi 0) ∧
      ∫ v in Ioi 0, scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v) =
        (∫ v in scOutCS m s, scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)) +
          -(c₀ * w) * ((log (m + s * u) - log m) / u) := by
  obtain ⟨iS, -⟩ := scOutC_k_S hm he hw hu hs hM c₀ c₁ c₂ c₃
  obtain ⟨iR, vR⟩ := scOutC_k_R (e := e) (w := w) hm hu hs c₀ c₁ c₂ c₃
  rw [← scOutCS_union]
  exact ⟨iS.union iR, by rw [setIntegral_union scOutCS_disjoint (measurableSet_scOutCR m s)
    iS iR, vR]⟩

/-- The weight is integrable against `(u + v)⁻²`, with integral `∫ k/(u + v) + ∫ κ/(u + v)²
+ P/u`. -/
theorem scOutCTg_integral (hm : 0 < m) (he : 0 < e) (hw : 0 < w) (hu : 0 < u) (hs : 0 ≤ s)
    (hM : m - e * u ≠ 0) (a₀ a₁ a₂ c₀ c₁ c₂ c₃ : ℝ) :
    IntegrableOn (fun v => scOutCTg a₀ a₁ a₂ c₀ c₁ c₂ c₃ m e w s v / (u + v) ^ 2) (Ioi 0) ∧
      ∫ v in Ioi 0, scOutCTg a₀ a₁ a₂ c₀ c₁ c₂ c₃ m e w s v / (u + v) ^ 2 =
        (∫ v in Ioi 0, scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)) +
          (∫ v in Ioi 0, scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2) +
            -(c₀ * w * log m) * (1 / u) := by
  obtain ⟨iK, vK⟩ := scOutC_ibp hu (measurable_scOutCk c₀ c₁ c₂ c₃ m e w s)
    (scOutC_k_int hm he hw hu hs hM c₀ c₁ c₂ c₃).1
  obtain ⟨iκ, -⟩ := scOutC_kap_int hm he hw hu hs hM a₀ a₁ a₂
  obtain ⟨i0, v0⟩ := scOutCI0 (M := u) (c := 0) (by simpa using hu)
  have i0' : IntegrableOn (fun v => -(c₀ * w * log m) * (1 / (u + v) ^ 2)) (Ioi 0) :=
    i0.const_mul _
  obtain ⟨i3, e3⟩ := scOutC_add3 iK iκ i0'
  have hcg : ∀ v, scOutCTg a₀ a₁ a₂ c₀ c₁ c₂ c₃ m e w s v / (u + v) ^ 2 =
      (∫ v' in Ioc 0 v, scOutCk c₀ c₁ c₂ c₃ m e w s v') / (u + v) ^ 2 +
        scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2 +
          -(c₀ * w * log m) * (1 / (u + v) ^ 2) := fun v => by
    unfold scOutCTg scOutCK
    ring
  simp only [hcg]
  refine ⟨i3, e3.trans ?_⟩
  rw [vK, integral_const_mul, v0, add_zero]

/-- **The `(u + v)⁻²`-representation of the outer-massive corner `b`-integral.** -/
theorem scOutC_cForm_eq (hm : 0 < m) (he : 0 < e) (hw : 0 < w) (hu : 0 < u) (hs : 0 ≤ s)
    (hM : m - e * u ≠ 0) (a₀ a₁ a₂ c₀ c₁ c₂ c₃ : ℝ) :
    cForm a₀ a₁ a₂ c₀ c₁ c₂ c₃ (w * (s + e)) (u / w) (m - e * u)
        (log (m - e * u + w * (s + e) * (u / w)))
        (log (1 + (m - e * u) / (w * (s + e) * (u / w)))) =
      ∫ v in Ioi 0, scOutCTg a₀ a₁ a₂ c₀ c₁ c₂ c₃ m e w s v / (u + v) ^ 2 := by
  rw [(scOutCTg_integral hm he hw hu hs hM a₀ a₁ a₂ c₀ c₁ c₂ c₃).2,
    (scOutC_k_int hm he hw hu hs hM c₀ c₁ c₂ c₃).2, (scOutC_k_S hm he hw hu hs hM c₀ c₁ c₂ c₃).2,
    (scOutC_kap_int hm he hw hu hs hM a₀ a₁ a₂).2]
  have hβh : w * (s + e) * (u / w) = (s + e) * u := by field_simp
  have hA : m - e * u + (s + e) * u = m + s * u := by ring
  rw [hβh, hA]
  set L := log (1 + (m - e * u) / ((s + e) * u))
  set M := m - e * u with hMdef
  have hsu : 0 < m + s * u := by nlinarith [mul_nonneg hs hu.le]
  have hc : 0 < (s + e) * u := by positivity
  have hMc : M + (s + e) * u = m + s * u := by rw [hMdef]; ring
  unfold cForm
  have hβh' : w * (s + e) * (u / w) = (s + e) * u := hβh
  rw [show M + w * (s + e) * (u / w) = m + s * u by rw [hβh']; exact hMc]
  have := hw.ne'
  have := hu.ne'
  have := hc.ne'
  have := hsu.ne'
  have : s + e ≠ 0 := by positivity
  field_simp
  ring

end

end QED.ChainProof.SetCK

end
