/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.RepsIntDB
public import QED.ChainProof.RepsIntBDInt

/-!
# (T₉′) for the `δ₃`–bubble representatives of set (b)

Helper for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53): the value integrand of
`repDB s` satisfies (T₉′) at `ε > 0` under the Pauli–Villars conditions and momentum conservation
(`chainValueIntegrable_repDB`). The proof is that of `repBD s`
(`QED/ChainProof/RepsIntBDInt.lean`): the transverse part is the same sum over the `VP` shapes
with extra photon denominators, and the longitudinal part has the same five denominator shapes,
with the numerator `dbN` (the photon momentum contracted at `a` instead of `c`), which is the
contracted form of `refinedBound_contract` after exchanging two index sums (`dbN_eq_contract`).
-/

@[expose] public section

open MeasureTheory Complex

namespace QED.ChainProof.RepsInt

open QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit
  QED.ChainProof.Enum
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrix
  classVPMomenta RefinedBound IntNoSubdivergenceRefined)

/-- `dbN` in the contracted form, with the open-line indices exchanged. -/
theorem dbN_eq_contract (P : Params) (p kext : Fin 4 → ℝ) (μ α β : Fin 4) (k v : Fin 4 → ℝ) :
    dbN P p kext μ α β k v = ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
      bdON P p kext k μ b a α β * ((Minkowski.metric b c : ℝ) : ℂ) *
        ((Minkowski.lower k a : ℝ) : ℂ) * ((v c : ℝ) : ℂ) := by
  unfold dbN
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/-- The degree bound for a contracted numerator with any entries of degree at most two. -/
theorem isLoopPoly_contract' {K V : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ} (hK : IsLoopAffine K)
    (hV : IsLoopAffine V) (X : (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hX : ∀ l0 l2, IsLoopPoly 2 2 fun ℓ => X ℓ l0 l2) :
    IsLoopPoly 2 4 fun ℓ =>
      ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4, X ℓ l0 l2 * ((Minkowski.metric l2 l3 : ℝ) : ℂ) *
        ((Minkowski.lower (K ℓ) l0 : ℝ) : ℂ) * ((V ℓ l3 : ℝ) : ℂ) := by
  refine IsLoopPoly.sum _ fun l0 _ => IsLoopPoly.sum _ fun l2 _ => IsLoopPoly.sum _ fun l3 _ => ?_
  exact (((hX l0 l2).mul (IsLoopPoly.const (n := 0) _)).mul (isLoopPoly_lower hK l0)).mul
    (hV.isLoopPoly_coord l3)

/-- **A longitudinal piece of `repDB`**: as `jointEnergyFirstIntegrable_bdPiece`, with the
numerator `dbN`. -/
theorem jointEnergyFirstIntegrable_dbPiece (P : Params) {m : ℕ} (hm : 7 ≤ m)
    (σ : Fin (m + 1) → Fin 6) (Ms : Fin (m + 1) → ℝ) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ)
    (μ α β : Fin 4) (eV : Fin (m + 1)) {V : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ} (hV : IsLoopAffine V)
    (h0 : σ 0 = 0) (h1 : σ 1 = 1) (h2 : σ 2 = 4)
    (hVe : ∀ ℓ, V ℓ = classLineVP p (p + kext) (σ eV) ℓ) (h10 : (1 : Fin (m + 1)) ≠ 0)
    (h2E : (2 : Fin (m + 1)) ∉ ({1, 0} : Finset (Fin (m + 1))))
    (hVE : eV ∉ ({1, 0} : Finset (Fin (m + 1)))) (h2V : (2 : Fin (m + 1)) ≠ eV)
    (hcrit : IntNoSubdivergenceRefined 2 ({1, 0} ∪ {2} ∪ {eV}) fun i => class5LoopMatrix .VP (σ i))
    (κ : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      (κ * dbN P p kext μ α β (-ℓ 1) (V ℓ)) *
        ∏ i, (propDenom (Ms i) P.ε (classLineVP p (p + kext) (σ i) ℓ))⁻¹ := by
  set al := castLoopMatrix fun i => class5LoopMatrix .VP (σ i)
  set pp : Fin (m + 1) → Fin 4 → ℝ := fun i => classVPMomenta p (p + kext) (σ i)
  have hlm : ∀ e ℓ, lineMomentum al pp e ℓ = classLineVP p (p + kext) (σ e) ℓ := fun _ _ => rfl
  have r0 : ∀ ℓ, classLineVP p (p + kext) 0 ℓ = p - -ℓ 1 := fun ℓ => (classLineVP_rows _ _ ℓ).1
  have r1 : ∀ ℓ, classLineVP p (p + kext) 1 ℓ = p + kext - -ℓ 1 := fun ℓ =>
    (classLineVP_rows _ _ ℓ).2.1
  have r4 : ∀ ℓ, classLineVP p (p + kext) 4 ℓ = -ℓ 1 := fun ℓ =>
    (classLineVP_rows _ _ ℓ).2.2.2.2.1
  simp only [dbN_eq_contract]
  have hpoly : IsLoopPoly 2 4 fun ℓ => κ * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
      bdON P p kext (-ℓ 1) μ b a α β * ((Minkowski.metric b c : ℝ) : ℂ) *
        ((Minkowski.lower (-ℓ 1) a : ℝ) : ℂ) * ((V ℓ c : ℝ) : ℂ) := by
    refine IsLoopPoly.const_mul κ (isLoopPoly_contract' isLoopAffine_neg_one hV _ fun a b => ?_)
    unfold bdON
    have hm : IsLoopPolyMat 2 (0 + 1 + 0 + 1 + 0) fun ℓ : Fin 2 → Fin 4 → ℝ =>
        Dirac.gamma a * electronNumerator P.m (p + kext - -ℓ 1) * Dirac.gamma μ *
          electronNumerator P.m (p - -ℓ 1) * Dirac.gamma b :=
      ((((IsLoopPolyMat.const _).mul ((IsLoopAffine.const_sub' isLoopAffine_neg_one
        (p + kext)).isLoopPolyMat_electronNumerator P.m)).mul (IsLoopPolyMat.const _)).mul
          ((IsLoopAffine.const_sub' isLoopAffine_neg_one p).isLoopPolyMat_electronNumerator
            P.m)).mul (IsLoopPolyMat.const _)
    exact hm α β
  have hB : RefinedBound al ({1, 0} ∪ {2} ∪ {eV}) 4 fun ℓ => κ * ∑ a : Fin 4, ∑ b : Fin 4,
      ∑ c : Fin 4, bdON P p kext (-ℓ 1) μ b a α β * ((Minkowski.metric b c : ℝ) : ℂ) *
        ((Minkowski.lower (-ℓ 1) a : ℝ) : ℂ) * ((V ℓ c : ℝ) : ℂ) := by
    refine RefinedBound.const_mul κ ?_
    refine refinedBound_contract' al pp h2E hVE h2V (fun ℓ => -ℓ 1) V
      (fun ℓ => by rw [hlm, h2, r4]) (fun ℓ => by rw [hlm, hVe])
      (fun ℓ a b => bdON P p kext (-ℓ 1) μ b a α β) fun a b => ?_
    unfold bdON
    exact refinedBound_openNum al pp h10 P.m (fun ℓ => p + kext - -ℓ 1) (fun ℓ => p - -ℓ 1)
      (fun ℓ => by rw [hlm, h1, r1]) (fun ℓ => by rw [hlm, h0, r0]) _ _ _ α β
  exact jointEnergyFirstIntegrable_vpRows hm σ Ms hε p (p + kext) hcrit hpoly hB

section DBAssembly

open QED.TwoLoop.ClassIntegrable

variable (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (αOut βIn μ : Fin 1 → Fin 4)

/-- The value integrand of `repDB s` in the nested routing, in the class variables
`q = λ₀`, `k = -λ₁`. -/
noncomputable def dbG (s : Fin 2) (pIn kIn : Fin 1 → Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
    regulatedAmplitude₂ P (repDB s) pIn kIn (dbMom s (pIn 0) (kIn 0) (ℓ 0) (-ℓ 1)) αOut βIn μ

/-- **The integrand of `repDB s` as a sum of pieces** (for `ε ≠ 0`, the Pauli–Villars conditions
and momentum conservation): two sums over the `VP` shapes with one, resp. two, extra photon
denominators, and the five longitudinal pieces. -/
theorem dbG_eq (s : Fin 2) (hε : P.ε ≠ 0) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    dbG P αOut βIn μ s pIn kIn ℓ =
      ((((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * (-(P.δ₃ / 2 : ℂ)) *
          ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) *
        ∑ t : Fin 4, vpTermNumer P pOut pIn kIn αOut βIn μ t ℓ *
          ((∏ i : Fin 10, (vpDenom P t (pIn 0) (pOut 0) i ℓ)⁻¹) * (propDenom P.Λ P.ε (ℓ 1))⁻¹) +
      ((((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * (P.δ₃ / 2 : ℂ) *
          ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) * (((P.mγ ^ 2 : ℝ) : ℂ) - P.ε * I)) *
        ∑ t : Fin 4, vpTermNumer P pOut pIn kIn αOut βIn μ t ℓ *
          ((∏ i : Fin 10, (vpDenom P t (pIn 0) (pOut 0) i ℓ)⁻¹) *
            ((propDenom P.mγ P.ε (ℓ 1))⁻¹ * (propDenom P.Λ P.ε (ℓ 1))⁻¹)) +
      (bdκL P * dbN P (pIn 0) (kIn 0) (μ 0) (αOut 0) (βIn 0) (-ℓ 1) (ℓ 0)) *
        ∏ i, (propDenom (massL1 P i) P.ε (classLineVP (pIn 0) (pIn 0 + kIn 0) (lineL1 i) ℓ))⁻¹ +
      (-bdκL P * dbN P (pIn 0) (kIn 0) (μ 0) (αOut 0) (βIn 0) (-ℓ 1) (ℓ 0 + -ℓ 1)) *
        ∏ i, (propDenom (massL1 P i) P.ε (classLineVP (pIn 0) (pIn 0 + kIn 0) (lineL2 i) ℓ))⁻¹ +
      (-(bdκL P * ((P.ε : ℂ) * I)) * dbN P (pIn 0) (kIn 0) (μ 0) (αOut 0) (βIn 0) (-ℓ 1) (-ℓ 1)) *
        ∏ i, (propDenom (massL3a P i) P.ε
          (classLineVP (pIn 0) (pIn 0 + kIn 0) (lineL3a i) ℓ))⁻¹ +
      (-(bdκL P * ((P.ε : ℂ) * I)) * dbN P (pIn 0) (kIn 0) (μ 0) (αOut 0) (βIn 0) (-ℓ 1) (-ℓ 1)) *
        ∏ i, (propDenom (massL3b P i) P.ε
          (classLineVP (pIn 0) (pIn 0 + kIn 0) (lineL3b i) ℓ))⁻¹ +
      (-(bdκL P * ((P.ε : ℂ) * I)) * dbN P (pIn 0) (kIn 0) (μ 0) (αOut 0) (βIn 0) (-ℓ 1) (-ℓ 1)) *
        ∏ i, (propDenom (massL3c P i) P.ε
          (classLineVP (pIn 0) (pIn 0 + kIn 0) (lineL3c i) ℓ))⁻¹ := by
  obtain ⟨p1, p2, p3a, p3b, p3c⟩ := prod_lineL P (pIn 0) (pIn 0 + kIn 0) ℓ
  -- the vacuum-polarization part
  have hVP : ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
      contractionAmplitude₂ P QED.TwoLoop.NestedVP.cV (QED.TwoLoop.NestedVP.flavV f) pIn kIn
        (QED.TwoLoop.NestedVP.nestedMom (pIn 0) (kIn 0) (ℓ 0) (-ℓ 1)) αOut βIn μ =
      ∑ t : Fin 4, vpTermNumer P pOut pIn kIn αOut βIn μ t ℓ *
        ∏ i : Fin 10, (vpDenom P t (pIn 0) (pOut 0) i ℓ)⁻¹ := by
    rw [← QED.TwoLoop.NestedVP.regulatedAmplitude₂_nested,
      ← classMomVP_eq_nestedMom, ← hmom, regulatedAmplitude₂_classMomVP_shapes P hε hc₁ hc₂ hmom]
  -- the transverse coefficient
  have hDγ := propDenom_ne_zero (M := P.mγ) hε (ℓ 1)
  have hDΛ := propDenom_ne_zero (M := P.Λ) hε (ℓ 1)
  have hT : ((Minkowski.dot (-ℓ 1) (-ℓ 1) : ℝ) : ℂ) * photonScalar P.mγ P.Λ P.ε (-ℓ 1) =
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) * ((propDenom P.Λ P.ε (ℓ 1))⁻¹ -
        (((P.mγ ^ 2 : ℝ) : ℂ) - P.ε * I) *
          ((propDenom P.mγ P.ε (ℓ 1))⁻¹ * (propDenom P.Λ P.ε (ℓ 1))⁻¹)) := by
    have hs : photonScalar P.mγ P.Λ P.ε (-ℓ 1) =
        (propDenom P.mγ P.ε (ℓ 1))⁻¹ - (propDenom P.Λ P.ε (ℓ 1))⁻¹ := by
      rw [← propDenom_neg P.mγ P.ε (ℓ 1), ← propDenom_neg P.Λ P.ε (ℓ 1)]
      rfl
    have hdot : ((Minkowski.dot (-ℓ 1) (-ℓ 1) : ℝ) : ℂ) =
        propDenom P.mγ P.ε (ℓ 1) - (((P.mγ ^ 2 : ℝ) : ℂ) - P.ε * I) := by
      rw [← propDenom_neg P.mγ P.ε (ℓ 1)]
      simp only [propDenom]; push_cast; ring
    have hdiff : propDenom P.Λ P.ε (ℓ 1) - propDenom P.mγ P.ε (ℓ 1) =
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) := by
      simp only [propDenom]; push_cast; ring
    rw [hs, hdot, ← hdiff]
    field_simp
  -- the longitudinal part
  have hL := dbLong_sum P hε hc₁ hc₂ (pIn 0) (kIn 0) (ℓ 0) (-ℓ 1) (αOut 0) (βIn 0) (μ 0)
  unfold dbG
  rw [regulatedAmplitude₂_repDB]
  simp only [db_amplitude_split, mul_add, Finset.sum_add_distrib]
  rw [show ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
      ((-(P.δ₃ / 2 : ℂ) * (((Minkowski.dot (-ℓ 1) (-ℓ 1) : ℝ) : ℂ) *
        photonScalar P.mγ P.Λ P.ε (-ℓ 1))) *
        contractionAmplitude₂ P QED.TwoLoop.NestedVP.cV (QED.TwoLoop.NestedVP.flavV f) pIn kIn
          (QED.TwoLoop.NestedVP.nestedMom (pIn 0) (kIn 0) (ℓ 0) (-ℓ 1)) αOut βIn μ) =
      (-(P.δ₃ / 2 : ℂ) * (((Minkowski.dot (-ℓ 1) (-ℓ 1) : ℝ) : ℂ) *
        photonScalar P.mγ P.Λ P.ε (-ℓ 1))) * ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        contractionAmplitude₂ P QED.TwoLoop.NestedVP.cV (QED.TwoLoop.NestedVP.flavV f) pIn kIn
          (QED.TwoLoop.NestedVP.nestedMom (pIn 0) (kIn 0) (ℓ 0) (-ℓ 1)) αOut βIn μ by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
  rw [show ∑ f : Fin 3, (P.loopCoeff f : ℂ) * ((P.δ₃ / 2 : ℂ) *
      dbLong P f (pIn 0) (kIn 0) (ℓ 0) (-ℓ 1) (αOut 0) (βIn 0) (μ 0)) =
      (P.δ₃ / 2 : ℂ) * ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        dbLong P f (pIn 0) (kIn 0) (ℓ 0) (-ℓ 1) (αOut 0) (βIn 0) (μ 0) by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
  rw [hVP, hT, hL, p1, p2, p3a, p3b, p3c]
  simp only [Fin.sum_univ_four, bdκL]
  ring

/-- **(T₉′) for the `δ₃`–bubble representatives**: at `ε > 0`, under the two Pauli–Villars
conditions and momentum conservation, the value integrand of `repDB s` satisfies both stages of
the joint energy-first integral, for all masses, cutoffs and counterterms. -/
theorem chainValueIntegrable_repDB (hε : 0 < P.ε) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hmom : pOut 0 = pIn 0 + kIn 0)
    (s : Fin 2) : ChainValueIntegrable P (repDB s) pOut pIn kIn αOut βIn μ := by
  have hG : QED.TwoLoop.jointEnergyFirstIntegrable 2 (dbG P αOut βIn μ s pIn kIn) := by
    have h1 := jointEnergyFirstIntegrable_vpSum_ext1 P hε pOut pIn kIn αOut βIn μ
      ((((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * (-(P.δ₃ / 2 : ℂ)) *
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) P.Λ
    have h2 := jointEnergyFirstIntegrable_vpSum_ext2 P hε pOut pIn kIn αOut βIn μ
      ((((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * (P.δ₃ / 2 : ℂ) *
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) * (((P.mγ ^ 2 : ℝ) : ℂ) - P.ε * I)) P.mγ P.Λ
    obtain ⟨c1, c2, c3a, c3b, c3c⟩ := crit_L
    have hL1 := jointEnergyFirstIntegrable_dbPiece P (by norm_num) lineL1 (massL1 P) hε (pIn 0)
      (kIn 0) (μ 0) (αOut 0) (βIn 0) 8 isLoopAffine_zero' rfl rfl rfl
      (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.1.symm) (by decide) (by decide) (by decide)
      (by decide) c1 (bdκL P)
    have hL2 := jointEnergyFirstIntegrable_dbPiece P (by norm_num) lineL2 (massL1 P) hε (pIn 0)
      (kIn 0) (μ 0) (αOut 0) (βIn 0) 8 (IsLoopAffine.add' isLoopAffine_zero' isLoopAffine_neg_one)
      rfl rfl rfl (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.1.symm) (by decide) (by decide)
      (by decide) (by decide) c2 (-bdκL P)
    have hL3a := jointEnergyFirstIntegrable_dbPiece P (by norm_num) lineL3a (massL3a P) hε (pIn 0)
      (kIn 0) (μ 0) (αOut 0) (βIn 0) 3 isLoopAffine_neg_one rfl rfl rfl
      (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm) (by decide) (by decide) (by decide)
      (by decide) c3a (-(bdκL P * ((P.ε : ℂ) * I)))
    have hL3b := jointEnergyFirstIntegrable_dbPiece P (by norm_num) lineL3b (massL3b P) hε (pIn 0)
      (kIn 0) (μ 0) (αOut 0) (βIn 0) 3 isLoopAffine_neg_one rfl rfl rfl
      (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm) (by decide) (by decide) (by decide)
      (by decide) c3b (-(bdκL P * ((P.ε : ℂ) * I)))
    have hL3c := jointEnergyFirstIntegrable_dbPiece P (by norm_num) lineL3c (massL3c P) hε (pIn 0)
      (kIn 0) (μ 0) (αOut 0) (βIn 0) 3 isLoopAffine_neg_one rfl rfl rfl
      (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm) (by decide) (by decide) (by decide)
      (by decide) c3c (-(bdκL P * ((P.ε : ℂ) * I)))
    have hsum := jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add
      (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add
        (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add h1 h2) hL1) hL2) hL3a)
          hL3b) hL3c
    refine (congrArg (QED.TwoLoop.jointEnergyFirstIntegrable 2) (funext fun ℓ => ?_)).mp hsum
    rw [dbG_eq P αOut βIn μ s hε.ne' hc₁ hc₂ hmom ℓ]
  unfold ChainValueIntegrable
  rw [loopCount_repDB]
  refine QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_of_matAct !![1, 1; 1, 0]
    (by rw [Matrix.det_fin_two]; simp) ![-(pIn 0), -(pIn 0)] hG fun ℓ => ?_
  rw [lineMomentum₂_repDB s hmom, dbG]
  congr 3
  · funext ν
    simp [QED.TwoLoop.Relabel.matAct, Fin.sum_univ_two]
    ring
  · funext ν
    simp [QED.TwoLoop.Relabel.matAct, Fin.sum_univ_two]
    ring

end DBAssembly

end QED.ChainProof.RepsInt

end
