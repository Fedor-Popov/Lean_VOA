import VOA.DeligneAudit.SL4TMiddleFlagAllTails
import VOA.DeligneAudit.SL4TPowerSumStableFlag
import VOA.DeligneAudit.SL4TMultiDoubledCount

/-! Power-sum-stable coefficient flags for arbitrary current cutoffs. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial
open VOA.DeligneAudit.CVsl2 (SL2 bal)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V}

/-- A coefficient flag is allowed to be stable only under the positive Cartan symbols. -/
structure MixedQuotientSubspaceFlag (q : MixedParams) (J : Ideal (MixedRing q))
    (M cost : ℕ) where
  length : ℕ
  vector : ℕ → MixedRing q ⧸ J
  space : ℕ → Submodule ℂ (MixedRing q ⧸ J)
  level : ℕ → ℕ
  zero : space 0 = ⊥
  top : space length = ⊤
  step : ∀ i < length, space (i + 1) = space i ⊔ ℂ ∙ vector i
  stable : ∀ i ≤ length, ∀ s, 1 ≤ s → ∀ a ∈ space i,
    Ideal.Quotient.mk J (mixedPowerSum q s) * a ∈ space i
  relation : ∀ i < length, ∃ p : (MixedRing q ⧸ J)[X],
    (∀ l, p.coeff l ∈ space i) ∧
    Polynomial.C (vector i) * X ^ (level i) + p ∈
      Ideal.span {(mixedCharacteristic q).map (Ideal.Quotient.mk J)} ⊔
        Ideal.span {X ^ M}
  bound : (∑ i ∈ Finset.range length,
    ((bal (mixedWeight q).toNat (level i)).map (· + 1)).prod) ≤ cost

/-- The concrete all-tail coefficient flag needed by the multi-doubled rank bound. -/
def MultiDoubledSiteCoefficientFlag (B k : ℕ) (q : MixedParams) : Prop :=
  Nonempty (MixedQuotientSubspaceFlag q (middleFlagAllTailIdeal q (B - k))
    (B - k) (multiDoubledSiteBlockBound B k q))

/-- A stable subspace flag in a killed coefficient quotient bounds the whole current image. -/
theorem mixedQuotientRingImage_bound_of_subspaceFlag
    (q : MixedParams) (hq : MixedValid q) (hS : SL2 E H F)
    (π : MixedRing q →ₗ[ℂ] V) (J : Ideal (MixedRing q))
    (hJ : J.restrictScalars ℂ ≤ LinearMap.ker π) (M cost : ℕ)
    (flag : MixedQuotientSubspaceFlag q J M cost)
    (hE : ∀ s φ, E s (π φ) = 0)
    (hH0 : ∀ φ, H 0 (π φ) = ((mixedWeight q).toNat : ℂ) • π φ)
    (hH : ∀ s, 1 ≤ s → ∀ φ, H s (π φ) = π (mixedPowerSum q s * φ))
    (hF0 : ∀ φ, (F 0 ^ ((mixedWeight q).toNat + 1)) (π φ) = 0)
    (hM : ∀ s, M ≤ s → ∀ φ, F s (π φ) = 0) :
    FiniteDimensional ℂ (currentSpan E H F (Set.range π)) ∧
      Module.finrank ℂ (currentSpan E H F (Set.range π)) ≤ cost := by
  let f := Ideal.Quotient.mkₐ ℂ J
  let ψ := multiplicityQuotientEvaluation π J hJ
  let p := fun s => f (mixedPowerSum q s)
  have heval (x : MixedRing q) : ψ (f x) = π x := rfl
  have hEq (s : ℕ) (x : MixedRing q ⧸ J) : E s (ψ x) = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J x
    exact hE s x
  have hHq (s : ℕ) (hs : 1 ≤ s) (x : MixedRing q ⧸ J) :
      H s (ψ x) = ψ (p s * x) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J x
    simpa only [p, ← map_mul, heval] using hH s hs x
  have hFq (x : MixedRing q ⧸ J) :
      (F 0 ^ ((mixedWeight q).toNat + 1)) (ψ x) = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J x
    exact hF0 x
  have htail (j : ℕ) (hj : (mixedWeight q).toNat < j) : newtonCoeff p j = 0 := by
    rw [newtonCoeff_map f, mixedPowerSum_newton_tail q hq j hj, map_zero]
  have hP := piCharacteristic_of_highest hS ψ p hEq hHq _ hFq htail
  have hpoly : descendingPoly (newtonCoeff p) (mixedWeight q).toNat =
      (mixedCharacteristic q).map f.toRingHom := by
    rw [← mixedPowerSum_descending q hq, descendingPoly_map]
    congr 1
    exact funext (newtonCoeff_map f (mixedPowerSum q))
  rw [hpoly] at hP
  obtain ⟨hf, hb⟩ := pi_subspaceFlag_bound_of_characteristic hS ψ p
    ((mixedCharacteristic q).map f.toRingHom) (mixedWeight q).toNat M flag.length
    flag.vector flag.space flag.level flag.zero flag.top flag.step flag.stable flag.relation
    (fun s hs => (mixedPowerSum_nilpotent q hq s hs).map f) hEq
    (fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J x
      exact hH0 x) hHq hFq
    (fun s hs x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J x
      exact hM s hs x) hP
  have hr : Set.range ψ = Set.range π := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J x
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨f x, rfl⟩
  rw [hr] at hf hb
  exact ⟨hf, hb.trans flag.bound⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.MixedQuotientSubspaceFlag
#print axioms VOA.DeligneAudit.SL4T.MultiDoubledSiteCoefficientFlag
#print axioms VOA.DeligneAudit.SL4T.mixedQuotientRingImage_bound_of_subspaceFlag
