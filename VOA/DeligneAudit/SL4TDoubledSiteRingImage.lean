import VOA.DeligneAudit.SL4TTruncatedMultiplicityQuotient
import VOA.DeligneAudit.SL4TDoubledSiteCount

/-! The ring-image bound with an independent cutoff and a quotient spanning filtration. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial VOA.DeligneAudit.CVsl2

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V}

/-- Garland and the cell bound descend through any killed coefficient ideal at any cutoff. -/
theorem mixedQuotientRingImage_bound_of_chain
    (q : MixedParams) (hq : MixedValid q) (hS : SL2 E H F)
    (π : MixedRing q →ₗ[ℂ] V) (I : Ideal (MixedRing q))
    (hI : I.restrictScalars ℂ ≤ LinearMap.ker π) (M : ℕ) (ns : List ℕ)
    (hchain : SpanningChain
      (Ideal.span {(mixedCharacteristic q).map (Ideal.Quotient.mk I)} ⊔
        Ideal.span {(X : (MixedRing q ⧸ I)[X]) ^ M}) ⊥ ⊤ ns)
    (hE : ∀ s φ, E s (π φ) = 0)
    (hH0 : ∀ φ, H 0 (π φ) = ((mixedWeight q).toNat : ℂ) • π φ)
    (hH : ∀ s, 1 ≤ s → ∀ φ, H s (π φ) = π (mixedPowerSum q s * φ))
    (hF0 : ∀ φ, (F 0 ^ ((mixedWeight q).toNat + 1)) (π φ) = 0)
    (hM : ∀ s, M ≤ s → ∀ φ, F s (π φ) = 0) :
    FiniteDimensional ℂ (currentSpan E H F (Set.range π)) ∧
      Module.finrank ℂ (currentSpan E H F (Set.range π)) ≤
        ∑ i ∈ Finset.range ns.length,
          ((bal (mixedWeight q).toNat (ns.getD i 0)).map (· + 1)).prod := by
  let f := Ideal.Quotient.mkₐ ℂ I
  let ψ := multiplicityQuotientEvaluation π I hI
  let p := fun s => f (mixedPowerSum q s)
  have heval (x : MixedRing q) : ψ (f x) = π x := rfl
  have hEq (s : ℕ) (x : MixedRing q ⧸ I) : E s (ψ x) = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I x
    exact hE s x
  have hHq (s : ℕ) (hs : 1 ≤ s) (x : MixedRing q ⧸ I) :
      H s (ψ x) = ψ (p s * x) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I x
    simpa only [p, ← map_mul, heval] using hH s hs x
  have hFq (x : MixedRing q ⧸ I) :
      (F 0 ^ ((mixedWeight q).toNat + 1)) (ψ x) = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I x
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
  have hb := SpanningChain.pi_bound_of_characteristic hS ψ p
    ((mixedCharacteristic q).map f.toRingHom) (mixedWeight q).toNat M hchain
    (fun s hs => (mixedPowerSum_nilpotent q hq s hs).map f) hEq
    (fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I x
      exact hH0 x) hHq hFq
    (fun s hs x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I x
      exact hM s hs x) hP
  have hr : Set.range ψ = Set.range π := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I x
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨f x, rfl⟩
  rw [hr] at hb
  exact hb

/-- The sum of balanced contributions in a single doubled-site block is its catalog mass. -/
theorem doubledSiteFiber_balanced_sum (B : ℕ) (q : MixedParams) :
    let ns := (mixedCatalogFiber q (doubledSiteCellCatalog (B - 2))).map mixedCellLevel
    (∑ i ∈ Finset.range ns.length,
      ((bal (mixedWeight q).toNat (ns.getD i 0)).map (· + 1)).prod) =
        doubledSiteBlockBound B q := by
  dsimp only
  rw [list_sum_getD _ (fun n => ((bal (mixedWeight q).toNat n).map (· + 1)).prod)]
  unfold doubledSiteBlockBound
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  obtain ⟨d, hd, he⟩ := List.mem_filterMap.mp hc
  by_cases hq : d.1 = q
  · simp only [hq, if_true, Option.some.injEq] at he
    rw [← he, ← hq]
    exact doubledSiteCellCatalog_balanced (B - 2) d hd
  · simp [hq] at he

/-- The ideal of positive flag-block tails at a specified cutoff. -/
def middleFlagTailIdeal (q : MixedParams) (N : ℕ) : Ideal (MixedRing q) :=
  Ideal.span (Set.range (middleFlagTailSymbols q N))

/-- The quotient spanning filtration with the shortened cutoff and ordered catalog levels. -/
def DoubledSiteSpanningFiltration (B : ℕ) (q : MixedParams) : Prop :=
  SpanningChain
    (Ideal.span {(mixedCharacteristic q).map
      (Ideal.Quotient.mk (middleFlagTailIdeal q (B - 1)))} ⊔
        Ideal.span {(X : (MixedRing q ⧸ middleFlagTailIdeal q (B - 1))[X]) ^ (B - 1)})
    ⊥ ⊤ ((mixedCatalogFiber q (doubledSiteCellCatalog (B - 2))).map mixedCellLevel)

/-- A doubled-site quotient flag gives the precise block bound at the shorter cutoff. -/
theorem doubledSiteRingImage_bound_of_chain
    (B : ℕ) (q : MixedParams) (hq : MixedValid q) (hS : SL2 E H F)
    (π : MixedRing q →ₗ[ℂ] V)
    (hI : (middleFlagTailIdeal q (B - 1)).restrictScalars ℂ ≤ LinearMap.ker π)
    (hchain : DoubledSiteSpanningFiltration B q)
    (hE : ∀ s φ, E s (π φ) = 0)
    (hH0 : ∀ φ, H 0 (π φ) = ((mixedWeight q).toNat : ℂ) • π φ)
    (hH : ∀ s, 1 ≤ s → ∀ φ, H s (π φ) = π (mixedPowerSum q s * φ))
    (hF0 : ∀ φ, (F 0 ^ ((mixedWeight q).toNat + 1)) (π φ) = 0)
    (hM : ∀ s, B - 1 ≤ s → ∀ φ, F s (π φ) = 0) :
    FiniteDimensional ℂ (currentSpan E H F (Set.range π)) ∧
      Module.finrank ℂ (currentSpan E H F (Set.range π)) ≤ doubledSiteBlockBound B q := by
  obtain ⟨hf, hb⟩ := mixedQuotientRingImage_bound_of_chain q hq hS π
    (middleFlagTailIdeal q (B - 1)) hI (B - 1) _ hchain hE hH0 hH hF0 hM
  exact ⟨hf, hb.trans_eq (doubledSiteFiber_balanced_sum B q)⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedQuotientRingImage_bound_of_chain
#print axioms VOA.DeligneAudit.SL4T.doubledSiteFiber_balanced_sum
#print axioms VOA.DeligneAudit.SL4T.doubledSiteRingImage_bound_of_chain
