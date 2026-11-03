import VOA.DeligneAudit.SL4TRadicalGrassmannianDescent

/-! Power sums and surjectivity of the three-Grassmannian multiplicity presentation. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open scoped TensorProduct

attribute [local instance 2000] Fin.fintype Fin.instOfNat

/-- The inverse Newton recursion commutes with algebra homomorphisms. -/
theorem powerSumOfCoeff_map {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℂ R] [Algebra ℂ S] (f : R →ₐ[ℂ] S) (d : ℕ) (e : ℕ → R) (s : ℕ) :
    f (powerSumOfCoeff d e s) = powerSumOfCoeff d (fun k => f (e k)) s := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    cases s with
    | zero => simp [powerSumOfCoeff]
    | succ s =>
      simp only [powerSumOfCoeff, map_sub, map_smul, map_sum, map_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih _ (by omega)]

/-- Positive power sums regarded as elements of their generated algebra. -/
def radicalPositivePowerSum (d : Fin 3 → ℕ) (j : Fin 3) (s : ℕ) :
    radicalPowerSumAlgebra d :=
  ⟨radicalModePowerSum d j (s + 1), Algebra.subset_adjoin ⟨(j, s), rfl⟩⟩

/-- Abstract elementary power sums specialize to positional power sums. -/
theorem radicalElementaryModes_powerSum (d : Fin 3 → ℕ) (j : Fin 3) (s : ℕ) :
    radicalElementaryModes d j
      (powerSumOfCoeff (d j) (fun k => (-1) ^ k * elementary k) (s + 1)) =
        radicalPositivePowerSum d j s := by
  apply Subtype.ext
  rw [radicalElementaryModes_val, powerSumOfCoeff_map]
  simp only [map_mul, map_pow, map_neg, map_one, elementarySpecialization_elementary]
  have he := powerSumOfCoeff_psum_map (Fin (d j)) (AlgHom.id ℂ _) (d j) (s + 1)
    (by omega)
  simp only [AlgHom.id_apply] at he
  rw [he]
  exact (radicalModePowerSum_eq_rename d j (s + 1)).symm

/-- Each Grassmannian power sum maps to the class of the corresponding positional sum. -/
theorem radicalGrassmannianFactor_powerSum {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule bracketTable V) (w : V) (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (j : Fin 3) (s : ℕ) :
    radicalGrassmannianFactor ρ w a b c h d j
      (grassmannianPowerSum (d j) (weightABC a b c j) (s + 1)) =
        Ideal.Quotient.mk _ (radicalPositivePowerSum d j s) := by
  have he : grassmannianPowerSum (d j) (weightABC a b c j) (s + 1) =
      (Ideal.Quotient.mkₐ ℂ (grassIdeal (d j) (weightABC a b c j - d j)))
        (powerSumOfCoeff (d j) (fun k => (-1) ^ k * elementary k) (s + 1)) := by
    rw [powerSumOfCoeff_map]
    simp only [grassmannianPowerSum, map_mul, map_pow, map_neg, map_one]
    rfl
  rw [he, Ideal.Quotient.mkₐ_eq_mk, radicalGrassmannianFactor_mk,
    radicalElementaryModes_powerSum]

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)
variable (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))

/-- The three tensor-product power sums give exactly the three alphabet classes. -/
theorem radicalGrassmannianQuotientMap_powerSum (d : Fin 3 → ℕ) (j : Fin 3) (s : ℕ) :
    radicalGrassmannianQuotientMap ρ w a b c h d
      (radicalGrassmannianPowerSum a b c d j (s + 1)) =
        Ideal.Quotient.mk _ (radicalPositivePowerSum d j s) := by
  fin_cases j <;>
    simp only [radicalGrassmannianPowerSum, radicalGrassmannianQuotientMap,
      Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one]
  all_goals exact radicalGrassmannianFactor_powerSum ρ w a b c h d _ s

/-- Positive power-sum generation makes the three-Grassmannian quotient map surjective. -/
theorem radicalGrassmannianQuotientMap_surjective (d : Fin 3 → ℕ) :
    Function.Surjective (radicalGrassmannianQuotientMap ρ w a b c h d) := by
  let φ := radicalGrassmannianQuotientMap ρ w a b c h d
  let q := Ideal.Quotient.mkₐ ℂ (radicalMultiplicityRelationIdeal ρ w a b c h d)
  let S := φ.range.comap q
  have hle : radicalPowerSumAlgebra d ≤ S.map (radicalPowerSumAlgebra d).val := by
    apply Algebra.adjoin_le
    rintro P ⟨⟨j, s⟩, rfl⟩
    apply Subalgebra.mem_map.mpr
    refine ⟨radicalPositivePowerSum d j s, ?_, rfl⟩
    exact ⟨radicalGrassmannianPowerSum a b c d j (s + 1),
      radicalGrassmannianQuotientMap_powerSum ρ w a b c h d j s⟩
  intro v
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ
    (radicalMultiplicityRelationIdeal ρ w a b c h d) v
  obtain ⟨Q, hQ, he⟩ := Subalgebra.mem_map.mp (hle P.property)
  have heq : Q = P := Subtype.ext he
  subst Q
  exact hQ

/-- The actual first Levi multiplicity is a quotient of the three Grassmannian rings. -/
theorem radicalGrassmannianEvaluation_surjective (d : Fin 3 → ℕ) :
    Function.Surjective (radicalGrassmannianEvaluation ρ w a b c h d) :=
  (radicalRelationQuotientEvaluation_surjective ρ w a b c h d).comp
    (radicalGrassmannianQuotientMap_surjective ρ w a b c h d)

set_option synthInstance.maxHeartbeats 100000 in
-- Nested tensor-product ring instances exceed the default synthesis budget during rewriting.
/-- Positive alphabet Cartan currents are multiplication by the Grassmannian power sums. -/
theorem radicalGrassmannianEvaluation_powerSum (d : Fin 3 → ℕ) (j : Fin 3)
    (s : ℕ) (hs : 0 < s) (φ : RadicalGrassmannianRing a b c d) :
    radicalAlphabetQuotCurrent ρ w a b c h d j s
      (radicalGrassmannianEvaluation ρ w a b c h d φ :
        V ⧸ higherRadicalCountClosure ρ w d) =
      (radicalGrassmannianEvaluation ρ w a b c h d
        (radicalGrassmannianPowerSum a b c d j s * φ) :
          V ⧸ higherRadicalCountClosure ρ w d) := by
  obtain ⟨s, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  obtain ⟨P, hP⟩ := Ideal.Quotient.mkₐ_surjective ℂ
    (radicalMultiplicityRelationIdeal ρ w a b c h d)
      (radicalGrassmannianQuotientMap ρ w a b c h d φ)
  simp only [radicalGrassmannianEvaluation, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, map_mul, radicalGrassmannianQuotientMap_powerSum, ← hP]
  change radicalAlphabetQuotCurrent ρ w a b c h d j (s + 1)
      (radicalMultiplicityEvaluation ρ w d P : V ⧸ higherRadicalCountClosure ρ w d) =
    (radicalRelationQuotientEvaluation ρ w a b c h d
      (Ideal.Quotient.mk _ (radicalPositivePowerSum d j s) * Ideal.Quotient.mk _ P) :
        V ⧸ higherRadicalCountClosure ρ w d)
  rw [← map_mul, radicalRelationQuotientEvaluation_mk]
  exact radicalMultiplicityEvaluation_powerSum ρ w a b c h d j (s + 1) (by omega) P

/-- The first Levi presentation holds at every dominant weight and every count triple. -/
theorem radicalGrassmannianPresentation (d : Fin 3 → ℕ) :
    RadicalGrassmannianPresentation ρ w a b c h d :=
  ⟨radicalGrassmannianEvaluation ρ w a b c h d,
    radicalGrassmannianEvaluation_surjective ρ w a b c h d,
    radicalGrassmannianEvaluation_powerSum ρ w a b c h d⟩

include h in
/-- Supported first Levi multiplicities have the product-of-binomials upper bound. -/
theorem radicalCountMultiplicity_rank_le (d : Fin 3 → ℕ)
    (h₀ : d 0 ≤ a) (h₁ : d 1 ≤ b) (h₂ : d 2 ≤ c) :
    Module.finrank ℂ (radicalCountMultiplicity ρ w d) ≤
      a.choose (d 0) * b.choose (d 1) * c.choose (d 2) := by
  obtain ⟨hf, hr⟩ := radicalGrassmannianRing_finite_rank_le a b c d h₀ h₁ h₂
  letI := hf
  exact (LinearMap.finrank_le_finrank_of_surjective
    (radicalGrassmannianEvaluation_surjective ρ w a b c h d)).trans hr

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.powerSumOfCoeff_map
#print axioms VOA.DeligneAudit.SL4T.radicalElementaryModes_powerSum
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianFactor_powerSum
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianQuotientMap_powerSum
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianQuotientMap_surjective
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianEvaluation_powerSum
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianPresentation
#print axioms VOA.DeligneAudit.SL4T.radicalCountMultiplicity_rank_le
