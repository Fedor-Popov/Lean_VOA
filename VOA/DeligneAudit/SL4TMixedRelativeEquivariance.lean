import VOA.DeligneAudit.SL4TMixedRelativeQuotient
import VOA.DeligneAudit.SL4TMixedCartanSymbols

/-! Compatibility of the mixed presentation with the last positive Cartan current. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial
attribute [local instance 2000] Fin.fintype Fin.instOfNat

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- Abstract power sums commute with every specialization of the five alphabets. -/
theorem mixedAlphabetPowerSum_specialization {R : Type*} [CommRing R] [Algebra ℂ R]
    (φ : MixedPoly →ₐ[ℂ] R) (i : Fin 5) (d s : ℕ) :
    mixedAlphabetPowerSum φ i d s =
      φ (mixedAlphabet i (powerSumOfCoeff d (fun k => (-1) ^ k * elementary k) s)) := by
  rw [powerSumOfCoeff_map, powerSumOfCoeff_map]
  simp only [mixedAlphabetPowerSum, mixedE, map_mul, map_pow, map_neg, map_one]

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The Grassmannian elementary presentation sends abstract sums to its named power sums. -/
theorem radicalGrassmannianAlphabet_abstractPowerSum (a b c : ℕ) (d : Fin 3 → ℕ)
    (j : Fin 3) (s : ℕ) :
    radicalGrassmannianAlphabet a b c d j
        (powerSumOfCoeff (d j) (fun k => (-1) ^ k * elementary k) s) =
      radicalGrassmannianPowerSum a b c d j s := by
  rw [radicalGrassmannianAlphabet_powerSum, powerSumOfCoeff_map]
  simp only [map_mul, map_pow, map_neg, map_one]

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The relative quotient map preserves every individual alphabet power sum. -/
theorem mixedToRadicalRelative_alphabetPowerSum (a b : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams a b d e₁ e₂)) (i : Fin 5) (n s : ℕ) :
    mixedToRadicalRelative a b d e₁ e₂ hv
        (mixedAlphabetPowerSum (mixedEvaluation (mixedLabelBlockParams a b d e₁ e₂)) i n s) =
      Ideal.Quotient.mk _ (mixedElementaryAlphabet a b a d e₁ e₂ i
        (powerSumOfCoeff n (fun k => (-1) ^ k * elementary k) s)) := by
  rw [mixedAlphabetPowerSum_specialization]
  change mixedToRadicalRelative a b d e₁ e₂ hv (Ideal.Quotient.mk _ _) = _
  rw [mixedToRadicalRelative_mk, mixedElementarySource_alphabet]

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The last Cartan symbol written in the five elementary polynomial alphabets. -/
def mixedLastCartanPolynomial (d₂ d₃ e₁ e₂ s : ℕ) : MixedPoly :=
  mixedAlphabet 3 (powerSumOfCoeff e₁ (fun k => (-1) ^ k * elementary k) s) +
    (mixedAlphabet 1 (powerSumOfCoeff d₂ (fun k => (-1) ^ k * elementary k) s) -
      mixedAlphabet 2 (powerSumOfCoeff d₃ (fun k => (-1) ^ k * elementary k) s) -
      mixedAlphabet 4 (powerSumOfCoeff e₂ (fun k => (-1) ^ k * elementary k) s))

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The universal Cartan polynomial specializes to the last Cartan power sum. -/
theorem mixedLastCartanPolynomial_specialization {R : Type*} [CommRing R] [Algebra ℂ R]
    (φ : MixedPoly →ₐ[ℂ] R) (d₂ d₃ e₁ e₂ s : ℕ) :
    φ (mixedLastCartanPolynomial d₂ d₃ e₁ e₂ s) =
      mixedLastCartanPowerSum φ d₂ d₃ e₁ e₂ s := by
  simp only [mixedLastCartanPolynomial, mixedLastCartanPowerSum, map_add, map_sub,
    mixedAlphabetPowerSum_specialization]

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The elementary substitution sends the universal polynomial to the retained Cartan symbol. -/
theorem mixedElementarySource_lastCartan (a b c : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ s : ℕ) :
    mixedElementarySource a b c d e₁ e₂
        (mixedLastCartanPolynomial (d 1) (d 2) e₁ e₂ (s + 1)) =
      secondLeviSourceCartanSymbol e₁ e₂ 1
        (radicalLeviPowerSum a b c d 1 (s + 1)) (s + 1) := by
  simp only [mixedLastCartanPolynomial, map_add, map_sub, mixedElementarySource_alphabet]
  apply Subtype.ext
  simp only [Subalgebra.coe_add, Subalgebra.coe_sub, mixedElementaryAlphabet,
    AlgHom.comp_apply, radicalGrassmannianAlphabet_abstractPowerSum]
  have hfirst := secondLeviElementaryAlphabet_powerSum
    (B := RadicalGrassmannianRing a b c d) e₁ e₂ 0 s
  have hsecond := secondLeviElementaryAlphabet_powerSum
    (B := RadicalGrassmannianRing a b c d) e₁ e₂ 1 s
  simp only [if_pos rfl, ite_true] at hfirst
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false] at hsecond
  rw [hfirst, hsecond]
  change secondLeviModePowerSum e₁ e₂ 0 (s + 1) +
      (MvPolynomial.C (radicalGrassmannianPowerSum a b c d 1 (s + 1)) -
        MvPolynomial.C (radicalGrassmannianPowerSum a b c d 2 (s + 1)) -
          secondLeviModePowerSum e₁ e₂ 1 (s + 1)) =
    MvPolynomial.C (radicalLeviPowerSum a b c d 1 (s + 1)) +
      (1 : ℂ) • secondLeviModePowerSum e₁ e₂ 0 (s + 1) -
        secondLeviModePowerSum e₁ e₂ 1 (s + 1)
  simp only [radicalLeviPowerSum, show (1 : Fin 2) ≠ 0 by decide, if_false,
    map_sub, one_smul]
  abel

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The mixed characteristic power sum becomes exactly the last Cartan source symbol. -/
theorem mixedToRadicalRelative_powerSum (a b : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams a b d e₁ e₂)) (s : ℕ) (hs : 0 < s) :
    mixedToRadicalRelative a b d e₁ e₂ hv
        (mixedPowerSum (mixedLabelBlockParams a b d e₁ e₂) s) =
      Ideal.Quotient.mk _
        (secondLeviSourceCartanSymbol e₁ e₂ 1 (radicalLeviPowerSum a b a d 1 s) s) := by
  obtain ⟨s, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  let q := mixedLabelBlockParams a b d e₁ e₂
  have hp : mixedPowerSum q (s + 1) = mixedEvaluation q
      (mixedLastCartanPolynomial (d 1) (d 2) e₁ e₂ (s + 1)) :=
    (mixedPowerSum_eq_lastCartan q hv (s + 1) (by omega)).trans
      (mixedLastCartanPolynomial_specialization (mixedEvaluation q)
        (d 1) (d 2) e₁ e₂ (s + 1)).symm
  refine (congrArg (mixedToRadicalRelative a b d e₁ e₂ hv) hp).trans ?_
  change mixedToRadicalRelative a b d e₁ e₂ hv (Ideal.Quotient.mk _ _) = _
  rw [mixedToRadicalRelative_mk]
  exact congrArg (Ideal.Quotient.mk _) (mixedElementarySource_lastCartan a b a d e₁ e₂ s)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedAlphabetPowerSum_specialization
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAlphabet_abstractPowerSum
#print axioms VOA.DeligneAudit.SL4T.mixedToRadicalRelative_alphabetPowerSum
#print axioms VOA.DeligneAudit.SL4T.mixedToRadicalRelative_powerSum

#print axioms VOA.DeligneAudit.SL4T.mixedLastCartanPolynomial_specialization
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_lastCartan
