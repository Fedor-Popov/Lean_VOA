import VOA.DeligneAudit.SL4TTruncatedCartanKernel

/-! High power sums vanish on the actual polynomial multiplicity sources at both Levi stages. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

variable {σ B V : Type*} [CommRing B] [Algebra ℂ B]
variable [AddCommGroup V] [Module ℂ V]

/-- A mode product containing a current above the cutoff is zero. -/
theorem positionModeProduct_zero_of_cutoff (F : σ → ℕ → Module.End ℂ V) (M : ℕ)
    (ht : ∀ i s, M ≤ s → F i s = 0) (is : List σ) (u : σ → ℕ)
    (i : σ) (hi : i ∈ is) (hu : M ≤ u i) : positionModeProduct F is u = 0 := by
  induction is with
  | nil => simp at hi
  | cons j js ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · simp [positionModeProduct, ht i (u i) hu]
    · change F j (u j) * positionModeProduct F js u = 0
      rw [ih hi, mul_zero]

/-- A high positional power kills every coefficient polynomial under mode evaluation. -/
theorem positionModeEvaluation_variable_tail (F : σ → ℕ → Module.End ℂ V)
    (is : List σ) (β : B →ₗ[ℂ] V) (M : ℕ) (ht : ∀ i s, M ≤ s → F i s = 0)
    (i : σ) (hi : i ∈ is) (s : ℕ) (hs : M ≤ s) (P : MvPolynomial σ B) :
    positionModeEvaluation F is β (X i ^ s * P) = 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u b =>
    rw [X_pow_eq_monomial, monomial_mul, one_mul, positionModeEvaluation_monomial]
    rw [positionModeProduct_zero_of_cutoff F M ht is _ i hi (by simp; omega)]
    rfl
  | add P Q hP hQ => simp only [mul_add, map_add, hP, hQ, add_zero]

/-- A base relation valid on every coefficient remains valid after arbitrary lowering words. -/
theorem positionModeEvaluation_base_relation (F : σ → ℕ → Module.End ℂ V)
    (is : List σ) (β : B →ₗ[ℂ] V) (b : B) (hb : ∀ c, β (b * c) = 0)
    (P : MvPolynomial σ B) : positionModeEvaluation F is β (MvPolynomial.C b * P) = 0 := by
  induction P using MvPolynomial.induction_on' with
  | monomial u c => rw [C_mul_monomial, positionModeEvaluation_monomial, hb c, map_zero]
  | add P Q hP hQ => simp only [mul_add, map_add, hP, hQ, add_zero]

variable {B V : Type} [CommRing B] [Algebra ℂ B]
variable [AddCommGroup V] [Module ℂ V]

/-- Each high power sum in either second-stage alphabet vanishes with every multiplier. -/
theorem secondLeviModeEvaluation_powerSum_tail
    (Q : CurrentModule VOA.AffineSl3.bracketTable V) (β : B →ₗ[ℂ] V)
    (M : ℕ) (ht : ∀ i s v, M ≤ s → Q.op i s v = 0)
    (e₁ e₂ : ℕ) (j : Fin 2) (s : ℕ) (hs : M ≤ s)
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) B) :
    secondLeviModeEvaluation Q β e₁ e₂ (secondLeviModePowerSum e₁ e₂ j s * P) = 0 := by
  classical
  have hF (i : SecondLeviModeSlot e₁ e₂) (n : ℕ) (hn : M ≤ n) :
      secondLeviPositionOperator Q e₁ e₂ i n = 0 := by
    ext v
    cases i <;> exact ht _ n v hn
  unfold secondLeviModePowerSum
  split_ifs <;> rw [Finset.sum_mul, map_sum] <;> apply Finset.sum_eq_zero
  · intro i _
    exact positionModeEvaluation_variable_tail _ _ β M hF (.inl i)
      (by simp [secondLeviModePositions]) s hs P
  · intro i _
    exact positionModeEvaluation_variable_tail _ _ β M hF (.inr i)
      (by simp [secondLeviModePositions]) s hs P

variable (ρ : CurrentModule bracketTable V) (w : V)
variable (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))
variable (M : ℕ) (ht : ∀ i s v, M ≤ s → ρ.op i s v = 0)

include ht

/-- Every separated alphabet Cartan also vanishes above the original current cutoff. -/
theorem radicalAlphabetQuotCurrent_truncated (d : Fin 3 → ℕ) (j : Fin 3)
    (s : ℕ) (hs : M ≤ s) (v : V ⧸ higherRadicalCountClosure ρ w d) :
    radicalAlphabetQuotCurrent ρ w a b c h d j s v = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ v
  rw [radicalAlphabetQuotCurrent_mk]
  have hz : radicalAlphabetCurrent ρ j s v = 0 := by
    simp only [radicalAlphabetCurrent, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.neg_apply, ht _ s v hs, neg_zero, smul_zero, add_zero]
  rw [hz, map_zero]

set_option synthInstance.maxHeartbeats 100000 in
-- The evaluator expands nested tensor-product coefficient algebras.
/-- High Grassmannian power sums annihilate every first-stage multiplicity input. -/
theorem radicalGrassmannianAmbientEvaluation_powerSum_tail (d : Fin 3 → ℕ)
    (j : Fin 3) (s : ℕ) (hs : M ≤ s) (hpos : 0 < s)
    (φ : RadicalGrassmannianRing a b c d) :
    radicalGrassmannianAmbientEvaluation ρ w a b c h d
      (radicalGrassmannianPowerSum a b c d j s * φ) = 0 := by
  change (radicalGrassmannianEvaluation ρ w a b c h d
    (radicalGrassmannianPowerSum a b c d j s * φ)).val = 0
  rw [← radicalGrassmannianEvaluation_powerSum ρ w a b c h d j s hpos φ]
  exact radicalAlphabetQuotCurrent_truncated ρ w a b c h M ht d j s hs _

set_option synthInstance.maxHeartbeats 100000 in
-- All five source alphabets share the same nested tensor-product coefficient algebra.
/-- Every abstract alphabet tail is killed on the complete second-stage polynomial source. -/
theorem mixedElementaryAlphabet_evaluation_tail (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (i : Fin 5) (s : ℕ) (hs : M ≤ s) (hpos : 0 < s)
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) (RadicalGrassmannianRing a b c d)) :
    secondLeviModeEvaluation (radicalCountQuotCurrent ρ w d)
      (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂
      ((mixedElementaryAlphabet a b c d e₁ e₂ i
        (powerSumOfCoeff (![d 0, d 1, d 2, e₁, e₂] i)
          (fun k => (-1) ^ k * elementary k) s)).val * P) = 0 := by
  obtain ⟨s, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  have hbase (j : Fin 3) :
      secondLeviModeEvaluation (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂
        (MvPolynomial.C (radicalGrassmannianPowerSum a b c d j (s + 1)) * P) = 0 :=
    positionModeEvaluation_base_relation _ _ _ _
      (radicalGrassmannianAmbientEvaluation_powerSum_tail
        ρ w a b c h M ht d j (s + 1) hs (by omega)) P
  have hmode (j : Fin 2) :
      secondLeviModeEvaluation (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂
        (secondLeviModePowerSum e₁ e₂ j (s + 1) * P) = 0 :=
    secondLeviModeEvaluation_powerSum_tail _ _ M
      (fun i n v hn => radicalCountQuot_truncated ρ w M ht d i n hn v)
      e₁ e₂ j (s + 1) hs P
  fin_cases i
  · change secondLeviModeEvaluation _ _ e₁ e₂
      (MvPolynomial.C (radicalGrassmannianAlphabet a b c d 0
        (powerSumOfCoeff (d 0) (fun k => (-1) ^ k * elementary k) (s + 1))) * P) = 0
    rw [radicalGrassmannianAlphabet_abstractPowerSum]
    exact hbase 0
  · change secondLeviModeEvaluation _ _ e₁ e₂
      (MvPolynomial.C (radicalGrassmannianAlphabet a b c d 1
        (powerSumOfCoeff (d 1) (fun k => (-1) ^ k * elementary k) (s + 1))) * P) = 0
    rw [radicalGrassmannianAlphabet_abstractPowerSum]
    exact hbase 1
  · change secondLeviModeEvaluation _ _ e₁ e₂
      (MvPolynomial.C (radicalGrassmannianAlphabet a b c d 2
        (powerSumOfCoeff (d 2) (fun k => (-1) ^ k * elementary k) (s + 1))) * P) = 0
    rw [radicalGrassmannianAlphabet_abstractPowerSum]
    exact hbase 2
  · change secondLeviModeEvaluation _ _ e₁ e₂
      ((secondLeviElementaryAlphabet e₁ e₂ 0
        (powerSumOfCoeff (if (0 : Fin 2) = 0 then e₁ else e₂)
          (fun k => (-1) ^ k * elementary k) (s + 1))).val * P) = 0
    rw [secondLeviElementaryAlphabet_powerSum]
    exact hmode 0
  · change secondLeviModeEvaluation _ _ e₁ e₂
      ((secondLeviElementaryAlphabet e₁ e₂ 1
        (powerSumOfCoeff (if (1 : Fin 2) = 0 then e₁ else e₂)
          (fun k => (-1) ^ k * elementary k) (s + 1))).val * P) = 0
    rw [secondLeviElementaryAlphabet_powerSum]
    exact hmode 1

set_option maxHeartbeats 800000 in
-- Descent expands two quotient maps over a tensor-product coefficient algebra.
set_option synthInstance.maxHeartbeats 100000 in
/-- All five alphabet tails vanish under the actual mixed-ring multiplicity evaluation. -/
theorem mixedSecondLeviEvaluation_alphabetPowerSum_tail
    (h : LocalWeylRel ρ w (weightABC a b a))
    (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams a b d e₁ e₂))
    (i : Fin 5) (s : ℕ) (hs : M ≤ s) (hpos : 0 < s)
    (φ : MixedRing (mixedLabelBlockParams a b d e₁ e₂)) :
    mixedSecondLeviEvaluation ρ w a b h d e₁ e₂ hv
      (mixedAlphabetPowerSum (mixedEvaluation (mixedLabelBlockParams a b d e₁ e₂))
        i (mixedLengths (mixedLabelBlockParams a b d e₁ e₂) i) s * φ) = 0 := by
  unfold mixedSecondLeviEvaluation
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul,
    mixedToRadicalRelative_alphabetPowerSum]
  obtain ⟨P, hP⟩ := Ideal.Quotient.mk_surjective (mixedToRadicalRelative a b d e₁ e₂ hv φ)
  rw [← hP, ← map_mul, radicalSecondLeviRelativeEvaluation_mk]
  apply Subtype.ext
  change Submodule.mkQ _ (secondLeviModeEvaluation _ _ e₁ e₂ (_ * P.val)) = 0
  rw [show mixedLengths (mixedLabelBlockParams a b d e₁ e₂) =
    ![d 0, d 1, d 2, e₁, e₂] by simp [mixedLengths, mixedLabelBlockParams]]
  rw [mixedElementaryAlphabet_evaluation_tail ρ w a b a h M ht d e₁ e₂ i s hs hpos P.val]
  exact map_zero _

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.positionModeProduct_zero_of_cutoff
#print axioms VOA.DeligneAudit.SL4T.positionModeEvaluation_variable_tail
#print axioms VOA.DeligneAudit.SL4T.positionModeEvaluation_base_relation
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_powerSum_tail
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetQuotCurrent_truncated
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAmbientEvaluation_powerSum_tail
#print axioms VOA.DeligneAudit.SL4T.mixedElementaryAlphabet_evaluation_tail
#print axioms VOA.DeligneAudit.SL4T.mixedSecondLeviEvaluation_alphabetPowerSum_tail
