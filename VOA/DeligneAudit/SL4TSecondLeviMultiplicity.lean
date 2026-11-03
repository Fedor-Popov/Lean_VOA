import VOA.DeligneAudit.SL4TSecondLeviSymmetricEvaluation

/-! Merged second Levi multiplicities and their two retained Cartan actions. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

variable {B V : Type} [CommRing B] [Algebra ℂ B]
variable [AddCommGroup V] [Module ℂ V]
variable (Q : CurrentModule VOA.AffineSl3.bracketTable V) (β : B →ₗ[ℂ] V)

/-- The Levi closure of strictly greater height at the same total lowering count. -/
def higherSecondLeviCountClosure (e₁ e₂ : ℕ) : Submodule ℂ V :=
  a2LeviClosure Q (⨆ u : ℕ, ⨆ v : ℕ, ⨆ (_ : u + v = e₁ + e₂ ∧ e₁ < u),
    secondLeviCountLayer Q β u v)

/-- The second multiplicity image after quotienting by higher counts. -/
def secondLeviMultiplicity (e₁ e₂ : ℕ) :
    Submodule ℂ (V ⧸ higherSecondLeviCountClosure Q β e₁ e₂) :=
  (secondLeviCountLayer Q β e₁ e₂).map (higherSecondLeviCountClosure Q β e₁ e₂).mkQ

/-- Both retained Cartan currents descend to the second count quotient. -/
def secondLeviQuotientCartan (e₁ e₂ : ℕ) (i : Fin 2) (s : ℕ) :
    Module.End ℂ (V ⧸ higherSecondLeviCountClosure Q β e₁ e₂) :=
  (higherSecondLeviCountClosure Q β e₁ e₂).mapQ
    (higherSecondLeviCountClosure Q β e₁ e₂) (Q.op (if i = 0 then 6 else 7) s)
    (a2LeviClosure_inv Q _ _ s (by
      by_cases hi : i = 0 <;> simp [a2Levi, hi]))

/-- The full labelled-mode evaluator into the second count quotient. -/
def secondLeviQuotientEvaluation (e₁ e₂ : ℕ) :
    MvPolynomial (SecondLeviModeSlot e₁ e₂) B →ₗ[ℂ]
      V ⧸ higherSecondLeviCountClosure Q β e₁ e₂ :=
  (higherSecondLeviCountClosure Q β e₁ e₂).mkQ.comp
    (secondLeviModeEvaluation Q β e₁ e₂)

/-- The separately symmetric evaluator takes values in the actual multiplicity image. -/
def secondLeviSymmetricMultiplicityEvaluation (e₁ e₂ : ℕ) :
    secondLeviSymmetricModes (B := B) e₁ e₂ →ₗ[ℂ] secondLeviMultiplicity Q β e₁ e₂ :=
  ((secondLeviQuotientEvaluation Q β e₁ e₂).comp
    (secondLeviSymmetricModes e₁ e₂).val.toLinearMap).codRestrict
      (secondLeviMultiplicity Q β e₁ e₂) (fun P =>
        ⟨_, (secondLeviModeEvaluation_range Q β e₁ e₂).le ⟨P.val, rfl⟩, rfl⟩)

/-- Every second multiplicity vector is represented by symmetric words over the base. -/
theorem secondLeviSymmetricMultiplicityEvaluation_surjective (e₁ e₂ : ℕ) :
    Function.Surjective (secondLeviSymmetricMultiplicityEvaluation Q β e₁ e₂) := by
  intro v
  obtain ⟨z, hz, he⟩ := v.property
  rw [← secondLeviModeEvaluation_range Q β e₁ e₂] at hz
  obtain ⟨P, rfl⟩ := hz
  obtain ⟨R, hR⟩ := secondLeviModeEvaluation_symmetric_representative Q β e₁ e₂ P
  refine ⟨R, Subtype.ext ?_⟩
  change (higherSecondLeviCountClosure Q β e₁ e₂).mkQ
    (secondLeviModeEvaluation Q β e₁ e₂ R) = v.val
  rw [hR]
  exact he

/-- Both Cartan mode-shift formulas survive the quotient by higher count layers. -/
theorem secondLeviQuotientEvaluation_cartan (e₁ e₂ : ℕ) (i : Fin 2) (s : ℕ) (U : B)
    (hb : ∀ φ, Q.op (if i = 0 then 6 else 7) s (β φ) = β (U * φ))
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) B) :
    secondLeviQuotientCartan Q β e₁ e₂ i s (secondLeviQuotientEvaluation Q β e₁ e₂ P) =
      secondLeviQuotientEvaluation Q β e₁ e₂
        ((MvPolynomial.C U +
          (if i = 0 then (-2 : ℂ) else 1) • secondLeviModePowerSum e₁ e₂ 0 s -
            secondLeviModePowerSum e₁ e₂ 1 s) * P) := by
  change (higherSecondLeviCountClosure Q β e₁ e₂).mkQ
    (Q.op (if i = 0 then 6 else 7) s (secondLeviModeEvaluation Q β e₁ e₂ P)) = _
  rw [secondLeviModeEvaluation_cartan Q β e₁ e₂ i s U hb]
  rfl

/-- The multiplicity image is stable under the two Cartan currents. -/
theorem secondLeviMultiplicity_cartan (e₁ e₂ : ℕ) (i : Fin 2) (s : ℕ) (U : B)
    (hb : ∀ φ, Q.op (if i = 0 then 6 else 7) s (β φ) = β (U * φ)) :
    secondLeviMultiplicity Q β e₁ e₂ ≤ (secondLeviMultiplicity Q β e₁ e₂).comap
      (secondLeviQuotientCartan Q β e₁ e₂ i s) := by
  rintro z ⟨v, hv, rfl⟩
  rw [← secondLeviModeEvaluation_range Q β e₁ e₂] at hv
  obtain ⟨P, rfl⟩ := hv
  change secondLeviQuotientCartan Q β e₁ e₂ i s
    (secondLeviQuotientEvaluation Q β e₁ e₂ P) ∈ secondLeviMultiplicity Q β e₁ e₂
  rw [secondLeviQuotientEvaluation_cartan Q β e₁ e₂ i s U hb]
  exact ⟨_, (secondLeviModeEvaluation_range Q β e₁ e₂).le ⟨_, rfl⟩, rfl⟩

variable (ρ : CurrentModule bracketTable V) (w : V)
variable (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))

set_option synthInstance.maxHeartbeats 100000 in
-- The coefficient algebra is a nested tensor product of quotient rings.
/-- The second evaluator over the actual three-Grassmannian base has both Cartan formulas. -/
theorem radicalSecondLeviEvaluation_cartan (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (i : Fin 2) (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) (RadicalGrassmannianRing a b c d)) :
    let Q := radicalCountQuotCurrent ρ w d
    let β := radicalGrassmannianAmbientEvaluation ρ w a b c h d
    secondLeviQuotientCartan Q β e₁ e₂ i s (secondLeviQuotientEvaluation Q β e₁ e₂ P) =
      secondLeviQuotientEvaluation Q β e₁ e₂
        ((MvPolynomial.C (radicalLeviPowerSum a b c d i s) +
          (if i = 0 then (-2 : ℂ) else 1) • secondLeviModePowerSum e₁ e₂ 0 s -
            secondLeviModePowerSum e₁ e₂ 1 s) * P) :=
  secondLeviQuotientEvaluation_cartan _ _ e₁ e₂ i s _
    (radicalGrassmannianAmbientEvaluation_cartan ρ w a b c h d i s hs) P

set_option synthInstance.maxHeartbeats 100000 in
-- The coefficient algebra is a nested tensor product of quotient rings.
/-- Symmetric lowering words over the three-Grassmannian ring cover the second multiplicity. -/
theorem radicalSecondLeviEvaluation_surjective (d : Fin 3 → ℕ) (e₁ e₂ : ℕ) :
    Function.Surjective (secondLeviSymmetricMultiplicityEvaluation
      (radicalCountQuotCurrent ρ w d)
      (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂) :=
  secondLeviSymmetricMultiplicityEvaluation_surjective _ _ e₁ e₂

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondLeviSymmetricMultiplicityEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotientEvaluation_cartan
#print axioms VOA.DeligneAudit.SL4T.secondLeviMultiplicity_cartan
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviEvaluation_cartan
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviEvaluation_surjective
