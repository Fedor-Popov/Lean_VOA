import VOA.DeligneAudit.SL4TSecondLeviKernel

/-! A symmetric relation quotient presenting the second Levi multiplicity space. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

attribute [local instance 2000] Fin.fintype Fin.instOfNat

variable {B V : Type} [CommRing B] [Algebra ℂ B]
variable [AddCommGroup V] [Module ℂ V]

/-- Complete functions in either labelled alphabet are separately symmetric. -/
theorem secondLeviComplete_symmetric (e₁ e₂ : ℕ) (j : Fin 2) (s : ℕ) :
    (if j = 0 then rename Sum.inl (hsymm (Fin e₁) B s)
      else rename Sum.inr (hsymm (Fin e₂) B s)) ∈ secondLeviSymmetricModes e₁ e₂ := by
  intro e
  by_cases hj : j = 0
  · simp only [if_pos hj, rename_rename]
    have he : (secondLeviSlotPermutation e₁ e₂ e : _ → _) ∘ Sum.inl =
        Sum.inl ∘ e.1 := rfl
    rw [he, ← rename_rename, rename_hsymm]
  · simp only [if_neg hj, rename_rename]
    have he : (secondLeviSlotPermutation e₁ e₂ e : _ → _) ∘ Sum.inr =
        Sum.inr ∘ e.2 := rfl
    rw [he, ← rename_rename, rename_hsymm]

/-- Relative complete functions belong to the symmetric coefficient source. -/
def secondLeviRelativeGenerator (e₁ e₂ : ℕ) (j : Fin 2) (p : ℕ → B) (s : ℕ) :
    secondLeviSymmetricModes (B := B) e₁ e₂ :=
  ⟨secondLeviRelativeComplete e₁ e₂ j p s, by
    apply Subalgebra.sum_mem
    intro z hz
    apply Subalgebra.mul_mem
    · exact secondLeviComplete_symmetric e₁ e₂ j z.1
    · intro e; exact rename_C _ _⟩

/-- The finite relative relation windows in the separately symmetric source. -/
def secondLeviRelativeIdeal (e₁ e₂ : ℕ) (r : Fin 2 → ℕ) (p : Fin 2 → ℕ → B) :
    Ideal (secondLeviSymmetricModes (B := B) e₁ e₂) :=
  Ideal.span {R | ∃ j s, r j - (if j = 0 then e₁ else e₂) < s ∧ s ≤ r j ∧
    secondLeviRelativeGenerator e₁ e₂ j (p j) s = R}

variable (Q : CurrentModule VOA.AffineSl3.bracketTable V) (β : B →ₗ[ℂ] V)
variable (u v : ℕ → B)
variable (hu : ∀ s, 1 ≤ s → ∀ φ, Q.op 6 s (β φ) = β (u s * φ))
variable (hv : ∀ s, 1 ≤ s → ∀ φ, Q.op 7 s (β φ) = β (v s * φ))

/-- Relations vanishing after every base multiplication form an ideal of the symmetric source. -/
def secondLeviSaturatedRelationIdeal (e₁ e₂ : ℕ) :
    Ideal (secondLeviSymmetricModes (B := B) e₁ e₂) where
  carrier := {R | ∀ φ, secondLeviQuotientEvaluation Q β e₁ e₂
    (MvPolynomial.C φ * R.val) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro P R hP hR φ
    change secondLeviQuotientEvaluation Q β e₁ e₂
      (MvPolynomial.C φ * (P.val + R.val)) = 0
    rw [mul_add, map_add, hP, hR, add_zero]
  smul_mem' := by
    intro P R hR φ
    change secondLeviQuotientEvaluation Q β e₁ e₂
      (MvPolynomial.C φ * (P.val * R.val)) = 0
    rw [← mul_assoc]
    apply secondLeviQuotientEvaluation_symmetric_mul Q β e₁ e₂ u v hu hv R.val
      (MvPolynomial.C φ * P.val) hR
    exact (secondLeviSymmetricModes e₁ e₂).mul_mem (fun e => rename_C _ _) P.property

/-- The saturated relation quotient still maps onto the actual multiplicity space. -/
def secondLeviRelationQuotientEvaluation (e₁ e₂ : ℕ) :
    (secondLeviSymmetricModes (B := B) e₁ e₂ ⧸
      secondLeviSaturatedRelationIdeal Q β u v hu hv e₁ e₂) →ₗ[ℂ]
        secondLeviMultiplicity Q β e₁ e₂ :=
  (secondLeviSaturatedRelationIdeal Q β u v hu hv e₁ e₂).restrictScalars ℂ |>.liftQ
    (secondLeviSymmetricMultiplicityEvaluation Q β e₁ e₂) (by
      intro P hP
      apply Subtype.ext
      have hz := hP (1 : B)
      simpa only [map_one, one_mul] using hz)

theorem secondLeviRelationQuotientEvaluation_mk (e₁ e₂ : ℕ)
    (P : secondLeviSymmetricModes (B := B) e₁ e₂) :
    secondLeviRelationQuotientEvaluation Q β u v hu hv e₁ e₂ (Ideal.Quotient.mk _ P) =
      secondLeviSymmetricMultiplicityEvaluation Q β e₁ e₂ P := rfl

/-- Passing to the saturated relation quotient preserves surjectivity. -/
theorem secondLeviRelationQuotientEvaluation_surjective (e₁ e₂ : ℕ) :
    Function.Surjective (secondLeviRelationQuotientEvaluation Q β u v hu hv e₁ e₂) := by
  intro x
  obtain ⟨P, rfl⟩ := secondLeviSymmetricMultiplicityEvaluation_surjective Q β e₁ e₂ x
  exact ⟨Ideal.Quotient.mk _ P, rfl⟩

variable (ρ : CurrentModule bracketTable V) (w : V)
variable (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))

set_option synthInstance.maxHeartbeats 100000 in
-- The source coefficient algebra is a tensor product of three quotient rings.
/-- Both complete-function relation windows lie in the actual saturated evaluation ideal. -/
theorem radicalSecondLeviRelativeIdeal_le_relations (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (hm : ∀ j, 0 ≤ a3KeyLabelInt b c j ⟨d 0, d 1, d 2, 0⟩) :
    secondLeviRelativeIdeal e₁ e₂
        (fun j => (a3KeyLabelInt b c j ⟨d 0, d 1, d 2, 0⟩).toNat)
        (radicalLeviPowerSum a b c d) ≤
      secondLeviSaturatedRelationIdeal (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d)
        (radicalLeviPowerSum a b c d 0) (radicalLeviPowerSum a b c d 1)
        (radicalGrassmannianAmbientEvaluation_cartan ρ w a b c h d 0)
        (radicalGrassmannianAmbientEvaluation_cartan ρ w a b c h d 1) e₁ e₂ := by
  apply Ideal.span_le.mpr
  rintro R ⟨j, s, hs, hs', rfl⟩ φ
  dsimp only at hs hs'
  have hk : 1 ≤ if j = 0 then e₁ else e₂ := by omega
  have hsum : (a3KeyLabelInt b c j ⟨d 0, d 1, d 2, 0⟩).toNat + 1 ≤
      (if j = 0 then e₁ else e₂) + s := by omega
  exact radicalSecondLeviEvaluation_relative_mul ρ w a b c h d e₁ e₂ j (hm j)
    s hk hsum (MvPolynomial.C φ) (fun e => rename_C _ _)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondLeviComplete_symmetric
#print axioms VOA.DeligneAudit.SL4T.secondLeviRelationQuotientEvaluation_mk
#print axioms VOA.DeligneAudit.SL4T.secondLeviRelationQuotientEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviRelativeIdeal_le_relations
