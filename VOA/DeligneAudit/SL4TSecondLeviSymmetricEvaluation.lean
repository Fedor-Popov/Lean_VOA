import VOA.DeligneAudit.SL4TSecondLeviEvaluation

/-! Separate symmetry preserves the full image of the second Levi mode evaluator. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviTypeA

attribute [local instance 2000] Fin.fintype Fin.instOfNat

variable {B V : Type} [CommRing B] [Algebra ℂ B]
variable [AddCommGroup V] [Module ℂ V]
variable (Q : CurrentModule VOA.AffineSl3.bracketTable V) (β : B →ₗ[ℂ] V)

/-- Independent permutations of the two labelled alphabets. -/
def secondLeviSlotPermutation (e₁ e₂ : ℕ)
    (e : Equiv.Perm (Fin e₁) × Equiv.Perm (Fin e₂)) :
    Equiv.Perm (SecondLeviModeSlot e₁ e₂) := Equiv.sumCongr e.1 e.2

theorem secondLeviColourProduct_perm (j : Fin 2) {xs ys : List ℕ}
    (hp : xs.Perm ys) :
    (xs.map fun s => a2RadicalOp Q j s).prod =
      (ys.map fun s => a2RadicalOp Q j s).prod := by
  apply (hp.map _).prod_eq'
  apply List.pairwise_map.mpr
  apply List.pairwise_of_forall
  intro s t
  exact a2RadicalOp_comm Q j j s t

theorem secondLeviPositionProduct_permute (e₁ e₂ : ℕ)
    (e : Equiv.Perm (Fin e₁) × Equiv.Perm (Fin e₂))
    (u : SecondLeviModeSlot e₁ e₂ → ℕ) :
    positionModeProduct (secondLeviPositionOperator Q e₁ e₂)
      (secondLeviModePositions e₁ e₂) (u ∘ secondLeviSlotPermutation e₁ e₂ e) =
        positionModeProduct (secondLeviPositionOperator Q e₁ e₂)
          (secondLeviModePositions e₁ e₂) u := by
  rw [secondLeviPositionProduct, secondLeviPositionProduct]
  have h₁ := secondLeviColourProduct_perm Q 0
    (e.1.ofFn_comp_perm (fun i => u (.inl i)))
  have h₂ := secondLeviColourProduct_perm Q 1
    (e.2.ofFn_comp_perm (fun i => u (.inr i)))
  simpa only [a2RadicalOp, secondLeviSlotPermutation, Function.comp_def,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, if_true, if_false,
    show (1 : Fin 2) ≠ 0 by decide] using congrArg₂ (· * ·) h₁ h₂

/-- Relabelling within either alphabet leaves mode evaluation unchanged. -/
theorem secondLeviModeEvaluation_rename (e₁ e₂ : ℕ)
    (e : Equiv.Perm (Fin e₁) × Equiv.Perm (Fin e₂))
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) B) :
    secondLeviModeEvaluation Q β e₁ e₂ (rename (secondLeviSlotPermutation e₁ e₂ e) P) =
      secondLeviModeEvaluation Q β e₁ e₂ P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u b =>
    rw [rename_monomial, secondLeviModeEvaluation, positionModeEvaluation_monomial,
      positionModeEvaluation_monomial]
    have hu : (Finsupp.mapDomain (secondLeviSlotPermutation e₁ e₂ e) u :
        SecondLeviModeSlot e₁ e₂ → ℕ) =
          u ∘ secondLeviSlotPermutation e₁ e₂ (e.1.symm, e.2.symm) := by
      funext i
      rw [Finsupp.mapDomain_equiv_apply]
      rfl
    rw [hu, secondLeviPositionProduct_permute]
  | add P R hP hR => simp only [map_add, hP, hR]

/-- Polynomials separately symmetric in both lowering alphabets over the base algebra. -/
def secondLeviSymmetricModes (e₁ e₂ : ℕ) :
    Subalgebra ℂ (MvPolynomial (SecondLeviModeSlot e₁ e₂) B) where
  carrier := {P | ∀ e, rename (secondLeviSlotPermutation e₁ e₂ e) P = P}
  zero_mem' := by intro e; exact map_zero _
  one_mem' := by intro e; exact map_one _
  add_mem' := by intro P R hP hR e; simp only [map_add, hP e, hR e]
  mul_mem' := by intro P R hP hR e; simp only [map_mul, hP e, hR e]
  algebraMap_mem' := by intro z e; exact rename_C _ _

/-- Orbit averaging before normalization, with coefficients fixed. -/
def secondLeviModeOrbitSum (e₁ e₂ : ℕ)
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) B) :
    MvPolynomial (SecondLeviModeSlot e₁ e₂) B :=
  ∑ e : Equiv.Perm (Fin e₁) × Equiv.Perm (Fin e₂),
    rename (secondLeviSlotPermutation e₁ e₂ e) P

theorem secondLeviModeOrbitSum_mem (e₁ e₂ : ℕ)
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) B) :
    secondLeviModeOrbitSum e₁ e₂ P ∈ secondLeviSymmetricModes e₁ e₂ := by
  classical
  intro f
  simp only [secondLeviModeOrbitSum, map_sum]
  apply Finset.sum_bij (fun e _ => f * e)
  · intro e he; simp
  · intro e he g hg hfg; exact mul_left_cancel hfg
  · intro e he; exact ⟨f⁻¹ * e, by simp, by group⟩
  · intro e he
    rw [rename_rename]
    have heq : (secondLeviSlotPermutation e₁ e₂ f :
        SecondLeviModeSlot e₁ e₂ → SecondLeviModeSlot e₁ e₂) ∘
          secondLeviSlotPermutation e₁ e₂ e =
            secondLeviSlotPermutation e₁ e₂ (f * e) := by
      funext i
      cases i <;> rfl
    rw [heq]

theorem secondLeviModeEvaluation_orbitSum (e₁ e₂ : ℕ)
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) B) :
    secondLeviModeEvaluation Q β e₁ e₂ (secondLeviModeOrbitSum e₁ e₂ P) =
      (Fintype.card (Equiv.Perm (Fin e₁) × Equiv.Perm (Fin e₂)) : ℂ) •
        secondLeviModeEvaluation Q β e₁ e₂ P := by
  classical
  simp only [secondLeviModeOrbitSum, map_sum, secondLeviModeEvaluation_rename]
  rw [Finset.sum_const, Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

/-- Every word polynomial has a separately symmetric representative with the same image. -/
theorem secondLeviModeEvaluation_symmetric_representative (e₁ e₂ : ℕ)
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) B) :
    ∃ R : secondLeviSymmetricModes (B := B) e₁ e₂,
      secondLeviModeEvaluation Q β e₁ e₂ R = secondLeviModeEvaluation Q β e₁ e₂ P := by
  let n := Fintype.card (Equiv.Perm (Fin e₁) × Equiv.Perm (Fin e₂))
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨⟨(n : ℂ)⁻¹ • secondLeviModeOrbitSum e₁ e₂ P,
    (secondLeviSymmetricModes e₁ e₂).smul_mem (secondLeviModeOrbitSum_mem e₁ e₂ P) _⟩, ?_⟩
  rw [map_smul, secondLeviModeEvaluation_orbitSum, smul_smul]
  change ((n : ℂ)⁻¹ * (n : ℂ)) • secondLeviModeEvaluation Q β e₁ e₂ P = _
  rw [inv_mul_cancel₀ hn, one_smul]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondLeviColourProduct_perm
#print axioms VOA.DeligneAudit.SL4T.secondLeviPositionProduct_permute
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_rename
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeOrbitSum_mem
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_orbitSum
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_symmetric_representative
