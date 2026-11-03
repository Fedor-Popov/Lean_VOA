import VOA.DeligneAudit.SL4TRadicalModeEvaluation

/-! Permutation invariance of the radical mode evaluator in each of its three alphabets. -/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviConversion

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- Products of currents of one radical colour are invariant under mode permutations. -/
theorem radicalColourProduct_perm (j : Fin 3) {xs ys : List ℕ} (hp : xs.Perm ys) :
    (xs.map fun s => ρ.op (F j) s).prod =
      (ys.map fun s => ρ.op (F j) s).prod := by
  have hc : ∀ zs : List ℕ, (zs.map fun s => ρ.op (F j) s).Pairwise Commute := by
    intro zs
    induction zs with
    | nil => simp
    | cons z zs ih =>
      simp only [List.map_cons, List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro y hy
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
      exact a3_conversion_radical_comm ρ j j z t
  exact (hp.map _).prod_eq' (hc xs)

/-- Independent relabelling of the three radical alphabets. -/
def radicalSlotPermutation (d : Fin 3 → ℕ)
    (e : (j : Fin 3) → Equiv.Perm (Fin (d j))) : Equiv.Perm (RadicalModeSlot d) :=
  Equiv.sumCongr (e 0) (Equiv.sumCongr (e 1) (e 2))

/-- Labelled words depend only on the unordered modes within each colour. -/
theorem radicalModeWord_permute (d : Fin 3 → ℕ)
    (e : (j : Fin 3) → Equiv.Perm (Fin (d j))) (u : RadicalModeSlot d → ℕ) :
    radicalModeWord ρ w d (u ∘ radicalSlotPermutation d e) =
      radicalModeWord ρ w d u := by
  have h₀ := radicalColourProduct_perm ρ 0
    ((e 0).ofFn_comp_perm (fun i => u (.inl i)))
  have h₁ := radicalColourProduct_perm ρ 1
    ((e 1).ofFn_comp_perm (fun i => u (.inr (.inl i))))
  have h₂ := radicalColourProduct_perm ρ 2
    ((e 2).ofFn_comp_perm (fun i => u (.inr (.inr i))))
  simp only [radicalModeWord, aWord, Function.comp_def, radicalSlotPermutation,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr] at *
  rw [h₀, h₁, h₂]

/-- Polynomial evaluation is invariant under independent alphabet permutations. -/
theorem radicalModeEvaluation_rename (d : Fin 3 → ℕ)
    (e : (j : Fin 3) → Equiv.Perm (Fin (d j))) (P : RadicalModePolynomial d) :
    radicalModeEvaluation ρ w d (MvPolynomial.rename (radicalSlotPermutation d e) P) =
      radicalModeEvaluation ρ w d P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u z =>
    rw [MvPolynomial.rename_monomial, radicalModeEvaluation_monomial,
      radicalModeEvaluation_monomial]
    congr 1
    have hu : (Finsupp.mapDomain (radicalSlotPermutation d e) u :
        RadicalModeSlot d → ℕ) = u ∘ radicalSlotPermutation d (fun j => (e j).symm) := by
      funext i
      rw [Finsupp.mapDomain_equiv_apply]
      rfl
    rw [hu, radicalModeWord_permute]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

/-- Separately symmetric polynomials in the three radical alphabets. -/
def radicalSymmetricModes (d : Fin 3 → ℕ) : Subalgebra ℂ (RadicalModePolynomial d) where
  carrier := {P | ∀ e, MvPolynomial.rename (radicalSlotPermutation d e) P = P}
  zero_mem' := by intro e; exact map_zero _
  one_mem' := by intro e; exact map_one _
  add_mem' := by intro P Q hP hQ e; simp only [map_add, hP e, hQ e]
  mul_mem' := by intro P Q hP hQ e; simp only [map_mul, hP e, hQ e]
  algebraMap_mem' := by intro z e; exact MvPolynomial.rename_C _ _

/-- The sum over all independent relabellings of the three alphabets. -/
def radicalModeOrbitSum (d : Fin 3 → ℕ) (P : RadicalModePolynomial d) :
    RadicalModePolynomial d :=
  ∑ e : (j : Fin 3) → Equiv.Perm (Fin (d j)),
    MvPolynomial.rename (radicalSlotPermutation d e) P

/-- Orbit sums are separately symmetric without any freeness assumption. -/
theorem radicalModeOrbitSum_mem (d : Fin 3 → ℕ) (P : RadicalModePolynomial d) :
    radicalModeOrbitSum d P ∈ radicalSymmetricModes d := by
  classical
  intro f
  simp only [radicalModeOrbitSum, map_sum]
  apply Finset.sum_bij (fun e _ => f * e)
  · intro e he; simp
  · intro e he g hg hfg; exact mul_left_cancel hfg
  · intro e he
    exact ⟨f⁻¹ * e, by simp, by group⟩
  · intro e he
    rw [MvPolynomial.rename_rename]
    have heq : (radicalSlotPermutation d f : RadicalModeSlot d → RadicalModeSlot d) ∘
        radicalSlotPermutation d e = radicalSlotPermutation d (f * e) := by
      funext i
      rcases i with i | i | i <;> rfl
    rw [heq]

/-- The evaluator sends an orbit sum to the group order times the original value. -/
theorem radicalModeEvaluation_orbitSum (d : Fin 3 → ℕ) (P : RadicalModePolynomial d) :
    radicalModeEvaluation ρ w d (radicalModeOrbitSum d P) =
      (Fintype.card ((j : Fin 3) → Equiv.Perm (Fin (d j))) : ℂ) •
        radicalModeEvaluation ρ w d P := by
  classical
  simp only [radicalModeOrbitSum, map_sum, radicalModeEvaluation_rename]
  rw [Finset.sum_const, Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

/-- Averaging supplies a separately symmetric representative of every evaluated polynomial. -/
theorem radicalModeEvaluation_symmetric_representative (d : Fin 3 → ℕ)
    (P : RadicalModePolynomial d) :
    ∃ Q : radicalSymmetricModes d, radicalModeEvaluation ρ w d Q =
      radicalModeEvaluation ρ w d P := by
  let n := Fintype.card ((j : Fin 3) → Equiv.Perm (Fin (d j)))
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨⟨(n : ℂ)⁻¹ • radicalModeOrbitSum d P,
    (radicalSymmetricModes d).smul_mem (radicalModeOrbitSum_mem d P) _⟩, ?_⟩
  rw [map_smul, radicalModeEvaluation_orbitSum, smul_smul]
  change ((n : ℂ)⁻¹ * (n : ℂ)) • radicalModeEvaluation ρ w d P = _
  rw [inv_mul_cancel₀ hn, one_smul]

/-- Evaluation on the separately symmetric source onto actual merged multiplicities. -/
def radicalSymmetricMultiplicityEvaluation (d : Fin 3 → ℕ) :
    radicalSymmetricModes d →ₗ[ℂ] radicalCountMultiplicity ρ w d :=
  (radicalMultiplicityEvaluation ρ w d).comp (radicalSymmetricModes d).val.toLinearMap

/-- Symmetry does not reduce the image of the multiplicity evaluator. -/
theorem radicalSymmetricMultiplicityEvaluation_surjective (d : Fin 3 → ℕ) :
    Function.Surjective (radicalSymmetricMultiplicityEvaluation ρ w d) := by
  intro v
  obtain ⟨P, rfl⟩ := radicalMultiplicityEvaluation_surjective ρ w d v
  obtain ⟨Q, hQ⟩ := radicalModeEvaluation_symmetric_representative ρ w d P
  refine ⟨Q, Subtype.ext ?_⟩
  exact congrArg (higherRadicalCountClosure ρ w d).mkQ hQ

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.radicalColourProduct_perm
#print axioms VOA.DeligneAudit.SL4T.radicalModeWord_permute
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_rename
#print axioms VOA.DeligneAudit.SL4T.radicalModeOrbitSum_mem
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_orbitSum
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_symmetric_representative
#print axioms VOA.DeligneAudit.SL4T.radicalSymmetricMultiplicityEvaluation_surjective
