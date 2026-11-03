import VOA.DeligneAudit.SL4TCompletePolynomialSpecialization
import VOA.DeligneAudit.SL4TRadicalCountSupport

/-! The complete symmetric polynomials evaluate to the radical Garland source vectors. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial VOA.DeligneAudit.LeviConversion
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

attribute [local instance 2000] Fin.fintype Fin.instOfNat

/-- A current power coefficient is a sum over all mode vectors of the specified total. -/
theorem currentPower_coeff_modeVectors {A : Type*} [Ring A]
    (f : ℕ → A) (n s : ℕ) :
    PowerSeries.coeff s (fCurrent f ^ n) =
      ∑ e : {e : Fin n → ℕ // ∑ i, e i = s}, ((List.ofFn e.1).map f).prod := by
  have hc := D4Levi.mixed_current_coeff_allocations (List.replicate n f) s
  simp only [List.map_replicate, List.prod_replicate, List.length_replicate] at hc
  rw [hc, D4Levi.rz_zero_alloc_sum_eq_vector_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [← List.ofFn_const, List.ofFn_eq_map, List.zip_map', List.map_map,
    Function.comp_def]

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- A full product of labelled monomials evaluates to its specified radical word. -/
theorem radicalModeEvaluation_prod (d : Fin 3 → ℕ) (u : RadicalModeSlot d → ℕ) :
    radicalModeEvaluation ρ w d (∏ i, X i ^ u i) = radicalModeWord ρ w d u := by
  classical
  let v := Finsupp.equivFunOnFinite.symm u
  have he : (monomial v 1 : RadicalModePolynomial d) = ∏ i, X i ^ u i := by
    rw [monomial_eq, map_one, one_mul]
    exact v.prod_fintype _ (fun i => pow_zero _)
  rw [← he, radicalModeEvaluation_monomial, one_smul]
  rfl

/-- Fill unused alphabets with zero modes. -/
def radicalSingleAlphabetModes (d : Fin 3 → ℕ) (j : Fin 3) (u : Fin (d j) → ℕ) :
    RadicalModeSlot d → ℕ :=
  match j with
  | 0 => Sum.elim u (fun _ => 0)
  | 1 => Sum.elim (fun _ => 0) (Sum.elim u (fun _ => 0))
  | 2 => Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) u)

/-- Evaluation after inserting a single alphabet leaves the other modes zero. -/
theorem radicalModeEvaluation_alphabet_prod (d : Fin 3 → ℕ) (j : Fin 3)
    (u : Fin (d j) → ℕ) :
    radicalModeEvaluation ρ w d
      (rename (radicalSlotEmbedding d j) (∏ i, X i ^ u i)) =
        radicalModeWord ρ w d (radicalSingleAlphabetModes d j u) := by
  have he : rename (radicalSlotEmbedding d j) (∏ i, X i ^ u i) =
      ∏ i, (X i : RadicalModePolynomial d) ^ radicalSingleAlphabetModes d j u i := by
    simp only [map_prod, map_pow, rename_X]
    fin_cases j <;>
      simp [Fintype.prod_sum_type, radicalSingleAlphabetModes, radicalSlotEmbedding]
    all_goals rfl
  rw [he, radicalModeEvaluation_prod]

/-- The complete polynomial in any one alphabet is exactly its Garland source coefficient. -/
theorem radicalModeEvaluation_complete (d : Fin 3 → ℕ) (j : Fin 3) (s : ℕ) :
    radicalModeEvaluation ρ w d
      (rename (radicalSlotEmbedding d j) (hsymm (Fin (d j)) ℂ s)) =
        radicalCompleteSource ρ w d j s := by
  classical
  rw [D4Levi.rz_hsymm_eq_sum_vectors, map_sum, map_sum]
  simp only [radicalModeEvaluation_alphabet_prod]
  have hsum (f : ℕ → Module.End ℂ V) (n : ℕ) (L R : Module.End ℂ V) :
      (L * PowerSeries.coeff s (fCurrent f ^ n) * R) w =
        ∑ e : {e : Fin n → ℕ // ∑ i, e i = s},
          (L * ((List.ofFn e.1).map f).prod * R) w := by
    rw [currentPower_coeff_modeVectors]
    simp only [Finset.mul_sum, Finset.sum_mul, LinearMap.sum_apply]
  fin_cases j
  · simp only [radicalCompleteSource]
    rw [mul_assoc, ← one_mul (PowerSeries.coeff s _), hsum]
    apply Finset.sum_congr rfl
    intro e he
    simp [radicalModeWord, radicalSingleAlphabetModes, aWord, List.ofFn_const,
      List.prod_replicate, mul_assoc]
  · simp only [radicalCompleteSource]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro e he
    simp [radicalModeWord, radicalSingleAlphabetModes, aWord, List.ofFn_const,
      List.prod_replicate]
  · have hz : (⟨2, by omega⟩ : Fin 3) ≠ 0 := by decide
    have ho : (⟨2, by omega⟩ : Fin 3) ≠ 1 := by decide
    simp only [radicalCompleteSource, hz, ho, if_false]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro e he
    simp only [radicalModeWord, radicalSingleAlphabetModes, Sum.elim_inl,
      Sum.elim_inr, aWord, List.ofFn_const, List.map_replicate, List.prod_replicate]
    have hc : Commute (ρ.op (F 1) 0 ^ d 1 *
        ((List.ofFn e.1).map fun s => ρ.op (F 2) s).prod) (ρ.op (F 0) 0 ^ d 0) := by
      apply Commute.mul_left
      · exact ((show Commute (ρ.op (F 1) 0) (ρ.op (F 0) 0) from
          a3_conversion_radical_comm ρ 1 0 0 0).pow_left _).pow_right _
      · apply Commute.list_prod_left
        intro x hx
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
        exact (show Commute (ρ.op (F 2) s) (ρ.op (F 0) 0) from
          a3_conversion_radical_comm ρ 2 0 s 0).pow_right _
    rw [mul_assoc]
    exact congrArg (fun T : Module.End ℂ V => T w) hc.eq.symm

/-- The complete-function tails lie in the kernel of the actual multiplicity evaluator. -/
theorem radicalMultiplicityEvaluation_complete_eq_zero (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) (d : Fin 3 → ℕ) (j : Fin 3)
    (s : ℕ) (hs : weightABC a b c j - d j < s) :
    radicalMultiplicityEvaluation ρ w d
      (rename (radicalSlotEmbedding d j) (hsymm (Fin (d j)) ℂ s)) = 0 := by
  by_cases hd : 1 ≤ d j
  · apply Subtype.ext
    change (higherRadicalCountClosure ρ w d).mkQ _ = 0
    rw [radicalModeEvaluation_complete]
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (radicalCompleteSource_mem_higher ρ w a b c h d j s hd (by omega))
  · have hz : d j = 0 := by omega
    have he : hsymm (Fin (d j)) ℂ s = 0 := by
      rw [hz, D4Levi.rz_hsymm_eq_sum_vectors]
      apply Finset.sum_eq_zero
      intro e he
      have hn := e.property
      simp only [Fin.sum_univ_zero] at hn
      omega
    rw [he, map_zero, map_zero]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.currentPower_coeff_modeVectors
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_prod
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_alphabet_prod
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_complete
#print axioms VOA.DeligneAudit.SL4T.radicalMultiplicityEvaluation_complete_eq_zero
