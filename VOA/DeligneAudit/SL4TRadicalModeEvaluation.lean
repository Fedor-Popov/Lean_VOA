import VOA.DeligneAudit.SL4TRadicalMultiplicityAction

/-! The labelled-mode polynomial evaluator onto the merged radical multiplicity space. -/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviConversion

noncomputable section

/-- The labelled positions in three radical alphabets. -/
abbrev RadicalModeSlot (d : Fin 3 → ℕ) := Fin (d 0) ⊕ (Fin (d 1) ⊕ Fin (d 2))

/-- Polynomials in the individual modes, before imposing symmetry or ring relations. -/
abbrev RadicalModePolynomial (d : Fin 3 → ℕ) := MvPolynomial (RadicalModeSlot d) ℂ

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- Evaluation of a labelled mode assignment as an ordered radical word. -/
def radicalModeWord (d : Fin 3 → ℕ) (u : RadicalModeSlot d → ℕ) : V :=
  (aWord (fun s => ρ.op (F 0) s) (List.ofFn fun i => u (.inl i)) *
    ((List.ofFn fun i => u (.inr (.inl i))).map fun s => ρ.op (F 1) s).prod *
    ((List.ofFn fun i => u (.inr (.inr i))).map fun s => ρ.op (F 2) s).prod) w

/-- Linear extension of evaluation on monomials; exponents are current modes. -/
def radicalModeEvaluation (d : Fin 3 → ℕ) : RadicalModePolynomial d →ₗ[ℂ] V :=
  Finsupp.lsum ℂ fun u : RadicalModeSlot d →₀ ℕ =>
    (LinearMap.ringLmapEquivSelf ℂ ℂ V).symm (radicalModeWord ρ w d u)

theorem radicalModeEvaluation_monomial (d : Fin 3 → ℕ)
    (u : RadicalModeSlot d →₀ ℕ) (z : ℂ) :
    radicalModeEvaluation ρ w d (MvPolynomial.monomial u z) =
      z • radicalModeWord ρ w d u := by
  change (Finsupp.lsum ℂ fun v : RadicalModeSlot d →₀ ℕ =>
    (LinearMap.ringLmapEquivSelf ℂ ℂ V).symm (radicalModeWord ρ w d v))
      (Finsupp.single u z) = _
  rw [Finsupp.lsum_single]
  rfl

/-- Every labelled word belongs to its count layer with all degrees retained. -/
theorem radicalModeWord_mem (d : Fin 3 → ℕ) (u : RadicalModeSlot d → ℕ) :
    radicalModeWord ρ w d u ∈ radicalCountLayer ρ w d := by
  have hm := a3_three_mode_mem_key ρ w
    (List.ofFn fun i => u (.inl i))
    (List.ofFn fun i => u (.inr (.inl i)))
    (List.ofFn fun i => u (.inr (.inr i)))
  simp only [List.length_ofFn] at hm
  exact Submodule.mem_iSup_of_mem _ hm

/-- The evaluator preserves the prescribed three letter counts. -/
theorem radicalModeEvaluation_mem (d : Fin 3 → ℕ) (P : RadicalModePolynomial d) :
    radicalModeEvaluation ρ w d P ∈ radicalCountLayer ρ w d := by
  induction P using MvPolynomial.induction_on' with
  | monomial u z =>
    rw [radicalModeEvaluation_monomial]
    exact Submodule.smul_mem _ _ (radicalModeWord_mem ρ w d u)
  | add P Q hP hQ =>
    rw [map_add]
    exact Submodule.add_mem _ hP hQ

/-- A list with specified length can be recovered from its labelled modes. -/
theorem modeList_of_length (n : ℕ) (xs : List ℕ) (hx : xs.length = n) :
    List.ofFn (fun i : Fin n => xs.get (Fin.cast hx.symm i)) = xs := by
  subst n
  simp

/-- The polynomial evaluator has exactly the merged count layer as its range. -/
theorem radicalModeEvaluation_range (d : Fin 3 → ℕ) :
    LinearMap.range (radicalModeEvaluation ρ w d) = radicalCountLayer ρ w d := by
  classical
  apply le_antisymm
  · rintro v ⟨P, rfl⟩
    exact radicalModeEvaluation_mem ρ w d P
  · apply iSup_le
    intro degree
    rw [a3KeyLayer_eq_sorted, a3SortedKeySpan, Submodule.span_le]
    rintro v ⟨xs, ys, zs, hx, hy, hz, hd, rfl⟩
    let u : RadicalModeSlot d → ℕ := Sum.elim
      (fun i => xs.get (Fin.cast hx.symm i))
      (Sum.elim (fun i => ys.get (Fin.cast hy.symm i))
        (fun i => zs.get (Fin.cast hz.symm i)))
    refine ⟨MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm u) 1, ?_⟩
    rw [radicalModeEvaluation_monomial, one_smul]
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    simp only [radicalModeWord, u, Sum.elim_inl, Sum.elim_inr]
    rw [modeList_of_length (d 0) xs hx, modeList_of_length (d 1) ys hy,
      modeList_of_length (d 2) zs hz]

/-- The labelled-mode evaluator followed by the quotient to actual multiplicities. -/
def radicalMultiplicityEvaluation (d : Fin 3 → ℕ) :
    RadicalModePolynomial d →ₗ[ℂ] radicalCountMultiplicity ρ w d :=
  ((higherRadicalCountClosure ρ w d).mkQ.comp
    (radicalModeEvaluation ρ w d)).codRestrict (radicalCountMultiplicity ρ w d)
      (fun P => ⟨_, radicalModeEvaluation_mem ρ w d P, rfl⟩)

/-- Every actual merged multiplicity vector has a labelled-mode polynomial representative. -/
theorem radicalMultiplicityEvaluation_surjective (d : Fin 3 → ℕ) :
    Function.Surjective (radicalMultiplicityEvaluation ρ w d) := by
  intro v
  obtain ⟨x, hx, he⟩ := v.property
  rw [← radicalModeEvaluation_range ρ w d] at hx
  obtain ⟨P, rfl⟩ := hx
  refine ⟨P, ?_⟩
  exact Subtype.ext he

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_monomial
#print axioms VOA.DeligneAudit.SL4T.radicalModeWord_mem
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_mem
#print axioms VOA.DeligneAudit.SL4T.modeList_of_length
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_range
#print axioms VOA.DeligneAudit.SL4T.radicalMultiplicityEvaluation_surjective
