import VOA.DeligneAudit.SL4TPositionModeEvaluation

/-! The two lowering alphabets applied to a coefficient space in a rank-two current module. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviTypeA VOA.DeligneAudit.LeviConversion

attribute [local instance 2000] Fin.fintype Fin.instOfNat

/-- Labelled positions of the two commuting lowering alphabets. -/
abbrev SecondLeviModeSlot (e₁ e₂ : ℕ) := Fin e₁ ⊕ Fin e₂

/-- The canonical ordered list of the two lowering alphabets. -/
def secondLeviModePositions (e₁ e₂ : ℕ) : List (SecondLeviModeSlot e₁ e₂) :=
  List.ofFn (fun i : Fin e₁ => .inl i) ++ List.ofFn (fun i : Fin e₂ => .inr i)

theorem secondLeviModePositions_nodup (e₁ e₂ : ℕ) :
    (secondLeviModePositions e₁ e₂).Nodup := by
  simp [secondLeviModePositions, List.nodup_append, List.nodup_ofFn,
    Function.Injective]

variable {B V : Type} [CommRing B] [Algebra ℂ B]
variable [AddCommGroup V] [Module ℂ V]
variable (Q : CurrentModule VOA.AffineSl3.bracketTable V) (β : B →ₗ[ℂ] V)

/-- The simple and compound lowering operators at a labelled position. -/
def secondLeviPositionOperator (e₁ e₂ : ℕ) :
    SecondLeviModeSlot e₁ e₂ → ℕ → Module.End ℂ V :=
  Sum.elim (fun _ s => Q.op 3 s) (fun _ s => Q.op 5 s)

/-- Evaluation of the two labelled mode alphabets with arbitrary base coefficients. -/
def secondLeviModeEvaluation (e₁ e₂ : ℕ) :
    MvPolynomial (SecondLeviModeSlot e₁ e₂) B →ₗ[ℂ] V :=
  positionModeEvaluation (secondLeviPositionOperator Q e₁ e₂)
    (secondLeviModePositions e₁ e₂) β

/-- Ordered mode products are the simple word followed by the compound word. -/
theorem secondLeviPositionProduct (e₁ e₂ : ℕ) (u : SecondLeviModeSlot e₁ e₂ → ℕ) :
    positionModeProduct (secondLeviPositionOperator Q e₁ e₂)
      (secondLeviModePositions e₁ e₂) u =
        ((List.ofFn fun i => u (.inl i)).map fun s => Q.op 3 s).prod *
          ((List.ofFn fun i => u (.inr i)).map fun s => Q.op 5 s).prod := by
  simp [positionModeProduct, secondLeviPositionOperator, secondLeviModePositions,
    List.map_append, List.prod_append, List.map_ofFn, Function.comp_def]

/-- All modes and all coefficient vectors are retained in a fixed count layer. -/
def secondLeviCountLayer (e₁ e₂ : ℕ) : Submodule ℂ V :=
  ⨆ φ : B, a2CountSpan Q (β φ) e₁ e₂

theorem secondLeviPositionProduct_mem (e₁ e₂ : ℕ)
    (u : SecondLeviModeSlot e₁ e₂ → ℕ) (φ : B) :
    positionModeProduct (secondLeviPositionOperator Q e₁ e₂)
      (secondLeviModePositions e₁ e₂) u (β φ) ∈ secondLeviCountLayer Q β e₁ e₂ := by
  rw [secondLeviPositionProduct, Module.End.mul_apply]
  apply Submodule.mem_iSup_of_mem φ
  have h₂ := a2CountSpan_second_word Q (β φ) (List.ofFn fun i : Fin e₂ => u (.inr i))
    0 0 (a2CountSpan_zero Q (β φ))
  have h₁ := a2CountSpan_first_word Q (β φ) (List.ofFn fun i : Fin e₁ => u (.inl i))
    0 e₂ (by simpa using h₂)
  simpa using h₁

/-- The evaluator has exactly the span of all words with the two prescribed counts. -/
theorem secondLeviModeEvaluation_range (e₁ e₂ : ℕ) :
    LinearMap.range (secondLeviModeEvaluation Q β e₁ e₂) =
      secondLeviCountLayer Q β e₁ e₂ := by
  classical
  apply le_antisymm
  · rintro v ⟨P, rfl⟩
    induction P using MvPolynomial.induction_on' with
    | monomial u φ =>
      rw [secondLeviModeEvaluation, positionModeEvaluation_monomial]
      exact secondLeviPositionProduct_mem Q β e₁ e₂ u φ
    | add P R hP hR => simpa only [map_add] using Submodule.add_mem _ hP hR
  · apply iSup_le
    intro φ
    apply iSup_le
    intro degree
    rw [a2KeyLayer, Submodule.span_le]
    rintro v ⟨l, h₁, h₂, hd, hl, rfl⟩
    have hx : (firstModes l).length = e₁ := by
      simpa [firstModes, List.countP_eq_length_filter] using h₁
    have hy : (secondModes l).length = e₂ := by
      simpa [secondModes, List.countP_eq_length_filter] using h₂
    let u : SecondLeviModeSlot e₁ e₂ → ℕ := Sum.elim
      (fun i => (firstModes l).get (Fin.cast hx.symm i))
      (fun i => (secondModes l).get (Fin.cast hy.symm i))
    refine ⟨monomial (Finsupp.equivFunOnFinite.symm u) φ, ?_⟩
    rw [secondLeviModeEvaluation, positionModeEvaluation_monomial,
      secondLeviPositionProduct, radicalWord_split]
    simp only [Finsupp.coe_equivFunOnFinite_symm, u, Sum.elim_inl, Sum.elim_inr]
    rw [modeList_of_length e₁ _ hx, modeList_of_length e₂ _ hy]
    rfl

/-- Positional power sums in either lowering alphabet. -/
def secondLeviModePowerSum (e₁ e₂ : ℕ) (j : Fin 2) (s : ℕ) :
    MvPolynomial (SecondLeviModeSlot e₁ e₂) B :=
  if j = 0 then ∑ i : Fin e₁, X (.inl i) ^ s
  else ∑ i : Fin e₂, X (.inr i) ^ s

/-- The two Cartan charges of the two lowering alphabets. -/
def secondLeviCartanCharge (e₁ e₂ : ℕ) (i : Fin 2) : SecondLeviModeSlot e₁ e₂ → ℂ :=
  Sum.elim (fun _ => if i = 0 then -2 else 1) (fun _ => -1)

theorem secondLeviPositionOperator_cartan (e₁ e₂ : ℕ) (i : Fin 2) (s n : ℕ)
    (j : SecondLeviModeSlot e₁ e₂) :
    Q.op (if i = 0 then 6 else 7) s * secondLeviPositionOperator Q e₁ e₂ j n -
      secondLeviPositionOperator Q e₁ e₂ j n * Q.op (if i = 0 then 6 else 7) s =
        secondLeviCartanCharge e₁ e₂ i j •
          secondLeviPositionOperator Q e₁ e₂ j (s + n) := by
  fin_cases i <;> cases j <;>
    simp [secondLeviPositionOperator, secondLeviCartanCharge, op_comm_end,
      Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]

theorem secondLeviModePowerSum_cartan (e₁ e₂ : ℕ) (i : Fin 2) (s : ℕ) :
    positionModePowerSum (B := B) (secondLeviModePositions e₁ e₂)
      (secondLeviCartanCharge e₁ e₂ i) s =
        (if i = 0 then (-2 : ℂ) else 1) • secondLeviModePowerSum e₁ e₂ 0 s -
          secondLeviModePowerSum e₁ e₂ 1 s := by
  simp [positionModePowerSum, secondLeviModePositions, secondLeviCartanCharge,
    secondLeviModePowerSum, List.map_append, List.sum_append, List.map_ofFn,
    List.sum_ofFn, Finset.smul_sum, sub_eq_add_neg, Function.comp_def]

/-- Both Cartan formulas hold on the entire polynomial source, including base coefficients. -/
theorem secondLeviModeEvaluation_cartan (e₁ e₂ : ℕ) (i : Fin 2) (s : ℕ) (U : B)
    (hb : ∀ φ, Q.op (if i = 0 then 6 else 7) s (β φ) = β (U * φ))
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) B) :
    Q.op (if i = 0 then 6 else 7) s (secondLeviModeEvaluation Q β e₁ e₂ P) =
      secondLeviModeEvaluation Q β e₁ e₂
        ((MvPolynomial.C U +
          (if i = 0 then (-2 : ℂ) else 1) • secondLeviModePowerSum e₁ e₂ 0 s -
            secondLeviModePowerSum e₁ e₂ 1 s) * P) := by
  rw [secondLeviModeEvaluation, positionModeEvaluation_cartan
    _ _ (secondLeviModePositions_nodup e₁ e₂) β _ U
    (secondLeviCartanCharge e₁ e₂ i) s
    (fun j n => secondLeviPositionOperator_cartan Q e₁ e₂ i s n j) hb,
    secondLeviModePowerSum_cartan, ← add_sub_assoc]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondLeviModePositions_nodup
#print axioms VOA.DeligneAudit.SL4T.secondLeviPositionProduct
#print axioms VOA.DeligneAudit.SL4T.secondLeviPositionProduct_mem
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_range
#print axioms VOA.DeligneAudit.SL4T.secondLeviPositionOperator_cartan
#print axioms VOA.DeligneAudit.SL4T.secondLeviModePowerSum_cartan
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_cartan
