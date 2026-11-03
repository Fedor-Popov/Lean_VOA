import VOA.DeligneAudit.SL4TRadicalSymmetricEvaluation

/-! Power-sum equivariance of labelled-mode evaluation before Grassmannian descent. -/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviConversion

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A mode assignment on a list of distinct positions with prescribed colours. -/
def radicalPositionModes {σ : Type*} (shape : σ → Fin 3)
    (is : List σ) (u : σ →₀ ℕ) : List (Fin 3 × ℕ) :=
  is.map fun i => (shape i, u i)

/-- Evaluation of an ordered coloured word on the given vector. -/
def radicalPositionWord (ρ : CurrentModule bracketTable V) (w : V)
    (l : List (Fin 3 × ℕ)) : V := LeviTypeA.radicalWord (radicalOp ρ) l • w

/-- The recursive colour shift equals the sum of shifts at labelled positions. -/
theorem radicalPowerSumWord_positions {σ : Type*}
    (ρ : CurrentModule bracketTable V) (w : V)
    (shape : σ → Fin 3) (is : List σ) (his : is.Nodup)
    (a : σ →₀ ℕ) (j : Fin 3) (r : ℕ) :
    radicalPowerSumWord ρ w j r (radicalPositionModes shape is a) =
      (is.map fun i => if j = shape i then
        (radicalPositionWord ρ w) (radicalPositionModes shape is (Finsupp.single i r + a))
        else 0).sum := by
  classical
  induction is with
  | nil => simp [radicalPositionModes, radicalPowerSumWord]
  | cons t ts ih =>
      have ht : t ∉ ts := (List.nodup_cons.mp his).1
      have hts : ts.Nodup := (List.nodup_cons.mp his).2
      have htail (i : σ) (hi : i ∈ ts) :
          (Finsupp.single i r + a) t = a t := by
        have hit : i ≠ t := by
          intro heq
          exact ht (heq ▸ hi)
        simp [hit]
      have htail_t : radicalPositionModes shape ts (Finsupp.single t r + a) =
          radicalPositionModes shape ts a := by
        simp only [radicalPositionModes]
        apply List.map_congr_left
        intro i hi
        have hit : t ≠ i := by
          intro heq
          exact ht (heq ▸ hi)
        simp [hit]
      have ih' :
          radicalPowerSumWord ρ w j r (List.map (fun i => (shape i, a i)) ts) =
            (ts.map fun i => if j = shape i then
              (radicalPositionWord ρ w)
                (List.map (fun t => (shape t, (Finsupp.single i r + a) t)) ts)
              else 0).sum := by
        simpa only [radicalPositionModes] using ih hts
      simp only [radicalPositionModes, List.map_cons, radicalPowerSumWord,
        List.sum_cons]
      by_cases hj : j = shape t
      · simp only [if_pos hj, one_smul]
        congr 1
        · apply congrArg (radicalPositionWord ρ w)
          simp only [List.cons.injEq]
          constructor
          · simp
          · simpa only [radicalPositionModes] using htail_t.symm
        · rw [ih', map_list_sum]
          simp only [List.map_map, Function.comp_def]
          congr 1
          apply List.map_congr_left
          intro i hi
          by_cases hij : j = shape i
          · simp only [if_pos hij]
            rw [← htail i hi]
            simp [radicalPositionWord, LeviTypeA.radicalWord, Module.End.mul_apply]
          · simp [hij]
      · simp only [if_neg hj, zero_smul, zero_add]
        rw [ih', map_list_sum]
        simp only [List.map_map, Function.comp_def]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hij : j = shape i
        · simp only [if_pos hij]
          rw [← htail i hi]
          simp [radicalPositionWord, LeviTypeA.radicalWord, Module.End.mul_apply]
        · simp [hij]


/-- The colour of a labelled position in the three radical alphabets. -/
def radicalSlotColour (d : Fin 3 → ℕ) : RadicalModeSlot d → Fin 3 :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))

/-- The canonical list of all labelled radical positions. -/
def radicalSlotList (d : Fin 3 → ℕ) : List (RadicalModeSlot d) :=
  List.ofFn (fun i : Fin (d 0) => .inl i) ++
    (List.ofFn (fun i : Fin (d 1) => .inr (.inl i)) ++
      List.ofFn (fun i : Fin (d 2) => .inr (.inr i)))

theorem radicalSlotList_nodup (d : Fin 3 → ℕ) : (radicalSlotList d).Nodup := by
  simp [radicalSlotList, List.nodup_append, List.nodup_ofFn, Function.Injective]

/-- Ordered radical words agree with the product of their individual operators. -/
theorem radicalOperatorWord_eq_product (ρ : CurrentModule bracketTable V)
    (l : List (Fin 3 × ℕ)) :
    LeviTypeA.radicalWord (radicalOp ρ) l = (l.map fun x => radicalOp ρ x.1 x.2).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [LeviTypeA.radicalWord, List.map_cons, List.prod_cons, ih]

/-- The ordered-slot and three-colour evaluator conventions coincide. -/
theorem radicalModeWord_eq_positionWord (ρ : CurrentModule bracketTable V) (w : V)
    (d : Fin 3 → ℕ) (u : RadicalModeSlot d →₀ ℕ) :
    radicalModeWord ρ w d u = radicalPositionWord ρ w
      (radicalPositionModes (radicalSlotColour d) (radicalSlotList d) u) := by
  simp [radicalModeWord, radicalPositionWord, radicalOperatorWord_eq_product,
    radicalPositionModes, radicalSlotColour, radicalSlotList, List.map_append,
    List.prod_append, List.map_ofFn, aWord, radicalOp, mul_assoc, Function.comp_def]

/-- The positional power sum for one radical colour. -/
def radicalModePowerSum (d : Fin 3 → ℕ) (j : Fin 3) (r : ℕ) :
    RadicalModePolynomial d :=
  ((radicalSlotList d).map fun i =>
    if j = radicalSlotColour d i then MvPolynomial.X i ^ r else 0).sum

/-- Multiplication by a positional power sum shifts one matching mode at a time. -/
theorem radicalModeEvaluation_powerSum_monomial
    (ρ : CurrentModule bracketTable V) (w : V) (d : Fin 3 → ℕ)
    (j : Fin 3) (r : ℕ) (u : RadicalModeSlot d →₀ ℕ) :
    radicalModeEvaluation ρ w d
      (radicalModePowerSum d j r * MvPolynomial.monomial u 1) =
        radicalPowerSumWord ρ w j r
          (radicalPositionModes (radicalSlotColour d) (radicalSlotList d) u) := by
  classical
  rw [radicalPowerSumWord_positions ρ w _ _ (radicalSlotList_nodup d)]
  simp only [radicalModePowerSum, ← List.sum_map_mul_right, map_list_sum, List.map_map,
    Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro i hi
  by_cases hj : j = radicalSlotColour d i
  · simp only [hj, if_true, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul, mul_one, radicalModeEvaluation_monomial, one_smul]
    exact radicalModeWord_eq_positionWord ρ w d _
  · simp [hj]

/-- Every positive alphabet current intertwines its positional power sum on the full source. -/
theorem radicalModeEvaluation_powerSum (ρ : CurrentModule bracketTable V) (w : V)
    (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (j : Fin 3) (r : ℕ) (hr : 0 < r)
    (P : RadicalModePolynomial d) :
    radicalAlphabetCurrent ρ j r (radicalModeEvaluation ρ w d P) =
      radicalModeEvaluation ρ w d (radicalModePowerSum d j r * P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial u z =>
    have he : (MvPolynomial.monomial u z : RadicalModePolynomial d) =
        z • MvPolynomial.monomial u 1 := by
      simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [he, map_smul, map_smul, mul_smul_comm, map_smul]
    congr 1
    rw [radicalModeEvaluation_monomial, one_smul, radicalModeWord_eq_positionWord]
    exact (radicalAlphabetCurrent_word ρ w a b c h j r hr _).trans
      (radicalModeEvaluation_powerSum_monomial ρ w d j r u).symm
  | add P Q hP hQ => simp only [map_add, mul_add, hP, hQ]

/-- The actual multiplicity quotient inherits positional power-sum equivariance. -/
theorem radicalMultiplicityEvaluation_powerSum
    (ρ : CurrentModule bracketTable V) (w : V)
    (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (j : Fin 3) (r : ℕ) (hr : 0 < r)
    (P : RadicalModePolynomial d) :
    radicalAlphabetQuotCurrent ρ w a b c h d j r
      (radicalMultiplicityEvaluation ρ w d P :
        V ⧸ higherRadicalCountClosure ρ w d) =
      (radicalMultiplicityEvaluation ρ w d (radicalModePowerSum d j r * P) :
        V ⧸ higherRadicalCountClosure ρ w d) := by
  change (higherRadicalCountClosure ρ w d).mkQ
    (radicalAlphabetCurrent ρ j r (radicalModeEvaluation ρ w d P)) = _
  rw [radicalModeEvaluation_powerSum ρ w a b c h d j r hr P]
  rfl

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.radicalPowerSumWord_positions
#print axioms VOA.DeligneAudit.SL4T.radicalSlotList_nodup
#print axioms VOA.DeligneAudit.SL4T.radicalOperatorWord_eq_product
#print axioms VOA.DeligneAudit.SL4T.radicalModeWord_eq_positionWord
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_powerSum_monomial
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_powerSum
#print axioms VOA.DeligneAudit.SL4T.radicalMultiplicityEvaluation_powerSum
