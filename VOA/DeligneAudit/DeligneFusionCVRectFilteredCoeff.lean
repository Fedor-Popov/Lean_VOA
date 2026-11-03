import VOA.DeligneAudit.DeligneFusionCVRectFilteredPolynomial

/-!
# Ordered current coefficients and their actual PBW symbols

The coefficient of a product of n lowering currents lies in the actual
length-n filtration, and its length symbol equals the corresponding
coefficient acting on the commuting graded cyclic generator. Relations
modulo shorter actual words therefore become actual graded annihilators.
-/

namespace VOA.DeligneAudit.A2.CVRectFiltered

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V) (w : V)

/-- An ordered list of current colors, with independent nonnegative modes. -/
def currentProduct {A : Type} [Semiring A] (F : Fin 3 → ℕ → A) :
    List (Fin 3) → PowerSeries A
  | [] => 1
  | a :: l => PowerSeries.mk (F a) * currentProduct F l

theorem currentProduct_append {A : Type} [Semiring A] (F : Fin 3 → ℕ → A)
    (l m : List (Fin 3)) :
    currentProduct F (l ++ m) = currentProduct F l * currentProduct F m := by
  induction l with
  | nil => simp [currentProduct]
  | cons a l ih => simp only [List.cons_append, currentProduct, ih, mul_assoc]

theorem currentProduct_replicate {A : Type} [Semiring A] (F : Fin 3 → ℕ → A)
    (a : Fin 3) (n : ℕ) : currentProduct F (List.replicate n a) = PowerSeries.mk (F a) ^ n := by
  induction n with
  | zero => simp [currentProduct]
  | succ n ih => simp [List.replicate_succ, currentProduct, ih, pow_succ']

/-- Every source coefficient is a linear combination of actual words of the
number of factors in the ordered current product. -/
theorem currentProduct_mem (l : List (Fin 3)) (s : ℕ) :
    (PowerSeries.coeff s (currentProduct (fun a => R.op (negRoot a)) l)) w ∈
      Pbelow R w (l.length + 1) := by
  induction l generalizing s with
  | nil =>
      simp only [currentProduct, PowerSeries.coeff_one]
      split_ifs
      · exact Submodule.subset_span ⟨[], by simp, rfl⟩
      · exact Submodule.zero_mem _
  | cons a l ih =>
      simp only [currentProduct, PowerSeries.coeff_mul, Garland.Fs, PowerSeries.coeff_mk,
        LinearMap.coe_sum, Finset.sum_apply, Module.End.mul_apply]
      apply Submodule.sum_mem
      intro x hx
      exact Pbelow_op R w a x.1 (l.length + 1) (ih x.2)

/-- The actual coefficient symbol agrees with the commuting graded action.
No coefficient ideal or source annihilation premise occurs here. -/
theorem currentProduct_symbol (l : List (Fin 3)) (s : ℕ) :
    (((PowerSeries.coeff s (currentProduct (grOp R w) l)) (grGenerator R w)) :
      AmbientGr R w) = symbol R w l.length
        ((PowerSeries.coeff s (currentProduct (fun a => R.op (negRoot a)) l)) w) := by
  induction l generalizing s with
  | nil =>
      simp only [currentProduct, PowerSeries.coeff_one]
      split_ifs
      · rfl
      · simp
  | cons a l ih =>
      simp only [currentProduct, PowerSeries.coeff_mul, Garland.Fs, PowerSeries.coeff_mk,
        LinearMap.coe_sum, Finset.sum_apply, Module.End.mul_apply, Submodule.coe_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro x hx
      change ambientOp R w a x.1
          (((PowerSeries.coeff x.2 (currentProduct (grOp R w) l)) (grGenerator R w)) :
            AmbientGr R w) = _
      rw [ih, ambientOp_symbol]
      rfl

theorem currentProduct_zero_of_mem (l : List (Fin 3)) (s : ℕ)
    (hrel : (PowerSeries.coeff s (currentProduct (fun a => R.op (negRoot a)) l)) w ∈
      Pbelow R w l.length) :
    (PowerSeries.coeff s (currentProduct (grOp R w) l)) (grGenerator R w) = 0 := by
  apply Subtype.ext
  rw [currentProduct_symbol]
  exact symbol_zero_of_mem R w hrel

/-- The concrete three-color source coefficient used by mixed straightening. -/
def orderedCoeff (p q r s : ℕ) : V :=
  (PowerSeries.coeff s (Garland.Fs (R.op 3) ^ p * Garland.Fs (R.op 5) ^ q *
    Garland.Fs (R.op 4) ^ r)) w

def gradedOrderedCoeff (p q r s : ℕ) : Gr R w :=
  (PowerSeries.coeff s (Garland.Fs (grOp R w 0) ^ p * Garland.Fs (grOp R w 1) ^ q *
    Garland.Fs (grOp R w 2) ^ r)) (grGenerator R w)

theorem orderedCoeff_mem (p q r s : ℕ) :
    orderedCoeff R w p q r s ∈ Pbelow R w (p + q + r + 1) := by
  have hh := currentProduct_mem R w
    (List.replicate p 0 ++ List.replicate q 1 ++ List.replicate r 2) s
  simpa only [currentProduct_append, currentProduct_replicate, List.length_append,
    List.length_replicate] using hh

theorem orderedCoeff_symbol (p q r s : ℕ) :
    (gradedOrderedCoeff R w p q r s : AmbientGr R w) =
      symbol R w (p + q + r) (orderedCoeff R w p q r s) := by
  have hh := currentProduct_symbol R w
    (List.replicate p 0 ++ List.replicate q 1 ++ List.replicate r 2) s
  simpa only [currentProduct_append, currentProduct_replicate, List.length_append,
    List.length_replicate] using hh

theorem gradedOrderedCoeff_zero (p q r s : ℕ)
    (hrel : orderedCoeff R w p q r s ∈ Pbelow R w (p + q + r)) :
    gradedOrderedCoeff R w p q r s = 0 := by
  apply Subtype.ext
  rw [orderedCoeff_symbol]
  exact symbol_zero_of_mem R w hrel

end

end VOA.DeligneAudit.A2.CVRectFiltered

#print axioms VOA.DeligneAudit.A2.CVRectFiltered.currentProduct_symbol
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.orderedCoeff_mem
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.gradedOrderedCoeff_zero
