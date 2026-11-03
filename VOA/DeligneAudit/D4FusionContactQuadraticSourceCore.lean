import VOA.DeligneAudit.D4FusionContactQuadraticSourceTable
import VOA.DeligneAudit.D4FusionContactFiltration

/-! Actual Levi action on quadratic contact words modulo radical length one. -/
namespace VOA.DeligneAudit.D4FusionContact.Quadratic.Source

open VOA.DeligneAudit.SectorWeyl
open scoped BigOperators

noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V) (w : V)

/-- The actual quotient by the first radical-word filtration piece. -/
abbrev Q := V ⧸ piece R w 1

/-- The symmetric quadratic class of two degree-one radical roots. -/
def quadratic (a b : Fin 8) : Q R w :=
  (piece R w 1).mkQ (R.op (radIndex a.castSucc) 0 (R.op (radIndex b.castSucc) 0 w))

/-- The quadratic columns use the certificate's actual root order. -/
def qcolumn (j : Fin 36) : Q R w := quadratic R w (first j) (second j)

/-- Evaluate an integer coefficient row on actual quadratic classes. -/
def rowEval (c : Fin 36 → ℤ) : Q R w := ∑ j : Fin 36, (c j : ℂ) • qcolumn R w j

private theorem center_mem : R.op 27 0 w ∈ piece R w 1 := by
  exact radicalWord_mem R w [8] (by decide)

/-- The order correction of two radical generators is already in length one. -/
theorem quadratic_symm (a b : Fin 8) : quadratic R w a b = quadratic R w b a := by
  apply eq_of_sub_eq_zero
  change (piece R w 1).mkQ _ - (piece R w 1).mkQ _ = 0
  rw [← map_sub]
  have hc := R.comm (radIndex a.castSucc) (radIndex b.castSucc) 0 0 w
  simp only [contact_table, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Nat.add_zero] at hc
  rw [hc]
  exact (Submodule.Quotient.mk_eq_zero (piece R w 1)).mpr
    (Submodule.smul_mem _ _ (center_mem R w))

/-- Sorting a pair changes no quadratic class. -/
theorem qcolumn_column (a b : Fin 8) :
    qcolumn R w (column a b) = quadratic R w a b := by
  rcases column_indices a b with h | h
  · simp only [qcolumn, h.1, h.2]
  · simpa only [qcolumn, h.1, h.2] using quadratic_symm R w b a

variable {R w} {m : ℕ}

private theorem levi_as_zeroIndex : ∀ i : Fin 3,
    zeroIndex (Fin.natAdd 7 i) = leviIndex i := by decide +kernel

/-- The Levi operator genuinely descends to the quotient by length one. -/
def leviOp (h : HighestRel R w m) (i : Fin 3) : Module.End ℂ (Q R w) :=
  (piece R w 1).mapQ (piece R w 1) (R.op (leviIndex i) 0) (by
    simpa only [levi_as_zeroIndex] using zero_piece_invariant h (Fin.natAdd 7 i) 1)

private theorem levi_apply (i : Fin 3) (a : Fin 8) (v : V) :
    R.op (leviIndex i) 0 (R.op (radIndex a.castSucc) 0 v) =
      (sign i a : ℂ) • R.op (radIndex (target i a).castSucc) 0 v +
        R.op (radIndex a.castSucc) 0 (R.op (leviIndex i) 0 v) := by
  have hc := R.comm (leviIndex i) (radIndex a.castSucc) 0 0 v
  simp only [levi_root, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Nat.add_zero] at hc
  exact sub_eq_iff_eq_add.mp hc

/-- On genuine quadratic classes the Levi action is the two-factor derivation. -/
theorem leviOp_quadratic (h : HighestRel R w m) (i : Fin 3) (a b : Fin 8) :
    leviOp h i (quadratic R w a b) =
      (sign i a : ℂ) • quadratic R w (target i a) b +
        (sign i b : ℂ) • quadratic R w a (target i b) := by
  change (piece R w 1).mkQ
    (R.op (leviIndex i) 0 (R.op (radIndex a.castSucc) 0
      (R.op (radIndex b.castSucc) 0 w))) = _
  rw [levi_apply, levi_apply, h.levi_zero, map_zero, add_zero, map_smul]
  simp only [map_add, map_smul, quadratic]

/-- The certificate transition matrix is the actual induced Levi action. -/
theorem leviOp_qcolumn (h : HighestRel R w m) (i : Fin 3) (j : Fin 36) :
    leviOp h i (qcolumn R w j) =
      ∑ k : Fin 36, (transition i j k : ℂ) • qcolumn R w k := by
  rw [qcolumn, leviOp_quadratic]
  simp only [transition, Int.cast_add, Int.cast_ite, Int.cast_zero,
    add_smul, ite_smul, zero_smul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, qcolumn_column]

/-- Integer row differentiation agrees with actual quotient operators. -/
theorem rowEval_derive (h : HighestRel R w m) (i : Fin 3) (c : Fin 36 → ℤ) :
    rowEval R w (derive i c) = leviOp h i (rowEval R w c) := by
  simp only [rowEval, derive, Int.cast_sum, Int.cast_mul,
    Finset.sum_smul, mul_smul, map_sum, map_smul, leviOp_qcolumn, Finset.smul_sum]
  exact Finset.sum_comm

end
end VOA.DeligneAudit.D4FusionContact.Quadratic.Source

#print axioms VOA.DeligneAudit.D4FusionContact.Quadratic.Source.quadratic_symm
#print axioms VOA.DeligneAudit.D4FusionContact.Quadratic.Source.rowEval_derive
