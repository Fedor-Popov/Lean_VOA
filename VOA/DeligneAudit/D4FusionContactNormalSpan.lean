import VOA.DeligneAudit.D4FusionContactQuadraticSpanning
import VOA.DeligneAudit.D4FusionContactQuadraticCoverage
import VOA.DeligneAudit.D4FusionContactOperators
import VOA.DeligneAudit.D4FusionContactFiltration

/-! # Explicit 28-vector contact spanning from actual quadratic rows -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl
open Quadratic

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V) (w : V)

abbrev NormalIndex := Unit ⊕ (Fin 9 ⊕ (Fin 9 ⊕ Fin 9))

def quadraticColumn (j : Fin 36) : V := R.op (pair j).1 0 (R.op (pair j).2 0 w)

/-- One highest vector, nine linear vectors, nine center products, and
nine quadratic normal columns. No independence claim is made. -/
def normalVector : NormalIndex → V
  | .inl _ => w
  | .inr (.inl i) => R.op (radIndex i) 0 w
  | .inr (.inr (.inl i)) => R.op (radIndex i) 0 (center R w)
  | .inr (.inr (.inr i)) => quadraticColumn R w (normalColumn i)

def normalSpan : Submodule ℂ V := Submodule.span ℂ (Set.range (normalVector R w))

theorem normal_generator_mem : w ∈ normalSpan R w :=
  Submodule.subset_span ⟨.inl (), rfl⟩

theorem normal_linear_mem (i : Fin 9) : R.op (radIndex i) 0 w ∈ normalSpan R w :=
  Submodule.subset_span ⟨.inr (.inl i), rfl⟩

theorem normal_center_mem (i : Fin 9) :
    R.op (radIndex i) 0 (center R w) ∈ normalSpan R w :=
  Submodule.subset_span ⟨.inr (.inr (.inl i)), rfl⟩

theorem normal_quadratic_mem (i : Fin 9) :
    quadraticColumn R w (normalColumn i) ∈ normalSpan R w :=
  Submodule.subset_span ⟨.inr (.inr (.inr i)), rfl⟩

theorem piece_one_le_normal : piece R w 1 ≤ normalSpan R w := by
  rw [piece, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  cases l with
  | nil => exact normal_generator_mem R w
  | cons i l =>
      have hz : l = [] := List.length_eq_zero_iff.mp (by
            simp only [List.length_cons] at hl
            omega)
      subst l
      exact normal_linear_mem R w i

variable {R w}

theorem column_mem_normal
    (hrows : ∀ r : Fin 27, (∑ j : Fin 36, (raw r j : ℂ) • quadraticColumn R w j) ∈
      piece R w 1) (j : Fin 36) : quadraticColumn R w j ∈ normalSpan R w := by
  apply (sup_le (piece_one_le_normal R w) ?_)
    (raw_rows_mem_implies_span (piece R w 1) (quadraticColumn R w) hrows j)
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact normal_quadratic_mem R w i

private theorem center_rad_comm (i : Fin 9) :
    center R * R.op (radIndex i) 0 = R.op (radIndex i) 0 * center R := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rfl
  · exact center_root_comm R j

private theorem two_root_mem_normal
    (hrows : ∀ r : Fin 27, (∑ j : Fin 36, (raw r j : ℂ) • quadraticColumn R w j) ∈
      piece R w 1) (i j : Fin 8) :
    R.op (radIndex i.castSucc) 0 (R.op (radIndex j.castSucc) 0 w) ∈ normalSpan R w := by
  by_cases hij : (radIndex i.castSucc).val ≤ (radIndex j.castSucc).val
  · obtain ⟨k, hk⟩ := pair_coverage i j hij
    simpa only [quadraticColumn, hk] using column_mem_normal hrows k
  · have hji : (radIndex j.castSucc).val ≤ (radIndex i.castSucc).val := by omega
    obtain ⟨k, hk⟩ := pair_coverage j i hji
    have hs : R.op (radIndex j.castSucc) 0 (R.op (radIndex i.castSucc) 0 w) ∈
        normalSpan R w := by
      simpa only [quadraticColumn, hk] using column_mem_normal hrows k
    have hc : R.op (radIndex i.castSucc) 0 (R.op (radIndex j.castSucc) 0 w) -
        R.op (radIndex j.castSucc) 0 (R.op (radIndex i.castSucc) 0 w) =
        (contactCoeff i.castSucc j.castSucc : ℂ) • center R w := by
      simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Nat.zero_add, center] using
        congrArg (fun T : Module.End ℂ V => T w) (contact_comm (R := R) i.castSucc j.castSucc 0 0)
    rw [sub_eq_iff_eq_add] at hc
    rw [hc]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (normal_linear_mem R w 8)) hs

theorem pair_mem_normal
    (hrows : ∀ r : Fin 27, (∑ j : Fin 36, (raw r j : ℂ) • quadraticColumn R w j) ∈
      piece R w 1) (i j : Fin 9) : radicalWord R [i,j] w ∈ normalSpan R w := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · have hc : center R (R.op (radIndex j) 0 w) = R.op (radIndex j) 0 (center R w) :=
      congrArg (fun T : Module.End ℂ V => T w) (center_rad_comm (R := R) j)
    change center R (R.op (radIndex j) 0 w) ∈ normalSpan R w
    rw [hc]
    exact normal_center_mem R w j
  · refine Fin.lastCases ?_ (fun b => ?_) j
    · exact normal_center_mem R w a.castSucc
    · exact two_root_mem_normal hrows a b

theorem piece_two_le_normal
    (hrows : ∀ r : Fin 27, (∑ j : Fin 36, (raw r j : ℂ) • quadraticColumn R w j) ∈
      piece R w 1) : piece R w 2 ≤ normalSpan R w := by
  rw [piece, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  cases l with
  | nil => exact normal_generator_mem R w
  | cons i l =>
      cases l with
      | nil => exact normal_linear_mem R w i
      | cons j l =>
          have hz : l = [] := List.length_eq_zero_iff.mp (by
            simp only [List.length_cons] at hl
            omega)
          subst l
          exact pair_mem_normal hrows i j

/-- The actual contact normal space has at most 28 dimensions, without
requiring the ambient module to be finite dimensional. -/
theorem normalSpan_bound : FiniteDimensional ℂ (normalSpan R w) ∧
    Module.finrank ℂ (normalSpan R w) ≤ 28 := by
  classical
  haveI : FiniteDimensional ℂ (normalSpan R w) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  refine ⟨inferInstance, ?_⟩
  exact (finrank_range_le_card (normalVector R w)).trans (by decide)

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.piece_two_le_normal
#print axioms VOA.DeligneAudit.D4FusionContact.normalSpan_bound
