import VOA.DeligneAudit.DeligneFusionCVPolarization
import VOA.DeligneAudit.DeligneFusionCVFinite
import VOA.DeligneAudit.DeligneFusionCVUnivDimension

/-!
# The zero-auxiliary residual theta base

The actual CV presentation of highest weight theta has an explicit eight-vector
span. The proof uses current commutators, polarization and highest-weight PBW
sorting. No irreducibility, Demazure identification or dimension premise occurs.
-/

namespace VOA.DeligneAudit.A2.CVResidualThetaZero

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVUniv
open VOA.DeligneAudit.A2.CVPolarization

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V}

/-- The eight classical adjoint words, with two independent zero-weight words. -/
def adjointVector (R : CurrentModule bracketTable V) (w : V) : Fin 8 → V :=
  ![w, R.op 3 0 w, R.op 4 0 w, R.op 5 0 w,
    R.op 3 0 (R.op 4 0 w), R.op 3 0 (R.op 5 0 w),
    R.op 5 0 (R.op 4 0 w), R.op 5 0 (R.op 5 0 w)]

def adjointSpan (R : CurrentModule bracketTable V) (w : V) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range (adjointVector R w))

private theorem vector_mem (i : Fin 8) : adjointVector R w i ∈ adjointSpan R w :=
  Submodule.subset_span ⟨i, rfl⟩

private theorem positive_generator (h : CV3Rel R w (0, 0) (0, 0) (0, 0) 1)
    (d : Fin 8) (q : ℕ) (hq : 1 ≤ q) : R.op d q w = 0 := by
  have hd : d.val < 3 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ 6 ≤ d.val := by omega
  rcases hd with hd | rfl | rfl | rfl | hd
  · exact h.raising d hd q
  · exact trunc_of_cvrel h.first q (by simpa [parts] using hq)
  · exact trunc_of_cvrel h.second q (by simpa [parts] using hq)
  · exact trunc_of_cvrel h.highest q (by simpa [parts] using hq)
  · exact h.cartan_pos d hd q hq

/-- Positive modes kill every zero-mode word, not just the cyclic generator. -/
theorem positive_zero_word (h : CV3Rel R w (0, 0) (0, 0) (0, 0) 1) :
    ∀ (l : List (Fin 8)) (d : Fin 8) (q : ℕ), 1 ≤ q →
      R.op d q (wordOp R (l.map fun e => (e, 0)) w) = 0
  | [], d, q, hq => positive_generator h d q hq
  | e :: l, d, q, hq => by
      change R.op d q (R.op e 0 (wordOp R (l.map fun e => (e, 0)) w)) = 0
      rw [comm_apply]
      simp only [positive_zero_word h l _ _ hq, map_zero,
        smul_zero, Finset.sum_const_zero, add_zero]

private theorem mixed_first (h : CV3Rel R w (0, 0) (0, 0) (0, 0) 1)
    (p q : ℕ) (hpq : p + q = 3) :
    (R.op 3 0 ^ p) ((R.op 5 0 ^ q) w) = 0 := by
  have hp := theta_cvrel_mixed R (h.raising 1 (by decide) 0) h.highest p q 0 0
    (by omega) (by simp [parts, T]; omega)
  simpa [mixedCoeff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    Garland.Fs, Module.End.mul_apply] using hp

private theorem second_theta_square (h : CV3Rel R w (0, 0) (0, 0) (0, 0) 1) :
    R.op 4 0 (R.op 5 0 (R.op 5 0 w)) = 0 := by
  have hQ := h.highest 3 0 0 (by omega) (by simp [parts, T])
  have hp := mixedCoeff_zero_of_Q (R.op 5) (R.op 4) (-R.op 0 0)
    (by intro k
        calc
          (-R.op 0 0) * R.op 5 k - R.op 5 k * (-R.op 0 0) =
              -(R.op 0 0 * R.op 5 k - R.op 5 k * R.op 0 0) := by noncomm_ring
          _ = R.op 4 k := by rw [op_comm_end]; simp [Fin.sum_univ_eight, bracketTable])
    (by intro k; rw [neg_mul, mul_neg, neg_inj, ← sub_eq_zero, op_comm_end];
        simp [Fin.sum_univ_eight, bracketTable])
    (by intro k l; rw [← sub_eq_zero, op_comm_end];
        simp [Fin.sum_univ_eight, bracketTable])
    (by simp [h.raising 0 (by decide) 0]) hQ 1 2 (by omega)
  simpa [mixedCoeff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    Garland.Fs, Module.End.mul_apply, pow_succ] using hp

/-- The lowering operators preserve the explicit eight-vector span. -/
theorem lowering_stable (h : CV3Rel R w (0, 0) (0, 0) (0, 0) 1)
    (d : Fin 8) (hd : 3 ≤ d.val ∧ d.val < 6) (q : ℕ) :
    adjointSpan R w ≤ (adjointSpan R w).comap (R.op d q) := by
  let X := R.op 3 0
  let Y := R.op 4 0
  let Z := R.op 5 0
  have hYX : ∀ v, Y (X v) = X (Y v) + Z v := by
    intro v; rw [comm_apply]; simp [X, Y, Z, Fin.sum_univ_eight, bracketTable]
  have hZX : ∀ v, Z (X v) = X (Z v) := fun v => (op3_op5 0 0 v).symm
  have hYZ : ∀ v, Y (Z v) = Z (Y v) := op4_op5 0 0
  have hX2 : X (X w) = 0 := by simpa [X, Function.iterate_succ_apply'] using h.lowering_first
  have hY2 : Y (Y w) = 0 := by simpa [Y, Function.iterate_succ_apply'] using h.lowering_second
  have hX2Z : X (X (Z w)) = 0 := by
    simpa [X, Z, pow_two, Module.End.mul_apply] using mixed_first h 2 1 (by decide)
  have hXZ2 : X (Z (Z w)) = 0 := by
    simpa [X, Z, pow_two, Module.End.mul_apply] using mixed_first h 1 2 (by decide)
  have hZ3 : Z (Z (Z w)) = 0 := by
    simpa [Z, pow_succ, Module.End.mul_apply] using mixed_first h 0 3 (by decide)
  have hYZ2 : Y (Z (Z w)) = 0 := second_theta_square h
  have hX2Y : X (X (Y w)) = -(2 : ℂ) • X (Z w) := by
    rw [neg_smul]
    apply eq_neg_iff_add_eq_zero.mpr
    calc
      X (X (Y w)) + (2 : ℂ) • X (Z w) = Y (X (X w)) := by
        rw [hYX, hYX, map_add, hZX]; module
      _ = 0 := by rw [hX2, map_zero]
  have hfour : (4 : ℂ) • X (Z (Y w)) = -(2 : ℂ) • Z (Z w) := by
    rw [neg_smul]
    apply eq_neg_iff_add_eq_zero.mpr
    calc
      (4 : ℂ) • X (Z (Y w)) + (2 : ℂ) • Z (Z w) = Y (Y (X (X w))) := by
        simp only [hYX, map_add, hZX, hYZ, hY2, map_zero]
        module
      _ = 0 := by rw [hX2, map_zero, map_zero]
  have hXYZmem : X (Z (Y w)) ∈ adjointSpan R w := by
    apply (Submodule.smul_mem_iff (adjointSpan R w) (by norm_num : (4 : ℂ) ≠ 0)).mp
    rw [hfour]
    exact Submodule.smul_mem _ _ (vector_mem (R := R) (w := w) 7)
  have hv (i : Fin 8) := vector_mem (R := R) (w := w) i
  have hXYmem : X (Y w) ∈ adjointSpan R w := hv 4
  have hXZmem : X (Z w) ∈ adjointSpan R w := hv 5
  have hZYmem : Z (Y w) ∈ adjointSpan R w := hv 6
  have hZZmem : Z (Z w) ∈ adjointSpan R w := hv 7
  rw [adjointSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  change R.op d q (adjointVector R w i) ∈ adjointSpan R w
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hd' : d = 3 ∨ d = 4 ∨ d = 5 := by omega
    rcases hd' with rfl | rfl | rfl
    · fin_cases i
      · exact hv 1
      · change X (X w) ∈ _; rw [hX2]; exact Submodule.zero_mem _
      · exact hXYmem
      · exact hXZmem
      · change X (X (Y w)) ∈ _; rw [hX2Y]; exact Submodule.smul_mem _ _ hXZmem
      · change X (X (Z w)) ∈ _; rw [hX2Z]; exact Submodule.zero_mem _
      · exact hXYZmem
      · change X (Z (Z w)) ∈ _; rw [hXZ2]; exact Submodule.zero_mem _
    · fin_cases i
      · exact hv 2
      · change Y (X w) ∈ _; rw [hYX]; exact Submodule.add_mem _ hXYmem (hv 3)
      · change Y (Y w) ∈ _; rw [hY2]; exact Submodule.zero_mem _
      · change Y (Z w) ∈ _; rw [hYZ]; exact hZYmem
      · change Y (X (Y w)) ∈ _; rw [hYX, hY2, map_zero, zero_add]; exact hZYmem
      · change Y (X (Z w)) ∈ _; rw [hYX, hYZ]; exact Submodule.add_mem _ hXYZmem hZZmem
      · change Y (Z (Y w)) ∈ _; rw [hYZ, hY2, map_zero]; exact Submodule.zero_mem _
      · change Y (Z (Z w)) ∈ _; rw [hYZ2]; exact Submodule.zero_mem _
    · fin_cases i
      · exact hv 3
      · change Z (X w) ∈ _; rw [hZX]; exact hXZmem
      · exact hZYmem
      · exact hZZmem
      · change Z (X (Y w)) ∈ _; rw [hZX]; exact hXYZmem
      · change Z (X (Z w)) ∈ _; rw [hZX, hXZ2]; exact Submodule.zero_mem _
      · change Z (Z (Y w)) ∈ _; rw [← hYZ, ← hYZ, hYZ2]; exact Submodule.zero_mem _
      · change Z (Z (Z w)) ∈ _; rw [hZ3]; exact Submodule.zero_mem _
  · have hz : R.op d q (adjointVector R w i) = 0 := by
      fin_cases i
      all_goals first
        | exact positive_zero_word h [] d q hq
        | exact positive_zero_word h [3] d q hq
        | exact positive_zero_word h [4] d q hq
        | exact positive_zero_word h [5] d q hq
        | exact positive_zero_word h [3, 4] d q hq
        | exact positive_zero_word h [3, 5] d q hq
        | exact positive_zero_word h [5, 4] d q hq
        | exact positive_zero_word h [5, 5] d q hq
    rw [hz]
    exact Submodule.zero_mem _

/-- Every actual current word belongs to the eight-vector span. -/
theorem cyclic_le_adjoint (h : CV3Rel R w (0, 0) (0, 0) (0, 0) 1) :
    cycSub R w ≤ adjointSpan R w := by
  rw [cycSub, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  have hs := CVFinite.cycDeg_le_sortedFin_of_cv3Rel h
    (VOA.DeligneAudit.SectorGraded.wordDeg l)
    (Submodule.subset_span ⟨l, rfl, rfl⟩)
  apply Submodule.span_le.mpr ?_ hs
  rintro _ ⟨l', _, hl', _, rfl⟩
  have hlow : ∀ (ll : List (Fin 8 × ℕ)), (∀ x ∈ ll, lowSl3 x.1) →
      wordOp R ll w ∈ adjointSpan R w := by
    intro ll
    induction ll with
    | nil => intro _; exact vector_mem 0
    | cons x ll ih =>
        intro hx
        exact lowering_stable h x.1 (hx x List.mem_cons_self) x.2
          (ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)))
  exact hlow l' hl'

/-- A constructive upper bound for the residual theta module with rho zero. -/
theorem adjoint_bound (h : CV3Rel R w (0, 0) (0, 0) (0, 0) 1) :
    FiniteDimensional ℂ (cycSub R w) ∧ Module.finrank ℂ (cycSub R w) ≤ 8 := by
  have hle := cyclic_le_adjoint h
  haveI : FiniteDimensional ℂ (adjointSpan R w) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : FiniteDimensional ℂ (cycSub R w) := Submodule.finiteDimensional_of_le hle
  refine ⟨inferInstance, (Submodule.finrank_mono hle).trans ?_⟩
  simpa using finrank_range_le_card (adjointVector R w)

/-- The actual universal residual module at rho zero is bounded by eight. -/
theorem universal_adjoint_bound :
    FiniteDimensional ℂ (CVMod (0, 0) (0, 0) (0, 0) 1) ∧
      Module.finrank ℂ (CVMod (0, 0) (0, 0) (0, 0) 1) ≤ 8 := by
  have hb := adjoint_bound (cvUniv_rel (0, 0) (0, 0) (0, 0) 1)
  have ht : cycSub (cvUnivRep (0, 0) (0, 0) (0, 0) 1)
      (cv_wU (0, 0) (0, 0) (0, 0) 1) = ⊤ := cv_span_top _ _ _ _
  rw [ht] at hb
  haveI := hb.1
  haveI : FiniteDimensional ℂ (CVMod (0, 0) (0, 0) (0, 0) 1) :=
    Module.Finite.of_surjective (⊤ : Submodule ℂ _).subtype
      (fun v => ⟨⟨v, Submodule.mem_top⟩, rfl⟩)
  exact ⟨inferInstance, by simpa using hb.2⟩

end
end VOA.DeligneAudit.A2.CVResidualThetaZero

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.CVResidualThetaZero.positive_zero_word
#print axioms VOA.DeligneAudit.A2.CVResidualThetaZero.lowering_stable
#print axioms VOA.DeligneAudit.A2.CVResidualThetaZero.adjoint_bound
#print axioms VOA.DeligneAudit.A2.CVResidualThetaZero.universal_adjoint_bound
end AxiomAudit
