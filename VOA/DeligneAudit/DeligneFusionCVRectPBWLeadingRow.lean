import VOA.DeligneAudit.DeligneFusionCVRectPBWLeadingCurrent

/-!
# The leading row of two actual source coefficients' commutator

Both source coefficients kill the generator. Their commutator therefore does
so too; its shorter double contractions disappear only after applying the
actual PBW quotient. The remaining single-contraction row is an actual graded
relation, not an assumed commutative presentation.
-/

namespace VOA.DeligneAudit.A2.CVRectPBWLeading

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.A2.CVRectFiltered

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V) (w : V)

def leadingRow (S r T : ℕ) : V :=
  ∑ ij ∈ Finset.antidiagonal S,
    R.op 3 ij.1 ((PowerSeries.coeff T (thetaShift R ij.2 * Garland.Fs (R.op 4) ^ r)) w)

/-- The actual single-contraction row lies in strictly shorter PBW words. -/
theorem leadingRow_below (S r T : ℕ)
    (hA : Q (R.op 3) 2 S w = 0) (hB : Q (R.op 4) (r + 1) T w = 0) :
    leadingRow R w S r T ∈ Pbelow R w (r + 2) := by
  let P := Pbelow R w (r + 2)
  let π := P.mkQ
  let B := Q (R.op 4) (r + 1) T
  have hAop : Q (R.op 3) 2 S =
      ∑ ij ∈ Finset.antidiagonal S, R.op 3 ij.1 * R.op 3 ij.2 := by
    simp only [Q, pow_two, PowerSeries.coeff_mul, Garland.Fs, PowerSeries.coeff_mk]
  have hcomm : (∑ ij ∈ Finset.antidiagonal S,
      (B * (R.op 3 ij.1 * R.op 3 ij.2) - (R.op 3 ij.1 * R.op 3 ij.2) * B) w) = 0 := by
    calc
      _ = (B * Q (R.op 3) 2 S - Q (R.op 3) 2 S * B) w := by
        rw [hAop, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
          LinearMap.sum_apply]
      _ = 0 := by simp only [LinearMap.sub_apply, Module.End.mul_apply, hA, hB, B,
        map_zero, sub_self]
  have hpoint (ij : ℕ × ℕ) :
      π ((B * (R.op 3 ij.1 * R.op 3 ij.2) - (R.op 3 ij.1 * R.op 3 ij.2) * B) w) =
        (r + 1) • π (R.op 3 ij.1
          ((PowerSeries.coeff T (thetaShift R ij.2 * Garland.Fs (R.op 4) ^ r)) w)) +
        (r + 1) • π (R.op 3 ij.2
          ((PowerSeries.coeff T (thetaShift R ij.1 * Garland.Fs (R.op 4) ^ r)) w)) := by
    have hl := (Pbelow R w (r + 2)).nsmul_mem (double_contraction_below R w ij.1 ij.2 r T)
      (r + 1)
    have hz : π ((r + 1) •
        ((r • PowerSeries.coeff T
          (thetaShift R ij.1 * thetaShift R ij.2 * Garland.Fs (R.op 4) ^ (r - 1))) w)) = 0 :=
      (Submodule.Quotient.mk_eq_zero P).mpr hl
    simp only [LinearMap.smul_apply, map_nsmul] at hz
    change π (((Q (R.op 4) (r + 1) T) * _ - _ * (Q (R.op 4) (r + 1) T)) w) = _
    rw [quadratic_commutator_coefficient]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
      map_add, map_nsmul, hz, add_zero]
  have hswap : (∑ ij ∈ Finset.antidiagonal S, π (R.op 3 ij.2
      ((PowerSeries.coeff T (thetaShift R ij.1 * Garland.Fs (R.op 4) ^ r)) w))) =
      ∑ ij ∈ Finset.antidiagonal S, π (R.op 3 ij.1
        ((PowerSeries.coeff T (thetaShift R ij.2 * Garland.Fs (R.op 4) ^ r)) w)) := by
    simpa only [Prod.swap] using
      (Finset.Nat.sum_antidiagonal_swap (n := S)
        (f := fun ij : ℕ × ℕ => π (R.op 3 ij.1
          ((PowerSeries.coeff T (thetaShift R ij.2 * Garland.Fs (R.op 4) ^ r)) w))))
  have hsum := congrArg π hcomm
  have hs : ((r + 1) + (r + 1)) • π (leadingRow R w S r T) = 0 := by
    simp only [map_sum, hpoint, map_zero, Finset.sum_add_distrib] at hsum
    simp only [← Nat.cast_smul_eq_nsmul ℂ] at hsum
    rw [← Finset.smul_sum, ← Finset.smul_sum, hswap] at hsum
    rw [← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_add, add_smul]
    simpa only [leadingRow, map_sum] using hsum
  have hπ : π (leadingRow R w S r T) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at hs
    exact hs.resolve_left (by exact_mod_cast (show (r + 1) + (r + 1) ≠ 0 by omega))
  exact (Submodule.Quotient.mk_eq_zero P).mp hπ

/-- The same row in the actually commuting graded cyclic representation. -/
def gradedLeadingRow (S r T : ℕ) : Gr R w :=
  ∑ ij ∈ Finset.antidiagonal S,
    grOp R w 0 ij.1
      ((PowerSeries.coeff T ((PowerSeries.mk fun k => grOp R w 1 (ij.2 + k)) *
        Garland.Fs (grOp R w 2) ^ r)) (grGenerator R w))

theorem leadingRow_symbol (S r T : ℕ) :
    (gradedLeadingRow R w S r T : AmbientGr R w) =
      symbol R w (r + 2) (leadingRow R w S r T) := by
  simp only [gradedLeadingRow, Submodule.coe_sum, leadingRow, map_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hi := shiftedProduct_symbol R w ((1, ij.2) :: List.replicate r (2, 0)) T
  simp only [shiftedProduct, shiftedProduct_replicate_zero,
    show negRoot (1 : Fin 3) = 5 from rfl, show negRoot (2 : Fin 3) = 4 from rfl,
    List.length_cons, List.length_replicate] at hi
  change ambientOp R w 0 ij.1
    (((PowerSeries.coeff T ((PowerSeries.mk fun k => grOp R w 1 (ij.2 + k)) *
      Garland.Fs (grOp R w 2) ^ r)) (grGenerator R w)) : AmbientGr R w) = _
  simp only [Garland.Fs, thetaShift]
  rw [hi, ambientOp_symbol]
  simp only [Nat.add_assoc, show negRoot (0 : Fin 3) = 3 from rfl]

/-- Actual source vanishing yields an actual graded leading-row relation. -/
theorem gradedLeadingRow_zero (S r T : ℕ)
    (hA : Q (R.op 3) 2 S w = 0) (hB : Q (R.op 4) (r + 1) T w = 0) :
    gradedLeadingRow R w S r T = 0 := by
  apply Subtype.ext
  rw [leadingRow_symbol]
  exact symbol_zero_of_mem R w (leadingRow_below R w S r T hA hB)

end
end VOA.DeligneAudit.A2.CVRectPBWLeading

#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.leadingRow_below
#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.leadingRow_symbol
#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.gradedLeadingRow_zero
