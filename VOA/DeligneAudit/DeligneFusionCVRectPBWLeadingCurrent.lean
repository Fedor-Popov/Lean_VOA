import VOA.DeligneAudit.DeligneFusionCVRectPBWLeadingRing
import VOA.DeligneAudit.DeligneFusionCVRectFilteredCoeff

/-!
# Shifted current coefficients and the quadratic mixed commutator

The formulas retain the exact lower contraction rather than discarding it.
Its actual PBW length bound is proved from negative-current words.
-/

namespace VOA.DeligneAudit.A2.CVRectPBWLeading

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.A2.CVRectFiltered

noncomputable section

/-- Each factor may start at its own current mode. -/
def shiftedProduct {A : Type*} [Semiring A] (F : Fin 3 → ℕ → A) :
    List NegLtr → PowerSeries A
  | [] => 1
  | (a, b) :: l => PowerSeries.mk (fun k => F a (b + k)) * shiftedProduct F l

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V) (w : V)

theorem shiftedProduct_mem (l : List NegLtr) (s : ℕ) :
    (PowerSeries.coeff s (shiftedProduct (fun a => R.op (negRoot a)) l)) w ∈
      Pbelow R w (l.length + 1) := by
  induction l generalizing s with
  | nil =>
      simp only [shiftedProduct, PowerSeries.coeff_one]
      split_ifs
      · exact Submodule.subset_span ⟨[], by simp, rfl⟩
      · exact Submodule.zero_mem _
  | cons x l ih =>
      rcases x with ⟨a, b⟩
      simp only [shiftedProduct, PowerSeries.coeff_mul, PowerSeries.coeff_mk,
        LinearMap.coe_sum, Finset.sum_apply, Module.End.mul_apply]
      apply Submodule.sum_mem
      intro ij hij
      exact Pbelow_op R w a (b + ij.1) (l.length + 1) (ih ij.2)

theorem shiftedProduct_symbol (l : List NegLtr) (s : ℕ) :
    (((PowerSeries.coeff s (shiftedProduct (grOp R w) l)) (grGenerator R w)) :
      AmbientGr R w) = symbol R w l.length
        ((PowerSeries.coeff s (shiftedProduct (fun a => R.op (negRoot a)) l)) w) := by
  induction l generalizing s with
  | nil =>
      simp only [shiftedProduct, PowerSeries.coeff_one]
      split_ifs
      · rfl
      · simp
  | cons x l ih =>
      rcases x with ⟨a, b⟩
      simp only [shiftedProduct, PowerSeries.coeff_mul, PowerSeries.coeff_mk,
        LinearMap.coe_sum, Finset.sum_apply, Module.End.mul_apply, Submodule.coe_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro ij hij
      change ambientOp R w a (b + ij.1)
        (((PowerSeries.coeff ij.2 (shiftedProduct (grOp R w) l)) (grGenerator R w)) :
          AmbientGr R w) = _
      rw [ih, ambientOp_symbol]
      rfl

theorem shiftedProduct_replicate_zero {A : Type*} [Semiring A]
    (F : Fin 3 → ℕ → A) (a : Fin 3) (n : ℕ) :
    shiftedProduct F (List.replicate n (a, 0)) = PowerSeries.mk (F a) ^ n := by
  induction n with
  | zero => simp [shiftedProduct]
  | succ n ih => simp [List.replicate_succ, shiftedProduct, ih, pow_succ']

/-- The central current shifted by one fixed first-root mode. -/
def thetaShift (i : ℕ) : PowerSeries (Module.End ℂ V) :=
  PowerSeries.mk (fun k => R.op 5 (i + k))

theorem second_thetaShift_commute (i : ℕ) :
    Garland.Fs (R.op 4) * thetaShift R i = thetaShift R i * Garland.Fs (R.op 4) := by
  apply current_series_commute
  intro a b
  ext v
  exact op4_op5 a (i + b) v

theorem second_first_series_commutator (i : ℕ) :
    Garland.Fs (R.op 4) * PowerSeries.C (R.op 3 i) -
      PowerSeries.C (R.op 3 i) * Garland.Fs (R.op 4) = thetaShift R i := by
  apply PowerSeries.ext
  intro k
  simp only [map_sub, PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul,
    Garland.Fs, thetaShift, PowerSeries.coeff_mk]
  rw [op_comm_end]
  simp [Fin.sum_univ_eight, bracketTable, Nat.add_comm]

theorem thetaShift_first_commute (i j : ℕ) :
    thetaShift R i * PowerSeries.C (R.op 3 j) =
      PowerSeries.C (R.op 3 j) * thetaShift R i := by
  apply PowerSeries.ext
  intro k
  simp only [PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul, thetaShift,
    PowerSeries.coeff_mk]
  ext v
  exact (op3_op5 j (i + k) v).symm

/-- Extracting a current coefficient leaves two leading single contractions
and one explicit double contraction of shorter PBW length. -/
theorem quadratic_commutator_coefficient (i j r t : ℕ) :
    Q (R.op 4) (r + 1) t * (R.op 3 i * R.op 3 j) -
      (R.op 3 i * R.op 3 j) * Q (R.op 4) (r + 1) t =
      (r + 1) • (R.op 3 i * PowerSeries.coeff t (thetaShift R j * Garland.Fs (R.op 4) ^ r)) +
      (r + 1) • (R.op 3 j * PowerSeries.coeff t (thetaShift R i * Garland.Fs (R.op 4) ^ r)) +
      (r + 1) • (r • PowerSeries.coeff t
        (thetaShift R i * thetaShift R j * Garland.Fs (R.op 4) ^ (r - 1))) := by
  have he := power_mul_two_commutator (second_first_series_commutator R i)
    (second_first_series_commutator R j) (second_thetaShift_commute R i)
    (second_thetaShift_commute R j) (thetaShift_first_commute R i j) r
  have hCC : PowerSeries.C (R.op 3 i) * PowerSeries.C (R.op 3 j) =
      PowerSeries.C (R.op 3 i * R.op 3 j) := (map_mul PowerSeries.C _ _).symm
  rw [hCC] at he
  have hc := congrArg (PowerSeries.coeff t) he
  simpa only [map_sub, map_add, map_nsmul, mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_C_mul, Q] using hc

/-- The double contraction is genuinely a shorter negative-current coefficient. -/
theorem double_contraction_below (i j r t : ℕ) :
    (r • PowerSeries.coeff t
      (thetaShift R i * thetaShift R j * Garland.Fs (R.op 4) ^ (r - 1))) w ∈
      Pbelow R w (r + 2) := by
  cases r with
  | zero => simp
  | succ r =>
      have hh := shiftedProduct_mem R w
        ((1, i) :: (1, j) :: List.replicate r (2, 0)) t
      have he : shiftedProduct (fun a => R.op (negRoot a))
          ((1, i) :: (1, j) :: List.replicate r (2, 0)) =
          thetaShift R i * thetaShift R j * Garland.Fs (R.op 4) ^ r := by
        simp only [shiftedProduct, shiftedProduct_replicate_zero,
          show negRoot (1 : Fin 3) = 5 from rfl, show negRoot (2 : Fin 3) = 4 from rfl,
          thetaShift, Garland.Fs, mul_assoc]
      rw [he] at hh
      have hm : (PowerSeries.coeff t
          (thetaShift R i * thetaShift R j * Garland.Fs (R.op 4) ^ r)) w ∈
          Pbelow R w (r + 1 + 2) := by simpa using hh
      simpa only [Nat.add_sub_cancel, LinearMap.smul_apply] using
        (Pbelow R w (r + 1 + 2)).nsmul_mem hm (r + 1)

end
end VOA.DeligneAudit.A2.CVRectPBWLeading

#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.shiftedProduct_symbol
#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.quadratic_commutator_coefficient
#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.double_contraction_below
