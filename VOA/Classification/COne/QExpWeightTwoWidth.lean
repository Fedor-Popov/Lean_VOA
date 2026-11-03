import VOA.Classification.COne.QExpKatzSpanning
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Changing the width of a q-expansion

For a Gamma1 form, expansion at width N inserts zero coefficients into its
width-one expansion. This allows full-level product identities to control
Gamma1 coefficients without constructing an averaging operator.
-/

open UpperHalfPlane
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne.SSHecke

theorem nat_mem_strictPeriods_Gamma1 (N m : ℕ) :
    (m : ℝ) ∈ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simpa using
    (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods.nsmul_mem
      (one_mem_strictPeriods_Gamma1 N) m

theorem nat_mem_strictPeriods_Gamma (N : ℕ) :
    (N : ℝ) ∈ (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma]
  exact AddSubgroup.mem_zmultiples _

theorem qParam_nat_pow {m : ℕ} (hm : 0 < m) (τ : ℍ) :
    Function.Periodic.qParam (m : ℝ) τ ^ m = Function.Periodic.qParam 1 τ := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul, Complex.ofReal_natCast,
    Complex.ofReal_one, div_one]
  congr 1
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp

/-- Width-m expansion is obtained by substituting X^m into the width-one expansion. -/
theorem qExpansion_nat_eq_expand {N m : ℕ} [NeZero N] (hm : 0 < m) {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) :
    qExpansion (m : ℝ) F = PowerSeries.expand m hm.ne' (qExpansion 1 F) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hinj : Function.Injective (fun n : ℕ => m * n) := mul_right_injective₀ hm.ne'
  have hsum (τ : ℍ) : HasSum
      (fun n => (PowerSeries.expand m hm.ne' (qExpansion 1 F)).coeff n •
        Function.Periodic.qParam (m : ℝ) τ ^ n) (F τ) := by
    apply (hinj.hasSum_iff ?_).mp
    · simpa only [Function.comp_def, PowerSeries.coeff_expand_mul, pow_mul,
        qParam_nat_pow hm] using
        hasSum_qExpansion one_pos
          (SlashInvariantFormClass.periodic_comp_ofComplex F (one_mem_strictPeriods_Gamma1 N))
          (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F) τ
    · intro n hn
      have hnd : ¬ m ∣ n := by
        rintro ⟨j, rfl⟩
        exact hn ⟨j, rfl⟩
      rw [PowerSeries.coeff_expand_of_not_dvd m hm.ne' _ hnd, zero_smul]
  ext n
  exact (ModularFormClass.qExpansion_coeff_unique hmR
    (nat_mem_strictPeriods_Gamma1 N m) hsum n).symm

/-- The width-one coefficients are a subsequence of the width-m coefficients. -/
theorem qExpansion_coeff_nat_mul {N m : ℕ} [NeZero N] (hm : 0 < m) {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
    (n : ℕ) :
    (qExpansion (m : ℝ) F).coeff (m * n) = (qExpansion 1 F).coeff n := by
  rw [qExpansion_nat_eq_expand hm, PowerSeries.coeff_expand_mul]

end VOA.Classification.COne.SSHecke
