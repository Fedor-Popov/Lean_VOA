import VOA.Moonshine.AutVnat
import Mathlib.LinearAlgebra.Trace

/-!
# Graded traces and the McKay–Thompson series

`mckayThompson` is the regular part of the Laurent series: coefficient `n`
is the trace on weight `n+1`. The repository's `JShift` is `q * J`, so the
identity specialization is `1 + X * mckayThompson 1 = JShift`.
-/

namespace VOA.Moonshine.ConwayNorton

open AutMonster

universe u

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The action on one homogeneous piece, with composition as multiplication. -/
noncomputable def gradedAutAction (V : VertexOperatorAlgebra M) (n : ℤ) :
    Aut V →* Module.End ℂ (V.grading n) where
  toFun g := (GriessAut.autRestrict g n).toLinearMap
  map_one' := by ext x; rfl
  map_mul' g h := by ext x; rfl

/-- The trace of an automorphism on weight `n`. -/
noncomputable def gradedAutTrace (V : VertexOperatorAlgebra M) (g : Aut V) (n : ℤ) : ℂ :=
  LinearMap.trace ℂ (V.grading n) (gradedAutAction V n g)

theorem gradedAutTrace_one (V : VertexOperatorAlgebra M) (n : ℤ) :
    gradedAutTrace V 1 n = (Module.finrank ℂ (V.grading n) : ℂ) := by
  letI := V.finrank n
  simp [gradedAutTrace]

theorem gradedAutTrace_conjugate (V : VertexOperatorAlgebra M) (g h : Aut V) (n : ℤ) :
    gradedAutTrace V (h * g * h⁻¹) n = gradedAutTrace V g n := by
  unfold gradedAutTrace
  rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, inv_mul_cancel_left]

/-- Every automorphism of the named moonshine VOA preserves every integer grade. -/
theorem vnatAut_preserves_grading (g : AutVnat) (n : ℤ) :
    (VnatVOA.grading n).map g.toLinearEquiv.toLinearMap = VnatVOA.grading n :=
  GriessAut.aut_map_grading g n

/-- The regular part of `T_g = q⁻¹ + Σ trace(g | V♮_{n+1}) qⁿ`. -/
noncomputable def mckayThompson (g : AutVnat) : PowerSeries ℂ :=
  PowerSeries.mk fun n => gradedAutTrace VnatVOA g ((n : ℤ) + 1)

@[simp] theorem mckayThompson_coeff (g : AutVnat) (n : ℕ) :
    PowerSeries.coeff n (mckayThompson g) =
      gradedAutTrace VnatVOA g ((n : ℤ) + 1) := by
  simp [mckayThompson]

theorem mckayThompson_coeff_zero (g : AutVnat) :
    PowerSeries.coeff 0 (mckayThompson g) = 0 := by
  rw [mckayThompson_coeff]
  change LinearMap.trace ℂ (VnatVOA.grading 1) (gradedAutAction VnatVOA 1 g) = 0
  have heq : gradedAutAction VnatVOA 1 g = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hx := (gradedAutAction VnatVOA 1 g x).property
    simpa only [VnatVOA_grading_one, Submodule.mem_bot] using hx
  rw [heq, map_zero]

theorem mckayThompson_conjugate (g h : AutVnat) :
    mckayThompson (h * g * h⁻¹) = mckayThompson g := by
  ext n
  simp only [mckayThompson_coeff, gradedAutTrace_conjugate]

/-- Exact coefficientwise identity, accounting for the shift in `JShift = q J`. -/
theorem mckayThompson_one :
    mckayThompson 1 = PowerSeries.mk (fun n => PowerSeries.coeff (n + 1) JShift) := by
  ext n
  rw [mckayThompson_coeff, gradedAutTrace_one, PowerSeries.coeff_mk]
  simpa only [VnatVOA_grading, Nat.cast_add, Nat.cast_one] using
    finrank_gradingNat_eq_coeff_JShift (n + 1)

/-- The power series `q T_g`, in the same normalization as `JShift`. -/
noncomputable def mckayThompsonShift (g : AutVnat) : PowerSeries ℂ :=
  1 + PowerSeries.X * mckayThompson g

theorem mckayThompsonShift_one : mckayThompsonShift 1 = JShift := by
  ext n
  cases n with
  | zero => simp [mckayThompsonShift, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  | succ n => simp [mckayThompsonShift, mckayThompson_one]

/-- The regular part cannot equal `q J`: their constant coefficients differ. -/
theorem mckayThompson_one_ne_JShift : mckayThompson 1 ≠ JShift := by
  intro h
  have hc := congrArg (PowerSeries.coeff (R := ℂ) 0) h
  rw [mckayThompson_coeff_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_JShift] at hc
  exact zero_ne_one hc

end VOA.Moonshine.ConwayNorton
