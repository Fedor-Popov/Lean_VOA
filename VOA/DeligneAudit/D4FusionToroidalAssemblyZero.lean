import VOA.DeligneAudit.D4FusionToroidalD4
import VOA.DeligneAudit.D4FusionTruncatedWeylRank

/-! The degree-zero part of the toroidal associated graded is the first filtration quotient. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) (R : RelSpec n) (m : ℕ)

/-- The zeroth coordinate of a relation in the graded denominator belongs to `TU 1`. -/
theorem denominator_zero_mem (v : ℕ →₀ UModG f R)
    (hv : v ∈ grDenominator f R m) : v 0 ∈ TU f R m 1 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨j, x, hx, rfl⟩ := hv
      by_cases hj : j = 0
      · subst j
        simpa using hx
      · simp [hj]
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa only [Finsupp.coe_add, Pi.add_apply] using
        (Submodule.add_mem (TU f R m 1) ihx ihy)
  | smul a x hx ih =>
      simpa only [Finsupp.coe_smul, Pi.smul_apply] using
        (Submodule.smul_mem (TU f R m 1) a ih)

/-- A class represented at grade zero by a vector of the universal module. -/
def zeroClass : UModG f R →ₗ[ℂ] Gr f R m where
  toFun x := (grKernel f R m).mkQ
    (gradedSingle f R m 0 x (by rw [TU_zero]; trivial))
  map_add' x y := by
    apply congrArg (grKernel f R m).mkQ
    apply Subtype.ext
    simp [gradedSingle]
  map_smul' a x := by
    apply congrArg (grKernel f R m).mkQ
    apply Subtype.ext
    simp [gradedSingle]

theorem zeroClass_ker : LinearMap.ker (zeroClass f R m) = TU f R m 1 := by
  ext x
  constructor
  · intro hx
    have hq : gradedSingle f R m 0 x (by rw [TU_zero]; trivial) ∈
        grKernel f R m :=
      (Submodule.Quotient.mk_eq_zero (grKernel f R m)).mp hx
    have hz := denominator_zero_mem f R m _ hq
    simpa [gradedSingle] using hz
  · intro hx
    change (grKernel f R m).mkQ
      (gradedSingle f R m 0 x (by rw [TU_zero]; trivial)) = 0
    apply (Submodule.Quotient.mk_eq_zero (grKernel f R m)).mpr
    exact gradedSingle_mem_kernel f R m 0 x hx

/-- The degree-zero graded piece, as a submodule of the whole associated graded. -/
def Gzero : Submodule ℂ (Gr f R m) := LinearMap.range (zeroClass f R m)

/-- The first filtration quotient is linearly equivalent to grade zero. -/
def truncEquivZero : FusionToroidal.truncMod f R m ≃ₗ[ℂ] Gzero f R m :=
  (Submodule.quotEquivOfEq (FusionToroidal.TU f R m 1)
    (LinearMap.ker (zeroClass f R m))
    ((TU_eq_filt f R m 1).symm.trans (zeroClass_ker f R m).symm)).trans
    (LinearMap.quotKerEquivRange (zeroClass f R m))

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.denominator_zero_mem
#print axioms VOA.DeligneAudit.Toroidal.zeroClass_ker
#print axioms VOA.DeligneAudit.Toroidal.truncEquivZero
