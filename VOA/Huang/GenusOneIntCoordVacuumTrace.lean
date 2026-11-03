import VOA.Huang.GenusOneG1cSCovariance

/-!
# The vacuum iterate as a convergent sum of Zhu one-point functions

The inner coefficients below are actual vectors of the VOA, independent of the
traced module and the modular parameter. No intertwiner coordinate substitution
is used. The coordinate in this file is the plane separation, not its logarithm.
-/

noncomputable section
namespace VOA.Huang.GenusOne.IntCoord
open VOA GenusTwoPoint GenusOneG1c VerlindeFusion VerlindeTransport TensorCat
open scoped BigOperators
universe u w
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P Q : LWModule W}

/-- The coefficient of plane degree `k - α - β` in a vacuum-target intertwiner. -/
def vacuumInnerCoeff (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    (wa : P.carrier) (wb : Q.carrier) (α β : ℂ) (k : ℕ) : V :=
  Y.val (α + β - 1 - k) wa wb

theorem vacuumInnerCoeff_mem_grading
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    {wa : P.carrier} {wb : Q.carrier} {α β : ℂ}
    (hwa : wa ∈ P.isMod.weight α) (hwb : wb ∈ Q.isMod.weight β) (k : ℕ) :
    vacuumInnerCoeff Y wa wb α β k ∈ W.grading (k : ℤ) := by
  have h := FusionTop.mem_weight Y.property hwa hwb (α + β - 1 - k)
  rw [show α + β - (α + β - 1 - (k : ℂ)) - 1 = ((k : ℤ) : ℂ) by
    push_cast; ring] at h
  change vacuumInnerCoeff Y wa wb α β k ∈ adjWeight W ((k : ℤ) : ℂ) at h
  simpa only [adjWeight_cast] using h

variable {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)

/-- Exact identification with the existing Zhu trace function, for every state. -/
theorem vacuum_traceFunction_eq (x : ι) (v : V) (τ : UpperHalfPlane) :
    traceFunction (moduleIntertwiner (lwOf D x).isMod) (lwOf D x).h v τ =
      traceFun D.Mfam D.h x v τ := by
  simp only [traceFunction, trace_moduleIntertwiner, traceFun, torusOnePoint, lwOf]
  rfl

/-- Evaluate a fixed inner-mode row of the vacuum iterate. This equality of
total sums needs no convergence assumption; convergence is supplied separately. -/
theorem vacuum_iterate_row (hv : W.vacuum ≠ 0)
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    {wa : P.carrier} {wb : Q.carrier} {α β : ℂ}
    (hwa : wa ∈ P.isMod.weight α) (hwb : wb ∈ Q.isMod.weight β)
    (x : ι) (τ : UpperHalfPlane) (z : ℂ) (k : ℕ) :
    (∑' j : ℕ, iterateTerm (Q := vacuumLW W hv) (N := lwOf D x)
      (moduleIntertwiner (lwOf D x).isMod) Y wa wb α β
      ((lwOf D x).h + j) z 1 k * qFactor (lwOf D x) τ j) =
      z ^ ((k : ℂ) - α - β) *
        traceFun D.Mfam D.h x (vacuumInnerCoeff Y wa wb α β k) τ := by
  simp only [iterateTerm_eq_onePoint _ _ hwa hwb, Complex.one_cpow, mul_one]
  have he : -((α + β - 1 - (vacuumLW W hv).h) - (k : ℂ)) - 1 =
      (k : ℂ) - α - β := by change -((α + β - 1 - 0) - _) - 1 = _; ring
  rw [he]
  simp only [vacuumLW, sub_zero]
  change (∑' j : ℕ, trace (moduleIntertwiner (lwOf D x).isMod)
    (vacuumInnerCoeff Y wa wb α β k) ((lwOf D x).h + j - W.centralCharge / 24) *
    z ^ ((k : ℂ) - α - β) * qFactor (lwOf D x) τ j) = _
  simp only [qFactor, trace_moduleIntertwiner, traceFun, torusOnePoint, qEvalAt]
  have he' : ∀ j : ℕ, (lwOf D x).h + j - W.centralCharge / 24 =
      D.h x - W.centralCharge / 24 + j := by intro j; change D.h x + _ - _ = _; ring
  simp only [he']
  simp_rw [show ∀ j : ℕ,
    onePoint (lwOf D x).isMod (vacuumInnerCoeff Y wa wb α β k)
      (D.h x - W.centralCharge / 24 + j) * z ^ ((k : ℂ) - α - β) *
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) *
        ((lwOf D x).h - W.centralCharge / 24)) * qParam τ ^ j) =
    (z ^ ((k : ℂ) - α - β) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (τ : ℂ) * (D.h x - W.centralCharge / 24))) *
      (onePoint (lwOf D x).isMod (vacuumInnerCoeff Y wa wb α β k)
        (D.h x - W.centralCharge / 24 + j) * qParam τ ^ j) by
    intro j; change _ * _ * (Complex.exp (_ * (D.h x - _)) * _) = _; ring]
  rw [tsum_mul_left]
  exact mul_assoc _ _ _

/-- Fubini for the actual vacuum iterate: the outer vertex operator gives Zhu
one-point functions, with the exact plane exponents and absolute convergence. -/
theorem vacuum_iterF_eq_tsum_traceFun (hv : W.vacuum ≠ 0)
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    {wa : P.carrier} {wb : Q.carrier} {α β : ℂ}
    (hwa : wa ∈ P.isMod.weight α) (hwb : wb ∈ Q.isMod.weight β)
    (x : ι) (τ : UpperHalfPlane) (z : ℂ)
    (hs : IterateSewingSummable (Q := vacuumLW W hv) (N := lwOf D x)
      (moduleIntertwiner (lwOf D x).isMod) Y wa wb α β z 1 τ) :
    HasSum (fun k : ℕ => z ^ ((k : ℂ) - α - β) *
      traceFun D.Mfam D.h x (vacuumInnerCoeff Y wa wb α β k) τ)
      (iterF (Q := vacuumLW W hv) (N := lwOf D x)
        (moduleIntertwiner (lwOf D x).isMod) Y wa wb α β τ z) := by
  have hrow := vacuum_iterate_row D hv Y hwa hwb x τ z
  have hs' := hs.prod_symm.prod
  have he : iterF (Q := vacuumLW W hv) (N := lwOf D x)
      (moduleIntertwiner (lwOf D x).isMod) Y wa wb α β τ z =
      ∑' k : ℕ, z ^ ((k : ℂ) - α - β) *
        traceFun D.Mfam D.h x (vacuumInnerCoeff Y wa wb α β k) τ := by
    unfold iterF
    rw [hs.tsum_prod]
    rw [← Summable.tsum_comm (f := fun j k : ℕ =>
      iterateTerm (Q := vacuumLW W hv) (N := lwOf D x)
        (moduleIntertwiner (lwOf D x).isMod) Y wa wb α β
        ((lwOf D x).h + j) z 1 k * qFactor (lwOf D x) τ j) hs]
    exact tsum_congr hrow
  rw [he]
  exact (hs'.congr hrow).hasSum

/-- The complete family has a common positive plane radius for each τ. The
state coefficients are independent of both τ and the traced label. -/
theorem vacuumChannel_plane_expansion (hV : StronglyRational W)
    (F : FusionChoice W) (hv : W.vacuum ≠ 0) {a b : ι} (c : TransferChoice F D a b)
    {wa : (lwOf D a).carrier} {wb : (lwOf D b).carrier} {α β : ℂ}
    (hwa : wa ∈ (lwOf D a).isMod.weight α) (hwb : wb ∈ (lwOf D b).isMod.weight β)
    (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : ι) (z : ℂ), 0 < z.re → ‖z‖ < δ →
      HasSum (fun k : ℕ => z ^ ((k : ℂ) - α - β) *
        traceFun D.Mfam D.h x (vacuumInnerCoeff (epsInt F c) wa wb α β k) τ)
        (iterF (Q := vacuumLW W hv) (N := lwOf D x)
          (moduleIntertwiner (lwOf D x).isMod) (epsInt F c) wa wb α β τ z) := by
  have hr : ∀ x : ι, ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, 0 < z.re → ‖z‖ < δ →
      IterateSewingSummable (Q := vacuumLW W hv) (N := lwOf D x)
        (moduleIntertwiner (lwOf D x).isMod) (epsInt F c) wa wb α β z 1 τ := by
    intro x
    obtain ⟨δ, hδ, -, hs⟩ := GenusOneG1b.exists_iterateSewingRadius_holds hV
      (lwOf_irreducible D a) (lwOf_irreducible D b) (lwOf_irreducible D x)
      ((isSimple_iff_adjointModule_isIrreducible W).mp hV.simple)
      (Q := vacuumLW W hv) (moduleIntertwiner (lwOf D x).isMod) (epsInt F c) hwa hwb τ
    refine ⟨δ, hδ, fun z hz hnorm => hs z 1 ?_ one_ne_zero (by simpa using hnorm)⟩
    exact fun he => by simp [he] at hz
  choose r hrpos hrs using hr
  let δ : ℝ := Finset.univ.inf' ⟨a, Finset.mem_univ a⟩ r
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).mpr fun x _ => hrpos x
  refine ⟨δ, hδ, fun x z hz hnorm => ?_⟩
  exact vacuum_iterF_eq_tsum_traceFun D hv (epsInt F c) hwa hwb x τ z
    (hrs x z hz (hnorm.trans_le (Finset.inf'_le r (Finset.mem_univ x))))

end VOA.Huang.GenusOne.IntCoord
