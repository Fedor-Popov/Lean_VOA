import VOA.Huang.GenusTwoPointSepEnergyWard

/-!
# Infinitesimal coordinate action on general intertwining operators

The indices below are complex, and the source and target modules may differ.
The finite Virasoro commutator comes from Jacobi. The locally finite generator
and its Hadamard expansion use the actual coordinate exponentials.
These statements do not identify that expansion with substitution in a
complex-power formal field.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P Q N : LWModule W}

/-- Jacobi gives the same finite nonnegative Virasoro commutator for every
intertwiner, including those with nonintegral mode indices. -/
theorem intertwiner_virasoro_comm (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (k : ℕ) (n : ℂ) (w : P.carrier) (x : Q.carrier) :
    SquareModule.roundL N.isMod k (Y.val n w x) -
        Y.val n w (SquareModule.roundL Q.isMod k x) =
      ∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : ℂ) •
        Y.val ((k : ℂ) + 1 + n - j)
          (mode (P.isMod.YM W.conformalVector) j w) x := by
  have h := Y.property.commutator W.conformalVector w x ((k : ℤ) + 1) n
  have hc (j : ℕ) : cbz ((k : ℤ) + 1) (j : ℤ) = ((k + 1).choose j : ℂ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using HuangODEModes.cbz_nat (k + 1) j
  rw [HuangODEModes.finsum_eq_sum_range _ (k + 2)] at h
  · simpa only [SquareModule.roundL, Int.cast_add, Int.cast_natCast, Int.cast_one,
      hc] using h
  · intro j hj
    rcases hj with hj | hj
    · rw [cbz_apply_neg _ hj, zero_smul]
    · rw [cbz_eq_zero_of_lt (by omega) (by omega), zero_smul]

/-- The first descendant is exactly the formal derivative contribution. -/
theorem intertwiner_virasoro_derivative_term
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (k : ℕ) (n : ℂ) (w : P.carrier) :
    Y.val ((k : ℂ) + 1 + n) (P.isMod.Lm1 w) =
      (-((k : ℂ) + 1 + n)) • Y.val (n + k) w := by
  rw [Y.property.L_neg_one]
  rw [show (k : ℂ) + 1 + n - 1 = n + k by ring]

/-- The full positive Virasoro generator commutator. The outer sum is
pointwise finite by source and target truncation, without truncating Huang's
coefficient sequence. -/
theorem intertwiner_coordinateGenerator_comm
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (a : ℕ → ℂ) (n : ℂ) (w : P.carrier) (x : Q.carrier) :
    moduleCoordGen N a (Y.val n w x) - Y.val n w (moduleCoordGen Q a x) =
      ∑ᶠ k : ℕ, a k •
        ∑ j ∈ Finset.range (k + 3), ((k + 2).choose j : ℂ) •
          Y.val ((k : ℂ) + 2 + n - j)
            (mode (P.isMod.YM W.conformalVector) j w) x := by
  have hright : (Function.support fun k : ℕ =>
      Y.val n w (a k • mode (Q.isMod.YM W.conformalVector) ((k : ℤ) + 2) x)).Finite :=
    (moduleCoordGen_support_finite Q a x).subset fun k hk hz =>
      hk (by dsimp at hz ⊢; rw [hz, map_zero])
  change (∑ᶠ k : ℕ, _) - Y.val n w (∑ᶠ k : ℕ, _) = _
  rw [map_finsum _ (moduleCoordGen_support_finite Q a x),
    ← finsum_sub_distrib (moduleCoordGen_support_finite N a (Y.val n w x)) hright]
  apply finsum_congr
  intro k
  rw [map_smul, ← smul_sub]
  have h := intertwiner_virasoro_comm Y (k + 1) n w x
  simp only [SquareModule.roundL, Nat.cast_add, Nat.cast_one,
    show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega,
    show (k : ℤ) + 1 + 1 = k + 2 by ring,
    show (k : ℂ) + 1 + 1 = k + 2 by ring] at h
  exact congrArg (a k • ·) h

/-- The actual U-independent normalized sandwich has a pointwise finite
Hadamard expansion, for general rectangular intertwiner modes. -/
theorem normalizedIntertwiner_commutator_expansion
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (n : ℂ) (w : P.carrier) (x : Q.carrier) :
    normalizedCoordinateChange N
        (Y.val n w ((normalizedCoordinateChange Q).symm x)) =
      ∑ᶠ r, conjugationCoeff
        (-moduleCoordGen N (iterativeLog (logarithmicCoordinate 1)))
        (-moduleCoordGen Q (iterativeLog (logarithmicCoordinate 1)))
        (Y.val n w) r x :=
  expFun_conjugation_eq_finsum
    (moduleCoordGen_isLocNilp N _).neg (moduleCoordGen_isLocNilp Q _).neg _ _

/-- The same expansion with the exact complex-mode scaling of Huang's U(1).
This is an evaluated commutator expansion, not yet a substitution formula. -/
theorem huangIntertwiner_commutator_expansion
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (n : ℂ) (w : P.carrier) (x : Q.carrier) :
    huangU N 0 (Y.val n w ((huangU Q 0).symm x)) =
      Complex.exp (-logTwoPiI * (n + 1)) •
        ∑ᶠ r, conjugationCoeff
          (-moduleCoordGen N (iterativeLog (logarithmicCoordinate 1)))
          (-moduleCoordGen Q (iterativeLog (logarithmicCoordinate 1)))
          (Y.val n (moduleWeightExp P.isMod logTwoPiI w)) r x := by
  have hscale := intertwiner_weightExp_conjugation Y logTwoPiI n w
    ((normalizedCoordinateChange Q).symm x)
  have hinv : (huangU Q 0).symm x = moduleWeightExp Q.isMod (-logTwoPiI)
      ((normalizedCoordinateChange Q).symm x) := by
    apply (huangU Q 0).injective
    rw [LinearEquiv.apply_symm_apply, huangU_eq_normalized, moduleWeightExp_zero,
      ← moduleWeightExp_add, add_neg_cancel, moduleWeightExp_zero,
      LinearEquiv.apply_symm_apply]
  rw [hinv, huangU_eq_normalized, moduleWeightExp_zero, hscale, map_smul,
    normalizedIntertwiner_commutator_expansion]

end VOA.Huang.GenusTwoPoint.Separate
