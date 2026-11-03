import VOA.Huang.GenusTwoPointSepFormalConjugation

/-!
# Positive Virasoro conjugation of actual intertwiner modes

The infinitesimal coordinate action follows from the actual Jacobi identity.
Its formal exponential is pointwise finite and equals conjugation by the
constructed coordinate operators. Identification with coordinate substitution
is a further statement, not presumed by the expansion proved here.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The Virasoro commutator, including the translation and energy terms.
The finite upper bound comes from the binomial coefficient, not from a
weight-dependent choice of truncation. -/
theorem intertwiner_virasoro_commutator {P₁ P₂ P₃ : LWModule W}
    (Y : IntertwiningOperator P₁.isMod P₂.isMod P₃.isMod)
    (r : ℕ) (n : ℂ) (w : P₁.carrier) (x : P₂.carrier) :
    SquareModule.roundL P₃.isMod r (Y.val n w x) -
      Y.val n w (SquareModule.roundL P₂.isMod r x) =
      ∑ i ∈ Finset.range (r + 2), cbz ((r : ℤ) + 1) (i : ℤ) •
        Y.val ((r : ℂ) + 1 + n - i)
          (SquareModule.roundL P₁.isMod ((i : ℤ) - 1) w) x := by
  have h := Y.property.commutator W.conformalVector w x ((r : ℤ) + 1) n
  have hs : Function.support (fun i : ℤ => cbz ((r : ℤ) + 1) i •
      Y.val (((r : ℤ) + 1 : ℤ) + n - i)
        (mode (P₁.isMod.YM W.conformalVector) i w) x) ⊆
      (Finset.Ico 0 ((r : ℤ) + 2) : Finset ℤ) := by
    intro i hi
    simp only [Finset.mem_coe, Finset.mem_Ico]
    by_contra hn
    apply hi
    dsimp only
    by_cases hneg : i < 0
    · rw [cbz_apply_neg _ hneg, zero_smul]
    · rw [cbz_eq_zero_of_lt (by omega) (by omega), zero_smul]
  rw [finsum_eq_sum_of_support_subset _ hs] at h
  change _ = _ at h
  rw [show SquareModule.roundL P₃.isMod r =
      mode (P₃.isMod.YM W.conformalVector) ((r : ℤ) + 1) from rfl,
    show SquareModule.roundL P₂.isMod r =
      mode (P₂.isMod.YM W.conformalVector) ((r : ℤ) + 1) from rfl, h]
  symm
  apply Finset.sum_bij (fun (i : ℕ) _ => (i : ℤ))
  · intro i hi
    simp only [Finset.mem_Ico, Finset.mem_range] at *
    omega
  · intro i _ j _ h
    exact_mod_cast h
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    exact ⟨i.toNat, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i _
    simp only [SquareModule.roundL, sub_add_cancel, Int.cast_add, Int.cast_natCast,
      Int.cast_one]

/-- The complete infinitesimal action of a locally finite positive Virasoro
generator on an intertwiner mode, with both output and input actions. -/
theorem moduleCoordGen_intertwiner_commutator {P₁ P₂ P₃ : LWModule W}
    (Y : IntertwiningOperator P₁.isMod P₂.isMod P₃.isMod)
    (c : ℕ → ℂ) (n : ℂ) (w : P₁.carrier) (x : P₂.carrier) :
    moduleCoordGen P₃ c (Y.val n w x) - Y.val n w (moduleCoordGen P₂ c x) =
      ∑ᶠ j : ℕ, c j •
        (∑ i ∈ Finset.range (j + 3), cbz ((j : ℤ) + 2) (i : ℤ) •
          Y.val ((j : ℂ) + 2 + n - i)
            (SquareModule.roundL P₁.isMod ((i : ℤ) - 1) w) x) := by
  have hl := moduleCoordGen_support_finite P₃ c (Y.val n w x)
  have hr := moduleCoordGen_support_finite P₂ c x
  have hr' : (Function.support (fun j : ℕ => c j •
      Y.val n w (mode (P₂.isMod.YM W.conformalVector) ((j : ℤ) + 2) x))).Finite := by
    refine hr.subset fun j hj => ?_
    intro hz
    exact hj (by simpa only [map_smul, map_zero] using congrArg (Y.val n w) hz)
  change (∑ᶠ j, c j • mode (P₃.isMod.YM W.conformalVector) ((j : ℤ) + 2)
      (Y.val n w x)) - Y.val n w (∑ᶠ j, c j •
        mode (P₂.isMod.YM W.conformalVector) ((j : ℤ) + 2) x) = _
  rw [map_finsum (Y.val n w) hr]
  simp only [map_smul]
  rw [← finsum_sub_distrib hl hr']
  apply finsum_congr
  intro j
  rw [← smul_sub]
  congr 1
  simpa only [SquareModule.roundL, Nat.cast_add, Nat.cast_one, add_assoc,
    show (1 + 1 : ℤ) = 2 from rfl, show (1 + 1 : ℂ) = 2 from by norm_num,
    show (1 + 2 : ℕ) = 3 from rfl] using
      intertwiner_virasoro_commutator Y (j + 1) n w x

/-- Exponentiation of the mode commutator, with the actual inverse operator.
This is a formal Hadamard expansion for arbitrary intertwining operators. -/
theorem moduleCoordinateChange_intertwiner_expansion {P₁ P₂ P₃ : LWModule W}
    (Y : IntertwiningOperator P₁.isMod P₂.isMod P₃.isMod)
    (c : ℕ → ℂ) (n : ℂ) (w : P₁.carrier) (x : P₂.carrier) :
    moduleCoordinateChange P₃ c
        (Y.val n w ((moduleCoordinateChange P₂ c).symm x)) =
      ∑ᶠ r, conjugationCoeff (-moduleCoordGen P₃ c) (-moduleCoordGen P₂ c) (Y.val n w) r x :=
  expFun_conjugation_eq_finsum (moduleCoordGen_isLocNilp P₃ c).neg
    (moduleCoordGen_isLocNilp P₂ c).neg (Y.val n w) x

/-- The same expansion at the uniquely determined normalized logarithmic coefficients. -/
theorem normalizedCoordinateChange_intertwiner_expansion {P₁ P₂ P₃ : LWModule W}
    (Y : IntertwiningOperator P₁.isMod P₂.isMod P₃.isMod)
    (n : ℂ) (w : P₁.carrier) (x : P₂.carrier) :
    normalizedCoordinateChange P₃
        (Y.val n w ((normalizedCoordinateChange P₂).symm x)) =
      ∑ᶠ r, conjugationCoeff
        (-moduleCoordGen P₃ (iterativeLog (logarithmicCoordinate 1)))
        (-moduleCoordGen P₂ (iterativeLog (logarithmicCoordinate 1))) (Y.val n w) r x :=
  moduleCoordinateChange_intertwiner_expansion Y _ n w x

end VOA.Huang.GenusTwoPoint.Separate
