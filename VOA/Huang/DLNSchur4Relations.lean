import VOA.Huang.DLNSchur4Transition

/-! # Two explicitly remaining lower-transition obligations

The top-to-top transitions reduce to a single self-defect at a generator of the
unit group. The other transitions are retained as a separate, strictly restricted
word problem. Neither remaining proposition is asserted as a theorem.
-/

namespace VOA.Huang.DLNSchur

/-- Remaining torus obligation: the self-defect of a unit-group generator vanishes.
This is implied by `GaussLowerRelations`, as proved below. -/
def TorusGeneratorRelations (n : ℕ) (h2 : Nat.Coprime 2 n) : Prop :=
  ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n)),
    Function.Surjective π → π.ker ≤ Subgroup.center E →
    ∀ X Y : Multiplicative (ZMod n) →* E,
      (∀ t, π (X t) = upperRoot t.toAdd) →
      (∀ t, π (Y t) = lowerRoot t.toAdd) →
      X.range ⊔ Y.range = commutator E → RootNormalization h2 π X Y →
      ∀ w : (ZMod n)ˣ, (∀ u : (ZMod n)ˣ, u ∈ Submonoid.powers w) →
        torusDefect X Y w w = 1

/-- Remaining chart obligation: the lower transition when at least one top-left
pivot is not a unit. No field-style Bruhat decomposition is assumed. -/
def GaussBoundaryRelations (n : ℕ) (h2 : Nat.Coprime 2 n) : Prop :=
  ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n)),
    Function.Surjective π → π.ker ≤ Subgroup.center E →
    ∀ X Y : Multiplicative (ZMod n) →* E,
      (∀ t, π (X t) = upperRoot t.toAdd) →
      (∀ t, π (Y t) = lowerRoot t.toAdd) →
      X.range ⊔ Y.range = commutator E → RootNormalization h2 π X Y →
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod n),
        (¬ IsUnit (g 0 0) ∨
          ¬ IsUnit ((g * lowerRoot 1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod n)) 0 0)) →
        gaussLift X Y (g * lowerRoot 1) = gaussLift X Y g * Y (Multiplicative.ofAdd 1)

/-- The new torus residual is a proved consequence of the original target. -/
theorem torusGeneratorRelations_of_gaussLowerRelations {n : ℕ}
    (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n)
    (h : GaussLowerRelations n h2) : TorusGeneratorRelations n h2 := by
  intro E _ π hs hc X Y hX hY hgen hn w _
  exact (gaussLift_mul_lower_one_top_iff h2 h3 π hs X Y hX hY hn
    0 ((w : ZMod n) - 1) w w (by ring)).mp
    (h E π hs hc X Y hX hY hgen hn _)

/-- Exact decomposition of the original residual, with no weakening. -/
theorem gaussLowerRelations_iff_generator_and_boundary {p k : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    GaussLowerRelations (p ^ k) (primePower_coprime_two_three hp hp5).1 ↔
      TorusGeneratorRelations (p ^ k) (primePower_coprime_two_three hp hp5).1 ∧
      GaussBoundaryRelations (p ^ k) (primePower_coprime_two_three hp hp5).1 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI := ZMod.isCyclic_units_of_prime_pow p hp (by omega) k
  constructor
  · intro h
    refine ⟨torusGeneratorRelations_of_gaussLowerRelations
      (primePower_coprime_two_three hp hp5).1 (primePower_coprime_two_three hp hp5).2 h, ?_⟩
    intro E _ π hs hc X Y hX hY hgen hn g _
    exact h E π hs hc X Y hX hY hgen hn g
  · rintro ⟨ht, hb⟩ E _ π hs hc X Y hX hY hgen hn g
    by_cases ha : IsUnit (g 0 0)
    · by_cases ha' :
          IsUnit ((g * lowerRoot 1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ k))) 0 0)
      · obtain ⟨w, hw⟩ := IsCyclic.exists_monoid_generator (α := (ZMod (p ^ k))ˣ)
        have hw0 := ht E π hs hc X Y hX hY hgen hn w hw
        apply gaussLift_mul_lower_one_of_unit_pivots
          (primePower_coprime_two_three hp hp5).1 (primePower_coprime_two_three hp hp5).2
          π hs X Y hX hY hn _ g ha ha'
        intro u v
        rcases torusDefect_eq_one_or_generator
          (primePower_coprime_two_three hp hp5).1 (primePower_coprime_two_three hp hp5).2
          π hs X Y hX hY hn hc w hw u v with h | h
        · exact h
        · exact h.trans hw0
      · exact hb E π hs hc X Y hX hY hgen hn g (Or.inr ha')
    · exact hb E π hs hc X Y hX hY hgen hn g (Or.inl ha)

/-- TRUE, unproved family of the generator self-defect obligations. -/
def LargePrimeTorusGeneratorRelations : Prop :=
  ∀ p k : ℕ, ∀ hp : p.Prime, ∀ hp5 : 5 ≤ p, 0 < k →
    TorusGeneratorRelations (p ^ k) (primePower_coprime_two_three hp hp5).1

/-- TRUE, unproved family of the chart-boundary lower transitions. -/
def LargePrimeGaussBoundaryRelations : Prop :=
  ∀ p k : ℕ, ∀ hp : p.Prime, ∀ hp5 : 5 ≤ p, 0 < k →
    GaussBoundaryRelations (p ^ k) (primePower_coprime_two_three hp hp5).1

/-- The two smaller residuals together are exactly the requested large-prime target. -/
theorem largePrimeGaussLowerRelations_iff_generator_and_boundary :
    LargePrimeGaussLowerRelations ↔
      LargePrimeTorusGeneratorRelations ∧ LargePrimeGaussBoundaryRelations := by
  constructor
  · intro h
    exact ⟨fun p k hp hp5 hk =>
      ((gaussLowerRelations_iff_generator_and_boundary hp hp5).mp (h p k hp hp5 hk)).1,
      fun p k hp hp5 hk =>
      ((gaussLowerRelations_iff_generator_and_boundary hp hp5).mp (h p k hp hp5 hk)).2⟩
  · rintro ⟨ht, hb⟩ p k hp hp5 hk
    exact (gaussLowerRelations_iff_generator_and_boundary hp hp5).mpr
      ⟨ht p k hp hp5 hk, hb p k hp hp5 hk⟩

/-- Conditional connection to the previous root-relation target. -/
theorem largePrimeRootRelations_of_generator_and_boundary
    (ht : LargePrimeTorusGeneratorRelations) (hb : LargePrimeGaussBoundaryRelations) :
    LargePrimeRootRelations :=
  largePrimeRootRelations_iff_gaussLowerRelations.mpr
    (largePrimeGaussLowerRelations_iff_generator_and_boundary.mpr ⟨ht, hb⟩)

end VOA.Huang.DLNSchur
