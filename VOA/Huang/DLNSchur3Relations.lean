import VOA.Huang.DLNSchur3Symbols

/-! # The explicit remaining lower-root transition

The upper-root transition and both unit-pivot decompositions have been proved.
Only the lower-root transition is assumed below. Its equivalence with the original
large-prime residual is proved; it is not supplied as an unconditional theorem.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl

/-- Multiplicativity can be checked by right transitions on a generating set. -/
theorem map_mul_of_right_transitions {G E : Type*} [Group G] [Group E]
    (f : G → E) (hf : f 1 = 1) (S : Set G) (hS : Subgroup.closure S = ⊤)
    (hstep : ∀ s ∈ S, ∀ g, f (g * s) = f g * f s) :
    ∀ g h, f (g * h) = f g * f h := by
  intro g h
  have hh : h ∈ Subgroup.closure S := by rw [hS]; trivial
  have hall : ∀ x, f (x * h) = f x * f h := by
    induction hh using Subgroup.closure_induction with
    | mem y hy => exact hstep y hy
    | one => intro x; simp [hf]
    | mul y z _ _ hy hz =>
      intro x
      rw [← mul_assoc, hz, hy, hz, mul_assoc]
    | inv y _ hy =>
      intro x
      have hinv : f y⁻¹ * f y = 1 := by simpa [hf] using (hy y⁻¹).symm
      apply mul_right_cancel (b := f y)
      calc
        f (x * y⁻¹) * f y = f ((x * y⁻¹) * y) := (hy _).symm
        _ = f x := by simp
        _ = (f x * f y⁻¹) * f y := by rw [mul_assoc, hinv, mul_one]
  exact hall g

/-- TRUE remaining word identity, restricted to canonically normalized root pairs.
This proposition is unproved here. It is nonvacuous by `exists_normalized_root_homs`. -/
def GaussLowerRelations (n : ℕ) (h2 : Nat.Coprime 2 n) : Prop :=
  ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n)),
    Function.Surjective π → π.ker ≤ Subgroup.center E →
    ∀ X Y : Multiplicative (ZMod n) →* E,
      (∀ t, π (X t) = upperRoot t.toAdd) →
      (∀ t, π (Y t) = lowerRoot t.toAdd) →
      X.range ⊔ Y.range = commutator E → RootNormalization h2 π X Y →
      ∀ g, gaussLift X Y (g * lowerRoot 1) =
        gaussLift X Y g * Y (Multiplicative.ofAdd 1)

/-- The remaining lower transition makes the explicit Gauss words multiplicative. -/
theorem gaussLift_mul_of_lower_transition {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {E : Type*} [Group E] (X Y : Multiplicative (ZMod (p ^ k)) →* E)
    (hl : ∀ g, gaussLift X Y (g * lowerRoot 1) =
      gaussLift X Y g * Y (Multiplicative.ofAdd 1)) :
    ∀ g h, gaussLift X Y (g * h) = gaussLift X Y g * gaussLift X Y h := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply map_mul_of_right_transitions _ (gaussLift_one X Y)
    {upperRoot 1, lowerRoot 1} (root_generators _)
  intro s hs g
  rcases hs with rfl | rfl
  · have hu := gaussLift_mul_upper X Y 1 (first_column_unit_primePower hp hk 1) 1
    simp only [one_mul, gaussLift_one] at hu
    rw [hu]
    exact gaussLift_mul_upper X Y g (first_column_unit_primePower hp hk g) 1
  · have hy := hl 1
    simp only [one_mul, gaussLift_one] at hy
    rw [hy]
    exact hl g

/-- The concrete lower transition suffices for the original Schur condition. -/
theorem schurTrivial_of_gaussLowerRelations {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (h2 : Nat.Coprime 2 (p ^ k)) (h3 : Nat.Coprime 3 (p ^ k))
    (hrel : GaussLowerRelations (p ^ k) h2) :
    SchurTrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ k))) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply (schurTrivial_iff_centralDerivedInjective _).mpr
  intro E _ π hs hc x hx hpx
  obtain ⟨X, Y, hX, hY, hgen, hn⟩ := exists_normalized_root_homs h2 h3 π hs hc
  let σ : Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ k)) →* E :=
    { toFun := gaussLift X Y
      map_one' := gaussLift_one X Y
      map_mul' := gaussLift_mul_of_lower_transition hp hk X Y (hrel E π hs hc X Y hX hY hgen hn) }
  have hσ : ∀ g, π (σ g) = g := fun g =>
    map_gaussLift π X Y hX hY g (first_column_unit_primePower hp hk g)
  have hrange : σ.range.map π = ⊤ := by
    apply top_unique
    intro g _
    exact ⟨σ g, ⟨g, rfl⟩, hσ g⟩
  obtain ⟨g, rfl⟩ := commutator_le_of_central_map_top π hc σ.range hrange hx
  have hg : g = 1 := (hσ g).symm.trans hpx
  simp [hg]

/-- Conversely, Schur injectivity proves the explicit lower transition. -/
theorem gaussLowerRelations_of_schurTrivial {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (h2 : Nat.Coprime 2 (p ^ k))
    (hschur : SchurTrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ k)))) :
    GaussLowerRelations (p ^ k) h2 := by
  intro E _ π hs hc X Y hX hY hgen _ g
  have hXm : ∀ t, X t ∈ commutator E := by
    intro t
    rw [← hgen]
    exact (show X.range ≤ X.range ⊔ Y.range from le_sup_left) ⟨t, rfl⟩
  have hYm : ∀ t, Y t ∈ commutator E := by
    intro t
    rw [← hgen]
    exact (show Y.range ≤ X.range ⊔ Y.range from le_sup_right) ⟨t, rfl⟩
  have hm := gaussLift_mem X Y (commutator E) hXm hYm
  have hmap := fun q => map_gaussLift π X Y hX hY q (first_column_unit_primePower hp hk q)
  apply eq_of_mul_inv_eq_one
  apply (schurTrivial_iff_centralDerivedInjective _).mp hschur E π hs hc
  · exact (commutator E).mul_mem (hm _) ((commutator E).inv_mem
      ((commutator E).mul_mem (hm _) (hYm _)))
  · simp only [map_mul, map_inv, hmap, hY, toAdd_ofAdd, mul_inv_cancel]

/-- An exact equivalence, rather than an unannounced weakening of the root-relation target. -/
theorem rootLiftExtension_iff_gaussLowerRelations {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (h2 : Nat.Coprime 2 (p ^ k)) (h3 : Nat.Coprime 3 (p ^ k)) :
    RootLiftExtension (p ^ k) ↔ GaussLowerRelations (p ^ k) h2 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  exact ⟨fun h => gaussLowerRelations_of_schurTrivial hp hk h2
    (schurTrivial_of_rootLiftExtension h2 h3 h),
    fun h => rootLiftExtension_of_schurTrivial (schurTrivial_of_gaussLowerRelations hp hk h2 h3 h)⟩

/-- TRUE residual family of explicit lower-root word identities, unproved here. -/
def LargePrimeGaussLowerRelations : Prop :=
  ∀ p k : ℕ, ∀ hp : p.Prime, ∀ hp5 : 5 ≤ p, 0 < k →
    GaussLowerRelations (p ^ k) (primePower_coprime_two_three hp hp5).1

theorem largePrimeRootRelations_iff_gaussLowerRelations :
    LargePrimeRootRelations ↔ LargePrimeGaussLowerRelations := by
  constructor
  · intro h p k hp hp5 hk
    exact (rootLiftExtension_iff_gaussLowerRelations hp hk
      (primePower_coprime_two_three hp hp5).1 (primePower_coprime_two_three hp hp5).2).mp
      (h p k hp hp5 hk)
  · intro h p k hp hp5 hk
    exact (rootLiftExtension_iff_gaussLowerRelations hp hk
      (primePower_coprime_two_three hp hp5).1 (primePower_coprime_two_three hp hp5).2).mpr
      (h p k hp hp5 hk)

/-- Conditional assembly with the new concrete word residual kept explicit. -/
theorem matrixDLNLifting_of_gaussLowerRelations
    (hlarge : LargePrimeGaussLowerRelations) (hthree : ThreePowerSchur)
    (htwo : TwoPowerInflationFromTwo) : VOA.Huang.DLNBridge.MatrixDLNLifting :=
  matrixDLNLifting_of_rootRelations
    (largePrimeRootRelations_iff_gaussLowerRelations.mpr hlarge) hthree htwo

end VOA.Huang.DLNSchur
