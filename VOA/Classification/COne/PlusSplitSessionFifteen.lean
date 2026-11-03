import VOA.Classification.COne.PlusSplitWeightOneZhu

/-! Exact open weight-four target and numerical charged separation.
No additional ordered pair is asserted to split unconditionally. -/
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.PlusResonantPairs
open PlusSplitting PlusCharacterTable PlusUnitary VOA.Huang.LogRemovalAdmissible

/-- OPEN, true narrower target: the degree-one W mode kills the generalized
vacuum lift in every simple extension with kernel bottom one. Actual quotient
maps always exist for these fixtures by `adjoint_quotient_of_zero_bottom`. -/
def VacuumWeightFourAnnihilation (m : ℕ) (hm : 1 ≤ m) : Prop :=
  ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus m hm) M) (P : Submodule (modeAlg A) M),
    IsAtom P → P ⋖ ⊤ → FactorBottom A ⊥ P 1 → FactorBottom A P ⊤ 0 →
    ∀ (π : A.Hom (adjointWeakModule (V2mPlus m hm))), modeComap π ⊥ = P →
    ∀ x : M, x ∈ (L0 A).maxGenEigenspace 0 →
      π.toLinearMap x = (V2mPlus m hm).vacuum → mode (A.YM (WP m hm)) 2 x = 0

/-- The new mode calculation is exactly the original sign/vacuum numerical
obligation, not a silently strengthened identification with the sign model. -/
theorem vacuumWeightFourAnnihilation_iff_sign (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    VacuumWeightFourAnnihilation m hm ↔ PairSplitting m hm (.inr 1) (.inr 0) := by
  constructor
  · intro h M _ _ A P hP hmax hb ht
    have hb' : FactorBottom A ⊥ P 1 := by simpa [weight] using hb
    have ht' : FactorBottom A P ⊤ 0 := by simpa [weight] using ht
    obtain ⟨π, hπ, hk⟩ := adjoint_quotient_of_zero_bottom (V2mPlus_c2Cofinite m hm)
      (V2mPlus_pseudoUnitary_ge2 m hm hm2) A P hmax ht'
    obtain ⟨x, hx, he⟩ := exists_generalized_vacuum_lift (V2mPlus_c2Cofinite m hm) A π hπ
    have h₂ := h A P hP hmax hb' ht' π hk x hx he
    have hc := (complement_iff_weightFour_obstruction m hm A π
      (by simpa only [hk] using hb') hx he).mpr h₂
    simpa only [hk] using hc
  · intro h M _ _ A P hP hmax hb ht π hk x hx he
    apply (complement_iff_weightFour_obstruction m hm A π
      (by simpa only [hk] using hb) hx he).mp
    rw [hk]
    exact h A P hP hmax (by simpa [weight] using hb) (by simpa [weight] using ht)

/-- One explicit degree-one mode identity suffices for all positive-integral
vacuum-quotient rows, including numerical collisions at weight one. -/
theorem vacuum_quotient_family_iff_weightFour (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    (∀ i : Label m, (.inr 0, i) ∈ positivePairs m →
      PairSplitting m hm i (.inr 0)) ↔ VacuumWeightFourAnnihilation m hm := by
  rw [vacuum_quotient_family_iff_sign m hm hm2, vacuumWeightFourAnnihilation_iff_sign m hm hm2]

/-- On charged tops, the W difference is twice the conformal-weight
difference. This numerical fact does not compute any relation commutator. -/
theorem charged_W_difference (m : ℕ) (a : ℝ) (r s : Fin (m - 1)) :
    (values m a (.inl s)).2.1 - (values m a (.inl r)).2.1 =
      2 * ((weight m (.inl s) : ℝ) - (weight m (.inl r) : ℝ)) := by
  simp only [values, weight, Rat.cast_div, Rat.cast_pow, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat]
  ring

theorem charged_W_separated_of_positivePair (m : ℕ) (a : ℝ) (r s : Fin (m - 1))
    (hrs : (.inl r, .inl s) ∈ positivePairs m) :
    (values m a (.inl r)).2.1 ≠ (values m a (.inl s)).2.1 := by
  have hp : 0 < weight m (.inl s) - weight m (.inl r) :=
    ((Finset.mem_filter.mp hrs).2).1
  have hp' : (0 : ℝ) < (weight m (.inl s) : ℝ) - (weight m (.inl r) : ℝ) := by
    exact_mod_cast hp
  have hd := charged_W_difference m a r s
  intro he
  rw [he, sub_self] at hd
  linarith

end VOA.Classification.COne.PlusResonantPairs
