import VOA.Moonshine.LatticeTwistedGeneralParity

/-! # Weight spaces of the parity modules -/
noncomputable section
namespace VOA.Moonshine.LatticeTwistedGeneral
open LatticeTwisted IntegralLattice TwistedHeisenberg TwistedSector TwistedPlus
open scoped TensorProduct
variable (L : IntegralLattice.{0}) (hEven : L.Even) (C : TwistedCharge L) (hPos : L.PosDef)
variable [FiniteDimensional ℂ C.carrier]

theorem parityLift_op_grade (odd : Bool) (d : ℕ) (x : MT L hEven C)
    (hx : x ∈ GT (rank L) C.carrier d) :
    (parityLift L hEven C hPos odd).op x = (-1 : ℂ) ^ (d + odd.toNat) • x := by
  have ht := twTheta_of_mem_twGrading hx
  cases odd
  · change -twTheta (rank L) C.carrier x = (-1 : ℂ) ^ (d + 0) • x
    rw [ht]
    simp [pow_succ]
  · exact ht

theorem map_parityModule_weight (odd : Bool) (α : ℂ) :
    ((parityModule L hEven C hPos odd).weight α).map
      (plusSub (parityLift L hEven C hPos odd)).subtype =
    plusSub (parityLift L hEven C hPos odd) ⊓ weightLT (rank L) C.carrier α :=
  map_plusWeight _ _

theorem map_parityModule_weight_level (odd : Bool) (d : ℕ) :
    ((parityModule L hEven C hPos odd).weight ((levelT (rank L) d : ℚ) : ℂ)).map
      (plusSub (parityLift L hEven C hPos odd)).subtype =
    if Even (d + odd.toNat) then GT (rank L) C.carrier d else ⊥ := by
  rw [map_parityModule_weight, weightLT_level]
  split_ifs with hd
  · apply inf_eq_right.mpr
    intro x hx
    rw [mem_plusSub, parityLift_op_grade L hEven C hPos odd d x hx,
      hd.neg_one_pow, one_smul]
  · apply bot_unique
    rintro x ⟨hp, hx⟩
    rw [SetLike.mem_coe, mem_plusSub, parityLift_op_grade L hEven C hPos odd d x hx,
      (Nat.not_even_iff_odd.mp hd).neg_one_pow, neg_one_smul] at hp
    exact (eq_zero_of_eq_neg hp.symm : x = 0)

theorem parityModule_weight_support (odd : Bool) (α : ℂ)
    (hα : (parityModule L hEven C hPos odd).weight α ≠ ⊥) :
    ∃ d : ℕ, α = ((levelT (rank L) d : ℚ) : ℂ) ∧ Even (d + odd.toNat) := by
  have hmap : ((parityModule L hEven C hPos odd).weight α).map
      (plusSub (parityLift L hEven C hPos odd)).subtype ≠ ⊥ := by
    intro hz
    apply hα
    exact Submodule.map_injective_of_injective (Submodule.injective_subtype _)
      (hz.trans (Submodule.map_bot _).symm)
  by_cases h : ∃ d, ((levelT (rank L) d : ℚ) : ℂ) = α
  · obtain ⟨d, rfl⟩ := h
    refine ⟨d, rfl, ?_⟩
    by_contra hd
    exact hmap (by rw [map_parityModule_weight_level, if_neg hd])
  · push Not at h
    exact False.elim (hmap (by rw [map_parityModule_weight,
      weightLT_eq_bot _ _ h, inf_bot_eq]))

theorem finrank_parityModule_weight_level (odd : Bool) (d : ℕ)
    (hd : Even (d + odd.toNat)) :
    Module.finrank ℂ ((parityModule L hEven C hPos odd).weight
      ((levelT (rank L) d : ℚ) : ℂ)) = twCount (rank L) d * Module.finrank ℂ C.carrier := by
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective
    (plusSub (parityLift L hEven C hPos odd)).subtype (Submodule.injective_subtype _) _)]
  rw [map_parityModule_weight_level, if_pos hd]
  exact finrank_twGrading d

end VOA.Moonshine.LatticeTwistedGeneral
