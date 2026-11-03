import VOA.Classification.COne.OrbC2hProbe

/-! Corrected remainder statement and its implication to the existing downstream target.
The implication below is conditional; the remainder memberships are separate certificates.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbC2h
open scoped Pointwise
open VOA VertexOperatorAlgebra OrbC2b OrbC2c OrbC2e OrbC2f PlusC2
local notation "P" => V2mPlus 4 four_ge_one

/-- The original remainder statement with just the erroneous weight-20 coefficient corrected.
No change is made to the intrinsic Virasoro error spaces or the normalization of U. -/
def CubicSeedRemaindersCorrected : Prop :=
  ∃ (X : VP 4 four_ge_one) (t : ℂ),
    plusCubic X = X ∧ X ∈ (P).grading 16 ∧
    modeRemainder P normalizedNine X (-3) 10 2
      (2^10 * ((djC20 : ℂ)/13 - (djB20 : ℂ)/4*t)) djB20 ∈
        virError P (P).vacuum ⊔ virError P X ∧
    modeRemainder P normalizedNine X (-5) 11 3
      (2^11 * ((djC22 : ℂ) - (djB22 : ℂ)/8*t)) djB22 ∈
        virError P (P).vacuum ⊔ virError P X

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

theorem virWord_smul (ks : List ℕ) (a : ℂ) (x : V) :
    virWord W ks (a • x) = a • virWord W ks x := by
  induction ks with
  | nil => rfl
  | cons k ks ih => rw [virWord, ih, map_smul, virWord]

theorem virError_smul_eq (a : ℂ) (ha : a ≠ 0) (x : V) :
    virError W (a • x) = virError W x := by
  unfold virError
  have he : Set.range (fun p : {ks : List ℕ // ∃ k ∈ ks, k ≠ 1} =>
      virWord W p.val (a • x)) =
      a • Set.range (fun p : {ks : List ℕ // ∃ k ∈ ks, k ≠ 1} => virWord W p.val x) := by
    simp only [virWord_smul, Set.smul_set_range]
  rw [he]
  exact Submodule.span_smul_eq_of_isUnit _ _ (isUnit_iff_ne_zero.mpr ha)

theorem modeRemainder_scale (s r : ℂ) (hs : s*s = r)
    (U X : V) (n : ℤ) (p q : ℕ) (a b : ℂ) :
    modeRemainder W (s • U) (r • X) n p q (r*a) b =
      r • modeRemainder W U X n p q a b := by
  simp only [modeRemainder, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, map_smul, smul_smul, hs]
  module
end General

/-- Rescaling is allowed by the existing existential downstream statement. -/
def normalizationSquare : ℚ := -18609010537 / 39858075
def parameterShift : ℚ := -1146379052032 / 304151988065625

theorem normalization_numbers (t : ℂ) :
    (normalizationSquare:ℂ) * (2^10 * ((djC20:ℂ)/13 - djB20/4*t)) =
      2^10 * ((djC20:ℂ) - djB20/4*((normalizationSquare:ℂ)*t+parameterShift)) ∧
    (normalizationSquare:ℂ) * (2^11 * ((djC22:ℂ) - djB22/8*t)) =
      2^11 * ((djC22:ℂ) - djB22/8*((normalizationSquare:ℂ)*t+parameterShift)) := by
  norm_num [normalizationSquare, parameterShift, djC20, djC22, djB20, djB22]
  constructor <;> ring

/-- The unchanged downstream target can absorb the coefficient correction by rescaling
its existential U and X. This does not repair the original fixed-normalization residual. -/
theorem tetrahedralModeDecomposition_of_corrected (h : CubicSeedRemaindersCorrected) :
    TetrahedralModeDecomposition := by
  obtain ⟨X,t,hfix,hX,h20,h22⟩ := h
  let r : ℂ := normalizationSquare
  have hr : r ≠ 0 := by norm_num [r, normalizationSquare]
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq r (show 0 < 2 by norm_num)
  have hs' : s*s = r := by simpa only [pow_two] using hs
  have hs0 : s ≠ 0 := by intro h0; rw [h0, zero_mul] at hs'; exact hr hs'.symm
  let U' : (orbifold (Subgroup.zpowers plusCubic)).carrier :=
    ⟨s • normalizedNine, (mem_orbifold_zpowers_iff _ _).mpr (by
      rw [map_smul, normalizedNine_fixed])⟩
  let X' : (orbifold (Subgroup.zpowers plusCubic)).carrier :=
    ⟨r • X, (mem_orbifold_zpowers_iff _ _).mpr (by rw [map_smul, hfix])⟩
  have liftRemainder (n : ℤ) (p q : ℕ) (a b : ℂ)
      (hh : modeRemainder P normalizedNine X n p q a b ∈
        virError P (P).vacuum ⊔ virError P X) :
      modeRemainder (orbifoldVOA (Subgroup.zpowers plusCubic)) U' X' n p q (r*a) b ∈
        virError (orbifoldVOA (Subgroup.zpowers plusCubic))
          (orbifoldVOA (Subgroup.zpowers plusCubic)).vacuum ⊔
        virError (orbifoldVOA (Subgroup.zpowers plusCubic)) X' := by
    apply fixed_remainder_mem
    change modeRemainder P (s • normalizedNine) (r • X) n p q (r*a) b ∈ _
    rw [modeRemainder_scale P s r hs', virError_smul_eq P r hr]
    exact Submodule.smul_mem _ r hh
  have h20' := liftRemainder (-3) 10 2 _ _ h20
  have h22' := liftRemainder (-5) 11 3 _ _ h22
  rw [(normalization_numbers t).1] at h20'
  rw [(normalization_numbers t).2] at h22'
  obtain ⟨e,he,hω⟩ := plus_cubic_tetra_iso
  refine ⟨e U', e X', r*t+parameterShift, ?_, ?_, ?_, ?_, ?_⟩
  · intro hz
    have hz' := congrArg Subtype.val (e.map_eq_zero_iff.mp hz)
    exact (smul_ne_zero hs0 normalizedNine_nonzero) hz'
  · apply ConverseUniverse.voaHom_map_grading he hω
    exact Submodule.smul_mem _ s (Submodule.smul_mem _ _ weightNine_mem_grading)
  · exact ConverseUniverse.voaHom_map_grading he hω (Submodule.smul_mem _ r hX)
  · exact hom_remainder_mem he hω _ _ _ _ _ _ _ h20'
  · exact hom_remainder_mem he hω _ _ _ _ _ _ _ h22'

end VOA.Classification.COne.OrbC2h
