import VOA.Classification.COne.OrbC2fTetra
import VOA.Classification.COne.OrbC2cResidual

/-! # The remaining intrinsic certificates, with cubic fixedness discharged

The proposed finite arithmetic obligation is on the ambient plus VOA, but its
remainders are spans of Virasoro words on fixed states. The lifting theorem
below proves that these are intrinsic errors in the fixed VOA.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbC2f
open VOA VertexOperatorAlgebra OrbC2c OrbC2e OrbC2b PlusC2

section Transport
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V'] [Module ℂ V']
  {W : VertexOperatorAlgebra V} {T : VertexOperatorAlgebra V'}
  {f : V →ₗ[ℂ] V'}

theorem hom_virWord (hf : IsVOAHom W T f)
    (hω : f W.conformalVector = T.conformalVector) (ks : List ℕ) (x : V) :
    f (virWord W ks x) = virWord T ks (f x) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    rw [virWord, ConverseUniverse.voaHom_map_L hf hω, ih, virWord]

theorem map_virError (hf : IsVOAHom W T f)
    (hω : f W.conformalVector = T.conformalVector) (x : V) :
    (virError W x).map f = virError T (f x) := by
  simp only [virError, Submodule.map_span, ← Set.range_comp']
  apply congrArg (Submodule.span ℂ)
  apply congrArg Set.range
  funext p
  exact hom_virWord hf hω p.val x

/-- One uniform expression for both prescribed remainder identities. -/
def modeRemainder (W : VertexOperatorAlgebra V) (U X : V)
    (n : ℤ) (p q : ℕ) (a b : ℂ) : V :=
  W.smul U n U - (a • ((W.L (-2) ^ p) W.vacuum) + b • ((W.L (-2) ^ q) X))

theorem hom_modeRemainder (hf : IsVOAHom W T f)
    (hω : f W.conformalVector = T.conformalVector)
    (U X : V) (n : ℤ) (p q : ℕ) (a b : ℂ) :
    f (modeRemainder W U X n p q a b) = modeRemainder T (f U) (f X) n p q a b := by
  rw [modeRemainder, map_sub, map_add, map_smul, map_smul, hf.map_smul,
    ConverseUniverse.voaHom_map_L_pow hf hω, ConverseUniverse.voaHom_map_L_pow hf hω,
    hf.map_vacuum, modeRemainder]

theorem hom_remainder_mem (hf : IsVOAHom W T f)
    (hω : f W.conformalVector = T.conformalVector)
    (U X : V) (n : ℤ) (p q : ℕ) (a b : ℂ)
    (hr : modeRemainder W U X n p q a b ∈ virError W W.vacuum ⊔ virError W X) :
    modeRemainder T (f U) (f X) n p q a b ∈ virError T T.vacuum ⊔ virError T (f X) := by
  have h : f (modeRemainder W U X n p q a b) ∈
      (virError W W.vacuum ⊔ virError W X).map f := Submodule.mem_map_of_mem hr
  rwa [Submodule.map_sup, map_virError hf hω, map_virError hf hω, hf.map_vacuum,
    hom_modeRemainder hf hω] at h

end Transport

local notation "P" => V2mPlus 4 four_ge_one
local notation "F" => orbifoldVOA (Subgroup.zpowers plusCubic)

/-- Its square normalization is 1/8, matching the published u⁽⁹⁾ normalization. -/
def normalizedNine : VP 4 four_ge_one := (cα 4)⁻¹ • weightNine

theorem normalizedNine_fixed : plusCubic normalizedNine = normalizedNine := by
  rw [normalizedNine, map_smul, weightNine_fixed]

def fixedNormalizedNine : (orbifold (Subgroup.zpowers plusCubic)).carrier :=
  ⟨normalizedNine, (mem_orbifold_zpowers_iff _ _).mpr normalizedNine_fixed⟩

theorem normalizedNine_nonzero : normalizedNine ≠ 0 :=
  smul_ne_zero (inv_ne_zero (cα_ne_zero 4 four_ge_one)) weightNine_ne_zero

theorem normalizedNine_self (n : ℤ) :
    (P).smul normalizedNine n normalizedNine = (1/8 : ℂ) • (P).smul weightNine n weightNine := by
  rw [normalizedNine, PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right, smul_smul]
  have hc : cα 4 * cα 4 = (8 : ℂ) := by
    convert cα_sq 4 four_ge_one using 1
    norm_num
  rw [← mul_inv, hc]
  norm_num

/-- OPEN: only the two state-level remainder certificates. The fixedness of
U is already a theorem; X is allowed to include its required vacuum correction.
This is stronger than `TetrahedralModeDecomposition`, with a specified U. -/
def CubicSeedRemainders : Prop :=
  ∃ (X : VP 4 four_ge_one) (t : ℂ),
    plusCubic X = X ∧ X ∈ (P).grading 16 ∧
    modeRemainder P normalizedNine X (-3) 10 2
      (2^10 * ((djC20 : ℂ) - (djB20 : ℂ)/4*t)) djB20 ∈
        virError P (P).vacuum ⊔ virError P X ∧
    modeRemainder P normalizedNine X (-5) 11 3
      (2^11 * ((djC22 : ℂ) - (djB22 : ℂ)/8*t)) djB22 ∈
        virError P (P).vacuum ⊔ virError P X

/-- Ambient Virasoro errors on fixed states lift to intrinsic errors. -/
theorem fixed_remainder_mem (U X : (orbifold (Subgroup.zpowers plusCubic)).carrier)
    (n : ℤ) (p q : ℕ) (a b : ℂ)
    (hr : modeRemainder P U X n p q a b ∈ virError P (P).vacuum ⊔ virError P X) :
    modeRemainder F U X n p q a b ∈ virError F (F).vacuum ⊔ virError F X := by
  let f := (orbifold (Subgroup.zpowers plusCubic)).carrier.subtype
  have hf : IsVOAHom F P f := ⟨rfl, fun _ _ _ => rfl⟩
  have hω : f (F).conformalVector = (P).conformalVector := rfl
  have hm : (virError F (F).vacuum ⊔ virError F X).map f =
      virError P (P).vacuum ⊔ virError P X := by
    rw [Submodule.map_sup, map_virError hf hω, map_virError hf hω]
    rfl
  rw [← hm] at hr
  obtain ⟨y, hy, he⟩ := hr
  have he' : y = modeRemainder F U X n p q a b := by
    apply Subtype.ext
    exact he.trans (hom_modeRemainder hf hω U X n p q a b).symm
  rwa [he'] at hy

/-- The arithmetic obligation closes the original input without weakening its error space. -/
theorem tetrahedralModeDecomposition_of_cubicSeedRemainders (h : CubicSeedRemainders) :
    TetrahedralModeDecomposition := by
  obtain ⟨X,t,hfix,hX,h20,h22⟩ := h
  let X' : (orbifold (Subgroup.zpowers plusCubic)).carrier :=
    ⟨X, (mem_orbifold_zpowers_iff _ _).mpr hfix⟩
  have h20' := fixed_remainder_mem fixedNormalizedNine X' (-3) 10 2 _ _ h20
  have h22' := fixed_remainder_mem fixedNormalizedNine X' (-5) 11 3 _ _ h22
  obtain ⟨e, he, hω⟩ := plus_cubic_tetra_iso
  refine ⟨e fixedNormalizedNine, e X', t, ?_, ?_, ?_, ?_, ?_⟩
  · intro hz
    have hz' := e.map_eq_zero_iff.mp hz
    exact normalizedNine_nonzero (congrArg Subtype.val hz')
  · apply ConverseUniverse.voaHom_map_grading he hω
    exact Submodule.smul_mem _ _ weightNine_mem_grading
  · exact ConverseUniverse.voaHom_map_grading he hω hX
  · exact hom_remainder_mem he hω _ _ _ _ _ _ _ h20'
  · exact hom_remainder_mem he hω _ _ _ _ _ _ _ h22'

end VOA.Classification.COne.OrbC2f
