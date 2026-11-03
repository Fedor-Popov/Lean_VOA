import VOA.Huang.NgSchauenburgModular
import VOA.Huang.NgSchauenburgRotation

/-! # Finite order of the actual ribbon twist

Vafa's root-of-unity theorem is a named, unproved target.  The passage from
its simple-object conclusion to a uniform finite order on all objects is
proved using the supplied semisimple decompositions.
-/

noncomputable section
set_option linter.unusedSectionVars false
universe v u

namespace VOA.Huang.NgSchauenburg

open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

namespace Ribbon

variable {F : SphericalFusion C} (R : Ribbon F.toPivotal)

theorem twistScalar_unitLabel : R.twistScalar F.unitLabel = 1 := by
  letI := F.simple_isSimple F.unitLabel
  have hn := R.naturality F.unitIso.hom
  rw [R.unit, Category.comp_id, ← R.twistScalar_smul_id,
    Linear.smul_comp, Category.id_comp] at hn
  have hne : F.unitIso.hom ≠ 0 := by
    intro h
    apply id_nonzero (F.simple F.unitLabel)
    rw [← F.unitIso.hom_inv_id, h, zero_comp]
  apply smul_left_injective ℂ hne
  simpa using hn.symm

/-- Order of the tuple of simple twist eigenvalues; zero means infinite order. -/
def twistOrder : ℕ := orderOf (fun i : F.Label => R.twistScalar i)

theorem twistOrder_eq_lcm :
    R.twistOrder = Finset.univ.lcm (fun i : F.Label => orderOf (R.twistScalar i)) :=
  Pi.orderOf _

/-- The power is formed in `End X` before coercing back to a categorical morphism. -/
def twistPower (X : C) (n : ℕ) : X ⟶ X := (End.of (R.twist X).hom ^ n).asHom

theorem twist_pow_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    f ≫ R.twistPower Y n = R.twistPower X n ≫ f := by
  induction n with
  | zero => simp [twistPower]
  | succ n ih =>
    simp only [twistPower, pow_succ, End.asHom, End.of, End.mul_def, Category.assoc]
    change f ≫ (R.twist Y).hom ≫ R.twistPower Y n =
      (R.twist X).hom ≫ R.twistPower X n ≫ f
    rw [← Category.assoc, R.naturality, Category.assoc, ih]

theorem twist_pow_simple (i : F.Label) (n : ℕ) :
    R.twistPower (F.simple i) n =
      R.twistScalar i ^ n • 𝟙 (F.simple i) := by
  induction n with
  | zero => simp [twistPower]
  | succ n ih =>
    change (R.twist (F.simple i)).hom ≫ R.twistPower (F.simple i) n = _
    rw [ih, ← R.twistScalar_smul_id]
    simp [pow_succ, smul_smul, mul_comm]


/-- A power of the natural twist is the identity on every object iff it is
the identity on each chosen simple. No modularity or Vafa theorem is used. -/
theorem twist_pow_eq_id_iff (n : ℕ) :
    (∀ X : C, R.twistPower X n = 𝟙 X) ↔
      ∀ i : F.Label, R.twistScalar i ^ n = 1 := by
  constructor
  · intro h i
    letI := F.simple_isSimple i
    apply smul_left_injective ℂ (id_nonzero (F.simple i))
    simpa [R.twist_pow_simple] using h (F.simple i)
  · intro h X
    obtain ⟨k, a, ⟨e⟩⟩ := F.decomposition X
    have hb : R.twistPower (⨁ fun j => F.simple (a j)) n = 𝟙 _ := by
      apply biproduct.hom_ext'
      intro j
      rw [R.twist_pow_naturality, R.twist_pow_simple, h]
      simp
    apply (cancel_mono e.hom).mp
    rw [← R.twist_pow_naturality, hb]
    simp

/-- The numerical tuple order is exactly the order of the natural twist,
in the sense of having the same annihilating powers. -/
theorem twistOrder_dvd_iff (n : ℕ) :
    R.twistOrder ∣ n ↔ ∀ X : C, R.twistPower X n = 𝟙 X := by
  rw [R.twist_pow_eq_id_iff, twistOrder, orderOf_dvd_iff_pow_eq_one]
  exact funext_iff

theorem twistOrder_pos_iff :
    0 < R.twistOrder ↔ ∀ i : F.Label, IsOfFinOrder (R.twistScalar i) := by
  rw [twistOrder, orderOf_pos_iff]
  exact ⟨IsOfFinOrder.apply, IsOfFinOrder.pi⟩

theorem finite_twist_of_simple_roots
    (h : ∀ i : F.Label, IsOfFinOrder (R.twistScalar i)) :
    0 < R.twistOrder ∧ ∀ X : C,
      R.twistPower X R.twistOrder = 𝟙 X :=
  ⟨R.twistOrder_pos_iff.mpr h, (R.twistOrder_dvd_iff _).mp dvd_rfl⟩

end Ribbon

/-- Vafa's theorem for the specified complex modular category: every
simple ribbon-twist eigenvalue is a root of unity. This Prop is not proved.
It does not assert finite order of an arbitrary normalized representation T. -/
def VafaTheorem (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ i : F.Label, IsOfFinOrder (M.twistScalar i)

theorem finite_twist_of_vafa (F : SphericalFusion C) (M : Modular F)
    (h : VafaTheorem F M) :
    0 < M.toRibbon.twistOrder ∧ ∀ X : C,
      M.toRibbon.twistPower X M.toRibbon.twistOrder = 𝟙 X :=
  M.toRibbon.finite_twist_of_simple_roots h

end VOA.Huang.NgSchauenburg
