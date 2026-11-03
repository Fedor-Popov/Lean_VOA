import VOA.Classification.COne.PlusSplitZeroModeSeparation
import VOA.Classification.COne.PlusSplitSignCharacter

/-! The actual weight-four/translation identity, retaining its degree-one
term. No vanishing of that term is inferred from distinct top characters. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusSplitting
open PlusUnitary ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

theorem kernel_generalized_below_bottom_eq_zero (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (h : ℂ) (hb : FactorBottom A ⊥ P h)
    {a : ℂ} {x : M} (hxP : x ∈ P) (hx : x ∈ (L0 A).maxGenEigenspace a)
    (ha : a.re < h.re) : x = 0 := by
  by_contra hn
  have hw : FactorWeight A ⊥ P a := fun ht => hn (ht ⟨hxP, hx⟩)
  exact (not_le_of_gt ha) (hb.2 a hw)

/-- The intrinsic kernel bottom consists of weak-module top vectors. -/
theorem kernel_bottom_mem_Omega (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (h : ℂ) (hb : FactorBottom A ⊥ P h)
    {x : M} (hxP : x ∈ P) (hx : x ∈ (L0 A).maxGenEigenspace h) : x ∈ Omega A := by
  intro w a ha n hn
  apply kernel_generalized_below_bottom_eq_zero A P h hb
    ((ofR A P).act_mem a n hxP) (mode_mem_maxGenEigenspace A ha n hx)
  simp only [Complex.add_re, Complex.intCast_re]
  have hd : (w - n - 1 : ℤ) < 0 := by omega
  have hd' : ((w - n - 1 : ℤ) : ℝ) < 0 := by exact_mod_cast hd
  linarith

/-- A positive kernel bottom kills every positive-weight zero mode on the
generalized vacuum lift. This also proves that lift is an L(0) eigenvector. -/
theorem zeroMode_vacuum_lift_eq_zero (A : WeakModule W M)
    (π : A.Hom (adjointWeakModule W)) (h : ℂ)
    (hb : FactorBottom A ⊥ (modeComap π ⊥) h) (hh : 0 < h.re)
    {x : M} (hx : x ∈ (L0 A).maxGenEigenspace 0)
    (he : π.toLinearMap x = W.vacuum)
    {a : V} {w : ℤ} (ha : a ∈ W.grading w) (hw : 1 ≤ w) :
    mode (A.YM a) (w - 1) x = 0 := by
  apply generalized_vacuum_lift_unique A π h hb hh (x := mode (A.YM a) (w - 1) x)
    (y := 0)
  · simpa using mode_mem_maxGenEigenspace A ha (w - 1) hx
  · exact Submodule.zero_mem _
  · change π.toLinearMap (A.act a (w - 1) x) = π.toLinearMap 0
    rw [π.map_act, he, map_zero]
    exact (W.creation a).2 _ (by omega)

/-- The translation of the generalized vacuum lift is an actual eigenvector
of weight one when the kernel has positive bottom. -/
theorem translation_vacuum_lift_eigen_one (A : WeakModule W M)
    (π : A.Hom (adjointWeakModule W)) (h : ℂ)
    (hb : FactorBottom A ⊥ (modeComap π ⊥) h) (hh : 0 < h.re)
    {x : M} (hx : x ∈ (L0 A).maxGenEigenspace 0)
    (he : π.toLinearMap x = W.vacuum) : L0 A (translation A x) = translation A x := by
  have hz : L0 A x = 0 := zeroMode_vacuum_lift_eq_zero A π h hb hh hx he
    W.conformal_mem (by norm_num)
  have hc := L0_commutator_weak A W.conformal_mem x 0
  rw [hz, map_zero, add_zero] at hc
  norm_num at hc
  exact hc

/-- Correct sign and mode indexing for the translation commutator. -/
theorem mode_translation_defect (A : WeakModule W M) (a : V) (n : ℤ) (x : M) :
    mode (A.YM a) n (translation A x) =
      translation A (mode (A.YM a) n x) + (n : ℂ) • mode (A.YM a) (n - 1) x := by
  have hc := L_neg_one_comm A a n x
  change translation A _ - mode (A.YM a) n (translation A x) = _ at hc
  rw [neg_smul] at hc
  apply sub_eq_zero.mp
  calc
    _ = -(translation A (mode (A.YM a) n x) -
      mode (A.YM a) n (translation A x)) -
        (n : ℂ) • mode (A.YM a) (n - 1) x := by abel
    _ = 0 := by rw [hc]; abel

/-- At weight four the unaccounted-for term is exactly three times a₂x. -/
theorem weightFour_translation_defect (A : WeakModule W M) (a : V) (x : M)
    (hx : mode (A.YM a) 3 x = 0) :
    mode (A.YM a) 3 (translation A x) = (3 : ℂ) • mode (A.YM a) 2 x := by
  have hc := mode_translation_defect A a 3 x
  rw [hx, map_zero, zero_add] at hc
  exact hc

/-- With sign eigenvalue 12, the commutator gives a₂x = 4 Tx, not Tx = 0. -/
theorem weightFour_degreeOne_eq_four_translation (A : WeakModule W M) (a : V) (x : M)
    (hx : mode (A.YM a) 3 x = 0)
    (ht : mode (A.YM a) 3 (translation A x) = (12 : ℂ) • translation A x) :
    mode (A.YM a) 2 x = (4 : ℂ) • translation A x := by
  have hc := weightFour_translation_defect A a x hx
  rw [ht] at hc
  have he := congrArg (fun y : M => (1 / 3 : ℂ) • y) hc
  norm_num [smul_smul] at he
  exact he.symm

/-- A nonzero eigenvalue does kill translation once the degree-one term is
proved zero. The extra hypothesis is indispensable to this argument. -/
theorem translation_zero_of_weightFour_separation (A : WeakModule W M)
    (a : V) (x : M) (b : ℂ) (hb : b ≠ 0)
    (hx : mode (A.YM a) 3 x = 0)
    (ht : mode (A.YM a) 3 (translation A x) = b • translation A x)
    (h₂ : mode (A.YM a) 2 x = 0) : translation A x = 0 := by
  have hc := weightFour_translation_defect A a x hx
  rw [ht, h₂, smul_zero] at hc
  exact (smul_eq_zero.mp hc).resolve_left hb

end VOA.Classification.COne.PlusSplitting

namespace VOA.Classification.COne.PlusSplitting
open PlusUnitary PlusCharacterTable
variable {M : Type} [AddCommGroup M] [Module ℂ M]

/-- Transport the proved sign character through an actual weak-module map.
If Tv = c h, the genuine commutator forces W₂v = 4 c h. No conclusion c = 0
is available until the degree-one mode is independently shown to vanish. -/
theorem sign_translation_W_degreeOne (m : ℕ) (hm : 1 ≤ m)
    (A : WeakModule (V2mPlus m hm) M)
    (ι : (signModule m hm).toWeakModule.Hom A) (x : M) (c : ℂ)
    (hx : mode (A.YM (WP m hm)) 3 x = 0)
    (ht : translation A x = c • ι.toLinearMap (signVector m hm)) :
    mode (A.YM (WP m hm)) 2 x = (4 * c) • ι.toLinearMap (signVector m hm) := by
  have hs : (signModule m hm).toWeakModule.act (WP m hm) 3 (signVector m hm) =
      (12 : ℂ) • signVector m hm := by
    have he := signVector_W m hm
    rw [oMod_homogeneous _ (WP_mem_grading m hm)] at he
    exact he
  have hW : mode (A.YM (WP m hm)) 3 (translation A x) =
      (12 : ℂ) • translation A x := by
    rw [ht, map_smul]
    change c • A.act (WP m hm) 3 (ι.toLinearMap (signVector m hm)) = _
    rw [← ι.map_act, hs, map_smul, smul_comm]
  rw [weightFour_degreeOne_eq_four_translation A (WP m hm) x hx hW, ht, smul_smul]

end VOA.Classification.COne.PlusSplitting
