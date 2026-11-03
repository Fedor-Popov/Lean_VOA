import VOA.Classification.COne.PlusSplitWeightFourObstruction

/-! Injectivity of the actual W zero mode at conformal weight one, obtained
from the certified Zhu quadratic relation, without identifying a module model. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusSplitting
open PlusUnitary PlusZhuNormalForms
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- Evaluation of the Zhu quotient on one actual weak-module top vector. -/
def topEvaluation (A : WeakModule W M) (x : M) (hx : x ∈ Omega A) :
    VOA.A W →ₗ[ℂ] M :=
  (O W).liftQ ((oLevW A 0).flip x) (by
    intro v hv
    exact O_annihilates_Omega A hv hx)

@[simp] theorem topEvaluation_mk (A : WeakModule W M) (x : M) (hx : x ∈ Omega A)
    (a : V) : topEvaluation A x hx (VOA.mk W a) = oLevW A 0 a x := rfl

theorem topEvaluation_mk_mul (A : WeakModule W M) (x : M) (hx : x ∈ Omega A)
    (a : V) (b : VOA.A W) :
    letI := instRingA W
    topEvaluation A x hx (VOA.mk W a * b) = oLevW A 0 a (topEvaluation A x hx b) := by
  letI := instRingA W
  obtain ⟨v, rfl⟩ := VOA.mk_surjective W b
  change oLevW A 0 (zhuMul W a v) x = oLevW A 0 a (oLevW A 0 v x)
  exact oOmega_zhuMul_mult A a v hx

end VOA.Classification.COne.PlusSplitting

namespace VOA.Classification.COne.PlusSplitting
open PlusUnitary PlusZhuNormalForms VOA.Huang.LogRemovalAdmissible
variable (m : ℕ) (hm : 1 ≤ m)
variable {M : Type} [AddCommGroup M] [Module ℂ M]

/-- At weight one the quadratic relation is W² - 14W + 24 = 0.
In particular W has no zero eigenvector there, even without simplicity. -/
theorem weightOne_eq_zero_of_W_zero (A : WeakModule (V2mPlus m hm) M)
    (x : M) (hx : x ∈ Omega A) (hω : L0 A x = x)
    (hW : mode (A.YM (WP m hm)) 3 x = 0) : x = 0 := by
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  let f := topEvaluation A x hx
  have hf (i : Fin 3) (b : VOA.A (V2mPlus m hm)) :
      f (generator m hm i * b) =
        oLevW A 0 (gP m hm i) (f b) :=
    topEvaluation_mk_mul A x hx _ b
  have hfo : f (generator m hm 0) = x := by
    change oLevW A 0 (V2mPlus m hm).conformalVector x = x
    rw [oLevW_homogeneous A 0 (V2mPlus m hm).conformal_mem]
    exact hω
  have hfw : f (generator m hm 1) = 0 := by
    change oLevW A 0 (WP m hm) x = 0
    rw [oLevW_homogeneous A 0 (WP_mem_grading m hm)]
    exact hW
  have ho : oLevW A 0 (gP m hm 0) x = x := hfo
  have he := congrArg f (W_squared m hm)
  simp only [map_add, map_sub, map_smul, pow_succ, pow_zero, one_mul,
    mul_assoc, hf, hfo, hfw, map_zero, ho, smul_zero, add_zero, sub_zero] at he
  have he' : (-24 : ℂ) • x = 0 := by
    calc
      _ = (-264 / 7 : ℂ) • x - (6 / 7 : ℂ) • x + (102 / 7 : ℂ) • x := by module
      _ = 0 := he.symm
  exact (smul_eq_zero.mp he').resolve_left (by norm_num)

/-- Exact weight-four obstruction for a vacuum quotient with kernel bottom
one. No sign-module identification or ordinary middle module is assumed. -/
theorem complement_iff_weightFour_obstruction (A : WeakModule (V2mPlus m hm) M)
    (π : A.Hom (adjointWeakModule (V2mPlus m hm)))
    (hb : FactorBottom A ⊥ (modeComap π ⊥) 1)
    {x : M} (hx : x ∈ (L0 A).maxGenEigenspace 0)
    (he : π.toLinearMap x = (V2mPlus m hm).vacuum) :
    (∃ Q : Submodule (modeAlg A) M, IsCompl (modeComap π ⊥) Q) ↔
      mode (A.YM (WP m hm)) 2 x = 0 := by
  rw [complement_iff_translation_zero_of_positive_bottom A π 1 hb (by norm_num) hx he]
  constructor
  · intro ht
    exact nonnegative_modes_zero_of_translation_zero A ht _ 2 (by norm_num)
  · intro h₂
    have hz := zeroMode_vacuum_lift_eq_zero A π 1 hb (by norm_num) hx he
      (WP_mem_grading m hm) (by norm_num)
    have ht := translation_vacuum_lift_eigen_one A π 1 hb (by norm_num) hx he
    refine weightOne_eq_zero_of_W_zero m hm A (translation A x) ?_ ht ?_
    · apply kernel_bottom_mem_Omega A (modeComap π ⊥) 1 hb
      · change π.toLinearMap (A.act (V2mPlus m hm).conformalVector 0 x) = 0
        rw [π.map_act, he]
        exact ((V2mPlus m hm).creation _).2 0 le_rfl
      · apply Module.End.eigenspace_le_maxGenEigenspace
        apply Module.End.mem_eigenspace_iff.mpr
        simpa only [one_smul] using ht
    · rw [weightFour_translation_defect A (WP m hm) x hz, h₂, smul_zero]

end VOA.Classification.COne.PlusSplitting
