import VOA.Huang.VerlindeEigen
import VOA.Huang.VerlindeRhoTrace
import VOA.Huang.HuangODEContra
import VOA.Huang.LWBottomRecovery

/-!
# The central modular matrix from contragredient trace parity

This file separates the square-bracket trace identity from the genus-zero
identification of the dual label. Neither is inferred from the existence-only
statement `VacuumFusionInput`. The matrix uniqueness and label transport are proved.
-/

namespace VOA.Huang.VerlindeRho

open VOA VOA.Classification.COne VOA.Huang.VerlindeFusion VOA.Huang.VerlindeEigen
  VOA.Huang.ZhuModData VOA.Huang.HuangODEContra VOA.VHat VOA.VHat.DLM3
open scoped BigOperators MatrixGroups

universe u w

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V} {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- Trace independence for the given irredundant family, with the PBW datum explicit.
Completeness and modularity are unnecessary for this step. -/
theorem traceIndependent_of_irredundant
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (D : VOA.ModularData W ι) (hC2 : C2Cofinite W) (hirr : Irredundant D.Mfam) :
    TraceIndependent D.Mfam D.h := by
  refine traceIndependent_of_bottomSeparation D.Mfam D.h D.hasWeight
    (fun i => onePointSubexp_of_c2 W (D.Mfam i).isMod (D.hasWeight i)
      (vacuumGradeZero_holds W) hC2)
    (fun i => LWBottomRecovery.isSimpleAMod_toAMod_of_irreducible
      (lwOf D i) (lwOf_irreducible D i)) ?_
  intro j k hjk _
  constructor
  intro e
  let Pj : IrrLWModule W := ⟨lwOf D j, lwOf_irreducible D j⟩
  let Pk : IrrLWModule W := ⟨lwOf D k, lwOf_irreducible D k⟩
  have hf : forwardMapIrr W (Quotient.mk (IrrLWModule.setoid W) Pj) =
      forwardMapIrr W (Quotient.mk (IrrLWModule.setoid W) Pk) := by
    rw [forwardMapIrr_mk, forwardMapIrr_mk]
    exact Quotient.sound ⟨e⟩
  have he := Quotient.exact ((zhuBijective Pr).1 hf)
  exact hjk (hirr j k he)

/-- The analytic parity law for a specified relabelling. -/
def TraceParity (D : VOA.ModularData W ι) (σ : ι → ι) : Prop :=
  ∀ (n : ℕ) (v : V), v ∈ sqWeightSpace W (n : ℂ) → ∀ (i : ι) (τ : UpperHalfPlane),
    traceFun D.Mfam D.h (σ i) v τ = (-1 : ℂ) ^ n * traceFun D.Mfam D.h i v τ

/-- The central matrix is a specified permutation whenever its trace parity is known. -/
theorem rep_neg_one_of_traceParity (D : VOA.ModularData W ι)
    (hZ : ZhuModularityAnalytic D) (hind : TraceIndependent D.Mfam D.h)
    (σ : ι → ι) (hp : TraceParity D σ) :
    ∀ x y, D.rep (-1) x y = if y = σ x then 1 else 0 := by
  have hlaw : RealisesLaw D.Mfam D.h (-1)
      (fun x y => if y = σ x then 1 else 0) := by
    intro n v hv i τ
    rw [ModularGroup.SL_neg_smul, one_smul, autFactor_neg_one]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [hp n v hv i τ, ← mul_assoc, ← mul_pow]
    simp
  have he := rho_unique D.Mfam D.h hind (hZ (-1)) hlaw
  exact fun x y => congrFun (congrFun he x) y

/-- With independence, trace parity is exactly the central-matrix assertion. -/
theorem traceParity_iff_rep_neg_one (D : VOA.ModularData W ι)
    (hZ : ZhuModularityAnalytic D) (hind : TraceIndependent D.Mfam D.h) (σ : ι → ι) :
    TraceParity D σ ↔ ∀ x y, D.rep (-1) x y = if y = σ x then 1 else 0 := by
  refine ⟨rep_neg_one_of_traceParity D hZ hind σ, ?_⟩
  intro h n v hv i τ
  have hz := hZ (-1) n v hv i τ
  rw [ModularGroup.SL_neg_smul, one_smul, autFactor_neg_one] at hz
  simp only [h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hz
  rw [hz, ← mul_assoc, ← mul_pow]
  simp

/-- The formal contragredient identity still needed at square-bracket weights.
This is the coordinate-change content of Huang (2008), (2.20), in Zhu coordinates. -/
def SquareBracketTraceParity (W : VertexOperatorAlgebra V) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M),
    ∀ (n : ℕ) (v : V), v ∈ sqWeightSpace W (n : ℂ) →
      onePoint (contragredientModule N) v = (-1 : ℂ) ^ n • onePoint N v

/-- The proposed labels really represent contragredient modules. -/
def ContragredientLabels (D : VOA.ModularData W ι) (σ : ι → ι) : Prop :=
  ∀ i, Nonempty (ModuleEquiv W (contragredientModule (D.Mfam i).isMod)
    (D.Mfam (σ i)).isMod)

/-- Completeness supplies contragredient labels, without a fusion assumption. -/
theorem exists_contragredientLabels (D : VOA.ModularData W ι) (hcomp : Complete D.Mfam) :
    ∃ σ : ι → ι, ContragredientLabels D σ := by
  have hex : ∀ i, ∃ j, Nonempty (ModuleEquiv W
      (contragredientModule (D.Mfam i).isMod) (D.Mfam j).isMod) := by
    intro i
    let P : IrrModule W :=
      { carrier := RestrictedDual (D.Mfam i).isMod
        isMod := contragredientModule (D.Mfam i).isMod
        irreducible := contragredient_isIrreducible _ (D.hasWeight i).1 (D.Mfam i).irreducible }
    exact hcomp P
  choose σ hσ using hex
  exact ⟨σ, hσ⟩

/-- A contragredient label has the same conformal weight, so the analytic bases agree. -/
theorem label_weight_eq (D : VOA.ModularData W ι) {σ : ι → ι}
    (hσ : ContragredientLabels D σ) (i : ι) : D.h (σ i) = D.h i := by
  obtain ⟨e⟩ := hσ i
  have hc : HasConformalWeight (contragredientModule (D.Mfam i).isMod) (D.h i) :=
    ⟨(contraLW (lwOf D i)).realized, (contraLW (lwOf D i)).isLow⟩
  exact hasConformalWeight_unique (D.hasWeight (σ i)) (ModuleEquiv.hasConformalWeight e hc)

/-- Formal square-bracket parity descends to the actual analytic trace functions. -/
theorem traceParity_of_contragredient (D : VOA.ModularData W ι)
    (hpar : SquareBracketTraceParity W) {σ : ι → ι} (hσ : ContragredientLabels D σ) :
    TraceParity D σ := by
  intro n v hv i τ
  obtain ⟨e⟩ := hσ i
  unfold traceFun
  change qEvalAt (onePoint (D.Mfam (σ i)).isMod v) _ _ = _
  rw [← onePoint_equiv e, label_weight_eq D hσ i, hpar _ _ n v hv, qEvalAt_smul]
  rfl

/-- The desired central-matrix result, conditional only on the two explicit bridges
and the regular-module PBW datum. -/
theorem rep_neg_one_of_contragredient
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (D : VOA.ModularData W ι) (hC2 : C2Cofinite W)
    (hZ : ZhuModularityAnalytic D) (hirr : Irredundant D.Mfam)
    (hpar : SquareBracketTraceParity W) {σ : ι → ι} (hσ : ContragredientLabels D σ) :
    ∀ x y, D.rep (-1) x y = if y = σ x then 1 else 0 :=
  rep_neg_one_of_traceParity D hZ (traceIndependent_of_irredundant Pr D hC2 hirr) σ
    (traceParity_of_contragredient D hpar hσ)

/-- A vacuum delta rule determines its labels uniquely. -/
theorem vacuum_labels_unique (D : VOA.ModularData W ι) (v0 : ι) (σ τ : ι → ι)
    (hσ : ∀ a b, famFusion D a b v0 = if b = σ a then 1 else 0)
    (hτ : ∀ a b, famFusion D a b v0 = if b = τ a then 1 else 0) : σ = τ := by
  funext a
  have he := (hσ a (σ a)).symm.trans (hτ a (σ a))
  by_contra hn
  simp [hn] at he

/-- The vacuum delta rule and skew-symmetry alone make its labels involutive. -/
theorem vacuum_labels_involutive (D : VOA.ModularData W ι) (v0 : ι) (σ : ι → ι)
    (hσ : ∀ a b, famFusion D a b v0 = if b = σ a then 1 else 0) :
    Function.Involutive σ := by
  intro a
  have hs : famFusion D a (σ a) v0 = famFusion D (σ a) a v0 :=
    BraidingSkew.fusionRule_swap (D.Mfam (σ a)).isMod
      (D.Mfam a).isMod (D.Mfam v0).isMod
  rw [hσ, hσ, if_pos rfl] at hs
  by_contra hn
  rw [if_neg (Ne.symm hn)] at hs
  exact one_ne_zero hs

/-- The vacuum label is fixed, using only its unit fusion rule. -/
theorem vacuum_labels_fix_vacuum (D : VOA.ModularData W ι) (hirr : Irredundant D.Mfam)
    (v0 : ι) (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)))
    (σ : ι → ι) (hσ : ∀ a b, famFusion D a b v0 = if b = σ a then 1 else 0) :
    σ v0 = v0 := by
  have hs := hσ v0 v0
  rw [famFusion_vac D hirr v0 hv0, if_pos rfl] at hs
  by_contra hn
  rw [if_neg (Ne.symm hn)] at hs
  exact one_ne_zero hs

/-- It suffices to prove nonvanishing into the vacuum for the contragredient label;
the assumed delta rule then forces that label to be `σ a`. -/
theorem contragredientLabels_of_vacuum_nonzero (D : VOA.ModularData W ι) (v0 : ι)
    (hcomp : Complete D.Mfam) (σ : ι → ι)
    (hσ : ∀ a b, famFusion D a b v0 = if b = σ a then 1 else 0)
    (hnz : ∀ a b, Nonempty (ModuleEquiv W (contragredientModule (D.Mfam a).isMod)
      (D.Mfam b).isMod) → famFusion D a b v0 ≠ 0) : ContragredientLabels D σ := by
  obtain ⟨τ, hτ⟩ := exists_contragredientLabels D hcomp
  intro a
  have he : τ a = σ a := by
    have h := hnz a (τ a) (hτ a)
    rw [hσ] at h
    split_ifs at h with he
    · exact he
    · exact (h rfl).elim
  rw [← he]
  exact hτ a

end VOA.Huang.VerlindeRho
