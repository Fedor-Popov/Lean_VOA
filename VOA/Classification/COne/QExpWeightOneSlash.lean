import VOA.Classification.COne.QExpWeightOneTransform

/-! # Composition of the weight-one generator laws

The residue action is right multiplication of the row `(a,b)` by the
integral matrix, reduced modulo N. The scalar in the unnormalized slash
law is the quotient of the two coefficient-clearing factors.
-/

open Complex UpperHalfPlane ModularForm Matrix
open scoped MatrixGroups

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- Right row action of an integral modular matrix on the torsion indices. -/
def weightOneResidueAction {N : ℕ} (x : Fin 2 → ZMod N) (γ : SL(2, ℤ)) :
    Fin 2 → ZMod N :=
  ![x 0 * (γ 0 0 : ZMod N) + x 1 * (γ 1 0 : ZMod N),
    x 0 * (γ 0 1 : ZMod N) + x 1 * (γ 1 1 : ZMod N)]

@[simp] theorem weightOneResidueAction_one {N : ℕ} (x : Fin 2 → ZMod N) :
    weightOneResidueAction x 1 = x := by
  ext i
  fin_cases i <;> simp [weightOneResidueAction]

theorem weightOneResidueAction_mul {N : ℕ} (x : Fin 2 → ZMod N) (γ δ : SL(2, ℤ)) :
    weightOneResidueAction x (γ * δ) =
      weightOneResidueAction (weightOneResidueAction x γ) δ := by
  ext i
  fin_cases i <;>
    simp [weightOneResidueAction, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

@[simp] theorem weightOneResidueAction_S {N : ℕ} (x : Fin 2 → ZMod N) :
    weightOneResidueAction x ModularGroup.S = ![x 1, -x 0] := by
  simp [weightOneResidueAction, ModularGroup.S]

@[simp] theorem weightOneResidueAction_T {N : ℕ} (x : Fin 2 → ZMod N) :
    weightOneResidueAction x ModularGroup.T = ![x 0, x 0 + x 1] := by
  simp [weightOneResidueAction, ModularGroup.T]

theorem weightOneResidueAction_Gamma {N : ℕ} (x : Fin 2 → ZMod N)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    weightOneResidueAction x γ = x := by
  obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
  ext i
  fin_cases i <;> simp [weightOneResidueAction, h00, h01, h10, h11]

/-- Full integral-matrix covariance, proved by S/T generation, including inverses. -/
theorem weightOneNormalized_slash {N : ℕ} [NeZero N] (hf : WeightOneThetaFourier N)
    (x : Fin 2 → ZMod N) (γ : SL(2, ℤ)) :
    weightOneNormalized (x 0) (x 1) ∣[(1 : ℤ)] γ =
      weightOneNormalized (weightOneResidueAction x γ 0) (weightOneResidueAction x γ 1) := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction generalizing x with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · simpa using weightOneNormalized_slash_S hf (x 0) (x 1)
    · simpa using weightOneNormalized_slash_T hf (x 0) (x 1)
  | one => simp
  | mul g h _ _ ig ih =>
    rw [SlashAction.slash_mul, ig, ih, weightOneResidueAction_mul]
  | inv g _ ig =>
    have h := ig (weightOneResidueAction x g⁻¹)
    rw [← weightOneResidueAction_mul, inv_mul_cancel, weightOneResidueAction_one] at h
    have h' := congrArg (fun f : ℍ → ℂ => f ∣[(1 : ℤ)] g⁻¹) h
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] using h'.symm

theorem weightOneQSeries_eq_scale_normalized {N : ℕ} [NeZero N] (a b : Fin N) :
    weightOneQSeries N (weightOneStandardRoot N) a b =
      weightOneScale N (weightOneStandardRoot N) a b •
        weightOneNormalized (a.val : ZMod N) (b.val : ZMod N) := by
  have hi (c : Fin N) : weightOneIndex (c.val : ZMod N) = c := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt c.isLt
  funext τ
  simp only [Pi.smul_apply, smul_eq_mul, weightOneNormalized, hi]
  exact (mul_div_cancel₀ _ (weightOneScale_ne_zero (NeZero.pos N)
    (show IsPrimitiveRoot (weightOneStandardRoot N) N from
      Complex.isPrimitiveRoot_exp N (NeZero.ne N)) a b)).symm

/-- Exact slash formula for the original series, with the row action and its
nonzero normalization ratio made explicit. -/
theorem weightOneQSeries_slash_of_thetaFourier {N : ℕ} [NeZero N]
    (hf : WeightOneThetaFourier N) (a b : Fin N) (γ : SL(2, ℤ)) :
    let x := weightOneResidueAction ![(a.val : ZMod N), (b.val : ZMod N)] γ
    weightOneQSeries N (weightOneStandardRoot N) a b ∣[(1 : ℤ)] γ =
      (weightOneScale N (weightOneStandardRoot N) a b /
        weightOneScale N (weightOneStandardRoot N)
          (weightOneIndex (x 0)) (weightOneIndex (x 1))) •
        weightOneQSeries N (weightOneStandardRoot N)
          (weightOneIndex (x 0)) (weightOneIndex (x 1)) := by
  dsimp only
  rw [weightOneQSeries_eq_scale_normalized, SL_smul_slash]
  have he := weightOneNormalized_slash hf ![(a.val : ZMod N), (b.val : ZMod N)] γ
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at he
  rw [he]
  funext τ
  simp only [Pi.smul_apply, smul_eq_mul, weightOneNormalized]
  ring

/-- The original complete slash predicate for the standard root, conditional only
on the explicitly stated classical analytic identity. -/
theorem weightOneSlashLaws_standard_of_thetaFourier {N : ℕ} (hN : 0 < N)
    (hf : WeightOneThetaFourier N) : WeightOneSlashLaws N (weightOneStandardRoot N) := by
  letI : NeZero N := ⟨hN.ne'⟩
  constructor
  · intro a b γ hγ
    obtain ⟨δ, hδ, rfl⟩ := hγ
    change weightOneQSeries N (weightOneStandardRoot N) a b ∣[(1 : ℤ)] δ =
      weightOneQSeries N (weightOneStandardRoot N) a b
    rw [weightOneQSeries_eq_scale_normalized, SL_smul_slash]
    have he := weightOneNormalized_slash hf ![(a.val : ZMod N), (b.val : ZMod N)] δ
    rw [weightOneResidueAction_Gamma _ δ hδ] at he
    simpa using congrArg (fun f : ℍ → ℂ => weightOneScale N (weightOneStandardRoot N) a b • f) he
  · intro a b γ
    let x := weightOneResidueAction ![(a.val : ZMod N), (b.val : ZMod N)] γ
    refine ⟨weightOneIndex (x 0), weightOneIndex (x 1),
      weightOneScale N (weightOneStandardRoot N) a b /
        weightOneScale N (weightOneStandardRoot N)
          (weightOneIndex (x 0)) (weightOneIndex (x 1)), ?_⟩
    exact weightOneQSeries_slash_of_thetaFourier hf a b γ

end VOA.Classification.COne.SSHecke
