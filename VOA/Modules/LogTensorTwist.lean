import VOA.Modules.LogTensorContraL0Exp
import VOA.Classification.COne.McRaeM2Dual

/-! The actual logarithmic conformal twist and its naturality.
The Jordan part is retained. This constructs the module automorphism;
its balancing identity requires the analytic braiding construction. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LogTensor.Contra
open Module (End)
open scoped BigOperators
universe u
variable {V M R : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℂ R]
  {W : VertexOperatorAlgebra V}

/-- Actual weak morphisms preserve the canonical generalized grading. -/
theorem hom_mem_weight (N : LogVModule W M) (P : LogVModule W R)
    (f : N.toWeakModule.Hom P.toWeakModule) {α : ℂ} {x : M}
    (hx : x ∈ N.weight α) : f.toLinearMap x ∈ P.weight α :=
  C2Rigid.gradedHom_of_isGenGraded N.toGW P.toGW f
    N.weight_le_maxGenEigenspace P.weight_le_maxGenEigenspace α x hx

/-- The actual Jordan operator is natural on logarithmic module morphisms. -/
theorem hom_L0nil (N : LogVModule W M) (P : LogVModule W R)
    (f : N.toWeakModule.Hom P.toWeakModule) (x : M) :
    f.toLinearMap (N.L0nil x) = P.L0nil (f.toLinearMap x) := by
  have hx : x ∈ ⨆ α, N.weight α := by
    rw [N.isInternal.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction N.weight
    (motive := fun x => f.toLinearMap (N.L0nil x) = P.L0nil (f.toLinearMap x))
    hx ?_ ?_ ?_
  · intro α y hy
    rw [N.L0nil_apply_of_mem hy,P.L0nil_apply_of_mem (hom_mem_weight N P f hy),
      LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,map_sub,map_smul]
    congr 1
    exact f.map_act W.conformalVector 1 y
  · simp only [map_zero]
  · intro a b ha hb
    simp only [map_add,ha,hb]

theorem hom_L0nil_pow (N : LogVModule W M) (P : LogVModule W R)
    (f : N.toWeakModule.Hom P.toWeakModule) (k : ℕ) (x : M) :
    f.toLinearMap ((N.L0nil ^ k) x) = (P.L0nil ^ k) (f.toLinearMap x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply,hom_L0nil,ih,pow_succ',Module.End.mul_apply]

/-- The finite Jordan exponential is natural, including on nonsemisimple modules. -/
theorem hom_nilExp (N : LogVModule W M) (P : LogVModule W R)
    (f : N.toWeakModule.Hom P.toWeakModule) (c : ℂ) (x : M) :
    f.toLinearMap (nilExp N c x) = nilExp P c (f.toLinearMap x) := by
  obtain ⟨k,hk⟩ := L0nil_locallyNilpotent N x
  have hp : (P.L0nil ^ k) (f.toLinearMap x) = 0 := by
    rw [← hom_L0nil_pow N P f k x,hk,map_zero]
  rw [nilExp_finite N c hk,nilExp_finite P c hp,map_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [map_smul,hom_L0nil_pow])

/-- The actual conformal exponential is natural on all actual logarithmic maps. -/
theorem hom_L0exp (N : LogVModule W M) (P : LogVModule W R)
    (f : N.toWeakModule.Hom P.toWeakModule) (c : ℂ) (x : M) :
    f.toLinearMap (L0exp N c x) = L0exp P c (f.toLinearMap x) := by
  have hx : x ∈ ⨆ α, N.weight α := by
    rw [N.isInternal.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction N.weight
    (motive := fun x => f.toLinearMap (L0exp N c x) = L0exp P c (f.toLinearMap x))
    hx ?_ ?_ ?_
  · intro α y hy
    rw [L0exp_apply_of_mem N c hy,
      L0exp_apply_of_mem P c (hom_mem_weight N P f hy),map_smul,hom_nilExp]
  · simp only [map_zero]
  · intro a b ha hb
    simp only [map_add,ha,hb]

/-- The actual logarithmic conformal twist exp(2 pi i L(0)). -/
def twist (N : LogVModule W M) : M ≃ₗ[ℂ] M := L0exp N (2 * Real.pi * Complex.I)

theorem twist_mode_homogeneous (N : LogVModule W M) {d : ℤ} {a : V}
    (ha : a ∈ W.grading d) (n : ℤ) (x : M) :
    twist N (mode (N.YM a) n x) = mode (N.YM a) n (twist N x) := by
  have hx : x ∈ ⨆ α, N.weight α := by
    rw [N.isInternal.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction N.weight
    (motive := fun x => twist N (mode (N.YM a) n x) = mode (N.YM a) n (twist N x))
    hx ?_ ?_ ?_
  · intro α y hy
    rw [twist,L0exp_apply_of_mem N _ (N.mode_mem_weight ha hy n),
      L0exp_apply_of_mem N _ hy,nilExp_mode,map_smul]
    have he : Complex.exp ((2 * Real.pi * Complex.I) * (α + (d : ℂ) - n - 1)) =
        Complex.exp ((2 * Real.pi * Complex.I) * α) := by
      have hc : (2 * (Real.pi : ℂ) * Complex.I) * (α + (d : ℂ) - n - 1) =
          (2 * Real.pi * Complex.I) * α + ((d-n-1 : ℤ) : ℂ) *
            (2 * Real.pi * Complex.I) := by push_cast; ring
      rw [hc,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]
    rw [he]
  · simp only [map_zero]
  · intro a b ha hb
    simp only [map_add,ha,hb]

/-- Integral VOA weights make the genuine twist a module automorphism. -/
theorem twist_mode (N : LogVModule W M) (a : V) (n : ℤ) (x : M) :
    twist N (mode (N.YM a) n x) = mode (N.YM a) n (twist N x) := by
  have ha : a ∈ ⨆ d, W.grading d := by
    rw [W.isInternal.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun a => twist N (mode (N.YM a) n x) = mode (N.YM a) n (twist N x))
    ha (fun d a ha => twist_mode_homogeneous N ha n x) ?_ ?_
  · simp only [map_zero,mode_zero,LinearMap.zero_apply]
  · intro a b ha hb
    simp only [map_add,mode_add,LinearMap.add_apply,ha,hb]

/-- The actual twist as a genuine weak-module endomorphism. -/
def twistHom (N : LogVModule W M) : N.toWeakModule.Hom N.toWeakModule where
  toLinearMap := (twist N).toLinearMap
  map_act := twist_mode N

/-- Naturality of the genuine twist, without a semisimple L(0) assumption. -/
theorem twist_natural (N : LogVModule W M) (P : LogVModule W R)
    (f : N.toWeakModule.Hom P.toWeakModule) (x : M) :
    f.toLinearMap (twist N x) = twist P (f.toLinearMap x) :=
  hom_L0exp N P f _ x

end VOA.LogTensor.Contra
