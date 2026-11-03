import VOA.DeligneAudit.DeligneFusionD1TensorGLocal
import VOA.DeligneAudit.A2SectorWeyl

/-!
# Actual tensor product current action

For any finite family of checked current modules, the sum of local current
operators is again a current module. Same-site brackets are transported by
the actual local linear map; all different-site brackets vanish.
-/

namespace VOA.DeligneAudit.D1TensorG

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {W : Type*} [AddCommGroup W] [Module K W]
variable {f : σ → σ → σ → K}

theorem current_comm_end (ρ : CurrentModule f W) (a b : σ) (r s : ℕ) :
    ρ.op a r * ρ.op b s - ρ.op b s * ρ.op a r = ∑ e, f a b e • ρ.op e (r + s) := by
  ext v
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
    LinearMap.smul_apply] using ρ.comm a b r s v

/-- Sum the actual current actions over tensor factors. -/
def tensorOp (ρ : ι → CurrentModule f W) (c : σ) (k : ℕ) :
    Module.End K (Tensor (K := K) (ι := ι) (W := W)) :=
  ∑ i, localOp i ((ρ i).op c k)

omit [Fintype ι] in
theorem local_current_comm (ρ : ι → CurrentModule f W) (i : ι) (a b : σ) (r s : ℕ) :
    localOp i ((ρ i).op a r) * localOp i ((ρ i).op b s) -
        localOp i ((ρ i).op b s) * localOp i ((ρ i).op a r) =
      ∑ e, f a b e • localOp i ((ρ i).op e (r + s)) := by
  rw [← localOp_mul, ← localOp_mul]
  change localMap i ((ρ i).op a r * (ρ i).op b s) -
    localMap i ((ρ i).op b s * (ρ i).op a r) = _
  rw [← map_sub, current_comm_end, map_sum]
  simp only [map_smul, localMap_apply]

theorem tensorOp_comm (ρ : ι → CurrentModule f W) (a b : σ) (r s : ℕ) :
    tensorOp ρ a r * tensorOp ρ b s - tensorOp ρ b s * tensorOp ρ a r =
      ∑ e, f a b e • tensorOp ρ e (r + s) := by
  have key : ∀ i j : ι,
      localOp i ((ρ i).op a r) * localOp j ((ρ j).op b s) -
          localOp j ((ρ j).op b s) * localOp i ((ρ i).op a r) =
        if i = j then ∑ e, f a b e • localOp i ((ρ i).op e (r + s)) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact local_current_comm ρ i a b r s
    · rw [localOp_comm hij, sub_self, if_neg hij]
  have he : tensorOp ρ a r * tensorOp ρ b s - tensorOp ρ b s * tensorOp ρ a r =
      ∑ i, ∑ j, (localOp i ((ρ i).op a r) * localOp j ((ρ j).op b s) -
        localOp j ((ρ j).op b s) * localOp i ((ρ i).op a r)) := by
    simp only [tensorOp, Finset.sum_mul_sum, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_comm
  rw [he]
  simp only [key, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [tensorOp, Finset.smul_sum]
  exact Finset.sum_comm

/-- The actual finite tensor product current module. -/
def tensorRep (ρ : ι → CurrentModule f W) :
    CurrentModule f (Tensor (K := K) (ι := ι) (W := W)) where
  op := tensorOp ρ
  comm a b r s v := by
    have hh := congrArg (fun A => A v) (tensorOp_comm ρ a b r s)
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
      LinearMap.smul_apply] using hh

@[simp] theorem tensorRep_op (ρ : ι → CurrentModule f W) (c : σ) (k : ℕ) :
    (tensorRep ρ).op c k = tensorOp ρ c k := rfl

end
end VOA.DeligneAudit.D1TensorG

#print axioms VOA.DeligneAudit.D1TensorG.tensorOp_comm
#print axioms VOA.DeligneAudit.D1TensorG.tensorRep
