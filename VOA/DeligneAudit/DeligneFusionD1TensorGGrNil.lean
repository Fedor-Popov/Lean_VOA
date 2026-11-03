import VOA.DeligneAudit.DeligneFusionD1TensorGLocal
import Mathlib.Data.Nat.Choose.Sum

/-! Sharp vector nilpotence for commuting sums and actual tensor factors. -/
namespace VOA.DeligneAudit.D1TensorG

open scoped TensorProduct

noncomputable section
variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The binomial pigeonhole bound needs nilpotence only on the selected vector. -/
theorem add_pow_apply_zero (A B : Module.End K V) (v : V)
    (hcomm : Commute A B) {a b d : ℕ} (hA : (A ^ a) v = 0) (hB : (B ^ b) v = 0)
    (hd : a + b ≤ d + 1) : ((A + B) ^ d) v = 0 := by
  rw [hcomm.add_pow']
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  suffices hh : (A ^ i * B ^ j) v = 0 by rw [hh, smul_zero]
  by_cases hi : a ≤ i
  · rw [(hcomm.pow_pow i j).eq, Module.End.mul_apply,
      Module.End.pow_map_zero_of_le hi hA, map_zero]
  · rw [Module.End.mul_apply, Module.End.pow_map_zero_of_le (by
      have he := Finset.mem_antidiagonal.mp hij
      omega) hB, map_zero]

/-- Sharp nilpotence for a finite sum of commuting operators, proved by
successive binomial expansions, with no global nilpotence assumption. -/
theorem sum_pow_apply_zero {ι : Type*}
    (s : Finset ι) (A : ι → Module.End K V) (cap : ι → ℕ) (v : V)
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, Commute (A i) (A j))
    (hA : ∀ i ∈ s, (A i ^ (cap i + 1)) v = 0) :
    ((∑ i ∈ s, A i) ^ ((∑ i ∈ s, cap i) + 1)) v = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      apply add_pow_apply_zero _ _ v
      · exact Commute.sum_right s A (A i) (fun j hj =>
          hcomm i (by simp) j (by simp [hj]))
      · exact hA i (by simp)
      · exact ih (fun a ha b hb => hcomm a (by simp [ha]) b (by simp [hb]))
          (fun j hj => hA j (by simp [hj]))
      · omega

variable {ι : Type*} [DecidableEq ι]
variable {W : Type*} [AddCommGroup W] [Module K W]

/-- Powers of a local operator are the actual powers on its tensor factor. -/
theorem localOp_pow_tprod (j : ι) (A : Module.End K W) (v : ι → W) (d : ℕ) :
    (localOp j A ^ d) (PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K (Function.update v j ((A ^ d) (v j))) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ', Module.End.mul_apply, ih, localOp_tprod]
      simp only [Function.update_self, Function.update_idem, pow_succ', Module.End.mul_apply]

/-- The source nil relation at one factor gives its exact tensor relation. -/
theorem localOp_pow_zero (j : ι) (A : Module.End K W) (v : ι → W) (d : ℕ)
    (hd : (A ^ d) (v j) = 0) :
    (localOp j A ^ d) (PiTensorProduct.tprod K v) = 0 := by
  rw [localOp_pow_tprod, hd]
  exact (PiTensorProduct.tprod K).map_update_zero v j

end
end VOA.DeligneAudit.D1TensorG

#print axioms VOA.DeligneAudit.D1TensorG.sum_pow_apply_zero
#print axioms VOA.DeligneAudit.D1TensorG.localOp_pow_zero
