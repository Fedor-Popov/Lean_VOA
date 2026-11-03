import VOA.DeligneAudit.DeligneFusionCVFamily
import VOA.DeligneAudit.DeligneFusionCVCoeff
import VOA.DeligneAudit.DeligneFusionCVCrossRoot
import VOA.DeligneAudit.DeligneFusionCVTransport
import VOA.DeligneAudit.DeligneFusionCVShort
import VOA.DeligneAudit.DeligneFusionCVKernelHW
import VOA.DeligneAudit.DeligneFusionCVKernelOther

/-!
# The general auxiliary-weight cross-root square relation

For the zero-epsilon three-level CV family, the first simple-root kernel
generator is killed by the square of the top highest-root mode. The proof
derives every transport hypothesis from the source presentation. It uses
the quadratic and cubic cutoff identities and does not assume a kernel
map, a dimension bound, or fusion-product strictness.
-/

namespace VOA.DeligneAudit.A2.CVFamily

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.CVsl2

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ν ϱ : Weight} {j : ℕ}

/-- The auxiliary-weight version of the new highest-root kernel relation. -/
theorem first_kernel_theta_square (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j) :
    (R.op 5 ((ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j - 1) ^ 2)
      (R.op 3 (ν.1 + ϱ.1 + j - 1) w) = 0 := by
  let A := ν.1 + ϱ.1
  let B := ν.2 + ϱ.2
  let X := R.op 3 A
  let Y := R.op 4 (B + j - 1)
  let Z := R.op 5 (A + B + j - 1)
  let u := R.op 3 (A + j - 1) w
  let t2 := QFrom (R.op 3) (A + 1) 2 (2 * A + j - 1) w
  let t3 := QFrom (R.op 3) (A + 1) 3 (3 * A + j - 1) w
  have htheta : ∀ k, A + B + j ≤ k → R.op 5 k w = 0 := theta_trunc h
  have hy2 : (Y ^ 2) w = 0 := second_top_square h (by omega)
  have ht2 : (Y ^ 2) t2 = 0 :=
    CVCrossRoot.tail_square_kills R A B j hj htheta hy2 2 _
  have ht3 : (Y ^ 2) t3 = 0 :=
    CVCrossRoot.tail_square_kills R A B j hj htheta hy2 3 _
  have h0 : (Y ^ 2) u = 0 :=
    CVCrossRoot.shifted_generator_square_kills R A B j hj htheta hy2
  have hc2 : (2 : ℂ) • X u + t2 = 0 := by
    have he := congrArg (fun T : Module.End ℂ V => T w)
      (cutoff_split_two (CVRoots.sl2_first R).hFF A j hj)
    dsimp only at he
    rw [first_cutoff_two h] at he
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
      ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_ofNat] using he.symm
  have hc3 : (3 : ℂ) • ((X ^ 2) u) + (3 : ℂ) • X t2 + t3 = 0 := by
    have he := congrArg (fun T : Module.End ℂ V => T w)
      (cutoff_split_three (CVRoots.sl2_first R).hFF A j hj)
    dsimp only at he
    rw [first_cutoff_three h (by omega)] at he
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
      ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_ofNat] using he.symm
  have h1 : (Y ^ 2) (X u) = 0 := by
    have he := congrArg (fun v : V => (Y ^ 2) v) hc2
    simp only [map_add, map_smul, map_zero, ht2, add_zero] at he
    exact (smul_eq_zero.mp he).resolve_left (by norm_num)
  have hc2X : (2 : ℂ) • ((X ^ 2) u) + X t2 = 0 := by
    have he := congrArg (fun v : V => X v) hc2
    simpa only [map_add, map_smul, map_zero, pow_two, Module.End.mul_apply] using he
  have helim : (3 : ℂ) • ((X ^ 2) u) = t3 := by
    have he : (3 : ℂ) • ((X ^ 2) u) - t3 =
        (3 : ℂ) • ((2 : ℂ) • ((X ^ 2) u) + X t2) -
          ((3 : ℂ) • ((X ^ 2) u) + (3 : ℂ) • X t2 + t3) := by module
    have hz : (3 : ℂ) • ((X ^ 2) u) - t3 = 0 := by
      simpa only [hc2X, hc3, smul_zero, sub_zero] using he
    exact sub_eq_zero.mp hz
  have h2 : (Y ^ 2) ((X ^ 2) u) = 0 := by
    have he := congrArg (fun v : V => (Y ^ 2) v) helim
    dsimp only at he
    rw [map_smul, ht3] at he
    exact (smul_eq_zero.mp he).resolve_left (by norm_num)
  have hXY : X * Y - Y * X = -Z := by
    dsimp only [X, Y, Z]
    rw [op_comm_end]
    simp [Fin.sum_univ_eight, bracketTable]
    congr 2
    omega
  have hXZ : X * (-Z) = (-Z) * X := by
    have hc : X * Z = Z * X := by
      ext v
      exact op3_op5 A (A + B + j - 1) v
    simpa only [mul_neg, neg_mul] using congrArg Neg.neg hc
  have hz := VOA.DeligneAudit.CVTransport.square_kill_of_commutator
    X Y (-Z) hXY hXZ u h0 h1 h2
  simpa only [neg_sq] using hz

/-- All second-root CV relations of the first kernel generator. -/
theorem first_kernel_second_cv (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j) :
    CVRel (R.op 4) (parts ϱ.2 (ν.2 + 1) (j - 1))
      (R.op 3 (ν.1 + ϱ.1 + j - 1) w) := by
  apply cvrel_parts123 ϱ.2 (ν.2 + 1) (j - 1) (CVRoots.sl2_second R)
    (fun s => CVKernelHW.first_raising h hj 1 (by decide) s)
    (fun p hp => CVKernelHW.first_cartan_pos h 7 (by decide) p hp)
  · rw [Module.End.pow_apply]
    rw [show 3 * ϱ.2 + 2 * (ν.2 + 1) + (j - 1) + 1 =
      2 * ν.2 + 3 * ϱ.2 + j + 2 by omega]
    exact CVKernelHW.first_lowering_second h
  · intro q hq
    exact CVKernelOther.second_trunc h hj q (by omega)
  · intro s hs
    exact CVKernelOther.second_quadratic h hj s (by omega)

/-- All highest-root CV relations of the first kernel generator. -/
theorem first_kernel_highest_cv (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j) :
    CVRel (R.op 5) (parts (ϱ.1 + ϱ.2) (ν.1 + ν.2 + j - 1) 1)
      (R.op 3 (ν.1 + ϱ.1 + j - 1) w) := by
  change CVRel (R.op 5)
    (List.replicate (ϱ.1 + ϱ.2) 3 ++
      List.replicate (ν.1 + ν.2 + j - 1) 2 ++ [1]) _
  apply cvrel_parts32_one (ϱ.1 + ϱ.2) (ν.1 + ν.2 + j - 1)
    (CVRoots.sl2_highest R)
    (fun s => CVKernelHW.first_raising h hj 2 (by decide) s)
  · intro p hp
    simp only [LinearMap.add_apply,
      CVKernelHW.first_cartan_pos h 6 (by decide) p hp,
      CVKernelHW.first_cartan_pos h 7 (by decide) p hp, add_zero]
  · rw [Module.End.pow_apply]
    rw [show 3 * (ϱ.1 + ϱ.2) + 2 * (ν.1 + ν.2 + j - 1) + 2 =
      2 * ν.1 + 3 * ϱ.1 + 2 * ν.2 + 3 * ϱ.2 + 2 * j by omega]
    exact CVKernelHW.first_lowering_highest h hj
  · intro q hq
    rw [← op3_op5]
    have hz : R.op 5 q w = 0 := theta_trunc h q (by omega)
    rw [hz, map_zero]
  · rw [show ϱ.1 + ϱ.2 + (ν.1 + ν.2 + j - 1) =
      (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j - 1 by omega]
    exact first_kernel_theta_square h hj

/-- The first kernel generator satisfies the complete smaller auxiliary
CV presentation. This is a source-module relation theorem, without a
dimension or injectivity premise. -/
theorem first_kernel_rel_zero (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j) :
    CV3Rel R (R.op 3 (ν.1 + ϱ.1 + j - 1) w)
      (0, 1) (ν + (0, 1)) ϱ (j - 2) := by
  refine ⟨CVKernelHW.first_raising h hj, CVKernelHW.first_cartan_pos h,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using CVKernelHW.first_cartan_first h hj
  · change R.op 7 0 _ = ((1 + 2 * (ν.2 + 1) + 3 * ϱ.2 + (j - 2) : ℕ) : ℂ) • _
    rw [show 1 + 2 * (ν.2 + 1) + 3 * ϱ.2 + (j - 2) =
      2 * ν.2 + 3 * ϱ.2 + j + 1 by omega]
    exact CVKernelHW.first_cartan_second h
  · simpa using CVKernelHW.first_lowering_first h hj
  · change (R.op 4 0)^[1 + 2 * (ν.2 + 1) + 3 * ϱ.2 + (j - 2) + 1] _ = 0
    rw [show 1 + 2 * (ν.2 + 1) + 3 * ϱ.2 + (j - 2) + 1 =
      2 * ν.2 + 3 * ϱ.2 + j + 2 by omega]
    exact CVKernelHW.first_lowering_second h
  · simpa only [Prod.fst_add, Nat.add_zero, Nat.zero_add] using
      CVKernelHW.first_same_root h hj
  · change CVRel (R.op 4) (parts ϱ.2 (ν.2 + 1) (1 + (j - 2))) _
    rw [show 1 + (j - 2) = j - 1 by omega]
    exact first_kernel_second_cv h hj
  · change CVRel (R.op 5)
      (parts (ϱ.1 + ϱ.2) (ν.1 + (ν.2 + 1) + (j - 2)) 1) _
    rw [show ν.1 + (ν.2 + 1) + (j - 2) = ν.1 + ν.2 + j - 1 by omega]
    exact first_kernel_highest_cv h hj

end VOA.DeligneAudit.A2.CVFamily

#print axioms VOA.DeligneAudit.A2.CVFamily.first_kernel_theta_square
#print axioms VOA.DeligneAudit.A2.CVFamily.first_kernel_second_cv
#print axioms VOA.DeligneAudit.A2.CVFamily.first_kernel_highest_cv
#print axioms VOA.DeligneAudit.A2.CVFamily.first_kernel_rel_zero
