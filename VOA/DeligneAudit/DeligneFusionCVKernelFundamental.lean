import VOA.DeligneAudit.DeligneFusionCVFamily
import VOA.DeligneAudit.DeligneFusionCVCoeff
import VOA.DeligneAudit.DeligneFusionCVCrossRoot
import VOA.DeligneAudit.DeligneFusionCVKernelOther
import VOA.DeligneAudit.DeligneFusionCVShort
import VOA.DeligneAudit.DeligneFusionCVKernelGeneralHW

/-!
# Highest-root truncation for the fundamental-epsilon first CV kernel

For `CV3Rel R w ω₁ ν ρ j`, write `A=ν₁+ρ₁`, `B=ν₂+ρ₂`,
`u=f₁(A+j)w`, and `q=A+B+j`. The new kernel relation is `fθ(q)u=0`.

The proof uses `Y=f₂(B+j)`, which already kills `w`, and the source
quadratic cutoff at `A`. Splitting off `f₁(A)` gives `2 f₁(A)u+tail=0`.
Every commutator of `Y` with a tail mode is beyond the source theta
truncation; also `Yu=0`. Applying `Y` leaves `2 fθ(q)u=0`.

Only source CV relations are used. The argument works already for
`j ≥ 1`, including the boundary needed by the fundamental base case.
-/

namespace VOA.DeligneAudit.A2.CVKernelFundamental

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVCrossRoot

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A high second-root mode killing the generator kills every coefficient of
the commuting cutoff series on the common high-theta kernel. -/
theorem f2_kills_QFrom (R : CurrentModule bracketTable V) {w : V} {L b p : ℕ}
    (hbp : L ≤ b + p) (htheta : ∀ k, L ≤ k → R.op 5 k w = 0)
    (hy : R.op 4 b w = 0) (r s : ℕ) :
    R.op 4 b (QFrom (R.op 3) p r s w) = 0 := by
  have hc : R.op 4 b (QFrom (R.op 3) p r s w) =
      QFrom (R.op 3) p r s (R.op 4 b w) := by
    apply Q_commute_on (fromMode (R.op 3) p) (R.op 4 b) (thetaKernel R L)
    · intro k v hv
      by_cases hk : p ≤ k
      · simpa only [fromMode, if_pos hk] using thetaKernel_f1 R L k hv
      · simp only [fromMode, if_neg hk, LinearMap.zero_apply]
        exact (thetaKernel R L).zero_mem
    · intro k v hv
      by_cases hk : p ≤ k
      · simp only [fromMode, if_pos hk]
        exact f2_f1_commute_on R (by omega) hv
      · simp only [fromMode, if_neg hk, LinearMap.zero_apply, map_zero]
    · exact htheta
  rw [hc, hy, map_zero]

variable {R : CurrentModule bracketTable V} {w : V} {ν ϱ : Weight} {j : ℕ}

theorem source_second_trunc (h : CV3Rel R w (1, 0) ν ϱ j) (s : ℕ)
    (hs : ν.2 + ϱ.2 + j ≤ s) : R.op 4 s w = 0 := by
  apply trunc_of_cvrel h.second s
  simp only [parts_length]
  omega

theorem source_theta_trunc (h : CV3Rel R w (1, 0) ν ϱ j) (s : ℕ)
    (hs : (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j + 1 ≤ s) : R.op 5 s w = 0 := by
  apply trunc_of_cvrel h.highest s
  simp only [parts_length]
  omega

/-- The source quadratic cutoff, with the extra trailing one from `ε=ω₁`. -/
theorem first_cutoff_two (h : CV3Rel R w (1, 0) ν ϱ j) :
    QFrom (R.op 3) (ν.1 + ϱ.1) 2 (2 * (ν.1 + ϱ.1) + j) w = 0 := by
  apply cvrel_cutoff (CVRoots.sl2_first R).hFF h.first
    (ν.1 + ϱ.1) 2 _ (by omega)
  have ht : T (ν.1 + ϱ.1) (parts ϱ.1 ν.1 (1 + j)) = j + 1 := by
    simpa only [Nat.add_comm 1 j, Nat.add_comm ν.1 ϱ.1] using
      parts_tail ϱ.1 ν.1 (j + 1)
  rw [ht]
  omega

/-- The genuinely new highest-root linear relation on the first kernel generator.
It holds already for `j ≥ 1`. -/
theorem theta_linear_of_pos (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 1 ≤ j) :
    R.op 5 ((ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j)
      (R.op 3 (ν.1 + ϱ.1 + j) w) = 0 := by
  let A := ν.1 + ϱ.1
  let B := ν.2 + ϱ.2
  let q := A + B + j
  let X := R.op 3 A
  let Y := R.op 4 (B + j)
  let u := R.op 3 (A + j) w
  change R.op 5 q u = 0
  have htheta : ∀ s, q + 1 ≤ s → R.op 5 s w = 0 := by
    intro s hs
    exact source_theta_trunc h s (by simpa only [q, A, B] using hs)
  have hy : R.op 4 (B + j) w = 0 := source_second_trunc h _ (by dsimp [B]; omega)
  have hquad : (2 : ℕ) • X u + QFrom (R.op 3) (A + 1) 2 (2 * A + j) w = 0 := by
    have hq := first_cutoff_two h
    change QFrom (R.op 3) A 2 (2 * A + j) w = 0 at hq
    have hs := cutoff_split_two (CVRoots.sl2_first R).hFF A (j + 1) (by omega)
    rw [show 2 * A + (j + 1) - 1 = 2 * A + j by omega,
      show A + (j + 1) - 1 = A + j by omega] at hs
    rw [hs, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply] at hq
    exact hq
  have htail : Y (QFrom (R.op 3) (A + 1) 2 (2 * A + j) w) = 0 :=
    f2_kills_QFrom R (L := q + 1) (b := B + j) (p := A + 1)
      (by dsimp [q]; omega) htheta hy 2 _
  have hyu : Y u = 0 := by
    change R.op 4 (B + j) (R.op 3 (A + j) w) = 0
    have hlast : R.op 5 ((B + j) + (A + j)) w = 0 :=
      htheta _ (by dsimp [q]; omega)
    rw [comm_apply 4 3]
    simp [Fin.sum_univ_eight, bracketTable, hy, hlast]
  have hcomm (v : V) : Y (X v) = X (Y v) + R.op 5 q v := by
    change R.op 4 (B + j) (R.op 3 A v) =
      R.op 3 A (R.op 4 (B + j) v) + R.op 5 q v
    rw [comm_apply 4 3]
    simp [Fin.sum_univ_eight, bracketTable, show B + j + A = q by dsimp [q]; omega]
  have h := congrArg Y hquad
  rw [map_add, map_nsmul, map_zero, htail, add_zero, hcomm u, hyu, map_zero,
    zero_add] at h
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h
  exact h.resolve_left (by norm_num)

/-- Compatibility specialization for the `j ≥ 2` fundamental recurrence. -/
theorem theta_linear (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 2 ≤ j) :
    R.op 5 ((ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j)
      (R.op 3 (ν.1 + ϱ.1 + j) w) = 0 :=
  theta_linear_of_pos h (by omega)

/-- All higher highest-root modes kill the first fundamental-epsilon kernel
generator, including the new boundary mode. -/
theorem theta_trunc_kernel_of_pos (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 1 ≤ j)
    (s : ℕ) (hs : (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j ≤ s) :
    R.op 5 s (R.op 3 (ν.1 + ϱ.1 + j) w) = 0 := by
  by_cases heq : s = (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j
  · subst s
    exact theta_linear_of_pos h hj
  · rw [← op3_op5 (ν.1 + ϱ.1 + j) s w,
      source_theta_trunc h s (by omega), map_zero]

theorem theta_trunc_kernel (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 2 ≤ j)
    (s : ℕ) (hs : (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j ≤ s) :
    R.op 5 s (R.op 3 (ν.1 + ϱ.1 + j) w) = 0 :=
  theta_trunc_kernel_of_pos h (by omega) s hs

/-- The second-root linear truncation on the fundamental first kernel. -/
theorem second_trunc_kernel (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 1 ≤ j)
    (s : ℕ) (hs : ν.2 + ϱ.2 + j ≤ s) :
    R.op 4 s (R.op 3 (ν.1 + ϱ.1 + j) w) = 0 := by
  have hs0 := source_second_trunc h s hs
  have ht : R.op 5 (s + (ν.1 + ϱ.1 + j)) w = 0 :=
    source_theta_trunc h _ (by omega)
  rw [comm_apply 4 3]
  simp [Fin.sum_univ_eight, bracketTable, hs0, ht]

/-- The source second-root cutoff relation at the target quadratic threshold. -/
theorem second_cutoff_two (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 1 ≤ j)
    (s : ℕ) (hs : 2 * (ν.2 + ϱ.2) + j ≤ s) :
    QFrom (R.op 4) (ν.2 + ϱ.2 + 1) 2 s w = 0 := by
  apply cvrel_cutoff (CVRoots.sl2_second R).hFF h.second
    (ν.2 + ϱ.2 + 1) 2 s (by omega)
  have ht : T (ν.2 + ϱ.2 + 1) (parts ϱ.2 ν.2 (0 + j)) = j - 1 := by
    simp only [parts, T_append, T_replicate,
      List.length_append, List.length_replicate]
    omega
  rw [ht]
  omega

/-- All target second-root quadratic coefficients vanish on the fundamental
first kernel generator, already at `j=1`. -/
theorem second_quadratic_kernel (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 1 ≤ j)
    (s : ℕ) (hs : 2 * (ν.2 + ϱ.2) + j ≤ s) :
    Q (R.op 4) 2 s (R.op 3 (ν.1 + ϱ.1 + j) w) = 0 := by
  rw [CVKernelOther.Q_two_eq_QFrom (R.op 4) (CVRoots.sl2_second R).hFF
    (ν.2 + ϱ.2) (ν.2 + ϱ.2 + j) s (second_trunc_kernel h hj) (by omega)]
  have hc := CVKernelOther.f1_QFrom_second R
    (L := (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j + 1)
    (a := ν.1 + ϱ.1 + j) (p := ν.2 + ϱ.2 + 1)
    (by omega) (source_theta_trunc h) 2 s
  rw [← hc, second_cutoff_two h hj s hs, map_zero]

/-- All second-root CV relations of the fundamental-epsilon first kernel source. -/
theorem first_kernel_second_cv (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 1 ≤ j) :
    CVRel (R.op 4) (parts ϱ.2 (ν.2 + 1) (j - 1))
      (R.op 3 (ν.1 + ϱ.1 + j) w) := by
  have hj' : 2 ≤ 1 + j := by omega
  have hidx : ν.1 + ϱ.1 + 1 + j - 1 = ν.1 + ϱ.1 + j := by omega
  apply cvrel_parts123 ϱ.2 (ν.2 + 1) (j - 1) (CVRoots.sl2_second R)
  · intro s
    simpa only [hidx] using
      CVKernelGeneralHW.first_raising h hj' 1 (by decide) s
  · intro p hp
    simpa only [hidx] using
      CVKernelGeneralHW.first_cartan_pos h 7 (by decide) p hp
  · rw [Module.End.pow_apply]
    rw [show 3 * ϱ.2 + 2 * (ν.2 + 1) + (j - 1) + 1 =
      2 * ν.2 + 3 * ϱ.2 + j + 2 by omega]
    simpa only [Nat.zero_add, hidx] using
      CVKernelGeneralHW.first_lowering_second h
  · intro s hs
    exact second_trunc_kernel h hj s (by omega)
  · intro s hs
    exact second_quadratic_kernel h hj s (by omega)

/-- The new theta cutoff supplies every highest-root CV relation of the
fundamental-epsilon first kernel source. -/
theorem first_kernel_highest_cv (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 1 ≤ j) :
    CVRel (R.op 5) (parts (ϱ.1 + ϱ.2) (ν.1 + ν.2 + j) 0)
      (R.op 3 (ν.1 + ϱ.1 + j) w) := by
  have hj' : 2 ≤ 1 + j := by omega
  have hidx : ν.1 + ϱ.1 + 1 + j - 1 = ν.1 + ϱ.1 + j := by omega
  have htr : ∀ s, (ϱ.1 + ϱ.2) + (ν.1 + ν.2 + j) ≤ s →
      R.op 5 s (R.op 3 (ν.1 + ϱ.1 + j) w) = 0 := by
    intro s hs
    exact theta_trunc_kernel_of_pos h hj s (by omega)
  apply cvrel_parts123 (ϱ.1 + ϱ.2) (ν.1 + ν.2 + j) 0 (CVRoots.sl2_highest R)
  · intro s
    simpa only [hidx] using
      CVKernelGeneralHW.first_raising h hj' 2 (by decide) s
  · intro p hp
    simp only [LinearMap.add_apply]
    have h6 := CVKernelGeneralHW.first_cartan_pos h 6 (by decide) p hp
    have h7 := CVKernelGeneralHW.first_cartan_pos h 7 (by decide) p hp
    simpa only [hidx, h6, h7, add_zero] using congrArg₂ HAdd.hAdd h6 h7
  · rw [Module.End.pow_apply]
    rw [show 3 * (ϱ.1 + ϱ.2) + 2 * (ν.1 + ν.2 + j) + 0 + 1 =
      1 + 0 + 2 * ν.1 + 3 * ϱ.1 + 2 * ν.2 + 3 * ϱ.2 + 2 * j by omega]
    simpa only [hidx] using
      CVKernelGeneralHW.first_lowering_highest h hj'
  · intro s hs
    exact htr s (by simpa only [Nat.add_zero] using hs)
  · intro s hs
    exact Q_high (CVRoots.sl2_highest R).hFF htr 2 s (by omega)

/-- The complete actual source presentation of the fundamental-epsilon first
kernel generator. This includes the boundary `j=1`. -/
theorem first_kernel_rel_fundamental (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 1 ≤ j) :
    CV3Rel R (R.op 3 (ν.1 + ϱ.1 + j) w) (0, 0) (ν + (0, 1)) ϱ (j - 1) := by
  have hj' : 2 ≤ 1 + j := by omega
  have hidx : ν.1 + ϱ.1 + 1 + j - 1 = ν.1 + ϱ.1 + j := by omega
  have hones : 1 + j - 2 = j - 1 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he s
    simpa only [hidx] using
      CVKernelGeneralHW.first_raising h hj' e he s
  · intro hh hhh s hs
    simpa only [hidx] using
      CVKernelGeneralHW.first_cartan_pos h hh hhh s hs
  · simpa only [Prod.fst_add, Nat.add_zero, Nat.zero_add, hidx, hones] using
      CVKernelGeneralHW.first_cartan_first h hj'
  · change R.op 7 0 _ = ((0 + 2 * (ν.2 + 1) + 3 * ϱ.2 + (j - 1) : ℕ) : ℂ) • _
    rw [show 0 + 2 * (ν.2 + 1) + 3 * ϱ.2 + (j - 1) =
      2 * ν.2 + 3 * ϱ.2 + j + 1 by omega]
    simpa only [Nat.zero_add, hidx] using
      CVKernelGeneralHW.first_cartan_second h
  · simpa only [Prod.fst_add, Nat.add_zero, Nat.zero_add, hidx, hones] using
      CVKernelGeneralHW.first_lowering_first h hj'
  · change (R.op 4 0)^[0 + 2 * (ν.2 + 1) + 3 * ϱ.2 + (j - 1) + 1] _ = 0
    rw [show 0 + 2 * (ν.2 + 1) + 3 * ϱ.2 + (j - 1) + 1 =
      2 * ν.2 + 3 * ϱ.2 + j + 2 by omega]
    simpa only [Nat.zero_add, hidx] using
      CVKernelGeneralHW.first_lowering_second h
  · simpa only [Prod.fst_add, Nat.add_zero, Nat.zero_add, hidx, hones] using
      CVKernelGeneralHW.first_same_root h hj'
  · simpa only [Prod.snd_add, Nat.zero_add] using first_kernel_second_cv h hj
  · change CVRel (R.op 5)
      (parts (ϱ.1 + ϱ.2) (ν.1 + (ν.2 + 1) + (j - 1)) (0 + 0)) _
    rw [show ν.1 + (ν.2 + 1) + (j - 1) = ν.1 + ν.2 + j by omega, Nat.zero_add]
    exact first_kernel_highest_cv h hj

end

end VOA.DeligneAudit.A2.CVKernelFundamental

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.CVKernelFundamental.theta_linear_of_pos
#print axioms VOA.DeligneAudit.A2.CVKernelFundamental.theta_linear
#print axioms VOA.DeligneAudit.A2.CVKernelFundamental.theta_trunc_kernel
#print axioms VOA.DeligneAudit.A2.CVKernelFundamental.second_trunc_kernel
#print axioms VOA.DeligneAudit.A2.CVKernelFundamental.second_quadratic_kernel
#print axioms VOA.DeligneAudit.A2.CVKernelFundamental.first_kernel_rel_fundamental
end AxiomAudit
