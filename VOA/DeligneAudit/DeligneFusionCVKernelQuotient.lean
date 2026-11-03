import VOA.DeligneAudit.DeligneFusionCVKernelOther
import VOA.DeligneAudit.DeligneFusionCVCoeff

/-!
# Highest-root truncation of the second A₂ kernel generator

In the zero-epsilon auxiliary CV family, impose the actual quotient relation
that the first simple-root kernel generator vanishes. Then the second
generator has the stronger highest-root linear truncation required by its
source presentation. This derives SRK (8.23) at the full auxiliary indices,
without a dimension bound or an assumed target presentation.
-/

namespace VOA.DeligneAudit.A2.CVKernelQuotient

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.A2.CVFamily

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ν ϱ : Weight} {j : ℕ}

/-- The source second-root quadratic relation at the first mode of its ones. -/
theorem second_cutoff_at_base (h : CV3Rel R w (0, 0) ν ϱ j) :
    QFrom (R.op 4) (ν.2 + ϱ.2) 2 (2 * (ν.2 + ϱ.2) + j - 1) w = 0 := by
  apply cvrel_cutoff (CVRoots.sl2_second R).hFF h.second
    (ν.2 + ϱ.2) 2 _ (by omega)
  have ht : T (ν.2 + ϱ.2) (parts ϱ.2 ν.2 (0 + j)) = j := by
    simpa only [Nat.zero_add, Nat.add_comm ν.2 ϱ.2] using parts_tail ϱ.2 ν.2 j
  rw [ht]
  omega

/-- The boundary highest-root mode kills the second kernel generator after
the first generator has been set to zero. -/
theorem second_kernel_theta_boundary (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j - 1) w = 0) :
    R.op 5 ((ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j - 1)
      (R.op 4 (ν.2 + ϱ.2 + j - 1) w) = 0 := by
  let A := ν.1 + ϱ.1
  let B := ν.2 + ϱ.2
  let a := A + j - 1
  let b := B + j - 1
  let z := A + B + j - 1
  let v := R.op 4 b w
  let t2 := QFrom (R.op 4) (B + 1) 2 (2 * B + j - 1) w
  have hfirst' : R.op 3 a w = 0 := hfirst
  have htheta : ∀ q, A + B + j ≤ q → R.op 5 q w = 0 := theta_trunc h
  have hXv : R.op 3 a v = 0 := by
    have ht := htheta (a + b) (by dsimp [a, b]; omega)
    change R.op 3 a (R.op 4 b w) = 0
    rw [comm_apply 3 4]
    simp [Fin.sum_univ_eight, bracketTable, hfirst', ht]
  have htail : R.op 3 a t2 = 0 := by
    have hc := CVKernelOther.f1_QFrom_second R
      (L := A + B + j) (a := a) (p := B + 1)
      (by dsimp [a]; omega) htheta 2 (2 * B + j - 1)
    change R.op 3 a (QFrom (R.op 4) (B + 1) 2 (2 * B + j - 1) w) = 0
    rw [hc, hfirst', map_zero]
  have hc2 : (2 : ℂ) • R.op 4 B v + t2 = 0 := by
    have he := congrArg (fun T : Module.End ℂ V => T w)
      (cutoff_split_two (CVRoots.sl2_second R).hFF B j hj)
    dsimp only at he
    rw [second_cutoff_at_base h] at he
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
      ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_ofNat] using he.symm
  have hcomm : R.op 3 a (R.op 4 B v) = -R.op 5 z v := by
    rw [comm_apply 3 4]
    simp [Fin.sum_univ_eight, bracketTable, hXv,
      show a + B = z by dsimp [a, z]; omega]
  have hneg : (2 : ℂ) • (-R.op 5 z v) = 0 := by
    have he := congrArg (fun x : V => R.op 3 a x) hc2
    simpa only [map_add, map_smul, map_zero, htail, add_zero, hcomm] using he
  exact neg_eq_zero.mp ((smul_eq_zero.mp hneg).resolve_left (by norm_num))

/-- All highest-root modes at the stronger target cutoff kill the second
kernel generator in the quotient by the first generator. -/
theorem second_kernel_theta_trunc (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j - 1) w = 0)
    (q : ℕ) (hq : (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j - 1 ≤ q) :
    R.op 5 q (R.op 4 (ν.2 + ϱ.2 + j - 1) w) = 0 := by
  by_cases heq : q = (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j - 1
  · subst q
    exact second_kernel_theta_boundary h hj hfirst
  · rw [← op4_op5, theta_trunc h q (by omega), map_zero]

/-- The quotient relation also improves the first-root linear truncation on
the second generator by one mode, as required by its source partition. -/
theorem second_kernel_first_trunc (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j - 1) w = 0)
    (q : ℕ) (hq : ν.1 + ϱ.1 + j - 1 ≤ q) :
    R.op 3 q (R.op 4 (ν.2 + ϱ.2 + j - 1) w) = 0 := by
  have hq0 : R.op 3 q w = 0 := by
    by_cases heq : q = ν.1 + ϱ.1 + j - 1
    · simpa only [heq] using hfirst
    · apply trunc_of_cvrel h.first q
      simp only [parts_length]
      omega
  have ht : R.op 5 (q + (ν.2 + ϱ.2 + j - 1)) w = 0 :=
    theta_trunc h _ (by omega)
  rw [comm_apply 3 4]
  simp [Fin.sum_univ_eight, bracketTable, hq0, ht]

/-- Setting the first generator to zero improves the source first-root
cutoff coefficient relation at its boundary degree. -/
theorem first_cutoff_in_quotient (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j - 1) w = 0)
    (s : ℕ) (hs : 2 * (ν.1 + ϱ.1) + j - 1 ≤ s) :
    QFrom (R.op 3) (ν.1 + ϱ.1 + 1) 2 s w = 0 := by
  let A := ν.1 + ϱ.1
  have hfirst' : R.op 3 (A + j - 1) w = 0 := hfirst
  by_cases heq : s = 2 * A + j - 1
  · subst s
    have he := congrArg (fun T : Module.End ℂ V => T w)
      (cutoff_split_two (CVRoots.sl2_first R).hFF A j hj)
    dsimp only at he
    rw [first_cutoff_two h] at he
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
      hfirst', map_zero, smul_zero, zero_add] using he.symm
  · apply cvrel_cutoff (CVRoots.sl2_first R).hFF h.first
      (ν.1 + ϱ.1 + 1) 2 s (by omega)
    have ht : T (ν.1 + ϱ.1 + 1) (parts ϱ.1 ν.1 (0 + j)) = j - 1 := by
      simp only [parts, T_append, T_replicate,
        List.length_append, List.length_replicate]
      omega
    rw [ht]
    dsimp only [A] at heq
    omega

/-- A cutoff first-root current commutes through a high second-root mode
on the common kernel of the high highest-root modes. -/
theorem f2_QFrom_first (R : CurrentModule bracketTable V) {w : V} {L b p : ℕ}
    (hbp : L ≤ b + p) (htheta : ∀ k, L ≤ k → R.op 5 k w = 0) (r s : ℕ) :
    R.op 4 b (QFrom (R.op 3) p r s w) =
      QFrom (R.op 3) p r s (R.op 4 b w) := by
  apply CVCrossRoot.Q_commute_on (fromMode (R.op 3) p) (R.op 4 b)
    (CVCrossRoot.thetaKernel R L)
  · intro k v hv
    by_cases hk : p ≤ k
    · simpa only [fromMode, if_pos hk] using CVCrossRoot.thetaKernel_f1 R L k hv
    · simp only [fromMode, if_neg hk, LinearMap.zero_apply]
      exact (CVCrossRoot.thetaKernel R L).zero_mem
  · intro k v hv
    by_cases hk : p ≤ k
    · simp only [fromMode, if_pos hk]
      exact CVCrossRoot.f2_f1_commute_on R (by omega) hv
    · simp only [fromMode, if_neg hk, LinearMap.zero_apply, map_zero]
  · exact htheta

/-- All target first-root quadratic relations hold on the second generator
after quotienting by the first generator. -/
theorem second_kernel_first_quadratic (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j - 1) w = 0)
    (s : ℕ) (hs : 2 * (ν.1 + ϱ.1) + j - 1 ≤ s) :
    Q (R.op 3) 2 s (R.op 4 (ν.2 + ϱ.2 + j - 1) w) = 0 := by
  rw [CVKernelOther.Q_two_eq_QFrom (R.op 3) (CVRoots.sl2_first R).hFF
    (ν.1 + ϱ.1) (ν.1 + ϱ.1 + j - 1) s
    (second_kernel_first_trunc h hj hfirst) (by omega)]
  have hc := f2_QFrom_first R
    (L := (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j)
    (b := ν.2 + ϱ.2 + j - 1) (p := ν.1 + ϱ.1 + 1)
    (by omega) (theta_trunc h) 2 s
  rw [← hc, first_cutoff_in_quotient h hj hfirst s hs, map_zero]

end VOA.DeligneAudit.A2.CVKernelQuotient

#print axioms VOA.DeligneAudit.A2.CVKernelQuotient.second_kernel_theta_boundary
#print axioms VOA.DeligneAudit.A2.CVKernelQuotient.second_kernel_theta_trunc
#print axioms VOA.DeligneAudit.A2.CVKernelQuotient.second_kernel_first_trunc
#print axioms VOA.DeligneAudit.A2.CVKernelQuotient.second_kernel_first_quadratic
