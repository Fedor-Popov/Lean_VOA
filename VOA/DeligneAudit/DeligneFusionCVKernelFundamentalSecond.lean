import VOA.DeligneAudit.DeligneFusionCVKernelQuotient
import VOA.DeligneAudit.DeligneFusionCVKernelSimple
import VOA.DeligneAudit.DeligneFusionCVKernelGeneralHW
import VOA.DeligneAudit.DeligneFusionCVShort

/-!
# The second kernel relations in the fundamental-epsilon CV quotient

For epsilon `ω₁`, quotient by the first kernel generator `f₁(A+j)w`.
The second vector `f₂(B+j-1)w` satisfies the stronger highest-root cutoff
and first-root quadratic relations of the proposed smaller source.
Every relation follows from the actual auxiliary presentation and quotient
relation, without a dimension or target-presentation hypothesis.
-/

namespace VOA.DeligneAudit.A2.CVKernelFundamentalSecond

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.A2.CVFamily

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ν ϱ : Weight} {j : ℕ}

theorem source_theta_trunc (h : CV3Rel R w (1, 0) ν ϱ j) (q : ℕ)
    (hq : (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j + 1 ≤ q) : R.op 5 q w = 0 := by
  apply trunc_of_cvrel h.highest q
  rw [parts_length]
  omega

theorem source_second_cutoff (h : CV3Rel R w (1, 0) ν ϱ j) :
    QFrom (R.op 4) (ν.2 + ϱ.2) 2 (2 * (ν.2 + ϱ.2) + j - 1) w = 0 := by
  apply cvrel_cutoff (CVRoots.sl2_second R).hFF h.second
    (ν.2 + ϱ.2) 2 _ (by omega)
  have ht : T (ν.2 + ϱ.2) (parts ϱ.2 ν.2 (0 + j)) = j := by
    simpa only [Nat.zero_add, Nat.add_comm ν.2 ϱ.2] using parts_tail ϱ.2 ν.2 j
  rw [ht]
  omega

/-- The improved highest-root boundary relation in the quotient by the first
kernel vector, with all auxiliary indices retained. -/
theorem theta_boundary (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j) w = 0) :
    R.op 5 ((ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j)
      (R.op 4 (ν.2 + ϱ.2 + j - 1) w) = 0 := by
  let A := ν.1 + ϱ.1
  let B := ν.2 + ϱ.2
  let a := A + j
  let b := B + j - 1
  let q := A + B + j
  let v := R.op 4 b w
  let t2 := QFrom (R.op 4) (B + 1) 2 (2 * B + j - 1) w
  have hfirst' : R.op 3 a w = 0 := hfirst
  have htheta : ∀ m, q + 1 ≤ m → R.op 5 m w = 0 := source_theta_trunc h
  have hXv : R.op 3 a v = 0 := by
    have ht := htheta (a + b) (by dsimp [a, b, q]; omega)
    change R.op 3 a (R.op 4 b w) = 0
    rw [comm_apply 3 4]
    simp [Fin.sum_univ_eight, bracketTable, hfirst', ht]
  have htail : R.op 3 a t2 = 0 := by
    have hc := CVKernelOther.f1_QFrom_second R
      (L := q + 1) (a := a) (p := B + 1)
      (by dsimp [a, q]; omega) htheta 2 (2 * B + j - 1)
    change R.op 3 a (QFrom (R.op 4) (B + 1) 2 (2 * B + j - 1) w) = 0
    rw [hc, hfirst', map_zero]
  have hc2 : (2 : ℂ) • R.op 4 B v + t2 = 0 := by
    have he := congrArg (fun T : Module.End ℂ V => T w)
      (cutoff_split_two (CVRoots.sl2_second R).hFF B j hj)
    dsimp only at he
    rw [source_second_cutoff h] at he
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
      ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_ofNat] using he.symm
  have hcomm : R.op 3 a (R.op 4 B v) = -R.op 5 q v := by
    rw [comm_apply 3 4]
    simp [Fin.sum_univ_eight, bracketTable, hXv,
      show a + B = q by dsimp [a, q]; omega]
  have hneg : (2 : ℂ) • (-R.op 5 q v) = 0 := by
    have he := congrArg (fun x : V => R.op 3 a x) hc2
    simpa only [map_add, map_smul, map_zero, htail, add_zero, hcomm] using he
  exact neg_eq_zero.mp ((smul_eq_zero.mp hneg).resolve_left (by norm_num))

theorem theta_trunc (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j) w = 0)
    (q : ℕ) (hq : (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j ≤ q) :
    R.op 5 q (R.op 4 (ν.2 + ϱ.2 + j - 1) w) = 0 := by
  by_cases heq : q = (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j
  · subst q
    exact theta_boundary h hj hfirst
  · rw [← op4_op5, source_theta_trunc h q (by omega), map_zero]

theorem first_trunc (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j) w = 0)
    (q : ℕ) (hq : ν.1 + ϱ.1 + j ≤ q) :
    R.op 3 q (R.op 4 (ν.2 + ϱ.2 + j - 1) w) = 0 := by
  have hq0 : R.op 3 q w = 0 := by
    by_cases heq : q = ν.1 + ϱ.1 + j
    · simpa only [heq] using hfirst
    · apply trunc_of_cvrel h.first q
      rw [parts_length]
      omega
  have ht : R.op 5 (q + (ν.2 + ϱ.2 + j - 1)) w = 0 :=
    source_theta_trunc h _ (by omega)
  rw [comm_apply 3 4]
  simp [Fin.sum_univ_eight, bracketTable, hq0, ht]

theorem source_first_cutoff (h : CV3Rel R w (1, 0) ν ϱ j) :
    QFrom (R.op 3) (ν.1 + ϱ.1 + 1) 2
      (2 * (ν.1 + ϱ.1 + 1) + j - 1) w = 0 := by
  apply cvrel_cutoff (CVRoots.sl2_first R).hFF h.first
    (ν.1 + ϱ.1 + 1) 2 _ (by omega)
  have ht : T (ν.1 + ϱ.1 + 1) (parts ϱ.1 ν.1 (1 + j)) = j := by
    simp only [parts, T_append, T_replicate,
      List.length_append, List.length_replicate]
    omega
  rw [ht]
  omega

/-- The quotient relation kills the boundary cutoff tail; source CV kills
all the tails above that degree. -/
theorem first_cutoff_in_quotient (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j) w = 0)
    (s : ℕ) (hs : 2 * (ν.1 + ϱ.1) + j + 1 ≤ s) :
    QFrom (R.op 3) (ν.1 + ϱ.1 + 2) 2 s w = 0 := by
  let A := ν.1 + ϱ.1
  have hfirst' : R.op 3 (A + 1 + j - 1) w = 0 := by
    rw [show A + 1 + j - 1 = A + j by omega]
    exact hfirst
  by_cases heq : s = 2 * A + j + 1
  · subst s
    have he := congrArg (fun T : Module.End ℂ V => T w)
      (cutoff_split_two (CVRoots.sl2_first R).hFF (A + 1) j hj)
    dsimp only at he
    rw [source_first_cutoff h] at he
    have ht : QFrom (R.op 3) (A + 1 + 1) 2 (2 * (A + 1) + j - 1) w = 0 := by
      simpa only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
        hfirst', map_zero, smul_zero, zero_add] using he.symm
    simpa only [show A + 1 + 1 = A + 2 by omega,
      show 2 * (A + 1) + j - 1 = 2 * A + j + 1 by omega] using ht
  · apply cvrel_cutoff (CVRoots.sl2_first R).hFF h.first
      (ν.1 + ϱ.1 + 2) 2 s (by omega)
    have ht : T (ν.1 + ϱ.1 + 2) (parts ϱ.1 ν.1 (1 + j)) = j - 1 := by
      simp only [parts, T_append, T_replicate,
        List.length_append, List.length_replicate]
      omega
    rw [ht]
    dsimp only [A] at heq
    omega

/-- The complete target first-root quadratic region follows from source
relations and the actual first-generator quotient relation. -/
theorem first_quadratic (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j) w = 0)
    (s : ℕ) (hs : 2 * (ν.1 + ϱ.1) + j + 1 ≤ s) :
    Q (R.op 3) 2 s (R.op 4 (ν.2 + ϱ.2 + j - 1) w) = 0 := by
  rw [CVKernelOther.Q_two_eq_QFrom (R.op 3) (CVRoots.sl2_first R).hFF
    (ν.1 + ϱ.1 + 1) (ν.1 + ϱ.1 + j) s
    (first_trunc h hj hfirst) (by omega)]
  have hc := CVKernelQuotient.f2_QFrom_first R
    (L := (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j + 1)
    (b := ν.2 + ϱ.2 + j - 1) (p := ν.1 + ϱ.1 + 2)
    (by omega) (source_theta_trunc h) 2 s
  rw [show ν.1 + ϱ.1 + 1 + 1 = ν.1 + ϱ.1 + 2 by omega,
    ← hc, first_cutoff_in_quotient h hj hfirst s hs, map_zero]

/-- The same-root second CV partition loses its two final parts one. -/
theorem second_cv (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 2 ≤ j) :
    CVRel (R.op 4) (parts ϱ.2 ν.2 (j - 2))
      (R.op 4 (ν.2 + ϱ.2 + j - 1) w) := by
  have hs := cvrel_trailing_ones
    (List.replicate ϱ.2 3 ++ List.replicate ν.2 2) j hj (CVRoots.sl2_second R)
    (fun s => h.raising 1 (by decide) s)
    (fun p hp => h.cartan_pos 7 (by decide) p hp)
    (by simpa only [parts, Nat.zero_add] using h.second)
  simpa only [parts, List.length_append, List.length_replicate,
    Nat.add_comm ϱ.2 ν.2] using hs

private theorem raising (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 2 ≤ j)
    (e : Fin 8) (he : e.val < 3) (k : ℕ) :
    R.op e k (R.op 4 (ν.2 + ϱ.2 + j - 1) w) = 0 := by
  simpa only [Nat.add_zero] using
    CVKernelGeneralHW.second_raising h (by simpa only [Nat.zero_add] using hj) e he k

private theorem cartan_pos (h : CV3Rel R w (1, 0) ν ϱ j)
    (hh : Fin 8) (hhh : 6 ≤ hh.val) (k : ℕ) (hk : 1 ≤ k) :
    R.op hh k (R.op 4 (ν.2 + ϱ.2 + j - 1) w) = 0 := by
  simpa only [Nat.add_zero] using CVKernelGeneralHW.second_cartan_pos h hh hhh k hk

/-- The full strengthened first-root CV partition of the second quotient
generator in the fundamental-epsilon recurrence. -/
theorem first_cv (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j) w = 0) :
    CVRel (R.op 3) (parts ϱ.1 (ν.1 + 2) (j - 2))
      (R.op 4 (ν.2 + ϱ.2 + j - 1) w) := by
  apply cvrel_parts123 ϱ.1 (ν.1 + 2) (j - 2) (CVRoots.sl2_first R)
    (fun s => raising h hj 0 (by decide) s)
    (fun p hp => cartan_pos h 6 (by decide) p hp)
  · rw [Module.End.pow_apply]
    rw [show 3 * ϱ.1 + 2 * (ν.1 + 2) + (j - 2) + 1 =
      1 + 2 * ν.1 + 3 * ϱ.1 + j + 2 by omega]
    simpa only [Nat.add_zero] using CVKernelGeneralHW.second_lowering_first h
  · intro q hq
    exact first_trunc h hj hfirst q (by omega)
  · intro s hs
    exact first_quadratic h hj hfirst s (by omega)

/-- The improved theta cutoff and sharp nilpotence give every highest-root
CV relation of the smaller fundamental-epsilon quotient source. -/
theorem highest_cv (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j) w = 0) :
    CVRel (R.op 5) (parts (ϱ.1 + ϱ.2) (ν.1 + ν.2 + j) 0)
      (R.op 4 (ν.2 + ϱ.2 + j - 1) w) := by
  let L := (ϱ.1 + ϱ.2) + (ν.1 + ν.2 + j)
  have htr : ∀ q, L ≤ q →
      R.op 5 q (R.op 4 (ν.2 + ϱ.2 + j - 1) w) = 0 := by
    intro q hq
    exact theta_trunc h hj hfirst q (by dsimp [L] at hq; omega)
  apply cvrel_parts123 (ϱ.1 + ϱ.2) (ν.1 + ν.2 + j) 0 (CVRoots.sl2_highest R)
    (fun s => raising h hj 2 (by decide) s)
  · intro p hp
    simp only [LinearMap.add_apply, cartan_pos h 6 (by decide) p hp,
      cartan_pos h 7 (by decide) p hp, add_zero]
  · rw [Module.End.pow_apply]
    rw [show 3 * (ϱ.1 + ϱ.2) + 2 * (ν.1 + ν.2 + j) + 0 + 1 =
      1 + 0 + 2 * ν.1 + 3 * ϱ.1 + 2 * ν.2 + 3 * ϱ.2 + 2 * j by omega]
    simpa only [Nat.add_zero] using
      CVKernelGeneralHW.second_lowering_highest h (by simpa only [Nat.zero_add] using hj)
  · intro q hq
    exact htr q (by simpa only [Nat.add_zero] using hq)
  · intro s hs
    exact Q_high (CVRoots.sl2_highest R).hFF htr 2 s (by dsimp only [L]; omega)

/-- The second quotient generator satisfies the complete smaller source
presentation in the fundamental-epsilon recurrence. Every relation is derived
from the original CV presentation and the actual first-generator quotient. -/
theorem rel (h : CV3Rel R w (1, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j) w = 0) :
    CV3Rel R (R.op 4 (ν.2 + ϱ.2 + j - 1) w)
      (0, 0) (ν + (2, 0)) ϱ (j - 2) := by
  refine ⟨raising h hj, cartan_pos h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change R.op 6 0 _ = ((0 + 2 * (ν.1 + 2) + 3 * ϱ.1 + (j - 2) : ℕ) : ℂ) • _
    rw [show 0 + 2 * (ν.1 + 2) + 3 * ϱ.1 + (j - 2) =
      1 + 2 * ν.1 + 3 * ϱ.1 + j + 1 by omega]
    simpa only [Nat.add_zero] using CVKernelGeneralHW.second_cartan_first h
  · simpa only [Prod.snd_add, Nat.add_zero, Nat.zero_add] using
      CVKernelGeneralHW.second_cartan_second h (by simpa only [Nat.zero_add] using hj)
  · change (R.op 3 0)^[0 + 2 * (ν.1 + 2) + 3 * ϱ.1 + (j - 2) + 1] _ = 0
    rw [show 0 + 2 * (ν.1 + 2) + 3 * ϱ.1 + (j - 2) + 1 =
      1 + 2 * ν.1 + 3 * ϱ.1 + j + 2 by omega]
    simpa only [Nat.add_zero] using CVKernelGeneralHW.second_lowering_first h
  · simpa only [Prod.snd_add, Nat.add_zero, Nat.zero_add] using
      CVKernelGeneralHW.second_lowering_second h (by simpa only [Nat.zero_add] using hj)
  · simpa only [Prod.fst_add, Nat.zero_add] using first_cv h hj hfirst
  · simpa only [Prod.snd_add, Nat.add_zero, Nat.zero_add] using second_cv h hj
  · change CVRel (R.op 5) (parts (ϱ.1 + ϱ.2) ((ν.1 + 2) + (ν.2 + 0) + (j - 2))
      (0 + 0)) _
    rw [show (ν.1 + 2) + (ν.2 + 0) + (j - 2) = ν.1 + ν.2 + j by omega,
      Nat.zero_add]
    exact highest_cv h hj hfirst

end VOA.DeligneAudit.A2.CVKernelFundamentalSecond

#print axioms VOA.DeligneAudit.A2.CVKernelFundamentalSecond.theta_boundary
#print axioms VOA.DeligneAudit.A2.CVKernelFundamentalSecond.theta_trunc
#print axioms VOA.DeligneAudit.A2.CVKernelFundamentalSecond.first_trunc
#print axioms VOA.DeligneAudit.A2.CVKernelFundamentalSecond.first_quadratic
#print axioms VOA.DeligneAudit.A2.CVKernelFundamentalSecond.second_cv
#print axioms VOA.DeligneAudit.A2.CVKernelFundamentalSecond.first_cv
#print axioms VOA.DeligneAudit.A2.CVKernelFundamentalSecond.highest_cv
#print axioms VOA.DeligneAudit.A2.CVKernelFundamentalSecond.rel
