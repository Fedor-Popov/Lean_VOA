import VOA.DeligneAudit.DeligneFusionCVFamily
import VOA.DeligneAudit.DeligneFusionCVKernelSimple

/-!
# Highest-weight relations of the first auxiliary CV kernel generator

For the zero-epsilon SRK family, the vector `f₁(A+j-1) w` has the
highest weight of the smaller family with epsilon `ω₂`, second auxiliary
weight increased by `ω₂`, and adjoint count `j-2`. All highest-weight,
Cartan and zero-mode nilpotence statements below follow from the actual
source presentation. No target-presentation or dimension hypothesis is used.
-/

namespace VOA.DeligneAudit.A2.CVKernelHW

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.A2.CVFamily

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ν ϱ : Weight} {j : ℕ}

/-- The zero-mode power relation is already included in a full CV presentation. -/
theorem cvrel_zero_nil {F : ℕ → Module.End ℂ V} {ξ : List ℕ}
    (h : CVRel F ξ w) : (F 0 ^ (ξ.sum + 1)) w = 0 := by
  have hz := h (ξ.sum + 1) 0 0 (by omega)
    (by simp only [T, List.drop_zero, Nat.mul_zero, Nat.add_zero, Nat.zero_add]; omega)
  simpa only [Q_s_zero] using hz

/-- Total weight of the partition with parts 3, 2 and 1. -/
theorem parts_sum (r n e : ℕ) : (parts r n e).sum = 3 * r + 2 * n + e := by
  simp [parts]
  omega

/-- Every raising current kills the first kernel generator. -/
theorem first_raising (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j)
    (e : Fin 8) (he : e.val < 3) (k : ℕ) :
    R.op e k (R.op 3 (ν.1 + ϱ.1 + j - 1) w) = 0 := by
  rw [comm_apply, h.raising e he, map_zero, zero_add]
  have hpos : 1 ≤ k + (ν.1 + ϱ.1 + j - 1) := by omega
  have he' : e = 0 ∨ e = 1 ∨ e = 2 := by omega
  rcases he' with rfl | rfl | rfl
  · simp [Fin.sum_univ_eight, bracketTable, h.cartan_pos 6 (by decide) _ hpos]
  · simp [Fin.sum_univ_eight, bracketTable]
  · simp [Fin.sum_univ_eight, bracketTable, h.raising 1 (by decide)]

/-- Every positive Cartan current kills the first kernel generator. -/
theorem first_cartan_pos (h : CV3Rel R w (0, 0) ν ϱ j)
    (hh : Fin 8) (hhh : 6 ≤ hh.val) (k : ℕ) (hk : 1 ≤ k) :
    R.op hh k (R.op 3 (ν.1 + ϱ.1 + j - 1) w) = 0 := by
  rw [comm_apply, h.cartan_pos hh hhh k hk, map_zero, zero_add]
  have htr : R.op 3 (k + (ν.1 + ϱ.1 + j - 1)) w = 0 := by
    apply trunc_of_cvrel h.first
    simp only [parts_length, Nat.zero_add]
    omega
  have hh' : hh = 6 ∨ hh = 7 := by omega
  rcases hh' with rfl | rfl <;> simp [Fin.sum_univ_eight, bracketTable, htr]

/-- The first Cartan weight decreases by two. The displayed weight is natural. -/
theorem first_cartan_first (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j) :
    R.op 6 0 (R.op 3 (ν.1 + ϱ.1 + j - 1) w) =
      ((2 * ν.1 + 3 * ϱ.1 + (j - 2) : ℕ) : ℂ) •
        R.op 3 (ν.1 + ϱ.1 + j - 1) w := by
  rw [comm_apply, h.cartan_first, map_smul]
  simp only [zero_add]
  simp [Fin.sum_univ_eight, bracketTable]
  rw [Nat.cast_sub hj, Nat.cast_ofNat]
  module

/-- The second Cartan weight increases by one. -/
theorem first_cartan_second (h : CV3Rel R w (0, 0) ν ϱ j) :
    R.op 7 0 (R.op 3 (ν.1 + ϱ.1 + j - 1) w) =
      ((2 * ν.2 + 3 * ϱ.2 + j + 1 : ℕ) : ℂ) •
        R.op 3 (ν.1 + ϱ.1 + j - 1) w := by
  rw [comm_apply, h.cartan_second, map_smul]
  simp [Fin.sum_univ_eight, bracketTable]
  module

/-- The full first-root CV relations of the smaller source, before any dimension estimate. -/
theorem first_same_root (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j) :
    CVRel (R.op 3) (parts ϱ.1 ν.1 (j - 2))
      (R.op 3 (ν.1 + ϱ.1 + j - 1) w) := by
  have hs := cvrel_trailing_ones
    (List.replicate ϱ.1 3 ++ List.replicate ν.1 2) j hj (CVRoots.sl2_first R)
    (fun s => h.raising 0 (by decide) s)
    (fun p hp => h.cartan_pos 6 (by decide) p hp)
    (by simpa only [parts, Prod.fst_zero, Nat.zero_add] using h.first)
  simpa only [parts, List.length_append, List.length_replicate,
    Nat.add_comm ϱ.1 ν.1] using hs

/-- The first zero-mode power is sharp at the smaller highest weight. -/
theorem first_lowering_first (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j) :
    (R.op 3 0)^[2 * ν.1 + 3 * ϱ.1 + (j - 2) + 1]
      (R.op 3 (ν.1 + ϱ.1 + j - 1) w) = 0 := by
  have hn := cvrel_zero_nil (first_same_root h hj)
  rw [parts_sum, Module.End.pow_apply] at hn
  convert hn using 1
  congr 2
  omega

/-- A central Heisenberg commutator gives the second zero-mode power bound. -/
theorem first_lowering_second (h : CV3Rel R w (0, 0) ν ϱ j) :
    (R.op 4 0)^[2 * ν.2 + 3 * ϱ.2 + j + 2]
      (R.op 3 (ν.1 + ϱ.1 + j - 1) w) = 0 := by
  let a := ν.1 + ϱ.1 + j - 1
  have hXY : R.op 3 a * R.op 4 0 - R.op 4 0 * R.op 3 a = -R.op 5 a := by
    rw [op_comm_end]
    simp [Fin.sum_univ_eight, bracketTable]
  have hYZ : R.op 4 0 * (-R.op 5 a) = (-R.op 5 a) * R.op 4 0 := by
    simp only [mul_neg, neg_mul, neg_inj]
    ext x
    exact op4_op5 0 a x
  have hn : (R.op 4 0 ^ (2 * ν.2 + 3 * ϱ.2 + j + 1)) w = 0 := by
    rw [Module.End.pow_apply]
    simpa only [Prod.snd_zero, Nat.zero_add] using h.lowering_second
  have hz := Garland.Ypow_Xpow_apply hXY hYZ hn 1
  simpa only [pow_one, Module.End.pow_apply, Nat.add_assoc, Nat.reduceAdd, a] using hz

/-- The highest-root zero mode has its sharp nilpotence degree on the first kernel vector. -/
theorem first_lowering_highest (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j) :
    (R.op 5 0)^[2 * ν.1 + 3 * ϱ.1 + 2 * ν.2 + 3 * ϱ.2 + 2 * j]
      (R.op 3 (ν.1 + ϱ.1 + j - 1) w) = 0 := by
  let u := R.op 3 (ν.1 + ϱ.1 + j - 1) w
  let l₁ := 2 * ν.1 + 3 * ϱ.1 + (j - 2)
  let l₂ := 2 * ν.2 + 3 * ϱ.2 + j + 1
  let H := R.op 6 0 + R.op 7 0
  have hE : R.op 2 0 u = 0 := first_raising h hj 2 (by decide) 0
  have hH : H u = (((l₁ + l₂ : ℕ) : ℤ) : ℂ) • u := by
    dsimp only [H, u]
    rw [LinearMap.add_apply, first_cartan_first h hj, first_cartan_second h]
    dsimp only [l₁, l₂]
    push_cast
    module
  have hEF : ∀ x, R.op 2 0 (R.op 5 0 x) - R.op 5 0 (R.op 2 0 x) = H x := by
    intro x
    have hc := congrArg (fun T : Module.End ℂ V => T x) ((CVRoots.sl2_highest R).hEF 0 0)
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, Nat.zero_add] using hc
  have hHF : ∀ x, H (R.op 5 0 x) - R.op 5 0 (H x) = (-2 : ℂ) • R.op 5 0 x := by
    intro x
    have hc := congrArg (fun T : Module.End ℂ V => T x) ((CVRoots.sl2_highest R).hHF 0 0)
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.mul_apply, Nat.zero_add] using hc
  have hn : (R.op 5 0)^[
      2 * ν.1 + 3 * ϱ.1 + 2 * ν.2 + 3 * ϱ.2 + 2 * j + 1] u = 0 := by
    have hc : Commute (R.op 5 0) (R.op 3 (ν.1 + ϱ.1 + j - 1)) := by
      ext x
      exact (op3_op5 (ν.1 + ϱ.1 + j - 1) 0 x).symm
    have hnil := cvrel_zero_nil h.highest
    rw [parts_sum] at hnil
    change (R.op 5 0 ^
      (3 * (ϱ.1 + ϱ.2) + 2 * (ν.1 + ν.2 + j) + (0 + 0) + 1)) w = 0 at hnil
    have he : 3 * (ϱ.1 + ϱ.2) + 2 * (ν.1 + ν.2 + j) + (0 + 0) + 1 =
        2 * ν.1 + 3 * ϱ.1 + 2 * ν.2 + 3 * ϱ.2 + 2 * j + 1 := by omega
    rw [he] at hnil
    rw [← Module.End.pow_apply]
    dsimp only [u]
    rw [← Module.End.mul_apply, (hc.pow_left _).eq,
      Module.End.mul_apply, hnil, map_zero]
  have hs := (CLFilt.hw_pow (R.op 2 0) (R.op 5 0) H hEF hHF hE hH _ hn).2
    (by positivity)
  have he : l₁ + l₂ + 1 =
      2 * ν.1 + 3 * ϱ.1 + 2 * ν.2 + 3 * ϱ.2 + 2 * j := by
    dsimp only [l₁, l₂]
    omega
  simpa only [Int.toNat_natCast, he] using hs

end

end VOA.DeligneAudit.A2.CVKernelHW

#print axioms VOA.DeligneAudit.A2.CVKernelHW.first_same_root
#print axioms VOA.DeligneAudit.A2.CVKernelHW.first_raising
#print axioms VOA.DeligneAudit.A2.CVKernelHW.first_cartan_pos
#print axioms VOA.DeligneAudit.A2.CVKernelHW.first_cartan_first
#print axioms VOA.DeligneAudit.A2.CVKernelHW.first_cartan_second
#print axioms VOA.DeligneAudit.A2.CVKernelHW.first_lowering_first
#print axioms VOA.DeligneAudit.A2.CVKernelHW.first_lowering_second
#print axioms VOA.DeligneAudit.A2.CVKernelHW.first_lowering_highest
