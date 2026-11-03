import VOA.DeligneAudit.DeligneFusionCVKernelGeneralHW
import VOA.DeligneAudit.DeligneFusionCVShort
import VOA.DeligneAudit.DeligneFusionCVTransport

/-!
# The zero-epsilon one-adjoint CV base with a rectangular factor

The assumption `0 < ν₁` lets the last part two interact with the final part
one. The kernel and quotient presentations have the weights specified by
the one-adjoint recurrence. No dimension bound or fusion model is assumed.
-/

namespace VOA.DeligneAudit.CVsl2

open VOA.DeligneAudit.CVPart

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V} {w : V}

/-- The minus-side CV relations when the final part is one and the preceding
equal parts have arbitrary positive size. No dimension hypothesis is used. -/
theorem cvrel_kernel_final_one (μ : List ℕ) (c a : ℕ) (ha : 1 ≤ a)
    (hS : SL2 E H F) (hE : ∀ s, E s w = 0)
    (hH : ∀ p, 1 ≤ p → H p w = 0) (hR : CVRel F (P μ c a 1) w) :
    CVRel F (Pm μ c a 1) (F (μ.length + c + 1) w) := by
  let L1 := μ.length + c + 1
  have hFhigh : ∀ q, L1 + 1 ≤ q → F q w = 0 := by
    intro q hq
    have hz := hR 1 q (μ.length + c + 2) le_rfl
      (by rw [T_P_high μ c a 1 _ le_rfl]; dsimp [L1] at hq; omega)
    rwa [Q_one] at hz
  obtain ⟨hE', hH', hF'⟩ :=
    hw_Fb hS.hEF hS.hHF hS.hFF (b := L1) (by dsimp [L1]; omega) hE hH hFhigh
  have hL : ∀ q, μ.length + c + 2 ≤ q → F q w = 0 :=
    fun q hq => hFhigh q (by dsimp [L1]; omega)
  have hL' : ∀ q, μ.length + c + 2 ≤ q → F q (F L1 w) = 0 :=
    fun q hq => hF' q (by dsimp [L1]; omega)
  have e1 : μ.length + c + 2 - 1 = L1 := by simp [L1]
  have e2 : μ.length + c + 2 - 2 = μ.length + c := by omega
  have htop : (F L1 ^ 2) w = 0 := by
    have ht := Q_top hS.hFF hL 2
    rw [e1] at ht
    rw [← ht]
    refine hR 2 _ L1 (by omega) ?_
    change 1 + 2 * (μ.length + c + 1) + T (μ.length + c + 1) (P μ c a 1) ≤ _
    rw [show μ.length + c + 1 = μ.length + (c + 1) by omega,
      T_P_mid μ c a 1 (c + 1) le_rfl]
    simp only [Nat.sub_self, Nat.zero_mul, zero_add]
    omega
  intro r s k hr h
  change Q F r s (F L1 w) = 0
  by_cases hk : k ≤ μ.length + c
  · have hT := (T_minus μ c a (b := 1) ha k).1 hk
    have hX := shift_iter hS.hEF hS.hHF hS.hHE hS.hFF hS.hEE
      k (T k (P μ c a 1)) L1 (by dsimp [L1]; omega) 1 w hE hH hFhigh
      (fun r s hr h => X_zero_of_Q hS.hEF hS.hHF hS.hFF hE hH hr (hR r s k hr h))
      r s hr (by omega)
    simp only [pow_one] at hX
    exact Q_zero_of_X hS.hEF hS.hHF hS.hFF hE' hH' hr hX
  · have hT := (T_minus μ c a (b := 1) ha k).2 (by omega)
    have hrk : r * (μ.length + c + 1) ≤ r * k :=
      Nat.mul_le_mul_left r (by omega)
    have hmem := Q_div hS.hFF hL' r 1 s (by rw [e2]; nlinarith)
    rw [e1, pow_one, ← Module.End.mul_apply, ← pow_two, htop, Fspan_zero] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem

end VOA.DeligneAudit.CVsl2

namespace VOA.DeligneAudit.A2.CVBaseOne

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.A2.CVFamily

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Two square-nilpotent Heisenberg directions force the central square to
kill the first descendant. This is a direct operator identity consequence. -/
theorem central_square_descendant {X Y Z : Module.End ℂ V} {w : V}
    (hXY : X * Y - Y * X = Z) (hXZ : X * Z = Z * X) (hYZ : Y * Z = Z * Y)
    (hX2 : (X ^ 2) w = 0) (hY2 : (Y ^ 2) w = 0) : (Z ^ 2) (X w) = 0 := by
  have hYX : Y * X - X * Y = -Z := by rw [← hXY]; noncomm_ring
  have hXZ' : X * (-Z) = (-Z) * X := by
    simpa only [mul_neg, neg_mul] using congrArg Neg.neg hXZ
  have hYZ' : Y * (-Z) = (-Z) * Y := by
    simpa only [mul_neg, neg_mul] using congrArg Neg.neg hYZ
  have hX3 : (X ^ 3) w = 0 := by
    rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ', Module.End.mul_apply, hX2, map_zero]
  have hX3Y : (X ^ 3) (Y w) = 0 := by
    simpa only [Nat.reduceAdd, pow_one] using Garland.Ypow_Xpow_apply hYX hXZ' hX2 1
  have hY2' : Y (Y w) = 0 := by simpa only [pow_two, Module.End.mul_apply] using hY2
  have had : (Garland.adX Y (Garland.adX Y (X ^ 3))) w = 0 := by
    simp only [Garland.adX, LinearMap.sub_apply, Module.End.mul_apply,
      hX3, hX3Y, hY2', map_zero, sub_self]
  have hf : Garland.adX Y (Garland.adX Y (X ^ 3)) = 6 • (Z ^ 2 * X) := by
    have he := Garland.iterate_adX_pow hYX hXZ' hYZ' 2 1
    norm_num [Function.iterate_succ_apply', Function.iterate_zero_apply,
      Nat.descFactorial, neg_sq] at he
    exact he
  have he := congrArg (fun T : Module.End ℂ V => T w) hf
  dsimp only at he
  rw [had] at he
  have hz : (6 : ℕ) • (Z ^ 2) (X w) = 0 := by
    simpa only [LinearMap.smul_apply, Module.End.mul_apply] using he.symm
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at hz
  exact hz.resolve_left (by norm_num)

variable {R : CurrentModule bracketTable V} {w : V} {ν ϱ : Weight}

private theorem first_square (h : CV3Rel R w (0, 0) ν ϱ 1) :
    (R.op 3 (ν.1 + ϱ.1) ^ 2) w = 0 := by
  simpa only [Nat.add_sub_cancel_right, Nat.add_comm ϱ.1 ν.1] using
    top_square_of_cvrel (r := ϱ.1) (n := ν.1) (j := 1)
      (CVRoots.sl2_first R).hFF le_rfl h.first

private theorem second_square (h : CV3Rel R w (0, 0) ν ϱ 1) :
    (R.op 4 (ν.2 + ϱ.2) ^ 2) w = 0 := by
  simpa only [Nat.add_sub_cancel_right, Nat.add_comm ϱ.2 ν.2] using
    top_square_of_cvrel (r := ϱ.2) (n := ν.2) (j := 1)
      (CVRoots.sl2_second R).hFF le_rfl h.second

/-- The highest-root top square kills the kernel vector in the one-adjoint base. -/
theorem kernel_theta_square (h : CV3Rel R w (0, 0) ν ϱ 1) :
    (R.op 5 ((ν.1 + ϱ.1) + (ν.2 + ϱ.2)) ^ 2)
      (R.op 3 (ν.1 + ϱ.1) w) = 0 := by
  let X := R.op 3 (ν.1 + ϱ.1)
  let Y := R.op 4 (ν.2 + ϱ.2)
  let Z := R.op 5 ((ν.1 + ϱ.1) + (ν.2 + ϱ.2))
  have hXY : X * Y - Y * X = -Z := by
    rw [op_comm_end]
    simp [Fin.sum_univ_eight, bracketTable, Z]
  have hXZ : X * (-Z) = (-Z) * X := by
    have hc : X * Z = Z * X := by ext v; exact op3_op5 _ _ v
    simpa only [mul_neg, neg_mul] using congrArg Neg.neg hc
  have hYZ : Y * (-Z) = (-Z) * Y := by
    have hc : Y * Z = Z * Y := by ext v; exact op4_op5 _ _ v
    simpa only [mul_neg, neg_mul] using congrArg Neg.neg hc
  simpa only [neg_sq] using
    central_square_descendant hXY hXZ hYZ (first_square h) (second_square h)

/-- In the quotient by the kernel generator, the same top square kills `w`. -/
theorem quotient_theta_square (h : CV3Rel R w (0, 0) ν ϱ 1)
    (htop : R.op 3 (ν.1 + ϱ.1) w = 0) :
    (R.op 5 ((ν.1 + ϱ.1) + (ν.2 + ϱ.2)) ^ 2) w = 0 := by
  let X := R.op 3 (ν.1 + ϱ.1)
  let Y := R.op 4 (ν.2 + ϱ.2)
  let Z := R.op 5 ((ν.1 + ϱ.1) + (ν.2 + ϱ.2))
  have hXY : X * Y - Y * X = -Z := by
    rw [op_comm_end]
    simp [Fin.sum_univ_eight, bracketTable, Z]
  have hXZ : X * (-Z) = (-Z) * X := by
    have hc : X * Z = Z * X := by ext v; exact op3_op5 _ _ v
    simpa only [mul_neg, neg_mul] using congrArg Neg.neg hc
  have hXw : X w = 0 := htop
  have hz := VOA.DeligneAudit.CVTransport.square_kill_of_commutator X Y (-Z) hXY hXZ w
    (second_square h) (by rw [hXw, map_zero])
    (by simp only [pow_two, Module.End.mul_apply, hXw, map_zero])
  simpa only [neg_sq] using hz

theorem quotient_first_trunc (h : CV3Rel R w (0, 0) ν ϱ 1)
    (htop : R.op 3 (ν.1 + ϱ.1) w = 0) (q : ℕ) (hq : ν.1 + ϱ.1 ≤ q) :
    R.op 3 q w = 0 := by
  by_cases heq : q = ν.1 + ϱ.1
  · simpa only [heq] using htop
  · apply trunc_of_cvrel h.first q
    rw [parts_length]
    omega

/-- The quotient has the first-root rectangular presentation: the sole new
linear mode makes every quadratic coefficient automatic. -/
theorem quotient_first_cv (h : CV3Rel R w (0, 0) ν ϱ 1) (hν : 0 < ν.1)
    (htop : R.op 3 (ν.1 + ϱ.1) w = 0) :
    CVRel (R.op 3) (parts (ϱ.1 + 1) (ν.1 - 1) 0) w := by
  have htr := quotient_first_trunc h htop
  apply cvrel_parts123 (ϱ.1 + 1) (ν.1 - 1) 0 (CVRoots.sl2_first R)
    (fun s => h.raising 0 (by decide) s)
    (fun p hp => h.cartan_pos 6 (by decide) p hp)
  · rw [Module.End.pow_apply]
    rw [show 3 * (ϱ.1 + 1) + 2 * (ν.1 - 1) + 0 + 1 =
      0 + 2 * ν.1 + 3 * ϱ.1 + 1 + 1 by omega]
    exact h.lowering_first
  · intro q hq
    exact htr q (by omega)
  · intro s hs
    exact Q_high (CVRoots.sl2_first R).hFF htr 2 s (by omega)

/-- The quotient's highest-root partition follows from the new central
square, the unchanged linear cutoff, and the unchanged total weight. -/
theorem quotient_highest_cv (h : CV3Rel R w (0, 0) ν ϱ 1) (hν : 0 < ν.1)
    (htop : R.op 3 (ν.1 + ϱ.1) w = 0) :
    CVRel (R.op 5) (parts ((ϱ.1 + 1) + ϱ.2) ((ν.1 - 1) + ν.2) 1) w := by
  apply cvrel_parts32_one ((ϱ.1 + 1) + ϱ.2) ((ν.1 - 1) + ν.2)
    (CVRoots.sl2_highest R) (fun s => h.raising 2 (by decide) s)
  · intro p hp
    simp only [LinearMap.add_apply, h.cartan_pos 6 (by decide) p hp,
      h.cartan_pos 7 (by decide) p hp, add_zero]
  · have hn := CVKernelHW.cvrel_zero_nil h.highest
    rw [CVKernelHW.parts_sum] at hn
    rw [show 3 * ((ϱ.1 + 1) + ϱ.2) + 2 * ((ν.1 - 1) + ν.2) + 2 =
      3 * (ϱ.1 + ϱ.2) + 2 * (ν.1 + ν.2 + 1) + (0 + 0) + 1 by omega]
    exact hn
  · intro q hq
    exact CVFamily.theta_trunc h q (by omega)
  · rw [show (ϱ.1 + 1) + ϱ.2 + ((ν.1 - 1) + ν.2) =
      (ν.1 + ϱ.1) + (ν.2 + ϱ.2) by omega]
    exact quotient_theta_square h htop

/-- The actual zero-epsilon one-adjoint quotient source when `ν₁ > 0`.
The source highest weights are unchanged; every target CV relation is derived. -/
theorem quotient_rel (h : CV3Rel R w (0, 0) ν ϱ 1) (hν : 0 < ν.1)
    (htop : R.op 3 (ν.1 + ϱ.1) w = 0) :
    CV3Rel R w (0, 1) (ν - (1, 0)) (ϱ + (1, 0)) 0 := by
  refine ⟨h.raising, h.cartan_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change R.op 6 0 w = ((0 + 2 * (ν.1 - 1) + 3 * (ϱ.1 + 1) + 0 : ℕ) : ℂ) • w
    rw [show 0 + 2 * (ν.1 - 1) + 3 * (ϱ.1 + 1) + 0 =
      0 + 2 * ν.1 + 3 * ϱ.1 + 1 by omega]
    exact h.cartan_first
  · change R.op 7 0 w = ((1 + 2 * ν.2 + 3 * ϱ.2 + 0 : ℕ) : ℂ) • w
    rw [show 1 + 2 * ν.2 + 3 * ϱ.2 + 0 = 0 + 2 * ν.2 + 3 * ϱ.2 + 1 by omega]
    exact h.cartan_second
  · change (R.op 3 0)^[0 + 2 * (ν.1 - 1) + 3 * (ϱ.1 + 1) + 0 + 1] w = 0
    rw [show 0 + 2 * (ν.1 - 1) + 3 * (ϱ.1 + 1) + 0 + 1 =
      0 + 2 * ν.1 + 3 * ϱ.1 + 1 + 1 by omega]
    exact h.lowering_first
  · change (R.op 4 0)^[1 + 2 * ν.2 + 3 * ϱ.2 + 0 + 1] w = 0
    rw [show 1 + 2 * ν.2 + 3 * ϱ.2 + 0 + 1 = 0 + 2 * ν.2 + 3 * ϱ.2 + 1 + 1 by omega]
    exact h.lowering_second
  · change CVRel (R.op 3) (parts (ϱ.1 + 1) (ν.1 - 1) (0 + 0)) w
    exact quotient_first_cv h hν htop
  · change CVRel (R.op 4) (parts ϱ.2 ν.2 (1 + 0)) w
    exact h.second
  · change CVRel (R.op 5) (parts ((ϱ.1 + 1) + ϱ.2) ((ν.1 - 1) + ν.2 + 0) (0 + 1)) w
    exact quotient_highest_cv h hν htop

/-- The `a=2,b=1` CV minus partition gives the kernel's actual first-root relations. -/
theorem kernel_first_cv (h : CV3Rel R w (0, 0) ν ϱ 1) (hν : 0 < ν.1) :
    CVRel (R.op 3) (parts ϱ.1 (ν.1 - 1) 1) (R.op 3 (ν.1 + ϱ.1) w) := by
  have hp : P (List.replicate ϱ.1 3) (ν.1 - 1) 2 1 = parts ϱ.1 ν.1 1 := by
    simp only [P, parts, List.replicate_one, show ν.1 - 1 + 1 = ν.1 by omega,
      List.append_assoc]
  have hs := cvrel_kernel_final_one (List.replicate ϱ.1 3) (ν.1 - 1) 2 (by omega)
    (CVRoots.sl2_first R) (fun s => h.raising 0 (by decide) s)
    (fun p hp => h.cartan_pos 6 (by decide) p hp)
    (by rw [hp]; exact h.first)
  simp only [List.length_replicate] at hs
  rw [show ϱ.1 + (ν.1 - 1) + 1 = ν.1 + ϱ.1 by omega] at hs
  simpa [Pm, parts] using hs

theorem kernel_raising (h : CV3Rel R w (0, 0) ν ϱ 1) (hν : 0 < ν.1)
    (e : Fin 8) (he : e.val < 3) (k : ℕ) :
    R.op e k (R.op 3 (ν.1 + ϱ.1) w) = 0 := by
  rw [comm_apply, h.raising e he, map_zero, zero_add]
  have hpos : 1 ≤ k + (ν.1 + ϱ.1) := by omega
  have he' : e = 0 ∨ e = 1 ∨ e = 2 := by omega
  rcases he' with rfl | rfl | rfl
  · simp [Fin.sum_univ_eight, bracketTable, h.cartan_pos 6 (by decide) _ hpos]
  · simp [Fin.sum_univ_eight, bracketTable]
  · simp [Fin.sum_univ_eight, bracketTable, h.raising 1 (by decide)]

theorem kernel_cartan_pos (h : CV3Rel R w (0, 0) ν ϱ 1)
    (hh : Fin 8) (hhh : 6 ≤ hh.val) (k : ℕ) (hk : 1 ≤ k) :
    R.op hh k (R.op 3 (ν.1 + ϱ.1) w) = 0 := by
  simpa only [Nat.add_zero, Nat.add_sub_cancel_right] using
    CVKernelGeneralHW.first_cartan_pos h hh hhh k hk

theorem kernel_cartan_first (h : CV3Rel R w (0, 0) ν ϱ 1) (hν : 0 < ν.1) :
    R.op 6 0 (R.op 3 (ν.1 + ϱ.1) w) =
      ((1 + 2 * (ν.1 - 1) + 3 * ϱ.1 : ℕ) : ℂ) • R.op 3 (ν.1 + ϱ.1) w := by
  rw [show 1 + 2 * (ν.1 - 1) + 3 * ϱ.1 = (2 * ν.1 + 3 * ϱ.1 + 1) - 2 by omega]
  rw [comm_apply, h.cartan_first, map_smul]
  simp only [zero_add]
  simp [Fin.sum_univ_eight, bracketTable]
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * ν.1 + 3 * ϱ.1), Nat.cast_one]
  push_cast
  module

theorem kernel_cartan_second (h : CV3Rel R w (0, 0) ν ϱ 1) :
    R.op 7 0 (R.op 3 (ν.1 + ϱ.1) w) =
      ((2 * (ν.2 + 1) + 3 * ϱ.2 : ℕ) : ℂ) • R.op 3 (ν.1 + ϱ.1) w := by
  have hc := CVKernelGeneralHW.first_cartan_second h
  simp only [Nat.add_zero, Nat.zero_add, Nat.add_sub_cancel_right] at hc
  rw [show 2 * ν.2 + 3 * ϱ.2 + 1 + 1 = 2 * (ν.2 + 1) + 3 * ϱ.2 by omega] at hc
  exact hc

theorem kernel_lowering_first (h : CV3Rel R w (0, 0) ν ϱ 1) (hν : 0 < ν.1) :
    (R.op 3 0)^[1 + 2 * (ν.1 - 1) + 3 * ϱ.1 + 1]
      (R.op 3 (ν.1 + ϱ.1) w) = 0 := by
  have hn := CVKernelHW.cvrel_zero_nil (kernel_first_cv h hν)
  rw [CVKernelHW.parts_sum, Module.End.pow_apply] at hn
  rw [show 1 + 2 * (ν.1 - 1) + 3 * ϱ.1 + 1 = 3 * ϱ.1 + 2 * (ν.1 - 1) + 1 + 1 by omega]
  exact hn

theorem kernel_lowering_second (h : CV3Rel R w (0, 0) ν ϱ 1) :
    (R.op 4 0)^[2 * (ν.2 + 1) + 3 * ϱ.2 + 1]
      (R.op 3 (ν.1 + ϱ.1) w) = 0 := by
  have hn := CVKernelGeneralHW.first_lowering_second h
  simp only [Nat.add_zero, Nat.zero_add, Nat.add_sub_cancel_right] at hn
  rw [show 2 * (ν.2 + 1) + 3 * ϱ.2 + 1 = 2 * ν.2 + 3 * ϱ.2 + 1 + 2 by omega]
  exact hn

/-- The theta zero mode has the sharp nilpotence degree at the actual kernel weight. -/
theorem kernel_lowering_highest (h : CV3Rel R w (0, 0) ν ϱ 1) (hν : 0 < ν.1) :
    (R.op 5 0)^[3 * (ϱ.1 + ϱ.2) + 2 * (ν.1 + ν.2) + 2]
      (R.op 3 (ν.1 + ϱ.1) w) = 0 := by
  let u := R.op 3 (ν.1 + ϱ.1) w
  let l₁ := 1 + 2 * (ν.1 - 1) + 3 * ϱ.1
  let l₂ := 2 * (ν.2 + 1) + 3 * ϱ.2
  let H := R.op 6 0 + R.op 7 0
  have hE : R.op 2 0 u = 0 := kernel_raising h hν 2 (by decide) 0
  have hH : H u = (((l₁ + l₂ : ℕ) : ℤ) : ℂ) • u := by
    dsimp only [H, u]
    rw [LinearMap.add_apply, kernel_cartan_first h hν, kernel_cartan_second h]
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
  have hn : (R.op 5 0)^[3 * (ϱ.1 + ϱ.2) + 2 * (ν.1 + ν.2 + 1) + 1] u = 0 := by
    have hc : Commute (R.op 5 0) (R.op 3 (ν.1 + ϱ.1)) := by
      ext x
      exact (op3_op5 (ν.1 + ϱ.1) 0 x).symm
    have hnil := CVKernelHW.cvrel_zero_nil h.highest
    rw [CVKernelHW.parts_sum] at hnil
    rw [← Module.End.pow_apply]
    dsimp only [u]
    rw [← Module.End.mul_apply, (hc.pow_left _).eq, Module.End.mul_apply]
    have hnil' : (R.op 5 0 ^ (3 * (ϱ.1 + ϱ.2) + 2 * (ν.1 + ν.2 + 1) + 1)) w = 0 := by
      simpa only [Nat.add_zero] using hnil
    rw [hnil', map_zero]
  have hs := (CLFilt.hw_pow (R.op 2 0) (R.op 5 0) H hEF hHF hE hH _ hn).2
    (by positivity)
  have he : l₁ + l₂ + 1 = 3 * (ϱ.1 + ϱ.2) + 2 * (ν.1 + ν.2) + 2 := by
    dsimp only [l₁, l₂]
    omega
  simpa only [Int.toNat_natCast, he] using hs

theorem kernel_second_trunc (h : CV3Rel R w (0, 0) ν ϱ 1)
    (q : ℕ) (hq : ν.2 + ϱ.2 + 1 ≤ q) :
    R.op 4 q (R.op 3 (ν.1 + ϱ.1) w) = 0 := by
  have hq0 : R.op 4 q w = 0 := by
    apply trunc_of_cvrel h.second q
    rw [parts_length]
    omega
  have ht : R.op 5 (q + (ν.1 + ϱ.1)) w = 0 := CVFamily.theta_trunc h _ (by omega)
  rw [comm_apply 4 3]
  simp [Fin.sum_univ_eight, bracketTable, hq0, ht]

theorem kernel_second_cv (h : CV3Rel R w (0, 0) ν ϱ 1) (hν : 0 < ν.1) :
    CVRel (R.op 4) (parts ϱ.2 (ν.2 + 1) 0) (R.op 3 (ν.1 + ϱ.1) w) := by
  have htr := kernel_second_trunc h
  apply cvrel_parts123 ϱ.2 (ν.2 + 1) 0 (CVRoots.sl2_second R)
    (fun s => kernel_raising h hν 1 (by decide) s)
    (fun p hp => kernel_cartan_pos h 7 (by decide) p hp)
  · rw [Module.End.pow_apply]
    rw [show 3 * ϱ.2 + 2 * (ν.2 + 1) + 0 + 1 = 2 * (ν.2 + 1) + 3 * ϱ.2 + 1 by omega]
    exact kernel_lowering_second h
  · intro q hq
    exact htr q (by omega)
  · intro s hs
    exact Q_high (CVRoots.sl2_second R).hFF htr 2 s (by omega)

theorem kernel_highest_cv (h : CV3Rel R w (0, 0) ν ϱ 1) (hν : 0 < ν.1) :
    CVRel (R.op 5) (parts (ϱ.1 + ϱ.2) (ν.1 + ν.2) 1)
      (R.op 3 (ν.1 + ϱ.1) w) := by
  apply cvrel_parts32_one (ϱ.1 + ϱ.2) (ν.1 + ν.2) (CVRoots.sl2_highest R)
    (fun s => kernel_raising h hν 2 (by decide) s)
  · intro p hp
    simp only [LinearMap.add_apply, kernel_cartan_pos h 6 (by decide) p hp,
      kernel_cartan_pos h 7 (by decide) p hp, add_zero]
  · rw [Module.End.pow_apply]
    exact kernel_lowering_highest h hν
  · intro q hq
    rw [← op3_op5, CVFamily.theta_trunc h q (by omega), map_zero]
  · rw [show ϱ.1 + ϱ.2 + (ν.1 + ν.2) = (ν.1 + ϱ.1) + (ν.2 + ϱ.2) by omega]
    exact kernel_theta_square h

/-- The complete actual kernel source in the one-adjoint base with `ν₁ > 0`. -/
theorem kernel_rel (h : CV3Rel R w (0, 0) ν ϱ 1) (hν : 0 < ν.1) :
    CV3Rel R (R.op 3 (ν.1 + ϱ.1) w)
      (1, 0) (ν - (1, 0) + (0, 1)) ϱ 0 := by
  refine ⟨kernel_raising h hν, kernel_cartan_pos h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change R.op 6 0 _ = ((1 + 2 * (ν.1 - 1) + 3 * ϱ.1 + 0 : ℕ) : ℂ) • _
    simpa only [Nat.add_zero] using kernel_cartan_first h hν
  · change R.op 7 0 _ = ((0 + 2 * (ν.2 + 1) + 3 * ϱ.2 + 0 : ℕ) : ℂ) • _
    simpa only [Nat.add_zero, Nat.zero_add] using kernel_cartan_second h
  · change (R.op 3 0)^[1 + 2 * (ν.1 - 1) + 3 * ϱ.1 + 0 + 1] _ = 0
    simpa only [Nat.add_zero] using kernel_lowering_first h hν
  · change (R.op 4 0)^[0 + 2 * (ν.2 + 1) + 3 * ϱ.2 + 0 + 1] _ = 0
    simpa only [Nat.add_zero, Nat.zero_add] using kernel_lowering_second h
  · change CVRel (R.op 3) (parts ϱ.1 (ν.1 - 1) (1 + 0)) _
    exact kernel_first_cv h hν
  · change CVRel (R.op 4) (parts ϱ.2 (ν.2 + 1) (0 + 0)) _
    exact kernel_second_cv h hν
  · change CVRel (R.op 5) (parts (ϱ.1 + ϱ.2) ((ν.1 - 1) + (ν.2 + 1) + 0) (1 + 0)) _
    rw [show (ν.1 - 1) + (ν.2 + 1) + 0 = ν.1 + ν.2 by omega]
    exact kernel_highest_cv h hν

private theorem first_trunc_of_quotient
    (h : CV3Rel R w (0, 1) (ν - (1, 0)) (ϱ + (1, 0)) 0) (hν : 0 < ν.1)
    (q : ℕ) (hq : ν.1 + ϱ.1 ≤ q) : R.op 3 q w = 0 := by
  apply trunc_of_cvrel h.first q
  rw [parts_length]
  change (ϱ.1 + 1) + (ν.1 - 1) + (0 + 0) ≤ q
  omega

private theorem source_first_cv_of_quotient
    (h : CV3Rel R w (0, 1) (ν - (1, 0)) (ϱ + (1, 0)) 0) (hν : 0 < ν.1) :
    CVRel (R.op 3) (parts ϱ.1 ν.1 1) w := by
  have htr := first_trunc_of_quotient h hν
  apply cvrel_parts123 ϱ.1 ν.1 1 (CVRoots.sl2_first R)
    (fun s => h.raising 0 (by decide) s)
    (fun p hp => h.cartan_pos 6 (by decide) p hp)
  · rw [Module.End.pow_apply]
    rw [show 3 * ϱ.1 + 2 * ν.1 + 1 + 1 =
      0 + 2 * (ν.1 - 1) + 3 * (ϱ.1 + 1) + 0 + 1 by omega]
    exact h.lowering_first
  · intro q hq
    exact htr q (by omega)
  · intro s hs
    exact Q_high (CVRoots.sl2_first R).hFF htr 2 s (by omega)

private theorem source_highest_cv_of_quotient
    (h : CV3Rel R w (0, 1) (ν - (1, 0)) (ϱ + (1, 0)) 0) (hν : 0 < ν.1) :
    CVRel (R.op 5) (parts (ϱ.1 + ϱ.2) (ν.1 + ν.2 + 1) 0) w := by
  have htr : ∀ q, (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + 1 ≤ q → R.op 5 q w = 0 := by
    intro q hq
    apply trunc_of_cvrel h.highest q
    rw [parts_length]
    change ((ϱ.1 + 1) + ϱ.2) + ((ν.1 - 1) + ν.2 + 0) + (0 + 1) ≤ q
    omega
  apply cvrel_parts123 (ϱ.1 + ϱ.2) (ν.1 + ν.2 + 1) 0 (CVRoots.sl2_highest R)
    (fun s => h.raising 2 (by decide) s)
  · intro p hp
    simp only [LinearMap.add_apply, h.cartan_pos 6 (by decide) p hp,
      h.cartan_pos 7 (by decide) p hp, add_zero]
  · have hn := CVKernelHW.cvrel_zero_nil h.highest
    rw [CVKernelHW.parts_sum] at hn
    change (R.op 5 0 ^
      (3 * ((ϱ.1 + 1) + ϱ.2) + 2 * ((ν.1 - 1) + ν.2 + 0) + (0 + 1) + 1)) w = 0 at hn
    rw [show 3 * (ϱ.1 + ϱ.2) + 2 * (ν.1 + ν.2 + 1) + 0 + 1 =
      3 * ((ϱ.1 + 1) + ϱ.2) + 2 * ((ν.1 - 1) + ν.2 + 0) + (0 + 1) + 1 by omega]
    exact hn
  · intro q hq
    exact htr q (by omega)
  · intro s hs
    exact Q_high (CVRoots.sl2_highest R).hFF htr 2 s (by omega)

/-- The one-adjoint quotient presentation implies all original source relations. -/
theorem source_of_quotient
    (h : CV3Rel R w (0, 1) (ν - (1, 0)) (ϱ + (1, 0)) 0) (hν : 0 < ν.1) :
    CV3Rel R w (0, 0) ν ϱ 1 := by
  refine ⟨h.raising, h.cartan_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change R.op 6 0 w = ((0 + 2 * ν.1 + 3 * ϱ.1 + 1 : ℕ) : ℂ) • w
    rw [show 0 + 2 * ν.1 + 3 * ϱ.1 + 1 =
      0 + 2 * (ν.1 - 1) + 3 * (ϱ.1 + 1) + 0 by omega]
    exact h.cartan_first
  · change R.op 7 0 w = ((0 + 2 * ν.2 + 3 * ϱ.2 + 1 : ℕ) : ℂ) • w
    rw [show 0 + 2 * ν.2 + 3 * ϱ.2 + 1 = 1 + 2 * ν.2 + 3 * ϱ.2 + 0 by omega]
    exact h.cartan_second
  · change (R.op 3 0)^[0 + 2 * ν.1 + 3 * ϱ.1 + 1 + 1] w = 0
    rw [show 0 + 2 * ν.1 + 3 * ϱ.1 + 1 + 1 =
      0 + 2 * (ν.1 - 1) + 3 * (ϱ.1 + 1) + 0 + 1 by omega]
    exact h.lowering_first
  · change (R.op 4 0)^[0 + 2 * ν.2 + 3 * ϱ.2 + 1 + 1] w = 0
    rw [show 0 + 2 * ν.2 + 3 * ϱ.2 + 1 + 1 = 1 + 2 * ν.2 + 3 * ϱ.2 + 0 + 1 by omega]
    exact h.lowering_second
  · exact source_first_cv_of_quotient h hν
  · exact h.second
  · exact source_highest_cv_of_quotient h hν

/-- The zero-epsilon one-adjoint quotient has exactly the original CV
relations together with the single actual first-root kernel-generator relation. -/
theorem quotient_rel_iff (hν : 0 < ν.1) :
    CV3Rel R w (0, 1) (ν - (1, 0)) (ϱ + (1, 0)) 0 ↔
      CV3Rel R w (0, 0) ν ϱ 1 ∧ R.op 3 (ν.1 + ϱ.1) w = 0 := by
  constructor
  · intro h
    exact ⟨source_of_quotient h hν, first_trunc_of_quotient h hν _ le_rfl⟩
  · rintro ⟨h, htop⟩
    exact quotient_rel h hν htop

end VOA.DeligneAudit.A2.CVBaseOne

#print axioms VOA.DeligneAudit.CVsl2.cvrel_kernel_final_one
#print axioms VOA.DeligneAudit.A2.CVBaseOne.central_square_descendant
#print axioms VOA.DeligneAudit.A2.CVBaseOne.kernel_theta_square
#print axioms VOA.DeligneAudit.A2.CVBaseOne.quotient_theta_square
#print axioms VOA.DeligneAudit.A2.CVBaseOne.quotient_rel
#print axioms VOA.DeligneAudit.A2.CVBaseOne.kernel_first_cv
#print axioms VOA.DeligneAudit.A2.CVBaseOne.kernel_lowering_highest
#print axioms VOA.DeligneAudit.A2.CVBaseOne.kernel_rel
#print axioms VOA.DeligneAudit.A2.CVBaseOne.quotient_rel_iff
