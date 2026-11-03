import VOA.DeligneAudit.LeviTypeA3TwoRootNil

/-! Sharp zero-mode nilpotence for the first compound radical root. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.FiniteG
open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

private theorem op_comm_end (x y : Fin 15) (r s : ℕ) :
    ρ.op x r * ρ.op y s - ρ.op y s * ρ.op x r =
      ∑ e, bracketTable x y e • ρ.op e (r + s) := by
  ext v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.smul_apply]
  exact ρ.comm x y r s v

theorem a3_compound_ef_table (e : Fin 15) :
    bracketTable 1 7 e =
      if e = 12 ∨ e = 13 then 1 else 0 := by
  have h : bracketInt 1 7 e =
      if e = 12 ∨ e = 13 then 1 else 0 := by
    fin_cases e <;> decide
  simp [bracketTable, h]

theorem a3_compound_hf_table (e : Fin 15) :
    bracketTable 12 7 e + bracketTable 13 7 e =
      if e = 7 then -2 else 0 := by
  have h : bracketInt 12 7 e + bracketInt 13 7 e =
      if e = 7 then -2 else 0 := by
    fin_cases e <;> decide
  change (bracketInt 12 7 e : ℂ) + (bracketInt 13 7 e : ℂ) = _
  rw [← Int.cast_add, h]
  split_ifs <;> norm_num

theorem a3_compound_one_nilpotence (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) :
    (ρ.op (F 1) 0 ^ (a + b + 1)) w = 0 := by
  let X : Module.End ℂ V := ρ.op (leviF 0) 0
  let Y : Module.End ℂ V := ρ.op (F 0) 0
  let Z : Module.End ℂ V := ρ.op (F 1) 0
  let E : Module.End ℂ V := ρ.op 1 0
  let H : Module.End ℂ V := ρ.op 12 0 + ρ.op 13 0
  have hXY : adR X Y = Z := by
    rw [adR_apply, op_comm_end]
    simp [X, Y, Z, levi_step_one]
  have hXXY : (adR X)^[2] Y = 0 := by
    rw [show (2 : ℕ) = 1 + 1 by omega, Function.iterate_add_apply]
    simp only [Function.iterate_one, hXY, adR_apply]
    rw [op_comm_end]
    simp [X, Z, levi_other_zero 0 1 (by decide)]
  have hYYX : (adR Y)^[2] X = 0 := by
    rw [show (2 : ℕ) = 1 + 1 by omega, Function.iterate_add_apply]
    have hYX : adR Y X = -Z := by
      rw [adR_apply]
      rw [show Y * X - X * Y = -(X * Y - Y * X) by abel]
      rw [← adR_apply, hXY]
    simp only [Function.iterate_one, hYX, adR_apply]
    have hc : Y * Z - Z * Y = 0 := by
      rw [op_comm_end]
      simp [Y, Z, radical_abelian]
    calc
      Y * -Z - -Z * Y = -(Y * Z - Z * Y) := by
        simp only [mul_neg, neg_mul]
        abel
      _ = 0 := by rw [hc]; simp
  have hY : (Y ^ (a + 1)) w = 0 := by
    simpa [Y, simpleF, F, weightABC, Module.End.pow_apply] using h.lowering 0
  have hX : (X ^ (b + 1)) w = 0 := by
    simpa [X, leviF, simpleF, weightABC, Module.End.pow_apply] using h.lowering 1
  have hN : Z^[a + 1 + 2 * b] w = 0 := by
    simpa [← Module.End.pow_apply] using
      two_root_nil_large X Y Z w a b hXY hXXY hYYX hY hX
  have hEF : ∀ v, E (Z v) - Z (E v) = H v := by
    intro v
    have hc : E * Z - Z * E = H := by
      rw [op_comm_end]
      simp [E, Z, H, F, Fin.sum_univ_succ, a3_compound_ef_table]
    exact congrArg (fun T : Module.End ℂ V => T v) hc
  have hHF : ∀ v, H (Z v) - Z (H v) = (-2 : ℂ) • Z v := by
    intro v
    have hc : H * Z - Z * H = (-2 : ℂ) • Z := by
      rw [show H * Z - Z * H =
        (ρ.op 12 0 * Z - Z * ρ.op 12 0) +
          (ρ.op 13 0 * Z - Z * ρ.op 13 0) by
            dsimp [H]; noncomm_ring]
      rw [op_comm_end, op_comm_end]
      rw [← Finset.sum_add_distrib]
      simp_rw [← add_smul]
      simp [Z, F, a3_compound_hf_table]
    exact congrArg (fun T : Module.End ℂ V => T v) hc
  have hE : E w = 0 := h.raising 1 (by decide) 0
  have hH : H w = ((a + b : ℕ) : ℂ) • w := by
    change ρ.op 12 0 w + ρ.op 13 0 w = ((a + b : ℕ) : ℂ) • w
    rw [show ρ.op 12 0 w = (a : ℂ) • w by
      simpa [simpleH, weightABC] using h.cartan_zero 0]
    rw [show ρ.op 13 0 w = (b : ℂ) • w by
      simpa [simpleH, weightABC] using h.cartan_zero 1]
    simp [Nat.cast_add, add_smul]
  have hsharp := sl2_lowering_of_nilpotent E Z H hEF hHF w
    (a + b) (a + 1 + 2 * b) hE hH hN (by omega)
  simpa [Z, Module.End.pow_apply] using hsharp

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_compound_one_nilpotence
#print axioms VOA.DeligneAudit.A3Sector.a3_compound_ef_table
#print axioms VOA.DeligneAudit.A3Sector.a3_compound_hf_table
