import VOA.Classification.COne.OrbRat5UCert

/-! # `U₍₈₎ J = -10800 E` in `V₈`

From the kernel certificate `cert_UJ` and the soundness of the evaluator (`actU_sound`).
-/
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbRat5
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e LatMod OrbRat3

theorem evalSt_JcSt : evalSt JcSt = Jc := by
  rw [JcSt, evalSt_cons, evalSt_nil, add_zero]
  change latStateGen (latP 4) (evRc (a0 4) (cα 4) (liftR JR)) 0 = _
  rw [evRc_liftR]

theorem evalSt_UJ : evalSt UJ = (-10800 : ℂ) • Ec := by
  simp only [UJ, evalSt_cons, evalSt_nil, evRc_nil, evRc_cons, evalWordC_nil, map_zero,
    add_zero, zero_add, sector, LinearMap.coe_mk, AddHom.coe_mk, latStateGen_csmul]
  rw [Ec, smul_add, add_comm]
  push_cast
  rfl

theorem actU_JcSt_sectors : ∀ p ∈ actU 8 8 JcSt, p.1 ∈ [-2, -1, 0, 1, 2] := by
  intro p hp
  simp only [actU, termU, scaleSt, actJ, actE, JcSt, List.mem_flatMap, List.mem_append,
    List.mem_map, List.mem_cons, List.mem_range, List.not_mem_nil, or_false] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases hp with ⟨i, -, hp⟩
  aesop

/-- `U₍₈₎ J = -10800 E` in `V₈`. -/
theorem U_eight_J : (V2m 4 four_ge_one).smul Uc 8 Jc = (-10800 : ℂ) • Ec := by
  rw [← evalSt_JcSt, actU_sound 8 8 JcSt (r := 4) (by rw [evalSt_JcSt]; exact Jc_mem)
    (by norm_num) (by norm_num), ← evalSt_bucket _ (by decide) _ actU_JcSt_sectors, cert_UJ,
    evalSt_UJ]

end VOA.Classification.COne.OrbRat5
