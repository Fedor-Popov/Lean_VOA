import VOA.DeligneAudit.LeviTypeA3GradedPairBox

/-! The smaller-mode terms of either conversion stay in the original key layer. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviTypeA
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_three_mode_mem_key (xs ys zs : List ℕ) :
    (aWord (fun i => ρ.op (F 0) i) xs *
      (ys.map fun i => ρ.op (F 1) i).prod *
        (zs.map fun i => ρ.op (F 2) i).prod) w ∈
      a3KeyLayer ρ w
        ⟨xs.length, ys.length, zs.length, xs.sum + ys.sum + zs.sum⟩ := by
  let l : List (Fin 3 × ℕ) :=
    (xs.map fun s => ((0 : Fin 3), s)) ++
      (ys.map fun s => ((1 : Fin 3), s)) ++
        (zs.map fun s => ((2 : Fin 3), s))
  have hkey : a3WordKey l =
      ⟨xs.length, ys.length, zs.length, xs.sum + ys.sum + zs.sum⟩ := by
    simp [l, a3WordKey, List.countP_append, List.map_map,
      Function.comp_def, List.sum_append, Nat.add_assoc]
  have hw := a3_radicalWord_mem_own_key ρ w l
  rw [hkey] at hw
  simpa [l, radicalWord, radicalOp, aWord, List.map_append,
    List.map_map, Function.comp_def, List.prod_append,
    mul_smul, mul_assoc] using hw

theorem a3_rotated_mode_mem_key (xs ys zs : List ℕ) :
    (aWord (fun i => ρ.op (F 1) i) xs *
      (ys.map fun i => ρ.op (F 2) i).prod *
        (zs.map fun i => ρ.op (F 0) i).prod) w ∈
      a3KeyLayer ρ w
        ⟨zs.length, xs.length, ys.length, xs.sum + ys.sum + zs.sum⟩ := by
  let l : List (Fin 3 × ℕ) :=
    (xs.map fun s => ((1 : Fin 3), s)) ++
      (ys.map fun s => ((2 : Fin 3), s)) ++
        (zs.map fun s => ((0 : Fin 3), s))
  have hkey : a3WordKey l =
      ⟨zs.length, xs.length, ys.length, xs.sum + ys.sum + zs.sum⟩ := by
    simp [l, a3WordKey, List.countP_append, List.map_map,
      Function.comp_def, List.sum_append, Nat.add_assoc]
  have hw := a3_radicalWord_mem_own_key ρ w l
  rw [hkey] at hw
  simpa [l, radicalWord, radicalOp, aWord, List.map_append,
    List.map_map, Function.comp_def, List.prod_append,
    mul_smul, mul_assoc] using hw

theorem a3PairModeLowerSpan_le_key (j : Fin 2) (zs : List ℕ)
    (xlen ylen degree σ : ℕ) :
    a3PairModeLowerSpan ρ w j zs xlen ylen degree σ ≤
      a3KeyLayer ρ w
        (if j = 0 then ⟨xlen, ylen, zs.length, degree + zs.sum⟩
        else ⟨zs.length, xlen, ylen, degree + zs.sum⟩) := by
  rw [a3PairModeLowerSpan, Submodule.span_le]
  rintro v ⟨xs, ys, hx, hy, hd, _, rfl⟩
  fin_cases j
  · have hw := a3_three_mode_mem_key ρ w xs ys zs
    simpa [a3ConvA, a3ConvB, a3ConvSpectator,
      hx, hy, hd, mul_assoc, Nat.add_assoc] using hw
  · have hw := a3_rotated_mode_mem_key ρ w xs ys zs
    simpa [a3ConvA, a3ConvB, a3ConvSpectator,
      hx, hy, hd, mul_assoc, Nat.add_assoc, Nat.add_comm] using hw

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_three_mode_mem_key
#print axioms VOA.DeligneAudit.A3Sector.a3_rotated_mode_mem_key
#print axioms VOA.DeligneAudit.A3Sector.a3PairModeLowerSpan_le_key
