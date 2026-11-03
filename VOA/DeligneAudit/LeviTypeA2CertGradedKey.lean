import VOA.DeligneAudit.LeviTypeA2CertF2Graded

/-! Interpret the graded conversion remainder inside one radical key. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviConversion
open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : SectorWeyl.CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

theorem a2_gradedLowerModeSpan_le_key (xs ys : List ℕ) (k d : ℕ) :
    gradedLowerModeSpan (fun i => ρ.op 3 i) (fun i => ρ.op 5 i)
      xs ys k d 1 w ≤
      a2KeyLayer ρ w ⟨xs.length, ys.length + k, d⟩ := by
  rw [gradedLowerModeSpan, Submodule.span_le]
  intro z hz
  obtain ⟨zs, bs, hza, hbs, hd, _, rfl⟩ := hz
  let l : List (Fin 2 × ℕ) :=
    (zs.map fun s => ((0 : Fin 2), s)) ++
      (bs.map fun s => ((1 : Fin 2), s))
  have hkey : a2WordKey l = ⟨xs.length, ys.length + k, d⟩ := by
    simp [l, a2WordKey, List.countP_append, List.sum_append,
      List.map_map, Function.comp_def, hza, hbs, hd]
  have hword : radicalWord (a2RadicalOp ρ) l • w =
      (aWord (fun i => ρ.op 3 i) zs *
        (bs.map fun i => ρ.op 5 i).prod) • (1 • w) := by
    simp [l, radicalWord, a2RadicalOp, aWord, List.map_append,
      List.map_map, Function.comp_def, List.prod_append, mul_smul]
  have hw := radicalWord_mem_own_key ρ w l
  rw [hword, hkey] at hw
  simpa only [one_smul] using hw

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_gradedLowerModeSpan_le_key
