import VOA.DeligneAudit.D4LeviKSRzRawAllocEvaluation

/-! The fixed-shape Rz word is the dressed Garland operator word. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rzRawWord_operator (ρ : CurrentModule D4sector.f V) (w : V)
    (b : ℕ) (xs modes zs : List ℕ) :
    radicalWord ρ w
        ((xs.map fun r => ((1 : Fin 6), r)) ++
          List.replicate b ((4 : Fin 6), 0) ++
          (modes.map fun r => ((5 : Fin 6), r)) ++
          (zs.map fun r => ((5 : Fin 6), r))) =
      ((yOp ρ 0) ^ b * (modes.map (zOp ρ)).prod) •
        (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) := by
  let Xs := xs.map fun r => ((1 : Fin 6), r)
  let Ys := List.replicate b ((4 : Fin 6), 0)
  let Ms := modes.map fun r => ((5 : Fin 6), r)
  let Zs := zs.map fun r => ((5 : Fin 6), r)
  have hp : (Xs ++ Ys ++ Ms ++ Zs).Perm
      (Ys ++ Ms ++ Xs ++ Zs) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := Xs) (l₂ := Ys ++ Ms)).append_right Zs
  rw [radicalWord_perm ρ w hp]
  rw [← pairRadicalOp_apply]
  simp [pairRadicalOp_append, pairRadicalOp,
    Xs, Ys, Ms, Zs, xOp, yOp, zOp, radicalColour,
    List.map_append, List.map_map, Function.comp_def,
    mul_assoc, Module.End.mul_apply]
  rfl

theorem rzRawSourceGenerator_word_bridge
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b k l s : ℕ) (α : Fin b ⊕ Fin a → ℕ)
    (β : Fin l → ℕ) :
    xyzEvaluation ρ w (pairSourceShape a b (k + l))
        (rzRawSourceGenerator a b k l s α β) =
      ((yOp ρ 0) ^ b *
        ((modeAllocations (List.replicate k 0) s).map fun modes =>
          (modes.map (zOp ρ)).prod).sum) •
        ((((Finset.univ.toList : List (Fin b ⊕ Fin a)).map α).map
            (xOp ρ)).prod *
          (((Finset.univ.toList : List (Fin l)).map β).map
            (zOp ρ)).prod) • w := by
  rw [rzRawSourceGenerator_eval_allocations]
  generalize ha : modeAllocations (List.replicate k 0) s = allocs
  clear ha
  induction allocs with
  | nil => simp
  | cons modes rest ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, add_smul]
      simp only [List.map_map, Function.comp_def]
      have hw := rzRawWord_operator ρ w b
        ((Finset.univ.toList : List (Fin b ⊕ Fin a)).map α)
        modes ((Finset.univ.toList : List (Fin l)).map β)
      simp only [List.map_map, Function.comp_def] at hw
      rw [hw]
      simpa only [List.map_map, Function.comp_def] using
        congrArg₂ (· + ·) rfl ih

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rzRawWord_operator
#print axioms VOA.DeligneAudit.D4Levi.rzRawSourceGenerator_word_bridge
