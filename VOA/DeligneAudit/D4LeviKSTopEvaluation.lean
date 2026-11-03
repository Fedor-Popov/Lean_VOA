import VOA.DeligneAudit.D4LeviKSTopWords

/-! Evaluating the finite top-contraction words in a D4 current module. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem radicalWord_eq_prod (ρ : CurrentModule D4sector.f V) (w : V)
    (l : List (Fin 6 × ℕ)) :
    radicalWord ρ w l =
      (l.map fun p => ρ.op (radicalColour p.1) p.2).prod w := by
  induction l with
  | nil => simp [radicalWord, wordOp]
  | cons p ps ih =>
      simp only [radicalWord, List.map_cons, wordOp,
        List.prod_cons, Module.End.mul_apply]
      exact congrArg (ρ.op (radicalColour p.1) p.2) ih

theorem topWordOp_eq_radical_prod
    (ρ : CurrentModule D4sector.f V) (k s : ℕ) (bases : List ℕ)
    (l : List (Fin 6 × ℕ)) (hl : l ∈ topWords k s bases) :
    topWordOp (yOp ρ) (zOp ρ) l =
      (l.map fun p => ρ.op (radicalColour p.1) p.2).prod := by
  obtain ⟨p, hp, zs, hzs, hk, rfl⟩ := topWords_colour_counts k s bases l hl
  simp only [topWordOp_allocation, List.map_append, List.prod_append,
    List.map_map, Function.comp_def, aWord]
  change (p.1.map (fun r => ρ.op (26 : Fin 28) r)).prod *
      (zs.map (fun r => ρ.op (27 : Fin 28) r)).prod =
    (p.1.map (fun r => ρ.op (26 : Fin 28) r)).prod *
      (zs.map (fun r => ρ.op (27 : Fin 28) r)).prod
  rfl

private theorem end_list_sum_apply (ts : List (Module.End ℂ V)) (v : V) :
    ts.sum v = (ts.map fun T => T v).sum := by
  induction ts with
  | nil => simp
  | cons T ts ih => simp [ih, LinearMap.add_apply]

noncomputable def rzTopWords (xs ys zs : List ℕ) (k s : ℕ) :
    List (List (Fin 6 × ℕ)) :=
  (topWords k s (ys ++ List.replicate k 0)).map fun l =>
    l ++ (xs.map fun r => ((1 : Fin 6), r)) ++
      (zs.map fun r => ((5 : Fin 6), r))

def rzTopColours (xs ys zs : List ℕ) (k : ℕ) : List (Fin 6) :=
  List.replicate ys.length 4 ++ List.replicate k 5 ++
    List.replicate xs.length 1 ++ List.replicate zs.length 5

theorem rzTopWords_colour_shape (xs ys zs : List ℕ) (k s : ℕ)
    (l : List (Fin 6 × ℕ)) (hl : l ∈ rzTopWords xs ys zs k s) :
    l.map Prod.fst = rzTopColours xs ys zs k := by
  simp only [rzTopWords, List.mem_map] at hl
  obtain ⟨t, ht, rfl⟩ := hl
  rw [List.map_append, List.map_append,
    topWords_colour_shape k s (ys ++ List.replicate k 0) t ht]
  simp [rzTopColours, List.map_map, List.map_const', Nat.add_sub_cancel_right]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, ih, List.length_cons]
      rw [Nat.add_comm xs.length 1]
      simp only [Nat.one_add, List.replicate_succ]
      simp

/-- The entire graded Rz contraction is a finite sum of fixed-colour
    radical words, including both spectator colours. -/
theorem rz_topSum_eq_wordSum (ρ : CurrentModule D4sector.f V) (w : V)
    (xs ys zs : List ℕ) (k s : ℕ) :
    topSum (yOp ρ) (zOp ρ) k s (ys ++ List.replicate k 0) •
      (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) =
    ((rzTopWords xs ys zs k s).map (radicalWord ρ w)).sum := by
  rw [topSum_eq_topWords]
  change ((topWords k s (ys ++ List.replicate k 0)).map
      (topWordOp (yOp ρ) (zOp ρ))).sum
        (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) w) =
    ((rzTopWords xs ys zs k s).map (radicalWord ρ w)).sum
  rw [end_list_sum_apply]
  simp only [rzTopWords, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro l hl
  rw [radicalWord_eq_prod, List.map_append, List.map_append,
    List.prod_append, List.prod_append,
    ← topWordOp_eq_radical_prod ρ k s _ l hl]
  simp [Module.End.mul_apply, mul_assoc, xOp, zOp, radicalColour,
    List.map_map, Function.comp_def]
  change (topWordOp (yOp ρ) (zOp ρ) l)
      ((xs.map fun r => ρ.op (22 : Fin 28) r).prod
        ((zs.map fun r => ρ.op (27 : Fin 28) r).prod w)) =
    (topWordOp (yOp ρ) (zOp ρ) l)
      ((xs.map fun r => ρ.op (22 : Fin 28) r).prod
        ((zs.map fun r => ρ.op (27 : Fin 28) r).prod w))
  rfl

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.radicalWord_eq_prod
#print axioms VOA.DeligneAudit.D4Levi.topWordOp_eq_radical_prod
#print axioms VOA.DeligneAudit.D4Levi.rz_topSum_eq_wordSum
#print axioms VOA.DeligneAudit.D4Levi.rzTopWords_colour_shape
