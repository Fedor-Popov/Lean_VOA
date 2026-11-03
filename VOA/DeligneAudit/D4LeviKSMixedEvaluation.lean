import VOA.DeligneAudit.D4LeviKSMixedWords

/-! Evaluation of the mixed contractions as fixed-colour radical words. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def recolourTop (j : Fin 6) (l : List (Fin 6 × ℕ)) :
    List (Fin 6 × ℕ) :=
  l.map fun p => (if p.1 = 4 then j else (5 : Fin 6), p.2)

theorem topWordOp_eq_recoloured
    (ρ : CurrentModule D4sector.f V) (j : Fin 6)
    (k s : ℕ) (bases : List ℕ)
    (l : List (Fin 6 × ℕ)) (hl : l ∈ topWords k s bases) :
    topWordOp (fun r => ρ.op (radicalColour j) r) (zOp ρ) l =
      ((recolourTop j l).map fun p => ρ.op (radicalColour p.1) p.2).prod := by
  obtain ⟨p, hp, zs, hzs, hk, rfl⟩ := topWords_colour_counts k s bases l hl
  simp [topWordOp_allocation, recolourTop, List.map_append,
    List.prod_append, List.map_map, Function.comp_def,
    VOA.DeligneAudit.LeviConversion.aWord, zOp, radicalColour]
  change ((p.1.map fun r => ρ.op (radicalColour j) r).prod *
      (zs.map fun r => ρ.op (27 : Fin 28) r).prod) =
    ((p.1.map fun r => ρ.op (radicalColour j) r).prod *
      (zs.map fun r => ρ.op (27 : Fin 28) r).prod)
  rfl

noncomputable def mixedXYZWords (j t : Fin 6)
    (k s : ℕ) (bases rs : List ℕ) : List (List (Fin 6 × ℕ)) :=
  (mixedTopWords k s bases rs).map fun p =>
    recolourTop j p.1 ++ (p.2.map fun r => (t, r))

def mixedXYZColours (j t : Fin 6) (k : ℕ)
    (bases rs : List ℕ) : List (Fin 6) :=
  List.replicate (bases.length - k) j ++ List.replicate k 5 ++
    List.replicate rs.length t

theorem mixedXYZWords_colour_shape (j t : Fin 6)
    (k s : ℕ) (bases rs : List ℕ)
    (l : List (Fin 6 × ℕ)) (hl : l ∈ mixedXYZWords j t k s bases rs) :
    l.map Prod.fst = mixedXYZColours j t k bases rs := by
  simp only [mixedXYZWords, List.mem_map] at hl
  obtain ⟨p, hp, rfl⟩ := hl
  obtain ⟨q, hq, htop, halloc⟩ := mixedTopWords_mem k s bases rs p hp
  have ht := topWords_colour_shape k q.1 bases p.1 htop
  have hr := modeAllocations_length rs q.2 p.2 halloc
  simp only [List.map_append, recolourTop, List.map_map, Function.comp_def]
  rw [show (p.1.map fun x => if x.1 = 4 then j else (5 : Fin 6)) =
      (p.1.map Prod.fst).map fun c => if c = 4 then j else 5 by
        simp [List.map_map, Function.comp_def]]
  rw [ht]
  simp [mixedXYZColours, hr, List.map_append]

private theorem end_list_sum_apply (ts : List (Module.End ℂ V)) (v : V) :
    ts.sum v = (ts.map fun T => T v).sum := by
  induction ts with
  | nil => simp
  | cons T ts ih => simp [ih, LinearMap.add_apply]

theorem mixedTop_eq_radicalWordSum
    (ρ : CurrentModule D4sector.f V) (w : V)
    (j t : Fin 6) (k s : ℕ) (bases rs : List ℕ) :
    mixedTop (fun r => ρ.op (radicalColour j) r) (zOp ρ)
      k s bases
      (rs.map (transportCurrent fun r => ρ.op (radicalColour t) r)).prod w =
    ((mixedXYZWords j t k s bases rs).map (radicalWord ρ w)).sum := by
  rw [mixedTop_eq_allocated_words]
  change ((mixedTopWords k s bases rs).map fun p =>
      topWordOp (fun r => ρ.op (radicalColour j) r) (zOp ρ) p.1 *
        (p.2.map fun r => ρ.op (radicalColour t) r).prod).sum w =
    ((mixedXYZWords j t k s bases rs).map (radicalWord ρ w)).sum
  rw [end_list_sum_apply]
  simp only [mixedXYZWords, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro p hp
  obtain ⟨q, hq, htop, halloc⟩ := mixedTopWords_mem k s bases rs p hp
  rw [radicalWord_eq_prod, List.map_append, List.prod_append]
  rw [← topWordOp_eq_recoloured ρ j k q.1 bases p.1 htop]
  simp only [List.map_map, Function.comp_def, Module.End.mul_apply]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.topWordOp_eq_recoloured
#print axioms VOA.DeligneAudit.D4Levi.mixedTop_eq_radicalWordSum
#print axioms VOA.DeligneAudit.D4Levi.mixedXYZWords_colour_shape
