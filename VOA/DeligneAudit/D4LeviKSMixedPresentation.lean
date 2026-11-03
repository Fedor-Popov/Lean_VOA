import VOA.DeligneAudit.D4LeviKSMixedEvaluation

/-! Fixed-shape mode polynomials for the mixed contraction families. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mixedTop_presentation
    (ρ : CurrentModule D4sector.f V) (w : V)
    (j t : Fin 6) (hj : j = 1 ∨ j = 4 ∨ j = 5)
    (ht : t = 1 ∨ t = 4 ∨ t = 5)
    (k s : ℕ) (bases rs : List ℕ) :
    ∃ (shape : Fin (mixedXYZColours j t k bases rs).length → Fin 6)
      (W : MvPolynomial (Fin (mixedXYZColours j t k bases rs).length) ℂ),
      (∀ u, shape u = 1 ∨ shape u = 4 ∨ shape u = 5) ∧
      xyzEvaluation ρ w shape W =
        mixedTop (fun r => ρ.op (radicalColour j) r) (zOp ρ)
          k s bases
          (rs.map (transportCurrent fun r => ρ.op (radicalColour t) r)).prod w := by
  classical
  let cs := mixedXYZColours j t k bases rs
  obtain ⟨shape, hshape⟩ := exists_colour_shape
    (σ := Fin cs.length) cs (by simp)
  have hcolour : ∀ p ∈ (mixedXYZWords j t k s bases rs).map
      (fun l => ((1 : ℂ), l)),
      (p.2.map Prod.fst).Perm (Finset.univ.toList.map shape) := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hp
    rw [mixedXYZWords_colour_shape j t k s bases rs l hl, hshape]
  obtain ⟨W, hW⟩ := xyzEvaluation_of_wordSum_colourPerm ρ w shape
    ((mixedXYZWords j t k s bases rs).map fun l => ((1 : ℂ), l)) hcolour
  have hgood : ∀ u, shape u = 1 ∨ shape u = 4 ∨ shape u = 5 := by
    intro u
    have hu : shape u ∈ cs := by
      rw [← hshape]
      exact List.mem_map.mpr ⟨u, by simp, rfl⟩
    simp [cs, mixedXYZColours] at hu
    rcases hu with ⟨_, hu⟩ | ⟨_, hu⟩ | ⟨_, hu⟩
    · simpa [hu] using hj
    · exact Or.inr (Or.inr hu)
    · simpa [hu] using ht
  refine ⟨shape, W, hgood, ?_⟩
  have hsum := mixedTop_eq_radicalWordSum ρ w j t k s bases rs
  have hW' : xyzEvaluation ρ w shape W =
      ((mixedXYZWords j t k s bases rs).map (radicalWord ρ w)).sum := by
    simpa only [List.map_map, Function.comp_def, one_smul] using hW
  exact hW'.trans hsum.symm

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.mixedTop_presentation
