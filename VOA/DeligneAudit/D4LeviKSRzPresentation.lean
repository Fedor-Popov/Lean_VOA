import VOA.DeligneAudit.D4LeviKSTopEvaluation

/-! A fixed-shape polynomial presentation of every graded Rz contraction. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rz_topSum_presentation
    (ρ : CurrentModule D4sector.f V) (w : V)
    (xs ys zs : List ℕ) (k s : ℕ) :
    ∃ (shape : Fin (rzTopColours xs ys zs k).length → Fin 6)
      (W : MvPolynomial (Fin (rzTopColours xs ys zs k).length) ℂ),
      (∀ t, shape t = 1 ∨ shape t = 4 ∨ shape t = 5) ∧
      xyzEvaluation ρ w shape W =
        topSum (yOp ρ) (zOp ρ) k s (ys ++ List.replicate k 0) •
          (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) := by
  classical
  let cs := rzTopColours xs ys zs k
  obtain ⟨shape, hshape⟩ := exists_colour_shape
    (σ := Fin cs.length) cs (by simp)
  have hcolour : ∀ p ∈ (rzTopWords xs ys zs k s).map
      (fun l => ((1 : ℂ), l)),
      (p.2.map Prod.fst).Perm (Finset.univ.toList.map shape) := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hp
    rw [rzTopWords_colour_shape xs ys zs k s l hl, hshape]
  obtain ⟨W, hW⟩ := xyzEvaluation_of_wordSum_colourPerm ρ w shape
    ((rzTopWords xs ys zs k s).map fun l => ((1 : ℂ), l)) hcolour
  have hgood : ∀ t, shape t = 1 ∨ shape t = 4 ∨ shape t = 5 := by
    intro t
    have ht : shape t ∈ cs := by
      rw [← hshape]
      exact List.mem_map.mpr ⟨t, by simp, rfl⟩
    simp [cs, rzTopColours] at ht
    tauto
  refine ⟨shape, W, hgood, ?_⟩
  have hsum := rz_topSum_eq_wordSum ρ w xs ys zs k s
  have hW' : xyzEvaluation ρ w shape W =
      ((rzTopWords xs ys zs k s).map (radicalWord ρ w)).sum := by
    simpa only [List.map_map, Function.comp_def, one_smul] using hW
  exact hW'.trans hsum.symm

/-- The full graded Rz family has arbitrary independent symmetric
    shifts of its X, Y, and Z modes, with no presentation hypothesis. -/
theorem rz_family_prefix_unconditional
    (ρ : CurrentModule D4sector.f V) (w : V) (m i : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (xs ys zs : List ℕ) (k s : ℕ)
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey xs ys zs k (xs.sum + ys.sum + zs.sum + s)) :
    ∃ (shape : Fin (rzTopColours xs ys zs k).length → Fin 6)
      (W : MvPolynomial (Fin (rzTopColours xs ys zs k).length) ℂ),
      (∀ t, shape t = 1 ∨ shape t = 4 ∨ shape t = 5) ∧
      xyzEvaluation ρ w shape W =
        topSum (yOp ρ) (zOp ρ) k s (ys ++ List.replicate k 0) •
          (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∧
      ∀ P : MvPolynomial (Fin (rzTopColours xs ys zs k).length) ℂ,
        P ∈ xyzPowerSumAlgebra shape →
          xyzEvaluation ρ w shape (symmetricShiftAction _ P W) ∈
            keyPrefix ρ w m i := by
  obtain ⟨shape, W, hshape, hW⟩ := rz_topSum_presentation ρ w xs ys zs k s
  refine ⟨shape, W, hshape, hW, ?_⟩
  intro P hP
  exact rz_family_prefix_of_evaluation ρ w m i h xs ys zs k s hk hks
    hi hkey shape hshape W P hW hP

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_topSum_presentation
#print axioms VOA.DeligneAudit.D4Levi.rz_family_prefix_unconditional
