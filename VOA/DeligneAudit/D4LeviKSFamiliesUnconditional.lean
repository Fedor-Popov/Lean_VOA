import VOA.DeligneAudit.D4LeviKSMixedPresentation

/-! The three unrestricted symmetric-shift relation families. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Rx with a concrete finite fixed-shape polynomial and every independent
    symmetric X, Y, Z shift. -/
theorem rx_family_prefix_unconditional
    (ρ : CurrentModule D4sector.f V) (w : V) (m i : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs ys : List ℕ) (c s : ℕ)
    (hK : 1 ≤ rs.length) (hks : m + 1 ≤ c + rs.length + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey (List.replicate rs.length 0) ys [] c (rs.sum + ys.sum + s)) :
    ∃ (shape : Fin (mixedXYZColours 4 1 c
        (ys ++ List.replicate c 0) rs).length → Fin 6)
      (W : MvPolynomial (Fin (mixedXYZColours 4 1 c
        (ys ++ List.replicate c 0) rs).length) ℂ),
      (∀ u, shape u = 1 ∨ shape u = 4 ∨ shape u = 5) ∧
      xyzEvaluation ρ w shape W =
        mixedTop (yOp ρ) (zOp ρ) c s (ys ++ List.replicate c 0)
          (rs.map (transportCurrent (xOp ρ))).prod w ∧
      ∀ P : MvPolynomial (Fin (mixedXYZColours 4 1 c
          (ys ++ List.replicate c 0) rs).length) ℂ,
        P ∈ xyzPowerSumAlgebra shape →
          xyzEvaluation ρ w shape (symmetricShiftAction _ P W) ∈
            keyPrefix ρ w m i := by
  obtain ⟨shape, W, hshape, hW⟩ := mixedTop_presentation ρ w 4 1
    (Or.inr (Or.inl rfl)) (Or.inl rfl) c s
    (ys ++ List.replicate c 0) rs
  have hW' : xyzEvaluation ρ w shape W =
      mixedTop (yOp ρ) (zOp ρ) c s (ys ++ List.replicate c 0)
        (rs.map (transportCurrent (xOp ρ))).prod w := by
    simpa [yOp, xOp, radicalColour] using hW
  refine ⟨shape, W, hshape, hW', ?_⟩
  intro P hP
  exact rx_family_prefix_of_evaluation ρ w m i h rs ys c s hK hks
    hi hkey shape hshape W P hW' hP

/-- Ry with a concrete finite fixed-shape polynomial and every independent
    symmetric X, Y, Z shift. -/
theorem ry_family_prefix_unconditional
    (ρ : CurrentModule D4sector.f V) (w : V) (m i : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs xs : List ℕ) (c s : ℕ)
    (hK : 1 ≤ rs.length) (hks : m + 1 ≤ c + rs.length + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey xs (List.replicate rs.length 0) [] c (rs.sum + xs.sum + s)) :
    ∃ (shape : Fin (mixedXYZColours 1 4 c
        (xs ++ List.replicate c 0) rs).length → Fin 6)
      (W : MvPolynomial (Fin (mixedXYZColours 1 4 c
        (xs ++ List.replicate c 0) rs).length) ℂ),
      (∀ u, shape u = 1 ∨ shape u = 4 ∨ shape u = 5) ∧
      xyzEvaluation ρ w shape W =
        mixedTop (xOp ρ) (zOp ρ) c s (xs ++ List.replicate c 0)
          (rs.map (transportCurrent (yOp ρ))).prod w ∧
      ∀ P : MvPolynomial (Fin (mixedXYZColours 1 4 c
          (xs ++ List.replicate c 0) rs).length) ℂ,
        P ∈ xyzPowerSumAlgebra shape →
          xyzEvaluation ρ w shape (symmetricShiftAction _ P W) ∈
            keyPrefix ρ w m i := by
  obtain ⟨shape, W, hshape, hW⟩ := mixedTop_presentation ρ w 1 4
    (Or.inl rfl) (Or.inr (Or.inl rfl)) c s
    (xs ++ List.replicate c 0) rs
  have hW' : xyzEvaluation ρ w shape W =
      mixedTop (xOp ρ) (zOp ρ) c s (xs ++ List.replicate c 0)
        (rs.map (transportCurrent (yOp ρ))).prod w := by
    simpa [yOp, xOp, radicalColour] using hW
  refine ⟨shape, W, hshape, hW', ?_⟩
  intro P hP
  exact ry_family_prefix_of_evaluation ρ w m i h rs xs c s hK hks
    hi hkey shape hshape W P hW' hP

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rx_family_prefix_unconditional
#print axioms VOA.DeligneAudit.D4Levi.ry_family_prefix_unconditional
