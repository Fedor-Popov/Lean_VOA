import VOA.DeligneAudit.D4LevelReductionBottomRelations

/-! Cartan weights and the ideal of mode-polynomial relations at a fixed level. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- The bottom radical multiplicity space with fixed letter counts and arbitrary modes. -/
def bottomMultiplicitySpan (a c : ℕ) : Submodule ℂ V :=
  ⨆ d : ℕ, keyLayer ρ w (bottomRadicalKey a c d)

/-- Cartan currents preserve both bottom letter counts. -/
theorem bottomMultiplicitySpan_rawCartan (m a c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (i : Fin 4) (r : ℕ) :
    bottomMultiplicitySpan ρ w a c ≤
      (bottomMultiplicitySpan ρ w a c).comap (ρ.op (reductiveCartanColour i) r) := by
  apply iSup_le
  intro d v hv
  change ρ.op (reductiveCartanColour i) r v ∈ bottomMultiplicitySpan ρ w a c
  have hsimple (j : Fin 3) : ρ.op (leviColour (A3Sector.simpleH j)) r v ∈
      bottomMultiplicitySpan ρ w a c := by
    by_cases hr : r = 0
    · subst r
      rw [cartan_weight_key ρ w m h j (bottomRadicalKey a c d) hv]
      exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem d hv)
    · apply Submodule.mem_iSup_of_mem (d + r)
      simpa [keyShift, bottomRadicalKey] using
        cartan_pos_maps_key ρ w m h j r (Nat.pos_of_ne_zero hr) _ hv
  fin_cases i
  · change ρ.op (0 : Fin 28) r v ∈ _
    by_cases hr : r = 0
    · subst r
      rw [extra_weight_key ρ w m h (bottomRadicalKey a c d) hv]
      exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem d hv)
    · apply Submodule.mem_iSup_of_mem (d + r)
      simpa [keyShift, bottomRadicalKey] using extra_pos_key ρ w m h r
        (Nat.pos_of_ne_zero hr) _ hv
  · exact hsimple 1
  · exact hsimple 0
  · exact hsimple 2

/-- All bottom Cartan vectors are linear combinations of words with the same two letter counts. -/
theorem bottomCartanSpan_le_bottomMultiplicity (m a c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    bottomCartanSpan ρ w a c ≤ bottomMultiplicitySpan ρ w a c := by
  rw [bottomCartanSpan, Submodule.span_le]
  rintro v ⟨l, rfl⟩
  induction l with
  | nil =>
      apply Submodule.mem_iSup_of_mem 0
      simpa [bottomVector, bottomRadicalWord_key, reductiveCartanWord, wordOp] using
        radicalWord_mem_key ρ w (bottomRadicalWord a c)
  | cons q l ih => exact bottomMultiplicitySpan_rawCartan ρ w m a c h q.1 q.2 ih

/-- The bottom multiplicity space has semisimple Levi weight with equal outer labels. -/
theorem bottomMultiplicitySpan_cartan_weight (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0))
    (i : Fin 3) {v : V} (hv : v ∈ bottomMultiplicitySpan ρ w a c) :
    (leviCurrent ρ).op (A3Sector.simpleH i) 0 v =
      (A3Sector.weightABC a b a i : ℂ) • v := by
  refine Submodule.iSup_induction (p := fun d => keyLayer ρ w (bottomRadicalKey a c d))
    (motive := fun v => (leviCurrent ρ).op (A3Sector.simpleH i) 0 v =
      (A3Sector.weightABC a b a i : ℂ) • v) hv ?_ ?_ ?_
  · intro d v hv
    have hw := cartan_weight_key ρ w (a + b + c) h i (bottomRadicalKey a c d) hv
    fin_cases i <;>
      simp [leviCurrent, leviSign, A3Sector.simpleH, A3Sector.weightABC,
        keyLabel, bottomRadicalKey, Nat.cast_add, Int.cast_add, Int.cast_sub] at hw ⊢
    all_goals convert hw using 1 <;> congr 1 <;> ring
  · simp
  · intro x y hx hy
    simp [map_add, hx, hy, smul_add]

/-- Every vector in the bottom Cartan orbit has the required zero-mode weights. -/
theorem bottomCartanSpan_weight (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0))
    (i : Fin 3) {v : V} (hv : v ∈ bottomCartanSpan ρ w a c) :
    (leviCurrent ρ).op (A3Sector.simpleH i) 0 v =
      (A3Sector.weightABC a b a i : ℂ) • v :=
  bottomMultiplicitySpan_cartan_weight ρ w a b c h i
    (bottomCartanSpan_le_bottomMultiplicity ρ w (a + b + c) a c h hv)

/-- Every linear combination of reductive Cartan currents preserves the level filtration. -/
theorem levelFiltration_cartanBlend (m : ℕ) (κ p : ℤ) (a b c : ℂ) (r : ℕ)
    {v : V} (hv : v ∈ levelFiltration ρ w m κ p) :
    cartanBlend ρ a b c r v ∈ levelFiltration ρ w m κ p := by
  let N := levelFiltration ρ w m κ p
  exact N.add_mem
    (N.add_mem (N.smul_mem a (levelFiltration_stable ρ w m κ p _ r
      (leviColour_isLevi (A3Sector.simpleH 0)) hv))
      (N.smul_mem b (levelFiltration_stable ρ w m κ p _ r
        (leviColour_isLevi (A3Sector.simpleH 1)) hv)))
    (N.smul_mem c (levelFiltration_stable ρ w m κ p 0 r ⟨0, rfl⟩ hv))

/-- Symmetric colour-mode multiplication preserves every evaluated level relation. -/
theorem levelModeRelation_mul {σ : Type*} [Fintype σ] (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ)
    (shape : σ → Fin 6) (hshape : ∀ t, shape t = 1 ∨ shape t = 4 ∨ shape t = 5)
    (P : MvPolynomial σ ℂ) (hP : P ∈ xyzPowerSumAlgebra shape)
    (W : MvPolynomial σ ℂ)
    (hW : xyzEvaluation ρ w shape W ∈ levelFiltration ρ w m κ p) :
    xyzEvaluation ρ w shape (P * W) ∈ levelFiltration ρ w m κ p := by
  let N := (levelFiltration ρ w m κ p).comap (xyzEvaluation ρ w shape)
  have hInv (q : Fin 3) (r : ℕ) {v : V} (hv : v ∈ levelFiltration ρ w m κ p) :
      selectiveCartan ρ q r v ∈ levelFiltration ρ w m κ p := by
    fin_cases q
    · exact levelFiltration_cartanBlend ρ w m κ p 1 0 (-1) r hv
    · exact levelFiltration_cartanBlend ρ w m κ p (-1) 0 (-1) r hv
    · exact levelFiltration_cartanBlend ρ w m κ p (-1) (-1) 0 r hv
  have hsub : xyzPowerSumAlgebra shape ≤
      preservingShiftAlgebra (MvPolynomial σ ℂ) (symmetricShiftAction σ) N := by
    apply Algebra.adjoin_le
    rintro Q ⟨j, r, hj, hr, rfl⟩ U hU
    have hh := hInv (if j = 1 then 0 else if j = 4 then 1 else 2) r hU
    rw [xyzEvaluation_psum_intertwine ρ w m h shape hshape j hj r hr U] at hh
    have hn : (if j = 5 then (1 : ℂ) else 2) ≠ 0 := by split_ifs <;> norm_num
    change xyzEvaluation ρ w shape
      (symmetricShiftAction σ (colourPsum shape j r) U) ∈ levelFiltration ρ w m κ p
    exact (Submodule.smul_mem_iff _ hn).mp hh
  exact hsub hP W hW

/-- The exact relations among symmetric mode polynomials form an ideal. -/
def levelModeRelationIdeal {σ : Type*} [Fintype σ] (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ)
    (shape : σ → Fin 6) (hshape : ∀ t, shape t = 1 ∨ shape t = 4 ∨ shape t = 5) :
    Ideal (xyzPowerSumAlgebra shape) where
  carrier := {P | xyzEvaluation ρ w shape P ∈ levelFiltration ρ w m κ p}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ
    change xyzEvaluation ρ w shape (P.val + Q.val) ∈ levelFiltration ρ w m κ p
    rw [map_add]
    exact (levelFiltration ρ w m κ p).add_mem hP hQ
  smul_mem' := by
    intro P Q hQ
    exact levelModeRelation_mul ρ w m h κ p shape hshape P P.property Q hQ

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.bottomMultiplicitySpan_rawCartan
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCartanSpan_le_bottomMultiplicity
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomMultiplicitySpan_cartan_weight
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCartanSpan_weight
#print axioms VOA.DeligneAudit.D4LevelReduction.levelFiltration_cartanBlend
#print axioms VOA.DeligneAudit.D4LevelReduction.levelModeRelation_mul
#print axioms VOA.DeligneAudit.D4LevelReduction.levelModeRelationIdeal
