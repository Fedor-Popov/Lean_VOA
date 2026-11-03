import VOA.DeligneAudit.D4LevelBoundsAdjointAudit

/-!
Parabolic raising relations on the exact-level radical multiplicity space.
The middle simple raising current preserves the level, and the outer simple
raising currents increase it. Consequently the positive parabolic radical
annihilates the multiplicity space modulo the next level.
-/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

/-- The level increment contributed by a simple positive Levi root. -/
def simpleRaisingLevel (i : Fin 3) : ℤ := if i = 1 then 0 else 1

/-- A simple raising replacement preserves the grade and has the root's level increment. -/
theorem raisingReplacement_grade_level (m : ℕ) (i : Fin 3) (r : ℕ)
    {l q : List (Fin 6 × ℕ)} (h : RaiseReplaces i r l q) :
    keyAlphaGrade m (wordKey q) = keyAlphaGrade m (wordKey l) ∧
      keyLeviLevel m (wordKey q) =
        keyLeviLevel m (wordKey l) + simpleRaisingLevel i := by
  induction h with
  | @head j s k n l h =>
      fin_cases i <;> fin_cases j <;> simp [raiseAction] at h
      all_goals
        obtain ⟨rfl, rfl⟩ := h
        simp [keyAlphaGrade, keyDepth, keyLeviLevel, wordKey, simpleRaisingLevel]
        omega
  | @tail j s l q h ih =>
      fin_cases j <;>
        simp [keyAlphaGrade, keyDepth, keyLeviLevel, wordKey] at ih ⊢ <;> omega

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- The span of radical key layers with the specified grade and level, in all degrees. -/
noncomputable def levelMultiplicitySpan (m : ℕ) (κ p : ℤ) : Submodule ℂ V :=
  ⨆ k : RadicalKey, ⨆ (_ : keyAlphaGrade m k = κ),
    ⨆ (_ : keyLeviLevel m k = p), keyLayer ρ w k

theorem keyLayer_le_levelMultiplicitySpan (m : ℕ) (κ p : ℤ) (k : RadicalKey)
    (hg : keyAlphaGrade m k = κ) (hp : keyLeviLevel m k = p) :
    keyLayer ρ w k ≤ levelMultiplicitySpan ρ w m κ p :=
  le_iSup_of_le k (le_iSup_of_le hg (le_iSup_of_le hp le_rfl))

/-- Every exact-level multiplicity vector lies in its Levi filtration term. -/
theorem levelMultiplicitySpan_le_filtration (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ) :
    levelMultiplicitySpan ρ w m κ p ≤ levelFiltration ρ w m κ p := by
  refine iSup_le fun k => iSup_le fun hg => iSup_le fun hp => ?_
  exact (keyLayer_le_orbit ρ w k).trans
    (keyOrbit_le_levelFiltration_of_sat ρ w m h κ p k hg hp.ge)

/-- The simple positive Levi currents shift the exact-level multiplicity space. -/
theorem levelMultiplicitySpan_simple_raise (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ) (i : Fin 3) (r : ℕ) :
    levelMultiplicitySpan ρ w m κ p ≤
      (levelMultiplicitySpan ρ w m κ (p + simpleRaisingLevel i)).comap
        ((leviCurrent ρ).op (A3Sector.simpleE i) r) := by
  refine iSup_le fun k => iSup_le fun hg => iSup_le fun hp => ?_
  rw [keyLayer, Submodule.span_le]
  rintro v ⟨l, hl, rfl⟩
  have hs : raiseWordSpan ρ w i r l ≤
      levelMultiplicitySpan ρ w m κ (p + simpleRaisingLevel i) := by
    rw [raiseWordSpan, Submodule.span_le]
    rintro v ⟨q, hq, rfl⟩
    obtain ⟨hgq, hpq⟩ := raisingReplacement_grade_level m i r hq
    rw [hl, hg] at hgq
    rw [hl, hp] at hpq
    exact keyLayer_le_levelMultiplicitySpan ρ w m κ _ (wordKey q) hgq hpq
      (radicalWord_mem_key ρ w q)
  exact Submodule.smul_mem _ _ (hs (simple_raise_word_span ρ w m h i r l))

/-- Every simple Cartan mode preserves the exact grade and level. -/
theorem levelMultiplicitySpan_cartan (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ) (i : Fin 3) (r : ℕ) :
    levelMultiplicitySpan ρ w m κ p ≤
      (levelMultiplicitySpan ρ w m κ p).comap
        ((leviCurrent ρ).op (A3Sector.simpleH i) r) := by
  refine iSup_le fun k => iSup_le fun hg => iSup_le fun hp => ?_
  intro v hv
  change (leviSign (A3Sector.simpleH i) : ℂ) •
    ρ.op (leviColour (A3Sector.simpleH i)) r v ∈ levelMultiplicitySpan ρ w m κ p
  apply Submodule.smul_mem
  by_cases hr : r = 0
  · subst r
    rw [cartan_weight_key ρ w m h i k hv]
    exact Submodule.smul_mem _ _
      (keyLayer_le_levelMultiplicitySpan ρ w m κ p k hg hp hv)
  · exact keyLayer_le_levelMultiplicitySpan ρ w m κ p (keyShift r k)
      (by simpa [keyAlphaGrade, keyDepth, keyShift] using hg)
      (by simpa [keyLeviLevel, keyShift] using hp)
      (cartan_pos_maps_key ρ w m h i r (Nat.pos_of_ne_zero hr) k hv)

/-- The additional reductive Cartan also preserves the exact-level multiplicity space. -/
theorem levelMultiplicitySpan_extraCartan (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ) (r : ℕ) :
    levelMultiplicitySpan ρ w m κ p ≤
      (levelMultiplicitySpan ρ w m κ p).comap (ρ.op (0 : Fin 28) r) := by
  refine iSup_le fun k => iSup_le fun hg => iSup_le fun hp => ?_
  intro v hv
  change ρ.op (0 : Fin 28) r v ∈ levelMultiplicitySpan ρ w m κ p
  by_cases hr : r = 0
  · subst r
    rw [extra_weight_key ρ w m h k hv]
    exact Submodule.smul_mem _ _
      (keyLayer_le_levelMultiplicitySpan ρ w m κ p k hg hp hv)
  · exact keyLayer_le_levelMultiplicitySpan ρ w m κ p (keyShift r k)
      (by simpa [keyAlphaGrade, keyDepth, keyShift] using hg)
      (by simpa [keyLeviLevel, keyShift] using hp)
      (extra_pos_key ρ w m h r (Nat.pos_of_ne_zero hr) k hv)

/-- Matrix-unit commutators generating the three nonsimple positive Levi roots. -/
theorem positiveLevi_pair_commutator
    (Q : CurrentModule A3Sector.bracketTable V) (c : Fin 3) (r s : ℕ) (v : V) :
    Q.op (if c = 2 then 2 else if c = 1 then 1 else 4) (r + s) v =
      Q.op (if c = 2 then 0 else if c = 1 then 0 else 3) r
        (Q.op (if c = 2 then 4 else if c = 1 then 3 else 5) s v) -
      Q.op (if c = 2 then 4 else if c = 1 then 3 else 5) s
        (Q.op (if c = 2 then 0 else if c = 1 then 0 else 3) r v) := by
  have ht (z : Fin 15) : A3Sector.bracketTable
      (if c = 2 then 0 else if c = 1 then 0 else 3)
      (if c = 2 then 4 else if c = 1 then 3 else 5) z =
        if z = (if c = 2 then 2 else if c = 1 then 1 else 4) then 1 else 0 := by
    have hz : A3Sector.bracketInt
        (if c = 2 then 0 else if c = 1 then 0 else 3)
        (if c = 2 then 4 else if c = 1 then 3 else 5) z =
          if z = (if c = 2 then 2 else if c = 1 then 1 else 4) then 1 else 0 := by
      fin_cases c <;> fin_cases z <;> decide
    simpa [A3Sector.bracketTable, hz]
  rw [Q.comm]
  simp [ht]

/-- The five positive parabolic root currents send exact-level vectors to the next level. -/
theorem levelMultiplicitySpan_parabolic_raise (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ)
    (e : Fin 15) (he : e.val < 6) (hne : e ≠ 3) (r : ℕ) :
    levelMultiplicitySpan ρ w m κ p ≤
      (levelFiltration ρ w m κ (p + 1)).comap ((leviCurrent ρ).op e r) := by
  let Q := leviCurrent ρ
  let N := levelFiltration ρ w m κ (p + 1)
  have hstable (e : Fin 15) (s : ℕ) {v : V} (hv : v ∈ N) : Q.op e s v ∈ N := by
    exact N.smul_mem _ (levelFiltration_stable ρ w m κ (p + 1)
      (leviColour e) s (leviColour_isLevi e) hv)
  have houter (i : Fin 3) (hi : i ≠ 1) (s : ℕ) {v : V}
      (hv : v ∈ levelMultiplicitySpan ρ w m κ p) :
      Q.op (A3Sector.simpleE i) s v ∈ N := by
    apply levelMultiplicitySpan_le_filtration ρ w m h κ (p + 1)
    simpa [simpleRaisingLevel, hi] using
      levelMultiplicitySpan_simple_raise ρ w m h κ p i s hv
  have hmiddle (s : ℕ) {v : V} (hv : v ∈ levelMultiplicitySpan ρ w m κ p) :
      Q.op 3 s v ∈ levelMultiplicitySpan ρ w m κ p := by
    simpa [simpleRaisingLevel] using
      levelMultiplicitySpan_simple_raise ρ w m h κ p 1 s hv
  intro v hv
  have h0 (s : ℕ) := houter 0 (by decide) s hv
  have h5 (s : ℕ) := houter 2 (by decide) s hv
  have h1 (s : ℕ) : Q.op 1 s v ∈ N := by
    have hc := positiveLevi_pair_commutator Q 1 0 s v
    simp only [show (1 : Fin 3) ≠ 2 by decide, if_false, if_true, zero_add] at hc
    rw [hc]
    exact N.sub_mem (houter 0 (by decide) 0 (hmiddle s hv)) (hstable 3 s (h0 0))
  have h4 (s : ℕ) : Q.op 4 s v ∈ N := by
    have hc := positiveLevi_pair_commutator Q 0 0 s v
    simp only [show (0 : Fin 3) ≠ 2 by decide, show (0 : Fin 3) ≠ 1 by decide,
      if_false, zero_add] at hc
    rw [hc]
    exact N.sub_mem (hstable 3 0 (h5 s)) (houter 2 (by decide) s (hmiddle 0 hv))
  have h2 (s : ℕ) : Q.op 2 s v ∈ N := by
    have hc := positiveLevi_pair_commutator Q 2 0 s v
    simp only [↓reduceIte, zero_add] at hc
    rw [hc]
    exact N.sub_mem (hstable 0 0 (h4 s)) (hstable 4 s (h0 0))
  fin_cases e
  · exact h0 r
  · exact h1 r
  · exact h2 r
  · exact (hne rfl).elim
  · exact h4 r
  · exact h5 r
  all_goals simp at he

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.raisingReplacement_grade_level
#print axioms VOA.DeligneAudit.D4LevelReduction.keyLayer_le_levelMultiplicitySpan
#print axioms VOA.DeligneAudit.D4LevelReduction.levelMultiplicitySpan_le_filtration
#print axioms VOA.DeligneAudit.D4LevelReduction.levelMultiplicitySpan_simple_raise
#print axioms VOA.DeligneAudit.D4LevelReduction.levelMultiplicitySpan_cartan
#print axioms VOA.DeligneAudit.D4LevelReduction.levelMultiplicitySpan_extraCartan
#print axioms VOA.DeligneAudit.D4LevelReduction.positiveLevi_pair_commutator
#print axioms VOA.DeligneAudit.D4LevelReduction.levelMultiplicitySpan_parabolic_raise
