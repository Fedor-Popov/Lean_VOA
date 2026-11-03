import VOA.DeligneAudit.D4LevelReductionParabolic

/-! The bottom vector and parabolic relations in the actual universal level coinvariant. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- High Levi images of any Levi invariant subspace are Levi invariant. -/
theorem currentTail_levi_invariant (S : Submodule ℂ V)
    (hS : ∀ a r, IsLevi a → S ≤ S.comap (ρ.op a r))
    (N : ℕ) (a : Fin 28) (s : ℕ) (ha : IsLevi a) :
    currentTail ρ S {c | IsLevi c} N ≤
      (currentTail ρ S {c | IsLevi c} N).comap (ρ.op a s) := by
  rw [currentTail, Submodule.span_le]
  rintro z ⟨b, hb, r, hr, v, hv, rfl⟩
  change ρ.op a s (ρ.op b r v) ∈ currentTail ρ S {c | IsLevi c} N
  rw [sub_eq_iff_eq_add.mp (ρ.comm a b s r v)]
  apply Submodule.add_mem
  · apply Submodule.sum_mem
    intro c _
    by_cases hc : IsLevi c
    · exact Submodule.smul_mem _ _ (currentTail_contains ρ S _ N hc (by omega) hv)
    · rw [reductiveLevi_bracket_support a b c ha hb hc, zero_smul]
      exact Submodule.zero_mem _
  · exact currentTail_contains ρ S _ N hb hr (hS a s ha hv)

/-- The ambient relations defining the truncated level piece. -/
abbrev levelCoinvariantRelations (m : ℕ) (κ p : ℤ) : Submodule ℂ V :=
  levelFiltration ρ w m κ (p + 1) ⊔
    currentTail ρ (levelFiltration ρ w m κ p) {c | IsLevi c} m

/-- Higher levels together with the high-current images form a Levi submodule. -/
theorem levelCoinvariantRelations_stable (m : ℕ) (κ p : ℤ) (a : Fin 28) (r : ℕ)
    (ha : IsLevi a) : levelCoinvariantRelations ρ w m κ p ≤
      (levelCoinvariantRelations ρ w m κ p).comap (ρ.op a r) := by
  apply sup_le
  · exact (levelFiltration_stable ρ w m κ (p + 1) a r ha).trans
      (Submodule.comap_mono le_sup_left)
  · exact (currentTail_levi_invariant ρ _
      (fun a r ha => levelFiltration_stable ρ w m κ p a r ha) m a r ha).trans
        (Submodule.comap_mono le_sup_right)

/-- The restricted raw Levi operator on a filtration term. -/
def levelRestrictedOperator (m : ℕ) (κ p : ℤ) (a : Fin 28) (r : ℕ)
    (ha : IsLevi a) : Module.End ℂ (levelFiltration ρ w m κ p) :=
  (ρ.op a r).restrict (fun _ hv => levelFiltration_stable ρ w m κ p a r ha hv)

/-- The induced raw Levi operator on the quotient by higher levels and high currents. -/
def levelCoinvariantOperator (m : ℕ) (κ p : ℤ) (a : Fin 28) (r : ℕ)
    (ha : IsLevi a) : Module.End ℂ (TruncatedLevelPiece ρ w m κ p) :=
  let R := (levelCoinvariantRelations ρ w m κ p).comap
    (levelFiltration ρ w m κ p).subtype
  R.mapQ R (levelRestrictedOperator ρ w m κ p a r ha)
    (fun v hv => levelCoinvariantRelations_stable ρ w m κ p a r ha hv)

/-- The quotient map from the level filtration term. -/
def levelCoinvariantMap (m : ℕ) (κ p : ℤ) :
    levelFiltration ρ w m κ p →ₗ[ℂ] TruncatedLevelPiece ρ w m κ p :=
  ((levelCoinvariantRelations ρ w m κ p).comap
    (levelFiltration ρ w m κ p).subtype).mkQ

/-- The quotient map intertwines every raw Levi current. -/
theorem levelCoinvariantOperator_map (m : ℕ) (κ p : ℤ) (a : Fin 28) (r : ℕ)
    (ha : IsLevi a) (v : levelFiltration ρ w m κ p) :
    levelCoinvariantOperator ρ w m κ p a r ha (levelCoinvariantMap ρ w m κ p v) =
      levelCoinvariantMap ρ w m κ p (levelRestrictedOperator ρ w m κ p a r ha v) := rfl

/-- The signed semisimple Levi current representation on a filtration term. -/
def levelLeviCurrent (m : ℕ) (κ p : ℤ) :
    CurrentModule A3Sector.bracketTable (levelFiltration ρ w m κ p) where
  op e r := (leviCurrent ρ).op e r |>.restrict (fun _ hv =>
    (levelFiltration ρ w m κ p).smul_mem _
      (levelFiltration_stable ρ w m κ p (leviColour e) r (leviColour_isLevi e) hv))
  comm a b r s v := by
    apply Subtype.ext
    simpa using (leviCurrent ρ).comm a b r s (v : V)

/-- The semisimple Levi current representation on the level coinvariant. -/
def levelCoinvariantCurrent (m : ℕ) (κ p : ℤ) :
    CurrentModule A3Sector.bracketTable (TruncatedLevelPiece ρ w m κ p) :=
  quotRepG (levelLeviCurrent ρ w m κ p)
    ((levelCoinvariantRelations ρ w m κ p).comap
      (levelFiltration ρ w m κ p).subtype) (fun e r v hv =>
        (levelCoinvariantRelations ρ w m κ p).smul_mem _
          (levelCoinvariantRelations_stable ρ w m κ p
            (leviColour e) r (leviColour_isLevi e) hv))

/-- The simple-root and highest-root radical letters in the bottom word. -/
def bottomRadicalWord (a c : ℕ) : List (Fin 6 × ℕ) :=
  List.replicate a (1, 0) ++ List.replicate c (5, 0)

/-- The radical key of the bottom multiplicity space at arbitrary degree. -/
def bottomRadicalKey (a c d : ℕ) : RadicalKey := ⟨0, a, 0, 0, 0, c, d⟩

theorem bottomRadicalWord_key (a c : ℕ) :
    wordKey (bottomRadicalWord a c) = bottomRadicalKey a c 0 := by
  simp [wordKey, bottomRadicalWord, bottomRadicalKey, List.countP_append, List.countP_replicate]

/-- The distinguished bottom vector, with all current modes zero. -/
def bottomVector (a c : ℕ) : V := radicalWord ρ w (bottomRadicalWord a c)

/-- The bottom vector has grade equal to the middle label and level twice the outer label. -/
theorem bottomVector_mem_multiplicity (a b c : ℕ) :
    bottomVector ρ w a c ∈ levelMultiplicitySpan ρ w (a + b + c) b (2 * a + b) := by
  apply keyLayer_le_levelMultiplicitySpan ρ w (a + b + c) b (2 * a + b)
    (bottomRadicalKey a c 0)
  · simp [keyAlphaGrade, keyDepth, bottomRadicalKey]
  · simp [keyLeviLevel, bottomRadicalKey]
    ring
  · simpa only [bottomVector, bottomRadicalWord_key] using
      radicalWord_mem_key ρ w (bottomRadicalWord a c)

/-- The four raw Cartan colours in the reductive Levi. -/
def reductiveCartanColour (i : Fin 4) : Fin 28 := ⟨i.val, by omega⟩

theorem reductiveCartanColour_isLevi (i : Fin 4) : IsLevi (reductiveCartanColour i) := by
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact leviColour_isLevi 13
  · exact leviColour_isLevi 12
  · exact leviColour_isLevi 14

/-- Every raw Cartan mode preserves the multiplicity space. -/
theorem levelMultiplicitySpan_rawCartan (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ) (i : Fin 4) (r : ℕ) :
    levelMultiplicitySpan ρ w m κ p ≤
      (levelMultiplicitySpan ρ w m κ p).comap (ρ.op (reductiveCartanColour i) r) := by
  fin_cases i
  · exact levelMultiplicitySpan_extraCartan ρ w m h κ p r
  · simpa [leviCurrent, leviSign, A3Sector.simpleH, leviColour, reductiveCartanColour] using
      levelMultiplicitySpan_cartan ρ w m h κ p 1 r
  · simpa [leviCurrent, leviSign, A3Sector.simpleH, leviColour, reductiveCartanColour] using
      levelMultiplicitySpan_cartan ρ w m h κ p 0 r
  · simpa [leviCurrent, leviSign, A3Sector.simpleH, leviColour, reductiveCartanColour] using
      levelMultiplicitySpan_cartan ρ w m h κ p 2 r

/-- A word in all four reductive Cartan current directions. -/
def reductiveCartanWord (l : List (Fin 4 × ℕ)) (v : V) : V :=
  wordOp ρ (l.map fun q => (reductiveCartanColour q.1, q.2)) v

/-- The Cartan orbit of the bottom vector, before passing to the level quotient. -/
def bottomCartanSpan (a c : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ l, v = reductiveCartanWord ρ l (bottomVector ρ w a c)}

/-- The complete Cartan orbit of the bottom vector stays in the exact-level space. -/
theorem bottomCartanSpan_le_multiplicity (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0)) :
    bottomCartanSpan ρ w a c ≤ levelMultiplicitySpan ρ w (a + b + c) b (2 * a + b) := by
  rw [bottomCartanSpan, Submodule.span_le]
  rintro v ⟨l, rfl⟩
  induction l with
  | nil => exact bottomVector_mem_multiplicity ρ w a b c
  | cons q l ih =>
      exact levelMultiplicitySpan_rawCartan ρ w (a + b + c) h b (2 * a + b) q.1 q.2 ih

/-- A bottom Cartan vector regarded as a vector of the filtration term. -/
def bottomCartanLift (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0))
    (v : bottomCartanSpan ρ w a c) : levelFiltration ρ w (a + b + c) b (2 * a + b) :=
  ⟨v, levelMultiplicitySpan_le_filtration ρ w (a + b + c) h b (2 * a + b)
    (bottomCartanSpan_le_multiplicity ρ w a b c h v.property)⟩

/-- The positive parabolic radical kills the entire bottom Cartan orbit in the level quotient. -/
theorem bottomCartan_parabolic_annihilation (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0))
    (v : bottomCartanSpan ρ w a c) (e : Fin 15) (he : e.val < 6) (hne : e ≠ 3) (r : ℕ) :
    (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b)).op e r
      (levelCoinvariantMap ρ w (a + b + c) b (2 * a + b)
        (bottomCartanLift ρ w a b c h v)) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply Submodule.mem_sup_left
  exact levelMultiplicitySpan_parabolic_raise ρ w (a + b + c) h b (2 * a + b)
    e he hne r (bottomCartanSpan_le_multiplicity ρ w a b c h v.property)

/-- The universal bottom Cartan orbit satisfies the positive parabolic relations for all labels. -/
theorem universalBottomCartan_parabolic_annihilation (a b c : ℕ)
    (v : bottomCartanSpan (demazureCurrent (a + b + c))
      (demazureGenerator (a + b + c)) a c)
    (e : Fin 15) (he : e.val < 6) (hne : e ≠ 3) (r : ℕ) :
    (levelCoinvariantCurrent (demazureCurrent (a + b + c))
      (demazureGenerator (a + b + c)) (a + b + c) b (2 * a + b)).op e r
        (levelCoinvariantMap _ _ (a + b + c) b (2 * a + b)
          (bottomCartanLift _ _ a b c
            (univG_sat D4sector.f (ravFam D4sector (a + b + c) 0)) v)) = 0 :=
  bottomCartan_parabolic_annihilation _ _ a b c
    (univG_sat D4sector.f (ravFam D4sector (a + b + c) 0)) v e he hne r

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.currentTail_levi_invariant
#print axioms VOA.DeligneAudit.D4LevelReduction.levelCoinvariantRelations_stable
#print axioms VOA.DeligneAudit.D4LevelReduction.levelCoinvariantOperator_map
#print axioms VOA.DeligneAudit.D4LevelReduction.levelLeviCurrent
#print axioms VOA.DeligneAudit.D4LevelReduction.levelCoinvariantCurrent
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomRadicalWord_key
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomVector_mem_multiplicity
#print axioms VOA.DeligneAudit.D4LevelReduction.reductiveCartanColour_isLevi
#print axioms VOA.DeligneAudit.D4LevelReduction.levelMultiplicitySpan_rawCartan
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCartanSpan_le_multiplicity
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCartan_parabolic_annihilation
#print axioms VOA.DeligneAudit.D4LevelReduction.universalBottomCartan_parabolic_annihilation
