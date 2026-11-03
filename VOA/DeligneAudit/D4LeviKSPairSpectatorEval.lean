import VOA.DeligneAudit.D4LeviKSPairSpectatorAssembly

/-! Match the labelled Y/XZ polynomial evaluator with the word operator. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

theorem pairXZSource_injective (a b c : ℕ) :
    Function.Injective (pairXZSource a b c) := by
  intro x y h
  rcases x with x | z <;> rcases y with y | z <;>
    simp [pairXZSource] at h ⊢ <;> exact h

theorem pairYSlot_injective (a b c : ℕ) :
    Function.Injective (pairYSlot a b c) := by
  intro x y h
  simpa [pairYSlot] using h

theorem pairXZSource_ne_ySlot (a b c : ℕ)
    (x : PairXZ a b c) (y : Fin b) :
    pairXZSource a b c x ≠ pairYSlot a b c y := by
  rcases x with x | z <;> simp [pairXZSource, pairYSlot]

theorem pairSourceModes_xz (a b c : ℕ)
    (d : Fin b →₀ ℕ) (e : PairXZ a b c →₀ ℕ)
    (x : PairXZ a b c) :
    (d.mapDomain (pairYSlot a b c) +
      e.mapDomain (pairXZSource a b c))
        (pairXZSource a b c x) = e x := by
  rw [Finsupp.add_apply]
  have hnot : pairXZSource a b c x ∉ Set.range (pairYSlot a b c) := by
    rintro ⟨y, hy⟩
    exact pairXZSource_ne_ySlot a b c x y hy.symm
  rw [Finsupp.mapDomain_notin_range d _ hnot]
  rw [Finsupp.mapDomain_apply (pairXZSource_injective a b c)]
  simp

theorem pairSourceModes_y (a b c : ℕ)
    (d : Fin b →₀ ℕ) (e : PairXZ a b c →₀ ℕ)
    (y : Fin b) :
    (d.mapDomain (pairYSlot a b c) +
      e.mapDomain (pairXZSource a b c))
        (pairYSlot a b c y) = d y := by
  rw [Finsupp.add_apply]
  rw [Finsupp.mapDomain_apply (pairYSlot_injective a b c)]
  have hnot : pairYSlot a b c y ∉ Set.range (pairXZSource a b c) := by
    rintro ⟨x, hx⟩
    exact pairXZSource_ne_ySlot a b c x y hx
  rw [Finsupp.mapDomain_notin_range e _ hnot]
  simp

theorem pairYModeWord_perm (b : ℕ) (d : Fin b →₀ ℕ) :
    ((Finset.univ.toList : List (Fin b)).map
      fun y => ((4 : Fin 6), d y)).Perm
      (yModeWord ((List.range b).map (pairYExponent b d))) := by
  have hp : (Finset.univ.toList : List (Fin b)).Perm (List.finRange b) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact Finset.nodup_toList _
    · exact List.nodup_finRange b
    · ext y
      simp
  have heq : (List.finRange b).map (fun y => ((4 : Fin 6), d y)) =
      yModeWord ((List.range b).map (pairYExponent b d)) := by
    apply List.ext_getElem
    · simp [yModeWord]
    · intro i hi
      have hib : i < b := by simpa using hi
      simp [yModeWord, pairYExponent, hib,
        List.getElem_finRange]
  simpa only [heq] using hp.map (fun y => ((4 : Fin 6), d y))

private theorem pairSource_slots_perm (a b c : ℕ) :
    ((Finset.univ.toList : List (PairXZ a b c)).map
        (pairXZSource a b c) ++
      (Finset.univ.toList : List (Fin b)).map (pairYSlot a b c)).Perm
      (Finset.univ.toList : List (PairSource a b c)) := by
  apply List.perm_of_nodup_nodup_toFinset_eq
  · apply List.Nodup.append
    · exact (Finset.nodup_toList _).map (by
        intro x y h
        rcases x with x | z <;> rcases y with y | z <;>
          simp [pairXZSource] at h ⊢ <;> exact h)
    · exact (Finset.nodup_toList _).map (by
        intro x y h
        simpa [pairYSlot] using h)
    · intro x hx hy
      rcases List.mem_map.mp hx with ⟨u, _, rfl⟩
      rcases List.mem_map.mp hy with ⟨v, _, heq⟩
      rcases u with u | z <;>
        simp [pairXZSource, pairYSlot] at heq
  · exact Finset.nodup_toList _
  · ext t
    rcases t with x | (y | z)
    · rcases x with p | x
      · simp [pairXZSource, pairYSlot]
      · simp [pairXZSource, pairYSlot]
    · simp [pairXZSource, pairYSlot]
    · simp [pairXZSource, pairYSlot]

theorem pairSourceModes_word_perm (a b c : ℕ)
    (d : Fin b →₀ ℕ) (e : PairXZ a b c →₀ ℕ) :
    (shapedModes (pairSourceShape a b c) Finset.univ.toList
      (d.mapDomain (pairYSlot a b c) +
        e.mapDomain (pairXZSource a b c))).Perm
      (shapedModes (pairXZRecolourShape a b c 0)
        Finset.univ.toList e ++
          yModeWord ((List.range b).map (pairYExponent b d))) := by
  let D := d.mapDomain (pairYSlot a b c) +
    e.mapDomain (pairXZSource a b c)
  have hp := (pairSource_slots_perm a b c).symm.map
    (fun t => (pairSourceShape a b c t, D t))
  have hx (x : PairXZ a b c) :
      (pairSourceShape a b c (pairXZSource a b c x),
        D (pairXZSource a b c x)) =
      (pairXZRecolourShape a b c 0 x, e x) := by
    rw [show D (pairXZSource a b c x) = e x from
      pairSourceModes_xz a b c d e x]
    rcases x with x | z <;>
      simp [pairSourceShape, pairXZRecolourShape_zero, pairXZSource]
  have hy (y : Fin b) :
      (pairSourceShape a b c (pairYSlot a b c y),
        D (pairYSlot a b c y)) = ((4 : Fin 6), d y) := by
    rw [show D (pairYSlot a b c y) = d y from
      pairSourceModes_y a b c d e y]
    rfl
  have hword :
      (shapedModes (pairSourceShape a b c) Finset.univ.toList D).Perm
        (shapedModes (pairXZRecolourShape a b c 0)
          Finset.univ.toList e ++
            (Finset.univ.toList : List (Fin b)).map
              fun y => ((4 : Fin 6), d y)) := by
    simpa only [shapedModes, List.map_append, List.map_map,
      Function.comp_def, hx, hy] using hp
  exact hword.trans (List.Perm.append_left _ (pairYModeWord_perm b d))

theorem pairY_xz_modeMonomial (a b c : ℕ)
    (d : Fin b →₀ ℕ) (e : PairXZ a b c →₀ ℕ) :
    pairYFinsuppMonomial a b c d *
      rename (pairXZSource a b c)
        (modeMonomial (PairXZ a b c) e) =
      modeMonomial (PairSource a b c)
        (d.mapDomain (pairYSlot a b c) +
          e.mapDomain (pairXZSource a b c)) := by
  simp [pairYFinsuppMonomial, pairYSlot, modeMonomial,
    rename_monomial, monomial_mul]
  rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pairY_xz_modeMonomial_evaluation
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c : ℕ) (d : Fin b →₀ ℕ)
    (e : PairXZ a b c →₀ ℕ) :
    xyzEvaluation ρ w (pairSourceShape a b c)
        (pairYFinsuppMonomial a b c d *
          rename (pairXZSource a b c)
            (modeMonomial (PairXZ a b c) e)) =
      pairXZRecolourOperator ρ a b c 0
        (modeMonomial (PairXZ a b c) e)
        (pairRadicalOp ρ
          (yModeWord ((List.range b).map (pairYExponent b d))) w) := by
  rw [pairY_xz_modeMonomial]
  simp only [xyzEvaluation, modeWordEvaluation_monomial]
  change radicalWord ρ w
      (shapedModes (pairSourceShape a b c) Finset.univ.toList
        (d.mapDomain (pairYSlot a b c) +
          e.mapDomain (pairXZSource a b c))) =
    pairWordOpEvaluation ρ
      (pairPolynomialWords (pairXZRecolourShape a b c 0)
        (modeMonomial (PairXZ a b c) e))
        (pairRadicalOp ρ
          (yModeWord ((List.range b).map (pairYExponent b d))) w)
  rw [pairPolynomialWords_monomial, pairWordOpEvaluation_single]
  rw [← Module.End.mul_apply, ← pairRadicalOp_append,
    pairRadicalOp_apply]
  exact radicalWord_perm ρ w (pairSourceModes_word_perm a b c d e)

theorem pairY_xz_evaluation
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c : ℕ) (d : Fin b →₀ ℕ)
    (Q : MvPolynomial (PairXZ a b c) ℂ) :
    xyzEvaluation ρ w (pairSourceShape a b c)
        (pairYFinsuppMonomial a b c d *
          rename (pairXZSource a b c) Q) =
      pairXZRecolourOperator ρ a b c 0 Q
        (pairRadicalOp ρ
          (yModeWord ((List.range b).map (pairYExponent b d))) w) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial e z =>
      have hm : (monomial e z : MvPolynomial (PairXZ a b c) ℂ) =
          z • modeMonomial (PairXZ a b c) e := by
        simp [modeMonomial, smul_monomial]
      rw [hm, map_smul, mul_smul_comm, map_smul,
        map_smul, LinearMap.smul_apply]
      exact congrArg (z • ·)
        (pairY_xz_modeMonomial_evaluation ρ w a b c d e)
  | add P Q ihP ihQ =>
      simpa only [map_add, mul_add, LinearMap.add_apply] using
        congrArg₂ (· + ·) ihP ihQ

theorem pairY_evaluation_bridge
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c : ℕ) : PairYEvaluationBridge ρ w a b c := by
  intro d Q
  exact pairY_xz_evaluation ρ w a b c d Q

/-- PAIR for every symmetric key, every `m`, and every current module
    satisfying the D4 highest-weight relations. -/
theorem pairKernelPrefix_of_sat
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c deg : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c deg) :
    PairKernelPrefix ρ w m i a b c := by
  exact pairKernelPrefix_of_sat_of_evalBridge ρ w m i a b c deg
    h hi hkey (pairY_evaluation_bridge ρ w a b c)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairSource_slots_perm
#print axioms VOA.DeligneAudit.D4Levi.pairXZSource_injective
#print axioms VOA.DeligneAudit.D4Levi.pairYSlot_injective
#print axioms VOA.DeligneAudit.D4Levi.pairXZSource_ne_ySlot
#print axioms VOA.DeligneAudit.D4Levi.pairSourceModes_xz
#print axioms VOA.DeligneAudit.D4Levi.pairSourceModes_y
#print axioms VOA.DeligneAudit.D4Levi.pairYModeWord_perm
#print axioms VOA.DeligneAudit.D4Levi.pairSourceModes_word_perm
#print axioms VOA.DeligneAudit.D4Levi.pairY_xz_modeMonomial
#print axioms VOA.DeligneAudit.D4Levi.pairY_xz_modeMonomial_evaluation
#print axioms VOA.DeligneAudit.D4Levi.pairY_xz_evaluation
#print axioms VOA.DeligneAudit.D4Levi.pairY_evaluation_bridge
#print axioms VOA.DeligneAudit.D4Levi.pairKernelPrefix_of_sat
