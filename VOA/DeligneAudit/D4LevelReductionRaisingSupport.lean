import VOA.DeligneAudit.D4LevelReductionCartanGeneration

/-! The middle raising depth of a bottom Cartan vector is bounded by its central letter count. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

/-- A middle raising replacement either creates a vanishing simple-root letter or consumes a
central letter. -/
theorem middleRaisingReplacement_support (r : ℕ) {l q : List (Fin 6 × ℕ)}
    (h : RaiseReplaces 1 r l q)
    (hl : ∀ t ∈ l, t.1 = 1 ∨ t.1 = 4 ∨ t.1 = 5) :
    0 < q.countP (fun t => t.1 = 0) ∨
      ((∀ t ∈ q, t.1 = 1 ∨ t.1 = 4 ∨ t.1 = 5) ∧
        q.countP (fun t => t.1 = 5) + 1 = l.countP (fun t => t.1 = 5)) := by
  induction h with
  | @head j s k n l h =>
      fin_cases j <;> simp [raiseAction] at h
      · obtain ⟨rfl, rfl⟩ := h
        left
        simp
      · obtain ⟨rfl, rfl⟩ := h
        right
        constructor
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · simp
          · exact hl t (List.mem_cons_of_mem _ ht)
        · simp
  | @tail j s l q h ih =>
      have ht := hl (j, s) (by simp)
      rcases ih (fun t ht => hl t (List.mem_cons_of_mem _ ht)) with he | ⟨hq, hz⟩
      · left
        simp only [List.countP_cons]
        split <;> omega
      · right
        constructor
        · intro t ht'
          rcases List.mem_cons.mp ht' with rfl | ht'
          · exact ht
          · exact hq t ht'
        · simp only [List.countP_cons]
          split <;> omega

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- The ordered product of middle simple raising currents at specified modes. -/
def middleRaisingProduct (rs : List ℕ) : Module.End ℂ V :=
  (rs.map fun r => ρ.op (leviColour (A3Sector.simpleE 1)) r).prod

/-- More middle raising currents than central letters annihilate every radical word. -/
theorem middleRaisingProduct_word_zero (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (rs : List ℕ)
    (l : List (Fin 6 × ℕ))
    (hl : ∀ t ∈ l, t.1 = 1 ∨ t.1 = 4 ∨ t.1 = 5)
    (hlen : l.countP (fun t => t.1 = 5) < rs.length) :
    middleRaisingProduct ρ rs (radicalWord ρ w l) = 0 := by
  induction rs using List.reverseRecOn generalizing l with
  | nil => simp at hlen
  | append_singleton rs r ih =>
      have hk : raiseWordSpan ρ w 1 r l ≤ LinearMap.ker (middleRaisingProduct ρ rs) := by
        rw [raiseWordSpan, Submodule.span_le]
        rintro v ⟨q, hq, rfl⟩
        change middleRaisingProduct ρ rs (radicalWord ρ w q) = 0
        rcases middleRaisingReplacement_support r hq hl with he | ⟨hc, hz⟩
        · rw [radicalWord_zero_of_E ρ w m h q he, map_zero]
        · exact ih q hc (by simp only [List.length_append, List.length_singleton] at hlen; omega)
      have hz := hk (simple_raise_word_span ρ w m h 1 r l)
      simpa only [middleRaisingProduct, List.map_append, List.map_cons, List.map_nil,
        List.prod_append, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply,
        LinearMap.mem_ker] using hz

/-- The positional bottom word has precisely the prescribed number of central letters. -/
theorem bottomMode_centralCount (a c : ℕ) (d : BottomModeSlot a c →₀ ℕ) :
    (shapedModes (bottomModeShape a c) Finset.univ.toList d).countP (fun t => t.1 = 5) = c := by
  classical
  rw [ksCountP_sum]
  simp only [shapedModes, List.map_map, Function.comp_def, Finset.sum_map_toList]
  simp only [decide_eq_true_eq]
  change (∑ i : Fin c ⊕ Fin a, if bottomModeShape a c i = 5 then 1 else 0) = c
  rw [Fintype.sum_sum_type]
  simp [bottomModeShape]

/-- The middle raising-depth bound holds on every bottom mode polynomial before taking quotients. -/
theorem middleRaisingProduct_bottomEvaluation_zero (m a c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (rs : List ℕ) (hrs : c < rs.length)
    (P : MvPolynomial (BottomModeSlot a c) ℂ) :
    middleRaisingProduct ρ rs (xyzEvaluation ρ w (bottomModeShape a c) P) = 0 := by
  induction P using MvPolynomial.induction_on' with
  | monomial d z =>
      have he : (monomial d z : MvPolynomial (BottomModeSlot a c) ℂ) =
          z • modeMonomial (BottomModeSlot a c) d := by simp [modeMonomial, smul_monomial]
      rw [he, map_smul, map_smul]
      have hz : middleRaisingProduct ρ rs
          (radicalWord ρ w (shapedModes (bottomModeShape a c) Finset.univ.toList d)) = 0 := by
        apply middleRaisingProduct_word_zero ρ w m h rs
        · rintro t ht
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
          exact bottomModeShape_colours a c u
        · rwa [bottomMode_centralCount]
      change z • middleRaisingProduct ρ rs
        (xyzEvaluation ρ w (bottomModeShape a c) (modeMonomial (BottomModeSlot a c) d)) = 0
      rw [show xyzEvaluation ρ w (bottomModeShape a c) (modeMonomial (BottomModeSlot a c) d) =
          radicalWord ρ w (shapedModes (bottomModeShape a c) Finset.univ.toList d) from
        modeWordEvaluation_monomial _ _ d, hz, smul_zero]
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_zero]

/-- The level quotient intertwines every semisimple Levi word. -/
theorem levelCoinvariantMap_word (m : ℕ) (κ p : ℤ) (l : List (Fin 15 × ℕ))
    (v : levelFiltration ρ w m κ p) :
    wordOp (levelCoinvariantCurrent ρ w m κ p) l (levelCoinvariantMap ρ w m κ p v) =
      levelCoinvariantMap ρ w m κ p (wordOp (levelLeviCurrent ρ w m κ p) l v) := by
  induction l with
  | nil => rfl
  | cons q l ih =>
      change (levelCoinvariantCurrent ρ w m κ p).op q.1 q.2
        (wordOp (levelCoinvariantCurrent ρ w m κ p) l (levelCoinvariantMap ρ w m κ p v)) = _
      rw [ih]
      rfl

/-- The restriction of a middle raising word has its original ambient operator product. -/
theorem levelLeviCurrent_middleWord (m : ℕ) (κ p : ℤ) (rs : List ℕ)
    (v : levelFiltration ρ w m κ p) :
    (↑(wordOp (levelLeviCurrent ρ w m κ p) (rs.map fun r => ((3 : Fin 15), r)) v) : V) =
      middleRaisingProduct ρ rs v := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      change (leviCurrent ρ).op 3 r
        (↑(wordOp (levelLeviCurrent ρ w m κ p) (rs.map fun r => ((3 : Fin 15), r)) v) : V) = _
      rw [ih]
      simp [middleRaisingProduct, leviCurrent, leviSign, A3Sector.simpleE, leviColour,
        Module.End.mul_apply]

/-- Every overfull raising word vanishes on the actual evaluated Grassmannian image. -/
theorem coreGrassmannianEvaluation_overfull (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0))
    (rs : List ℕ) (hrs : c < rs.length) (P : CoreBaseRing a b c) :
    wordOp (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b))
      (rs.map fun r => (3, r)) (coreGrassmannianEvaluation ρ w a b c h P) = 0 := by
  induction P using Quotient.inductionOn' with
  | h P =>
      change wordOp (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b))
        (rs.map fun r => (3, r))
        (levelCoinvariantMap ρ w (a + b + c) b (2 * a + b)
          (bottomCartanLift ρ w a b c h
            (bottomSymmetricToCartan ρ w a b c h
              (bottomElementaryModes a c (leftComplementAlphabet P))))) = 0
      rw [levelCoinvariantMap_word]
      have hz : wordOp (levelLeviCurrent ρ w (a + b + c) b (2 * a + b))
          (rs.map fun r => (3, r))
          (bottomCartanLift ρ w a b c h
            (bottomSymmetricToCartan ρ w a b c h
              (bottomElementaryModes a c (leftComplementAlphabet P)))) = 0 := by
        apply Subtype.ext
        rw [levelLeviCurrent_middleWord]
        exact middleRaisingProduct_bottomEvaluation_zero ρ w (a + b + c) a c h rs hrs _
      rw [hz, map_zero]

/-- Positional raising evaluation is the corresponding ordered current word. -/
theorem middlePositionEvaluation_word {B : Type*} [CommRing B] [Algebra ℂ B]
    (Q : CurrentModule A3Sector.bracketTable V) (β : B →ₗ[ℂ] V)
    {σ : Type*} (is : List σ) (u : σ →₀ ℕ) (z : B) :
    SL4T.positionModeEvaluation (fun _ s => Q.op 3 s) is β (monomial u z) =
      wordOp Q ((is.map fun i => u i).map fun r => (3, r)) (β z) := by
  rw [SL4T.positionModeEvaluation_monomial]
  induction is with
  | nil => rfl
  | cons i is ih =>
      simpa only [SL4T.positionModeProduct, List.map_cons, List.prod_cons,
        Module.End.mul_apply, wordOp] using congrArg (Q.op 3 (u i)) ih

/-- The converted evaluator is zero when its raising length exceeds the central count. -/
theorem universalCoreEvaluation_raising_overfull (a b c j : ℕ) (hj : c < j) :
    coreRaisingEvaluation (universalCoreCurrent a b c) a b c (universalCoreEvaluation a b c) j =
      0 := by
  apply LinearMap.ext
  intro P
  induction P using MvPolynomial.induction_on' with
  | monomial u z =>
      change SL4T.positionModeEvaluation (fun _ s => (universalCoreCurrent a b c).op 3 s)
        (List.finRange j) (universalCoreEvaluation a b c) (monomial u z) = 0
      rw [middlePositionEvaluation_word]
      exact coreGrassmannianEvaluation_overfull _ _ a b c _ _ (by simpa using hj) z
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_zero, LinearMap.zero_apply]

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.middleRaisingReplacement_support
#print axioms VOA.DeligneAudit.D4LevelReduction.middleRaisingProduct_word_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomMode_centralCount
#print axioms VOA.DeligneAudit.D4LevelReduction.middleRaisingProduct_bottomEvaluation_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.levelCoinvariantMap_word
#print axioms VOA.DeligneAudit.D4LevelReduction.levelLeviCurrent_middleWord
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianEvaluation_overfull
#print axioms VOA.DeligneAudit.D4LevelReduction.middlePositionEvaluation_word
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_raising_overfull
