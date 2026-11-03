import VOA.DeligneAudit.D4LevelReductionCoreCartanAction

/-! The honest Grassmannian evaluation surjects onto the bottom Cartan orbit. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- The four reductive Cartan currents commute at arbitrary nonnegative modes. -/
theorem reductiveCartan_commute (i j : Fin 4) (r s : ℕ) (v : V) :
    ρ.op (reductiveCartanColour i) r (ρ.op (reductiveCartanColour j) s v) =
      ρ.op (reductiveCartanColour j) s (ρ.op (reductiveCartanColour i) r v) := by
  apply sub_eq_zero.mp
  rw [ρ.comm]
  have hb : ∀ i j : Fin 4, br i.val j.val = [] := by decide +kernel
  simp [D4sector, fD4, VOA.DeligneAudit.DeligneSector.Sparse.fC,
    VOA.DeligneAudit.DeligneSector.Sparse.fZ,
    VOA.DeligneAudit.DeligneSector.Sparse.sget, reductiveCartanColour, hb]

/-- The extra reductive Cartan is minus an outer semisimple Cartan on the bottom vector. -/
theorem bottomVector_extraCartan (m a c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (r : ℕ) :
    ρ.op (reductiveCartanColour 0) r (bottomVector ρ w a c) =
      -ρ.op (reductiveCartanColour 2) r (bottomVector ρ w a c) := by
  by_cases hr : r = 0
  · subst r
    have hv : bottomVector ρ w a c ∈ keyLayer ρ w (bottomRadicalKey a c 0) := by
      simpa only [bottomVector, bottomRadicalWord_key] using
        radicalWord_mem_key ρ w (bottomRadicalWord a c)
    have hx := extra_weight_key ρ w m h (bottomRadicalKey a c 0) hv
    have hh := cartan_weight_key ρ w m h 0 (bottomRadicalKey a c 0) hv
    have hx' : ρ.op (reductiveCartanColour 0) 0 (bottomVector ρ w a c) =
        -(a : ℂ) • bottomVector ρ w a c := by
      simpa [extraLabel, bottomRadicalKey, reductiveCartanColour] using hx
    have hh' : ρ.op (reductiveCartanColour 2) 0 (bottomVector ρ w a c) =
        (a : ℂ) • bottomVector ρ w a c := by
      simpa [keyLabel, bottomRadicalKey, reductiveCartanColour,
        A3Sector.simpleH, leviColour] using hh
    rw [hx', hh', neg_smul]
  · have hc : ∀ q ∈ bottomRadicalWord a c, q.1 = 1 ∨ q.1 = 5 := by
      simp only [bottomRadicalWord, List.mem_append, List.mem_replicate]
      rintro q (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp
    have hx := bottomWord_extraCartanPowerSum ρ w m h r (Nat.pos_of_ne_zero hr) _ hc
    have hh := bottomWord_cartanPowerSums ρ w m h 0 r (Nat.pos_of_ne_zero hr) _ hc
    simp only [show (0 : Fin 3) ≠ 1 by decide, if_false] at hh
    rw [← hh] at hx
    simpa [bottomVector, reductiveCartanColour, leviCurrent, leviSign,
      A3Sector.simpleH, leviColour] using hx

/-- The extra Cartan identity holds on the entire bottom Cartan orbit. -/
theorem bottomCartanSpan_extraCartan (m a c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (r : ℕ)
    {v : V} (hv : v ∈ bottomCartanSpan ρ w a c) :
    ρ.op (reductiveCartanColour 0) r v = -ρ.op (reductiveCartanColour 2) r v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      induction l with
      | nil => exact bottomVector_extraCartan ρ w m a c h r
      | cons q l ih =>
          simp only [reductiveCartanWord] at ih
          change ρ.op (reductiveCartanColour 0) r
            (ρ.op (reductiveCartanColour q.1) q.2 _) =
              -ρ.op (reductiveCartanColour 2) r
                (ρ.op (reductiveCartanColour q.1) q.2 _)
          rw [reductiveCartan_commute, ih, map_neg, reductiveCartan_commute]
  | zero => simp
  | add x y hx hy hx' hy' => simp only [map_add, hx', hy', neg_add]
  | smul z v hv hv' => simp [map_smul, hv']

/-- Semisimple Cartan currents preserve the image of the universal core evaluator. -/
theorem universalCoreEvaluation_semisimple_stable (a b c : ℕ) (i : Fin 3) (r : ℕ) :
    LinearMap.range (universalCoreEvaluation a b c) ≤
      (LinearMap.range (universalCoreEvaluation a b c)).comap
        ((universalCoreCurrent a b c).op (A3Sector.simpleH i) r) := by
  rintro v ⟨P, rfl⟩
  by_cases hr : r = 0
  · subst r
    obtain ⟨u, hu⟩ := universalCoreEvaluation_range a b c
      (LinearMap.mem_range_self (universalCoreEvaluation a b c) P)
    have he := bottomCartanToLevel_weight _ _ a b c
      (univG_sat D4sector.f (ravFam D4sector (a + b + c) 0)) i u
    rw [hu] at he
    exact ⟨(A3Sector.weightABC a b a i : ℂ) • P, (map_smul _ _ _).trans he.symm⟩
  · exact ⟨coreCartanSymbol a b c i r * P,
      (universalCoreEvaluation_cartan a b c i r (Nat.pos_of_ne_zero hr) P).symm⟩

/-- The raw Cartan action on bottom vectors is compatible with its quotient image. -/
theorem bottomCartanToLevel_rawCartan (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0))
    (i : Fin 4) (r : ℕ) (v : bottomCartanSpan ρ w a c) :
    bottomCartanToLevel ρ w a b c h
      ⟨ρ.op (reductiveCartanColour i) r v, bottomCartanSpan_rawCartan ρ w a c i r v.property⟩ =
        levelCoinvariantOperator ρ w (a + b + c) b (2 * a + b)
          (reductiveCartanColour i) r (reductiveCartanColour_isLevi i)
          (bottomCartanToLevel ρ w a b c h v) := rfl

/-- Raw semisimple Cartan directions agree with the signed Levi representation after quotienting. -/
theorem bottomCartanToLevel_semisimpleCartan (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0))
    (i : Fin 4) (j : Fin 3) (r : ℕ)
    (hcol : reductiveCartanColour i = leviColour (A3Sector.simpleH j))
    (v : bottomCartanSpan ρ w a c) :
    bottomCartanToLevel ρ w a b c h
      ⟨ρ.op (reductiveCartanColour i) r v, bottomCartanSpan_rawCartan ρ w a c i r v.property⟩ =
        (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b)).op (A3Sector.simpleH j) r
          (bottomCartanToLevel ρ w a b c h v) := by
  change levelCoinvariantMap ρ w (a + b + c) b (2 * a + b) _ =
    levelCoinvariantMap ρ w (a + b + c) b (2 * a + b) _
  congr 1
  apply Subtype.ext
  change ρ.op (reductiveCartanColour i) r v =
    (leviCurrent ρ).op (A3Sector.simpleH j) r v
  rw [hcol]
  fin_cases j <;> simp [leviCurrent, leviSign, A3Sector.simpleH]

/-- The core image is closed under all four Cartan directions acting on bottom vectors. -/
theorem universalBottomCartan_coreRange_stable (a b c : ℕ)
    (i : Fin 4) (r : ℕ)
    (v : bottomCartanSpan (demazureCurrent (a + b + c)) (demazureGenerator (a + b + c)) a c)
    (hv : universalBottomCartanMap a b c v ∈ LinearMap.range (universalCoreEvaluation a b c)) :
    universalBottomCartanMap a b c
      ⟨(demazureCurrent (a + b + c)).op (reductiveCartanColour i) r v,
        bottomCartanSpan_rawCartan _ _ a c i r v.property⟩ ∈
          LinearMap.range (universalCoreEvaluation a b c) := by
  have hsimple (j : Fin 3) : (universalCoreCurrent a b c).op (A3Sector.simpleH j) r
      (universalBottomCartanMap a b c v) ∈ LinearMap.range (universalCoreEvaluation a b c) :=
    universalCoreEvaluation_semisimple_stable a b c j r hv
  have houter : universalBottomCartanMap a b c
      ⟨(demazureCurrent (a + b + c)).op (reductiveCartanColour 2) r v,
        bottomCartanSpan_rawCartan _ _ a c 2 r v.property⟩ ∈
          LinearMap.range (universalCoreEvaluation a b c) := by
    rw [bottomCartanToLevel_semisimpleCartan _ _ a b c _ 2 0 r rfl]
    exact hsimple 0
  fin_cases i
  · have he := bottomCartanSpan_extraCartan _ _ (a + b + c) a c
      (univG_sat D4sector.f (ravFam D4sector (a + b + c) 0)) r v.property
    have hsub : (⟨(demazureCurrent (a + b + c)).op (reductiveCartanColour 0) r v,
        bottomCartanSpan_rawCartan _ _ a c 0 r v.property⟩ : bottomCartanSpan _ _ a c) =
        -⟨(demazureCurrent (a + b + c)).op (reductiveCartanColour 2) r v,
          bottomCartanSpan_rawCartan _ _ a c 2 r v.property⟩ := Subtype.ext he
    have hh := congrArg (universalBottomCartanMap a b c) hsub
    simp only [map_neg] at hh
    exact hh.symm ▸ (Submodule.neg_mem _ houter)
  · rw [bottomCartanToLevel_semisimpleCartan _ _ a b c _ _ 1 r rfl]
    exact hsimple 1
  · exact houter
  · rw [bottomCartanToLevel_semisimpleCartan _ _ a b c _ _ 2 r rfl]
    exact hsimple 2

/-- Every bottom Cartan word is represented by the honest Grassmannian pair. -/
theorem universalBottomCartan_word_mem_coreRange (a b c : ℕ) (l : List (Fin 4 × ℕ)) :
    ∀ hv, universalBottomCartanMap a b c
      ⟨reductiveCartanWord (demazureCurrent (a + b + c)) l
        (bottomVector (demazureCurrent (a + b + c)) (demazureGenerator (a + b + c)) a c), hv⟩ ∈
          LinearMap.range (universalCoreEvaluation a b c) := by
  induction l with
  | nil =>
      intro hv
      exact ⟨1, universalCoreEvaluation_one a b c⟩
  | cons q l ih =>
      intro hv
      let v : bottomCartanSpan (demazureCurrent (a + b + c))
          (demazureGenerator (a + b + c)) a c :=
        ⟨reductiveCartanWord _ l (bottomVector _ _ a c), Submodule.subset_span ⟨l, rfl⟩⟩
      exact universalBottomCartan_coreRange_stable a b c q.1 q.2 v (ih v.property)

/-- The honest core-ring evaluation is onto the entire bottom Cartan image. -/
theorem universalCoreEvaluation_range_eq (a b c : ℕ) :
    LinearMap.range (universalCoreEvaluation a b c) =
      LinearMap.range (universalBottomCartanMap a b c) := by
  apply le_antisymm (universalCoreEvaluation_range a b c)
  rintro z ⟨⟨v, hv⟩, rfl⟩
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      exact universalBottomCartan_word_mem_coreRange a b c l _
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy hx' hy' =>
      exact (LinearMap.range (universalCoreEvaluation a b c)).add_mem hx' hy'
  | smul z v hv hv' =>
      exact (LinearMap.range (universalCoreEvaluation a b c)).smul_mem z hv'

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.reductiveCartan_commute
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomVector_extraCartan
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCartanSpan_extraCartan
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_semisimple_stable
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCartanToLevel_rawCartan
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCartanToLevel_semisimpleCartan
#print axioms VOA.DeligneAudit.D4LevelReduction.universalBottomCartan_coreRange_stable
#print axioms VOA.DeligneAudit.D4LevelReduction.universalBottomCartan_word_mem_coreRange
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_range_eq
