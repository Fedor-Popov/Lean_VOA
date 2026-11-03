import VOA.DeligneAudit.D4LevelReductionCoreCoefficientCover

/-! The finite coefficient cover preserves the complete core presentation. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Intertwiners commute with ordered products of positional currents. -/
theorem corePositionProduct_natural {ι : Type}
    (F : ι → ℕ → Module.End ℂ V) (G : ι → ℕ → Module.End ℂ W) (L : V →ₗ[ℂ] W)
    (hL : ∀ i r v, L (F i r v) = G i r (L v)) (is : List ι) (u : ι → ℕ) (v : V) :
    L (SL4T.positionModeProduct F is u v) = SL4T.positionModeProduct G is u (L v) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      simp only [SL4T.positionModeProduct, List.map_cons, List.prod_cons,
        Module.End.mul_apply] at ⊢
      rw [hL]
      exact congrArg (G i (u i)) ih

/-- The converted polynomial evaluator is natural under current intertwiners. -/
theorem coreRaisingEvaluation_natural (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (R : CurrentModule A3Sector.bracketTable W)
    (π : CoreBaseRing a b c →ₗ[ℂ] V) (L : V →ₗ[ℂ] W)
    (hL : ∀ e r v, L (Q.op e r v) = R.op e r (L v))
    (j : ℕ) (P : MvPolynomial (Fin j) (CoreBaseRing a b c)) :
    L (coreRaisingEvaluation Q a b c π j P) =
      coreRaisingEvaluation R a b c (L.comp π) j P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u σ =>
      simp only [coreRaisingEvaluation, SL4T.positionModeEvaluation_monomial]
      exact corePositionProduct_natural _ _ L (fun _ r v => hL 3 r v) _ u (π σ)
  | add P T hP hT => simp only [map_add, hP, hT]

/-- Evaluation at a coefficient is a linear map out of the coefficient-map space. -/
def coreCoefficientAt (a b c : ℕ) (φ : CoreBaseRing a b c) :
    (CoreBaseRing a b c →ₗ[ℂ] V) →ₗ[ℂ] V where
  toFun f := f φ
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Multiplying the coefficient input is multiplication by a constant mode polynomial. -/
theorem coreCoefficientRaising_apply (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing a b c →ₗ[ℂ] V)
    (j : ℕ) (P : MvPolynomial (Fin j) (CoreBaseRing a b c)) (φ : CoreBaseRing a b c) :
    coreRaisingEvaluation (coreCoefficientCurrent a b c Q) a b c
      (coreCoefficientMap a b c π) j P φ =
        coreRaisingEvaluation Q a b c π j (MvPolynomial.C φ * P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial u σ =>
      rw [coreRaisingEvaluation, SL4T.positionModeEvaluation_monomial,
        MvPolynomial.C_mul_monomial, coreRaisingEvaluation,
        SL4T.positionModeEvaluation_monomial]
      have ht := corePositionProduct_natural
        (fun _ r => (coreCoefficientCurrent a b c Q).op 3 r) (fun _ r => Q.op 3 r)
        (coreCoefficientAt a b c φ) (fun _ _ _ => rfl) (List.finRange j) u
        (coreCoefficientMap a b c π σ)
      simpa only [coreCoefficientAt, coreCoefficientMap, coreCoefficientTranslate,
        LinearMap.coe_mk, AddHom.coe_mk, mul_comm σ φ] using ht
  | add P T hP hT => simp only [map_add, LinearMap.add_apply, mul_add, hP, hT]

/-- All defining core relations hold in the full coefficient-map space. -/
theorem coreCoefficientMap_relations (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing a b c →ₗ[ℂ] V)
    (h : CoreRelations Q a b c π) :
    CoreRelations (coreCoefficientCurrent a b c Q) a b c (coreCoefficientMap a b c π) where
  parabolic e he hne r σ := by
    apply LinearMap.ext
    intro φ
    exact h.parabolic e he hne r (σ * φ)
  weight i σ := by
    apply LinearMap.ext
    intro φ
    exact h.weight i (σ * φ)
  cartan := coreCoefficientMap_cartan a b c Q π h.cartan
  converted j P hP := by
    apply LinearMap.ext
    intro φ
    rw [coreCoefficientRaising_apply]
    exact h.converted j ((coreRaisingIdeal a b c j).mul_mem_left (MvPolynomial.C φ) hP)

/-- The coefficient map with codomain restricted to the cyclic cover. -/
def coreCoverMap (a b c : ℕ) (Q : CurrentModule A3Sector.bracketTable V)
    (π : CoreBaseRing a b c →ₗ[ℂ] V) (h : CoreCartanAction Q a b c π) :
    CoreBaseRing a b c →ₗ[ℂ] coreCoefficientSpan a b c Q π :=
  (coreCoefficientMap a b c π).codRestrict _ (coreCoefficientMap_mem a b c Q π h)

/-- Restriction to the cyclic coefficient cover retains every core relation. -/
theorem coreCoverMap_relations (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing a b c →ₗ[ℂ] V)
    (h : CoreRelations Q a b c π) :
    CoreRelations (coreCoverCurrent a b c Q π) a b c (coreCoverMap a b c Q π h.cartan) := by
  have hc := coreCoefficientMap_relations a b c Q π h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he hne r σ
    exact Subtype.ext (hc.parabolic e he hne r σ)
  · intro i σ
    exact Subtype.ext (hc.weight i σ)
  · intro i s hs σ
    exact Subtype.ext (hc.cartan i s hs σ)
  · intro j P hP
    apply Subtype.ext
    have hn := coreRaisingEvaluation_natural a b c (coreCoverCurrent a b c Q π)
      (coreCoefficientCurrent a b c Q) (coreCoverMap a b c Q π h.cartan)
      (coreCoefficientSpan a b c Q π).subtype (fun _ _ _ => rfl) j P
    exact hn.trans (hc.converted j hP)

/-- Current words in the cover are the same coefficient maps as in its ambient space. -/
theorem coreCoverCurrent_word_coe (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing a b c →ₗ[ℂ] V)
    (l : List (Ltr 15)) (v : coreCoefficientSpan a b c Q π) :
    (wordOp (coreCoverCurrent a b c Q π) l v).val =
      wordOp (coreCoefficientCurrent a b c Q) l v.val := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg ((coreCoefficientCurrent a b c Q).op x.1 x.2) ih

/-- The coefficient cover is cyclic on the lifted unit vector. -/
theorem coreCoverMap_cyclic (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing a b c →ₗ[ℂ] V)
    (h : CoreCartanAction Q a b c π) :
    cycSubG (coreCoverCurrent a b c Q π) (coreCoverMap a b c Q π h 1) = ⊤ := by
  apply top_unique
  rintro ⟨v, hv⟩ htop
  clear htop
  have hc : (coreCoverMap a b c Q π h 1).val = π := coreCoefficientMap_one a b c π
  change v ∈ cycSubG (coreCoefficientCurrent a b c Q) π at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      have hw := wordOp_mem_cycSubG (coreCoverCurrent a b c Q π)
        (coreCoverMap a b c Q π h 1) l
      convert hw using 1
      apply Subtype.ext
      rw [coreCoverCurrent_word_coe, hc]
  | zero => exact Submodule.zero_mem _
  | add v w hv hw ihv ihw => exact Submodule.add_mem _ ihv ihw
  | smul z v hv ih => exact Submodule.smul_mem _ z ih

/-- The lifted coefficient map is multiplication applied to its unit vector. -/
theorem coreCoverAction_unit (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing a b c →ₗ[ℂ] V)
    (h : CoreCartanAction Q a b c π) (σ : CoreBaseRing a b c) :
    coreCoverAction a b c Q π h σ (coreCoverMap a b c Q π h 1) =
      coreCoverMap a b c Q π h σ := by
  apply Subtype.ext
  change coreCoefficientTranslate a b c σ (coreCoefficientMap a b c π 1) = _
  rw [coreCoefficientMap_one]
  rfl

/-- The cover inherits the original operator truncation at the site count. -/
theorem coreCoverCurrent_high (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing a b c →ₗ[ℂ] V)
    (hhigh : ∀ e r, a + b + c ≤ r → Q.op e r = 0)
    (e : Fin 15) (r : ℕ) (hr : a + b + c ≤ r) :
    (coreCoverCurrent a b c Q π).op e r = 0 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  apply LinearMap.ext
  intro φ
  change Q.op e r (v.val φ) = 0
  rw [hhigh e r hr, LinearMap.zero_apply]

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.corePositionProduct_natural
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingEvaluation_natural
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoefficientRaising_apply
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoefficientMap_relations
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoverMap_relations
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoverCurrent_word_coe
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoverMap_cyclic
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoverAction_unit
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoverCurrent_high
