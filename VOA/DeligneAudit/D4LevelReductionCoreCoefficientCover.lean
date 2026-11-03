import VOA.DeligneAudit.D4LevelReductionCoreRingGeneration

/-!
A finite coefficient cover carrying the Grassmannian action by current endomorphisms.
The cover retains every coefficient translate of a core map before evaluation at the unit.
This avoids assuming that coefficient multiplication descends to an arbitrary cyclic quotient.
-/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The Grassmannian coefficient ring is finite in every nonnegative triple. -/
theorem coreBaseRing_finite (a b c : ℕ) : FiniteDimensional ℂ (CoreBaseRing a b c) := by
  classical
  obtain ⟨σ, F, hprefix, htop, _⟩ := SL4T.k1_spanning (a + b + c) (a + b) a
    (by omega) (by omega)
  have ht := hprefix (SL4T.cellCatalog (a + b + c) (a + b) a).length le_rfl
  rw [htop, Submodule.restrictScalars_top] at ht
  apply Module.Finite.of_fg_top
  rw [ht]
  apply Submodule.fg_span
  convert (Finset.range (SL4T.cellCatalog (a + b + c) (a + b) a).length).finite_toSet.image σ
    using 1
  ext x
  simp [Set.mem_image, eq_comm]

/-- Currents act pointwise on linear maps out of the coefficient ring. -/
def coreCoefficientCurrent (a b c : ℕ) (Q : CurrentModule A3Sector.bracketTable V) :
    CurrentModule A3Sector.bracketTable (CoreBaseRing a b c →ₗ[ℂ] V) where
  op e r :=
    { toFun := fun f => (Q.op e r).comp f
      map_add' := by
        intro f g
        apply LinearMap.ext
        intro φ
        exact (Q.op e r).map_add (f φ) (g φ)
      map_smul' := by
        intro z f
        apply LinearMap.ext
        intro φ
        exact (Q.op e r).map_smul z (f φ) }
  comm e f r s v := by
    apply LinearMap.ext
    intro φ
    exact Q.comm e f r s (v φ)

/-- Multiplication translates the coefficient argument of a linear map. -/
def coreCoefficientTranslate (a b c : ℕ) (σ : CoreBaseRing a b c) :
    Module.End ℂ (CoreBaseRing a b c →ₗ[ℂ] V) where
  toFun f :=
    { toFun := fun φ => f (σ * φ)
      map_add' := by intros; simp [mul_add]
      map_smul' := by intros; simp }
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The lifted coefficient map records multiplication before applying the original map. -/
def coreCoefficientMap (a b c : ℕ) (π : CoreBaseRing a b c →ₗ[ℂ] V) :
    CoreBaseRing a b c →ₗ[ℂ] (CoreBaseRing a b c →ₗ[ℂ] V) where
  toFun σ := coreCoefficientTranslate a b c σ π
  map_add' := by
    intro σ τ
    apply LinearMap.ext
    intro φ
    exact (congrArg π (add_mul σ τ φ)).trans (map_add π _ _)
  map_smul' := by
    intro z σ
    apply LinearMap.ext
    intro φ
    exact (congrArg π (smul_mul_assoc z σ φ)).trans (map_smul π _ _)

theorem coreCoefficientMap_one (a b c : ℕ) (π : CoreBaseRing a b c →ₗ[ℂ] V) :
    coreCoefficientMap a b c π 1 = π := by
  apply LinearMap.ext
  intro φ
  exact congrArg π (one_mul φ)

/-- Coefficient translation commutes with every current word. -/
theorem coreCoefficientTranslate_word (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (σ : CoreBaseRing a b c)
    (l : List (Ltr 15)) (f : CoreBaseRing a b c →ₗ[ℂ] V) :
    coreCoefficientTranslate a b c σ (wordOp (coreCoefficientCurrent a b c Q) l f) =
      wordOp (coreCoefficientCurrent a b c Q) l (coreCoefficientTranslate a b c σ f) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      change (coreCoefficientCurrent a b c Q).op x.1 x.2
        (coreCoefficientTranslate a b c σ (wordOp (coreCoefficientCurrent a b c Q) l f)) = _
      rw [ih]
      rfl

/-- The lifted coefficient map has the same positive Cartan symbols. -/
theorem coreCoefficientMap_cartan (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing a b c →ₗ[ℂ] V)
    (h : CoreCartanAction Q a b c π) :
    CoreCartanAction (coreCoefficientCurrent a b c Q) a b c (coreCoefficientMap a b c π) := by
  intro i s hs σ
  apply LinearMap.ext
  intro φ
  simpa only [coreCoefficientCurrent, coreCoefficientMap, coreCoefficientTranslate,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, mul_assoc] using h i s hs (σ * φ)

/-- The cyclic cover before evaluation at the unit coefficient. -/
def coreCoefficientSpan (a b c : ℕ) (Q : CurrentModule A3Sector.bracketTable V)
    (π : CoreBaseRing a b c →ₗ[ℂ] V) : Submodule ℂ (CoreBaseRing a b c →ₗ[ℂ] V) :=
  cycSubG (coreCoefficientCurrent a b c Q) π

/-- All coefficient translates lie in the cyclic cover. -/
theorem coreCoefficientMap_mem (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing a b c →ₗ[ℂ] V)
    (h : CoreCartanAction Q a b c π) (σ : CoreBaseRing a b c) :
    coreCoefficientMap a b c π σ ∈ coreCoefficientSpan a b c Q π := by
  have ht := coreEvaluation_mem_cyclic (coreCoefficientCurrent a b c Q) a b c
    (coreCoefficientMap a b c π) (coreCoefficientMap_cartan a b c Q π h) σ
  rwa [coreCoefficientMap_one] at ht

/-- The cover is stable under the whole coefficient ring. -/
theorem coreCoefficientSpan_translate (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing a b c →ₗ[ℂ] V)
    (h : CoreCartanAction Q a b c π) (σ : CoreBaseRing a b c) :
    coreCoefficientSpan a b c Q π ≤
      (coreCoefficientSpan a b c Q π).comap (coreCoefficientTranslate a b c σ) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  change coreCoefficientTranslate a b c σ
    (wordOp (coreCoefficientCurrent a b c Q) l π) ∈ coreCoefficientSpan a b c Q π
  rw [coreCoefficientTranslate_word]
  exact wordOp_mem_of_inv _ _ (cycSubG_inv _ π)
    (coreCoefficientMap_mem a b c Q π h σ) l

/-- The coefficient cover is finite whenever its target module is finite. -/
theorem coreCoefficientSpan_finite (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing a b c →ₗ[ℂ] V)
    [FiniteDimensional ℂ V] : FiniteDimensional ℂ (coreCoefficientSpan a b c Q π) := by
  haveI := coreBaseRing_finite a b c
  infer_instance

/-- The current representation restricted to the cyclic coefficient cover. -/
def coreCoverCurrent (a b c : ℕ) (Q : CurrentModule A3Sector.bracketTable V)
    (π : CoreBaseRing a b c →ₗ[ℂ] V) :
    CurrentModule A3Sector.bracketTable (coreCoefficientSpan a b c Q π) where
  op e r := ((coreCoefficientCurrent a b c Q).op e r).restrict
    (fun _ hv => cycSubG_inv _ π e r hv)
  comm e f r s v := by
    apply Subtype.ext
    simpa using (coreCoefficientCurrent a b c Q).comm e f r s v.val

/-- The Grassmannian ring acts on the cover by linear endomorphisms. -/
def coreCoverAction (a b c : ℕ) (Q : CurrentModule A3Sector.bracketTable V)
    (π : CoreBaseRing a b c →ₗ[ℂ] V) (h : CoreCartanAction Q a b c π) :
    CoreBaseRing a b c →ₐ[ℂ] Module.End ℂ (coreCoefficientSpan a b c Q π) where
  toFun σ := (coreCoefficientTranslate a b c σ).restrict
    (fun _ hv => coreCoefficientSpan_translate a b c Q π h σ hv)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro φ
    exact congrArg f.val (one_mul φ)
  map_mul' := by
    intro σ τ
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro φ
    change f.val ((σ * τ) * φ) = f.val (τ * (σ * φ))
    rw [mul_assoc, mul_left_comm]
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro φ
    exact (congrArg f.val (zero_mul φ)).trans (map_zero f.val)
  map_add' := by
    intro σ τ
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro φ
    exact (congrArg f.val (add_mul σ τ φ)).trans (map_add _ _ _)
  commutes' := by
    intro z
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro φ
    change f.val (algebraMap ℂ (CoreBaseRing a b c) z * φ) = z • f.val φ
    simpa only [Algebra.smul_def] using f.val.map_smul z φ

/-- Every coefficient operator on the cover commutes with every Levi current. -/
theorem coreCoverAction_commute (a b c : ℕ) (Q : CurrentModule A3Sector.bracketTable V)
    (π : CoreBaseRing a b c →ₗ[ℂ] V) (h : CoreCartanAction Q a b c π)
    (σ : CoreBaseRing a b c) (e : Fin 15) (r : ℕ) :
    Commute (coreCoverAction a b c Q π h σ) ((coreCoverCurrent a b c Q π).op e r) := by
  rfl

/-- Evaluation at the unit sends the coefficient cover to the original module. -/
def coreCoverEvaluation (a b c : ℕ) (Q : CurrentModule A3Sector.bracketTable V)
    (π : CoreBaseRing a b c →ₗ[ℂ] V) : coreCoefficientSpan a b c Q π →ₗ[ℂ] V where
  toFun f := f.val 1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem coreCoefficientCurrent_word_apply (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (l : List (Ltr 15))
    (f : CoreBaseRing a b c →ₗ[ℂ] V) (φ : CoreBaseRing a b c) :
    wordOp (coreCoefficientCurrent a b c Q) l f φ = wordOp Q l (f φ) := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg (Q.op x.1 x.2) ih

/-- Evaluation at the unit is onto every cyclic core target. -/
theorem coreCoverEvaluation_surjective (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing a b c →ₗ[ℂ] V)
    (hcyclic : cycSubG Q (π 1) = ⊤) :
    Function.Surjective (coreCoverEvaluation a b c Q π) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hcyclic]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  exact ⟨⟨wordOp (coreCoefficientCurrent a b c Q) l π,
    wordOp_mem_cycSubG _ π l⟩, coreCoefficientCurrent_word_apply a b c Q l π 1⟩

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.coreBaseRing_finite
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoefficientMap_one
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoefficientTranslate_word
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoefficientMap_cartan
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoefficientMap_mem
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoefficientSpan_translate
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoefficientSpan_finite
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoverAction_commute
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoefficientCurrent_word_apply
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoverEvaluation_surjective
