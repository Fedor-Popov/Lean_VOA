import VOA.Examples.AffineSl2GoodFiltration
import VOA.Examples.AffineSl2NotSimple85
import VOA.Core.InvariantFormRadical
import VOA.Core.GradedUnitarity

/-!
# First graded-form facts at level `-8/5`

This file deliberately records only the first unconditional affine calculations needed by
the graded-unitarity project.  It specializes the corrected universal affine filtration to
the simple quotient and computes the canonical invariant bilinear form on the three
weight-one current states.

The quotient filtration below is the induced filtration; no equality with an independently
defined intrinsic quotient filtration is asserted.  Likewise, the bilinear calculation is
not yet a Hermitian-signature theorem: that requires a compatible compact real structure and
descent of the form to the simple quotient.
-/

namespace VOA.AffineVOA.GradedUnitarityLow

open VOA.VertexOperatorAlgebra
open VOA.AffineVOA.Inst
open VOA.AffineVOA.Vir
open VOA.AffineVOA.CorrectedR
open VOA.Sl2NotSimple85
open VOA.WakLY

noncomputable section

/-- The universal affine vertex operator algebra at the first nontrivial comparison level
`k = -8/5`. -/
abbrev W85 : VertexOperatorAlgebra (WakModule (-8 / 5 : ℂ)) :=
  affineSl2VOA_closed (-8 / 5 : ℂ) hk85

/-- The normalized canonical invariant bilinear form on the universal algebra at `k = -8/5`. -/
noncomputable def canonicalForm85 : InvariantForm W85 :=
  canonicalInvariantForm vacuum85_ne_zero qp85

/-- On weight-one current states the canonical form is `8/5` times the chosen Killing form.
The sign change from the level `-8/5` comes from the FHL adjoint convention. -/
theorem canonicalForm85_currentState (a b : Fin 3) :
    canonicalForm85.form (currentState (-8 / 5 : ℂ) a)
      (currentState (-8 / 5 : ℂ) b) = (8 / 5 : ℂ) * kappa a b := by
  have h := eval_oneMode_grading1_FHL vacuum85_ne_zero qp85
    (currentState_mem_grading (-8 / 5 : ℂ) hk85 a)
    (currentState_mem_grading (-8 / 5 : ℂ) hk85 b)
  rw [smul_currentState_eq_J, currentState_def, J1_neg1_vac] at h
  change ((-8 / 5 : ℂ) * kappa a b) • W85.vacuum =
      (-canonicalForm85.form (currentState (-8 / 5 : ℂ) a)
        (currentState (-8 / 5 : ℂ) b)) • W85.vacuum at h
  have h0 : (((-8 / 5 : ℂ) * kappa a b) -
      (-canonicalForm85.form (currentState (-8 / 5 : ℂ) a)
        (currentState (-8 / 5 : ℂ) b))) • W85.vacuum = 0 := by
    rw [sub_smul, h, sub_self]
  have hc := (smul_eq_zero.mp h0).resolve_right vacuum85_ne_zero
  linear_combination hc

/-! ## Descent of the canonical bilinear form -/

/-- The maximal graded ideal at level `-8/5`. -/
abbrev I85 : Submodule ℂ (WakModule (-8 / 5 : ℂ)) := QuotVOA.maxGradedIdeal W85

/-- The simple affine quotient at level `-8/5`. -/
abbrev L85 : VertexOperatorAlgebra
    (WakModule (-8 / 5 : ℂ) ⧸ I85) := QuotVOA.maxQuotientVOA W85

private theorem leftRadical85_eq_I85 :
    InvariantForm.leftRadical canonicalForm85 = I85 := by
  simpa only [I85, W85, canonicalForm85] using
    LiRadical.leftRadical_eq_maxGradedIdeal
      (canonicalInvariantForm_isFullyInvariant vacuum85_ne_zero qp85)
      (canonicalInvariantForm_normalized vacuum85_ne_zero qp85)

private theorem rightRadical85_eq_I85 :
    SingVec.rightRadical canonicalForm85 = I85 := by
  simpa only [I85, W85, canonicalForm85] using
    LiRadical.rightRadical_eq_maxGradedIdeal
      (canonicalInvariantForm_isFullyInvariant vacuum85_ne_zero qp85)
      (canonicalInvariantForm_normalized vacuum85_ne_zero qp85)

private theorem I85_le_leftRadical :
    I85 ≤ InvariantForm.leftRadical canonicalForm85 := leftRadical85_eq_I85.ge

private theorem I85_le_rightRadical :
    I85 ≤ SingVec.rightRadical canonicalForm85 := rightRadical85_eq_I85.ge

/-- The canonical form after descent in its second variable. -/
noncomputable def simpleCanonicalForm85Snd :
    (WakModule (-8 / 5 : ℂ) ⧸ I85) →ₗ[ℂ]
      WakModule (-8 / 5 : ℂ) →ₗ[ℂ] ℂ :=
  I85.liftQ canonicalForm85.form.flip <| by
    change I85 ≤ SingVec.rightRadical canonicalForm85
    exact I85_le_rightRadical

@[simp] theorem simpleCanonicalForm85Snd_mkQ
    (y x : WakModule (-8 / 5 : ℂ)) :
    simpleCanonicalForm85Snd (I85.mkQ y) x = canonicalForm85.form x y := rfl

set_option maxHeartbeats 800000 in
/-- The canonical bilinear form descends through the maximal ideal in both variables. -/
noncomputable def simpleCanonicalBilin85 :
    (WakModule (-8 / 5 : ℂ) ⧸ I85) →ₗ[ℂ]
      (WakModule (-8 / 5 : ℂ) ⧸ I85) →ₗ[ℂ] ℂ :=
  I85.liftQ simpleCanonicalForm85Snd.flip <| by
    intro x hx
    refine LinearMap.mem_ker.mpr (LinearMap.ext fun q => ?_)
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I85 q
    change canonicalForm85.form x y = 0
    have hzero := InvariantForm.mem_leftRadical.mp (I85_le_leftRadical hx)
    exact LinearMap.congr_fun hzero y

@[simp] theorem simpleCanonicalBilin85_mkQ
    (x y : WakModule (-8 / 5 : ℂ)) :
    simpleCanonicalBilin85 (I85.mkQ x) (I85.mkQ y) =
      canonicalForm85.form x y := rfl

/-- The descended bilinear form is an invariant form on the simple quotient. -/
noncomputable def simpleCanonicalForm85 : InvariantForm L85 where
  form := simpleCanonicalBilin85
  virasoro_adj := by
    intro n a b
    obtain ⟨x, rfl⟩ := I85.mkQ_surjective a
    obtain ⟨y, rfl⟩ := I85.mkQ_surjective b
    change simpleCanonicalBilin85
        (I85.mkQ (W85.L n x)) (I85.mkQ y) =
      simpleCanonicalBilin85 (I85.mkQ x) (I85.mkQ (W85.L (-n) y))
    rw [simpleCanonicalBilin85_mkQ, simpleCanonicalBilin85_mkQ]
    exact canonicalForm85.virasoro_adj n x y

@[simp] theorem simpleCanonicalForm85_mkQ
    (x y : WakModule (-8 / 5 : ℂ)) :
    simpleCanonicalForm85.form (I85.mkQ x) (I85.mkQ y) =
      canonicalForm85.form x y := rfl

/-- Quotienting by the two-sided radical makes the descended form nondegenerate. -/
theorem simpleCanonicalBilin85_nondegenerate :
    LinearMap.Nondegenerate simpleCanonicalBilin85 := by
  constructor
  · intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective I85 q
    rw [Submodule.Quotient.mk_eq_zero]
    rw [← leftRadical85_eq_I85]
    rw [InvariantForm.mem_leftRadical]
    apply LinearMap.ext
    intro y
    have h := hq (I85.mkQ y)
    simpa only [simpleCanonicalBilin85_mkQ] using h
  · intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I85 q
    rw [Submodule.Quotient.mk_eq_zero]
    rw [← rightRadical85_eq_I85]
    rw [SingVec.mem_rightRadical]
    intro x
    have h := hq (I85.mkQ x)
    simpa only [simpleCanonicalBilin85_mkQ] using h

/-! ## The compact current calculation

The following construction is intentionally confined to the three-dimensional current-coordinate
space.  It is not a `RealStructure W85`: constructing that object would require a semilinear map
on the entire affine vacuum module, preservation of its defining ideal, and mode covariance.
-/

/-- Coefficients of a linear combination of the three Chevalley current states. -/
abbrev CurrentCoords := Fin 3 → ℂ

/-- Compact conjugation on horizontal `sl₂` current coordinates:
`e ↦ -f`, `f ↦ -e`, and `h ↦ -h`, with complex-conjugated coefficients. -/
noncomputable def compactCurrentConj :
    CurrentCoords →ₛₗ[starRingEnd ℂ] CurrentCoords where
  toFun z := fun a => match a with
    | 0 => -(starRingEnd ℂ) (z 1)
    | 1 => -(starRingEnd ℂ) (z 0)
    | 2 => -(starRingEnd ℂ) (z 2)
  map_add' z w := by
    funext a
    fin_cases a <;> simp <;> abel
  map_smul' c z := by
    funext a
    fin_cases a <;> simp [smul_eq_mul, map_mul]

@[simp] theorem compactCurrentConj_E (z : CurrentCoords) :
    compactCurrentConj z colE = -(starRingEnd ℂ) (z colF) := rfl

@[simp] theorem compactCurrentConj_F (z : CurrentCoords) :
    compactCurrentConj z colF = -(starRingEnd ℂ) (z colE) := rfl

@[simp] theorem compactCurrentConj_H (z : CurrentCoords) :
    compactCurrentConj z colH = -(starRingEnd ℂ) (z colH) := rfl

@[simp] theorem compactCurrentConj_sq (z : CurrentCoords) :
    compactCurrentConj (compactCurrentConj z) = z := by
  funext a
  fin_cases a <;> simp

/-- A current-coordinate vector evaluated in the universal affine VOA. -/
noncomputable def currentCoordinates85 :
    CurrentCoords →ₗ[ℂ] WakModule (-8 / 5 : ℂ) where
  toFun z := ∑ a : Fin 3, z a • currentState (-8 / 5 : ℂ) a
  map_add' z w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c z := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

/-- Bilinear current Gram matrix in arbitrary coordinates. -/
theorem canonicalForm85_currentCoordinates (z w : CurrentCoords) :
    canonicalForm85.form (currentCoordinates85 z) (currentCoordinates85 w) =
      ∑ a : Fin 3, ∑ b : Fin 3,
        z a * w b * ((8 / 5 : ℂ) * kappa a b) := by
  change canonicalForm85.form
      (∑ a : Fin 3, z a • currentState (-8 / 5 : ℂ) a)
      (∑ b : Fin 3, w b • currentState (-8 / 5 : ℂ) b) = _
  simp only [map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, canonicalForm85_currentState]
  simp only [Fin.sum_univ_three, kappa]
  ring

/-- The signed Hermitian form on current coordinates.  The minus sign is the corrected-degree-one
sign `(-1)^1`; it turns the compact-conjugated bilinear form into a positive form. -/
noncomputable def compactCurrentSignedForm85 : SesqForm CurrentCoords where
  toFun z w := (8 / 5 : ℂ) *
    ((starRingEnd ℂ) (z colE) * w colE +
      (starRingEnd ℂ) (z colF) * w colF +
      2 * (starRingEnd ℂ) (z colH) * w colH)
  add_left z z' w := by simp only [Pi.add_apply, map_add]; ring
  smul_left c z w := by simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
  add_right z w w' := by simp only [Pi.add_apply]; ring
  smul_right c z w := by simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- Exact compatibility of the local compact conjugation with the canonical invariant bilinear
form on current states.  This is a local current-space identity, not mode covariance on `W85`. -/
theorem compactCurrentSignedForm85_eq_canonical (z w : CurrentCoords) :
    compactCurrentSignedForm85 z w =
      -canonicalForm85.form (currentCoordinates85 (compactCurrentConj z))
        (currentCoordinates85 w) := by
  rw [canonicalForm85_currentCoordinates]
  simp only [compactCurrentSignedForm85, SesqForm.coe_mk, Fin.sum_univ_three,
    compactCurrentConj_E, compactCurrentConj_F, compactCurrentConj_H, kappa]
  ring

/-- The diagonal of the local signed form is an explicit positive weighted sum of squared
absolute values. -/
theorem compactCurrentSignedForm85_self (z : CurrentCoords) :
    compactCurrentSignedForm85 z z =
      (((8 / 5 : ℝ) *
        (Complex.normSq (z colE) + Complex.normSq (z colF) +
          2 * Complex.normSq (z colH)) : ℝ) : ℂ) := by
  change (8 / 5 : ℂ) *
      ((starRingEnd ℂ) (z colE) * z colE +
        (starRingEnd ℂ) (z colF) * z colF +
        2 * (starRingEnd ℂ) (z colH) * z colH) = _
  push_cast
  simp_rw [← Complex.normSq_eq_conj_mul_self]
  have hH := Complex.normSq_eq_conj_mul_self (z := z colH)
  linear_combination -(16 / 5 : ℂ) * hH

/-- Genuine positivity of the signed Hermitian form on the complete three-dimensional current
coordinate space.  Together with `compactCurrentSignedForm85_eq_canonical`, this is the first
local affine graded-unitarity theorem at `k=-8/5`.  It still does not supply a VOA real structure. -/
theorem compactCurrentSignedForm85_positive :
    IsPosOn compactCurrentSignedForm85 (⊤ : Submodule ℂ CurrentCoords) := by
  intro z _ hz
  have hex : ∃ a : Fin 3, z a ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    funext a
    exact h a
  obtain ⟨a, ha⟩ := hex
  have hsum : 0 < Complex.normSq (z colE) + Complex.normSq (z colF) +
      2 * Complex.normSq (z colH) := by
    have hE := Complex.normSq_nonneg (z colE)
    have hF := Complex.normSq_nonneg (z colF)
    have hH := Complex.normSq_nonneg (z colH)
    fin_cases a
    · have hp := Complex.normSq_pos.mpr (by simpa [colE] using ha)
      nlinarith
    · have hp := Complex.normSq_pos.mpr (by simpa [colF] using ha)
      nlinarith
    · have hp := Complex.normSq_pos.mpr (by simpa [colH] using ha)
      nlinarith
  refine ⟨(8 / 5 : ℝ) *
      (Complex.normSq (z colE) + Complex.normSq (z colF) +
        2 * Complex.normSq (z colH)), ?_, compactCurrentSignedForm85_self z⟩
  exact mul_pos (by norm_num) hsum

/-- The corrected universal filtration induces an unconditional good filtration on the simple
quotient at `k = -8/5`. -/
noncomputable def simpleCorrectedGoodFiltration85 :
    GoodFiltration (QuotVOA.maxQuotientVOA W85) :=
  correctedAffineRQuotientGoodFiltration (-8 / 5 : ℂ) hk85
    (QuotVOA.maxGradedIdeal W85) (QuotVOA.maxGradedIdeal_isIdeal W85)
    (QuotVOA.maxGradedIdeal_isGradedIdeal W85)

end

end VOA.AffineVOA.GradedUnitarityLow
