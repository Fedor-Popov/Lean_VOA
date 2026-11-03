/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2Fusion
import VOA.DeligneAudit.DeligneCharacterExceptional
import VOA.DeligneAudit.DeligneCharacterD4Final
import VOA.DeligneAudit.DeligneCharacterD4Wp12

/-!
# The star inputs in `≤` form

Downstream, the star identity `D_N = target_N` is only ever used through `D_N ≤ target_N ≤ dim W_N`
(`demazureBoundFor_of_Q` is `(hstar.eq N).trans_le (hlow.le N)`). This file sharpens the named residuals
to the one-sided form:

* `StarBoundQ hilb c := ∀ N, D_N ≤ c N` and `demazureBoundFor_of_bound`;
* `StarIdentityQ.toStarBoundQ`: the `=` versions are corollaries;
* per type: `G2StarBound`, `F4StarBound`, `E6StarBound`, `E7StarBound`, `E8StarBound`
  (against `mldeCoeff h∨`), and for `D₄` both `D4DemazureLeSchur` (against `d4SchurQ`) and
  `D4StarBound` (against `mldeCoeff 6`, equivalent via `d4SchurQ_eq_mldeCoeff_holds`);
* capstones in `≤` form, siblings of the existing ones (which are unchanged):
  `classicallyFree_of_starBound` (generic, sibling of `classicallyFree_of_sectorFusion`),
  `g2_classicallyFree_of_starBound`, `e{6,7,8}DemazureBoundFor_of_starBound`,
  `d4DemazureBound_of_le`, `d4DemazureBoundFor_of_starBound`.
-/

namespace VOA.DeligneAudit.DeligneCharacter

open VertexOperatorAlgebra

/-- **The star input in `≤` form**: `D_N ≤ c_N` for all `N`. -/
def StarBoundQ (hilb : ℕ → ℕ → ℕ) (c : ℕ → ℚ) : Prop :=
  ∀ N, (demazureSumCoeff hilb N : ℚ) ≤ c N

theorem StarIdentityQ.toStarBoundQ {hilb : ℕ → ℕ → ℕ} {c : ℕ → ℚ} (h : StarIdentityQ hilb c) :
    StarBoundQ hilb c :=
  fun N => (h.eq N).le

theorem demazureBoundFor_of_bound {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : VertexOperatorAlgebra V} {hilb : ℕ → ℕ → ℕ} {target : ℕ → ℚ}
    (hstar : StarBoundQ hilb target) (hlow : TargetLowerBoundQ W target) :
    DemazureBoundFor W hilb :=
  ⟨fun N => by
    have h := (hstar N).trans (hlow.le N)
    exact_mod_cast h⟩

/-- `demazureBoundFor_of_Q` is the special case `StarIdentityQ ⟹ StarBoundQ`. -/
theorem demazureBoundFor_of_Q' {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : VertexOperatorAlgebra V} {hilb : ℕ → ℕ → ℕ} {target : ℕ → ℚ}
    (hstar : StarIdentityQ hilb target) (hlow : TargetLowerBoundQ W target) :
    DemazureBoundFor W hilb :=
  demazureBoundFor_of_bound hstar.toStarBoundQ hlow

/-! ## Per-type residuals in `≤` form -/

abbrev G2StarBound : Prop := StarBoundQ g2DemazureHilb (mldeCoeff 4)
abbrev F4StarBound : Prop := StarBoundQ f4DemazureHilb (mldeCoeff 9)
abbrev E6StarBound : Prop := StarBoundQ e6DemazureHilb (mldeCoeff 12)
abbrev E7StarBound : Prop := StarBoundQ e7DemazureHilb (mldeCoeff 18)
abbrev E8StarBound : Prop := StarBoundQ e8DemazureHilb (mldeCoeff 30)

theorem g2StarBound_of_identity (h : G2StarIdentity) : G2StarBound := h.toStarBoundQ
theorem f4StarBound_of_identity (h : F4StarIdentity) : F4StarBound := h.toStarBoundQ
theorem e6StarBound_of_identity (h : E6StarIdentity) : E6StarBound := h.toStarBoundQ
theorem e7StarBound_of_identity (h : E7StarIdentity) : E7StarBound := h.toStarBoundQ
theorem e8StarBound_of_identity (h : E8StarIdentity) : E8StarBound := h.toStarBoundQ

/-- `D₄`, Schur form: `D_N ≤ d4SchurQ N`. -/
def D4DemazureLeSchur : Prop := ∀ N, (demazureSumCoeff d4DemazureHilb N : ℚ) ≤ D4K.d4SchurQ N

/-- `D₄`, MLDE form. -/
abbrev D4StarBound : Prop := StarBoundQ d4DemazureHilb (mldeCoeff 6)

theorem d4DemazureLeSchur_of_eq (h : D4DemazureEqSchur) : D4DemazureLeSchur := fun N => (h N).le

theorem d4StarBound_iff_leSchur : D4StarBound ↔ D4DemazureLeSchur := by
  unfold D4StarBound StarBoundQ D4DemazureLeSchur
  simp only [D4Wp.d4SchurQ_eq_mldeCoeff_holds]

/-! ## Capstones in `≤` form -/

section
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

/-- `D₄` sibling of `d4DemazureBound` (in `DeligneCharacterD4Final`). -/
theorem d4DemazureBound_of_le (hle : D4DemazureLeSchur) (hS : D4ClassS W) :
    DemazureBoundFor W d4DemazureHilb :=
  ⟨fun N => by
    have h := (hle N).trans (hS.le N)
    exact_mod_cast h⟩

/-- `D₄` via the AK lower bound (the `d4_targetLowerBoundQ_of_quartic`) instead of class S. -/
theorem d4DemazureBoundFor_of_starBound (hB : D4StarBound)
    (hc : W.centralCharge = -2 * (((6 : ℕ) : ℂ) + 1)) (hvac : W.vacuum ≠ 0) {κ : ℂ}
    (hrel : DeligneMLDE.VacuumQuarticRelation W κ) : DemazureBoundFor W d4DemazureHilb :=
  demazureBoundFor_of_bound hB (DeligneMLDE.d4_targetLowerBoundQ_of_quartic W hc hvac hrel)

theorem e6DemazureBoundFor_of_starBound (hB : E6StarBound) (hlow : E6TargetLowerBound W) :
    DemazureBoundFor W e6DemazureHilb :=
  demazureBoundFor_of_bound hB hlow

theorem e7DemazureBoundFor_of_starBound (hB : E7StarBound) (hlow : E7TargetLowerBound W) :
    DemazureBoundFor W e7DemazureHilb :=
  demazureBoundFor_of_bound hB hlow

theorem e8DemazureBoundFor_of_starBound (hB : E8StarBound) (hlow : E8TargetLowerBound W) :
    DemazureBoundFor W e8DemazureHilb :=
  demazureBoundFor_of_bound hB hlow

end

end VOA.DeligneAudit.DeligneCharacter

namespace VOA.DeligneAudit.DeligneCarrier

open VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneCharacter

/-- **Generic capstone, `≤` form**: sibling of `classicallyFree_of_sectorFusion` taking the star
input as `StarBoundQ hilb target` and the AK-type lower bound `TargetLowerBoundQ W target`. -/
theorem classicallyFree_of_starBound {case : HigherRankDeligneCase} {V : Type*}
    [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V} (P : CurrentC2Presentation case W)
    (S : DeligneSectorData) (hilb : ℕ → ℕ → ℕ) {target : ℕ → ℚ}
    (hsurj : CurrentJetSurjectivity case W P)
    (hgeom : GeometricCarrierEmbedding case W P
      (CarrierEmbedding.Carrier S.toDeligneCarrierData.rel))
    (hU5 : FusionModuleBoundG S (fusionOf (hilbSeries hilb))) (hD : DivisorComparisonG S)
    (hB : StarBoundQ hilb target) (hlow : TargetLowerBoundQ W target) :
    CaseClassicallyFree case W P ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩).toRingHom = P.ideal :=
  classicallyFree_of_sectorFusion P S hilb hsurj hgeom hU5 hD (demazureBoundFor_of_bound hB hlow)

/-- **The `G₂` headline, `≤` form**: sibling of `g2_classicallyFree` with the star input as
`G2StarBound` (implied by the fermionic split via `g2StarBound_of_identity`). -/
theorem g2_classicallyFree_of_starBound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (P : CurrentC2Presentation .G2 W) (S : DeligneSectorData)
    (hsurj : CurrentJetSurjectivity .G2 W P)
    (hgeom : GeometricCarrierEmbedding .G2 W P
      (CarrierEmbedding.Carrier S.toDeligneCarrierData.rel))
    (hU5 : FusionModuleBoundG S g2FusionF) (hD : DivisorComparisonG S)
    (hc : W.centralCharge = -2 * (((4 : ℕ) : ℂ) + 1)) (hvac : W.vacuum ≠ 0) {κ : ℂ}
    (hrel : DeligneMLDE.VacuumQuarticRelation W κ) (hB : G2StarBound) :
    CaseClassicallyFree .G2 W P ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩).toRingHom = P.ideal :=
  classicallyFree_of_starBound P S g2DemazureHilb hsurj hgeom hU5 hD hB
    (DeligneMLDE.g2TargetLowerBound_of_quartic W hc hvac hrel)

end VOA.DeligneAudit.DeligneCarrier

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.demazureBoundFor_of_bound
#print axioms VOA.DeligneAudit.DeligneCharacter.d4StarBound_iff_leSchur
#print axioms VOA.DeligneAudit.DeligneCharacter.d4DemazureBoundFor_of_starBound
#print axioms VOA.DeligneAudit.DeligneCarrier.classicallyFree_of_starBound
#print axioms VOA.DeligneAudit.DeligneCarrier.g2_classicallyFree_of_starBound
end AxiomAudit
