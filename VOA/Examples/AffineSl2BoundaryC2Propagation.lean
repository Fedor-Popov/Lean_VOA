/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2BoundaryC2Reduction

/-!
# Uniform horizontal propagation for the boundary affine `sl₂` `C₂` ideal

This file separates the easy and hard inclusions in the boundary `C₂` presentation.

Suppose an ideal `I` of the universal affine VOA contains a vector `s` whose `C₂` symbol is a
nonzero multiple of `e Cas^n`.  The image of `I` in the universal `C₂` algebra is a Poisson
ideal.  Applying the horizontal lowering operator twice therefore shows that it contains all
three relations

```text
Cas^n e,  Cas^n h,  Cas^n f.
```

Consequently the candidate boundary ideal is contained in the quotient-symbol kernel.  This is
the relation-containment direction only.  Exactness still needs the reverse inclusion saying
that every `C₂` class coming from `I` belongs to the displayed ideal.  The latter is the genuine
PBW/representation-theory theorem, exposed below as `BoundaryC2ImageUpper`.

Nothing in this file assumes that containment implies equality.
-/

namespace VOA

open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace QuotVOA

variable {W : VertexOperatorAlgebra 𝒱} {I : Submodule ℂ 𝒱}

/-! ## The image of a VOA ideal is a Poisson ideal -/

/-- The `C₂` image of a VOA ideal is closed under bracketing on the left by an arbitrary
`C₂` class.  This is zero-mode absorption upstairs. -/
theorem A₂IdealImage_bracket_mem (hI : W.IsIdeal I) (p q : A₂ W)
    (hq : q ∈ A₂IdealImage hI) :
    A₂bracket W p q ∈ A₂IdealImage hI := by
  obtain ⟨u, rfl⟩ := mk₂_surjective W p
  obtain ⟨i, hiI, rfl⟩ := Submodule.mem_map.mp hq
  rw [A₂bracket_mk]
  refine Submodule.mem_map.mpr ⟨poissonBracket W u i, ?_, rfl⟩
  exact hI u i 0 hiI

/-- The right-bracket version follows from antisymmetry. -/
theorem A₂IdealImage_bracket_mem_right (hI : W.IsIdeal I) (p q : A₂ W)
    (hp : p ∈ A₂IdealImage hI) :
    A₂bracket W p q ∈ A₂IdealImage hI := by
  rw [A₂bracket_antisymm]
  exact Submodule.neg_mem _ (A₂IdealImage_bracket_mem hI q p hp)

end QuotVOA

namespace AffineSl2BoundaryC2

open VOA.AffineVOA
open VOA.AffineVOA.Inst
open VOA.QuasiLisseSl2
open VOA.SingVec
open VOA.Sl2Pres
open VOA.Sl2Symbol

noncomputable section

variable (k : ℂ) (hk : k + 2 ≠ 0)

private abbrev W : VertexOperatorAlgebra (WakModule k) := affineSl2VOA_closed k hk

/-! ## Universal horizontal compatibility -/

/-- The universal affine symbol map intertwines the classical lowering derivation with the
Poisson bracket by the current class `[f]`. -/
theorem symbolAlg_adF_compat (p : SymSl2) :
    symbolAlg k hk (adF p) =
      A₂bracket (W k hk) (fCl k hk) (symbolAlg k hk p) :=
  adCompat_of_generators (W k hk) (symbolAlg k hk) adF adF_mul
    (fun c => by rw [adF]; exact adOf_C _ _ _ _ c) (fCl k hk) (by
      intro i
      fin_cases i
      · change symbolAlg k hk (adF eSym) =
          A₂bracket (W k hk) (fCl k hk) (symbolAlg k hk eSym)
        rw [adF_e, map_smul, symbolAlg_eSym, symbolAlg_hSym, A₂bracket_f_e]
        rfl
      · change symbolAlg k hk (adF hSym) =
          A₂bracket (W k hk) (fCl k hk) (symbolAlg k hk hSym)
        rw [adF_h, map_smul, symbolAlg_hSym, symbolAlg_fSym, A₂bracket_f_h]
      · change symbolAlg k hk (adF fSym) =
          A₂bracket (W k hk) (fCl k hk) (symbolAlg k hk fSym)
        rw [adF_f, map_zero, symbolAlg_fSym, A₂bracket_self]) p

/-! ## Splitting the exact `C₂` image into two inclusions -/

/-- The easy inclusion: all proposed boundary relations occur in the `C₂` image of `I`. -/
def BoundaryC2ImageLower (n : ℕ) (I : Submodule ℂ (WakModule k))
    (hI : (W k hk).IsIdeal I) : Prop :=
  Ideal.map (symbolAlg k hk) (boundaryIdeal n) ≤ QuotVOA.A₂IdealImage hI

/-- The hard inclusion: `I` produces no `C₂` relations beyond the proposed boundary ideal.

For a singular-generated maximal ideal this is exactly the non-circular PBW normal-form input.
-/
def BoundaryC2ImageUpper (n : ℕ) (I : Submodule ℂ (WakModule k))
    (hI : (W k hk).IsIdeal I) : Prop :=
  QuotVOA.A₂IdealImage hI ≤ Ideal.map (symbolAlg k hk) (boundaryIdeal n)

/-- Representative form of the hard upper inclusion: every vector of `I`, after passing to
`C₂`, is represented by a polynomial in the proposed boundary ideal.

For `I = idealGen W s`, this is the exact Lean interface for the negative-loop PBW argument:
after reordering, every term with a mode at most `-2` dies, and the surviving mode-minus-one
terms are polynomial multiples of horizontal descendants of the highest symbol. -/
def BoundaryC2RepresentativeUpper (n : ℕ) (I : Submodule ℂ (WakModule k)) : Prop :=
  ∀ i ∈ I, ∃ q : SymSl2,
    q ∈ boundaryIdeal n ∧ mk₂ (W k hk) i = symbolAlg k hk q

/-- The representative normal-form statement is equivalent to the hard ideal inclusion. -/
theorem boundaryC2RepresentativeUpper_iff_imageUpper
    (n : ℕ) (I : Submodule ℂ (WakModule k)) (hI : (W k hk).IsIdeal I) :
    BoundaryC2RepresentativeUpper k hk n I ↔ BoundaryC2ImageUpper k hk n I hI := by
  constructor
  · intro hrepr x hx
    obtain ⟨i, hiI, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨q, hq, hiq⟩ := hrepr i hiI
    rw [hiq]
    exact Ideal.mem_map_of_mem (symbolAlg k hk) hq
  · intro hupper i hiI
    have himage : mk₂ (W k hk) i ∈ QuotVOA.A₂IdealImage hI :=
      Submodule.mem_map.mpr ⟨i, hiI, rfl⟩
    have hrel := hupper himage
    rw [Ideal.mem_map_iff_of_surjective _ (symbolAlg_surjective k hk)] at hrel
    obtain ⟨q, hq, hqi⟩ := hrel
    exact ⟨q, hq, hqi.symm⟩

/-- The hard normal-form input specialized to the affine ideal generated by one singular
vector.  This is a proposition, not an axiom. -/
def SingularC2PBWUpper (n : ℕ) (s : WakModule k) : Prop :=
  BoundaryC2RepresentativeUpper k hk n (idealGen (W k hk) s)

/-- The existing equality predicate is precisely the conjunction of the two directed
inclusions. -/
theorem boundaryC2Image_iff_lower_and_upper
    (n : ℕ) (I : Submodule ℂ (WakModule k)) (hI : (W k hk).IsIdeal I) :
    BoundaryC2Image k hk n I ↔
      BoundaryC2ImageLower k hk n I hI ∧ BoundaryC2ImageUpper k hk n I hI := by
  rw [boundaryC2Image_iff_ideal_eq k hk n I hI]
  unfold BoundaryC2ImageLower BoundaryC2ImageUpper
  constructor
  · intro h
    exact ⟨h.ge, h.le⟩
  · rintro ⟨hlower, hupper⟩
    exact le_antisymm hupper hlower

/-! ## Propagation from one highest-weight symbol -/

/-- A nonzero complex scalar multiple belongs to an ideal in a complex algebra exactly when the
element does. -/
private theorem ideal_mem_of_smul_mem {A : Type*} [CommRing A] [Algebra ℂ A]
    (S : Ideal A) {c : ℂ} (hc : c ≠ 0) {x : A} (hx : c • x ∈ S) : x ∈ S := by
  have hmem := Ideal.mul_mem_left S (algebraMap ℂ A c⁻¹) hx
  have heq : algebraMap ℂ A c⁻¹ * (c • x) = x := by
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  rwa [heq] at hmem

/-- If `I` contains a vector with nonzero symbol `c e Cas^n`, then its `C₂` image contains
the highest relation `e Cas^n`. -/
theorem highestRelation_mem_A₂IdealImage
    (n : ℕ) (I : Submodule ℂ (WakModule k)) (hI : (W k hk).IsIdeal I)
    (s : WakModule k) (hsI : s ∈ I) (c : ℂ) (hc : c ≠ 0)
    (hsymbol : mk₂ (W k hk) s = c • symbolAlg k hk (eSym * casSym ^ n)) :
    symbolAlg k hk (eSym * casSym ^ n) ∈ QuotVOA.A₂IdealImage hI := by
  apply ideal_mem_of_smul_mem (QuotVOA.A₂IdealImage hI) hc
  rw [← hsymbol]
  exact Submodule.mem_map.mpr ⟨s, hsI, rfl⟩

/-- One horizontal lowering of the highest relation gives the middle relation. -/
theorem middleRelation_mem_A₂IdealImage
    (n : ℕ) (I : Submodule ℂ (WakModule k)) (hI : (W k hk).IsIdeal I)
    (s : WakModule k) (hsI : s ∈ I) (c : ℂ) (hc : c ≠ 0)
    (hsymbol : mk₂ (W k hk) s = c • symbolAlg k hk (eSym * casSym ^ n)) :
    symbolAlg k hk (hSym * casSym ^ n) ∈ QuotVOA.A₂IdealImage hI := by
  have hhighest := highestRelation_mem_A₂IdealImage k hk n I hI s hsI c hc hsymbol
  have hbracket := QuotVOA.A₂IdealImage_bracket_mem hI (fCl k hk)
    (symbolAlg k hk (eSym * casSym ^ n)) hhighest
  rw [← symbolAlg_adF_compat k hk, adF_mul, adF_e,
    derivation_cas_pow_eq_zero adF adF_mul adF_cas, mul_zero, add_zero,
    smul_mul_assoc, map_smul] at hbracket
  exact ideal_mem_of_smul_mem (QuotVOA.A₂IdealImage hI)
    (by norm_num : (-1 : ℂ) ≠ 0) hbracket

/-- A second horizontal lowering gives the lowest relation. -/
theorem lowestRelation_mem_A₂IdealImage
    (n : ℕ) (I : Submodule ℂ (WakModule k)) (hI : (W k hk).IsIdeal I)
    (s : WakModule k) (hsI : s ∈ I) (c : ℂ) (hc : c ≠ 0)
    (hsymbol : mk₂ (W k hk) s = c • symbolAlg k hk (eSym * casSym ^ n)) :
    symbolAlg k hk (fSym * casSym ^ n) ∈ QuotVOA.A₂IdealImage hI := by
  have hmiddle := middleRelation_mem_A₂IdealImage k hk n I hI s hsI c hc hsymbol
  have hbracket := QuotVOA.A₂IdealImage_bracket_mem hI (fCl k hk)
    (symbolAlg k hk (hSym * casSym ^ n)) hmiddle
  rw [← symbolAlg_adF_compat k hk, adF_mul, adF_h,
    derivation_cas_pow_eq_zero adF adF_mul adF_cas, mul_zero, add_zero,
    smul_mul_assoc, map_smul] at hbracket
  exact ideal_mem_of_smul_mem (QuotVOA.A₂IdealImage hI)
    (by norm_num : (2 : ℂ) ≠ 0) hbracket

/-- The single nonzero highest-weight symbol forces the complete lower inclusion of the
candidate boundary ideal into the singular ideal's `C₂` image. -/
theorem boundaryC2ImageLower_of_highestSymbol
    (n : ℕ) (I : Submodule ℂ (WakModule k)) (hI : (W k hk).IsIdeal I)
    (s : WakModule k) (hsI : s ∈ I) (c : ℂ) (hc : c ≠ 0)
    (hsymbol : mk₂ (W k hk) s = c • symbolAlg k hk (eSym * casSym ^ n)) :
    BoundaryC2ImageLower k hk n I hI := by
  rw [BoundaryC2ImageLower, Ideal.map_le_iff_le_comap, boundaryIdeal, Ideal.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · change symbolAlg k hk (casSym ^ n * eSym) ∈ QuotVOA.A₂IdealImage hI
    rw [mul_comm]
    exact highestRelation_mem_A₂IdealImage k hk n I hI s hsI c hc hsymbol
  · change symbolAlg k hk (casSym ^ n * hSym) ∈ QuotVOA.A₂IdealImage hI
    rw [mul_comm]
    exact middleRelation_mem_A₂IdealImage k hk n I hI s hsI c hc hsymbol
  · change symbolAlg k hk (casSym ^ n * fSym) ∈ QuotVOA.A₂IdealImage hI
    rw [mul_comm]
    exact lowestRelation_mem_A₂IdealImage k hk n I hI s hsI c hc hsymbol

/-- Equivalently, the whole boundary relation ideal is contained in the quotient-symbol
kernel.  This is not an exactness statement. -/
theorem boundaryIdeal_le_ker_quotientSymbol_of_highestSymbol
    (n : ℕ) (I : Submodule ℂ (WakModule k)) (hI : (W k hk).IsIdeal I)
    (hgr : QuotVOA.IsGradedIdeal (W k hk) I)
    (s : WakModule k) (hsI : s ∈ I) (c : ℂ) (hc : c ≠ 0)
    (hsymbol : mk₂ (W k hk) s = c • symbolAlg k hk (eSym * casSym ^ n)) :
    boundaryIdeal n ≤ RingHom.ker (quotientSymbol k hk I hI hgr) := by
  intro p hp
  change QuotVOA.A₂quot hI hgr (symbolAlg k hk p) = 0
  rw [← RingHom.mem_ker, QuotVOA.mem_ker_A₂quot_iff hI hgr]
  have hlower := boundaryC2ImageLower_of_highestSymbol k hk n I hI s hsI c hc hsymbol
  exact hlower (Ideal.mem_map_of_mem (symbolAlg k hk) hp)

/-- After the lower inclusion has been discharged by the highest symbol, exactness needs only
the hard upper inclusion, together with universal-symbol injectivity. -/
theorem exact_quotientSymbol_of_highestSymbol_and_upper
    (n : ℕ) (I : Submodule ℂ (WakModule k)) (hI : (W k hk).IsIdeal I)
    (hgr : QuotVOA.IsGradedIdeal (W k hk) I)
    (s : WakModule k) (hsI : s ∈ I) (c : ℂ) (hc : c ≠ 0)
    (hsymbol : mk₂ (W k hk) s = c • symbolAlg k hk (eSym * casSym ^ n))
    (huniv : Function.Injective (symbolAlg k hk))
    (hupper : BoundaryC2ImageUpper k hk n I hI) :
    Presentation.IsExactPresentation (boundaryIdeal n) (quotientSymbol k hk I hI hgr) := by
  apply exact_quotientSymbol_of_boundaryC2Image k hk I hI hgr huniv
  rw [boundaryC2Image_iff_lower_and_upper k hk n I hI]
  exact ⟨boundaryC2ImageLower_of_highestSymbol k hk n I hI s hsI c hc hsymbol, hupper⟩

/-- The uniform simple-boundary presentation reduced to its smallest independent inputs.

The highest-symbol identity proves the complete lower inclusion internally.  The remaining
external inputs are universal affine `C₂` PBW injectivity, maximal-ideal generation by `s`, and
the representative PBW upper normal form for the singular-generated ideal. -/
theorem exact_boundary_simple_of_highestSymbol_and_PBWUpper
    (n : ℕ) (s : WakModule k) (c : ℂ) (hc : c ≠ 0)
    (hsymbol : mk₂ (W k hk) s = c • symbolAlg k hk (eSym * casSym ^ n))
    (huniv : Function.Injective (symbolAlg k hk))
    (hmax : QuotVOA.maxGradedIdeal (W k hk) = idealGen (W k hk) s)
    (hPBWUpper : SingularC2PBWUpper k hk n s) :
    Presentation.IsExactPresentation (boundaryIdeal n)
      (quotientSymbol k hk (QuotVOA.maxGradedIdeal (W k hk))
        (QuotVOA.maxGradedIdeal_isIdeal _) (QuotVOA.maxGradedIdeal_isGradedIdeal _)) := by
  let I := QuotVOA.maxGradedIdeal (W k hk)
  have hsI : s ∈ I := by
    change s ∈ QuotVOA.maxGradedIdeal (W k hk)
    rw [hmax]
    exact mem_idealGen_self (W k hk) s
  have hrepr : BoundaryC2RepresentativeUpper k hk n I := by
    change BoundaryC2RepresentativeUpper k hk n (QuotVOA.maxGradedIdeal (W k hk))
    rw [hmax]
    exact hPBWUpper
  have hupper : BoundaryC2ImageUpper k hk n I (QuotVOA.maxGradedIdeal_isIdeal _) :=
    (boundaryC2RepresentativeUpper_iff_imageUpper k hk n I
      (QuotVOA.maxGradedIdeal_isIdeal _)).mp hrepr
  exact exact_quotientSymbol_of_highestSymbol_and_upper k hk n I
    (QuotVOA.maxGradedIdeal_isIdeal _) (QuotVOA.maxGradedIdeal_isGradedIdeal _)
    s hsI c hc hsymbol huniv hupper

end
end AffineSl2BoundaryC2
end VOA

section AxiomAudit
#print axioms VOA.QuotVOA.A₂IdealImage_bracket_mem
#print axioms VOA.AffineSl2BoundaryC2.symbolAlg_adF_compat
#print axioms VOA.AffineSl2BoundaryC2.boundaryC2ImageLower_of_highestSymbol
#print axioms VOA.AffineSl2BoundaryC2.boundaryIdeal_le_ker_quotientSymbol_of_highestSymbol
#print axioms VOA.AffineSl2BoundaryC2.exact_quotientSymbol_of_highestSymbol_and_upper
#print axioms VOA.AffineSl2BoundaryC2.exact_boundary_simple_of_highestSymbol_and_PBWUpper
end AxiomAudit
