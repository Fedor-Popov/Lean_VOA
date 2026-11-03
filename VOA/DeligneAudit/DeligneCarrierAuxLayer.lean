/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCarrierAuxJet

/-!
# Type-generic version of `A2CarrierAuxiliaryLayer`

Mechanically generalized from the A₂ file `A2CarrierAuxiliaryLayer` to arbitrary type data
`D : DeligneCarrierData` (`Fin 8 ↦ Fin D.n`, `I2ns ↦ D.I`, `casimir ↦ D.Q`, U3 ↦ `D.u3`).
See that file for the mathematical commentary.
-/

namespace VOA.DeligneAudit.DeligneCarrier

open MvPolynomial
open VOA.FiniteJet VOA.CasimirCostFiltration VOA.QuadraticJetCoefficientPairing
open DeligneCarrierData

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

variable (D : DeligneCarrierData)
include D


/-! ### Weights on auxiliary jets -/

/-- Conformal base weight: currents `1`, Casimir `2`. -/
def auxBase : (AuxVar D) → ℕ := Sum.elim (fun _ => 1) (fun _ => 2)

/-- Casimir count of a generator. -/
def auxCount : (AuxVar D) → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

/-- Li/conformal bidegree of an auxiliary jet variable. -/
def auxBideg (p : ℕ) (v : JetVar (AuxVar D) p) : ℕ × ℕ :=
  (v.order.val, (auxBase D) v.generator + v.order.val)

/-- (Casimir count, conformal weight) of an auxiliary jet variable. -/
def auxCW (p : ℕ) (v : JetVar (AuxVar D) p) : ℕ × ℕ :=
  ((auxCount D) v.generator, (auxBase D) v.generator + v.order.val)

/-- The Casimir jet ideal at jet order `p`. -/
abbrev casI (p : ℕ) : Ideal (JetPoly ℂ (Fin D.n) p) :=
  VOA.DeligneCasimirJetFiltration.casimirJetIdeal (K := ℂ) p D.Q

theorem casI_le (p : ℕ) :
    (casI D) p ≤ VOA.MvPolynomialMinimumWeight.minimumWeightIdeal
      (jetWeight (fun _ : Fin D.n => 1) p) 2 :=
  VOA.DeligneCasimirJetFiltration.casimirJetIdeal_le_minimumWeightTwo _ p D.Q
    D.Q_isWeightedHomogeneous

theorem weight_prod_fst {ι : Type*} (w : ι → ℕ × ℕ) (e : ι →₀ ℕ) :
    (Finsupp.weight w e).1 = Finsupp.weight (fun i => (w i).1) e := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | single_add a n f _ _ ih => simp [map_add, Finsupp.weight_single, ih]

theorem weight_prod_snd {ι : Type*} (w : ι → ℕ × ℕ) (e : ι →₀ ℕ) :
    (Finsupp.weight w e).2 = Finsupp.weight (fun i => (w i).2) e := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | single_add a n f _ _ ih => simp [map_add, Finsupp.weight_single, ih]

theorem relationCoeff_casimir_bihomogeneous (p b : ℕ) (hb : b ≤ p) :
    (relationCoeff (R := ℂ) p b D.Q).IsWeightedHomogeneous
      (jetLiBidegree (fun _ : Fin D.n => 1) p) (b, 2 + b) := by
  rw [DeligneCarrierData.Q, relationCoeff_quadraticRelation D.cas p b hb]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro xy _
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro ab hab
  have hprod := (MvPolynomial.isWeightedHomogeneous_X ℂ (jetLiBidegree (fun _ : Fin D.n => 1) p)
      (⟨xy.1, ab.1⟩ : JetVar (Fin D.n) p)).mul
    (MvPolynomial.isWeightedHomogeneous_X ℂ (jetLiBidegree (fun _ : Fin D.n => 1) p)
      (⟨xy.2, ab.2⟩ : JetVar (Fin D.n) p))
  have hsum := (VOA.ModeParticlePairing.mem_coefficientPairs ab.1 ab.2).mp hab
  have hdeg : jetLiBidegree (fun _ : Fin D.n => 1) p (⟨xy.1, ab.1⟩ : JetVar (Fin D.n) p) +
      jetLiBidegree (fun _ : Fin D.n => 1) p (⟨xy.2, ab.2⟩ : JetVar (Fin D.n) p) = (b, 2 + b) := by
    simp only [jetLiBidegree, Prod.mk_add_mk]
    refine Prod.ext hsum ?_
    simp only
    omega
  rw [hdeg] at hprod
  exact (MvPolynomial.weightedHomogeneousSubmodule ℂ _ (b, 2 + b)).smul_mem (D.cas xy) hprod

theorem auxJetImage_bihomogeneous (p : ℕ) (v : JetVar (AuxVar D) p) :
    ((auxJetImage D) p v).IsWeightedHomogeneous (jetLiBidegree (fun _ : Fin D.n => 1) p)
      ((auxBideg D) p v) := by
  rcases v with ⟨g, a⟩
  rcases g with x | u
  · exact MvPolynomial.isWeightedHomogeneous_X ℂ _ (⟨x, a⟩ : JetVar (Fin D.n) p)
  · exact (relationCoeff_casimir_bihomogeneous D) p a.val (Nat.lt_succ_iff.mp a.isLt)

theorem auxJetImage_mem_pow (p : ℕ) (v : JetVar (AuxVar D) p) (n : ℕ) :
    (auxJetImage D) p v ^ n ∈ (casI D) p ^ (n * (auxCount D) v.generator) := by
  rcases v with ⟨g, a⟩
  rcases g with x | u
  · simp [auxCount]
  · simp only [auxCount, Sum.elim_inr, mul_one]
    apply Ideal.pow_mem_pow
    exact relationCoeff_mem_jetIdeal p a.val (Ideal.span {D.Q}) D.Q
      (Ideal.subset_span rfl) (Nat.lt_succ_iff.mp a.isLt)

/-- **Images of auxiliary monomials**: bihomogeneous, and in the Casimir-count power of the Casimir
jet ideal. -/
theorem auxJetSubst_monomial (p : ℕ) (e : JetVar (AuxVar D) p →₀ ℕ) :
    ((auxJetSubst D) p (monomial e 1)).IsWeightedHomogeneous (jetLiBidegree (fun _ : Fin D.n => 1) p)
        (Finsupp.weight ((auxBideg D) p) e) ∧
      (auxJetSubst D) p (monomial e 1) ∈
        (casI D) p ^ Finsupp.weight (fun v : JetVar (AuxVar D) p => (auxCount D) v.generator) e := by
  classical
  induction e using Finsupp.induction with
  | zero =>
    rw [← C_apply, C_1, map_one]
    exact ⟨MvPolynomial.isWeightedHomogeneous_one ℂ _, by simp⟩
  | single_add a n f _ _ ih =>
    have hsplit : (monomial (Finsupp.single a n + f) (1 : ℂ) : JetPoly ℂ (AuxVar D) p) =
        X a ^ n * monomial f 1 := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    rw [hsplit, map_mul, map_pow, auxJetSubst, aeval_X, ← auxJetSubst]
    refine ⟨?_, ?_⟩
    · rw [map_add, Finsupp.weight_single]
      exact (((auxJetImage_bihomogeneous D) p a).pow n).mul ih.1
    · rw [map_add, Finsupp.weight_single, pow_add, smul_eq_mul]
      exact Ideal.mul_mem_mul ((auxJetImage_mem_pow D) p a n) ih.2

/-! ### The map onto a Casimir layer -/

/-- Auxiliary jets of Casimir count `d` and conformal weight `N`. -/
abbrev auxSource (p N d : ℕ) : Submodule ℂ (JetPoly ℂ (AuxVar D) p) :=
  MvPolynomial.weightedHomogeneousSubmodule ℂ ((auxCW D) p) (d, N)

theorem auxJetSubst_of_mem_auxSource (p N d : ℕ) {F : JetPoly ℂ (AuxVar D) p}
    (hF : F ∈ (auxSource D) p N d) :
    ((auxJetSubst D) p F).IsWeightedHomogeneous (jetWeight (fun _ : Fin D.n => 1) p) N ∧
      (auxJetSubst D) p F ∈ (casI D) p ^ d := by
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hF
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp only [map_zero]; exact ⟨isWeightedHomogeneous_zero ℂ _ N, zero_mem _⟩
  | add f g _ _ hf hg => rw [map_add]; exact ⟨hf.1.add hg.1, add_mem hf.2 hg.2⟩
  | monomial e r hr =>
    have hm := (auxJetSubst_monomial D) p e
    have h1 : Finsupp.weight (fun v : JetVar (AuxVar D) p => (auxCount D) v.generator) e = d := by
      have := congrArg Prod.fst hr
      rw [(weight_prod_fst D)] at this
      exact this
    have h2 : (Finsupp.weight ((auxBideg D) p) e).2 = N := by
      have := congrArg Prod.snd hr
      rw [(weight_prod_snd D)] at this
      rw [(weight_prod_snd D)]
      exact this
    rw [show (monomial e r : JetPoly ℂ (AuxVar D) p) = r • monomial e 1 by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul]
    refine ⟨?_, ?_⟩
    · have hw := isWeightedHomogeneous_jetWeight_of_jetLiBidegree (fun _ : Fin D.n => 1) p
        (Finsupp.weight ((auxBideg D) p) e).1 (Finsupp.weight ((auxBideg D) p) e).2 hm.1
      rw [h2] at hw
      exact (MvPolynomial.weightedHomogeneousSubmodule ℂ _ N).smul_mem r hw
    · rw [← h1]
      exact Submodule.smul_of_tower_mem _ r hm.2

/-- Project, substitute, and land in the depth-`d` weight-`N` representatives. -/
def layerPre (p N d : ℕ) :
    JetPoly ℂ (AuxVar D) p →ₗ[ℂ]
      polynomialCostPiece (K := ℂ) (jetWeight (fun _ : Fin D.n => 1) p) N ((casI D) p) d where
  toFun f :=
    ⟨⟨(auxJetSubst D) p (weightedHomogeneousComponent ((auxCW D) p) (d, N) f),
      ((auxJetSubst_of_mem_auxSource D) p N d
        (weightedHomogeneousComponent_mem _ f (d, N))).1⟩,
      ((auxJetSubst_of_mem_auxSource D) p N d (weightedHomogeneousComponent_mem _ f (d, N))).2⟩
  map_add' f g := by
    apply Subtype.ext; apply Subtype.ext
    simp only [map_add, Submodule.coe_add]
  map_smul' c f := by
    apply Subtype.ext; apply Subtype.ext
    simp only [map_smul, Submodule.coe_smul, RingHom.id_apply]

/-- The map from auxiliary jets onto the `d`-th Casimir layer of the `(p, N)` piece of `Jet R̃`. -/
def auxToLayer (p N d : ℕ) : JetPoly ℂ (AuxVar D) p →ₗ[ℂ] (casimirLayer D) p N d :=
  (polynomialCostToAssociated (K := ℂ) (jetWeight (fun _ : Fin D.n => 1) p) N ((casI D) p) ((casI_le D) p)
    ((toBidegreeImage D) p N) ((toBidegreeImage_surjective D) p N) d).comp ((layerPre D) p N d)

theorem auxToLayer_apply (p N d : ℕ) (f : JetPoly ℂ (AuxVar D) p) :
    (auxToLayer D) p N d f =
      polynomialCostToAssociated (K := ℂ) (jetWeight (fun _ : Fin D.n => 1) p) N ((casI D) p)
        ((casI_le D) p) ((toBidegreeImage D) p N) ((toBidegreeImage_surjective D) p N) d
        ((layerPre D) p N d f) := rfl

/-! ### `(toBidegreeImage D)` kills the jet ideal of `I₂ⁿˢ` -/

theorem whc_jetLi_eq_whc_bidegree (p N : ℕ) (h : p ≤ N) (φ : JetPoly ℂ (Fin D.n) p) :
    weightedHomogeneousComponent (jetLiBidegree (fun _ : Fin D.n => 1) p) (p, N) φ =
      weightedHomogeneousComponent (VOA.QuadraticJetRestrictedDual.bidegreeWeight p) (N - p, p) φ := by
  classical
  ext e
  rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent,
    CarrierEmbedding.weight_jetLiBidegree_one]
  congr 1
  apply propext
  constructor
  · intro h1
    have h2 := Prod.ext_iff.mp h1
    simp only at h2
    exact Prod.ext (by omega) (by omega)
  · intro h1
    rw [h1]
    exact Prod.ext rfl (by simp only; omega)

theorem whc_jetLi_eq_zero (p N : ℕ) (h : N < p) (φ : JetPoly ℂ (Fin D.n) p) :
    weightedHomogeneousComponent (jetLiBidegree (fun _ : Fin D.n => 1) p) (p, N) φ = 0 := by
  classical
  ext e
  rw [coeff_weightedHomogeneousComponent, CarrierEmbedding.weight_jetLiBidegree_one, coeff_zero]
  rw [if_neg]
  intro h1
  have h2 := Prod.ext_iff.mp h1
  simp only at h2
  omega

theorem toBidegreeImage_eq_zero_of_mem (p N : ℕ)
    (g : VOA.DeligneCasimirJetFiltration.JetWeightSource (K := ℂ) (fun _ : Fin D.n => 1) p N)
    (hg : g.1 ∈ jetIdeal (R := ℂ) p D.I) : (toBidegreeImage D) p N g = 0 := by
  apply Subtype.ext
  change presentedJetMk (R := ℂ) p D.I
    (weightedHomogeneousComponent (jetLiBidegree (fun _ : Fin D.n => 1) p) (p, N) g.1) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  by_cases h : p ≤ N
  · rw [(whc_jetLi_eq_whc_bidegree D) p N h]
    exact VOA.QuadraticJetRestrictedDual.bidegreeComponent_mem_ideal D.rel p (N - p) p
      g.1 hg
  · rw [(whc_jetLi_eq_zero D) p N (by omega)]
    exact zero_mem _

/-! ### Relations are killed -/

theorem relationCoeff_quadraticRelation_auxCW (p n : ℕ) (hn : n ≤ p)
    (q : (AuxVar D) × (AuxVar D) → ℂ) (c s : ℕ)
    (hq : ∀ xy, q xy ≠ 0 →
      (auxCount D) xy.1 + (auxCount D) xy.2 = c ∧ (auxBase D) xy.1 + (auxBase D) xy.2 = s) :
    (relationCoeff (R := ℂ) p n (quadraticRelation q)).IsWeightedHomogeneous ((auxCW D) p)
      (c, s + n) := by
  rw [relationCoeff_quadraticRelation q p n hn]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro xy _
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro ab hab
  by_cases hxy : q xy = 0
  · rw [hxy, zero_smul]
    exact isWeightedHomogeneous_zero ℂ _ _
  have hprod := (MvPolynomial.isWeightedHomogeneous_X ℂ ((auxCW D) p)
      (⟨xy.1, ab.1⟩ : JetVar (AuxVar D) p)).mul
    (MvPolynomial.isWeightedHomogeneous_X ℂ ((auxCW D) p) (⟨xy.2, ab.2⟩ : JetVar (AuxVar D) p))
  have hsum := (VOA.ModeParticlePairing.mem_coefficientPairs ab.1 ab.2).mp hab
  obtain ⟨hc, hs⟩ := hq xy hxy
  have hdeg : (auxCW D) p (⟨xy.1, ab.1⟩ : JetVar (AuxVar D) p) +
      (auxCW D) p (⟨xy.2, ab.2⟩ : JetVar (AuxVar D) p) = (c, s + n) := by
    simp only [auxCW, Prod.mk_add_mk]
    exact Prod.ext hc (by simp only; omega)
  rw [hdeg] at hprod
  exact (MvPolynomial.weightedHomogeneousSubmodule ℂ _ (c, s + n)).smul_mem (q xy) hprod

/-- Casimir count of a relation. -/
def relCount : (AuxRel D) → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

/-- Base weight of a relation. -/
def relBase : (AuxRel D) → ℕ
  | .inl _ => 2
  | .inr (.inl _) => 3
  | .inr (.inr _) => 4

theorem auxMatrix_support (r : (AuxRel D)) (xy : (AuxVar D) × (AuxVar D)) (h : (auxMatrix D) r xy ≠ 0) :
    (auxCount D) xy.1 + (auxCount D) xy.2 = (relCount D) r ∧ (auxBase D) xy.1 + (auxBase D) xy.2 = (relBase D) r := by
  rcases r with o | a | u <;> rcases xy with ⟨x | x, y | y⟩ <;>
    simp_all [auxMatrix, auxCount, auxBase, relCount, relBase]

theorem relationCoeff_auxMatrix_auxCW (p n : ℕ) (hn : n ≤ p) (r : (AuxRel D)) :
    (relationCoeff (R := ℂ) p n (quadraticRelation ((auxMatrix D) r))).IsWeightedHomogeneous
      ((auxCW D) p) ((relCount D) r, (relBase D) r + n) :=
  (relationCoeff_quadraticRelation_auxCW D) p n hn _ _ _ ((auxMatrix_support D) r)

theorem layerPre_eq_zero (p N d : ℕ) (f : JetPoly ℂ (AuxVar D) p)
    (h : weightedHomogeneousComponent ((auxCW D) p) (d, N) f = 0) : (layerPre D) p N d f = 0 := by
  apply Subtype.ext; apply Subtype.ext
  change (auxJetSubst D) p (weightedHomogeneousComponent ((auxCW D) p) (d, N) f) = 0
  rw [h, map_zero]

/-- **The auxiliary relations vanish in every Casimir layer.** -/
theorem auxToLayer_relation (p N d : ℕ) (r : (AuxRel D)) (n : ℕ) (hn : n ≤ p)
    (e : JetVar (AuxVar D) p →₀ ℕ) :
    (auxToLayer D) p N d
      (monomial e 1 * relationCoeff (R := ℂ) p n (quadraticRelation ((auxMatrix D) r))) = 0 := by
  classical
  set f := (monomial e 1 * relationCoeff (R := ℂ) p n (quadraticRelation ((auxMatrix D) r)) :
    JetPoly ℂ (AuxVar D) p) with hf
  have hhom : f.IsWeightedHomogeneous ((auxCW D) p)
      (Finsupp.weight ((auxCW D) p) e + ((relCount D) r, (relBase D) r + n)) :=
    (isWeightedHomogeneous_monomial _ e 1 rfl).mul ((relationCoeff_auxMatrix_auxCW D) p n hn r)
  by_cases hdeg : Finsupp.weight ((auxCW D) p) e + ((relCount D) r, (relBase D) r + n) = (d, N)
  swap
  · rw [(auxToLayer_apply D), (layerPre_eq_zero D) p N d f
      (hhom.weightedHomogeneousComponent_ne _ (Ne.symm hdeg))]
    exact map_zero _
  have hcomp : weightedHomogeneousComponent ((auxCW D) p) (d, N) f = f := by
    rw [← hdeg]; exact hhom.weightedHomogeneousComponent_same
  have hcount : Finsupp.weight (fun v : JetVar (AuxVar D) p => (auxCount D) v.generator) e +
      (relCount D) r = d := by
    have := congrArg Prod.fst hdeg
    simp only [Prod.fst_add] at this
    rw [(weight_prod_fst D)] at this
    exact this
  have hΦ : (auxJetSubst D) p f = (auxJetSubst D) p (monomial e 1) *
      (auxJetSubst D) p (relationCoeff (R := ℂ) p n (quadraticRelation ((auxMatrix D) r))) := by
    rw [hf, map_mul]
  rw [(auxToLayer_apply D)]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [Submodule.mem_comap]
  by_cases hr : r = .inl none
  · -- the Casimir relation of `I₂`: one more Casimir factor
    subst hr
    simp only [relCount, add_zero] at hcount
    change (toBidegreeImage D) p N (((layerPre D) p N d f).1) ∈
      quotientCostPiece (K := ℂ) (jetWeight (fun _ : Fin D.n => 1) p) N ((casI D) p)
        ((toBidegreeImage D) p N) (d + 1)
    refine ⟨((layerPre D) p N d f).1, ?_, rfl⟩
    change (auxJetSubst D) p (weightedHomogeneousComponent ((auxCW D) p) (d, N) f) ∈ (casI D) p ^ (d + 1)
    rw [hcomp, hΦ, (auxJetSubst_relation_casimir D) p n hn, pow_succ]
    refine Ideal.mul_mem_mul ?_ ?_
    · rw [← hcount]; exact ((auxJetSubst_monomial D) p e).2
    · exact relationCoeff_mem_jetIdeal p n (Ideal.span {D.Q}) D.Q
        (Ideal.subset_span rfl) hn
  · have hz : (toBidegreeImage D) p N ((layerPre D) p N d f).1 = 0 := by
      apply (toBidegreeImage_eq_zero_of_mem D)
      change (auxJetSubst D) p (weightedHomogeneousComponent ((auxCW D) p) (d, N) f) ∈ _
      rw [hcomp, hΦ]
      exact Ideal.mul_mem_left _ _ ((auxJetSubst_relation_mem D) p n hn r hr)
    change (toBidegreeImage D) p N (((layerPre D) p N d f).1) ∈
      quotientCostPiece (K := ℂ) (jetWeight (fun _ : Fin D.n => 1) p) N ((casI D) p)
        ((toBidegreeImage D) p N) (d + 1)
    rw [hz]
    exact zero_mem _

/-! ### Support of `(auxToLayer D)` on monomials -/

theorem auxToLayer_eq_zero_of_image (p N d : ℕ) (f : JetPoly ℂ (AuxVar D) p)
    (h : (toBidegreeImage D) p N ((layerPre D) p N d f).1 = 0) : (auxToLayer D) p N d f = 0 := by
  rw [(auxToLayer_apply D)]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [Submodule.mem_comap]
  change (toBidegreeImage D) p N (((layerPre D) p N d f).1) ∈
    quotientCostPiece (K := ℂ) (jetWeight (fun _ : Fin D.n => 1) p) N ((casI D) p)
      ((toBidegreeImage D) p N) (d + 1)
  rw [h]
  exact zero_mem _

theorem weight_auxCW (p : ℕ) (e : JetVar (AuxVar D) p →₀ ℕ) :
    Finsupp.weight ((auxCW D) p) e =
      (Finsupp.weight (fun v : JetVar (AuxVar D) p => (auxCount D) v.generator) e,
        (Finsupp.weight ((auxBideg D) p) e).2) := by
  refine Prod.ext ?_ ?_
  · rw [(weight_prod_fst D)]; rfl
  · rw [(weight_prod_snd D), (weight_prod_snd D)]; rfl

/-- **Support.**  A monomial contributes to the layer only in Casimir count `d`, conformal weight
`N` and Li degree `p`. -/
theorem auxToLayer_monomial_eq_zero (p N d : ℕ) (e : JetVar (AuxVar D) p →₀ ℕ)
    (h : ¬ (Finsupp.weight ((auxCW D) p) e = (d, N) ∧ (Finsupp.weight ((auxBideg D) p) e).1 = p)) :
    (auxToLayer D) p N d (monomial e 1) = 0 := by
  classical
  have hmon := isWeightedHomogeneous_monomial ((auxCW D) p) e (1 : ℂ) rfl
  by_cases hcw : Finsupp.weight ((auxCW D) p) e = (d, N)
  · have hli : (Finsupp.weight ((auxBideg D) p) e).1 ≠ p := fun h' => h ⟨hcw, h'⟩
    apply (auxToLayer_eq_zero_of_image D)
    apply Subtype.ext
    change presentedJetMk (R := ℂ) p D.I
      (weightedHomogeneousComponent (jetLiBidegree (fun _ : Fin D.n => 1) p) (p, N)
        ((auxJetSubst D) p (weightedHomogeneousComponent ((auxCW D) p) (d, N) (monomial e 1)))) = 0
    rw [← hcw, hmon.weightedHomogeneousComponent_same,
      ((auxJetSubst_monomial D) p e).1.weightedHomogeneousComponent_ne _ (by
        intro h'; exact hli (congrArg Prod.fst h').symm), map_zero]
  · rw [(auxToLayer_apply D), (layerPre_eq_zero D) p N d _
      (hmon.weightedHomogeneousComponent_ne _ (Ne.symm hcw))]
    exact map_zero _

/-! ### Surjectivity -/

/-- Lift current jets into the auxiliary jets (Casimir count zero). -/
def auxLift (p : ℕ) : JetPoly ℂ (Fin D.n) p →ₐ[ℂ] JetPoly ℂ (AuxVar D) p :=
  rename (fun v : JetVar (Fin D.n) p => (⟨Sum.inl v.generator, v.order⟩ : JetVar (AuxVar D) p))

theorem auxJetSubst_auxLift (p : ℕ) (f : JetPoly ℂ (Fin D.n) p) :
    (auxJetSubst D) p ((auxLift D) p f) = f := by
  have h : ((auxJetSubst D) p).comp ((auxLift D) p) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [auxLift, auxJetSubst, auxJetImage]
  exact congrArg (fun φ : JetPoly ℂ (Fin D.n) p →ₐ[ℂ] JetPoly ℂ (Fin D.n) p => φ f) h

/-- Casimir count as a weight. -/
abbrev auxCnt (p : ℕ) : JetVar (AuxVar D) p → ℕ := fun v => (auxCount D) v.generator

theorem auxLift_count (p : ℕ) (f : JetPoly ℂ (Fin D.n) p) :
    ((auxLift D) p f).IsWeightedHomogeneous ((auxCnt D) p) 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [auxLift, rename_C]; exact isWeightedHomogeneous_C _ a
  | add f g hf hg => rw [map_add]; exact hf.add hg
  | mul_X f v hf =>
    rw [map_mul, auxLift, rename_X, ← auxLift]
    have := hf.mul (isWeightedHomogeneous_X ℂ ((auxCnt D) p)
      (⟨Sum.inl v.generator, v.order⟩ : JetVar (AuxVar D) p))
    simpa [auxCnt, auxCount] using this

theorem casI_lift (p : ℕ) (b : JetPoly ℂ (Fin D.n) p) (hb : b ∈ (casI D) p) :
    ∃ F : JetPoly ℂ (AuxVar D) p, F.IsWeightedHomogeneous ((auxCnt D) p) 1 ∧ (auxJetSubst D) p F = b := by
  have hb' : b ∈ Submodule.span (JetPoly ℂ (Fin D.n) p)
      (jetRelationSetOfSet (R := ℂ) p ({D.Q} : Set (MvPolynomial (Fin D.n) ℂ))) := by
    have := hb
    rw [casI, VOA.DeligneCasimirJetFiltration.casimirJetIdeal,
      jetIdeal_span_eq_jetIdealOfSet, jetIdealOfSet] at this
    exact this
  clear hb
  induction hb' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, j, rfl⟩ := hx
    rw [Set.mem_singleton_iff] at hf
    subst hf
    refine ⟨X ⟨Sum.inr (), j⟩, ?_, ?_⟩
    · exact isWeightedHomogeneous_X ℂ ((auxCnt D) p) _
    · simp [auxJetSubst, auxJetImage]
  | zero => exact ⟨0, isWeightedHomogeneous_zero ℂ _ 1, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, rfl⟩ := hx
    obtain ⟨G, hG, rfl⟩ := hy
    exact ⟨F + G, hF.add hG, map_add _ F G⟩
  | smul a x _ hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    refine ⟨(auxLift D) p a * F, ?_, ?_⟩
    · simpa using ((auxLift_count D) p a).mul hF
    · rw [map_mul, (auxJetSubst_auxLift D), smul_eq_mul]

theorem casI_pow_lift (p : ℕ) : ∀ (d : ℕ) (g : JetPoly ℂ (Fin D.n) p), g ∈ (casI D) p ^ d →
    ∃ F : JetPoly ℂ (AuxVar D) p, F.IsWeightedHomogeneous ((auxCnt D) p) d ∧ (auxJetSubst D) p F = g
  | 0, g, _ => ⟨(auxLift D) p g, (auxLift_count D) p g, (auxJetSubst_auxLift D) p g⟩
  | d + 1, g, hg => by
    rw [pow_succ] at hg
    refine Submodule.mul_induction_on hg ?_ ?_
    · intro a ha b hb
      obtain ⟨F, hF, rfl⟩ := casI_pow_lift p d a ha
      obtain ⟨G, hG, rfl⟩ := (casI_lift D) p b hb
      exact ⟨F * G, hF.mul hG, map_mul _ F G⟩
    · rintro x y ⟨F, hF, rfl⟩ ⟨G, hG, rfl⟩
      exact ⟨F + G, hF.add hG, map_add _ F G⟩

theorem auxJetSubst_whc (p N d : ℕ) {F : JetPoly ℂ (AuxVar D) p}
    (hF : F.IsWeightedHomogeneous ((auxCnt D) p) d) :
    weightedHomogeneousComponent (jetWeight (fun _ : Fin D.n => 1) p) N ((auxJetSubst D) p F) =
      (auxJetSubst D) p (weightedHomogeneousComponent ((auxCW D) p) (d, N) F) := by
  classical
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add f g _ _ hf hg => simp only [map_add, hf, hg]
  | monomial e r hr =>
    have hm := (auxJetSubst_monomial D) p e
    have hw := isWeightedHomogeneous_jetWeight_of_jetLiBidegree (fun _ : Fin D.n => 1) p
      (Finsupp.weight ((auxBideg D) p) e).1 (Finsupp.weight ((auxBideg D) p) e).2 hm.1
    have hmon := isWeightedHomogeneous_monomial ((auxCW D) p) e r rfl
    rw [show (monomial e r : JetPoly ℂ (AuxVar D) p) = r • monomial e 1 by
      rw [smul_monomial, smul_eq_mul, mul_one]] at hmon ⊢
    rw [map_smul, map_smul, map_smul]
    have hcw := (weight_auxCW D) p e
    rw [hr] at hcw
    by_cases hN : (Finsupp.weight ((auxBideg D) p) e).2 = N
    · rw [← hN, hw.weightedHomogeneousComponent_same, hN,
        show ((d, N) : ℕ × ℕ) = Finsupp.weight ((auxCW D) p) e by rw [hcw, hN],
        (isWeightedHomogeneous_monomial ((auxCW D) p) e (1 : ℂ) rfl).weightedHomogeneousComponent_same]
      exact (map_smul _ _ _).symm
    · rw [hw.weightedHomogeneousComponent_ne _ (Ne.symm hN),
        (isWeightedHomogeneous_monomial ((auxCW D) p) e (1 : ℂ) rfl).weightedHomogeneousComponent_ne
          _ (by rw [hcw]; intro h; exact hN (congrArg Prod.snd h).symm)]
      simp

/-- **`(auxToLayer D)` is onto the Casimir layer.** -/
theorem auxToLayer_surjective (p N d : ℕ) : Function.Surjective ((auxToLayer D) p N d) := by
  intro y
  obtain ⟨x, rfl⟩ := polynomialCostToAssociated_surjective (K := ℂ)
    (jetWeight (fun _ : Fin D.n => 1) p) N ((casI D) p) ((casI_le D) p) ((toBidegreeImage D) p N)
    ((toBidegreeImage_surjective D) p N) d y
  have hx : x.1.1 ∈ (casI D) p ^ d := x.2
  obtain ⟨F, hF, hFx⟩ := (casI_pow_lift D) p d x.1.1 hx
  refine ⟨F, ?_⟩
  rw [(auxToLayer_apply D)]
  congr 1
  apply Subtype.ext; apply Subtype.ext
  change (auxJetSubst D) p (weightedHomogeneousComponent ((auxCW D) p) (d, N) F) = x.1.1
  rw [← (auxJetSubst_whc D) p N d hF, hFx]
  exact (x.1.2 : x.1.1.IsWeightedHomogeneous _ N).weightedHomogeneousComponent_same

end

end VOA.DeligneAudit.DeligneCarrier
