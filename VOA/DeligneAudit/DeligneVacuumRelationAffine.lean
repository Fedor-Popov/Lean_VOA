/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneVacuumRelation
import VOA.AffineGeneral.SimpleQuotient

/-!
# The vacuum quartic relation for `L_k(𝔤)`, any `LieData` (type-generic part)

For any `D : LieData κ ι` and non-critical level `k`, the simple affine VOA
`L_k(𝔤) = simpleVOA D k hk` carries square-bracket current data (`affineCurrentData`): currents
`simpleCurrentState (generator i)`, brackets `structureConstant`, form `formTable`, inverse form
`kappaInv`, dual Coxeter number `D.h`, Sugawara vector.  Every field is a general fact about
`AffineGeneral` — no type-specific computation.

What remains for a given Deligne type is purely about polynomials and singular vectors:
* `vacuumQuarticRelation_affine` — from `∀ i, sym (X i * casPoly) = 0`;
* `vacuumQuarticRelation_affine_of_relations` — from relation polynomials `r` with vanishing
  symbols and U3 for `casPoly` (`X i · casPoly ∈ (r)`);
* `sym_singular` — a relation polynomial `Σ c_s X_{a_s} X_{b_s}` whose ordinary state
  `Σ c_s J^{a_s}(-1)J^{b_s}(-1)|0⟩` dies in `L_k(𝔤)`, and whose bracket and form shadows vanish,
  has vanishing square symbol;
* `sym_step` — propagation along the coadjoint derivation (`adG structureConstant`).
-/

namespace VOA.DeligneAudit.VacuumRelation

open VOA VOA.ZhuCoordinate VOA.DeligneAudit.DeligneMLDE MvPolynomial
open VOA.AffineGeneral VOA.AffineGeneral.LieData VOA.AffineGeneral.SugawaraCov

noncomputable section

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (D : LieData κ ι) (k : ℂ) (hk : k + D.h ≠ 0)

/-- The current states of `L_k(𝔤)`. -/
abbrev affGen (i : ι) : Vacuum D k ⧸ maxIdeal D k hk :=
  simpleCurrentState D k hk (D.generator i)

theorem affGen_eq (i : ι) :
    affGen D k hk i = simpleProjection D k hk (J D k i (-1) (vacuumA D k)) := rfl

theorem affine_smulJ (a : ι) (m : ℤ) (v : Vacuum D k) :
    (affineVOA D k hk).smul (J D k a (-1) (vacuumA D k)) m v = J D k a m v := by
  change mode (YA D k hk (J D k a (-1) (vacuumA D k))) m v = _
  rw [YA_current_state, mode_Jfield]

theorem affGen_smul (a : ι) (m : ℤ) (x : Vacuum D k) :
    (simpleVOA D k hk).smul (affGen D k hk a) m (simpleProjection D k hk x) =
      simpleProjection D k hk (J D k a m x) := by
  have h := SimpleQuot.maxQuotientVOA_mkQ_smul (affineVOA D k hk)
    (J D k a (-1) (vacuumA D k)) m x
  rw [affine_smulJ] at h
  exact h

theorem simple_vacuum_eq :
    (simpleVOA D k hk).vacuum = simpleProjection D k hk (vacuumA D k) := rfl

theorem simple_conformal_eq :
    (simpleVOA D k hk).conformalVector = simpleProjection D k hk (omegaA D k) := rfl

theorem J_J_comm' (a b : ι) (m n : ℤ) (w : Vacuum D k) :
    J D k a m (J D k b n w) =
      J D k b n (J D k a m w) + (∑ c, D.structureConstant a b c • J D k c (m + n) w)
        + (if m + n = 0 then ((m : ℂ) * k * D.formTable a b) • w else 0) := by
  have h := LinearMap.congr_fun (current_comm D k a b m n) w
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.sum_apply, sub_eq_iff_eq_add'] at h
  rw [h, add_assoc]
  congr 2
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn, LinearMap.smul_apply, LinearMap.id_apply]
  · rw [if_neg hmn, if_neg hmn, LinearMap.zero_apply]

theorem affGen_primary (a : ι) : (simpleVOA D k hk).L 1 (affGen D k hk a) = 0 := by
  change (simpleVOA D k hk).smul (simpleVOA D k hk).conformalVector (1 + 1) (affGen D k hk a) = 0
  rw [simple_conformal_eq, affGen_eq]
  have h := SimpleQuot.maxQuotientVOA_mkQ_smul (affineVOA D k hk) (omegaA D k) (1 + 1)
    (J D k a (-1) (vacuumA D k))
  refine h.trans ?_
  change (maxIdeal D k hk).mkQ (mode (YA D k hk (omegaA D k)) (1 + 1) _) = 0
  rw [show (1 + 1 : ℤ) = 2 by norm_num]
  rw [current_primary D k hk a, map_zero]

theorem affGen_bracket (b i : ι) :
    (simpleVOA D k hk).smul (affGen D k hk b) 0 (affGen D k hk i)
      = ∑ c, D.structureConstant b i c • affGen D k hk c := by
  rw [affGen_eq D k hk i, affGen_smul, J_J_comm', J_vacuum_nonneg D k b le_rfl, map_zero,
    zero_add, if_neg (by norm_num), add_zero, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, zero_add, affGen_eq]

theorem affGen_form (a b : ι) :
    (simpleVOA D k hk).smul (affGen D k hk a) 1 (affGen D k hk b)
      = (k * D.formTable a b) • (simpleVOA D k hk).vacuum := by
  rw [affGen_eq D k hk b, affGen_smul, J_J_comm', J_vacuum_nonneg D k a (by norm_num), map_zero,
    zero_add, if_pos (by norm_num), map_add, map_sum, simple_vacuum_eq, map_smul]
  have h0 : ∀ c, simpleProjection D k hk
      (D.structureConstant a b c • J D k c (1 + -1) (vacuumA D k)) = 0 := by
    intro c
    rw [show (1 : ℤ) + -1 = 0 by norm_num, J_vacuum_nonneg D k c le_rfl, smul_zero, map_zero]
  rw [Finset.sum_eq_zero fun c _ => h0 c, zero_add]
  norm_num

theorem affGen_sugawara :
    (simpleVOA D k hk).conformalVector = (2 * (k + D.h))⁻¹ •
      ∑ i, ∑ j, D.kappaInv i j • (simpleVOA D k hk).smul (affGen D k hk i) (-1) (affGen D k hk j) := by
  rw [simple_conformal_eq, omegaA_creation_form, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, affGen_eq D k hk j, affGen_smul]

/-- **The square-bracket current data of `L_k(𝔤)`**, for any `LieData`. -/
def affineCurrentData : SqCurrentData (simpleVOA D k hk) ι where
  g := affGen D k hk
  mem i := simpleCurrentState_mem D k hk i
  primary := affGen_primary D k hk
  T := D.structureConstant
  bracket := affGen_bracket D k hk
  F := D.formTable
  level := k
  form := affGen_form D k hk
  K := D.kappaInv
  hdual := D.h
  ne := hk
  sugawara := affGen_sugawara D k hk
  bracket_trace := D.kappaInv_fabc_antisymm_zero
  central := by
    rw [D.trace_kappaInv_formTable]
    change (Fintype.card ι : ℂ) * k / (k + D.h) * (k + D.h) = k * Fintype.card ι
    field_simp

theorem simple_vacuum_ne_zero' : (simpleVOA D k hk).vacuum ≠ 0 :=
  SimpleQuot.maxQuotientVOA_vacuum_ne_zero (affineVOA D k hk) (vacuumA_ne_zero D k)

theorem simple_centralCharge' :
    (simpleVOA D k hk).centralCharge = (Fintype.card ι : ℂ) * k / (k + D.h) := rfl

/-- **The vacuum quartic relation for `L_k(𝔤)`** from the cubic symbols. -/
theorem vacuumQuarticRelation_affine
    (h : ∀ i, (affineCurrentData D k hk).sym (X i * (affineCurrentData D k hk).casPoly) = 0) :
    VacuumQuarticRelation (simpleVOA D k hk)
      (5 / 4 * (simpleVOA D k hk).centralCharge ^ 2 + 11 / 2 * (simpleVOA D k hk).centralCharge) :=
  (affineCurrentData D k hk).vacuumQuarticRelation_of_symbols (simple_vacuum_ne_zero' D k hk) h

/-- **From relations and U3**: if every relation polynomial has vanishing square symbol and
`X i · casPoly` lies in the ideal they generate, the vacuum quartic relation holds. -/
theorem vacuumQuarticRelation_affine_of_relations {ρ : Type*} (r : ρ → MvPolynomial ι ℂ)
    (hr : ∀ e, (affineCurrentData D k hk).sym (r e) = 0)
    (hu3 : ∀ i, X i * (affineCurrentData D k hk).casPoly ∈ Ideal.span (Set.range r)) :
    VacuumQuarticRelation (simpleVOA D k hk)
      (5 / 4 * (simpleVOA D k hk).centralCharge ^ 2 + 11 / 2 * (simpleVOA D k hk).centralCharge) :=
  vacuumQuarticRelation_affine D k hk fun i =>
    (affineCurrentData D k hk).sym_eq_zero_of_mem_span r hr (hu3 i)

/-- `sym (c • p) = c • sym p`. -/
theorem sym_smul' (c : ℂ) (p : MvPolynomial ι ℂ) :
    (affineCurrentData D k hk).sym (c • p) = c • (affineCurrentData D k hk).sym p := by
  rw [MvPolynomial.smul_eq_C_mul, SqCurrentData.sym_C_mul]

/-- **Propagation step** along the coadjoint derivation: `q • ad_b P = p • P'`, `p ≠ 0`. -/
theorem sym_step {b : ι} {P P' : MvPolynomial ι ℂ} {p q : ℂ} (hp : p ≠ 0)
    (h : q • adG D.structureConstant b P = p • P')
    (hP : (affineCurrentData D k hk).sym P = 0) : (affineCurrentData D k hk).sym P' = 0 := by
  have h1 : (affineCurrentData D k hk).sym (adG D.structureConstant b P) = 0 := by
    have := (affineCurrentData D k hk).sym_adG b P
    rw [hP, map_zero] at this
    exact this
  have h2 := congrArg (affineCurrentData D k hk).sym h
  rw [sym_smul', sym_smul', h1, smul_zero] at h2
  exact (smul_eq_zero.mp h2.symm).resolve_left hp

/-- **Square symbol of a singular-vector relation** (any `LieData`, any level): if
`Σ c_s J^{a_s}(-1)J^{b_s}(-1)|0⟩` dies in `L_k(𝔤)` and its bracket and form shadows vanish, the
square symbol of `Σ c_s X_{a_s} X_{b_s}` vanishes. -/
theorem sym_singular {σ : Type*} [Fintype σ] (c : σ → ℂ) (a b : σ → ι)
    (hsing : simpleProjection D k hk
      (∑ s, c s • J D k (a s) (-1) (J D k (b s) (-1) (vacuumA D k))) = 0)
    (hbr : ∀ e, ∑ s, c s * D.structureConstant (a s) (b s) e = 0)
    (hform : ∑ s, c s * D.formTable (a s) (b s) = 0) :
    (affineCurrentData D k hk).sym (∑ s, c s • (X (a s) * X (b s))) = 0 := by
  set E := affineCurrentData D k hk
  have hsym : E.sym (∑ s, c s • (X (a s) * X (b s)))
      = (currentC2 _ E.g).mkQ (∑ s, c s • E.sq (a s) (-1) (E.sq (b s) (-1) (simpleVOA D k hk).vacuum)) := by
    simp only [SqCurrentData.sym, SqCurrentData.ev_sum, LinearMap.sum_apply, map_sum, map_smul,
      SqCurrentData.ev_smul, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [SqCurrentData.ev_mul, SqCurrentData.ev_X, SqCurrentData.ev_X]
    rfl
  have hexp : ∀ s, E.sq (a s) (-1) (E.sq (b s) (-1) (simpleVOA D k hk).vacuum)
      = (simpleVOA D k hk).smul (affGen D k hk (a s)) (-1) (affGen D k hk (b s))
        + (1 / 2 : ℂ) • (simpleVOA D k hk).smul (affGen D k hk (a s)) 0 (affGen D k hk (b s))
        - (1 / 12 : ℂ) • (simpleVOA D k hk).smul (affGen D k hk (a s)) 1 (affGen D k hk (b s)) := by
    intro s
    change vSqZ _ (affGen D k hk (a s)) 1 (-1) (vSqZ _ (affGen D k hk (b s)) 1 (-1) _) = _
    rw [vSqZ_neg_one_vacuum, vSqZ_neg_one_current _ (simpleCurrentState_mem D k hk _)
      (simpleCurrentState_mem D k hk _)]
  have h1 : ∑ s, c s • (simpleVOA D k hk).smul (affGen D k hk (a s)) (-1) (affGen D k hk (b s))
      = 0 := by
    rw [← hsing, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, affGen_eq D k hk (b s), affGen_smul]
  have h2 : ∑ s, c s • (simpleVOA D k hk).smul (affGen D k hk (a s)) 0 (affGen D k hk (b s))
      = 0 := by
    simp only [affGen_bracket, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [← Finset.sum_smul, hbr e, zero_smul]
  have h3 : ∑ s, c s • (simpleVOA D k hk).smul (affGen D k hk (a s)) 1 (affGen D k hk (b s))
      = 0 := by
    simp only [affGen_form, smul_smul, ← Finset.sum_smul]
    rw [show ∑ s, c s * (k * D.formTable (a s) (b s)) = k * ∑ s, c s * D.formTable (a s) (b s) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring, hform, mul_zero,
      zero_smul]
  rw [hsym]
  simp only [hexp, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    smul_comm (c _) ((1 / 2 : ℂ)), smul_comm (c _) ((1 / 12 : ℂ)), ← Finset.smul_sum, h1, h2, h3,
    smul_zero, add_zero, sub_zero, map_zero]

end

end VOA.DeligneAudit.VacuumRelation

section AxiomAudit
#print axioms VOA.DeligneAudit.VacuumRelation.affineCurrentData
#print axioms VOA.DeligneAudit.VacuumRelation.vacuumQuarticRelation_affine_of_relations
#print axioms VOA.DeligneAudit.VacuumRelation.sym_step
#print axioms VOA.DeligneAudit.VacuumRelation.sym_singular
end AxiomAudit
