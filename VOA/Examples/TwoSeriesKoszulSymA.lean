/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.KoszulResidualGr
import VOA.Examples.TwoSeriesKoszulEval

/-!
# Level-generic port of `KoszulResidualSymA`, `KoszulResidualGr`
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.KoszulResidual VOA.KoszulConcrete VOA.SymbolModel VOA.CyclicEval
open VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra Sl2CosetConcrete Sl2SemiInfinite
open AffineSl2GeneralRigidity AffineSl2BelowCritical VOA.LeeYangTransferAssembly MvPolynomial
open AffineVOA
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

variable (L : CosetLevels)

/-! ## Port of `KoszulResidualSymA` -/


variable (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))

/-- The `R`-preserving component of the nonnegative mode `J^c_n` on `A`. -/
def aPos (c : Fin 3) (n : ℕ) : Module.End ℂ (ASpace L) :=
  compOp ((aDeg_isInternal L) hA) ((aMode L) c n) (· + e0n n)

theorem aPos_of_mem (c : Fin 3) (n : ℕ) {i : (ℤ × ℤ) × ℂ} {x : (ASpace L)} (hx : x ∈ (aDeg L) i) :
    (aPos L) hA c n x = iproj ((aDeg_isInternal L) hA) (i + e0n n) ((aMode L) c n x) :=
  compOp_of_mem _ _ _ hx

theorem aPos_mem (c : Fin 3) (n : ℕ) {i : (ℤ × ℤ) × ℂ} {x : (ASpace L)} (hx : x ∈ (aDeg L) i) :
    (aPos L) hA c n x ∈ (aDeg L) (i + e0n n) :=
  compOp_mem _ _ (· + e0n n) hx

/-- The commutator target of `[(aPos L) c n, (aLead L) q]`. -/
def posLeadComm (c : Fin 3) (n : ℕ) (q : LexLetter) : Module.End ℂ (ASpace L) :=
  if n ≤ (ofLex q).2 then
    ∑ i : Fin 3, fabc c (ofLex q).1 i • (aLead L) hA (toLex (i, (ofLex q).2 - n))
  else 0

/-- Components of a mode with a target raising `R` by one, from a source piece. -/
theorem iproj_mode_eq_zero_R1 (c : Fin 3) {m' : ℤ} (hm' : 0 ≤ m') {i T : (ℤ × ℤ) × ℂ}
    (hT : T.1.1 = i.1.1 + 2) {x : (ASpace L)} (hx : x ∈ (aDeg L) i) :
    iproj ((aDeg_isInternal L) hA) T ((aMode L) c m' x) = 0 := by
  refine iproj_eq_zero_of_mem_iSup ((aDeg_isInternal L) hA) (fun j => ∃ δ, modePred m' δ ∧ j = i + δ)
    ?_ ?_
  · have h := (aMode_shifts L) hA c m' i x hx
    have hle : shiftTarget (aDeg L) (modePred m') i ≤
        ⨆ (j : (ℤ × ℤ) × ℂ) (_ : ∃ δ, modePred m' δ ∧ j = i + δ), (aDeg L) j :=
      iSup_le fun δ => iSup_le fun hδ => le_iSup_of_le (i + δ) (le_iSup_of_le ⟨δ, hδ, rfl⟩ le_rfl)
    exact hle h
  · rintro ⟨δ, ⟨d, rfl, -, hd⟩, rfl⟩
    have : eN m' = 0 := by simp [eN, hm']
    rw [this] at hd
    simp only [Prod.fst_add] at hT
    push_cast at hd
    omega

set_option maxHeartbeats 800000 in
/-- **The commutator of a degree-preserving positive mode with a leading creation mode.** -/
theorem aPos_aLead_comm (c : Fin 3) (n : ℕ) (q : LexLetter) :
    (aPos L) hA c n ∘ₗ (aLead L) hA q - (aLead L) hA q ∘ₗ (aPos L) hA c n = (posLeadComm L) hA c n q := by
  apply linearMap_ext_internal ((aDeg_isInternal L) hA)
  intro i x hx
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply, aPos, aLead]
  rw [compOp_comp_of_mem _ _ _ _ _ _ _ ((aMode_shifts L) hA _ _) ((aMode_shifts L) hA _ _)
      (huniq_pos_lead c n q) hx,
    compOp_comp_of_mem _ _ _ _ _ _ _ ((aMode_shifts L) hA _ _) ((aMode_shifts L) hA _ _)
      (huniq_lead_pos c n q) hx]
  rw [show i + e0n n + eq q = i + eq q + e0n n by abel, ← map_sub]
  have hc := LinearMap.congr_fun ((aAction L).current_comm c (ofLex q).1 (n : ℤ) (nq q)) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply] at hc
  change (aMode L) c (n : ℤ) ((aMode L) (ofLex q).1 (nq q) x) -
    (aMode L) (ofLex q).1 (nq q) ((aMode L) c (n : ℤ) x) = _ at hc
  rw [hc, map_add, map_sum]
  -- the central term
  have hcen : iproj ((aDeg_isInternal L) hA) (i + eq q + e0n n)
      ((if (n : ℤ) + nq q = 0 then (((n : ℤ) : ℂ) * L.kAct * kappa c (ofLex q).1) •
        (LinearMap.id : Module.End ℂ (ASpace L)) else 0) x) = 0 := by
    split_ifs
    · rw [LinearMap.smul_apply, LinearMap.id_apply, map_smul,
        iproj_of_mem_ne _ (by
          intro h
          have := congrArg (fun x : (ℤ × ℤ) × ℂ => x.1.1) h
          simp at this) hx, smul_zero]
    · rw [LinearMap.zero_apply, map_zero]
  rw [hcen, add_zero]
  rw [posLeadComm]
  split_ifs with hjn
  · rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [map_smul, LinearMap.smul_apply]
    congr 1
    set q' := toLex (i', (ofLex q).2 - n)
    have hnq : (n : ℤ) + nq q = nq q' := by
      simp only [nq, q', ofLex_toLex]; omega
    have hidx : i + eq q + e0n n = i + eq q' := by
      simp only [eq, e0n, q', letterWt, ofLex_toLex]
      rw [add_assoc]
      congr 1
      simp only [Prod.mk_add_mk, add_zero]
      congr 1
      push_cast [hjn]
      ring
    rw [hnq, hidx]
    exact ((aLead_of_mem L) hA q' hx).symm
  · rw [LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [map_smul]
    have h0 := (iproj_mode_eq_zero_R1 L) hA i' (m' := (n : ℤ) + nq q) (by simp only [nq]; omega)
      (T := i + eq q + e0n n) (by
        have e1 : (eq q).1.1 = 2 := rfl
        have e2 : (e0n n).1.1 = 0 := rfl
        simp only [Prod.fst_add, e1, e2, add_zero]) hx
    change _ • iproj _ _ ((aMode L) i' _ x) = 0
    rw [h0, smul_zero]

theorem evalA_symDer_X (c : Fin 3) (n : ℕ) (q : LexLetter) :
    ((evalA L) hA (symDer c n (X q)) : Module.End ℂ (ASpace L)) = -(posLeadComm L) hA c n q := by
  rw [symDer_X, posLeadComm]
  split_ifs
  · rw [map_sum, AddSubmonoidClass.coe_finset_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Subalgebra.coe_smul, evalA_X, smul_neg]
  · simp

set_option maxHeartbeats 800000 in
/-- **The degree-preserving positive modes act on evaluated symbols by `symDer`.** -/
theorem aPos_evalA (c : Fin 3) (n : ℕ) (p : MvPolynomial LexLetter ℂ) :
    (aPos L) hA c n * ((evalA L) hA p : Module.End ℂ (ASpace L)) -
      ((evalA L) hA p : Module.End ℂ (ASpace L)) * (aPos L) hA c n =
      ((evalA L) hA (symDer c n p) : Module.End ℂ (ASpace L)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have h1 : ((evalA L) hA (MvPolynomial.C a) : Module.End ℂ (ASpace L)) =
          a • (1 : Module.End ℂ (ASpace L)) := by
        rw [show MvPolynomial.C a = algebraMap ℂ (MvPolynomial LexLetter ℂ) a from rfl,
          AlgHom.commutes]
        rfl
      rw [h1, show symDer c n (MvPolynomial.C a) = 0 from Derivation.map_algebraMap _ a,
        map_zero,
        Subalgebra.coe_zero, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_self]
  | add p q hp hq =>
      rw [map_add, Subalgebra.coe_add, mul_add, add_mul, map_add, map_add, Subalgebra.coe_add,
        ← hp, ← hq]
      abel
  | mul_X p q hp =>
      have hcomm := (aPos_aLead_comm L) hA c n q
      have hcomm' : (aPos L) hA c n * (aLead L) hA q - (aLead L) hA q * (aPos L) hA c n =
          (posLeadComm L) hA c n q := hcomm
      have hP : ((evalA L) hA (symDer c n p) : Module.End ℂ (ASpace L)) * (aLead L) hA q =
          (aLead L) hA q * ((evalA L) hA (symDer c n p) : Module.End ℂ (ASpace L)) :=
        (evalA_comm_aLead L) hA _ q
      have e1 : ((evalA L) hA (p * X q) : Module.End ℂ (ASpace L)) =
          ((evalA L) hA p : Module.End ℂ (ASpace L)) * (-(aLead L) hA q) := by
        rw [map_mul, Subalgebra.coe_mul, evalA_X]
      have e2 : ((evalA L) hA (symDer c n (p * X q)) : Module.End ℂ (ASpace L)) =
          ((evalA L) hA p : Module.End ℂ (ASpace L)) * (-(posLeadComm L) hA c n q) +
            (-(aLead L) hA q) * ((evalA L) hA (symDer c n p) : Module.End ℂ (ASpace L)) := by
        have hl : symDer c n (p * X q) = p * symDer c n (X q) + X q * symDer c n p := by
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        rw [hl, map_add, map_mul, map_mul, Subalgebra.coe_add, Subalgebra.coe_mul,
          Subalgebra.coe_mul, evalA_symDer_X, evalA_X]
      have hp' : (aPos L) hA c n * ((evalA L) hA p : Module.End ℂ (ASpace L)) =
          ((evalA L) hA p : Module.End ℂ (ASpace L)) * (aPos L) hA c n +
            ((evalA L) hA (symDer c n p) : Module.End ℂ (ASpace L)) := by
        rw [← hp]; abel
      rw [e1, e2, ← hcomm']
      calc (aPos L) hA c n * (((evalA L) hA p : Module.End ℂ (ASpace L)) * -(aLead L) hA q) -
            ((evalA L) hA p : Module.End ℂ (ASpace L)) * -(aLead L) hA q * (aPos L) hA c n
          = -(((aPos L) hA c n * ((evalA L) hA p : Module.End ℂ (ASpace L))) * (aLead L) hA q) +
            ((evalA L) hA p : Module.End ℂ (ASpace L)) * (aLead L) hA q * (aPos L) hA c n := by noncomm_ring
        _ = -((((evalA L) hA p : Module.End ℂ (ASpace L)) * (aPos L) hA c n +
              ((evalA L) hA (symDer c n p) : Module.End ℂ (ASpace L))) * (aLead L) hA q) +
            ((evalA L) hA p : Module.End ℂ (ASpace L)) * (aLead L) hA q * (aPos L) hA c n := by rw [hp']
        _ = -(((evalA L) hA p : Module.End ℂ (ASpace L)) * (aPos L) hA c n * (aLead L) hA q) -
              ((evalA L) hA (symDer c n p) : Module.End ℂ (ASpace L)) * (aLead L) hA q +
            ((evalA L) hA p : Module.End ℂ (ASpace L)) * (aLead L) hA q * (aPos L) hA c n := by noncomm_ring
        _ = -(((evalA L) hA p : Module.End ℂ (ASpace L)) * (aPos L) hA c n * (aLead L) hA q) -
              (aLead L) hA q * ((evalA L) hA (symDer c n p) : Module.End ℂ (ASpace L)) +
            ((evalA L) hA p : Module.End ℂ (ASpace L)) * (aLead L) hA q * (aPos L) hA c n := by rw [hP]
        _ = _ := by noncomm_ring

/-- The symbol derivation on `U` (the `R`-preserving part of `J^c_n`, `n ≥ 0`). -/
def uPos (c : Fin 3) (n : ℕ) : Module.End ℂ (USpace L) :=
  (PhiU L).symm.toLinearMap ∘ₗ (symDer c n).toLinearMap ∘ₗ (PhiU L).toLinearMap

theorem PhiU_uPos (c : Fin 3) (n : ℕ) (u : (USpace L)) : (PhiU L) ((uPos L) c n u) = symDer c n ((PhiU L) u) := by
  simp [uPos]

/-- The `R`-preserving component of `J^c_n` (`n ≥ 0`) on the matter space. -/
def mPos (c : Fin 3) (n : ℕ) : Module.End ℂ (MatterSpace L) :=
  TensorProduct.map (TensorProduct.map ((aPos L) hA c n) LinearMap.id) LinearMap.id +
    TensorProduct.map (TensorProduct.map LinearMap.id (bMode c n)) LinearMap.id +
    TensorProduct.map LinearMap.id ((uPos L) c n)

theorem aPos_evalA_apply (c : Fin 3) (n : ℕ) (p : MvPolynomial LexLetter ℂ) (x : (ASpace L)) :
    (aPos L) hA c n (((evalA L) hA p : Module.End ℂ (ASpace L)) x) =
      ((evalA L) hA p : Module.End ℂ (ASpace L)) ((aPos L) hA c n x) +
        ((evalA L) hA (symDer c n p) : Module.End ℂ (ASpace L)) x := by
  have h := congrArg (fun T : Module.End ℂ (ASpace L) => T x) ((aPos_evalA L) hA c n p)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [← h]; abel

/-- **`(ev L)` intertwines the degree-preserving positive modes.** -/
theorem ev_mPos (c : Fin 3) (n : ℕ) (m : (MatterSpace L)) :
    (ev L) hA ((mPos L) hA c n m) = TensorProduct.map ((aPos L) hA c n) LinearMap.id ((ev L) hA m) +
      TensorProduct.map LinearMap.id (bMode c n) ((ev L) hA m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | tmul xy u =>
      simp only [mPos, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply, map_add,
        ev_tmul, evU_apply, PhiU_uPos]
      induction xy using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          have h := congrArg₂ (· + ·) hx hy
          simp only [map_add] at h ⊢
          rw [← sub_eq_zero] at h ⊢
          rw [← h]
          abel
      | tmul x y =>
          simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.id_apply,
            aPos_evalA_apply, TensorProduct.add_tmul]
          abel


/-! ## Port of `KoszulResidualGr` -/


variable (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))

theorem aDeg_le_aFil (r : ℕ) {i : (ℤ × ℤ) × ℂ} (hi : i.1 = (2 * (r : ℤ), 0)) :
    (aDeg L) i ≤ (aFil L) r := by
  refine iSup_le fun m => iSup_le fun p => iSup_le fun h => ?_
  subst h
  have hp : p = r := by
    have := congrArg Prod.fst hi
    simp only [layerIndex] at this
    omega
  subst hp
  rintro _ ⟨x, hx, rfl⟩
  exact Submodule.mem_iSup_of_mem m (GradedFlag.layer_le_pieceIn (affineFlag L) m _ p hx)

/-- The `R = r` part of an index-wise map into `gr_r A`. -/
def grPiece (r : ℕ) (i : (ℤ × ℤ) × ℂ) : (aDeg L) i →ₗ[ℂ] (GrA L) r :=
  if h : i.1 = (2 * (r : ℤ), 0) then
    ((grKer L) r).mkQ ∘ₗ Submodule.inclusion ((aDeg_le_aFil L) r h)
  else 0

/-- `A → gr_r A`: the class of the `R = r` component. -/
def grMapA (r : ℕ) : (ASpace L) →ₗ[ℂ] (GrA L) r :=
  DirectSum.toModule ℂ _ _ ((grPiece L) r) ∘ₗ (internalEquiv ((aDeg_isInternal L) hA)).symm.toLinearMap

theorem grMapA_of_mem (r : ℕ) {i : (ℤ × ℤ) × ℂ} (hi : i.1 = (2 * (r : ℤ), 0)) {x : (ASpace L)}
    (hx : x ∈ (aDeg L) i) :
    (grMapA L) hA r x = ((grKer L) r).mkQ ⟨x, (aDeg_le_aFil L) r hi hx⟩ := by
  simp only [grMapA, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [internalEquiv_symm_of_mem _ hx, ← DirectSum.lof_eq_of ℂ, DirectSum.toModule_lof, grPiece,
    dif_pos hi]
  rfl

/-- The layers of `R = r` (all weights). -/
def SR (r : ℕ) : Submodule ℂ (ASpace L) :=
  ⨆ (i : (ℤ × ℤ) × ℂ) (_ : i.1 = (2 * (r : ℤ), 0)), (aDeg L) i

theorem SR_le_aFil (r : ℕ) : (SR L) r ≤ (aFil L) r :=
  iSup_le fun _ => iSup_le fun hi => (aDeg_le_aFil L) r hi

theorem grMapA_of_SR (r : ℕ) {x : (ASpace L)} (hx : x ∈ (SR L) r) :
    (grMapA L) hA r x = ((grKer L) r).mkQ ⟨x, (SR_le_aFil L) r hx⟩ := by
  induction hx using Submodule.iSup_induction' with
  | mem i y hy =>
      by_cases hi : i.1 = (2 * (r : ℤ), 0)
      · rw [iSup_pos hi] at hy
        exact (grMapA_of_mem L) hA r hi hy
      · rw [iSup_neg hi, Submodule.mem_bot] at hy
        subst hy
        rw [map_zero]
        exact (map_zero _).symm
  | zero => rw [map_zero]; exact (map_zero _).symm
  | add x y hx hy ihx ihy =>
      rw [map_add, ihx, ihy, ← map_add]
      rfl

/-- **`(grMapA L)` is injective on the layers of `R = r`.** -/
theorem grMapA_injOn (r : ℕ) {x : (ASpace L)} (hx : x ∈ (SR L) r) (h0 : (grMapA L) hA r x = 0) : x = 0 := by
  rw [(grMapA_of_SR L) hA r hx, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  have hlt : x ∈ (aFilLT L) r := h0
  refine eq_of_iproj_eq ((aDeg_isInternal L) hA) fun j => ?_
  rw [map_zero]
  by_cases hj : j.1 = (2 * (r : ℤ), 0)
  · -- `x` lies in the layers below `r`
    rcases r with _ | r
    · rw [aFilLT, Submodule.mem_bot] at hlt; rw [hlt, map_zero]
    · rw [aFilLT] at hlt
      refine iproj_eq_zero_of_mem_iSup ((aDeg_isInternal L) hA)
        (fun j : (ℤ × ℤ) × ℂ => ∃ s m, s ≤ r ∧ layerIndex s m = j) ?_ ?_
      · refine Submodule.iSup_induction _ (motive := fun x => x ∈ ⨆ (j : (ℤ × ℤ) × ℂ)
          (_ : ∃ s m, s ≤ r ∧ layerIndex s m = j), (aDeg L) j) hlt ?_ (Submodule.zero_mem _)
          (fun _ _ => Submodule.add_mem _)
        intro m y hy
        have h := piece_le_iSup_layerDeg (affineForm L) (affineRealStructure L) (affineFlag L) hA
          (affineGramRefl L) r m hy
        have hle : (⨆ (s : ℕ) (_ : s ≤ r), (aDeg L) (layerIndex s m)) ≤
            ⨆ (j : (ℤ × ℤ) × ℂ) (_ : ∃ s m, s ≤ r ∧ layerIndex s m = j), (aDeg L) j :=
          iSup_le fun s => iSup_le fun hs =>
            le_iSup_of_le (layerIndex s m) (le_iSup_of_le ⟨s, m, hs, rfl⟩ le_rfl)
        exact hle h
      · rintro ⟨s, m, hs, rfl⟩
        have := congrArg Prod.fst hj
        simp only [layerIndex] at this
        omega
  · exact iproj_eq_zero_of_mem_iSup ((aDeg_isInternal L) hA) _ hx hj

theorem aMode_sub_aPos_mem (c : Fin 3) (n : ℕ) (r : ℕ) {i : (ℤ × ℤ) × ℂ}
    (hi : i.1 = (2 * (r : ℤ), 0)) {x : (ASpace L)} (hx : x ∈ (aDeg L) i) :
    (aMode L) c n x - (aPos L) hA c n x ∈ (aFilLT L) r := by
  rw [(aPos_of_mem L) hA c n hx]
  have h := sub_iproj_mem_ne ((aDeg_isInternal L) hA) (e := e0n n) ((aMode_shifts L) hA c n i x hx)
  refine (iSup_le fun j => iSup_le fun hj => ?_ : _ ≤ (aFilLT L) r) h
  obtain ⟨δ, hδ, hne, rfl⟩ := hj
  obtain ⟨d, rfl, hd1, hd0⟩ := modePred_nonneg hδ
  have hd : d = -1 := by
    rcases (show d = -1 ∨ d = 0 by omega) with h | h
    · exact h
    · subst h; exact absurd (by simp) hne
  subst hd
  rcases r with _ | r
  · rw [show (aDeg L) (i + ((2 * -1, 0), ((-(n : ℤ) : ℤ) : ℂ))) =
        layerDeg (affineForm L) (affineFlag L) (i + ((2 * -1, 0), ((-(n : ℤ) : ℤ) : ℂ))) from rfl,
      layerDeg_eq_bot_of (affineForm L) (affineFlag L)]
    · exact bot_le
    · intro t m h
      have := congrArg (fun x : (ℤ × ℤ) × ℂ => x.1.1) h
      simp only [layerIndex, Prod.fst_add, hi] at this
      omega
  · refine ((aDeg_le_aFil L) r ?_).trans le_rfl
    simp only [Prod.fst_add, hi, Prod.mk_add_mk]
    push_cast; ring_nf

theorem grMapA_aPos_of_mem (c : Fin 3) (n : ℕ) (r : ℕ) {i : (ℤ × ℤ) × ℂ}
    (hi : i.1 = (2 * (r : ℤ), 0)) {x : (ASpace L)} (hx : x ∈ (aDeg L) i) :
    (grMapA L) hA r ((aPos L) hA c n x) = (grRho L) r (c, n) ((grMapA L) hA r x) := by
  have hi' : (i + e0n n).1 = (2 * (r : ℤ), 0) := by simp [hi]
  rw [(grMapA_of_mem L) hA r hi' ((aPos_mem L) hA c n hx), (grMapA_of_mem L) hA r hi hx]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, grRho_mk, Submodule.Quotient.eq]
  have h := (aMode_sub_aPos_mem L) hA c n r hi hx
  change ((aPos L) hA c n x - (aMode L) c n x) ∈ (aFilLT L) r
  rw [← neg_sub]
  exact Submodule.neg_mem _ h

/-- **`(grMapA L)` intertwines `(aPos L)` with the induced action on `gr_r A`.** -/
theorem grMapA_aPos (c : Fin 3) (n : ℕ) (r : ℕ) {x : (ASpace L)} (hx : x ∈ (SR L) r) :
    (grMapA L) hA r ((aPos L) hA c n x) = (grRho L) r (c, n) ((grMapA L) hA r x) := by
  induction hx using Submodule.iSup_induction' with
  | mem i y hy =>
      by_cases hi : i.1 = (2 * (r : ℤ), 0)
      · rw [iSup_pos hi] at hy
        exact (grMapA_aPos_of_mem L) hA c n r hi hy
      · rw [iSup_neg hi, Submodule.mem_bot] at hy
        subst hy
        simp
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add, map_add, ihx, ihy, map_add, map_add]

/-! ### `(PiR L) = (grMapA L) ⊗ 1` -/

/-- `A ⊗ B → gr_r A ⊗ B`. -/
def PiR (r : ℕ) : (ASpace L) ⊗[ℂ] BSpace →ₗ[ℂ] (GrA L) r ⊗[ℂ] BSpace :=
  TensorProduct.map ((grMapA L) hA r) LinearMap.id

theorem tensorDeg_mem_range (r : ℕ) {w : ℂ} {x : (ASpace L) ⊗[ℂ] BSpace}
    (hx : x ∈ tensorDeg (aDeg L) bDeg ((2 * (r : ℤ), 0), w)) :
    x ∈ LinearMap.range (LinearMap.rTensor BSpace ((SR L) r).subtype) := by
  refine tensorDeg_induction (aDeg L) bDeg _ (fun x => x ∈ LinearMap.range
    (LinearMap.rTensor BSpace ((SR L) r).subtype)) (Submodule.zero_mem _)
    (fun _ _ => Submodule.add_mem _) (fun c _ h => Submodule.smul_mem _ c h) ?_ x hx
  intro b a ha y hy
  by_cases hb : b.1 = (2 * (r : ℤ), 0)
  · exact ⟨⟨a, Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem hb ha)⟩ ⊗ₜ[ℂ] y, rfl⟩
  · have hy0 : y = 0 := by
      unfold bDeg trivialDeg at hy
      split_ifs at hy with h
      · exfalso; apply hb
        have := h
        simp only [Prod.fst_sub] at this
        exact eq_of_sub_pair this
      · exact (Submodule.mem_bot ℂ).mp hy
    rw [hy0, TensorProduct.tmul_zero]
    exact Submodule.zero_mem _

/-- **`(PiR L)` is injective on `tensorDeg (aDeg L) bDeg ((2r,0), w)`.** -/
theorem PiR_injOn (r : ℕ) {w : ℂ} {x : (ASpace L) ⊗[ℂ] BSpace}
    (hx : x ∈ tensorDeg (aDeg L) bDeg ((2 * (r : ℤ), 0), w)) (h0 : (PiR L) hA r x = 0) : x = 0 := by
  obtain ⟨x', rfl⟩ := (tensorDeg_mem_range L) r hx
  have hinj : Function.Injective ((grMapA L) hA r ∘ₗ ((SR L) r).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Subtype.ext ((grMapA_injOn L) hA r v.2 hv)
  have h := Module.Flat.rTensor_preserves_injective_linearMap (R := ℂ) (M := BSpace) _ hinj
  have hx' : LinearMap.rTensor BSpace ((grMapA L) hA r ∘ₗ ((SR L) r).subtype) x' = 0 := by
    rw [LinearMap.rTensor_comp_apply]; exact h0
  rw [show x' = 0 from h (by rw [hx', map_zero]), map_zero]

theorem PiR_aPos (r : ℕ) (c : Fin 3) (n : ℕ) {w : ℂ} {x : (ASpace L) ⊗[ℂ] BSpace}
    (hx : x ∈ tensorDeg (aDeg L) bDeg ((2 * (r : ℤ), 0), w)) :
    (PiR L) hA r (TensorProduct.map ((aPos L) hA c n) LinearMap.id x) =
      LinearMap.rTensor BSpace ((grRho L) r (c, n)) ((PiR L) hA r x) := by
  obtain ⟨x', rfl⟩ := (tensorDeg_mem_range L) r hx
  clear hx
  induction x' using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a y =>
      simp only [PiR, LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        Submodule.subtype_apply]
      rw [(grMapA_aPos L) hA c n r a.2]

theorem PiR_bMode (r : ℕ) (c : Fin 3) (n : ℕ) (x : (ASpace L) ⊗[ℂ] BSpace) :
    (PiR L) hA r (TensorProduct.map LinearMap.id (bMode c n) x) =
      LinearMap.lTensor ((GrA L) r) (CyclicEval.bMode (c, n)) ((PiR L) hA r x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a y => rfl

/-- `(PiR L)` lands in the right weight. -/
theorem PiR_weight (r : ℕ) (n0 : ℤ) {x : (ASpace L) ⊗[ℂ] BSpace}
    (hx : x ∈ tensorDeg (aDeg L) bDeg ((2 * (r : ℤ), 0), (n0 : ℂ))) :
    (PiR L) hA r x ∈ tensorWeight ((grDeg L) r) bWeight n0 := by
  refine tensorDeg_induction (aDeg L) bDeg _ (fun x => (PiR L) hA r x ∈ tensorWeight ((grDeg L) r) bWeight n0)
    (by simp) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_ x hx
  intro b a ha y hy
  by_cases hb1 : b.1 = (2 * (r : ℤ), 0)
  · by_cases hb : ∃ d : ℤ, b = layerIndex r d
    · obtain ⟨d, rfl⟩ := hb
      have hy' : y ∈ bWeight (n0 - d) := by
        unfold bDeg trivialDeg at hy
        split_ifs at hy with h
        · unfold bWeight
          convert hy using 2
          simp [layerIndex]
        · rw [Submodule.mem_bot] at hy; rw [hy]; exact Submodule.zero_mem _
      have ha' : (grMapA L) hA r a ∈ (grDeg L) r d := by
        rw [(grMapA_of_mem L) hA r rfl ha]
        refine ⟨⟨a, (aDeg_le_aFil L) r rfl ha⟩, ?_, rfl⟩
        have ha2 := ha
        rw [show (aDeg L) (layerIndex r d) = layerDeg (affineForm L) (affineFlag L) (layerIndex r d) from rfl,
          layerDeg_layerIndex] at ha2
        obtain ⟨z, hz, hza⟩ := ha2
        change a ∈ (affineFlag L).piece r d
        rw [← hza]
        exact GradedFlag.layer_le_pieceIn (affineFlag L) d _ r hz
      rw [PiR, TensorProduct.map_tmul, LinearMap.id_apply]
      exact Submodule.mem_iSup_of_mem d (Submodule.apply_mem_map₂ _ ha' hy')
    · push Not at hb
      have hbot : (aDeg L) b = ⊥ := layerDeg_eq_bot_of (affineForm L) (affineFlag L) (fun t m h => by
        have ht : t = r := by
          have := congrArg (fun x : (ℤ × ℤ) × ℂ => x.1.1) h
          simp only [layerIndex, hb1] at this
          omega
        subst ht
        exact hb m h.symm)
      rw [hbot, Submodule.mem_bot] at ha
      rw [ha, TensorProduct.zero_tmul, map_zero]; exact Submodule.zero_mem _
  · have hy0 : y = 0 := by
      unfold bDeg trivialDeg at hy
      split_ifs at hy with h
      · exfalso; apply hb1
        simp only [Prod.fst_sub] at h
        exact eq_of_sub_pair h
      · exact (Submodule.mem_bot ℂ).mp hy
    rw [hy0, TensorProduct.tmul_zero, map_zero]; exact Submodule.zero_mem _

/-! ### The symbol evaluation preserves the interpreted index -/

theorem rTensor_sum_apply {ι : Type*} (s : Finset ι) (f : ι → Module.End ℂ (ASpace L))
    (xy : (ASpace L) ⊗[ℂ] BSpace) :
    LinearMap.rTensor BSpace (∑ i ∈ s, f i) xy = ∑ i ∈ s, LinearMap.rTensor BSpace (f i) xy := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.rTensor_add,
        LinearMap.add_apply, ih]

theorem evalA_word_mem (l : List LexLetter) {j : (ℤ × ℤ) × ℂ} {x : (ASpace L)} (hx : x ∈ (aDeg L) j) :
    ((evalA L) hA (monomial (expOf l) 1) : Module.End ℂ (ASpace L)) x ∈
      (aDeg L) (j + ((2 * (l.length : ℤ), 0), ((enOf (expOf l) : ℕ) : ℂ))) := by
  induction l with
  | nil =>
      have h1 : (monomial (expOf []) (1 : ℂ) : MvPolynomial LexLetter ℂ) = 1 := by
        simp [expOf]
      rw [h1, map_one, Subalgebra.coe_one, Module.End.one_apply]
      convert hx using 2
      ext <;> simp [expOf]
  | cons q l ih =>
      rw [monomial_expOf_cons, map_mul, Subalgebra.coe_mul, evalA_X, Module.End.mul_apply,
        LinearMap.neg_apply]
      have h := (aLead_mem L) hA q ih
      refine Submodule.neg_mem _ ?_
      have e : j + ((2 * ((q :: l).length : ℤ), 0), ((enOf (expOf (q :: l)) : ℕ) : ℂ)) =
          j + ((2 * (l.length : ℤ), 0), ((enOf (expOf l) : ℕ) : ℂ)) + eq q := by
        rw [add_assoc]
        congr 1
        rw [expOf_cons]
        simp only [enOf, map_add, Finsupp.weight_single, smul_eq_mul, one_mul, eq, letterWt,
          List.length_cons]
        ext <;> simp <;> push_cast <;> ring
      rw [e]
      exact h

theorem evalA_monomial_mem (μ : CurrentIndex) {j : (ℤ × ℤ) × ℂ} {x : (ASpace L)} (hx : x ∈ (aDeg L) j) :
    ((evalA L) hA (monomial μ 1) : Module.End ℂ (ASpace L)) x ∈
      (aDeg L) (j + ((2 * (μ.degree : ℤ), 0), ((enOf μ : ℕ) : ℂ))) := by
  have h := (evalA_word_mem L) hA (lexExponentWord μ) hx
  rw [expOf_lexExponentWord] at h
  have hl : (lexExponentWord μ).length = μ.degree := by
    rw [← degree_expOf, expOf_lexExponentWord]
  rwa [hl] at h

/-- **The symbol evaluation preserves the interpreted index.** -/
theorem ev_mem (i : (ℤ × ℤ) × ℂ) :
    ∀ m ∈ (matterDeg L) i, (ev L) hA m ∈ tensorDeg (aDeg L) bDeg i := by
  refine tensorDeg_induction (tensorDeg (aDeg L) bDeg) (uDeg L) i _ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_
  intro b xy hxy u hu
  rw [ev_tmul, evU_apply]
  by_cases hi : ∃ t m, layerIndex t m = i - b
  · obtain ⟨t, m, htm⟩ := hi
    rw [← htm] at hu
    have hsupp := (PhiU_support_of_mem L) hu
    rw [((PhiU L) u).as_sum, map_sum, AddSubmonoidClass.coe_finset_sum, rTensor_sum_apply]
    refine Submodule.sum_mem _ fun μ hμ => ?_
    obtain ⟨hdeg, hen⟩ := hsupp μ hμ
    rw [show monomial μ (coeff μ ((PhiU L) u)) = coeff μ ((PhiU L) u) • monomial μ 1 by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, Subalgebra.coe_smul,
      LinearMap.rTensor_smul, LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    have h := tensorDeg_map_shift (aDeg L) bDeg
      (((evalA L) hA (monomial μ 1) : Module.End ℂ (ASpace L))) LinearMap.id
      ((2 * (μ.degree : ℤ), 0), ((enOf μ : ℕ) : ℂ)) 0
      (fun j x hx => (evalA_monomial_mem L) hA μ hx) (fun j y hy => by rwa [add_zero]) b xy hxy
    have e : b + (((2 * (μ.degree : ℤ), 0), ((enOf μ : ℕ) : ℂ)) + 0) = i := by
      rw [add_zero, hdeg]
      have : ((2 * (t : ℤ), 0), ((enOf μ : ℕ) : ℂ)) = i - b := by
        rw [← htm]; simp only [layerIndex]; rw [← hen]; push_cast; rfl
      rw [this]; abel
    rwa [e] at h
  · push Not at hi
    rw [(uDeg_eq_bot_of L) hi, Submodule.mem_bot] at hu
    rw [hu, map_zero, map_zero, ZeroMemClass.coe_zero, LinearMap.rTensor_zero,
      LinearMap.zero_apply]
    exact Submodule.zero_mem _


end

end VOA.TwoSeries
