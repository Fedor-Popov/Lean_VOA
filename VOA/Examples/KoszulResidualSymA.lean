/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.KoszulResidualH0

/-!
# The symbol evaluation intertwines the degree-preserving positive modes

* `aPos hA c n` — the `R`-preserving component of the nonnegative mode `J^c_n` on `A`;
* `aPos_aLead_comm` — `[aPos c n, aLead (a, j)] = Σ_i f^{ca}_i aLead (i, j - n)` (`j ≥ n`), `0`
  otherwise (from the current algebra and the shift bounds);
* `aPos_evalA` — `[aPos c n, evalA p] = evalA (symDer c n p)`;
* `uPos c n` — the symbol derivation on `U`; `mPos hA c n` — the `R`-preserving component of
  `J^c_n` on the matter space;
* `ev_mPos` — `ev ∘ mPos c n = (aPos c n ⊗ 1 + 1 ⊗ J^c_n) ∘ ev`.

Everything is proved outright from `hA`.
-/

set_option linter.deprecated false

namespace VOA.KoszulResidual

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.LeeYangTransferAssembly VOA.KoszulConcrete MvPolynomial AffineVOA
open scoped TensorProduct

noncomputable section

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag)

/-- The shift of the `R`-preserving component of `J^c_n`: weight `-n`. -/
abbrev e0n (n : ℕ) : (ℤ × ℤ) × ℂ := ((0, 0), (((-(n : ℤ)) : ℤ) : ℂ))

/-- The `R`-preserving component of the nonnegative mode `J^c_n` on `A`. -/
def aPos (c : Fin 3) (n : ℕ) : Module.End ℂ ASpace :=
  compOp (aDeg_isInternal hA) (aMode c n) (· + e0n n)

theorem modePred_nonneg {n : ℕ} {δ : (ℤ × ℤ) × ℂ} (h : modePred (n : ℤ) δ) :
    ∃ d : ℤ, δ = ((2 * d, 0), (((-(n : ℤ)) : ℤ) : ℂ)) ∧ -1 ≤ d ∧ d ≤ 0 := by
  obtain ⟨d, rfl, h1, h2⟩ := h
  refine ⟨d, rfl, le_trans ?_ h1, le_trans h2 ?_⟩
  · unfold eN; split_ifs <;> norm_num
  · unfold eN; split_ifs <;> norm_num; omega

theorem huniq_pos_lead (c : Fin 3) (n : ℕ) (q : LexLetter) :
    ∀ δ δ', modePred (n : ℤ) δ → modePred (nq q) δ' → δ' + δ = eq q + e0n n → δ' = eq q := by
  intro δ δ' h h' he
  obtain ⟨d, rfl, hd0, hd1⟩ := modePred_nonneg h
  obtain ⟨d', rfl, hd0', hd1'⟩ := modePred_nq h'
  have h1 := congrArg (fun x : (ℤ × ℤ) × ℂ => x.1.1) he
  simp only [Prod.fst_add] at h1
  have : d' = 1 := by omega
  subst this
  simp

theorem huniq_lead_pos (c : Fin 3) (n : ℕ) (q : LexLetter) :
    ∀ δ δ', modePred (nq q) δ → modePred (n : ℤ) δ' → δ' + δ = e0n n + eq q → δ' = e0n n := by
  intro δ δ' h h' he
  obtain ⟨d, rfl, hd0, hd1⟩ := modePred_nq h
  obtain ⟨d', rfl, hd0', hd1'⟩ := modePred_nonneg h'
  have h1 := congrArg (fun x : (ℤ × ℤ) × ℂ => x.1.1) he
  simp only [Prod.fst_add] at h1
  have : d' = 0 := by omega
  subst this
  simp

theorem aPos_of_mem (c : Fin 3) (n : ℕ) {i : (ℤ × ℤ) × ℂ} {x : ASpace} (hx : x ∈ aDeg i) :
    aPos hA c n x = iproj (aDeg_isInternal hA) (i + e0n n) (aMode c n x) :=
  compOp_of_mem _ _ _ hx

theorem aPos_mem (c : Fin 3) (n : ℕ) {i : (ℤ × ℤ) × ℂ} {x : ASpace} (hx : x ∈ aDeg i) :
    aPos hA c n x ∈ aDeg (i + e0n n) :=
  compOp_mem _ _ (· + e0n n) hx

/-- The commutator target of `[aPos c n, aLead q]`. -/
def posLeadComm (c : Fin 3) (n : ℕ) (q : LexLetter) : Module.End ℂ ASpace :=
  if n ≤ (ofLex q).2 then
    ∑ i : Fin 3, fabc c (ofLex q).1 i • aLead hA (toLex (i, (ofLex q).2 - n))
  else 0

/-- Components of a mode with a target raising `R` by one, from a source piece. -/
theorem iproj_mode_eq_zero_R1 (c : Fin 3) {m' : ℤ} (hm' : 0 ≤ m') {i T : (ℤ × ℤ) × ℂ}
    (hT : T.1.1 = i.1.1 + 2) {x : ASpace} (hx : x ∈ aDeg i) :
    iproj (aDeg_isInternal hA) T (aMode c m' x) = 0 := by
  refine iproj_eq_zero_of_mem_iSup (aDeg_isInternal hA) (fun j => ∃ δ, modePred m' δ ∧ j = i + δ)
    ?_ ?_
  · have h := aMode_shifts hA c m' i x hx
    have hle : shiftTarget aDeg (modePred m') i ≤
        ⨆ (j : (ℤ × ℤ) × ℂ) (_ : ∃ δ, modePred m' δ ∧ j = i + δ), aDeg j :=
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
    aPos hA c n ∘ₗ aLead hA q - aLead hA q ∘ₗ aPos hA c n = posLeadComm hA c n q := by
  apply linearMap_ext_internal (aDeg_isInternal hA)
  intro i x hx
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply, aPos, aLead]
  rw [compOp_comp_of_mem _ _ _ _ _ _ _ (aMode_shifts hA _ _) (aMode_shifts hA _ _)
      (huniq_pos_lead c n q) hx,
    compOp_comp_of_mem _ _ _ _ _ _ _ (aMode_shifts hA _ _) (aMode_shifts hA _ _)
      (huniq_lead_pos c n q) hx]
  rw [show i + e0n n + eq q = i + eq q + e0n n by abel, ← map_sub]
  have hc := LinearMap.congr_fun (aAction.current_comm c (ofLex q).1 (n : ℤ) (nq q)) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply] at hc
  change aMode c (n : ℤ) (aMode (ofLex q).1 (nq q) x) -
    aMode (ofLex q).1 (nq q) (aMode c (n : ℤ) x) = _ at hc
  rw [hc, map_add, map_sum]
  -- the central term
  have hcen : iproj (aDeg_isInternal hA) (i + eq q + e0n n)
      ((if (n : ℤ) + nq q = 0 then (((n : ℤ) : ℂ) * (-4 / 3) * kappa c (ofLex q).1) •
        (LinearMap.id : Module.End ℂ ASpace) else 0) x) = 0 := by
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
    exact (aLead_of_mem hA q' hx).symm
  · rw [LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [map_smul]
    have h0 := iproj_mode_eq_zero_R1 hA i' (m' := (n : ℤ) + nq q) (by simp only [nq]; omega)
      (T := i + eq q + e0n n) (by
        have e1 : (eq q).1.1 = 2 := rfl
        have e2 : (e0n n).1.1 = 0 := rfl
        simp only [Prod.fst_add, e1, e2, add_zero]) hx
    change _ • iproj _ _ (aMode i' _ x) = 0
    rw [h0, smul_zero]

theorem evalA_symDer_X (c : Fin 3) (n : ℕ) (q : LexLetter) :
    (evalA hA (symDer c n (X q)) : Module.End ℂ ASpace) = -posLeadComm hA c n q := by
  rw [symDer_X, posLeadComm]
  split_ifs
  · rw [map_sum, AddSubmonoidClass.coe_finset_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Subalgebra.coe_smul, evalA_X, smul_neg]
  · simp

set_option maxHeartbeats 800000 in
/-- **The degree-preserving positive modes act on evaluated symbols by `symDer`.** -/
theorem aPos_evalA (c : Fin 3) (n : ℕ) (p : MvPolynomial LexLetter ℂ) :
    aPos hA c n * (evalA hA p : Module.End ℂ ASpace) -
      (evalA hA p : Module.End ℂ ASpace) * aPos hA c n =
      (evalA hA (symDer c n p) : Module.End ℂ ASpace) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have h1 : (evalA hA (MvPolynomial.C a) : Module.End ℂ ASpace) =
          a • (1 : Module.End ℂ ASpace) := by
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
      have hcomm := aPos_aLead_comm hA c n q
      have hcomm' : aPos hA c n * aLead hA q - aLead hA q * aPos hA c n =
          posLeadComm hA c n q := hcomm
      have hP : (evalA hA (symDer c n p) : Module.End ℂ ASpace) * aLead hA q =
          aLead hA q * (evalA hA (symDer c n p) : Module.End ℂ ASpace) :=
        evalA_comm_aLead hA _ q
      have e1 : (evalA hA (p * X q) : Module.End ℂ ASpace) =
          (evalA hA p : Module.End ℂ ASpace) * (-aLead hA q) := by
        rw [map_mul, Subalgebra.coe_mul, evalA_X]
      have e2 : (evalA hA (symDer c n (p * X q)) : Module.End ℂ ASpace) =
          (evalA hA p : Module.End ℂ ASpace) * (-posLeadComm hA c n q) +
            (-aLead hA q) * (evalA hA (symDer c n p) : Module.End ℂ ASpace) := by
        have hl : symDer c n (p * X q) = p * symDer c n (X q) + X q * symDer c n p := by
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        rw [hl, map_add, map_mul, map_mul, Subalgebra.coe_add, Subalgebra.coe_mul,
          Subalgebra.coe_mul, evalA_symDer_X, evalA_X]
      have hp' : aPos hA c n * (evalA hA p : Module.End ℂ ASpace) =
          (evalA hA p : Module.End ℂ ASpace) * aPos hA c n +
            (evalA hA (symDer c n p) : Module.End ℂ ASpace) := by
        rw [← hp]; abel
      rw [e1, e2, ← hcomm']
      calc aPos hA c n * ((evalA hA p : Module.End ℂ ASpace) * -aLead hA q) -
            (evalA hA p : Module.End ℂ ASpace) * -aLead hA q * aPos hA c n
          = -((aPos hA c n * (evalA hA p : Module.End ℂ ASpace)) * aLead hA q) +
            (evalA hA p : Module.End ℂ ASpace) * aLead hA q * aPos hA c n := by noncomm_ring
        _ = -(((evalA hA p : Module.End ℂ ASpace) * aPos hA c n +
              (evalA hA (symDer c n p) : Module.End ℂ ASpace)) * aLead hA q) +
            (evalA hA p : Module.End ℂ ASpace) * aLead hA q * aPos hA c n := by rw [hp']
        _ = -((evalA hA p : Module.End ℂ ASpace) * aPos hA c n * aLead hA q) -
              (evalA hA (symDer c n p) : Module.End ℂ ASpace) * aLead hA q +
            (evalA hA p : Module.End ℂ ASpace) * aLead hA q * aPos hA c n := by noncomm_ring
        _ = -((evalA hA p : Module.End ℂ ASpace) * aPos hA c n * aLead hA q) -
              aLead hA q * (evalA hA (symDer c n p) : Module.End ℂ ASpace) +
            (evalA hA p : Module.End ℂ ASpace) * aLead hA q * aPos hA c n := by rw [hP]
        _ = _ := by noncomm_ring

/-- The symbol derivation on `U` (the `R`-preserving part of `J^c_n`, `n ≥ 0`). -/
def uPos (c : Fin 3) (n : ℕ) : Module.End ℂ USpace :=
  PhiU.symm.toLinearMap ∘ₗ (symDer c n).toLinearMap ∘ₗ PhiU.toLinearMap

theorem PhiU_uPos (c : Fin 3) (n : ℕ) (u : USpace) : PhiU (uPos c n u) = symDer c n (PhiU u) := by
  simp [uPos]

/-- The `R`-preserving component of `J^c_n` (`n ≥ 0`) on the matter space. -/
def mPos (c : Fin 3) (n : ℕ) : Module.End ℂ MatterSpace :=
  TensorProduct.map (TensorProduct.map (aPos hA c n) LinearMap.id) LinearMap.id +
    TensorProduct.map (TensorProduct.map LinearMap.id (bMode c n)) LinearMap.id +
    TensorProduct.map LinearMap.id (uPos c n)

theorem aPos_evalA_apply (c : Fin 3) (n : ℕ) (p : MvPolynomial LexLetter ℂ) (x : ASpace) :
    aPos hA c n ((evalA hA p : Module.End ℂ ASpace) x) =
      (evalA hA p : Module.End ℂ ASpace) (aPos hA c n x) +
        (evalA hA (symDer c n p) : Module.End ℂ ASpace) x := by
  have h := congrArg (fun T : Module.End ℂ ASpace => T x) (aPos_evalA hA c n p)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [← h]; abel

/-- **`ev` intertwines the degree-preserving positive modes.** -/
theorem ev_mPos (c : Fin 3) (n : ℕ) (m : MatterSpace) :
    ev hA (mPos hA c n m) = TensorProduct.map (aPos hA c n) LinearMap.id (ev hA m) +
      TensorProduct.map LinearMap.id (bMode c n) (ev hA m) := by
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

end

end VOA.KoszulResidual
