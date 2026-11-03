/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneVacuumRelationCarrier
import VOA.DeligneAudit.E8LieSingular
import VOA.DeligneAudit.E8CarrierData
import VOA.DeligneAudit.E8VacuumStepAll
import VOA.DeligneAudit.DeligneMLDETypes

/-!
# `E₈`: the vacuum quartic relation of `L_{-6}(𝔢₈)` and the MLDE target bound

`targetLowerBound_of_carrierData` applied to `E8data` and the cert-basis `LieData` `e8CertData`:

* the highest relation (`relQ 0`) has vanishing square symbol by `sym_singular`, from the singular vector
  `sv` (`E8LieSingular.simpleProjection_sv`) and the two shadow checks (`hw_bracket_shadow`,
  `hw_form_shadow`);
* every other relation by the BFS step `ad x_f (P_p) = g · P_s` (`stepOK_all`, kernel-checked sparse
  identities) through `sym_step`, by strong induction (`sym_rel_all`);
* `casPoly = 2 · Q` (`casPoly_eq`), from a sparse quadratic identity;
* `c = 248 · (-6)/24 = -62 = -2(30+1)`.

`E8Lie.vacuumQuarticRelation8 : VacuumQuarticRelation W8 ((30+1)(5·30-6))` and
`E8Lie.targetLowerBoundQ8 : TargetLowerBoundQ W8 (mldeCoeff 30)`.
-/

namespace VOA.DeligneAudit.E8Lie

open MvPolynomial VOA VOA.AffineGeneral VOA.DeligneAudit.VacuumRelation
  VOA.DeligneAudit.DeligneMLDE VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E7Sparse
  VOA.DeligneAudit.DeligneCarrier.E8

noncomputable section

set_option maxRecDepth 100000

/-- `L_{-6}(𝔢₈)` in the cert basis. -/
abbrev W8 := simpleVOA e8CertData (-6) hk8

/-- Its square-bracket current data. -/
abbrev E8C : SqCurrentData W8 (Fin 248) := affineCurrentData e8CertData (-6) hk8

/-! ## `ad x_f` on sparse quadratic lists -/

theorem list_X_eq_sum (l : List (Fin 248 × ℤ)) :
    (l.map fun t => ((t.2 : ℤ) : MvPolynomial (Fin 248) ℂ) * X t.1).sum
      = ∑ c, ((((l.map fun t => if t.1 = c then t.2 else 0).sum : ℤ) : ℂ)) • X c := by
  induction l with
  | nil => simp
  | cons t l ih =>
      rw [List.map_cons, List.sum_cons, ih]
      simp only [List.map_cons, List.sum_cons, Int.cast_add, add_smul, Finset.sum_add_distrib,
        apply_ite (fun z : ℤ => (z : ℂ)), Int.cast_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      congr 1
      rw [← map_intCast (MvPolynomial.C (σ := Fin 248) (R := ℂ)), MvPolynomial.smul_eq_C_mul]

theorem adG_X_sparse (f i : Fin 248) :
    adG e8CertData.structureConstant f (X i)
      = ((sL f i).map fun t => ((t.2 : ℤ) : MvPolynomial (Fin 248) ℂ) * X t.1).sum := by
  rw [adG_X, list_X_eq_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [structureConstant_eq]
  rfl

theorem sLn_eq (f i : Fin 248) : sLn f i = (sL f i).map fun t => (t.1.val, t.2) := rfl

theorem adG_Xn (f : Fin 248) (i : ℕ) (hi : i < 248) :
    adG e8CertData.structureConstant f (Xn 248 i)
      = ((sLn f i).map fun kv => ((kv.2 : ℤ) : MvPolynomial (Fin 248) ℂ) * Xn 248 kv.1).sum := by
  have h := sLn_eq f ⟨i, hi⟩
  simp only [Fin.val_mk] at h
  rw [show Xn 248 i = X ⟨i, hi⟩ by rw [Xn, dif_pos hi], adG_X_sparse, h, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  rw [Xn_fin]

theorem quadP_cons' (t : ℕ × ℕ × ℤ) (l : List (ℕ × ℕ × ℤ)) :
    quadP 248 (t :: l) = ((t.2.2 : ℤ) : MvPolynomial (Fin 248) ℂ) * (Xn 248 t.1 * Xn 248 t.2.1)
      + quadP 248 l := by
  simp [quadP]

theorem quadP_append' (l₁ l₂ : List (ℕ × ℕ × ℤ)) :
    quadP 248 (l₁ ++ l₂) = quadP 248 l₁ + quadP 248 l₂ := by
  simp [quadP]

theorem quadP_map_left (c : ℤ) (j : ℕ) (L : List (ℕ × ℤ)) :
    quadP 248 (L.map fun kv => (kv.1, j, c * kv.2))
      = ((c : ℤ) : MvPolynomial (Fin 248) ℂ) * Xn 248 j *
        (L.map fun kv => ((kv.2 : ℤ) : MvPolynomial (Fin 248) ℂ) * Xn 248 kv.1).sum := by
  induction L with
  | nil => simp [quadP]
  | cons kv L ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      rw [quadP_cons', ih]
      push_cast
      ring

theorem quadP_map_right (c : ℤ) (i : ℕ) (L : List (ℕ × ℤ)) :
    quadP 248 (L.map fun kv => (i, kv.1, c * kv.2))
      = ((c : ℤ) : MvPolynomial (Fin 248) ℂ) * Xn 248 i *
        (L.map fun kv => ((kv.2 : ℤ) : MvPolynomial (Fin 248) ℂ) * Xn 248 kv.1).sum := by
  induction L with
  | nil => simp [quadP]
  | cons kv L ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      rw [quadP_cons', ih]
      push_cast
      ring

/-- **The sparse derivation is `ad x_f`.** -/
theorem quadP_dQuad (f : Fin 248) (P : List (ℕ × ℕ × ℤ)) (hP : inRange248 P = true) :
    quadP 248 (dQuad f P) = adG e8CertData.structureConstant f (quadP 248 P) := by
  induction P with
  | nil => simp [dQuad, quadP]
  | cons t P ih =>
      simp only [inRange248, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hP
      obtain ⟨⟨h1, h2⟩, hP⟩ := hP
      rw [dQuad, List.flatMap_cons, ← dQuad, quadP_append', quadP_append', quadP_map_left,
        quadP_map_right, ih hP, quadP_cons', map_add, Derivation.leibniz, Derivation.leibniz,
        adG_Xn f _ h1, adG_Xn f _ h2]
      have hc : adG e8CertData.structureConstant f ((t.2.2 : ℤ) : MvPolynomial (Fin 248) ℂ) = 0 := by
        rw [← map_intCast (MvPolynomial.C (σ := Fin 248) (R := ℂ)), ← MvPolynomial.algebraMap_eq,
          Derivation.map_algebraMap]
      rw [hc, smul_zero, add_zero, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      ring

/-- A quadratic list is zero if `X₀` times it passes the cubic check. -/
theorem quadP_eq_zero_of_check (l : List (ℕ × ℕ × ℤ)) (h : cubicZero (E7Sparse.mulX 1 0 l) = true) :
    quadP 248 l = 0 := by
  have h0 := cubicP_eq_zero_of_cubicZero (n := 248) _ h
  rw [E7Sparse.cubicP_mulX, Int.cast_one, one_mul, show Xn 248 0 = X (0 : Fin 248) by rw [Xn, dif_pos (by norm_num)]; rfl] at h0
  exact (mul_eq_zero.mp h0).resolve_left (X_ne_zero _)

theorem quadP_map_scale (g : ℤ) (l : List (ℕ × ℕ × ℤ)) :
    quadP 248 (l.map fun x => (x.1, x.2.1, -(g * x.2.2)))
      = -((g : ℤ) : MvPolynomial (Fin 248) ℂ) * quadP 248 l := by
  induction l with
  | nil => simp [quadP]
  | cons x l ih =>
      simp only [List.map_cons] at ih ⊢
      rw [quadP_cons', quadP_cons', ih]
      push_cast
      ring

/-! ## Propagation -/

theorem relQ_inRange (b : ℕ) (hb : b < 3875) : inRange248 (relQ b) = true :=
  List.all_eq_true.mp rel_inRange b (List.mem_range.mpr hb)

/-- One BFS step carries a vanishing symbol forward. -/
theorem sym_of_step (s : ℕ) (hs : s < 3875) (h : stepOK s = true)
    (hp : E8C.sym (quadP 248 (relQ (stepOf s).1)) = 0) : E8C.sym (quadP 248 (relQ s)) = 0 := by
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlt, hf⟩, hg⟩, hc⟩ := h
  have hz := quadP_eq_zero_of_check _ hc
  rw [stepList, quadP_append', quadP_map_scale,
    quadP_dQuad ⟨(stepOf s).2.1, hf⟩ _ (relQ_inRange _ (by omega))] at hz
  have hstep : (1 : ℂ) • adG e8CertData.structureConstant ⟨(stepOf s).2.1, hf⟩
      (quadP 248 (relQ (stepOf s).1)) = ((stepOf s).2.2 : ℂ) • quadP 248 (relQ s) := by
    rw [one_smul, MvPolynomial.smul_eq_C_mul, map_intCast]
    linear_combination hz
  exact sym_step e8CertData (-6) hk8 (by exact_mod_cast hg) hstep hp

/-- The highest relation, from the singular vector. -/
theorem relQ_zero : relQ 0 = [(107, 127, -1), (110, 126, -1), (113, 125, -1), (115, 124, -1),
    (117, 123, -1), (119, 122, -1), (120, 121, 1)] := by decide +kernel

theorem hw_bracket_shadowZ : ∀ e : Fin 248, ∑ i, cz i * sZ (ta i) (tb i) e = 0 := by decide +kernel

theorem hw_form_shadowZ : ∑ i, cz i * Gz (ta i) (tb i) = 0 := by decide +kernel

theorem sym_rel_zero : E8C.sym (quadP 248 (relQ 0)) = 0 := by
  have h := sym_singular e8CertData (-6) hk8 (fun i => (cz i : ℂ)) ta tb
    (by
      have h := simpleProjection_sv
      rw [sv] at h
      simpa [w2] using h)
    (fun e => by
      have := hw_bracket_shadowZ e
      simp only [structureConstant_eq]
      exact_mod_cast this)
    (by
      have := hw_form_shadowZ
      simp only [formTable_eq]
      exact_mod_cast this)
  have he : quadP 248 (relQ 0) = ∑ i, (cz i : ℂ) • (X (ta i) * X (tb i)) := by
    rw [relQ_zero]
    simp only [quadP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Fin.sum_univ_seven,
      ta, tb, cz, Xn]
    simp [MvPolynomial.smul_eq_C_mul]
    ring_nf
  rw [he]
  exact h

/-- **Every relation of `I₂ⁿˢ = 3875` has vanishing square symbol.** -/
theorem sym_rel_all : ∀ s, s < 3875 → E8C.sym (quadP 248 (relQ s)) = 0 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · exact sym_rel_zero
    · have hok := stepOK_all s hpos hs
      have hlt : (stepOf s).1 < s := by
        simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at hok
        exact hok.1.1.1
      exact sym_of_step s hs hok (ih _ hlt (by omega))

/-! ## The Casimir -/

theorem dualx_eq (a : Fin 248) :
    dualx a = ∑ c, (((Gi2L a).map fun t => if t.1 = c then (1 / 2 : ℂ) * t.2 else 0).sum) • xs c := by
  unfold dualx
  induction Gi2L a with
  | nil => simp
  | cons t l ih =>
      rw [List.map_cons, List.sum_cons, ih]
      simp only [List.map_cons, List.sum_cons, add_smul, Finset.sum_add_distrib, ite_smul,
        zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      congr 1
      rw [div_eq_mul_inv, mul_comm, one_div]

theorem kappaInv8 (a c : Fin 248) :
    e8CertData.kappaInv a c = ((Gi2L a).map fun t => if t.1 = c then (1 / 2 : ℂ) * t.2 else 0).sum := by
  unfold LieData.kappaInv LieData.coordinates LieData.dualGenerator
  rw [e8CertData_dual, e8CertData_basis, dualx_eq, repr_sum]

/-- The Casimir as a sparse quadratic list (twice `casPoly`). -/
def casList : List (ℕ × ℕ × ℤ) :=
  (List.finRange 248).flatMap fun i => (Gi2L i).map fun t => (i.val, t.1.val, t.2)

theorem casCheck : cubicZero (E7Sparse.mulX 1 0 (casList ++ qQ.map fun x => (x.1, x.2.1, -(4 * x.2.2)))) = true := by
  decide +kernel

theorem casPoly_row (i : Fin 248) :
    ∑ j, MvPolynomial.C (e8CertData.kappaInv i j) * (X i * X j)
      = (1 / 2 : ℂ) • quadP 248 ((Gi2L i).map fun t => (i.val, t.1.val, t.2)) := by
  simp only [kappaInv8]
  induction Gi2L i with
  | nil => simp [quadP]
  | cons t l ih =>
      simp only [List.map_cons, List.sum_cons, map_add, add_mul, Finset.sum_add_distrib, ih]
      rw [quadP_cons', smul_add]
      congr 1
      simp only [apply_ite MvPolynomial.C, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      rw [Xn_fin, Xn_fin, MvPolynomial.smul_eq_C_mul, map_mul, map_intCast]
      ring

theorem quadP_flatMap {α : Type*} (l : List α) (g : α → List (ℕ × ℕ × ℤ)) :
    quadP 248 (l.flatMap g) = (l.map fun a => quadP 248 (g a)).sum := by
  induction l with
  | nil => simp [quadP]
  | cons a l ih => rw [List.flatMap_cons, quadP_append', ih, List.map_cons, List.sum_cons]

/-- **`casPoly = 2 · Q`.** -/
theorem casPoly_eq : E8C.casPoly = MvPolynomial.C 2 * E8data.Q := by
  have h0 := quadP_eq_zero_of_check _ casCheck
  rw [quadP_append', quadP_map_scale] at h0
  have h4 : quadP 248 casList = (4 : MvPolynomial (Fin 248) ℂ) * quadP 248 qQ := by
    push_cast at h0
    linear_combination h0
  have hcas : E8C.casPoly = (1 / 2 : ℂ) • quadP 248 casList := by
    show ∑ i, ∑ j, MvPolynomial.C (e8CertData.kappaInv i j) * (X i * X j) = _
    simp only [casPoly_row]
    rw [← Finset.smul_sum, Fin.sum_univ_def, casList, quadP_flatMap]
  have hQ : E8data.Q = quadP 248 qQ := quadraticRelation_cas
  rw [hcas, hQ, h4, MvPolynomial.smul_eq_C_mul, ← mul_assoc,
    ← map_ofNat (MvPolynomial.C (σ := Fin 248) (R := ℂ)) 4, ← map_mul]
  congr 2
  norm_num

/-! ## The theorems -/

theorem W8_centralCharge : W8.centralCharge = -2 * (((30 : ℕ) : ℂ) + 1) := by
  rw [simple_centralCharge', e8CertData_h]
  norm_num

/-- **The `E₈` MLDE target bound** `dim (L_{-6}(𝔢₈))_N ≥ mldeCoeff 30 N`. -/
theorem targetLowerBoundQ8 :
    DeligneCharacter.TargetLowerBoundQ W8 (DeligneCharacter.mldeCoeff 30) :=
  targetLowerBound_of_carrierData E8data e8CertData (-6) hk8 30
    (by
      rw [e8CertData_h, show (E8data.n : ℂ) = 248 from rfl]
      norm_num) 2 casPoly_eq
    (fun r => by
      change E8C.sym (quadraticRelation (rel r)) = 0
      rw [quadraticRelation_rel]
      exact sym_rel_all r.val r.isLt)

/-- **The vacuum quartic relation of `L_{-6}(𝔢₈)`** (`κ = (30+1)(5·30-6) = 4464`). -/
theorem vacuumQuarticRelation8 : VacuumQuarticRelation W8 4464 := by
  have h := vacuumQuarticRelation_of_carrierData E8data e8CertData (-6) hk8 2 casPoly_eq
    (fun r => by
      change E8C.sym (quadraticRelation (rel r)) = 0
      rw [quadraticRelation_rel]
      exact sym_rel_all r.val r.isLt)
  convert h using 1
  rw [simple_centralCharge', e8CertData_h, show (Fintype.card (Fin E8data.n) : ℂ) = 248 from by
    rw [Fintype.card_fin]; rfl]
  norm_num

end

end VOA.DeligneAudit.E8Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.E8Lie.sym_rel_all
#print axioms VOA.DeligneAudit.E8Lie.casPoly_eq
#print axioms VOA.DeligneAudit.E8Lie.vacuumQuarticRelation8
#print axioms VOA.DeligneAudit.E8Lie.targetLowerBoundQ8
end AxiomAudit
