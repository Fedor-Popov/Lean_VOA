/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStableEntries
import VOA.DeligneAudit.E7SectorStab13
import VOA.DeligneAudit.E7SectorStab12
import VOA.DeligneAudit.E7SectorStab11
import VOA.DeligneAudit.E7SectorStab10
import VOA.DeligneAudit.E7SectorStab9
import VOA.DeligneAudit.E7SectorStab8
import VOA.DeligneAudit.E7SectorStab7
import VOA.DeligneAudit.E7SectorStab76
import VOA.DeligneAudit.E7SectorStab75
import VOA.DeligneAudit.E7SectorStab74
import VOA.DeligneAudit.E7SectorStab73
import VOA.DeligneAudit.E7SectorStab72
import VOA.DeligneAudit.E7SectorStab71
import VOA.DeligneAudit.E7SectorStab70
import VOA.DeligneAudit.E7SectorChecksW
import VOA.DeligneAudit.E7SectorChecksB
import VOA.DeligneAudit.E7SectorLinkA
import VOA.DeligneAudit.E7SectorLinkB
import VOA.DeligneAudit.E7SectorLinkC
import VOA.DeligneAudit.E7SectorLinkD
import VOA.DeligneAudit.E7SectorLinkE
import VOA.DeligneAudit.E7SectorLinkF
import VOA.DeligneAudit.E7SectorLinkG
import VOA.DeligneAudit.E7LieData
import VOA.DeligneAudit.E7CarrierData
import VOA.DeligneAudit.E6SectorSparse

/-!
# `E₇` sector data: structure constants, Jacobi, ad-stability of `I₂`

* `fE7 = scF e7T 133` equals the cert structure constants `E7Lie.sZ` (`fE7_eq_sZ`), which are those of the
  Lie algebra `e7Lie` in the basis `xs` (`E7Lie.bracket_xs`); hence **`e7_jacobi`** from the Jacobi identity
  of `e7Lie` (no table check).
* Stability of `I₂ = I₂ⁿˢ ⊕ ℂQ` under the 14 Chevalley generators from the certificates `E7SectorStab*`
  (`stable_gen`), transported to all 133 basis vectors along single-term brackets
  (`stable_of_bracket`); **`e7_stable : RelationsStable fE7 E7data.fullMatrix`**.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E7

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector

noncomputable section

/-- Structure constants of `𝔢₇` in the cert basis. -/
abbrev fE7 : Fin 133 → Fin 133 → Fin 133 → ℂ := scF e7T 133

theorem rowLink_all (a : ℕ) (ha : a < 133) : rowLinkOK a = true := by
  have go : ∀ (lo n : ℕ), (List.range' lo n).all rowLinkOK = true → lo ≤ a → a < lo + n →
      rowLinkOK a = true := fun lo n h h1 h2 =>
    List.all_eq_true.mp h a (List.mem_range'_1.mpr ⟨h1, h2⟩)
  by_cases c0 : a < 19; · exact go 0 19 rowLink0 (by omega) (by omega)
  by_cases c1 : a < 38; · exact go 19 19 rowLink1 (by omega) (by omega)
  by_cases c2 : a < 57; · exact go 38 19 rowLink2 (by omega) (by omega)
  by_cases c3 : a < 76; · exact go 57 19 rowLink3 (by omega) (by omega)
  by_cases c4 : a < 95; · exact go 76 19 rowLink4 (by omega) (by omega)
  by_cases c5 : a < 114; · exact go 95 19 rowLink5 (by omega) (by omega)
  exact go 114 19 rowLink6 (by omega) (by omega)

theorem entry_e7T (a b : Fin 133) : entry e7T a b = (E7Lie.sL a b).map fun t => (t.1.val, t.2) := by
  have h := rowLink_all a.val a.isLt
  unfold rowLinkOK at h
  have hb := List.all_eq_true.mp h b (List.mem_finRange b)
  have hmod : (⟨a.val % 133, Nat.mod_lt _ (by decide)⟩ : Fin 133) = a := Fin.ext (Nat.mod_eq_of_lt a.isLt)
  rw [hmod] at hb
  exact beq_iff_eq.mp hb

theorem coef_map_val (l : List (Fin 133 × ℤ)) (c : Fin 133) :
    coef (l.map fun t => (t.1.val, t.2)) c = (l.map fun t => if t.1 = c then t.2 else 0).sum := by
  induction l with
  | nil => rfl
  | cons t l ih =>
      simp only [List.map_cons, coef_cons, List.sum_cons, ih]
      congr 1
      by_cases h : t.1 = c
      · simp [h]
      · have : t.1.val ≠ c.val := fun e => h (Fin.ext e)
        simp [h, this]

theorem fE7_eq_sZ (a b c : Fin 133) : fE7 a b c = (E7Lie.sZ a b c : ℂ) := by
  simp only [fE7, scF, sc, entry_e7T, coef_map_val, E7Lie.sZ]

theorem fE7_eq_sc (a b c : Fin 133) : fE7 a b c = E7Lie.e7CertData.structureConstant a b c := by
  rw [fE7_eq_sZ, E7Lie.structureConstant_eq]

/-- Coordinates of a bracket of basis vectors. -/
theorem repr_bracket_sum (a : Fin 133) (v : Fin 133 → ℂ) (c : Fin 133) :
    E7Lie.bB.repr ⁅E7Lie.xs a, ∑ d, v d • E7Lie.xs d⁆ c = ∑ d, v d * fE7 a d c := by
  simp only [lie_sum, lie_smul, E7Lie.bracket_xs, Finset.smul_sum, smul_smul, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, E7Lie.repr_xs, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, fE7_eq_sZ]

theorem bracket_sum (a b : Fin 133) : ⁅E7Lie.xs a, E7Lie.xs b⁆ = ∑ d, fE7 a b d • E7Lie.xs d := by
  rw [E7Lie.bracket_xs]
  simp only [fE7_eq_sZ]

/-- **Jacobi**, from the Lie algebra `e7Lie`. -/
theorem e7_jacobi : JacobiCoord fE7 := by
  intro a b x c
  have h := leibniz_lie (E7Lie.xs b) (E7Lie.xs a) (E7Lie.xs x)
  have h' : ⁅E7Lie.xs b, ⁅E7Lie.xs a, E7Lie.xs x⁆⁆ - ⁅E7Lie.xs a, ⁅E7Lie.xs b, E7Lie.xs x⁆⁆ =
      ⁅⁅E7Lie.xs b, E7Lie.xs a⁆, E7Lie.xs x⁆ := by rw [h]; abel
  have hc := congrArg (fun y => E7Lie.bB.repr y c) h'
  simp only [map_sub, Finsupp.coe_sub, Pi.sub_apply] at hc
  rw [bracket_sum a x, bracket_sum b x, repr_bracket_sum, repr_bracket_sum, bracket_sum b a,
    sum_lie] at hc
  simp only [smul_lie] at hc
  have hr : E7Lie.bB.repr (∑ e, fE7 b a e • ⁅E7Lie.xs e, E7Lie.xs x⁆) c = ∑ e, fE7 b a e * fE7 e x c := by
    simp only [bracket_sum, Finset.smul_sum, smul_smul, map_sum, map_smul, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, E7Lie.repr_xs, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hr] at hc
  have hanti : ∀ e, fE7 b a e = -fE7 a b e := by
    intro e
    rw [fE7_eq_sc, fE7_eq_sc, VOA.AffineGeneral.LieData.structureConstant_antisymm]
  simp only [hanti, neg_mul, Finset.sum_neg_distrib] at hc
  linear_combination hc

theorem e7_bound : boundOK e7T 133 = true :=
  boundOK_of_chunks _ _ fun i hi => by
    rcases (show (0 ≤ i ∧ i < 19) ∨ (19 ≤ i ∧ i < 38) ∨ (38 ≤ i ∧ i < 57) ∨ (57 ≤ i ∧ i < 76) ∨
        (76 ≤ i ∧ i < 95) ∨ (95 ≤ i ∧ i < 114) ∨ (114 ≤ i ∧ i < 133) by omega) with h | h | h | h | h | h | h
    · exact ⟨0, 19, h.1, h.2, e7_bound0⟩
    · exact ⟨19, 38, h.1, h.2, e7_bound1⟩
    · exact ⟨38, 57, h.1, h.2, e7_bound2⟩
    · exact ⟨57, 76, h.1, h.2, e7_bound3⟩
    · exact ⟨76, 95, h.1, h.2, e7_bound4⟩
    · exact ⟨95, 114, h.1, h.2, e7_bound5⟩
    · exact ⟨114, 133, h.1, h.2, e7_bound6⟩

/-! ## Stability of `I₂` -/

theorem quadP_bridge (l : List (ℕ × ℕ × ℤ)) : E6Sparse.quadP 133 l = E7Sparse.quadP 133 l := rfl

/-- Index of a quadratic of `I₂`. -/
def qIdx : Option E7data.ρ → ℕ
  | none => 1539
  | some r => (show Fin 1539 from r).val

theorem qIdx_lt (s : Option E7data.ρ) : qIdx s < 1540 := by
  cases s with
  | none => simp [qIdx]
  | some r => have := (show Fin 1539 from r).2; simp only [qIdx]; omega

theorem quadraticRelation_fullMatrix (s : Option E7data.ρ) :
    quadraticRelation (E7data.fullMatrix s) = E7Sparse.quadP 133 (Pq (qIdx s)) := by
  cases s with
  | none =>
    show quadraticRelation cas = _
    rw [quadraticRelation_cas]; simp [qIdx, Pq]
  | some r =>
    show quadraticRelation (rel (show Fin 1539 from r)) = _
    rw [quadraticRelation_rel]; simp [qIdx, Pq, (show Fin 1539 from r).2]

/-- The span of `I₂`. -/
def S2 : Submodule ℂ (MvPolynomial (Fin 133) ℂ) :=
  Submodule.span ℂ (Set.range fun s => quadraticRelation (E7data.fullMatrix s))

theorem Pq_mem (t : ℕ) (ht : t ≤ 1539) : E7Sparse.quadP 133 (Pq t) ∈ S2 := by
  by_cases h : t < 1539
  · have := quadraticRelation_fullMatrix (some (show E7data.ρ from (⟨t, h⟩ : Fin 1539)))
    simp only [qIdx] at this
    rw [← this]
    exact Submodule.subset_span ⟨_, rfl⟩
  · have ht' : t = 1539 := by omega
    subst ht'
    have := quadraticRelation_fullMatrix none
    simp only [qIdx] at this
    rw [← this]
    exact Submodule.subset_span ⟨_, rfl⟩

theorem intCast_mul_mem (z : ℤ) {q : MvPolynomial (Fin 133) ℂ} (hq : q ∈ S2) :
    (z : MvPolynomial (Fin 133) ℂ) * q ∈ S2 := by
  have : (z : MvPolynomial (Fin 133) ℂ) * q = (z : ℂ) • q := by
    rw [Algebra.smul_def]; simp
  rw [this]; exact S2.smul_mem _ hq

theorem quadP_flatMap7 {α : Type*} (l : List α) (g : α → List (ℕ × ℕ × ℤ)) :
    E7Sparse.quadP 133 (l.flatMap g) = (l.map fun a => E7Sparse.quadP 133 (g a)).sum := by
  induction l with
  | nil => simp [E7Sparse.quadP]
  | cons a l ih => rw [List.flatMap_cons, E7Sparse.quadP_append, ih, List.map_cons, List.sum_cons]

theorem stabRow_sound (g r : ℕ) (c : List ℕ) (h : stabRowOK g r c = true) :
    E7Sparse.quadP 133 (adS e7T g (Pq r)) ∈ S2 := by
  simp only [stabRowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hL, hs⟩, hz⟩ := h
  have h0 := E7Sparse.quadP_eq_zero_of_quadZero (n := 133) _ hz
  rw [E7Sparse.quadP_append, E7Sparse.quadP_scaleQ, E7Sparse.quadP_scaleQ, quadP_flatMap7] at h0
  have hmem : (certL c : MvPolynomial (Fin 133) ℂ) * E7Sparse.quadP 133 (adS e7T g (Pq r)) ∈ S2 := by
    have e : (certL c : MvPolynomial (Fin 133) ℂ) * E7Sparse.quadP 133 (adS e7T g (Pq r)) =
        ((pairsOf c.tail).map fun p => E7Sparse.quadP 133 (E7Sparse.scaleQ p.1 (Pq p.2))).sum := by
      push_cast at h0 ⊢
      linear_combination h0
    rw [e]
    refine list_sum_mem fun y hy => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    rw [E7Sparse.quadP_scaleQ]
    exact intCast_mul_mem _ (Pq_mem _ (by simpa using List.all_eq_true.mp hs p hp))
  have hC : ((certL c : ℂ))⁻¹ • ((certL c : MvPolynomial (Fin 133) ℂ) *
      E7Sparse.quadP 133 (adS e7T g (Pq r))) = E7Sparse.quadP 133 (adS e7T g (Pq r)) := by
    rw [smul_eq_C_mul, ← mul_assoc,
      show (certL c : MvPolynomial (Fin 133) ℂ) = MvPolynomial.C (certL c : ℂ) by simp,
      ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hL), map_one, one_mul]
  rw [← hC]
  exact S2.smul_mem _ hmem

theorem stable_gen (g : ℕ) (hg : g < 133) (rows : List (List ℕ))
    (h : ∀ r, r < 1540 → stabRowOK g r (rows.getD r []) = true) :
    ∀ q ∈ S2, adDer fE7 ⟨g, hg⟩ q ∈ S2 := by
  intro q hq
  induction hq using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    beta_reduce
    have hs : qIdx s < 1540 := qIdx_lt s
    erw [quadraticRelation_fullMatrix]
    rw [← quadP_bridge,
      adDer_quadP e7_bound ⟨g, hg⟩ _ (List.all_eq_true.mp Pq_inRange _ (List.mem_range.mpr hs)),
      quadP_bridge]
    exact stabRow_sound g _ _ (h _ hs)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact S2.add_mem hx hy
  | smul a x _ hx => rw [Derivation.map_smul]; exact S2.smul_mem a hx

theorem rows_of_parts (g : ℕ) (rows : List (List ℕ)) (h1 : stabPart g rows 0 385 = true)
    (h2 : stabPart g rows 385 770 = true) (h3 : stabPart g rows 770 1155 = true)
    (h4 : stabPart g rows 1155 1540 = true) :
    ∀ r, r < 1540 → stabRowOK g r (rows.getD r []) = true := by
  intro r hr
  rcases (show r < 385 ∨ (385 ≤ r ∧ r < 770) ∨ (770 ≤ r ∧ r < 1155) ∨ (1155 ≤ r ∧ r < 1540) by omega)
    with h | h | h | h
  · exact List.all_eq_true.mp h1 r (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact List.all_eq_true.mp h2 r (List.mem_range'_1.mpr ⟨h.1, by omega⟩)
  · exact List.all_eq_true.mp h3 r (List.mem_range'_1.mpr ⟨h.1, by omega⟩)
  · exact List.all_eq_true.mp h4 r (List.mem_range'_1.mpr ⟨h.1, by omega⟩)

theorem hab_of_entry {a b c : Fin 133} {κ : ℤ} (h : entry e7T a b = [((c : ℕ), κ)]) :
    ∀ e, fE7 a b e = if e = c then ((κ : ℤ) : ℂ) else 0 := by
  intro e
  simp only [fE7, scF, sc, h, coef_cons, coef_nil, add_zero]
  by_cases he : e = c
  · subst he; simp
  · have : (c : ℕ) ≠ e := fun h' => he (Fin.ext h'.symm)
    simp [he, this]

theorem st13 : ∀ q ∈ S2, adDer fE7 (13 : Fin 133) q ∈ S2 :=
  stable_gen 13 (by norm_num) stab13 (rows_of_parts 13 stab13 stab13_p0 stab13_p1 stab13_p2 stab13_p3)

theorem st12 : ∀ q ∈ S2, adDer fE7 (12 : Fin 133) q ∈ S2 :=
  stable_gen 12 (by norm_num) stab12 (rows_of_parts 12 stab12 stab12_p0 stab12_p1 stab12_p2 stab12_p3)

theorem st11 : ∀ q ∈ S2, adDer fE7 (11 : Fin 133) q ∈ S2 :=
  stable_gen 11 (by norm_num) stab11 (rows_of_parts 11 stab11 stab11_p0 stab11_p1 stab11_p2 stab11_p3)

theorem st10 : ∀ q ∈ S2, adDer fE7 (10 : Fin 133) q ∈ S2 :=
  stable_gen 10 (by norm_num) stab10 (rows_of_parts 10 stab10 stab10_p0 stab10_p1 stab10_p2 stab10_p3)

theorem st9 : ∀ q ∈ S2, adDer fE7 (9 : Fin 133) q ∈ S2 :=
  stable_gen 9 (by norm_num) stab9 (rows_of_parts 9 stab9 stab9_p0 stab9_p1 stab9_p2 stab9_p3)

theorem st8 : ∀ q ∈ S2, adDer fE7 (8 : Fin 133) q ∈ S2 :=
  stable_gen 8 (by norm_num) stab8 (rows_of_parts 8 stab8 stab8_p0 stab8_p1 stab8_p2 stab8_p3)

theorem st7 : ∀ q ∈ S2, adDer fE7 (7 : Fin 133) q ∈ S2 :=
  stable_gen 7 (by norm_num) stab7 (rows_of_parts 7 stab7 stab7_p0 stab7_p1 stab7_p2 stab7_p3)

theorem st76 : ∀ q ∈ S2, adDer fE7 (76 : Fin 133) q ∈ S2 :=
  stable_gen 76 (by norm_num) stab76 (rows_of_parts 76 stab76 stab76_p0 stab76_p1 stab76_p2 stab76_p3)

theorem st75 : ∀ q ∈ S2, adDer fE7 (75 : Fin 133) q ∈ S2 :=
  stable_gen 75 (by norm_num) stab75 (rows_of_parts 75 stab75 stab75_p0 stab75_p1 stab75_p2 stab75_p3)

theorem st74 : ∀ q ∈ S2, adDer fE7 (74 : Fin 133) q ∈ S2 :=
  stable_gen 74 (by norm_num) stab74 (rows_of_parts 74 stab74 stab74_p0 stab74_p1 stab74_p2 stab74_p3)

theorem st73 : ∀ q ∈ S2, adDer fE7 (73 : Fin 133) q ∈ S2 :=
  stable_gen 73 (by norm_num) stab73 (rows_of_parts 73 stab73 stab73_p0 stab73_p1 stab73_p2 stab73_p3)

theorem st72 : ∀ q ∈ S2, adDer fE7 (72 : Fin 133) q ∈ S2 :=
  stable_gen 72 (by norm_num) stab72 (rows_of_parts 72 stab72 stab72_p0 stab72_p1 stab72_p2 stab72_p3)

theorem st71 : ∀ q ∈ S2, adDer fE7 (71 : Fin 133) q ∈ S2 :=
  stable_gen 71 (by norm_num) stab71 (rows_of_parts 71 stab71 stab71_p0 stab71_p1 stab71_p2 stab71_p3)

theorem st70 : ∀ q ∈ S2, adDer fE7 (70 : Fin 133) q ∈ S2 :=
  stable_gen 70 (by norm_num) stab70 (rows_of_parts 70 stab70 stab70_p0 stab70_p1 stab70_p2 stab70_p3)

theorem st0 : ∀ q ∈ S2, adDer fE7 (0 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 13 76 0 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry0) st13 st76

theorem st1 : ∀ q ∈ S2, adDer fE7 (1 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 12 75 1 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry1) st12 st75

theorem st2 : ∀ q ∈ S2, adDer fE7 (2 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 11 74 2 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry2) st11 st74

theorem st3 : ∀ q ∈ S2, adDer fE7 (3 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 10 73 3 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry3) st10 st73

theorem st4 : ∀ q ∈ S2, adDer fE7 (4 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 9 72 4 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry4) st9 st72

theorem st5 : ∀ q ∈ S2, adDer fE7 (5 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 71 5 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry5) st8 st71

theorem st6 : ∀ q ∈ S2, adDer fE7 (6 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 70 6 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry6) st7 st70

theorem st14 : ∀ q ∈ S2, adDer fE7 (14 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 8 14 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry14) st7 st8

theorem st15 : ∀ q ∈ S2, adDer fE7 (15 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 9 15 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry15) st8 st9

theorem st16 : ∀ q ∈ S2, adDer fE7 (16 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 9 10 16 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry16) st9 st10

theorem st17 : ∀ q ∈ S2, adDer fE7 (17 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 10 11 17 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry17) st10 st11

theorem st18 : ∀ q ∈ S2, adDer fE7 (18 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 10 12 18 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry18) st10 st12

theorem st19 : ∀ q ∈ S2, adDer fE7 (19 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 11 13 19 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry19) st11 st13

theorem st20 : ∀ q ∈ S2, adDer fE7 (20 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 15 20 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry20) st7 st15

theorem st21 : ∀ q ∈ S2, adDer fE7 (21 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 16 21 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry21) st8 st16

theorem st22 : ∀ q ∈ S2, adDer fE7 (22 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 9 17 22 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry22) st9 st17

theorem st23 : ∀ q ∈ S2, adDer fE7 (23 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 9 18 23 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry23) st9 st18

theorem st24 : ∀ q ∈ S2, adDer fE7 (24 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 11 18 24 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry24) st11 st18

theorem st25 : ∀ q ∈ S2, adDer fE7 (25 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 10 19 25 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry25) st10 st19

theorem st26 : ∀ q ∈ S2, adDer fE7 (26 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 21 26 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry26) st7 st21

theorem st27 : ∀ q ∈ S2, adDer fE7 (27 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 22 27 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry27) st8 st22

theorem st28 : ∀ q ∈ S2, adDer fE7 (28 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 23 28 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry28) st8 st23

theorem st29 : ∀ q ∈ S2, adDer fE7 (29 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 9 24 29 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry29) st9 st24

theorem st30 : ∀ q ∈ S2, adDer fE7 (30 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 9 25 30 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry30) st9 st25

theorem st31 : ∀ q ∈ S2, adDer fE7 (31 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 12 25 31 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry31) st12 st25

theorem st32 : ∀ q ∈ S2, adDer fE7 (32 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 27 32 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry32) st7 st27

theorem st33 : ∀ q ∈ S2, adDer fE7 (33 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 28 33 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry33) st7 st28

theorem st34 : ∀ q ∈ S2, adDer fE7 (34 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 29 34 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry34) st8 st29

theorem st35 : ∀ q ∈ S2, adDer fE7 (35 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 10 29 35 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry35) st10 st29

theorem st36 : ∀ q ∈ S2, adDer fE7 (36 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 30 36 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry36) st8 st30

theorem st37 : ∀ q ∈ S2, adDer fE7 (37 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 9 31 37 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry37) st9 st31

theorem st38 : ∀ q ∈ S2, adDer fE7 (38 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 34 38 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry38) st7 st34

theorem st39 : ∀ q ∈ S2, adDer fE7 (39 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 35 39 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry39) st8 st35

theorem st40 : ∀ q ∈ S2, adDer fE7 (40 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 36 40 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry40) st7 st36

theorem st41 : ∀ q ∈ S2, adDer fE7 (41 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 37 41 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry41) st8 st37

theorem st42 : ∀ q ∈ S2, adDer fE7 (42 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 10 37 42 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry42) st10 st37

theorem st43 : ∀ q ∈ S2, adDer fE7 (43 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 39 43 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry43) st7 st39

theorem st44 : ∀ q ∈ S2, adDer fE7 (44 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 9 39 44 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry44) st9 st39

theorem st45 : ∀ q ∈ S2, adDer fE7 (45 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 41 45 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry45) st7 st41

theorem st46 : ∀ q ∈ S2, adDer fE7 (46 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 42 46 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry46) st8 st42

theorem st47 : ∀ q ∈ S2, adDer fE7 (47 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 11 42 47 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry47) st11 st42

theorem st48 : ∀ q ∈ S2, adDer fE7 (48 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 44 48 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry48) st7 st44

theorem st49 : ∀ q ∈ S2, adDer fE7 (49 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 46 49 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry49) st7 st46

theorem st50 : ∀ q ∈ S2, adDer fE7 (50 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 9 46 50 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry50) st9 st46

theorem st51 : ∀ q ∈ S2, adDer fE7 (51 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 47 51 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry51) st8 st47

theorem st52 : ∀ q ∈ S2, adDer fE7 (52 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 48 52 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry52) st8 st48

theorem st53 : ∀ q ∈ S2, adDer fE7 (53 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 50 53 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry53) st7 st50

theorem st54 : ∀ q ∈ S2, adDer fE7 (54 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 51 54 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry54) st7 st51

theorem st55 : ∀ q ∈ S2, adDer fE7 (55 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 9 51 55 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry55) st9 st51

theorem st56 : ∀ q ∈ S2, adDer fE7 (56 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 53 56 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry56) st8 st53

theorem st57 : ∀ q ∈ S2, adDer fE7 (57 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 55 57 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry57) st7 st55

theorem st58 : ∀ q ∈ S2, adDer fE7 (58 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 10 55 58 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry58) st10 st55

theorem st59 : ∀ q ∈ S2, adDer fE7 (59 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 57 59 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry59) st8 st57

theorem st60 : ∀ q ∈ S2, adDer fE7 (60 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 58 60 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry60) st7 st58

theorem st61 : ∀ q ∈ S2, adDer fE7 (61 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 12 58 61 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry61) st12 st58

theorem st62 : ∀ q ∈ S2, adDer fE7 (62 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 60 62 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry62) st8 st60

theorem st63 : ∀ q ∈ S2, adDer fE7 (63 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 7 61 63 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry63) st7 st61

theorem st64 : ∀ q ∈ S2, adDer fE7 (64 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 9 62 64 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry64) st9 st62

theorem st65 : ∀ q ∈ S2, adDer fE7 (65 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 8 63 65 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry65) st8 st63

theorem st66 : ∀ q ∈ S2, adDer fE7 (66 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 9 65 66 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry66) st9 st65

theorem st67 : ∀ q ∈ S2, adDer fE7 (67 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 10 66 67 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry67) st10 st66

theorem st68 : ∀ q ∈ S2, adDer fE7 (68 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 11 67 68 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry68) st11 st67

theorem st69 : ∀ q ∈ S2, adDer fE7 (69 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 13 68 69 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry69) st13 st68

theorem st77 : ∀ q ∈ S2, adDer fE7 (77 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 71 77 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry77) st70 st71

theorem st78 : ∀ q ∈ S2, adDer fE7 (78 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 71 72 78 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry78) st71 st72

theorem st79 : ∀ q ∈ S2, adDer fE7 (79 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 72 73 79 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry79) st72 st73

theorem st80 : ∀ q ∈ S2, adDer fE7 (80 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 73 74 80 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry80) st73 st74

theorem st81 : ∀ q ∈ S2, adDer fE7 (81 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 73 75 81 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry81) st73 st75

theorem st82 : ∀ q ∈ S2, adDer fE7 (82 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 74 76 82 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry82) st74 st76

theorem st83 : ∀ q ∈ S2, adDer fE7 (83 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 78 83 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry83) st70 st78

theorem st84 : ∀ q ∈ S2, adDer fE7 (84 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 71 79 84 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry84) st71 st79

theorem st85 : ∀ q ∈ S2, adDer fE7 (85 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 72 80 85 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry85) st72 st80

theorem st86 : ∀ q ∈ S2, adDer fE7 (86 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 72 81 86 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry86) st72 st81

theorem st87 : ∀ q ∈ S2, adDer fE7 (87 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 74 81 87 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry87) st74 st81

theorem st88 : ∀ q ∈ S2, adDer fE7 (88 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 73 82 88 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry88) st73 st82

theorem st89 : ∀ q ∈ S2, adDer fE7 (89 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 84 89 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry89) st70 st84

theorem st90 : ∀ q ∈ S2, adDer fE7 (90 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 71 85 90 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry90) st71 st85

theorem st91 : ∀ q ∈ S2, adDer fE7 (91 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 71 86 91 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry91) st71 st86

theorem st92 : ∀ q ∈ S2, adDer fE7 (92 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 72 87 92 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry92) st72 st87

theorem st93 : ∀ q ∈ S2, adDer fE7 (93 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 72 88 93 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry93) st72 st88

theorem st94 : ∀ q ∈ S2, adDer fE7 (94 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 75 88 94 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry94) st75 st88

theorem st95 : ∀ q ∈ S2, adDer fE7 (95 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 90 95 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry95) st70 st90

theorem st96 : ∀ q ∈ S2, adDer fE7 (96 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 91 96 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry96) st70 st91

theorem st97 : ∀ q ∈ S2, adDer fE7 (97 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 71 92 97 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry97) st71 st92

theorem st98 : ∀ q ∈ S2, adDer fE7 (98 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 73 92 98 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry98) st73 st92

theorem st99 : ∀ q ∈ S2, adDer fE7 (99 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 71 93 99 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry99) st71 st93

theorem st100 : ∀ q ∈ S2, adDer fE7 (100 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 72 94 100 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry100) st72 st94

theorem st101 : ∀ q ∈ S2, adDer fE7 (101 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 97 101 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry101) st70 st97

theorem st102 : ∀ q ∈ S2, adDer fE7 (102 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 71 98 102 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry102) st71 st98

theorem st103 : ∀ q ∈ S2, adDer fE7 (103 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 99 103 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry103) st70 st99

theorem st104 : ∀ q ∈ S2, adDer fE7 (104 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 71 100 104 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry104) st71 st100

theorem st105 : ∀ q ∈ S2, adDer fE7 (105 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 73 100 105 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry105) st73 st100

theorem st106 : ∀ q ∈ S2, adDer fE7 (106 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 102 106 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry106) st70 st102

theorem st107 : ∀ q ∈ S2, adDer fE7 (107 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 72 102 107 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry107) st72 st102

theorem st108 : ∀ q ∈ S2, adDer fE7 (108 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 104 108 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry108) st70 st104

theorem st109 : ∀ q ∈ S2, adDer fE7 (109 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 71 105 109 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry109) st71 st105

theorem st110 : ∀ q ∈ S2, adDer fE7 (110 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 74 105 110 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry110) st74 st105

theorem st111 : ∀ q ∈ S2, adDer fE7 (111 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 107 111 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry111) st70 st107

theorem st112 : ∀ q ∈ S2, adDer fE7 (112 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 109 112 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry112) st70 st109

theorem st113 : ∀ q ∈ S2, adDer fE7 (113 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 72 109 113 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry113) st72 st109

theorem st114 : ∀ q ∈ S2, adDer fE7 (114 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 71 110 114 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry114) st71 st110

theorem st115 : ∀ q ∈ S2, adDer fE7 (115 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 71 111 115 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry115) st71 st111

theorem st116 : ∀ q ∈ S2, adDer fE7 (116 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 113 116 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry116) st70 st113

theorem st117 : ∀ q ∈ S2, adDer fE7 (117 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 114 117 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry117) st70 st114

theorem st118 : ∀ q ∈ S2, adDer fE7 (118 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 72 114 118 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry118) st72 st114

theorem st119 : ∀ q ∈ S2, adDer fE7 (119 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 71 116 119 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry119) st71 st116

theorem st120 : ∀ q ∈ S2, adDer fE7 (120 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 118 120 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry120) st70 st118

theorem st121 : ∀ q ∈ S2, adDer fE7 (121 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 73 118 121 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry121) st73 st118

theorem st122 : ∀ q ∈ S2, adDer fE7 (122 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 71 120 122 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry122) st71 st120

theorem st123 : ∀ q ∈ S2, adDer fE7 (123 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 121 123 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry123) st70 st121

theorem st124 : ∀ q ∈ S2, adDer fE7 (124 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 75 121 124 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry124) st75 st121

theorem st125 : ∀ q ∈ S2, adDer fE7 (125 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 71 123 125 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry125) st71 st123

theorem st126 : ∀ q ∈ S2, adDer fE7 (126 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 70 124 126 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry126) st70 st124

theorem st127 : ∀ q ∈ S2, adDer fE7 (127 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 72 125 127 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry127) st72 st125

theorem st128 : ∀ q ∈ S2, adDer fE7 (128 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 71 126 128 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry128) st71 st126

theorem st129 : ∀ q ∈ S2, adDer fE7 (129 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 72 128 129 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry129) st72 st128

theorem st130 : ∀ q ∈ S2, adDer fE7 (130 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 73 129 130 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry130) st73 st129

theorem st131 : ∀ q ∈ S2, adDer fE7 (131 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 74 130 131 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry131) st74 st130

theorem st132 : ∀ q ∈ S2, adDer fE7 (132 : Fin 133) q ∈ S2 :=
  stable_of_bracket e7_jacobi S2 76 131 132 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry stable_entry132) st76 st131

theorem e7_stable : RelationsStable fE7 E7data.fullMatrix := by
  intro x r
  rw [quadraticRelation_adMatrix]
  fin_cases x
  · exact st0 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st1 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st2 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st3 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st4 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st5 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st6 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st7 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st8 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st9 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st10 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st11 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st12 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st13 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st14 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st15 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st16 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st17 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st18 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st19 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st20 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st21 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st22 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st23 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st24 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st25 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st26 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st27 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st28 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st29 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st30 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st31 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st32 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st33 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st34 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st35 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st36 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st37 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st38 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st39 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st40 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st41 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st42 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st43 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st44 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st45 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st46 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st47 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st48 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st49 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st50 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st51 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st52 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st53 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st54 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st55 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st56 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st57 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st58 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st59 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st60 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st61 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st62 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st63 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st64 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st65 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st66 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st67 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st68 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st69 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st70 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st71 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st72 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st73 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st74 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st75 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st76 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st77 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st78 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st79 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st80 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st81 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st82 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st83 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st84 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st85 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st86 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st87 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st88 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st89 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st90 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st91 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st92 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st93 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st94 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st95 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st96 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st97 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st98 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st99 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st100 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st101 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st102 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st103 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st104 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st105 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st106 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st107 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st108 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st109 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st110 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st111 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st112 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st113 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st114 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st115 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st116 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st117 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st118 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st119 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st120 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st121 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st122 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st123 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st124 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st125 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st126 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st127 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st128 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st129 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st130 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st131 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st132 _ (Submodule.subset_span ⟨r, rfl⟩)

end

end VOA.DeligneAudit.DeligneCarrier.E7

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.e7_jacobi
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.e7_stable
end AxiomAudit
