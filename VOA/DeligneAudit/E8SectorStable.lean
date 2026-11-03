/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorStab15
import VOA.DeligneAudit.E8SectorStab14
import VOA.DeligneAudit.E8SectorStab13
import VOA.DeligneAudit.E8SectorStab12
import VOA.DeligneAudit.E8SectorStab11
import VOA.DeligneAudit.E8SectorStab10
import VOA.DeligneAudit.E8SectorStab9
import VOA.DeligneAudit.E8SectorStab8
import VOA.DeligneAudit.E8SectorStab135
import VOA.DeligneAudit.E8SectorStab134
import VOA.DeligneAudit.E8SectorStab133
import VOA.DeligneAudit.E8SectorStab132
import VOA.DeligneAudit.E8SectorStab131
import VOA.DeligneAudit.E8SectorStab130
import VOA.DeligneAudit.E8SectorStab129
import VOA.DeligneAudit.E8SectorStab128
import VOA.DeligneAudit.E8SectorChecksWA
import VOA.DeligneAudit.E8SectorChecksWB
import VOA.DeligneAudit.E8SectorBoundA
import VOA.DeligneAudit.E8SectorBoundB
import VOA.DeligneAudit.E8SectorChecksB
import VOA.DeligneAudit.E8SectorLinkA
import VOA.DeligneAudit.E8SectorLinkB
import VOA.DeligneAudit.E8SectorLinkC
import VOA.DeligneAudit.E8SectorLinkD
import VOA.DeligneAudit.E8LieData
import VOA.DeligneAudit.E8CarrierData
import VOA.DeligneAudit.E6SectorSparse

/-!
# `E₈` sector data: structure constants, Jacobi, ad-stability of `I₂`

* `fE8 = scF e8T 248` equals the cert structure constants `E8Lie.sZ` (`fE8_eq_sZ`), which are those of the
  Lie algebra `e8Lie` in the basis `xs` (`E8Lie.bracket_xs`); hence **`e8_jacobi`** from the Jacobi identity
  of `e8Lie` (no table check).
* Stability of `I₂ = I₂ⁿˢ ⊕ ℂQ` under the 16 Chevalley generators from the certificates `E8SectorStab*`
  (`stable_gen`), transported to all 248 basis vectors along single-term brackets
  (`stable_of_bracket`); **`e8_stable : RelationsStable fE8 E8data.fullMatrix`**.

Port of the `E7SectorStable`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E8

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector

noncomputable section

/-- Structure constants of `𝔢₈` in the cert basis. -/
abbrev fE8 : Fin 248 → Fin 248 → Fin 248 → ℂ := scF e8T 248

theorem rowLink_all (a : ℕ) (ha : a < 248) : rowLinkOK a = true := by
  have go : ∀ (lo n : ℕ), (List.range' lo n).all rowLinkOK = true → lo ≤ a → a < lo + n →
      rowLinkOK a = true := fun lo n h h1 h2 =>
    List.all_eq_true.mp h a (List.mem_range'_1.mpr ⟨h1, h2⟩)
  by_cases c0 : a < 4; · exact go 0 4 rowLink0 (by omega) (by omega)
  by_cases c1 : a < 8; · exact go 4 4 rowLink1 (by omega) (by omega)
  by_cases c2 : a < 12; · exact go 8 4 rowLink2 (by omega) (by omega)
  by_cases c3 : a < 16; · exact go 12 4 rowLink3 (by omega) (by omega)
  by_cases c4 : a < 20; · exact go 16 4 rowLink4 (by omega) (by omega)
  by_cases c5 : a < 24; · exact go 20 4 rowLink5 (by omega) (by omega)
  by_cases c6 : a < 28; · exact go 24 4 rowLink6 (by omega) (by omega)
  by_cases c7 : a < 32; · exact go 28 4 rowLink7 (by omega) (by omega)
  by_cases c8 : a < 36; · exact go 32 4 rowLink8 (by omega) (by omega)
  by_cases c9 : a < 40; · exact go 36 4 rowLink9 (by omega) (by omega)
  by_cases c10 : a < 44; · exact go 40 4 rowLink10 (by omega) (by omega)
  by_cases c11 : a < 48; · exact go 44 4 rowLink11 (by omega) (by omega)
  by_cases c12 : a < 52; · exact go 48 4 rowLink12 (by omega) (by omega)
  by_cases c13 : a < 56; · exact go 52 4 rowLink13 (by omega) (by omega)
  by_cases c14 : a < 60; · exact go 56 4 rowLink14 (by omega) (by omega)
  by_cases c15 : a < 64; · exact go 60 4 rowLink15 (by omega) (by omega)
  by_cases c16 : a < 68; · exact go 64 4 rowLink16 (by omega) (by omega)
  by_cases c17 : a < 72; · exact go 68 4 rowLink17 (by omega) (by omega)
  by_cases c18 : a < 76; · exact go 72 4 rowLink18 (by omega) (by omega)
  by_cases c19 : a < 80; · exact go 76 4 rowLink19 (by omega) (by omega)
  by_cases c20 : a < 84; · exact go 80 4 rowLink20 (by omega) (by omega)
  by_cases c21 : a < 88; · exact go 84 4 rowLink21 (by omega) (by omega)
  by_cases c22 : a < 92; · exact go 88 4 rowLink22 (by omega) (by omega)
  by_cases c23 : a < 96; · exact go 92 4 rowLink23 (by omega) (by omega)
  by_cases c24 : a < 100; · exact go 96 4 rowLink24 (by omega) (by omega)
  by_cases c25 : a < 104; · exact go 100 4 rowLink25 (by omega) (by omega)
  by_cases c26 : a < 108; · exact go 104 4 rowLink26 (by omega) (by omega)
  by_cases c27 : a < 112; · exact go 108 4 rowLink27 (by omega) (by omega)
  by_cases c28 : a < 116; · exact go 112 4 rowLink28 (by omega) (by omega)
  by_cases c29 : a < 120; · exact go 116 4 rowLink29 (by omega) (by omega)
  by_cases c30 : a < 124; · exact go 120 4 rowLink30 (by omega) (by omega)
  by_cases c31 : a < 128; · exact go 124 4 rowLink31 (by omega) (by omega)
  by_cases c32 : a < 132; · exact go 128 4 rowLink32 (by omega) (by omega)
  by_cases c33 : a < 136; · exact go 132 4 rowLink33 (by omega) (by omega)
  by_cases c34 : a < 140; · exact go 136 4 rowLink34 (by omega) (by omega)
  by_cases c35 : a < 144; · exact go 140 4 rowLink35 (by omega) (by omega)
  by_cases c36 : a < 148; · exact go 144 4 rowLink36 (by omega) (by omega)
  by_cases c37 : a < 152; · exact go 148 4 rowLink37 (by omega) (by omega)
  by_cases c38 : a < 156; · exact go 152 4 rowLink38 (by omega) (by omega)
  by_cases c39 : a < 160; · exact go 156 4 rowLink39 (by omega) (by omega)
  by_cases c40 : a < 164; · exact go 160 4 rowLink40 (by omega) (by omega)
  by_cases c41 : a < 168; · exact go 164 4 rowLink41 (by omega) (by omega)
  by_cases c42 : a < 172; · exact go 168 4 rowLink42 (by omega) (by omega)
  by_cases c43 : a < 176; · exact go 172 4 rowLink43 (by omega) (by omega)
  by_cases c44 : a < 180; · exact go 176 4 rowLink44 (by omega) (by omega)
  by_cases c45 : a < 184; · exact go 180 4 rowLink45 (by omega) (by omega)
  by_cases c46 : a < 188; · exact go 184 4 rowLink46 (by omega) (by omega)
  by_cases c47 : a < 192; · exact go 188 4 rowLink47 (by omega) (by omega)
  by_cases c48 : a < 196; · exact go 192 4 rowLink48 (by omega) (by omega)
  by_cases c49 : a < 200; · exact go 196 4 rowLink49 (by omega) (by omega)
  by_cases c50 : a < 204; · exact go 200 4 rowLink50 (by omega) (by omega)
  by_cases c51 : a < 208; · exact go 204 4 rowLink51 (by omega) (by omega)
  by_cases c52 : a < 212; · exact go 208 4 rowLink52 (by omega) (by omega)
  by_cases c53 : a < 216; · exact go 212 4 rowLink53 (by omega) (by omega)
  by_cases c54 : a < 220; · exact go 216 4 rowLink54 (by omega) (by omega)
  by_cases c55 : a < 224; · exact go 220 4 rowLink55 (by omega) (by omega)
  by_cases c56 : a < 228; · exact go 224 4 rowLink56 (by omega) (by omega)
  by_cases c57 : a < 232; · exact go 228 4 rowLink57 (by omega) (by omega)
  by_cases c58 : a < 236; · exact go 232 4 rowLink58 (by omega) (by omega)
  by_cases c59 : a < 240; · exact go 236 4 rowLink59 (by omega) (by omega)
  by_cases c60 : a < 244; · exact go 240 4 rowLink60 (by omega) (by omega)
  exact go 244 4 rowLink61 (by omega) (by omega)

theorem entry_e8T (a b : Fin 248) : entry e8T a b = (E8Lie.sL a b).map fun t => (t.1.val, t.2) := by
  have h := rowLink_all a.val a.isLt
  unfold rowLinkOK at h
  have hb := List.all_eq_true.mp h b (List.mem_finRange b)
  have hmod : (⟨a.val % 248, Nat.mod_lt _ (by decide)⟩ : Fin 248) = a := Fin.ext (Nat.mod_eq_of_lt a.isLt)
  rw [hmod] at hb
  exact beq_iff_eq.mp hb

theorem coef_map_val (l : List (Fin 248 × ℤ)) (c : Fin 248) :
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

theorem fE8_eq_sZ (a b c : Fin 248) : fE8 a b c = (E8Lie.sZ a b c : ℂ) := by
  simp only [fE8, scF, sc, entry_e8T, coef_map_val, E8Lie.sZ]

theorem fE8_eq_sc (a b c : Fin 248) : fE8 a b c = E8Lie.e8CertData.structureConstant a b c := by
  rw [fE8_eq_sZ, E8Lie.structureConstant_eq]

/-- Coordinates of a bracket of basis vectors. -/
theorem repr_bracket_sum (a : Fin 248) (v : Fin 248 → ℂ) (c : Fin 248) :
    E8Lie.bB.repr ⁅E8Lie.xs a, ∑ d, v d • E8Lie.xs d⁆ c = ∑ d, v d * fE8 a d c := by
  simp only [lie_sum, lie_smul, E8Lie.bracket_xs, Finset.smul_sum, smul_smul, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, E8Lie.repr_xs, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, fE8_eq_sZ]

theorem bracket_sum (a b : Fin 248) : ⁅E8Lie.xs a, E8Lie.xs b⁆ = ∑ d, fE8 a b d • E8Lie.xs d := by
  rw [E8Lie.bracket_xs]
  simp only [fE8_eq_sZ]

/-- **Jacobi**, from the Lie algebra `e8Lie`. -/
theorem e8_jacobi : JacobiCoord fE8 := by
  intro a b x c
  have h := leibniz_lie (E8Lie.xs b) (E8Lie.xs a) (E8Lie.xs x)
  have h' : ⁅E8Lie.xs b, ⁅E8Lie.xs a, E8Lie.xs x⁆⁆ - ⁅E8Lie.xs a, ⁅E8Lie.xs b, E8Lie.xs x⁆⁆ =
      ⁅⁅E8Lie.xs b, E8Lie.xs a⁆, E8Lie.xs x⁆ := by rw [h]; abel
  have hc := congrArg (fun y => E8Lie.bB.repr y c) h'
  simp only [map_sub, Finsupp.coe_sub, Pi.sub_apply] at hc
  rw [bracket_sum a x, bracket_sum b x, repr_bracket_sum, repr_bracket_sum, bracket_sum b a,
    sum_lie] at hc
  simp only [smul_lie] at hc
  have hr : E8Lie.bB.repr (∑ e, fE8 b a e • ⁅E8Lie.xs e, E8Lie.xs x⁆) c = ∑ e, fE8 b a e * fE8 e x c := by
    simp only [bracket_sum, Finset.smul_sum, smul_smul, map_sum, map_smul, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, E8Lie.repr_xs, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hr] at hc
  have hanti : ∀ e, fE8 b a e = -fE8 a b e := by
    intro e
    rw [fE8_eq_sc, fE8_eq_sc, VOA.AffineGeneral.LieData.structureConstant_antisymm]
  simp only [hanti, neg_mul, Finset.sum_neg_distrib] at hc
  linear_combination hc

theorem e8_bound : boundOK e8T 248 = true :=
  boundOK_of_chunks _ _ fun i hi => by
    by_cases c0 : i < 4; · exact ⟨0, 4, by omega, by omega, e8_bound0⟩
    by_cases c1 : i < 8; · exact ⟨4, 8, by omega, by omega, e8_bound1⟩
    by_cases c2 : i < 12; · exact ⟨8, 12, by omega, by omega, e8_bound2⟩
    by_cases c3 : i < 16; · exact ⟨12, 16, by omega, by omega, e8_bound3⟩
    by_cases c4 : i < 20; · exact ⟨16, 20, by omega, by omega, e8_bound4⟩
    by_cases c5 : i < 24; · exact ⟨20, 24, by omega, by omega, e8_bound5⟩
    by_cases c6 : i < 28; · exact ⟨24, 28, by omega, by omega, e8_bound6⟩
    by_cases c7 : i < 32; · exact ⟨28, 32, by omega, by omega, e8_bound7⟩
    by_cases c8 : i < 36; · exact ⟨32, 36, by omega, by omega, e8_bound8⟩
    by_cases c9 : i < 40; · exact ⟨36, 40, by omega, by omega, e8_bound9⟩
    by_cases c10 : i < 44; · exact ⟨40, 44, by omega, by omega, e8_bound10⟩
    by_cases c11 : i < 48; · exact ⟨44, 48, by omega, by omega, e8_bound11⟩
    by_cases c12 : i < 52; · exact ⟨48, 52, by omega, by omega, e8_bound12⟩
    by_cases c13 : i < 56; · exact ⟨52, 56, by omega, by omega, e8_bound13⟩
    by_cases c14 : i < 60; · exact ⟨56, 60, by omega, by omega, e8_bound14⟩
    by_cases c15 : i < 64; · exact ⟨60, 64, by omega, by omega, e8_bound15⟩
    by_cases c16 : i < 68; · exact ⟨64, 68, by omega, by omega, e8_bound16⟩
    by_cases c17 : i < 72; · exact ⟨68, 72, by omega, by omega, e8_bound17⟩
    by_cases c18 : i < 76; · exact ⟨72, 76, by omega, by omega, e8_bound18⟩
    by_cases c19 : i < 80; · exact ⟨76, 80, by omega, by omega, e8_bound19⟩
    by_cases c20 : i < 84; · exact ⟨80, 84, by omega, by omega, e8_bound20⟩
    by_cases c21 : i < 88; · exact ⟨84, 88, by omega, by omega, e8_bound21⟩
    by_cases c22 : i < 92; · exact ⟨88, 92, by omega, by omega, e8_bound22⟩
    by_cases c23 : i < 96; · exact ⟨92, 96, by omega, by omega, e8_bound23⟩
    by_cases c24 : i < 100; · exact ⟨96, 100, by omega, by omega, e8_bound24⟩
    by_cases c25 : i < 104; · exact ⟨100, 104, by omega, by omega, e8_bound25⟩
    by_cases c26 : i < 108; · exact ⟨104, 108, by omega, by omega, e8_bound26⟩
    by_cases c27 : i < 112; · exact ⟨108, 112, by omega, by omega, e8_bound27⟩
    by_cases c28 : i < 116; · exact ⟨112, 116, by omega, by omega, e8_bound28⟩
    by_cases c29 : i < 120; · exact ⟨116, 120, by omega, by omega, e8_bound29⟩
    by_cases c30 : i < 124; · exact ⟨120, 124, by omega, by omega, e8_bound30⟩
    by_cases c31 : i < 128; · exact ⟨124, 128, by omega, by omega, e8_bound31⟩
    by_cases c32 : i < 132; · exact ⟨128, 132, by omega, by omega, e8_bound32⟩
    by_cases c33 : i < 136; · exact ⟨132, 136, by omega, by omega, e8_bound33⟩
    by_cases c34 : i < 140; · exact ⟨136, 140, by omega, by omega, e8_bound34⟩
    by_cases c35 : i < 144; · exact ⟨140, 144, by omega, by omega, e8_bound35⟩
    by_cases c36 : i < 148; · exact ⟨144, 148, by omega, by omega, e8_bound36⟩
    by_cases c37 : i < 152; · exact ⟨148, 152, by omega, by omega, e8_bound37⟩
    by_cases c38 : i < 156; · exact ⟨152, 156, by omega, by omega, e8_bound38⟩
    by_cases c39 : i < 160; · exact ⟨156, 160, by omega, by omega, e8_bound39⟩
    by_cases c40 : i < 164; · exact ⟨160, 164, by omega, by omega, e8_bound40⟩
    by_cases c41 : i < 168; · exact ⟨164, 168, by omega, by omega, e8_bound41⟩
    by_cases c42 : i < 172; · exact ⟨168, 172, by omega, by omega, e8_bound42⟩
    by_cases c43 : i < 176; · exact ⟨172, 176, by omega, by omega, e8_bound43⟩
    by_cases c44 : i < 180; · exact ⟨176, 180, by omega, by omega, e8_bound44⟩
    by_cases c45 : i < 184; · exact ⟨180, 184, by omega, by omega, e8_bound45⟩
    by_cases c46 : i < 188; · exact ⟨184, 188, by omega, by omega, e8_bound46⟩
    by_cases c47 : i < 192; · exact ⟨188, 192, by omega, by omega, e8_bound47⟩
    by_cases c48 : i < 196; · exact ⟨192, 196, by omega, by omega, e8_bound48⟩
    by_cases c49 : i < 200; · exact ⟨196, 200, by omega, by omega, e8_bound49⟩
    by_cases c50 : i < 204; · exact ⟨200, 204, by omega, by omega, e8_bound50⟩
    by_cases c51 : i < 208; · exact ⟨204, 208, by omega, by omega, e8_bound51⟩
    by_cases c52 : i < 212; · exact ⟨208, 212, by omega, by omega, e8_bound52⟩
    by_cases c53 : i < 216; · exact ⟨212, 216, by omega, by omega, e8_bound53⟩
    by_cases c54 : i < 220; · exact ⟨216, 220, by omega, by omega, e8_bound54⟩
    by_cases c55 : i < 224; · exact ⟨220, 224, by omega, by omega, e8_bound55⟩
    by_cases c56 : i < 228; · exact ⟨224, 228, by omega, by omega, e8_bound56⟩
    by_cases c57 : i < 232; · exact ⟨228, 232, by omega, by omega, e8_bound57⟩
    by_cases c58 : i < 236; · exact ⟨232, 236, by omega, by omega, e8_bound58⟩
    by_cases c59 : i < 240; · exact ⟨236, 240, by omega, by omega, e8_bound59⟩
    by_cases c60 : i < 244; · exact ⟨240, 244, by omega, by omega, e8_bound60⟩
    exact ⟨244, 248, by omega, by omega, e8_bound61⟩

/-! ## Stability of `I₂` -/

theorem quadP_bridge (l : List (ℕ × ℕ × ℤ)) : E6Sparse.quadP 248 l = E7Sparse.quadP 248 l := rfl

/-- Index of a quadratic of `I₂`. -/
def qIdx : Option E8data.ρ → ℕ
  | none => 3875
  | some r => (show Fin 3875 from r).val

theorem qIdx_lt (s : Option E8data.ρ) : qIdx s < 3876 := by
  cases s with
  | none => simp [qIdx]
  | some r => have := (show Fin 3875 from r).2; simp only [qIdx]; omega

theorem quadraticRelation_fullMatrix (s : Option E8data.ρ) :
    quadraticRelation (E8data.fullMatrix s) = E7Sparse.quadP 248 (Pq (qIdx s)) := by
  cases s with
  | none =>
    show quadraticRelation cas = _
    rw [quadraticRelation_cas]; simp [qIdx, Pq]
  | some r =>
    show quadraticRelation (rel (show Fin 3875 from r)) = _
    rw [quadraticRelation_rel]; simp [qIdx, Pq, (show Fin 3875 from r).2]

/-- The span of `I₂`. -/
def S2 : Submodule ℂ (MvPolynomial (Fin 248) ℂ) :=
  Submodule.span ℂ (Set.range fun s => quadraticRelation (E8data.fullMatrix s))

theorem Pq_mem (t : ℕ) (ht : t ≤ 3875) : E7Sparse.quadP 248 (Pq t) ∈ S2 := by
  by_cases h : t < 3875
  · have := quadraticRelation_fullMatrix (some (show E8data.ρ from (⟨t, h⟩ : Fin 3875)))
    simp only [qIdx] at this
    rw [← this]
    exact Submodule.subset_span ⟨_, rfl⟩
  · have ht' : t = 3875 := by omega
    subst ht'
    have := quadraticRelation_fullMatrix none
    simp only [qIdx] at this
    rw [← this]
    exact Submodule.subset_span ⟨_, rfl⟩

theorem intCast_mul_mem (z : ℤ) {q : MvPolynomial (Fin 248) ℂ} (hq : q ∈ S2) :
    (z : MvPolynomial (Fin 248) ℂ) * q ∈ S2 := by
  have : (z : MvPolynomial (Fin 248) ℂ) * q = (z : ℂ) • q := by
    rw [Algebra.smul_def]; simp
  rw [this]; exact S2.smul_mem _ hq

theorem quadP_flatMap8 {α : Type*} (l : List α) (g : α → List (ℕ × ℕ × ℤ)) :
    E7Sparse.quadP 248 (l.flatMap g) = (l.map fun a => E7Sparse.quadP 248 (g a)).sum := by
  induction l with
  | nil => simp [E7Sparse.quadP]
  | cons a l ih => rw [List.flatMap_cons, E7Sparse.quadP_append, ih, List.map_cons, List.sum_cons]

theorem stabRow_sound (g r : ℕ) (c : List ℕ) (h : stabRowOK g r c = true) :
    E7Sparse.quadP 248 (adS e8T g (Pq r)) ∈ S2 := by
  simp only [stabRowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hL, hs⟩, hz⟩ := h
  have h0 := E7Sparse.quadP_eq_zero_of_quadZero (n := 248) _ hz
  rw [E7Sparse.quadP_append, E7Sparse.quadP_scaleQ, E7Sparse.quadP_scaleQ, quadP_flatMap8] at h0
  have hmem : (certL c : MvPolynomial (Fin 248) ℂ) * E7Sparse.quadP 248 (adS e8T g (Pq r)) ∈ S2 := by
    have e : (certL c : MvPolynomial (Fin 248) ℂ) * E7Sparse.quadP 248 (adS e8T g (Pq r)) =
        ((pairsOf c.tail).map fun p => E7Sparse.quadP 248 (E7Sparse.scaleQ p.1 (Pq p.2))).sum := by
      push_cast at h0 ⊢
      linear_combination h0
    rw [e]
    refine list_sum_mem fun y hy => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    rw [E7Sparse.quadP_scaleQ]
    exact intCast_mul_mem _ (Pq_mem _ (by simpa using List.all_eq_true.mp hs p hp))
  have hC : ((certL c : ℂ))⁻¹ • ((certL c : MvPolynomial (Fin 248) ℂ) *
      E7Sparse.quadP 248 (adS e8T g (Pq r))) = E7Sparse.quadP 248 (adS e8T g (Pq r)) := by
    rw [smul_eq_C_mul, ← mul_assoc,
      show (certL c : MvPolynomial (Fin 248) ℂ) = MvPolynomial.C (certL c : ℂ) by simp,
      ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hL), map_one, one_mul]
  rw [← hC]
  exact S2.smul_mem _ hmem

theorem stable_gen (g : ℕ) (hg : g < 248)
    (h : ∀ r, r < 3876 → ∃ c, stabRowOK g r c = true) :
    ∀ q ∈ S2, adDer fE8 ⟨g, hg⟩ q ∈ S2 := by
  intro q hq
  induction hq using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    beta_reduce
    have hs : qIdx s < 3876 := qIdx_lt s
    erw [quadraticRelation_fullMatrix]
    rw [← quadP_bridge,
      adDer_quadP e8_bound ⟨g, hg⟩ _ (List.all_eq_true.mp Pq_inRange _ (List.mem_range.mpr hs)),
      quadP_bridge]
    obtain ⟨c, hc⟩ := h _ hs
    exact stabRow_sound g _ c hc
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact S2.add_mem hx hy
  | smul a x _ hx => rw [Derivation.map_smul]; exact S2.smul_mem a hx

theorem rows_of_parts (g : ℕ) (d0 : List (List ℕ)) (d1 : List (List ℕ)) (d2 : List (List ℕ)) (d3 : List (List ℕ)) (d4 : List (List ℕ)) (d5 : List (List ℕ)) (d6 : List (List ℕ)) (d7 : List (List ℕ)) (d8 : List (List ℕ)) (d9 : List (List ℕ))
    (h0 : stabPart g d0 0 400 = true)
    (h1 : stabPart g d1 400 800 = true)
    (h2 : stabPart g d2 800 1200 = true)
    (h3 : stabPart g d3 1200 1600 = true)
    (h4 : stabPart g d4 1600 2000 = true)
    (h5 : stabPart g d5 2000 2400 = true)
    (h6 : stabPart g d6 2400 2800 = true)
    (h7 : stabPart g d7 2800 3200 = true)
    (h8 : stabPart g d8 3200 3600 = true)
    (h9 : stabPart g d9 3600 3876 = true)
    : ∀ r, r < 3876 → ∃ c, stabRowOK g r c = true := by
  intro r hr
  by_cases c0 : r < 400; · exact ⟨_, List.all_eq_true.mp h0 r (List.mem_range'_1.mpr ⟨by omega, by omega⟩)⟩
  by_cases c1 : r < 800; · exact ⟨_, List.all_eq_true.mp h1 r (List.mem_range'_1.mpr ⟨by omega, by omega⟩)⟩
  by_cases c2 : r < 1200; · exact ⟨_, List.all_eq_true.mp h2 r (List.mem_range'_1.mpr ⟨by omega, by omega⟩)⟩
  by_cases c3 : r < 1600; · exact ⟨_, List.all_eq_true.mp h3 r (List.mem_range'_1.mpr ⟨by omega, by omega⟩)⟩
  by_cases c4 : r < 2000; · exact ⟨_, List.all_eq_true.mp h4 r (List.mem_range'_1.mpr ⟨by omega, by omega⟩)⟩
  by_cases c5 : r < 2400; · exact ⟨_, List.all_eq_true.mp h5 r (List.mem_range'_1.mpr ⟨by omega, by omega⟩)⟩
  by_cases c6 : r < 2800; · exact ⟨_, List.all_eq_true.mp h6 r (List.mem_range'_1.mpr ⟨by omega, by omega⟩)⟩
  by_cases c7 : r < 3200; · exact ⟨_, List.all_eq_true.mp h7 r (List.mem_range'_1.mpr ⟨by omega, by omega⟩)⟩
  by_cases c8 : r < 3600; · exact ⟨_, List.all_eq_true.mp h8 r (List.mem_range'_1.mpr ⟨by omega, by omega⟩)⟩
  exact ⟨_, List.all_eq_true.mp h9 r (List.mem_range'_1.mpr ⟨by omega, by omega⟩)⟩

theorem hab_of_entry {a b c : Fin 248} {κ : ℤ} (h : entry e8T a b = [((c : ℕ), κ)]) :
    ∀ e, fE8 a b e = if e = c then ((κ : ℤ) : ℂ) else 0 := by
  intro e
  simp only [fE8, scF, sc, h, coef_cons, coef_nil, add_zero]
  by_cases he : e = c
  · subst he; simp
  · have : (c : ℕ) ≠ e := fun h' => he (Fin.ext h'.symm)
    simp [he, this]

theorem st15 : ∀ q ∈ S2, adDer fE8 (15 : Fin 248) q ∈ S2 :=
  stable_gen 15 (by norm_num) (rows_of_parts 15 _ _ _ _ _ _ _ _ _ _ stab15_p0 stab15_p1 stab15_p2 stab15_p3 stab15_p4 stab15_p5 stab15_p6 stab15_p7 stab15_p8 stab15_p9)

theorem st14 : ∀ q ∈ S2, adDer fE8 (14 : Fin 248) q ∈ S2 :=
  stable_gen 14 (by norm_num) (rows_of_parts 14 _ _ _ _ _ _ _ _ _ _ stab14_p0 stab14_p1 stab14_p2 stab14_p3 stab14_p4 stab14_p5 stab14_p6 stab14_p7 stab14_p8 stab14_p9)

theorem st13 : ∀ q ∈ S2, adDer fE8 (13 : Fin 248) q ∈ S2 :=
  stable_gen 13 (by norm_num) (rows_of_parts 13 _ _ _ _ _ _ _ _ _ _ stab13_p0 stab13_p1 stab13_p2 stab13_p3 stab13_p4 stab13_p5 stab13_p6 stab13_p7 stab13_p8 stab13_p9)

theorem st12 : ∀ q ∈ S2, adDer fE8 (12 : Fin 248) q ∈ S2 :=
  stable_gen 12 (by norm_num) (rows_of_parts 12 _ _ _ _ _ _ _ _ _ _ stab12_p0 stab12_p1 stab12_p2 stab12_p3 stab12_p4 stab12_p5 stab12_p6 stab12_p7 stab12_p8 stab12_p9)

theorem st11 : ∀ q ∈ S2, adDer fE8 (11 : Fin 248) q ∈ S2 :=
  stable_gen 11 (by norm_num) (rows_of_parts 11 _ _ _ _ _ _ _ _ _ _ stab11_p0 stab11_p1 stab11_p2 stab11_p3 stab11_p4 stab11_p5 stab11_p6 stab11_p7 stab11_p8 stab11_p9)

theorem st10 : ∀ q ∈ S2, adDer fE8 (10 : Fin 248) q ∈ S2 :=
  stable_gen 10 (by norm_num) (rows_of_parts 10 _ _ _ _ _ _ _ _ _ _ stab10_p0 stab10_p1 stab10_p2 stab10_p3 stab10_p4 stab10_p5 stab10_p6 stab10_p7 stab10_p8 stab10_p9)

theorem st9 : ∀ q ∈ S2, adDer fE8 (9 : Fin 248) q ∈ S2 :=
  stable_gen 9 (by norm_num) (rows_of_parts 9 _ _ _ _ _ _ _ _ _ _ stab9_p0 stab9_p1 stab9_p2 stab9_p3 stab9_p4 stab9_p5 stab9_p6 stab9_p7 stab9_p8 stab9_p9)

theorem st8 : ∀ q ∈ S2, adDer fE8 (8 : Fin 248) q ∈ S2 :=
  stable_gen 8 (by norm_num) (rows_of_parts 8 _ _ _ _ _ _ _ _ _ _ stab8_p0 stab8_p1 stab8_p2 stab8_p3 stab8_p4 stab8_p5 stab8_p6 stab8_p7 stab8_p8 stab8_p9)

theorem st135 : ∀ q ∈ S2, adDer fE8 (135 : Fin 248) q ∈ S2 :=
  stable_gen 135 (by norm_num) (rows_of_parts 135 _ _ _ _ _ _ _ _ _ _ stab135_p0 stab135_p1 stab135_p2 stab135_p3 stab135_p4 stab135_p5 stab135_p6 stab135_p7 stab135_p8 stab135_p9)

theorem st134 : ∀ q ∈ S2, adDer fE8 (134 : Fin 248) q ∈ S2 :=
  stable_gen 134 (by norm_num) (rows_of_parts 134 _ _ _ _ _ _ _ _ _ _ stab134_p0 stab134_p1 stab134_p2 stab134_p3 stab134_p4 stab134_p5 stab134_p6 stab134_p7 stab134_p8 stab134_p9)

theorem st133 : ∀ q ∈ S2, adDer fE8 (133 : Fin 248) q ∈ S2 :=
  stable_gen 133 (by norm_num) (rows_of_parts 133 _ _ _ _ _ _ _ _ _ _ stab133_p0 stab133_p1 stab133_p2 stab133_p3 stab133_p4 stab133_p5 stab133_p6 stab133_p7 stab133_p8 stab133_p9)

theorem st132 : ∀ q ∈ S2, adDer fE8 (132 : Fin 248) q ∈ S2 :=
  stable_gen 132 (by norm_num) (rows_of_parts 132 _ _ _ _ _ _ _ _ _ _ stab132_p0 stab132_p1 stab132_p2 stab132_p3 stab132_p4 stab132_p5 stab132_p6 stab132_p7 stab132_p8 stab132_p9)

theorem st131 : ∀ q ∈ S2, adDer fE8 (131 : Fin 248) q ∈ S2 :=
  stable_gen 131 (by norm_num) (rows_of_parts 131 _ _ _ _ _ _ _ _ _ _ stab131_p0 stab131_p1 stab131_p2 stab131_p3 stab131_p4 stab131_p5 stab131_p6 stab131_p7 stab131_p8 stab131_p9)

theorem st130 : ∀ q ∈ S2, adDer fE8 (130 : Fin 248) q ∈ S2 :=
  stable_gen 130 (by norm_num) (rows_of_parts 130 _ _ _ _ _ _ _ _ _ _ stab130_p0 stab130_p1 stab130_p2 stab130_p3 stab130_p4 stab130_p5 stab130_p6 stab130_p7 stab130_p8 stab130_p9)

theorem st129 : ∀ q ∈ S2, adDer fE8 (129 : Fin 248) q ∈ S2 :=
  stable_gen 129 (by norm_num) (rows_of_parts 129 _ _ _ _ _ _ _ _ _ _ stab129_p0 stab129_p1 stab129_p2 stab129_p3 stab129_p4 stab129_p5 stab129_p6 stab129_p7 stab129_p8 stab129_p9)

theorem st128 : ∀ q ∈ S2, adDer fE8 (128 : Fin 248) q ∈ S2 :=
  stable_gen 128 (by norm_num) (rows_of_parts 128 _ _ _ _ _ _ _ _ _ _ stab128_p0 stab128_p1 stab128_p2 stab128_p3 stab128_p4 stab128_p5 stab128_p6 stab128_p7 stab128_p8 stab128_p9)

theorem st0 : ∀ q ∈ S2, adDer fE8 (0 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 15 135 0 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st15 st135

theorem st1 : ∀ q ∈ S2, adDer fE8 (1 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 14 134 1 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st14 st134

theorem st2 : ∀ q ∈ S2, adDer fE8 (2 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 13 133 2 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st13 st133

theorem st3 : ∀ q ∈ S2, adDer fE8 (3 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 12 132 3 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st12 st132

theorem st4 : ∀ q ∈ S2, adDer fE8 (4 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 131 4 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st131

theorem st5 : ∀ q ∈ S2, adDer fE8 (5 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 130 5 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st130

theorem st6 : ∀ q ∈ S2, adDer fE8 (6 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 129 6 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st129

theorem st7 : ∀ q ∈ S2, adDer fE8 (7 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 128 7 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st128

theorem st16 : ∀ q ∈ S2, adDer fE8 (16 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 9 16 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st9

theorem st17 : ∀ q ∈ S2, adDer fE8 (17 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 10 17 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st10

theorem st18 : ∀ q ∈ S2, adDer fE8 (18 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 11 18 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st11

theorem st19 : ∀ q ∈ S2, adDer fE8 (19 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 12 19 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st12

theorem st20 : ∀ q ∈ S2, adDer fE8 (20 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 12 13 20 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st12 st13

theorem st21 : ∀ q ∈ S2, adDer fE8 (21 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 12 14 21 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st12 st14

theorem st22 : ∀ q ∈ S2, adDer fE8 (22 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 13 15 22 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st13 st15

theorem st23 : ∀ q ∈ S2, adDer fE8 (23 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 17 23 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st17

theorem st24 : ∀ q ∈ S2, adDer fE8 (24 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 18 24 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st18

theorem st25 : ∀ q ∈ S2, adDer fE8 (25 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 19 25 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st19

theorem st26 : ∀ q ∈ S2, adDer fE8 (26 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 20 26 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st20

theorem st27 : ∀ q ∈ S2, adDer fE8 (27 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 21 27 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st21

theorem st28 : ∀ q ∈ S2, adDer fE8 (28 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 13 21 28 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st13 st21

theorem st29 : ∀ q ∈ S2, adDer fE8 (29 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 12 22 29 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st12 st22

theorem st30 : ∀ q ∈ S2, adDer fE8 (30 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 24 30 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st24

theorem st31 : ∀ q ∈ S2, adDer fE8 (31 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 25 31 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st25

theorem st32 : ∀ q ∈ S2, adDer fE8 (32 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 26 32 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st26

theorem st33 : ∀ q ∈ S2, adDer fE8 (33 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 27 33 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st27

theorem st34 : ∀ q ∈ S2, adDer fE8 (34 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 28 34 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st28

theorem st35 : ∀ q ∈ S2, adDer fE8 (35 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 29 35 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st29

theorem st36 : ∀ q ∈ S2, adDer fE8 (36 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 14 29 36 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st14 st29

theorem st37 : ∀ q ∈ S2, adDer fE8 (37 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 31 37 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st31

theorem st38 : ∀ q ∈ S2, adDer fE8 (38 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 32 38 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st32

theorem st39 : ∀ q ∈ S2, adDer fE8 (39 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 33 39 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st33

theorem st40 : ∀ q ∈ S2, adDer fE8 (40 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 34 40 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st34

theorem st41 : ∀ q ∈ S2, adDer fE8 (41 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 12 34 41 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st12 st34

theorem st42 : ∀ q ∈ S2, adDer fE8 (42 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 35 42 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st35

theorem st43 : ∀ q ∈ S2, adDer fE8 (43 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 36 43 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st36

theorem st44 : ∀ q ∈ S2, adDer fE8 (44 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 38 44 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st38

theorem st45 : ∀ q ∈ S2, adDer fE8 (45 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 39 45 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st39

theorem st46 : ∀ q ∈ S2, adDer fE8 (46 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 40 46 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st40

theorem st47 : ∀ q ∈ S2, adDer fE8 (47 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 41 47 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st41

theorem st48 : ∀ q ∈ S2, adDer fE8 (48 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 42 48 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st42

theorem st49 : ∀ q ∈ S2, adDer fE8 (49 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 43 49 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st43

theorem st50 : ∀ q ∈ S2, adDer fE8 (50 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 12 43 50 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st12 st43

theorem st51 : ∀ q ∈ S2, adDer fE8 (51 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 46 51 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st46

theorem st52 : ∀ q ∈ S2, adDer fE8 (52 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 47 52 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st47

theorem st53 : ∀ q ∈ S2, adDer fE8 (53 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 47 53 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st47

theorem st54 : ∀ q ∈ S2, adDer fE8 (54 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 48 54 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st48

theorem st55 : ∀ q ∈ S2, adDer fE8 (55 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 49 55 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st49

theorem st56 : ∀ q ∈ S2, adDer fE8 (56 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 50 56 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st50

theorem st57 : ∀ q ∈ S2, adDer fE8 (57 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 13 50 57 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st13 st50

theorem st58 : ∀ q ∈ S2, adDer fE8 (58 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 52 58 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st52

theorem st59 : ∀ q ∈ S2, adDer fE8 (59 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 53 59 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st53

theorem st60 : ∀ q ∈ S2, adDer fE8 (60 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 55 60 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st55

theorem st61 : ∀ q ∈ S2, adDer fE8 (61 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 56 61 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st56

theorem st62 : ∀ q ∈ S2, adDer fE8 (62 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 56 62 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st56

theorem st63 : ∀ q ∈ S2, adDer fE8 (63 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 57 63 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st57

theorem st64 : ∀ q ∈ S2, adDer fE8 (64 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 59 64 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st59

theorem st65 : ∀ q ∈ S2, adDer fE8 (65 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 59 65 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st59

theorem st66 : ∀ q ∈ S2, adDer fE8 (66 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 61 66 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st61

theorem st67 : ∀ q ∈ S2, adDer fE8 (67 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 62 67 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st62

theorem st68 : ∀ q ∈ S2, adDer fE8 (68 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 63 68 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st63

theorem st69 : ∀ q ∈ S2, adDer fE8 (69 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 63 69 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st63

theorem st70 : ∀ q ∈ S2, adDer fE8 (70 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 65 70 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st65

theorem st71 : ∀ q ∈ S2, adDer fE8 (71 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 67 71 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st67

theorem st72 : ∀ q ∈ S2, adDer fE8 (72 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 67 72 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st67

theorem st73 : ∀ q ∈ S2, adDer fE8 (73 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 68 73 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st68

theorem st74 : ∀ q ∈ S2, adDer fE8 (74 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 69 74 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st69

theorem st75 : ∀ q ∈ S2, adDer fE8 (75 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 12 69 75 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st12 st69

theorem st76 : ∀ q ∈ S2, adDer fE8 (76 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 70 76 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st70

theorem st77 : ∀ q ∈ S2, adDer fE8 (77 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 72 77 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st72

theorem st78 : ∀ q ∈ S2, adDer fE8 (78 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 74 78 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st74

theorem st79 : ∀ q ∈ S2, adDer fE8 (79 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 74 79 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st74

theorem st80 : ∀ q ∈ S2, adDer fE8 (80 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 75 80 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st75

theorem st81 : ∀ q ∈ S2, adDer fE8 (81 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 14 75 81 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st14 st75

theorem st82 : ∀ q ∈ S2, adDer fE8 (82 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 77 82 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st77

theorem st83 : ∀ q ∈ S2, adDer fE8 (83 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 79 83 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st79

theorem st84 : ∀ q ∈ S2, adDer fE8 (84 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 80 84 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st80

theorem st85 : ∀ q ∈ S2, adDer fE8 (85 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 80 85 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st80

theorem st86 : ∀ q ∈ S2, adDer fE8 (86 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 81 86 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st81

theorem st87 : ∀ q ∈ S2, adDer fE8 (87 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 83 87 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st83

theorem st88 : ∀ q ∈ S2, adDer fE8 (88 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 85 88 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st85

theorem st89 : ∀ q ∈ S2, adDer fE8 (89 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 85 89 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st85

theorem st90 : ∀ q ∈ S2, adDer fE8 (90 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 86 90 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st86

theorem st91 : ∀ q ∈ S2, adDer fE8 (91 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 86 91 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st86

theorem st92 : ∀ q ∈ S2, adDer fE8 (92 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 88 92 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st88

theorem st93 : ∀ q ∈ S2, adDer fE8 (93 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 89 93 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st89

theorem st94 : ∀ q ∈ S2, adDer fE8 (94 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 91 94 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st91

theorem st95 : ∀ q ∈ S2, adDer fE8 (95 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 91 95 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st91

theorem st96 : ∀ q ∈ S2, adDer fE8 (96 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 93 96 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st93

theorem st97 : ∀ q ∈ S2, adDer fE8 (97 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 94 97 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st94

theorem st98 : ∀ q ∈ S2, adDer fE8 (98 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 95 98 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st95

theorem st99 : ∀ q ∈ S2, adDer fE8 (99 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 12 95 99 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st12 st95

theorem st100 : ∀ q ∈ S2, adDer fE8 (100 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 96 100 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st96

theorem st101 : ∀ q ∈ S2, adDer fE8 (101 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 98 101 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st98

theorem st102 : ∀ q ∈ S2, adDer fE8 (102 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 99 102 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st99

theorem st103 : ∀ q ∈ S2, adDer fE8 (103 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 13 99 103 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st13 st99

theorem st104 : ∀ q ∈ S2, adDer fE8 (104 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 101 104 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st101

theorem st105 : ∀ q ∈ S2, adDer fE8 (105 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 102 105 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st102

theorem st106 : ∀ q ∈ S2, adDer fE8 (106 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 103 106 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st103

theorem st107 : ∀ q ∈ S2, adDer fE8 (107 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 15 103 107 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st15 st103

theorem st108 : ∀ q ∈ S2, adDer fE8 (108 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 105 108 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st105

theorem st109 : ∀ q ∈ S2, adDer fE8 (109 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 106 109 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st106

theorem st110 : ∀ q ∈ S2, adDer fE8 (110 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 107 110 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st107

theorem st111 : ∀ q ∈ S2, adDer fE8 (111 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 108 111 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st108

theorem st112 : ∀ q ∈ S2, adDer fE8 (112 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 109 112 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st109

theorem st113 : ∀ q ∈ S2, adDer fE8 (113 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 110 113 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st110

theorem st114 : ∀ q ∈ S2, adDer fE8 (114 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 112 114 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st112

theorem st115 : ∀ q ∈ S2, adDer fE8 (115 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 113 115 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st113

theorem st116 : ∀ q ∈ S2, adDer fE8 (116 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 12 114 116 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st12 st114

theorem st117 : ∀ q ∈ S2, adDer fE8 (117 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 115 117 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st115

theorem st118 : ∀ q ∈ S2, adDer fE8 (118 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 14 116 118 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st14 st116

theorem st119 : ∀ q ∈ S2, adDer fE8 (119 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 12 117 119 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st12 st117

theorem st120 : ∀ q ∈ S2, adDer fE8 (120 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 13 119 120 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st13 st119

theorem st121 : ∀ q ∈ S2, adDer fE8 (121 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 14 119 121 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st14 st119

theorem st122 : ∀ q ∈ S2, adDer fE8 (122 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 13 121 122 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st13 st121

theorem st123 : ∀ q ∈ S2, adDer fE8 (123 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 12 122 123 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st12 st122

theorem st124 : ∀ q ∈ S2, adDer fE8 (124 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 11 123 124 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st123

theorem st125 : ∀ q ∈ S2, adDer fE8 (125 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 10 124 125 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st124

theorem st126 : ∀ q ∈ S2, adDer fE8 (126 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 9 125 126 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st125

theorem st127 : ∀ q ∈ S2, adDer fE8 (127 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 8 126 127 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st126

theorem st136 : ∀ q ∈ S2, adDer fE8 (136 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 129 136 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st129

theorem st137 : ∀ q ∈ S2, adDer fE8 (137 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 130 137 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st130

theorem st138 : ∀ q ∈ S2, adDer fE8 (138 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 131 138 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st131

theorem st139 : ∀ q ∈ S2, adDer fE8 (139 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 131 132 139 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st131 st132

theorem st140 : ∀ q ∈ S2, adDer fE8 (140 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 132 133 140 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st132 st133

theorem st141 : ∀ q ∈ S2, adDer fE8 (141 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 132 134 141 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st132 st134

theorem st142 : ∀ q ∈ S2, adDer fE8 (142 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 133 135 142 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st133 st135

theorem st143 : ∀ q ∈ S2, adDer fE8 (143 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 137 143 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st137

theorem st144 : ∀ q ∈ S2, adDer fE8 (144 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 138 144 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st138

theorem st145 : ∀ q ∈ S2, adDer fE8 (145 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 139 145 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st139

theorem st146 : ∀ q ∈ S2, adDer fE8 (146 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 131 140 146 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st131 st140

theorem st147 : ∀ q ∈ S2, adDer fE8 (147 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 131 141 147 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st131 st141

theorem st148 : ∀ q ∈ S2, adDer fE8 (148 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 133 141 148 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st133 st141

theorem st149 : ∀ q ∈ S2, adDer fE8 (149 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 132 142 149 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st132 st142

theorem st150 : ∀ q ∈ S2, adDer fE8 (150 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 144 150 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st144

theorem st151 : ∀ q ∈ S2, adDer fE8 (151 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 145 151 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st145

theorem st152 : ∀ q ∈ S2, adDer fE8 (152 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 146 152 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st146

theorem st153 : ∀ q ∈ S2, adDer fE8 (153 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 147 153 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st147

theorem st154 : ∀ q ∈ S2, adDer fE8 (154 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 131 148 154 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st131 st148

theorem st155 : ∀ q ∈ S2, adDer fE8 (155 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 131 149 155 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st131 st149

theorem st156 : ∀ q ∈ S2, adDer fE8 (156 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 134 149 156 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st134 st149

theorem st157 : ∀ q ∈ S2, adDer fE8 (157 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 151 157 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st151

theorem st158 : ∀ q ∈ S2, adDer fE8 (158 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 152 158 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st152

theorem st159 : ∀ q ∈ S2, adDer fE8 (159 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 153 159 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st153

theorem st160 : ∀ q ∈ S2, adDer fE8 (160 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 154 160 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st154

theorem st161 : ∀ q ∈ S2, adDer fE8 (161 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 132 154 161 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st132 st154

theorem st162 : ∀ q ∈ S2, adDer fE8 (162 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 155 162 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st155

theorem st163 : ∀ q ∈ S2, adDer fE8 (163 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 131 156 163 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st131 st156

theorem st164 : ∀ q ∈ S2, adDer fE8 (164 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 158 164 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st158

theorem st165 : ∀ q ∈ S2, adDer fE8 (165 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 159 165 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st159

theorem st166 : ∀ q ∈ S2, adDer fE8 (166 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 160 166 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st160

theorem st167 : ∀ q ∈ S2, adDer fE8 (167 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 161 167 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st161

theorem st168 : ∀ q ∈ S2, adDer fE8 (168 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 162 168 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st162

theorem st169 : ∀ q ∈ S2, adDer fE8 (169 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 163 169 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st163

theorem st170 : ∀ q ∈ S2, adDer fE8 (170 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 132 163 170 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st132 st163

theorem st171 : ∀ q ∈ S2, adDer fE8 (171 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 166 171 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st166

theorem st172 : ∀ q ∈ S2, adDer fE8 (172 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 167 172 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st167

theorem st173 : ∀ q ∈ S2, adDer fE8 (173 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 131 167 173 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st131 st167

theorem st174 : ∀ q ∈ S2, adDer fE8 (174 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 168 174 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st168

theorem st175 : ∀ q ∈ S2, adDer fE8 (175 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 169 175 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st169

theorem st176 : ∀ q ∈ S2, adDer fE8 (176 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 170 176 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st170

theorem st177 : ∀ q ∈ S2, adDer fE8 (177 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 133 170 177 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st133 st170

theorem st178 : ∀ q ∈ S2, adDer fE8 (178 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 172 178 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st172

theorem st179 : ∀ q ∈ S2, adDer fE8 (179 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 173 179 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st173

theorem st180 : ∀ q ∈ S2, adDer fE8 (180 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 175 180 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st175

theorem st181 : ∀ q ∈ S2, adDer fE8 (181 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 176 181 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st176

theorem st182 : ∀ q ∈ S2, adDer fE8 (182 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 131 176 182 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st131 st176

theorem st183 : ∀ q ∈ S2, adDer fE8 (183 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 177 183 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st177

theorem st184 : ∀ q ∈ S2, adDer fE8 (184 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 179 184 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st179

theorem st185 : ∀ q ∈ S2, adDer fE8 (185 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 179 185 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st179

theorem st186 : ∀ q ∈ S2, adDer fE8 (186 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 181 186 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st181

theorem st187 : ∀ q ∈ S2, adDer fE8 (187 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 182 187 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st182

theorem st188 : ∀ q ∈ S2, adDer fE8 (188 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 183 188 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st183

theorem st189 : ∀ q ∈ S2, adDer fE8 (189 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 131 183 189 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st131 st183

theorem st190 : ∀ q ∈ S2, adDer fE8 (190 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 185 190 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st185

theorem st191 : ∀ q ∈ S2, adDer fE8 (191 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 187 191 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st187

theorem st192 : ∀ q ∈ S2, adDer fE8 (192 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 187 192 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st187

theorem st193 : ∀ q ∈ S2, adDer fE8 (193 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 188 193 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st188

theorem st194 : ∀ q ∈ S2, adDer fE8 (194 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 189 194 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st189

theorem st195 : ∀ q ∈ S2, adDer fE8 (195 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 132 189 195 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st132 st189

theorem st196 : ∀ q ∈ S2, adDer fE8 (196 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 190 196 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st190

theorem st197 : ∀ q ∈ S2, adDer fE8 (197 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 192 197 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st192

theorem st198 : ∀ q ∈ S2, adDer fE8 (198 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 194 198 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st194

theorem st199 : ∀ q ∈ S2, adDer fE8 (199 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 194 199 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st194

theorem st200 : ∀ q ∈ S2, adDer fE8 (200 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 195 200 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st195

theorem st201 : ∀ q ∈ S2, adDer fE8 (201 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 134 195 201 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st134 st195

theorem st202 : ∀ q ∈ S2, adDer fE8 (202 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 197 202 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st197

theorem st203 : ∀ q ∈ S2, adDer fE8 (203 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 199 203 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st199

theorem st204 : ∀ q ∈ S2, adDer fE8 (204 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 200 204 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st200

theorem st205 : ∀ q ∈ S2, adDer fE8 (205 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 200 205 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st200

theorem st206 : ∀ q ∈ S2, adDer fE8 (206 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 201 206 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st201

theorem st207 : ∀ q ∈ S2, adDer fE8 (207 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 203 207 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st203

theorem st208 : ∀ q ∈ S2, adDer fE8 (208 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 205 208 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st205

theorem st209 : ∀ q ∈ S2, adDer fE8 (209 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 131 205 209 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st131 st205

theorem st210 : ∀ q ∈ S2, adDer fE8 (210 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 206 210 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st206

theorem st211 : ∀ q ∈ S2, adDer fE8 (211 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 206 211 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st206

theorem st212 : ∀ q ∈ S2, adDer fE8 (212 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 208 212 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st208

theorem st213 : ∀ q ∈ S2, adDer fE8 (213 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 209 213 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st209

theorem st214 : ∀ q ∈ S2, adDer fE8 (214 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 211 214 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st211

theorem st215 : ∀ q ∈ S2, adDer fE8 (215 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 131 211 215 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st131 st211

theorem st216 : ∀ q ∈ S2, adDer fE8 (216 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 213 216 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st213

theorem st217 : ∀ q ∈ S2, adDer fE8 (217 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 214 217 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st214

theorem st218 : ∀ q ∈ S2, adDer fE8 (218 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 215 218 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st215

theorem st219 : ∀ q ∈ S2, adDer fE8 (219 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 132 215 219 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st132 st215

theorem st220 : ∀ q ∈ S2, adDer fE8 (220 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 216 220 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st216

theorem st221 : ∀ q ∈ S2, adDer fE8 (221 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 218 221 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st218

theorem st222 : ∀ q ∈ S2, adDer fE8 (222 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 219 222 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st219

theorem st223 : ∀ q ∈ S2, adDer fE8 (223 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 133 219 223 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st133 st219

theorem st224 : ∀ q ∈ S2, adDer fE8 (224 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 221 224 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st221

theorem st225 : ∀ q ∈ S2, adDer fE8 (225 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 222 225 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st222

theorem st226 : ∀ q ∈ S2, adDer fE8 (226 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 223 226 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st223

theorem st227 : ∀ q ∈ S2, adDer fE8 (227 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 135 223 227 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st135 st223

theorem st228 : ∀ q ∈ S2, adDer fE8 (228 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 225 228 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st225

theorem st229 : ∀ q ∈ S2, adDer fE8 (229 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 226 229 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st226

theorem st230 : ∀ q ∈ S2, adDer fE8 (230 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 227 230 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st227

theorem st231 : ∀ q ∈ S2, adDer fE8 (231 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 131 228 231 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st131 st228

theorem st232 : ∀ q ∈ S2, adDer fE8 (232 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 229 232 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st229

theorem st233 : ∀ q ∈ S2, adDer fE8 (233 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 230 233 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st230

theorem st234 : ∀ q ∈ S2, adDer fE8 (234 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 131 232 234 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st131 st232

theorem st235 : ∀ q ∈ S2, adDer fE8 (235 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 233 235 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st233

theorem st236 : ∀ q ∈ S2, adDer fE8 (236 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 132 234 236 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st132 st234

theorem st237 : ∀ q ∈ S2, adDer fE8 (237 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 131 235 237 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st131 st235

theorem st238 : ∀ q ∈ S2, adDer fE8 (238 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 134 236 238 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st134 st236

theorem st239 : ∀ q ∈ S2, adDer fE8 (239 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 132 237 239 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st132 st237

theorem st240 : ∀ q ∈ S2, adDer fE8 (240 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 133 239 240 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st133 st239

theorem st241 : ∀ q ∈ S2, adDer fE8 (241 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 134 239 241 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st134 st239

theorem st242 : ∀ q ∈ S2, adDer fE8 (242 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 133 241 242 ((-1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st133 st241

theorem st243 : ∀ q ∈ S2, adDer fE8 (243 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 132 242 243 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st132 st242

theorem st244 : ∀ q ∈ S2, adDer fE8 (244 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 131 243 244 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st131 st243

theorem st245 : ∀ q ∈ S2, adDer fE8 (245 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 130 244 245 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st130 st244

theorem st246 : ∀ q ∈ S2, adDer fE8 (246 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 129 245 246 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st129 st245

theorem st247 : ∀ q ∈ S2, adDer fE8 (247 : Fin 248) q ∈ S2 :=
  stable_of_bracket e8_jacobi S2 128 246 247 ((1 : ℤ) : ℂ) (by norm_num) (hab_of_entry (by decide +kernel)) st128 st246

theorem e8_stable : RelationsStable fE8 E8data.fullMatrix := by
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
  · exact st133 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st134 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st135 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st136 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st137 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st138 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st139 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st140 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st141 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st142 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st143 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st144 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st145 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st146 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st147 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st148 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st149 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st150 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st151 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st152 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st153 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st154 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st155 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st156 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st157 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st158 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st159 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st160 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st161 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st162 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st163 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st164 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st165 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st166 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st167 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st168 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st169 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st170 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st171 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st172 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st173 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st174 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st175 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st176 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st177 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st178 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st179 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st180 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st181 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st182 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st183 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st184 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st185 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st186 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st187 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st188 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st189 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st190 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st191 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st192 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st193 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st194 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st195 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st196 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st197 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st198 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st199 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st200 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st201 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st202 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st203 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st204 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st205 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st206 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st207 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st208 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st209 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st210 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st211 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st212 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st213 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st214 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st215 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st216 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st217 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st218 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st219 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st220 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st221 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st222 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st223 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st224 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st225 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st226 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st227 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st228 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st229 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st230 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st231 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st232 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st233 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st234 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st235 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st236 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st237 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st238 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st239 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st240 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st241 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st242 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st243 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st244 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st245 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st246 _ (Submodule.subset_span ⟨r, rfl⟩)
  · exact st247 _ (Submodule.subset_span ⟨r, rfl⟩)

end

end VOA.DeligneAudit.DeligneCarrier.E8

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.E8.e8_jacobi
#print axioms VOA.DeligneAudit.DeligneCarrier.E8.e8_stable
end AxiomAudit
