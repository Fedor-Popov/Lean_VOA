/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6CarrierData
import VOA.DeligneAudit.E6SectorStab11
import VOA.DeligneAudit.E6SectorStab10
import VOA.DeligneAudit.E6SectorStab9
import VOA.DeligneAudit.E6SectorStab8
import VOA.DeligneAudit.E6SectorStab7
import VOA.DeligneAudit.E6SectorStab6
import VOA.DeligneAudit.E6SectorStab47
import VOA.DeligneAudit.E6SectorStab46
import VOA.DeligneAudit.E6SectorStab45
import VOA.DeligneAudit.E6SectorStab44
import VOA.DeligneAudit.E6SectorStab43
import VOA.DeligneAudit.E6SectorStab42
import VOA.AffineGeneral.E6Lie
import VOA.DeligneAudit.E6SectorSparse

set_option linter.style.longLine false

/-!
# E₆ sector data: structure constants, Jacobi, ad-stability of `I₂`
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E6

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6Sparse VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector

noncomputable section

/-- Structure constants of `𝔢₆` in the carrier basis. -/
abbrev fE6 : Fin 78 → Fin 78 → Fin 78 → ℂ := scF e6T 78

theorem e6_jacobi : JacobiCoord fE6 := jacobiCoord_of_checks e6Checks

/-! ## Stability of `I₂` -/

/-- Index of a quadratic of `I₂`. -/
def qIdx : Option E6data.ρ → ℕ
  | none => 650
  | some r => (show Fin 650 from r).val

theorem qIdx_lt (s : Option E6data.ρ) : qIdx s < 651 := by
  cases s with
  | none => simp [qIdx]
  | some r => have := (show Fin 650 from r).2; simp only [qIdx]; omega

theorem quadraticRelation_fullMatrix (s : Option E6data.ρ) :
    quadraticRelation (E6data.fullMatrix s) = quadP 78 (Pq (qIdx s)) := by
  cases s with
  | none =>
    show quadraticRelation cas = _
    rw [quadraticRelation_cas]; simp [qIdx, Pq]
  | some r =>
    show quadraticRelation (rel (show Fin 650 from r)) = _
    rw [quadraticRelation_rel]; simp [qIdx, Pq, (show Fin 650 from r).2]

/-- The span of `I₂`. -/
def S2 : Submodule ℂ (MvPolynomial (Fin 78) ℂ) :=
  Submodule.span ℂ (Set.range fun s => quadraticRelation (E6data.fullMatrix s))

theorem Pq_mem (t : ℕ) (ht : t ≤ 650) : quadP 78 (Pq t) ∈ S2 := by
  by_cases h : t < 650
  · have := quadraticRelation_fullMatrix (some (show E6data.ρ from (⟨t, h⟩ : Fin 650)))
    simp only [qIdx] at this
    rw [← this]
    exact Submodule.subset_span ⟨_, rfl⟩
  · have ht' : t = 650 := by omega
    subst ht'
    have := quadraticRelation_fullMatrix none
    simp only [qIdx] at this
    rw [← this]
    exact Submodule.subset_span ⟨_, rfl⟩

theorem intCast_mul_mem (z : ℤ) {q : MvPolynomial (Fin 78) ℂ} (hq : q ∈ S2) :
    (z : MvPolynomial (Fin 78) ℂ) * q ∈ S2 := by
  have : (z : MvPolynomial (Fin 78) ℂ) * q = (z : ℂ) • q := by
    rw [Algebra.smul_def]; simp
  rw [this]; exact S2.smul_mem _ hq

theorem stabRow_sound (g r : ℕ) (c : List ℕ) (h : stabRowOK g r c = true) :
    quadP 78 (adS e6T g (Pq r)) ∈ S2 := by
  simp only [stabRowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hL, hs⟩, hz⟩ := h
  have h0 := quadP_eq_zero_of_quadZero (n := 78) (by norm_num) _ hz
  rw [quadP_append', quadP_scaleQ, negQ, quadP_scaleQ, quadP_flatMap'] at h0
  have hmem : (certL c : MvPolynomial (Fin 78) ℂ) * quadP 78 (adS e6T g (Pq r)) ∈ S2 := by
    have e : (certL c : MvPolynomial (Fin 78) ℂ) * quadP 78 (adS e6T g (Pq r)) =
        ((pairsOf c.tail).map fun p => quadP 78 (scaleQ p.1 (Pq p.2))).sum := by
      push_cast at h0 ⊢
      linear_combination h0
    rw [e]
    refine list_sum_mem fun y hy => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    rw [quadP_scaleQ]
    exact intCast_mul_mem _ (Pq_mem _ (by simpa using List.all_eq_true.mp hs p hp))
  have hC : ((certL c : ℂ))⁻¹ • ((certL c : MvPolynomial (Fin 78) ℂ) * quadP 78 (adS e6T g (Pq r)))
      = quadP 78 (adS e6T g (Pq r)) := by
    rw [smul_eq_C_mul, ← mul_assoc, show (certL c : MvPolynomial (Fin 78) ℂ) = MvPolynomial.C (certL c : ℂ) by simp,
      ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hL), map_one, one_mul]
  rw [← hC]
  exact S2.smul_mem _ hmem

theorem stable_gen (g : ℕ) (hg : g < 78) (rows : List (List ℕ)) (h : stabOK g rows = true) :
    ∀ q ∈ S2, adDer fE6 ⟨g, hg⟩ q ∈ S2 := by
  simp only [stabOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlen, hrows⟩ := h
  intro q hq
  induction hq using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    beta_reduce
    have hs : qIdx s < 651 := qIdx_lt s
    erw [quadraticRelation_fullMatrix]
    rw [adDer_quadP e6_bound ⟨g, hg⟩ _
      (List.all_eq_true.mp Pq_inRange _ (List.mem_range.mpr hs))]
    exact stabRow_sound g _ _ (List.all_eq_true.mp hrows _ (List.mem_range.mpr hs))
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact S2.add_mem hx hy
  | smul a x _ hx => rw [Derivation.map_smul]; exact S2.smul_mem a hx

theorem hab_of_entry {a b c : Fin 78} {κ : ℤ} (h : entry e6T a b = [((c : ℕ), κ)]) :
    ∀ e, fE6 a b e = if e = c then ((κ : ℤ) : ℂ) else 0 := by
  intro e
  simp only [fE6, scF, sc, h, coef_cons, coef_nil, add_zero]
  by_cases he : e = c
  · subst he; simp
  · have : (c : ℕ) ≠ e := fun h' => he (Fin.ext h'.symm)
    simp [he, this]

theorem st11 : ∀ q ∈ S2, adDer fE6 (11 : Fin 78) q ∈ S2 :=
  stable_gen 11 (by norm_num) stab11 stab11_ok

theorem st10 : ∀ q ∈ S2, adDer fE6 (10 : Fin 78) q ∈ S2 :=
  stable_gen 10 (by norm_num) stab10 stab10_ok

theorem st9 : ∀ q ∈ S2, adDer fE6 (9 : Fin 78) q ∈ S2 :=
  stable_gen 9 (by norm_num) stab9 stab9_ok

theorem st8 : ∀ q ∈ S2, adDer fE6 (8 : Fin 78) q ∈ S2 :=
  stable_gen 8 (by norm_num) stab8 stab8_ok

theorem st7 : ∀ q ∈ S2, adDer fE6 (7 : Fin 78) q ∈ S2 :=
  stable_gen 7 (by norm_num) stab7 stab7_ok

theorem st6 : ∀ q ∈ S2, adDer fE6 (6 : Fin 78) q ∈ S2 :=
  stable_gen 6 (by norm_num) stab6 stab6_ok

theorem st47 : ∀ q ∈ S2, adDer fE6 (47 : Fin 78) q ∈ S2 :=
  stable_gen 47 (by norm_num) stab47 stab47_ok

theorem st46 : ∀ q ∈ S2, adDer fE6 (46 : Fin 78) q ∈ S2 :=
  stable_gen 46 (by norm_num) stab46 stab46_ok

theorem st45 : ∀ q ∈ S2, adDer fE6 (45 : Fin 78) q ∈ S2 :=
  stable_gen 45 (by norm_num) stab45 stab45_ok

theorem st44 : ∀ q ∈ S2, adDer fE6 (44 : Fin 78) q ∈ S2 :=
  stable_gen 44 (by norm_num) stab44 stab44_ok

theorem st43 : ∀ q ∈ S2, adDer fE6 (43 : Fin 78) q ∈ S2 :=
  stable_gen 43 (by norm_num) stab43 stab43_ok

theorem st42 : ∀ q ∈ S2, adDer fE6 (42 : Fin 78) q ∈ S2 :=
  stable_gen 42 (by norm_num) stab42 stab42_ok

theorem st12 : ∀ q ∈ S2, adDer fE6 (12 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 6 7 12 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st6 st7

theorem st5 : ∀ q ∈ S2, adDer fE6 (5 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 6 42 5 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st6 st42

theorem st13 : ∀ q ∈ S2, adDer fE6 (13 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 7 8 13 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st7 st8

theorem st4 : ∀ q ∈ S2, adDer fE6 (4 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 7 43 4 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st7 st43

theorem st14 : ∀ q ∈ S2, adDer fE6 (14 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 8 9 14 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st9

theorem st15 : ∀ q ∈ S2, adDer fE6 (15 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 8 10 15 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st10

theorem st3 : ∀ q ∈ S2, adDer fE6 (3 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 8 44 3 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st44

theorem st16 : ∀ q ∈ S2, adDer fE6 (16 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 9 11 16 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st11

theorem st2 : ∀ q ∈ S2, adDer fE6 (2 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 9 45 2 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st45

theorem st1 : ∀ q ∈ S2, adDer fE6 (1 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 10 46 1 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st10 st46

theorem st0 : ∀ q ∈ S2, adDer fE6 (0 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 11 47 0 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st11 st47

theorem st48 : ∀ q ∈ S2, adDer fE6 (48 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 42 43 48 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st42 st43

theorem st49 : ∀ q ∈ S2, adDer fE6 (49 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 43 44 49 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st43 st44

theorem st50 : ∀ q ∈ S2, adDer fE6 (50 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 44 45 50 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st44 st45

theorem st51 : ∀ q ∈ S2, adDer fE6 (51 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 44 46 51 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st44 st46

theorem st52 : ∀ q ∈ S2, adDer fE6 (52 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 45 47 52 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st45 st47

theorem st17 : ∀ q ∈ S2, adDer fE6 (17 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 6 13 17 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st6 st13

theorem st18 : ∀ q ∈ S2, adDer fE6 (18 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 7 14 18 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st7 st14

theorem st19 : ∀ q ∈ S2, adDer fE6 (19 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 7 15 19 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st7 st15

theorem st21 : ∀ q ∈ S2, adDer fE6 (21 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 8 16 21 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st8 st16

theorem st20 : ∀ q ∈ S2, adDer fE6 (20 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 9 15 20 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st15

theorem st22 : ∀ q ∈ S2, adDer fE6 (22 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 12 14 22 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st12 st14

theorem st23 : ∀ q ∈ S2, adDer fE6 (23 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 12 15 23 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st12 st15

theorem st25 : ∀ q ∈ S2, adDer fE6 (25 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 13 16 25 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st13 st16

theorem st26 : ∀ q ∈ S2, adDer fE6 (26 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 15 16 26 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st15 st16

theorem st53 : ∀ q ∈ S2, adDer fE6 (53 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 42 49 53 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st42 st49

theorem st54 : ∀ q ∈ S2, adDer fE6 (54 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 43 50 54 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st43 st50

theorem st55 : ∀ q ∈ S2, adDer fE6 (55 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 43 51 55 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st43 st51

theorem st57 : ∀ q ∈ S2, adDer fE6 (57 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 44 52 57 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st44 st52

theorem st56 : ∀ q ∈ S2, adDer fE6 (56 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 45 51 56 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st45 st51

theorem st58 : ∀ q ∈ S2, adDer fE6 (58 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 48 50 58 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st48 st50

theorem st59 : ∀ q ∈ S2, adDer fE6 (59 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 48 51 59 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st48 st51

theorem st61 : ∀ q ∈ S2, adDer fE6 (61 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 49 52 61 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st49 st52

theorem st62 : ∀ q ∈ S2, adDer fE6 (62 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 51 52 62 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st51 st52

theorem st29 : ∀ q ∈ S2, adDer fE6 (29 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 6 25 29 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st6 st25

theorem st24 : ∀ q ∈ S2, adDer fE6 (24 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 7 20 24 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st7 st20

theorem st30 : ∀ q ∈ S2, adDer fE6 (30 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 7 26 30 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st7 st26

theorem st27 : ∀ q ∈ S2, adDer fE6 (27 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 9 23 27 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st9 st23

theorem st32 : ∀ q ∈ S2, adDer fE6 (32 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 12 26 32 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st12 st26

theorem st28 : ∀ q ∈ S2, adDer fE6 (28 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 13 20 28 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st13 st20

theorem st33 : ∀ q ∈ S2, adDer fE6 (33 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 13 26 33 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st13 st26

theorem st31 : ∀ q ∈ S2, adDer fE6 (31 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 14 23 31 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st14 st23

theorem st35 : ∀ q ∈ S2, adDer fE6 (35 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 17 26 35 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st17 st26

theorem st34 : ∀ q ∈ S2, adDer fE6 (34 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 18 23 34 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st18 st23

theorem st36 : ∀ q ∈ S2, adDer fE6 (36 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 18 26 36 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st18 st26

theorem st38 : ∀ q ∈ S2, adDer fE6 (38 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 22 26 38 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st22 st26

theorem st37 : ∀ q ∈ S2, adDer fE6 (37 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 23 25 37 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st23 st25

theorem st65 : ∀ q ∈ S2, adDer fE6 (65 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 42 61 65 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st42 st61

theorem st60 : ∀ q ∈ S2, adDer fE6 (60 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 43 56 60 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st43 st56

theorem st66 : ∀ q ∈ S2, adDer fE6 (66 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 43 62 66 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st43 st62

theorem st63 : ∀ q ∈ S2, adDer fE6 (63 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 45 59 63 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st45 st59

theorem st68 : ∀ q ∈ S2, adDer fE6 (68 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 48 62 68 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st48 st62

theorem st64 : ∀ q ∈ S2, adDer fE6 (64 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 49 56 64 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st49 st56

theorem st69 : ∀ q ∈ S2, adDer fE6 (69 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 49 62 69 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st49 st62

theorem st67 : ∀ q ∈ S2, adDer fE6 (67 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 50 59 67 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st50 st59

theorem st71 : ∀ q ∈ S2, adDer fE6 (71 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 53 62 71 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st53 st62

theorem st70 : ∀ q ∈ S2, adDer fE6 (70 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 54 59 70 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st54 st59

theorem st72 : ∀ q ∈ S2, adDer fE6 (72 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 54 62 72 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st54 st62

theorem st74 : ∀ q ∈ S2, adDer fE6 (74 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 58 62 74 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st58 st62

theorem st73 : ∀ q ∈ S2, adDer fE6 (73 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 59 61 73 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st59 st61

theorem st39 : ∀ q ∈ S2, adDer fE6 (39 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 7 38 39 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st7 st38

theorem st40 : ∀ q ∈ S2, adDer fE6 (40 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 13 38 40 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st13 st38

theorem st41 : ∀ q ∈ S2, adDer fE6 (41 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 19 38 41 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st19 st38

theorem st75 : ∀ q ∈ S2, adDer fE6 (75 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 43 74 75 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st43 st74

theorem st76 : ∀ q ∈ S2, adDer fE6 (76 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 49 74 76 (-1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st49 st74

theorem st77 : ∀ q ∈ S2, adDer fE6 (77 : Fin 78) q ∈ S2 :=
  stable_of_bracket e6_jacobi S2 55 74 77 (1 : ℤ) (by norm_num) (hab_of_entry (by decide +kernel)) st55 st74

/-- **`I₂` is ad-stable.** -/
theorem e6_stable : RelationsStable fE6 E6data.fullMatrix := by
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


end

end VOA.DeligneAudit.DeligneCarrier.E6
