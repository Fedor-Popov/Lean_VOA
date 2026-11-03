/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusC2M1Cert
import VOA.Modules.PairClosure

/-!
# `M(1)⁺`: the generator OPE table of `{ω, W⁴}` closes

Let `T = iterProdSpan M1P {ω, W⁴}` (the span of the iterated products `g₁₍₋ₙ₁₎⋯g_k₍₋ₙ_k₎𝟙`).

## Main results

* `pair_closed` — `g₍ⱼ₎h ∈ T` for all `g, h ∈ {ω, W⁴}` and `j ≥ 0`.  The `(ω, ω)` entries are
  free (`conformal_smul_conformal_mem_iterProdSpan`), `ω₍₀₎, ω₍₁₎` are `L(−1), L(0)`, the
  `(W, ω)` column follows by skew symmetry, and the remaining finitely many entries
  `ω₍ⱼ₎W` (`2 ≤ j ≤ 5`) and `W₍ⱼ₎W` (`0 ≤ j ≤ 7`) are explicit kernel-checked certificates, e.g.
  `W₍₁₎W = −384 L(−4)ω + 240 L(−3)²𝟙 + 96 L(−2)W + 28 W₍₋₃₎𝟙` (found by exact linear algebra,
  `scratchpad/q2c/cert.py`).
* `T_smul_closed` — `T` is closed under **all** products `u₍ₙ₎v` (`u, v ∈ T`, `n ∈ ℤ`), by the
  general pair-closure theorem `iterProdSpan_smul_closed`.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN VOA.Moonshine LatMod
  MvPolynomial VOA.TripletNilp VOA.SparseRational PlusC2Eval

namespace PlusC2

variable (m : ℕ) (hm : 1 ≤ m)

/-- The strong span `T` of `{ω, W⁴}`. -/
noncomputable abbrev TM : Submodule ℂ (m1Sub m hm).carrier := iterProdSpan (M1P m hm) (gensM m hm)

/-! ## §1  Iterated words -/

/-- The two generators: `true ↦ ω`, `false ↦ W⁴`. -/
noncomputable def gen : Bool → (m1Sub m hm).carrier
  | true => ωM m hm
  | false => WM m hm

def genR : Bool → RawPoly ℕ
  | true => omR
  | false => WR

def genWt : Bool → ℕ
  | true => 2
  | false => 4

theorem gen_mem (g : Bool) : gen m hm g ∈ gensM m hm := by
  cases g
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem hasPoly_gen (g : Bool) : HasPoly m hm (gen m hm g) (genR g) := by
  cases g
  · exact hasPoly_W m hm
  · exact hasPoly_omega m hm

def iwWt : List (Bool × ℕ) → ℕ
  | [] => 0
  | (g, k) :: rest => genWt g + k - 1 + iwWt rest

/-- The polynomial of the iterated word `g₁₍₋k₁₎⋯g_r₍₋k_r₎𝟙`. -/
def iwPoly : List (Bool × ℕ) → RawPoly ℕ
  | [] => vacR
  | (g, k) :: rest => normR (polyAct (genR g) ((k : ℤ) - 1) (iwWt rest) (iwPoly rest))

/-- The iterated word itself. -/
noncomputable def iwVal : List (Bool × ℕ) → (m1Sub m hm).carrier
  | [] => (M1P m hm).vacuum
  | (g, k) :: rest => (M1P m hm).smul (gen m hm g) (-(k : ℤ)) (iwVal rest)

/-- The kernel-checkable well-formedness condition. -/
def iwOK : List (Bool × ℕ) → Bool
  | [] => true
  | (_, k) :: rest => decide (1 ≤ k) && (iwPoly rest).all (fun t => wWt t.2 == iwWt rest) && iwOK rest

theorem iw_spec : ∀ l : List (Bool × ℕ), iwOK l = true →
    IsIterProd (M1P m hm) (gensM m hm) (iwVal m hm l) ∧ HasPoly m hm (iwVal m hm l) (iwPoly l)
  | [], _ => ⟨IsIterProd.vacuum, hasPoly_vacuum m hm⟩
  | (g, k) :: rest, h => by
    simp only [iwOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hk, hw⟩, hrest⟩ := h
    obtain ⟨h1, h2⟩ := iw_spec rest hrest
    refine ⟨IsIterProd.step _ (gen_mem m hm g) (k : ℤ) (by exact_mod_cast hk) _ h1, ?_⟩
    refine hasPoly_normR m hm ?_
    have := M1P_smul_poly m hm (hasPoly_gen m hm g) h2 (iwWt rest) hw (-(k : ℤ))
    simpa using this

theorem iw_mem (l : List (Bool × ℕ)) (h : iwOK l = true) : iwVal m hm l ∈ TM m hm :=
  Submodule.subset_span (iw_spec m hm l h).1

/-- A certificate `y = Σ cᵢ·(word i)` puts `y ∈ T`. -/
theorem mem_TM_of_cert {y : (m1Sub m hm).carrier} {A : RawPoly ℕ} (hy : HasPoly m hm y A)
    (cert : List (ℚ × List (Bool × ℕ))) (hok : cert.all (fun t => iwOK t.2) = true)
    (h : normR A = normR (lc (cert.map fun t => (t.1, iwPoly t.2)))) : y ∈ TM m hm := by
  refine mem_of_cert m hm _ hy _ ?_ h
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  rw [List.all_eq_true] at hok
  exact ⟨_, iw_mem m hm s.2 (hok s hs), (iw_spec m hm s.2 (hok s hs)).2⟩

/-! ## §2  The table -/

/-- `ω₍ⱼ₎W` for `2 ≤ j ≤ 5`: `L(1)W = 0`, `L(2)W = 24ω`, `L(3)W = L(4)W = 0`. -/
def omWcert : ℕ → List (ℚ × List (Bool × ℕ))
  | 3 => [(24, [(true, 1)])]
  | _ => []

theorem omW_cert (j : ℕ) (hj : 2 ≤ j ∧ j ≤ 5) :
    normR (polyAct omR (-(j : ℤ) - 1) 4 WR) = normR (lc ((omWcert j).map fun t => (t.1, iwPoly t.2))) ∧
      (omWcert j).all (fun t => iwOK t.2) = true := by
  obtain ⟨h1, h2⟩ := hj
  interval_cases j <;> decide +kernel

/-- The `(W, W)` table, `W₍ⱼ₎W` for `0 ≤ j ≤ 7`. -/
def WWcert : ℕ → List (ℚ × List (Bool × ℕ))
  | 0 => [(-576, [(true, 4), (true, 1)]), (288, [(true, 3), (true, 2)]), (48, [(true, 2), (false, 1)]),
          (48, [(true, 1), (false, 2)]), (-12, [(false, 4)])]
  | 1 => [(-384, [(true, 3), (true, 1)]), (240, [(true, 2), (true, 2)]), (96, [(true, 1), (false, 1)]),
          (28, [(false, 3)])]
  | 2 => [(192, [(true, 4)]), (108, [(false, 2)])]
  | 3 => [(288, [(true, 3)]), (216, [(false, 1)])]
  | 4 => [(480, [(true, 2)])]
  | 5 => [(960, [(true, 1)])]
  | 7 => [(120, [])]
  | _ => []

theorem WW_cert (j : ℕ) (hj : j ≤ 7) :
    normR (polyAct WR (-(j : ℤ) - 1) 4 WR) = normR (lc ((WWcert j).map fun t => (t.1, iwPoly t.2))) ∧
      (WWcert j).all (fun t => iwOK t.2) = true := by
  interval_cases j <;> decide +kernel

theorem ωM_mem_gensM : ωM m hm ∈ gensM m hm := Or.inl rfl
theorem WM_mem_gensM : WM m hm ∈ gensM m hm := Or.inr rfl

theorem omW_mem (j : ℤ) (hj : 0 ≤ j) : (M1P m hm).smul (ωM m hm) j (WM m hm) ∈ TM m hm := by
  have hWT : WM m hm ∈ TM m hm := by
    have := Submodule.subset_span (R := ℂ) (IsIterProd.step (W := M1P m hm) _ (WM_mem_gensM m hm) 1
      le_rfl _ IsIterProd.vacuum)
    rwa [show (-(1 : ℤ)) = -1 from rfl, (M1P m hm).smul_vacuum_neg_one] at this
  rcases (show j = 0 ∨ j = 1 ∨ (2 ≤ j ∧ j ≤ 5) ∨ 6 ≤ j by omega) with rfl | rfl | ⟨h2, h5⟩ | h6
  · exact conformal_smul_zero_mem_iterProdSpan _ _ hWT
  · exact conformal_smul_one_mem_iterProdSpan _ _ (gensM_homog m hm) hWT
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k := ⟨j.toNat, by omega⟩
    obtain ⟨hc, hok⟩ := omW_cert k ⟨by omega, by omega⟩
    have hy := M1P_smul_poly m hm (hasPoly_omega m hm) (hasPoly_W m hm) 4 (by decide) (k : ℤ)
    exact mem_TM_of_cert m hm hy _ hok hc
  · rw [smul_grading_neg_eq_zero (M1P m hm) (ωM_mem_grading m hm) (WM_mem_grading m hm) (by omega)]
    exact Submodule.zero_mem _

theorem WW_mem (j : ℤ) (hj : 0 ≤ j) : (M1P m hm).smul (WM m hm) j (WM m hm) ∈ TM m hm := by
  rcases (show j ≤ 7 ∨ 8 ≤ j by omega) with h7 | h8
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k := ⟨j.toNat, by omega⟩
    obtain ⟨hc, hok⟩ := WW_cert k (by omega)
    have hy := M1P_smul_poly m hm (hasPoly_W m hm) (hasPoly_W m hm) 4 (by decide) (k : ℤ)
    exact mem_TM_of_cert m hm hy _ hok hc
  · rw [smul_grading_neg_eq_zero (M1P m hm) (WM_mem_grading m hm) (WM_mem_grading m hm) (by omega)]
    exact Submodule.zero_mem _

/-- **The generator OPE table closes.** -/
theorem pair_closed : ∀ s ∈ gensM m hm, ∀ t ∈ gensM m hm, ∀ j : ℤ, 0 ≤ j →
    (M1P m hm).smul s j t ∈ TM m hm := by
  rintro s (rfl | rfl) t (rfl | rfl) j hj
  · exact conformal_smul_conformal_mem_iterProdSpan _ _ (ωM_mem_gensM m hm) j hj
  · exact omW_mem m hm j hj
  · exact smul_mem_iterProdSpan_of_skew _ _ _ _ j fun k hk => omW_mem m hm k (by omega)
  · exact WW_mem m hm j hj

/-- **`T` is closed under all products.** -/
theorem T_smul_closed {u v : (m1Sub m hm).carrier} (hu : u ∈ TM m hm) (n : ℤ) (hv : v ∈ TM m hm) :
    (M1P m hm).smul u n v ∈ TM m hm :=
  iterProdSpan_smul_closed _ _ (gensM_homog m hm) (pair_closed m hm) hu n hv

end PlusC2

end VOA.Classification.COne
