/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.AnFiniteDim
import VOA.Modules.ZhuVermaAnArchAnmFull
import VOA.Modules.ZhuVermaAnArchDJCarrier

/-!
# `C_{n+2}`-cofiniteness ⟹ `dim A_{n,0}(𝒱) < ∞`

⚠ **Index caveat.**  `DJPiece W U n = A_{n,0}(𝒱) ⊗_{A(𝒱)} U` uses the
**Dong–Jiang** bimodule `A_{n,0}(𝒱) = 𝒱 ⧸ O_{n,0}^{full}(𝒱)`, whose circle generator is
`anmCirc W n 0 u v = resHom W 0 (n+2) u v` — pole `n+2`.  That is **not** the Frenkel–Zhu `A_n(𝒱)`,
whose circle generator `circ W n` has pole `2n+2`.  So the cofiniteness that `hfin` actually needs
is `C_{n+2}`, not `C_{2n+2}`.  (Both are equally out of reach of `C₂` alone; only the index
differs.)

The absorption is stated once, generically in the residue data `(s, p)` of `resHom`, and both levels
are corollaries.

## Main results

* `smul_negP_mem_of_lower_resHom` — the generic one-step absorption;
* `grading_le_span_sup_Onm_zero`, `span_sup_Onm_zero_eq_top`;
* `finiteDimensional_AnmFull_of_cofinite` — `dim 𝒱/C_{n+2} < ∞ ⟹ dim A_{n,0}(𝒱) < ∞`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators TensorProduct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The generic one-step absorption.**  If the residue `Res_z (1+z)^{wt a + s} z^{-p} Y(a,z)b`
lies in `T`, and `T` contains every grade strictly below `k + q + p − 1`, then the leading mode
`a₍₋ₚ₎b` lies in `T`. -/
theorem smul_negP_mem_of_lower_resHom (W : VertexOperatorAlgebra 𝒱) (s p : ℤ) {k q : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading k) (hb : b ∈ W.grading q)
    (T : Submodule ℂ 𝒱) (hres : resHom W s p a b ∈ T)
    (hT : ∀ m : ℤ, m < k + q + p - 1 → W.grading m ≤ T) :
    W.smul a (-p) b ∈ T := by
  classical
  have hexp := resHom_homogeneous W s p ha b
  obtain ⟨R, hR⟩ : ∃ R : ℕ, (k + s).toNat = R := ⟨_, rfl⟩
  rw [hR, Finset.sum_range_succ'] at hexp
  have htail : ∑ i ∈ Finset.range R,
      cbz (k + s) ((i : ℕ) + 1 : ℕ) • W.smul a (((i + 1 : ℕ) : ℤ) - p) b ∈ T := by
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
    refine hT _ ?_ (cgen_mem_grading W ha hb)
    push_cast
    omega
  have hzero : cbz (k + s) ((0 : ℕ) : ℤ) • W.smul a (((0 : ℕ) : ℤ) - p) b ∈ T := by
    have := Submodule.sub_mem _ hres htail
    rwa [hexp, add_sub_cancel_left] at this
  rw [Nat.cast_zero, cbz_zero, one_smul, show ((0 : ℤ) - p) = -p by ring] at hzero
  exact hzero

/-- **The degree induction for the Dong–Jiang ideal at level `(n, 0)`.** -/
theorem grading_le_span_sup_Onm_zero (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱)
      = Submodule.span ℂ S ⊔ CGen W (-((n : ℤ) + 2))) (N : ℤ) :
    W.grading N ≤ Submodule.span ℂ S ⊔ Onm W n 0 := by
  classical
  set T : Submodule ℂ 𝒱 := Submodule.span ℂ S ⊔ Onm W n 0 with hTdef
  have hOle : Onm W n 0 ≤ T := le_sup_right
  have hO : ∀ u v : 𝒱, anmCirc W n 0 u v ∈ T := fun u v => hOle (anmCirc_mem_Onm W n 0 u v)
  rcases lt_or_ge N 0 with hneg | hnn
  · rw [W.positivity N hneg]; exact bot_le
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = (M : ℤ) := ⟨N.toNat, by omega⟩
  induction M using Nat.strong_induction_on with
  | _ M ihM =>
    have hT : ∀ m : ℤ, m < (M : ℤ) → W.grading m ≤ T := by
      intro m hm
      rcases lt_or_ge m 0 with hm0 | hm0
      · rw [W.positivity m hm0]; exact bot_le
      · obtain ⟨M', rfl⟩ : ∃ M' : ℕ, m = (M' : ℤ) := ⟨m.toNat, by omega⟩
        exact ihM M' (by exact_mod_cast hm) (by exact_mod_cast hm0)
    refine le_trans (grading_le_span_sup_CGen_inf W _ S hShom htop (M : ℤ)) ?_
    refine sup_le le_sup_left ?_
    refine le_trans (CGen_inf_grading_le_span_deg W _ (M : ℤ)) ?_
    rw [Submodule.span_le]
    rintro g ⟨p, q, a, b, ha, hb, hpq, rfl⟩
    have hres : resHom W 0 ((n : ℤ) + 2) a b ∈ T := by
      have h0 := hO a b
      rw [anmCirc] at h0
      simpa using h0
    have habs := smul_negP_mem_of_lower_resHom W 0 ((n : ℤ) + 2) ha hb T hres
      (fun m hm => hT m (by omega))
    exact habs

/-- Span form. -/
theorem span_sup_Onm_zero_eq_top (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱)
      = Submodule.span ℂ S ⊔ CGen W (-((n : ℤ) + 2))) :
    (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ Onm W n 0 := by
  refine le_antisymm ?_ le_top
  rw [← span_homog_eq_top W, Submodule.span_le]
  rintro x ⟨m, hx⟩
  exact grading_le_span_sup_Onm_zero W n S hShom htop m hx

/-- **`C_{n+2}`-cofinite ⟹ `dim A_{n,0}(𝒱) < ∞`**, for the FULL Dong–Jiang ideal — the
finiteness that `DJPiece W U n = A_{n,0}(𝒱) ⊗_{A(𝒱)} U` needs. -/
theorem finiteDimensional_AnmFull_of_cofinite (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (S : Finset 𝒱)
    (hShom : ∀ s ∈ (S : Set 𝒱), IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱)
      = Submodule.span ℂ (S : Set 𝒱) ⊔ CGen W (-((n : ℤ) + 2))) :
    FiniteDimensional ℂ (AnmFull W n 0) ∧ Module.finrank ℂ (AnmFull W n 0) ≤ S.card := by
  refine finiteDimensional_and_finrank_quot_le_of_span_sup S ?_
  refine le_antisymm ?_ le_top
  rw [span_sup_Onm_zero_eq_top W n _ hShom htop]
  exact sup_le_sup_left (Onm_le_OnmFull W n 0) _

/-! ## Onward to `DJPiece` -/

/-- **The level-`n` piece of `M(U)` is finite-dimensional** once `A_{n,0}(𝒱)` and `U` are.
`DJPiece W U n = (A_{n,0}(𝒱) ⊗_ℂ U) ⧸ balancing`, so both hypotheses are exactly what is needed. -/
theorem finiteDimensional_DJPiece {W : VertexOperatorAlgebra 𝒱} (U : AmMod W 0) (n : ℕ)
    (hA : FiniteDimensional ℂ (AnmFull W n 0)) (hU : FiniteDimensional ℂ U.carrier) :
    FiniteDimensional ℂ (DJPiece W U n) := by
  haveI := hA
  haveI := hU
  haveI : FiniteDimensional ℂ (DJCover W U n) :=
    inferInstanceAs (FiniteDimensional ℂ (AnmFull W n 0 ⊗[ℂ] U.carrier))
  infer_instance

end VOA
