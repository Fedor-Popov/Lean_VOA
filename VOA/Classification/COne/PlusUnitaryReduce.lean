/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusUnitaryZhu
import VOA.Classification.COne.PlusC2Final
import VOA.Modularity.LowestWeightExistence

/-!
# Pseudo-unitarity of `V_{2m}⁺` from four facts about a top vector

Let `N` be an irreducible ordinary `V⁺ = V_{2m}⁺`-module with lowest weight `h`, and let
`x ∈ N_h` be an eigenvector of the zero mode of `W = W⁴ = 4h(−1)h(−3) − 3h(−2)²` (orthonormal
boson `h`), with eigenvalue `w`.  Write `E = e^α + e^{−α}` (`⟨α,α⟩ = 2m`).  The four named
statements below are each a TRUE consequence of Dong–Nagatomo's analysis of `A(V_L⁺)`
(Comm. Math. Phys. 202 (1999), §5; J. Algebra 216 (1999) for `M(1)⁺`).  All four are
theorems (`PlusUnitaryM1`, `PlusUnitaryERel`, `PlusUnitaryEE`, `PlusUnitaryVac`; assembled in
`PlusUnitaryFinal.lean`):

* `PlusM1Dichotomy` (**H1**): `w = 2h` or `h ∈ {1/16, 9/16, 1}` — the curve of the modules
  `M(1,λ)` (`h = λ²/2`, `w = λ²`) and the three exceptional `M(1)⁺`-modules
  `M(1)(θ)^±` (`1/16`, `9/16`) and `M(1)⁻` (`1`).
* `PlusERelation` (**H2**): `(h − m/4)(h − 1/16)(h − 9/16)·o(E)x = 0` — the relation
  `(ω − m/4) ∗ (ω − 1/16) ∗ (ω − 9/16) ∗ E ∈ O(V⁺)`.
* `PlusEESquare` (**H3**): if `w = 2h` and `o(E)x = 0` then `4mh = j²` for some `0 ≤ j < m`
  (the eigenvalue of `o(E ∗ E)` on the curve is `c·∏_{j<m}(4mh − j²)`, `c ≠ 0`).
* `PlusVacuumTop` (**H4**): if `h = 0` and `o(W)x = o(E)x = 0` then `N ≅ V⁺`.

## Main results
* `pseudoUnitary_of_tops : PlusM1Dichotomy → PlusERelation → PlusEESquare → PlusVacuumTop →
  PseudoUnitary (V2mPlus m hm)`.
* `v2mPlusPseudoUnitaryFactGe2_of_tops` — the cited fact `V2mPlusPseudoUnitaryFactGe2` from the
  four statements for all `m ≥ 2`.

No classification of the irreducible modules is needed: the argument is a case split on the
top-level eigenvalues.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne.PlusUnitary

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice PlusC2

variable (m : ℕ) (hm : 1 ≤ m)

/-! ## The three generators of `V⁺` used on the top level -/

/-- `W⁴` as an element of `V⁺`. -/
noncomputable def WP : VP m hm := incl m hm (WM m hm)

/-- `E = e^α + e^{−α} ∈ V⁺`. -/
noncomputable def EP : VP m hm := xP m hm ((1 : ℤ) : (latP m).carrier)

/-! ## The four top-level statements -/

/-- **H1** (`M(1)⁺` dichotomy, TRUE: Dong–Nagatomo, J. Algebra 216 (1999), the classification of
irreducible `M(1)⁺`-modules, via the two relations of weights 8 and 10 in `A(M(1)⁺)`). -/
def PlusM1Dichotomy : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2mPlus m hm) M) (h w : ℂ) (x : M),
    IsLowestWeight N h → x ∈ N.weight h → x ≠ 0 → oMod N (WP m hm) x = w • x →
      w = 2 * h ∨ h = 1 / 16 ∨ h = 9 / 16 ∨ h = 1

/-- **H2** (TRUE: Dong–Nagatomo, CMP 202 (1999), §5; the relation
`(ω − m/4) ∗ (ω − 1/16) ∗ (ω − 9/16) ∗ E ∈ O(V⁺)`). -/
def PlusERelation : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2mPlus m hm) M) (h : ℂ) (x : M),
    IsLowestWeight N h → x ∈ N.weight h →
      ((h - (m : ℂ) / 4) * (h - 1 / 16) * (h - 9 / 16)) • oMod N (EP m hm) x = 0

/-- **H3** (TRUE: on the curve `w = 2h`, `o(E∗E)` acts by `c·∏_{j<m}(4mh − j²)` with `c ≠ 0`;
Dong–Nagatomo, CMP 202 (1999), §5). -/
def PlusEESquare : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2mPlus m hm) M) (h : ℂ) (x : M),
    IsLowestWeight N h → x ∈ N.weight h → x ≠ 0 → oMod N (WP m hm) x = (2 * h) • x →
      oMod N (EP m hm) x = 0 → ∃ j : ℕ, j < m ∧ 4 * (m : ℂ) * h = (j : ℂ) ^ 2

/-- **H4** (TRUE: a top vector with the vacuum's eigenvalues generates a copy of `V⁺`). -/
def PlusVacuumTop : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2mPlus m hm) M), N.IsIrreducible →
    ∀ x : M, IsLowestWeight N 0 → x ∈ N.weight 0 → x ≠ 0 → oMod N (WP m hm) x = 0 →
      oMod N (EP m hm) x = 0 → Nonempty (ModuleEquiv (V2mPlus m hm) N (adjointModule (V2mPlus m hm)))

/-! ## Assembly -/

/-- An eigenvector of `o(u)` on a nonzero lowest-weight space. -/
theorem exists_eigen_lowest {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (V2mPlus m hm) M) {h : ℂ} (hne : N.weight h ≠ ⊥) (u : VP m hm) :
    ∃ (w : ℂ) (x : M), x ∈ N.weight h ∧ x ≠ 0 ∧ oMod N u x = w • x := by
  haveI := N.finrank h
  haveI : Nontrivial (N.weight h) := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨w, hw⟩ := Module.End.exists_eigenvalue (rhoLW N h u)
  obtain ⟨y, hy⟩ := hw.exists_hasEigenvector
  refine ⟨w, (y : M), y.2, fun h0 => hy.2 (Subtype.ext h0), ?_⟩
  have := congrArg (fun z : N.weight h => (z : M)) (Module.End.HasEigenvector.apply_eq_smul hy)
  simpa [rhoLW_apply_coe] using this

/-- **Pseudo-unitarity of `V_{2m}⁺` from the four top-level statements.** -/
theorem pseudoUnitary_of_tops (h1 : PlusM1Dichotomy m hm) (h2 : PlusERelation m hm)
    (h3 : PlusEESquare m hm) (h4 : PlusVacuumTop m hm) : PseudoUnitary (V2mPlus m hm) := by
  intro M _ _ N hirr hnot α hα
  obtain ⟨h, hlow, hne⟩ := OrdVModule.exists_isLowestWeight_of_irreducible N hirr
  -- it suffices to show `0 < re h`
  suffices hpos : 0 < h.re by
    obtain ⟨n, rfl⟩ := hlow α hα
    simp only [Complex.add_re, Complex.natCast_re]
    positivity
  obtain ⟨w, x, hx, hx0, hW⟩ := exists_eigen_lowest m hm N hne (WP m hm)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rcases h1 M N h w x hlow hx hx0 hW with hcurve | h16 | h916 | hone
  · by_cases hE : oMod N (EP m hm) x = 0
    · obtain ⟨j, hjm, hj⟩ := h3 M N h x hlow hx hx0 (by rw [hW, hcurve]) hE
      have hh : h = (j : ℂ) ^ 2 / (4 * m) := by
        have : (4 * (m : ℂ)) ≠ 0 := by
          have : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
          exact mul_ne_zero (by norm_num) this
        rw [eq_div_iff this]; linear_combination hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · -- `h = 0`: the vacuum case
        exfalso
        have h0 : h = 0 := by simpa using hh
        subst h0
        obtain ⟨e⟩ := h4 M N hirr x hlow hx hx0 (by rw [hW, hcurve]; simp) hE
        exact hnot.false e
      · rw [hh]
        have : ((j : ℂ) ^ 2 / (4 * m)) = (((j : ℝ) ^ 2 / (4 * m) : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_re]
        have : (0 : ℝ) < j := by exact_mod_cast hj0
        positivity
    · have hrel := h2 M N h x hlow hx
      have hc : (h - (m : ℂ) / 4) * (h - 1 / 16) * (h - 9 / 16) = 0 := by
        by_contra hc; exact hE ((smul_eq_zero.mp hrel).resolve_left hc)
      rcases mul_eq_zero.mp hc with hc | hc
      · rcases mul_eq_zero.mp hc with hc | hc
        · rw [sub_eq_zero.mp hc]
          have : ((m : ℂ) / 4) = (((m : ℝ) / 4 : ℝ) : ℂ) := by push_cast; ring
          rw [this, Complex.ofReal_re]; positivity
        · rw [sub_eq_zero.mp hc]; norm_num
      · rw [sub_eq_zero.mp hc]; norm_num
  · rw [h16]; norm_num
  · rw [h916]; norm_num
  · rw [hone]; norm_num

/-- **The cited fact `V2mPlusPseudoUnitaryFactGe2` from the four top-level statements.** -/
theorem v2mPlusPseudoUnitaryFactGe2_of_tops
    (H : ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
      PlusM1Dichotomy m hm ∧ PlusERelation m hm ∧ PlusEESquare m hm ∧ PlusVacuumTop m hm) :
    V2mPlusPseudoUnitaryFactGe2 := fun m hm hm2 =>
  let ⟨h1, h2, h3, h4⟩ := H m hm hm2
  pseudoUnitary_of_tops m hm h1 h2 h3 h4

end VOA.Classification.COne.PlusUnitary
