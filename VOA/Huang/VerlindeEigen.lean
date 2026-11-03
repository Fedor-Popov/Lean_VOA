/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.VerlindeFusion
import VOA.Huang.BraidingSkewJacobi

/-!
# Huang's §5: the Verlinde package from "S diagonalises the fusion matrices"

Y.-Z. Huang, *Vertex operator algebras and the Verlinde conjecture*, Commun. Contemp. Math. 10
(2008) 103–154 (arXiv:math/0406291), §5, derives everything that
`HuangVerlindeFusionInput` asks for from two facts:

* **Theorem 5.2** (the main theorem): for every `a`, the columns of `S` are eigenvectors of the
  fusion matrix `N(a)`, `N(a)_{xy} = N_{ax}^y` (here `FusionEigen`);
* **Proposition 5.3** (`S² = C`): `ρ(−1)` is the permutation matrix of `a ↦ a'`, together with
  the fusion rule `N_{ab}^{V} = δ_{b,a'}` (FHL), used in the proof of Theorem 5.6.

This file proves that derivation (pure linear algebra over a finite index type), in the
library's convention `χ_x(−1/τ) = Σ_y S_xy χ_y(τ)` (`D.repS`, Huang's `S_{a₁}^{a₂}`, (4.26)):

* `verlinde_of_eigen` — Huang (5.10) and (5.9): the right unit row `N_{a0}^y = δ_ay` and
  `FusionEigen` give `S_ax S_bx = S₀ₓ Σ_c N_ab^c S_cx` (no nonvanishing needed);
* `vacRow_ne_of_eigen` — Huang Theorem 5.5: with `S` invertible, `S₀ₓ ≠ 0`;
* `symm_vac_of_eigen` — the vacuum-row case of Huang Theorem 5.6, via (5.12)–(5.14);
* `huangVerlindeFusionInput_of_inputs :
    FusionEigenInput → ChargeConjugationInput → HuangVerlindeFusionInput`;
* `chargeConjugationInput_of : VacuumFusionInput → RhoNegOneInput → ChargeConjugationInput` and
  `huangVerlindeFusionInput_of_three`.

`FusionEigenInput` (Huang Thm 5.2) and `ChargeConjugationInput` (Huang Prop 5.3 and FHL
Prop 5.5.2 with Prop 5.4.7) are TRUE narrower inputs, not asserted here.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.VerlindeEigen

open VOA VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.VerlindeReduction
  VOA.Huang.VerlindeFusion Matrix

universe u w

/-! ## §1 Pure algebra -/

section Algebra

variable {ι : Type w} [Fintype ι]

/-- **The columns of `S` are common eigenvectors of the fusion matrices** `N(a)_{xy} = N a x y`
(Huang 2008, Theorem 5.2, in the form `N(a) S = S diag(λ_a)`). -/
def FusionEigen (N : ι → ι → ι → ℕ) (S : ι → ι → ℂ) : Prop :=
  ∀ a z, ∃ μ : ℂ, ∀ x, ∑ y, (N a x y : ℂ) * S y z = μ * S x z

/-- The eigenvalue of column `z` of `S` for `N(a)` (a choice). -/
noncomputable def eigval {N : ι → ι → ι → ℕ} {S : ι → ι → ℂ} (hE : FusionEigen N S)
    (a z : ι) : ℂ :=
  Classical.choose (hE a z)

theorem eigval_spec {N : ι → ι → ι → ℕ} {S : ι → ι → ℂ} (hE : FusionEigen N S) (a z x : ι) :
    ∑ y, (N a x y : ℂ) * S y z = eigval hE a z * S x z :=
  Classical.choose_spec (hE a z) x

variable [DecidableEq ι] {N : ι → ι → ι → ℕ} {S : ι → ι → ℂ} {v0 : ι}

/-- Huang (5.10): with the right unit row `N_{a v0}^y = δ_ay`, the eigenvalue is read off the
vacuum row, `S_az = λ_az S_{v0 z}`. -/
theorem eq_eigval_mul (hunit : ∀ a y, N a v0 y = if y = a then 1 else 0)
    (hE : FusionEigen N S) (a z : ι) : S a z = eigval hE a z * S v0 z := by
  have h := eigval_spec hE a z v0
  simp only [hunit, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact h

/-- **The Verlinde identity from the eigenvector property** (Huang (5.9)–(5.11)):
`S_ax S_bx = S₀ₓ Σ_c N_ab^c S_cx`.  No nonvanishing of `S₀ₓ` is needed. -/
theorem verlinde_of_eigen (hunit : ∀ a y, N a v0 y = if y = a then 1 else 0)
    (hE : FusionEigen N S) (a b x : ι) :
    S a x * S b x = S v0 x * ∑ c, (N a b c : ℂ) * S c x := by
  rw [eigval_spec hE a x b, eq_eigval_mul hunit hE a x]
  ring

/-- **Nonvanishing of the vacuum row** (Huang Theorem 5.5): if `S` has a left inverse, then
`S_{v0 z} ≠ 0`, since otherwise column `z` of `S` vanishes. -/
theorem vacRow_ne_of_eigen (hunit : ∀ a y, N a v0 y = if y = a then 1 else 0)
    (hE : FusionEigen N S) (T : Matrix ι ι ℂ) (hT : T * Matrix.of S = 1) (z : ι) :
    S v0 z ≠ 0 := by
  intro h0
  have hcol : ∀ a, S a z = 0 := fun a => by rw [eq_eigval_mul hunit hE a z, h0, mul_zero]
  have h1 := congrFun (congrFun hT z) z
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  simp only [Matrix.of_apply, hcol, mul_zero, Finset.sum_const_zero] at h1
  exact zero_ne_one h1

/-- Huang (5.12): the rows of a two-sided inverse `T` of `S` are left eigenvectors,
`Σ_x T_zx N_ax^y = λ_az T_zy`. -/
theorem inv_eigen (hE : FusionEigen N S) (T : Matrix ι ι ℂ) (hTS : T * Matrix.of S = 1)
    (hST : Matrix.of S * T = 1) (a z y : ι) :
    ∑ x, T z x * (N a x y : ℂ) = eigval hE a z * T z y := by
  classical
  set Na : Matrix ι ι ℂ := Matrix.of fun x y => (N a x y : ℂ) with hNa
  set Λ : Matrix ι ι ℂ := Matrix.diagonal fun z => eigval hE a z with hΛ
  have hNS : Na * Matrix.of S = Matrix.of S * Λ := by
    ext x z'
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    simp only [hNa, Matrix.of_apply]
    rw [eigval_spec hE a z' x, mul_comm]
  have key : T * Na = Λ * T := by
    calc T * Na = T * Na * (Matrix.of S * T) := by rw [hST, Matrix.mul_one]
      _ = T * (Na * Matrix.of S) * T := by simp only [Matrix.mul_assoc]
      _ = T * (Matrix.of S * Λ) * T := by rw [hNS]
      _ = (T * Matrix.of S) * Λ * T := by simp only [Matrix.mul_assoc]
      _ = Λ * T := by rw [hTS, Matrix.one_mul]
  have h := congrFun (congrFun key z) y
  rw [Matrix.mul_apply, Matrix.diagonal_mul] at h
  simpa [hNa] using h

/-- **Symmetry of the vacuum row** (the vacuum case of Huang Theorem 5.6, via (5.12)–(5.14)).
Hypotheses: the right unit row; `N_{ax}^{v0} = δ_{x,σa}` for an injective `σ` fixing `v0`
(the contragredient map); and a two-sided inverse `T = S · P_σ` of `S` (Huang Cor. 5.4). -/
theorem symm_vac_of_eigen (hunit : ∀ a y, N a v0 y = if y = a then 1 else 0)
    (hE : FusionEigen N S) (σ : ι → ι) (hσ : Function.Injective σ) (hσ0 : σ v0 = v0)
    (hdual : ∀ a x, N a x v0 = if x = σ a then 1 else 0)
    (T : Matrix ι ι ℂ) (hTS : T * Matrix.of S = 1) (hST : Matrix.of S * T = 1)
    (hTdef : ∀ w y, T w y = ∑ u, S w u * (if y = σ u then 1 else 0)) (a : ι) :
    S v0 a = S a v0 := by
  have hTrow : ∀ b, T v0 (σ b) = S v0 b := fun b => by
    rw [hTdef, Finset.sum_eq_single b]
    · simp
    · intro u _ hu
      rw [if_neg (fun h => hu (hσ h).symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ b) h
  have h := inv_eigen hE T hTS hST a v0 v0
  simp only [hdual, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  have h00 : T v0 v0 = S v0 v0 := by
    have := hTrow v0; rwa [hσ0] at this
  rw [hTrow a, h00] at h
  rw [h, eq_eigval_mul hunit hE a v0]

end Algebra

/-! ## §2 The two named inputs and the reduction -/

/-- **Huang's main theorem (2008, Theorem 5.2).** For a nice VOA and Zhu's `ρ(S)` on a complete
irredundant family with vacuum label `v0`, every column of `ρ(S)` is a common eigenvector of the
fusion matrices `N(a)_{xy} = famFusion D a x y = N_{ax}^y`.

*Source.* Huang, Commun. Contemp. Math. 10 (2008), Theorem 5.2 (`S` diagonalises `N(a)` for all
`a`), proved there from Cor. 4.7 (the second Moore–Seiberg formula, which uses genus-one
two-point functions) and Prop. 5.1. Huang's standing hypotheses (§1) hold for nice `V`:
pseudo-unitarity gives `W_(0) = 0` for irreducible `W ≇ V`, his stated substitute for `V' ≅ V`.
The fusion rules there are FHL dimensions, i.e. `famFusion`.

*Convention.* `FusionEigen` is a statement about each column separately, so it is invariant under
permuting the columns of `S`; it therefore does not depend on whether Huang's normalisation (4.26)
(with `(−1/τ)^{L(0)}`) and Zhu's (`τⁿ`, used by `ZhuModularityAnalytic`) differ by the charge
conjugation `C`. Also `N_{ax}^y = N_{xa}^y` (`fusionRule_swap`), so the order in `N(a)` is
immaterial. -/
def FusionEigenInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
        FusionEigen (famFusion D) D.repS

/-- **Charge conjugation.** There is a relabelling `σ` (the contragredient map `a ↦ a'`) such that
`ρ(−1)` is its permutation matrix and `N_{ab}^{V} = δ_{b,σa}`.

*Sources.* `ρ(−1) = ρ(S)² = C`: Huang 2008, Prop. 5.3 (from `Z_{M'}(v) = (−1)ⁿ Z_M(v)`, his (2.20),
and uniqueness of `ρ` from linear independence of trace functions, Zhu 1996 / DLM 2000).
`N_{ab}^{V} = δ_{b,a'}`: FHL Prop. 5.5.2 (`I(V / M_a M_b) ≅ I(M_b' / M_a V')`) with `V' ≅ V`,
Prop. 5.4.7 and `N_{V M}^{M''} = δ`; used by Huang in the proof of Theorem 5.6.
`σ` is pinned by the second clause (`σ a` is the unique `b` with `N_{ab}^{V} ≠ 0`). -/
def ChargeConjugationInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
        ∃ σ : ι → ι, (∀ x y, D.rep (-1) x y = if y = σ x then 1 else 0) ∧
          ∀ a b, famFusion D a b v0 = if b = σ a then 1 else 0

/-- `S · S = −1` in `SL₂(ℤ)`. -/
theorem modularS_mul_S : ModularGroup.S * ModularGroup.S = -1 := by
  ext i j
  have h := congrFun (congrFun ModularGroup.S_mul_S_eq i) j
  simpa using h

/-- The right unit row of the family's fusion rules, `N_{a v0}^y = δ_ay` (from the left unit row
`famFusion_vac` and skew-symmetry `fusionRule_swap`). -/
theorem famFusion_vac_right {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VertexOperatorAlgebra 𝒱} {ι : Type w} [Fintype ι] [DecidableEq ι]
    (D : VOA.ModularData W ι) (hirr : Irredundant D.Mfam) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) (a y : ι) :
    famFusion D a v0 y = if y = a then 1 else 0 := by
  have h := famFusion_vac D hirr v0 hv0 a y
  have hs : famFusion D a v0 y = famFusion D v0 a y :=
    BraidingSkew.fusionRule_swap (D.Mfam v0).isMod (D.Mfam a).isMod (D.Mfam y).isMod
  rw [hs, h]
  by_cases hay : a = y
  · subst hay; simp
  · rw [if_neg hay, if_neg (Ne.symm hay)]

/-- **Huang's §5 in Lean**: the eigenvector property and charge conjugation give the full
Verlinde package with the true fusion rules. -/
theorem huangVerlindeFusionInput_of_inputs (hE : FusionEigenInput.{u, w})
    (hC : ChargeConjugationInput.{u, w}) : HuangVerlindeFusionInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0
  have hEig := hE 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  obtain ⟨σ, hP, hdual⟩ := hC 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  have hunit := famFusion_vac_right D hirr v0 hv0
  -- the inverse `T = ρ(S · (−1)) = ρ(S) ρ(−1)`
  set T : Matrix ι ι ℂ := D.rep (ModularGroup.S * -1) with hTdef'
  have hRS : D.rep ModularGroup.S = Matrix.of D.repS := D.rep_S
  have hST : Matrix.of D.repS * T = 1 := by
    rw [← hRS, hTdef', ← map_mul, ← mul_assoc, modularS_mul_S, neg_one_mul, neg_neg, map_one]
  have hTS : T * Matrix.of D.repS = 1 := mul_eq_one_comm.mp hST
  have hTval : ∀ x y, T x y = ∑ u, D.repS x u * (if y = σ u then 1 else 0) := by
    intro x y
    rw [hTdef', map_mul, hRS, Matrix.mul_apply]
    simp only [Matrix.of_apply, hP]
  -- `σ` is an involution, hence injective
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    have h1 : D.rep (-1) * D.rep (-1) = 1 := by
      rw [← map_mul, neg_one_mul, neg_neg, map_one]
    have h2 := congrFun (congrFun h1 x) x
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h2
    simp only [hP] at h2
    rw [Finset.sum_eq_single (σ x)] at h2
    · by_contra hne
      rw [if_pos rfl, if_neg (Ne.symm hne), mul_zero] at h2
      exact zero_ne_one h2
    · intro u _ hu; rw [if_neg hu, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hσinj : Function.Injective σ := fun x y hxy => by
    rw [← hσσ x, hxy, hσσ y]
  have hσ0 : σ v0 = v0 := by
    have h1 := hdual v0 v0
    rw [famFusion_vac D hirr v0 hv0, if_pos rfl] at h1
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h1
    exact one_ne_zero h1
  refine ⟨vacRow_ne_of_eigen hunit hEig T hTS, fun a => ?_, verlinde_of_eigen hunit hEig⟩
  exact symm_vac_of_eigen hunit hEig σ hσinj hσ0 hdual T hTS hST hTval a

/-- **Fusion into the vacuum** (genus zero only): there is a relabelling `σ` with
`N_{ab}^{V} = δ_{b,σa}`.

*Source.* FHL (1993) Prop. 5.5.2 (`I(V / M_a M_b) ≅ I(M_b' / M_a V')`), `V' ≅ V` (for nice `V`:
`V'` is irreducible with `V'_(0) ≠ 0`, so pseudo-unitarity forces `V' ≅ V`), Prop. 5.4.7 and
`N_{V M}^{M''} = δ` (`fusionRule_adjoint_eq`),
`M_a'` irreducible (FHL Prop. 5.3.2) and in the complete family; `σ a` is the label of `M_a'`. -/
def VacuumFusionInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
        ∃ σ : ι → ι, ∀ a b, famFusion D a b v0 = if b = σ a then 1 else 0

/-- **`ρ(−1)` is the charge conjugation** determined by fusion into the vacuum.

*Source.* Huang 2008, Prop. 5.3 (`S² = C`), resting on his (2.20) `Z_{M'}(v) = (−1)ⁿ Z_M(v)`
for `v ∈ V_[n]` and the uniqueness of `ρ` (linear independence of the trace functions of a
complete irredundant family: Zhu 1996, DLM 2000). The `σ` of the hypothesis is forced to be the
contragredient map by `VacuumFusionInput`'s source, so this is the statement `ρ(−1) = C`. -/
def RhoNegOneInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
        ∀ σ : ι → ι, (∀ a b, famFusion D a b v0 = if b = σ a then 1 else 0) →
          ∀ x y, D.rep (-1) x y = if y = σ x then 1 else 0

/-- The two genus-zero / Zhu inputs give `ChargeConjugationInput`. -/
theorem chargeConjugationInput_of (hF : VacuumFusionInput.{u, w}) (hR : RhoNegOneInput.{u, w}) :
    ChargeConjugationInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0
  obtain ⟨σ, hσ⟩ := hF 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  exact ⟨σ, hR 𝒱 W hNice ι D hZ hirr hcomp v0 hv0 σ hσ, hσ⟩

/-- **The headline reduction of V7**: Huang's Theorem 5.2, fusion into the vacuum, and
`ρ(−1) = C` give `HuangVerlindeFusionInput`. -/
theorem huangVerlindeFusionInput_of_three (hE : FusionEigenInput.{u, w})
    (hF : VacuumFusionInput.{u, w}) (hR : RhoNegOneInput.{u, w}) :
    HuangVerlindeFusionInput.{u, w} :=
  huangVerlindeFusionInput_of_inputs hE (chargeConjugationInput_of hF hR)

/-- The weakened Verlinde input from the two named inputs. -/
theorem verlindeInput_of_inputs (hE : FusionEigenInput.{u, w})
    (hC : ChargeConjugationInput.{u, w}) : VerlindeInput.{u, w} :=
  verlindeInput_of_fusion (huangVerlindeFusionInput_of_inputs hE hC)

end VOA.Huang.VerlindeEigen
