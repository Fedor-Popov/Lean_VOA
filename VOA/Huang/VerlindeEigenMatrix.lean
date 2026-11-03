/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.VerlindeVacuumFusion
import VOA.Huang.ModuleC2Main

/-!
# Huang's §4.5–§5.2: the endgame of "S diagonalises the fusion matrices"

Y.-Z. Huang, *Vertex operator algebras and the Verlinde conjecture*, Commun. Contemp. Math. 10
(2008), arXiv:math/0406291. The proof of Theorem 5.2 has an analytic part (Lemma 4.2, the A- and
B-cycle continuations of the genus-one two-point functions `Ψ_x` in the vacuum channel; their
`S`-covariance; Prop. 2.11 independence) and a genus-zero part (Theorem 4.1, the first
Moore–Seiberg formula, whose consequence (4.9) evaluates the B-cycle matrix). This file proves
everything that comes **after** those inputs, as linear algebra:

* `transport_conj` — Huang Prop. 4.5 (`βS = Sα`) on an abstract space of functions: an
  `S`-operator and the two transport operators with `T_B ∘ S = S ∘ T_A`, vacuum-channel vectors
  `Ψ_x` independent modulo an `S`-stable remainder (the other channels), give
  `S·β = diag(Ω)·S` in the row/source convention `S(Ψ_x) = Σ_y S_xy Ψ_y`;
* `beta_eq_of_trace` — (4.24) with (4.9): a B-matrix entry that is a sum over a basis
  `Fin (N …)` of terms each equal to `f` is `f·N`;
* `ne_zero_of_row`, `ne_zero_of_col` — Huang Prop. 5.1 (`f ≠ 0`), from `Ω_{v0} ≠ 0` and
  invertibility of `S`;
* `fusionEigen_of_col`, `fusionEigen_of_row`, `fusionEigen_of_rowT` — Huang Thm 5.2 in the three
  index conventions in which the transport identity can come out (the last one, Huang's literal
  index reading of (4.24), needs `ρ(−1)` central and the FHL symmetry `N_{ay}^x = N_{a x'}^{y'}`);
* `famFusion_atrans_sigma` — that FHL symmetry for the family, from `fusionRule_atrans_eq`;
* `fusionEigenInput_of_transport_rho : HuangTransportInput → RhoNegOneInput →
  FusionEigenInput` and `fusionEigenInput_of_diag : HuangDiagonalInput → FusionEigenInput`.

`HuangTransportInput` (Huang Cor. 4.7, in the convention produced by Prop. 4.5) and
`HuangDiagonalInput` (Huang (5.1)) are TRUE named inputs stated against `D.repS` and `famFusion D`.
They are **not narrower** than `FusionEigenInput` in analytic content: they are Huang's own
intermediate statements, isolated so that the genus-one (Lemma 4.2, `S`-covariance) and genus-zero
(Theorem 4.1) inputs can be attacked separately.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.VerlindeEigenMatrix

open VOA VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.VerlindeReduction
  VOA.Huang.VerlindeFusion VOA.Huang.VerlindeEigen VOA.Huang.VerlindeVacuum Matrix

universe u w v

/-! ## §1 Huang Prop. 4.5 on an abstract space of functions -/

section Transport

variable {ι : Type w} [Fintype ι] {K : Type v} [AddCommGroup K] [Module ℂ K]

/-- **Huang Prop. 4.5, abstractly.** `K` is a space of (two-point) functions, `R ≤ K` the span of
the non-vacuum channels (`S`-stable: channelwise one-point `S`-closure), `Ψ x` the vacuum-channel
functions, independent modulo `R` (Huang Prop. 2.11). If `S(Ψ_x) = Σ_y S_xy Ψ_y`, the A-transport
is `Ω_x` on `Ψ_x` modulo `R`, the B-transport has vacuum-channel matrix `β`, and `T_B ∘ S = S ∘ T_A`
on the `Ψ_x` (the rescaling `z ↦ z/τ` maps the B-cycle at `τ` to the A-cycle at `−1/τ`), then
`S·β = diag(Ω)·S`. -/
theorem transport_conj (R : Submodule ℂ K) (Sop tA tB : K →ₗ[ℂ] K) (Ψ : ι → K)
    (S β : ι → ι → ℂ) (Ω : ι → ℂ)
    (hSR : ∀ r ∈ R, Sop r ∈ R)
    (hS : ∀ x, Sop (Ψ x) = ∑ y, S x y • Ψ y)
    (hcomm : ∀ x, tB (Sop (Ψ x)) = Sop (tA (Ψ x)))
    (hA : ∀ x, tA (Ψ x) - Ω x • Ψ x ∈ R)
    (hB : ∀ x, tB (Ψ x) - ∑ z, β x z • Ψ z ∈ R)
    (hind : ∀ c : ι → ℂ, ∑ z, c z • Ψ z ∈ R → c = 0) (x z : ι) :
    ∑ y, S x y * β y z = Ω x * S x z := by
  have hA1 : tB (Sop (Ψ x)) - ∑ z, (∑ y, S x y * β y z) • Ψ z ∈ R := by
    have heq : tB (Sop (Ψ x)) - ∑ z, (∑ y, S x y * β y z) • Ψ z
        = ∑ y, S x y • (tB (Ψ y) - ∑ z, β y z • Ψ z) := by
      rw [hS, map_sum]
      simp only [map_smul, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul,
        Finset.sum_smul]
      rw [Finset.sum_comm (f := fun z y => (S x y * β y z) • Ψ z)]
    rw [heq]
    exact R.sum_mem (fun y _ => R.smul_mem _ (hB y))
  have hA2 : Sop (tA (Ψ x)) - ∑ z, (Ω x * S x z) • Ψ z ∈ R := by
    have heq : Sop (tA (Ψ x)) - ∑ z, (Ω x * S x z) • Ψ z = Sop (tA (Ψ x) - Ω x • Ψ x) := by
      rw [map_sub, map_smul, hS, Finset.smul_sum]
      simp only [smul_smul]
    rw [heq]
    exact hSR _ (hA x)
  have hdiff : ∑ z, (fun z => ∑ y, S x y * β y z - Ω x * S x z) z • Ψ z ∈ R := by
    have heq : ∑ z, (fun z => ∑ y, S x y * β y z - Ω x * S x z) z • Ψ z
        = (Sop (tA (Ψ x)) - ∑ z, (Ω x * S x z) • Ψ z)
          - (tB (Sop (Ψ x)) - ∑ z, (∑ y, S x y * β y z) • Ψ z) := by
      rw [hcomm x]
      simp only [sub_smul, Finset.sum_sub_distrib]
      abel
    rw [heq]
    exact R.sub_mem hA2 hA1
  have h0 := congrFun (hind _ hdiff) z
  simp only [Pi.zero_apply] at h0
  exact sub_eq_zero.mp h0

end Transport

/-! ## §2 (4.24) with (4.9): the B-matrix is `f · N` -/

section Trace

variable {ι : Type w}

/-- Huang (4.24) + (4.9): if each B-matrix entry is a sum over a basis `Fin (N x z)` (the
multiplicity space of the fusion rule) of a term `Σ_k F_{ik} G_{ik}` which (4.9) evaluates to the
same `f` for every basis vector `i`, then the entry is `f · N x z`. -/
theorem beta_eq_of_trace {N : ι → ι → ℕ} {K : ι → ι → Type v} [∀ x z, Fintype (K x z)]
    (F G : ∀ x z, Fin (N x z) → K x z → ℂ) (f : ℂ)
    (h49 : ∀ x z i, ∑ k, F x z i k * G x z i k = f) (β : ι → ι → ℂ)
    (h424 : ∀ x z, β x z = ∑ i, ∑ k, F x z i k * G x z i k) (x z : ι) :
    β x z = f * N x z := by
  rw [h424]
  simp only [h49, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Trace

/-! ## §3 Prop. 5.1 and Thm 5.2 as linear algebra -/

section Eigen

variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- **Huang Prop. 5.1, row form.** If `S·L = diag(Ω)·S` with `L = f·N` and `Ω_{v0} ≠ 0`, and `S`
has a right inverse, then `f ≠ 0` (otherwise row `v0` of `S` vanishes). -/
theorem ne_zero_of_row {S : ι → ι → ℂ} {Ω : ι → ℂ} {f : ℂ} {L : ι → ι → ℂ} {v0 : ι}
    (hrow : ∀ x z, ∑ y, S x y * (f * L y z) = Ω x * S x z) (hΩ : Ω v0 ≠ 0)
    (T : Matrix ι ι ℂ) (hST : Matrix.of S * T = 1) : f ≠ 0 := by
  intro hf
  have hzero : ∀ z, S v0 z = 0 := fun z => by
    have h := hrow v0 z
    simp only [hf, zero_mul, mul_zero, Finset.sum_const_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hΩ
  have h1 := congrFun (congrFun hST v0) v0
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  simp only [Matrix.of_apply, hzero, zero_mul, Finset.sum_const_zero] at h1
  exact zero_ne_one h1

/-- **Huang Prop. 5.1, column form.** If `f·N·S = S·diag(Ω)` with `Ω_{v0} ≠ 0`, and `S` has a left
inverse, then `f ≠ 0`. -/
theorem ne_zero_of_col {S : ι → ι → ℂ} {Ω : ι → ℂ} {f : ℂ} {L : ι → ι → ℂ} {v0 : ι}
    (hcol : ∀ x z, ∑ y, (f * L x y) * S y z = S x z * Ω z) (hΩ : Ω v0 ≠ 0)
    (T : Matrix ι ι ℂ) (hTS : T * Matrix.of S = 1) : f ≠ 0 := by
  intro hf
  have hzero : ∀ x, S x v0 = 0 := fun x => by
    have h := hcol x v0
    simp only [hf, zero_mul, Finset.sum_const_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hΩ
  have h1 := congrFun (congrFun hTS v0) v0
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  simp only [Matrix.of_apply, hzero, mul_zero, Finset.sum_const_zero] at h1
  exact zero_ne_one h1

/-- **Huang Thm 5.2, column form** ((5.1)): `f·N(a)·S = S·diag(Ω)` with `Ω_{v0} ≠ 0` and `S`
invertible gives the eigenvector property with eigenvalues `Ω_z / f`. -/
theorem fusionEigen_of_col {N : ι → ι → ι → ℕ} {S : ι → ι → ℂ} {v0 : ι}
    (T : Matrix ι ι ℂ) (hTS : T * Matrix.of S = 1)
    (h : ∀ a, ∃ (Ω : ι → ℂ) (f : ℂ), Ω v0 ≠ 0 ∧
      ∀ x z, ∑ y, (f * (N a x y : ℂ)) * S y z = S x z * Ω z) :
    FusionEigen N S := by
  intro a z
  obtain ⟨Ω, f, hΩ, hcol⟩ := h a
  have hf := ne_zero_of_col hcol hΩ T hTS
  refine ⟨Ω z / f, fun x => ?_⟩
  have hx := hcol x z
  simp only [mul_assoc, ← Finset.mul_sum] at hx
  field_simp
  linear_combination hx

/-- The column-eigen identity `L·T = T·diag(Ω)` obtained from the row identity
`S·L = diag(Ω)·S` and a two-sided inverse `T`. -/
theorem col_of_row {S : ι → ι → ℂ} {Ω : ι → ℂ} {L : ι → ι → ℂ}
    (hrow : ∀ x z, ∑ y, S x y * L y z = Ω x * S x z)
    (T : Matrix ι ι ℂ) (hTS : T * Matrix.of S = 1) (hST : Matrix.of S * T = 1) (x w : ι) :
    ∑ y, L x y * T y w = T x w * Ω w := by
  set Lm : Matrix ι ι ℂ := Matrix.of L with hLm
  have hSL : Matrix.of S * Lm = Matrix.diagonal Ω * Matrix.of S := by
    ext x' z'
    rw [Matrix.mul_apply, Matrix.diagonal_mul]
    simp only [hLm, Matrix.of_apply]
    exact hrow x' z'
  have key : Lm * T = T * Matrix.diagonal Ω := by
    calc Lm * T = (T * Matrix.of S) * Lm * T := by rw [hTS, Matrix.one_mul]
      _ = T * (Matrix.of S * Lm) * T := by simp only [Matrix.mul_assoc]
      _ = T * (Matrix.diagonal Ω * Matrix.of S) * T := by rw [hSL]
      _ = T * Matrix.diagonal Ω * (Matrix.of S * T) := by simp only [Matrix.mul_assoc]
      _ = T * Matrix.diagonal Ω := by rw [hST, Matrix.mul_one]
  have h := congrFun (congrFun key x) w
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
  simpa [hLm] using h

/-- **Huang Thm 5.2, row form** (the convention of Prop. 4.5, `S·β = diag(Ω)·S`, with
`β_yz = f·N_{ay}^z`). With `T = S·P_σ` a two-sided inverse (charge conjugation) the columns of
`S` are eigenvectors of `N(a)`. -/
theorem fusionEigen_of_row {N : ι → ι → ι → ℕ} {S : ι → ι → ℂ} {v0 : ι} (σ : ι → ι)
    (T : Matrix ι ι ℂ) (hTS : T * Matrix.of S = 1) (hST : Matrix.of S * T = 1)
    (hT : ∀ y z, T y (σ z) = S y z)
    (h : ∀ a, ∃ (Ω : ι → ℂ) (f : ℂ), Ω v0 ≠ 0 ∧
      ∀ x z, ∑ y, S x y * (f * (N a y z : ℂ)) = Ω x * S x z) :
    FusionEigen N S := by
  intro a z
  obtain ⟨Ω, f, hΩ, hrow⟩ := h a
  have hf := ne_zero_of_row hrow hΩ T hST
  refine ⟨Ω (σ z) / f, fun x => ?_⟩
  have hx := col_of_row hrow T hTS hST x (σ z)
  simp only [hT, mul_assoc, ← Finset.mul_sum] at hx
  field_simp
  linear_combination hx

/-- **Huang Thm 5.2, transposed row form** (Huang's literal index reading of (4.24):
`β_yz = f·N_{az}^y`). Needs `T = S·P_σ`, the symmetry `S_{σx,σz} = S_{xz}` (i.e. `ρ(−1)` commutes
with `ρ(S)`), `σ` bijective, and the FHL symmetry `N_{ay}^x = N_{a,σx}^{σy}`. -/
theorem fusionEigen_of_rowT {N : ι → ι → ι → ℕ} {S : ι → ι → ℂ} {v0 : ι} (σ : ι → ι)
    (hσ : Function.Bijective σ)
    (T : Matrix ι ι ℂ) (hTS : T * Matrix.of S = 1) (hST : Matrix.of S * T = 1)
    (hT : ∀ y z, T y (σ z) = S y z) (hSσ : ∀ x z, S (σ x) (σ z) = S x z)
    (hsym : ∀ a x y, N a y x = N a (σ x) (σ y))
    (h : ∀ a, ∃ (Ω : ι → ℂ) (f : ℂ), Ω v0 ≠ 0 ∧
      ∀ x z, ∑ y, S x y * (f * (N a z y : ℂ)) = Ω x * S x z) :
    FusionEigen N S := by
  intro a z
  obtain ⟨Ω, f, hΩ, hrow⟩ := h a
  have hf := ne_zero_of_row hrow hΩ T hST
  refine ⟨Ω (σ (σ z)) / f, fun x => ?_⟩
  -- the transposed column identity at the permuted row and column
  have hx := col_of_row hrow T hTS hST (σ x) (σ (σ z))
  simp only [hT, mul_assoc, ← Finset.mul_sum] at hx
  -- reindex the left side by `y ↦ σ y`
  have hre : ∑ y, (N a y (σ x) : ℂ) * S y (σ z)
      = ∑ y, (N a x y : ℂ) * S y z := by
    rw [← Equiv.sum_comp (Equiv.ofBijective σ hσ)]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp only [Equiv.ofBijective_apply]
    rw [hSσ, ← hsym a y x]
  rw [hre, hSσ] at hx
  field_simp
  linear_combination hx

/-- **Huang §4.5–§5.2 in one statement (abstract endgame).** For each `a`: a space `K a` of
two-point functions with an `S`-operator, A- and B-transports and an `S`-stable remainder `R a`;
vacuum-channel functions `Ψ a x` independent modulo `R a` and `S`-covariant with matrix `S`
(the "clearly" before Huang Thm 4.6); A-eigenvalues `Ω a` with `Ω a v0 ≠ 0` ((4.18), (4.23));
B-matrix entries given by the trace form (4.24) over `Fin (N a z x)`, each term evaluated to
`f a` by (4.9). With `T = S·P_σ`, `ρ(−1)` central and the FHL symmetry, `S` diagonalises `N(a)`. -/
theorem fusionEigen_of_transport_data {N : ι → ι → ι → ℕ} {S : ι → ι → ℂ} {v0 : ι}
    (σ : ι → ι) (hσ : Function.Bijective σ)
    (T : Matrix ι ι ℂ) (hTS : T * Matrix.of S = 1) (hST : Matrix.of S * T = 1)
    (hT : ∀ y z, T y (σ z) = S y z) (hSσ : ∀ x z, S (σ x) (σ z) = S x z)
    (hsym : ∀ a x y, N a y x = N a (σ x) (σ y))
    (K : ι → Type v) [∀ a, AddCommGroup (K a)] [∀ a, Module ℂ (K a)]
    (R : ∀ a, Submodule ℂ (K a)) (Sop tA tB : ∀ a, K a →ₗ[ℂ] K a) (Ψ : ∀ a, ι → K a)
    (Ω : ι → ι → ℂ) (hΩ : ∀ a, Ω a v0 ≠ 0) (f : ι → ℂ)
    (Kb : ι → ι → ι → Type v) [∀ a x z, Fintype (Kb a x z)]
    (F G : ∀ a x z, Fin (N a z x) → Kb a x z → ℂ)
    (hSR : ∀ a, ∀ r ∈ R a, Sop a r ∈ R a)
    (hS : ∀ a x, Sop a (Ψ a x) = ∑ y, S x y • Ψ a y)
    (hcomm : ∀ a x, tB a (Sop a (Ψ a x)) = Sop a (tA a (Ψ a x)))
    (hA : ∀ a x, tA a (Ψ a x) - Ω a x • Ψ a x ∈ R a)
    (hB : ∀ a x, tB a (Ψ a x)
      - ∑ z, (∑ i, ∑ k, F a x z i k * G a x z i k) • Ψ a z ∈ R a)
    (h49 : ∀ a x z i, ∑ k, F a x z i k * G a x z i k = f a)
    (hind : ∀ a, ∀ c : ι → ℂ, ∑ z, c z • Ψ a z ∈ R a → c = 0) :
    FusionEigen N S := by
  refine fusionEigen_of_rowT (v0 := v0) σ hσ T hTS hST hT hSσ hsym (fun a => ⟨Ω a, f a, hΩ a,
    fun x z => ?_⟩)
  have h := transport_conj (R a) (Sop a) (tA a) (tB a) (Ψ a) S
    (fun x z => ∑ i, ∑ k, F a x z i k * G a x z i k) (Ω a) (hSR a) (hS a) (hcomm a) (hA a)
    (hB a) (hind a) x z
  rw [← h]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [beta_eq_of_trace (N := fun x z => N a z x) (F a) (G a) (f a) (h49 a) _ (fun _ _ => rfl) y z]

end Eigen

/-! ## §4 The FHL symmetry `N_{ay}^x = N_{a x'}^{y'}` for the family -/

section FHL

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)

/-- **FHL Prop. 5.5.2 for the family**: if `M_x' ≅ M_{σx}` and `M_y' ≅ M_{σy}`, then
`N_{ay}^x = N_{a,σx}^{σy}`. -/
theorem famFusion_atrans_sigma (hV : Nice W) (σ : ι → ι)
    (hσ : ∀ b, Nonempty (ModuleEquiv W (contragredientModule (D.Mfam b).isMod)
      (D.Mfam (σ b)).isMod)) (a x y : ι) :
    famFusion D a y x = famFusion D a (σ x) (σ y) := by
  obtain ⟨ex⟩ := hσ x
  obtain ⟨ey⟩ := hσ y
  let E : intertwiningSpace (D.Mfam a).isMod (contragredientModule (D.Mfam x).isMod)
        (contragredientModule (D.Mfam y).isMod) ≃ₗ[ℂ]
      intertwiningSpace (D.Mfam a).isMod (D.Mfam (σ x)).isMod (D.Mfam (σ y)).isMod :=
    (intertwiningEquivRight ey).trans (intertwiningEquivMid ex)
  haveI : FiniteDimensional ℂ
      (intertwiningSpace (D.Mfam a).isMod (D.Mfam (σ x)).isMod (D.Mfam (σ y)).isMod) :=
    VOA.Huang.ModuleC2.finiteDimensional_fusion_of_nice hV D a (σ x) (σ y)
  haveI : FiniteDimensional ℂ (intertwiningSpace (D.Mfam a).isMod
      (contragredientModule (D.Mfam x).isMod) (contragredientModule (D.Mfam y).isMod)) :=
    LinearEquiv.finiteDimensional E.symm
  unfold famFusion
  rw [VOA.Huang.ATransform.fusionRule_atrans_eq (D.Mfam a).isMod (D.Mfam y).isMod
    (D.Mfam x).isMod]
  exact E.finrank_eq

/-- The contragredient relabelling read off from fusion into the vacuum: if
`N_{ab}^{v0} = δ_{b,σa}` then `M_{σa} ≅ M_a'`. -/
theorem contra_equiv_of_vacuum (hV : Nice W) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) (σ : ι → ι)
    (hdual : ∀ a b, famFusion D a b v0 = if b = σ a then 1 else 0) (a : ι) :
    Nonempty (ModuleEquiv W (contragredientModule (D.Mfam a).isMod) (D.Mfam (σ a)).isMod) := by
  classical
  have hle := famFusion_vacuum_le D hV v0 hv0 a (σ a)
  rw [hdual a (σ a), if_pos rfl] at hle
  by_contra hne
  have hne' : ¬ Nonempty (ModuleEquiv W (D.Mfam (σ a)).isMod
      (contragredientModule (D.Mfam a).isMod)) := fun ⟨e⟩ => hne ⟨e.symm⟩
  rw [if_neg hne'] at hle
  omega

end FHL

/-! ## §5 The named inputs and the reductions -/

/-- **Huang Cor. 4.7 in the convention of Prop. 4.5** (`S(Ψ_x) = Σ_y S_xy Ψ_y`,
`β(Ψ_x) = Σ_z β_xz Ψ_z`, `S·β = diag(Ω)·S`), with Huang's index reading of (4.24):
`β_xz = f·N_{az}^x`. Here `Ω_x` is the A-cycle eigenvalue on `Ψ_x` (Huang (4.23), up to the common
factor `e^{−2πih_a}`), with `Ω_{v0} ≠ 0` (`(B^{(−1)})²` is `1` on the vacuum channel), and `f` is
`F(Y^a_{ae} ⊗ Y^e_{a'a}; Y^a_{ea} ⊗ Y^e_{aa'})` times that factor.

*Source.* Huang, Commun. Contemp. Math. 10 (2008), Prop. 4.5, Cor. 4.4 and Thm 4.1 ((4.9)),
i.e. Cor. 4.7 transcribed without inverting `S`. Analytic inputs: Lemma 4.2 (genus-one two-point
product and iterate convergence, continuation along the A- and B-cycles), Prop. 2.11, the
`S`-covariance of `Ψ_x`; genus-zero input: three-intertwiner associativity for Thm 4.1. TRUE, of the
same strength as `FusionEigenInput` (not narrower). -/
def HuangTransportInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
        ∀ a : ι, ∃ (Ω : ι → ℂ) (f : ℂ), Ω v0 ≠ 0 ∧
          ∀ x z, ∑ y, D.repS x y * (f * (famFusion D a z y : ℂ)) = Ω x * D.repS x z

/-- **Huang (5.1)**: `f·N(a)·S = S·diag(Ω)` with `Ω_{v0} ≠ 0`.

*Source.* Huang 2008, Thm 5.2 in the form (5.1) (there `Ω_x = (B^{(−1)})²(…)` and
`f = F(…)`, nonzero by Prop. 5.1). TRUE, of the same strength as `FusionEigenInput`. -/
def HuangDiagonalInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
        ∀ a : ι, ∃ (Ω : ι → ℂ) (f : ℂ), Ω v0 ≠ 0 ∧
          ∀ x z, ∑ y, (f * (famFusion D a x y : ℂ)) * D.repS y z = D.repS x z * Ω z

/-- `(5.1) ⟹ Thm 5.2` (Prop. 5.1 included), with `S⁻¹ = ρ(S⁻¹)`. -/
theorem fusionEigenInput_of_diag (h : HuangDiagonalInput.{u, w}) : FusionEigenInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0
  have hRS : D.rep ModularGroup.S = Matrix.of D.repS := D.rep_S
  have hTS : D.rep ModularGroup.S⁻¹ * Matrix.of D.repS = 1 := by
    rw [← hRS, ← map_mul, inv_mul_cancel, map_one]
  exact fusionEigen_of_col (v0 := v0) _ hTS (h 𝒱 W hNice ι D hZ hirr hcomp v0 hv0)

/-- **Huang's endgame, transport form**: Cor. 4.7 in the Prop. 4.5 convention and
`ρ(−1) = C` give Thm 5.2. Uses the proved fusion into the vacuum (`vacuumFusionInput`), the FHL
symmetry (`famFusion_atrans_sigma`), and centrality of `ρ(−1)`. -/
theorem fusionEigenInput_of_transport_rho (hT : HuangTransportInput.{u, w})
    (hR : RhoNegOneInput.{u, w}) : FusionEigenInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0
  obtain ⟨σ, hP, hdual⟩ :=
    chargeConjugationInput_of_rhoNegOne hR 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
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
  -- `σ` is an involution
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
  have hσinj : Function.Injective σ := fun x y hxy => by rw [← hσσ x, hxy, hσσ y]
  have hσbij : Function.Bijective σ := ⟨hσinj, fun x => ⟨σ x, hσσ x⟩⟩
  have hTσ : ∀ y z, T y (σ z) = D.repS y z := by
    intro y z
    rw [hTval, Finset.sum_eq_single z]
    · simp
    · intro u _ hu
      rw [if_neg (fun h => hu (hσinj h).symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ z) h
  -- `ρ(−1)` is central: `S_{σx,σz} = S_{xz}`
  have hSσ : ∀ x z, D.repS (σ x) (σ z) = D.repS x z := by
    intro x z
    have hc : D.rep (-1) * D.rep ModularGroup.S = D.rep ModularGroup.S * D.rep (-1) := by
      rw [← map_mul, ← map_mul, neg_one_mul, mul_neg_one]
    have h := congrFun (congrFun hc x) (σ z)
    rw [Matrix.mul_apply, Matrix.mul_apply, hRS] at h
    simp only [hP, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [h, Finset.sum_eq_single z]
    · simp
    · intro u _ hu
      rw [if_neg (fun h => hu (hσinj h).symm)]
    · intro h; exact absurd (Finset.mem_univ z) h
  have hsym : ∀ a x y, famFusion D a y x = famFusion D a (σ x) (σ y) :=
    famFusion_atrans_sigma D hNice σ (contra_equiv_of_vacuum D hNice v0 hv0 σ hdual)
  exact fusionEigen_of_rowT (v0 := v0) σ hσbij T hTS hST hTσ hSσ hsym
    (hT 𝒱 W hNice ι D hZ hirr hcomp v0 hv0)

/-- **Equal strength, machine-checked**: Thm 5.2 and `ρ(−1) = C` give (5.1) back
(`Ω = λ`, `f = 1`; `λ_{a,v0} ≠ 0` because `S_{a v0} = S_{v0 a} ≠ 0`). So `HuangDiagonalInput` is a
restatement of `FusionEigenInput` (given `RhoNegOneInput`), not a narrowing. -/
theorem huangDiagonalInput_of_eigen_rho (hE : FusionEigenInput.{u, w})
    (hR : RhoNegOneInput.{u, w}) : HuangDiagonalInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0 a
  have hEig := hE 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  obtain ⟨hne, hsymm, -⟩ :=
    huangVerlindeFusionInput_of_eigen_rho hE hR 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  have hunit := famFusion_vac_right D hirr v0 hv0
  refine ⟨fun z => eigval hEig a z, 1, ?_, fun x z => ?_⟩
  · intro h0
    have h := eq_eigval_mul hunit hEig a v0
    simp only at h0
    rw [h0, zero_mul, ← hsymm a] at h
    exact hne a h
  · simp only [one_mul]
    rw [eigval_spec hEig a z x, mul_comm]

/-- The Verlinde package from the transport form of Cor. 4.7 and `ρ(−1) = C`. -/
theorem huangVerlindeFusionInput_of_transport_rho (hT : HuangTransportInput.{u, w})
    (hR : RhoNegOneInput.{u, w}) : HuangVerlindeFusionInput.{u, w} :=
  huangVerlindeFusionInput_of_eigen_rho (fusionEigenInput_of_transport_rho hT hR) hR

/-- The Verlinde package from Huang's (5.1) and `ρ(−1) = C`. -/
theorem huangVerlindeFusionInput_of_diag_rho (hD : HuangDiagonalInput.{u, w})
    (hR : RhoNegOneInput.{u, w}) : HuangVerlindeFusionInput.{u, w} :=
  huangVerlindeFusionInput_of_eigen_rho (fusionEigenInput_of_diag hD) hR

end VOA.Huang.VerlindeEigenMatrix
