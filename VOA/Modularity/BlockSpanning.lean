/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ConvergenceBridge

/-!
# The trace-spanning datum and Zhu's modularity for every `A ∈ SL₂(ℤ)`  (Gannon 5.3.18–5.3.19)

Zhu's Theorem 5.3.8 has two halves.  The **structural** half — that the analytic one-point trace
functions `S_i(v,τ) = 𝒵_{M_i}(v;τ)` span an `SL₂(ℤ)`-stable space (Zhu's genus-one conformal
blocks) and are linearly independent — is the deep input (Zhu Thms 5.3.1–5.3.3, resting on the
recursion, `C₂`-cofiniteness, and the `A(𝒱)`-bijection).  The **representation-theoretic** half —
that the modular matrices are then *forced*, form a representation, have `ρ(T)` diagonal, and
give 5.3.18a for every `A` — is proved here from two named data:

* `TraceSpanning`: for every `A` there is a matrix `ρ_A` with
  `S_i(v, Aτ) = (cτ+d)^{wt[v]}·Σ_j (ρ_A)_{ij} S_j(v,τ)` for all homogeneous `v` (5.3.19: the
  slash-transforms of the trace functions lie in their span);
* `TraceIndependent`: the `S_j` are linearly independent as functions of `(v,τ)`.

Then `ρ_A` is unique (`rho_unique`), `A ↦ ρ_A` is a monoid homomorphism (`modularRepOf`, from
the cocycle `autFactor_mul` and `mul_smul`), `ρ_T` is the diagonal `T`-matrix (`rhoOf_T`,
from `qEvalAt_translate` + `onePoint_T_transform`), so the data assemble into a `ModularData`
(`modularDataOf`) and **`zhu_modularity_of_spanning`** — 5.3.18a for **every** `A`, every
homogeneous `v`, every `τ` — holds.

## Status
Proved, axiom-clean, `pbw`-free, conditional on the two named data.  Residual: producing
`TraceSpanning` and `TraceIndependent` for `C₂`-cofinite rational VOAs (Zhu §5).
-/

namespace VOA

open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The automorphy factor is a cocycle -/

theorem autFactor_eq_denom (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    autFactor A τ = UpperHalfPlane.denom (A : GL (Fin 2) ℝ) τ := by
  rw [autFactor, ModularGroup.denom_apply]

theorem autFactor_ne_zero (A : SL(2, ℤ)) (τ : UpperHalfPlane) : autFactor A τ ≠ 0 := by
  rw [autFactor_eq_denom]
  exact UpperHalfPlane.denom_ne_zero _ _

/-- The coordinate of `A • τ`. -/
theorem coe_SL_smul (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ((A • τ : UpperHalfPlane) : ℂ)
      = (((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (τ : ℂ)
          + ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ)) / autFactor A τ := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, autFactor]
  simp only [eq_intCast, Complex.ofReal_intCast]

/-- **The cocycle** `j(AB, τ) = j(A, Bτ)·j(B, τ)`. -/
theorem autFactor_mul (A B : SL(2, ℤ)) (τ : UpperHalfPlane) :
    autFactor (A * B) τ = autFactor A (B • τ) * autFactor B τ := by
  have hB := autFactor_ne_zero B τ
  rw [autFactor, autFactor, coe_SL_smul, autFactor, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [autFactor] at hB
  push_cast
  field_simp
  ring

@[simp] theorem autFactor_one (τ : UpperHalfPlane) : autFactor 1 τ = 1 := by
  simp [autFactor]

theorem autFactor_neg_one (τ : UpperHalfPlane) : autFactor (-1) τ = -1 := by
  simp [autFactor]

/-! ## The trace functions and the two data -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : VertexOperatorAlgebra 𝒱}

/-- **The analytic one-point trace function** `S_i(v, τ) = 𝒵_{M_i}(v; τ)`, evaluated through
`qEvalAt` along the weight shift `h_i − c/24`. -/
noncomputable def traceFun (Mfam : ι → IrrModule W) (h : ι → ℂ) (i : ι) (v : 𝒱)
    (τ : UpperHalfPlane) : ℂ :=
  qEvalAt (torusOnePoint (Mfam i).isMod v) (h i - W.centralCharge / 24) τ

/-- **Trace spanning (Gannon 5.3.19)**: for every `A ∈ SL₂(ℤ)` some matrix `ρ_A` realises the
weighted transformation law of the trace functions on all homogeneous `v`. -/
def TraceSpanning (Mfam : ι → IrrModule W) (h : ι → ℂ) : Prop :=
  ∀ A : SL(2, ℤ), ∃ ρA : ι → ι → ℂ, ∀ (n : ℕ) (v : 𝒱), v ∈ sqWeightSpace W (n : ℂ) →
    ∀ (i : ι) (τ : UpperHalfPlane),
      traceFun Mfam h i v (A • τ) = autFactor A τ ^ n * ∑ j, ρA i j * traceFun Mfam h j v τ

/-- **Trace independence**: the trace functions are linearly independent as functions of `(v,τ)`
over homogeneous `v`. -/
def TraceIndependent (Mfam : ι → IrrModule W) (h : ι → ℂ) : Prop :=
  ∀ c : ι → ℂ, (∀ (n : ℕ) (v : 𝒱), v ∈ sqWeightSpace W (n : ℂ) → ∀ τ : UpperHalfPlane,
    ∑ j, c j * traceFun Mfam h j v τ = 0) → c = 0

/-- The transformation law at `A` realised by the matrix `ρA`. -/
def RealisesLaw (Mfam : ι → IrrModule W) (h : ι → ℂ) (A : SL(2, ℤ)) (ρA : ι → ι → ℂ) : Prop :=
  ∀ (n : ℕ) (v : 𝒱), v ∈ sqWeightSpace W (n : ℂ) → ∀ (i : ι) (τ : UpperHalfPlane),
    traceFun Mfam h i v (A • τ) = autFactor A τ ^ n * ∑ j, ρA i j * traceFun Mfam h j v τ

variable (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- **Uniqueness of the modular matrix** at each `A`, from independence. -/
theorem rho_unique (hind : TraceIndependent Mfam h) {A : SL(2, ℤ)} {ρ ρ' : ι → ι → ℂ}
    (hρ : RealisesLaw Mfam h A ρ) (hρ' : RealisesLaw Mfam h A ρ') : ρ = ρ' := by
  funext i
  have := hind (fun j => ρ i j - ρ' i j) (fun n v hv τ => ?_)
  · funext j
    have hj := congrFun this j
    simp only [Pi.zero_apply] at hj
    exact sub_eq_zero.mp hj
  · have h1 := hρ n v hv i τ
    have h2 := hρ' n v hv i τ
    have hne : autFactor A τ ^ n ≠ 0 := pow_ne_zero _ (autFactor_ne_zero A τ)
    have hsum : autFactor A τ ^ n * (∑ j, ρ i j * traceFun Mfam h j v τ)
        = autFactor A τ ^ n * (∑ j, ρ' i j * traceFun Mfam h j v τ) := by rw [← h1, ← h2]
    have := mul_left_cancel₀ hne hsum
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun j _ => by ring)

/-- The identity matrix realises the law at `A = 1`. -/
theorem realisesLaw_one : RealisesLaw Mfam h 1 (fun i j => if i = j then 1 else 0) := by
  intro n v _ i τ
  rw [one_smul, autFactor_one, one_pow, one_mul,
    Finset.sum_eq_single i (fun j _ hj => by simp only; rw [if_neg (Ne.symm hj), zero_mul])
      (fun hi => absurd (Finset.mem_univ i) hi)]
  simp

/-- **The product law**: if `ρA` realises `A` and `ρB` realises `B`, then the matrix product
realises `AB` — the cocycle `autFactor_mul` and `mul_smul` do the work. -/
theorem realisesLaw_mul {A B : SL(2, ℤ)} {ρA ρB : ι → ι → ℂ}
    (hA : RealisesLaw Mfam h A ρA) (hB : RealisesLaw Mfam h B ρB) :
    RealisesLaw Mfam h (A * B) (fun i k => ∑ j, ρA i j * ρB j k) := by
  intro n v hv i τ
  rw [mul_smul, hA n v hv i (B • τ), autFactor_mul, mul_pow, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  simp_rw [hB n v hv _ τ]
  have hL : ∀ x, ρA i x * (autFactor B τ ^ n * ∑ j, ρB x j * traceFun Mfam h j v τ)
      = ∑ j, autFactor B τ ^ n * (ρA i x * ρB x j * traceFun Mfam h j v τ) := by
    intro x
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp_rw [hL]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_mul, Finset.mul_sum]

/-- **`T` is realised by the diagonal `T`-matrix**, unconditionally: `qEvalAt_translate` and the
`T`-periodicity `onePoint_T_transform` of every one-point function. -/
theorem realisesLaw_T (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i)) :
    RealisesLaw Mfam h ModularGroup.T (modularRepT W h) := by
  intro n v _ i τ
  rw [autFactor_T, one_pow, one_mul,
    Finset.sum_eq_single i (fun j _ hj => by rw [modularRepT_off_diag W h (Ne.symm hj), zero_mul])
      (fun hi => absurd (Finset.mem_univ i) hi), modularRepT_diag, modularTEntry]
  have hτ : ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [ModularGroup.T]
  rw [traceFun, traceFun, qEvalAt_translate _ _ hτ,
    show torusOnePoint (Mfam i).isMod v = onePoint (Mfam i).isMod v from rfl,
    onePoint_T_transform (Mfam i).isMod v (h i) (hcw i), qEvalAt_smul]

/-! ## Reading off the representation -/

variable (hsp : TraceSpanning Mfam h)

/-- The modular matrix at `A`, chosen from the spanning datum. -/
noncomputable def rhoOf (A : SL(2, ℤ)) : ι → ι → ℂ := Classical.choose (hsp A)

theorem rhoOf_spec (A : SL(2, ℤ)) : RealisesLaw Mfam h A (rhoOf Mfam h hsp A) :=
  Classical.choose_spec (hsp A)

variable (hind : TraceIndependent Mfam h)

include hind in
theorem rhoOf_one : rhoOf Mfam h hsp 1 = fun i j => if i = j then 1 else 0 :=
  rho_unique Mfam h hind (rhoOf_spec Mfam h hsp 1) (realisesLaw_one Mfam h)

include hind in
theorem rhoOf_mul (A B : SL(2, ℤ)) :
    rhoOf Mfam h hsp (A * B) = fun i k => ∑ j, rhoOf Mfam h hsp A i j * rhoOf Mfam h hsp B j k :=
  rho_unique Mfam h hind (rhoOf_spec Mfam h hsp (A * B))
    (realisesLaw_mul Mfam h (rhoOf_spec Mfam h hsp A) (rhoOf_spec Mfam h hsp B))

include hind in
theorem rhoOf_T (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i)) :
    rhoOf Mfam h hsp ModularGroup.T = modularRepT W h :=
  rho_unique Mfam h hind (rhoOf_spec Mfam h hsp ModularGroup.T) (realisesLaw_T Mfam h hcw)

/-- **The modular representation, read off**: `A ↦ ρ_A` is a monoid homomorphism
`SL₂(ℤ) →* Matrix ι ι ℂ`. -/
noncomputable def modularRepOf : SL(2, ℤ) →* Matrix ι ι ℂ where
  toFun A := Matrix.of (rhoOf Mfam h hsp A)
  map_one' := by
    refine Matrix.ext (fun i j => ?_)
    rw [Matrix.of_apply, rhoOf_one Mfam h hsp hind, Matrix.one_apply]
  map_mul' A B := by
    refine Matrix.ext (fun i k => ?_)
    rw [Matrix.of_apply, rhoOf_mul Mfam h hsp hind, Matrix.mul_apply]
    rfl

/-- **The modular data assembled from the two named inputs.** -/
noncomputable def modularDataOf (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i)) :
    ModularData W ι where
  Mfam := Mfam
  h := h
  hasWeight := hcw
  rep := modularRepOf Mfam h hsp hind
  repS := rhoOf Mfam h hsp ModularGroup.S
  rep_S := rfl
  rep_T := by
    show Matrix.of (rhoOf Mfam h hsp ModularGroup.T) = _
    rw [rhoOf_T Mfam h hsp hind hcw]

/-- **Zhu's 5.3.18a, analytically, for a `ModularData`**: for every `A`, every `v` of
`L[0]`-weight `n`, every `i` and `τ`,
`𝒵_{M_i}(v; Aτ) = (cτ+d)ⁿ · Σ_j ρ(A)_{ij} 𝒵_{M_j}(v; τ)`. -/
def ZhuModularityAnalytic (D : ModularData W ι) : Prop :=
  ∀ (A : SL(2, ℤ)) (n : ℕ) (v : 𝒱), v ∈ sqWeightSpace W (n : ℂ) → ∀ (i : ι) (τ : UpperHalfPlane),
    traceFun D.Mfam D.h i v (A • τ)
      = autFactor A τ ^ n * ∑ j, D.rep A i j * traceFun D.Mfam D.h j v τ

/-- **Zhu's modularity theorem 5.3.8 (5.3.18a), for EVERY `A ∈ SL₂(ℤ)`**, from the
trace-spanning and independence data. -/
theorem zhu_modularity_of_spanning (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i)) :
    ZhuModularityAnalytic (modularDataOf Mfam h hsp hind hcw) := by
  intro A n v hv i τ
  exact rhoOf_spec Mfam h hsp A n v hv i τ

/-! ## Consequences read off from the group -/

/-- `ρ(−1)² = 1`. -/
theorem modularRepOf_neg_one_sq :
    modularRepOf Mfam h hsp hind (-1) * modularRepOf Mfam h hsp hind (-1) = 1 := by
  rw [← map_mul, neg_one_mul, neg_neg, map_one]

/-- The law at `−1 ∈ SL₂(ℤ)` (which acts trivially on `ℍ`): `S_i(v,τ) = (−1)ⁿ Σ_j ρ(−1)_{ij} S_j(v,τ)`. -/
theorem traceFun_neg_one_law (n : ℕ) (v : 𝒱) (hv : v ∈ sqWeightSpace W (n : ℂ)) (i : ι)
    (τ : UpperHalfPlane) :
    traceFun Mfam h i v τ
      = (-1) ^ n * ∑ j, rhoOf Mfam h hsp (-1) i j * traceFun Mfam h j v τ := by
  have := rhoOf_spec Mfam h hsp (-1) n v hv i τ
  rwa [show ((-1 : SL(2, ℤ)) • τ) = τ from by
    rw [show (-1 : SL(2, ℤ)) = -(1 : SL(2, ℤ)) from rfl, ModularGroup.SL_neg_smul, one_smul],
    autFactor_neg_one] at this

end

end VOA
