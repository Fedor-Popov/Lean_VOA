/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.WeakModule

/-!
# The OrdVModule quotient functor — `M ⧸ N` for an invariant submodule `N`

The keystone construction for `M̄(U) = M(U)/(defect)`, `L(U) = M(U)/J`, and Game Two:
given a weak (or `ℂ`-graded) `𝒱`-module `M` and an *action-invariant* `ℂ`-submodule
`N : WeakModule.Submodule' A` (closed under every mode `u₍ₙ₎`), the quotient
`M ⧸ N.carrier` carries a canonical weak/graded `𝒱`-module structure for which the
projection `mkQ : M ↠ M ⧸ N` is a surjective module homomorphism intertwining the action.

## Construction

This is **general algebra**, no engine needed — every weak-module axiom is an equality of
mode applications, and each is preserved by pushing through the surjective intertwiner
`mkQ`. Concretely:

* The descended action is `YM_quot a := j ↦ (A.YM a j).mapQ` (Mathlib's
  `Submodule.mapQ`, well-defined because `N` is invariant: `(A.YM a j) N ⊆ N`).
  Linearity in `a` is proved by quotient extensionality (`Submodule.linearMap_qext`).
* **Vacuum** (5.3.1a) and **truncation** descend pointwise because `mkQ` intertwines and
  is surjective.
* **Module Jacobi** (5.3.1b) descends: each `mode (YM_quot a) k [x] = [mode (YM a) k x]`
  (`quotient_action_mk`), so the entire mode identity is the image under the `ℂ`-linear,
  `finsum`-commuting map `mkQ` of the corresponding identity on `M`.

## Main results

* `WeakModule.quotient A N : WeakModule W (M ⧸ N.carrier)` — the quotient weak module.
* `WeakModule.quotientMk A N : A.Hom (WeakModule.quotient A N)` — the projection as a
  module homomorphism.
* `WeakModule.quotient_action_mk` — `mode ((quotient A N).YM a) k ⟦x⟧ = ⟦mode (A.YM a) k x⟧`.
* `OrdVModule.quotientWeak` / the precise remaining grading axiom for the full graded
  `OrdVModule` descent (the grading on `M ⧸ N` is the image grading `mkQ '' M_α`, whose
  internal-direct-sum + bounded-below + finite-dimensional repackaging is the only
  remaining graded obligation — the *weak* structure is complete below).

## Dependencies
* `VOA.Modules.WeakModule`.

## References
* Gannon §5.3.1 (Def. 5.3.1a–c); Lepowsky–Li Ch. 4–5 (module quotients); DLM3.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

namespace WeakModule

variable (A : WeakModule W M) (N : WeakModule.Submodule' A)

/-! ## Invariance of the carrier under each coefficient of `Y_M` -/

/-- The submodule `N` is invariant under every **coefficient** `(Y_M a)_j` of the field
`Y_M a` (not just under the `act`-indexed modes): for `x ∈ N`, `(A.YM a j) x ∈ N`. This is
`act_mem` reindexed by `j = -(n)-1` (mode `n ↦ a₍ₙ₎` reads coefficient `-n-1`). -/
theorem coeff_mem (a : 𝒱) (j : ℤ) {x : M} (hx : x ∈ N.carrier) :
    (A.YM a) j x ∈ N.carrier := by
  have h := N.act_mem a (-j - 1) hx
  rw [act_def, mode_apply, show -(-j - 1) - 1 = j from by ring] at h
  exact h

/-- The invariance hypothesis in the exact `mapQ` shape `N ≤ comap (A.YM a j) N`. -/
theorem coeff_le_comap (a : 𝒱) (j : ℤ) :
    N.carrier ≤ N.carrier.comap (A.YM a j) :=
  fun _ hx => coeff_mem A N a j hx

/-! ## The descended action -/

/-- The descended `j`-th coefficient endomorphism of `M ⧸ N`. -/
def YMquotCoeff (a : 𝒱) (j : ℤ) : End ℂ (M ⧸ N.carrier) :=
  N.carrier.mapQ N.carrier (A.YM a j) (coeff_le_comap A N a j)

@[simp] theorem YMquotCoeff_mk (a : 𝒱) (j : ℤ) (x : M) :
    YMquotCoeff A N a j (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((A.YM a j) x) :=
  Submodule.mapQ_apply _ _ _ x

/-- The descended action `Y_{M/N}(a, z)`, bundled `ℂ`-linearly in `a`. -/
def YMquot : 𝒱 →ₗ[ℂ] (End ℂ (M ⧸ N.carrier))⟦z^±⟧ where
  toFun a := fun j => YMquotCoeff A N a j
  map_add' a b := by
    funext j
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    change YMquotCoeff A N (a + b) j (Submodule.Quotient.mk x)
      = (YMquotCoeff A N a j + YMquotCoeff A N b j) (Submodule.Quotient.mk x)
    rw [YMquotCoeff_mk, LinearMap.add_apply, YMquotCoeff_mk, YMquotCoeff_mk]
    rw [show A.YM (a + b) j = A.YM a j + A.YM b j from by
        rw [map_add]; rfl]
    rw [LinearMap.add_apply, Submodule.Quotient.mk_add]
  map_smul' c a := by
    funext j
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    change YMquotCoeff A N (c • a) j (Submodule.Quotient.mk x)
      = (c • YMquotCoeff A N a j) (Submodule.Quotient.mk x)
    rw [YMquotCoeff_mk, LinearMap.smul_apply, YMquotCoeff_mk]
    rw [show A.YM (c • a) j = c • A.YM a j from by
        rw [map_smul]; rfl]
    rw [LinearMap.smul_apply, Submodule.Quotient.mk_smul]

@[simp] theorem YMquot_apply_coeff (a : 𝒱) (j : ℤ) :
    YMquot A N a j = YMquotCoeff A N a j := rfl

/-- **The descended mode action commutes with the projection** — the load-bearing
intertwining identity: `mode (Y_{M/N} a) k ⟦x⟧ = ⟦mode (Y_M a) k x⟧`. -/
@[simp] theorem quotient_action_mk (a : 𝒱) (k : ℤ) (x : M) :
    mode (YMquot A N a) k (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (mode (A.YM a) k x) := by
  simp only [mode_apply, YMquot_apply_coeff, YMquotCoeff_mk]

/-! ## Finiteness of the Jacobi summands on `M` (mirroring `Borcherds.{Puv,Pvu,BR}_fin`) -/

/-- Finiteness of the `Y_M(u)Y_M(v)` summand family (module mirror of `Puv_fin`): uses
the field truncation of `Y_M v` on `x`. -/
theorem jacL_uv_fin (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ i) •
        mode (A.YM u) (ℓ + m - i) (mode (A.YM v) (n + i) x)).Finite := by
  obtain ⟨Nv, hNv⟩ := A.truncation v x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nv - n))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [hNv (n + i) (by omega), map_zero, smul_zero]

/-- Finiteness of the `Y_M(v)Y_M(u)` summand family (module mirror of `Pvu_fin`). -/
theorem jacL_vu_fin (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ i) •
        mode (A.YM v) (ℓ + n - i) (mode (A.YM u) (m + i) x)).Finite := by
  obtain ⟨Nu, hNu⟩ := A.truncation u x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nu - m))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [hNu (m + i) (by omega), map_zero, smul_zero]

/-- Finiteness of the full LHS summand family (the difference). -/
theorem jacL_fin (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ i) •
        (mode (A.YM u) (ℓ + m - i) (mode (A.YM v) (n + i) x)
          - negOnePow ℓ • mode (A.YM v) (ℓ + n - i) (mode (A.YM u) (m + i) x))).Finite := by
  apply ((jacL_uv_fin A u v x ℓ m n).union (jacL_vu_fin A u v x ℓ m n)).subset
  intro i hi
  rw [Function.mem_support] at hi
  by_contra hcon
  rw [Set.mem_union, Function.mem_support, Function.mem_support] at hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply hi
  rw [smul_sub, h1, smul_comm (negOnePow i * cbz ℓ i) (negOnePow ℓ), h2, smul_zero, sub_zero]

/-- Finiteness of the RHS summand family (module mirror of `BR_fin`): uses the VOA-level
truncation of `u₍ℓ₊ᵢ₎v` together with linearity `Y_M 0 = 0`. -/
theorem jacR_fin (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      cbz m i • mode (A.YM (W.smul u (ℓ + i) v)) (m + n - i) x).Finite := by
  obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
  apply Set.Finite.subset (Set.finite_Icc 0 (N - ℓ))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg m h, zero_smul]
  · rw [hN (ℓ + i) (by omega), map_zero]
    change cbz m i • mode (0 : (End ℂ M)⟦z^±⟧) (m + n - i) x = 0
    rw [show mode (0 : (End ℂ M)⟦z^±⟧) (m + n - i) = (0 : End ℂ M) from rfl,
      LinearMap.zero_apply, smul_zero]

/-! ## The quotient is a weak module -/

/-- **The quotient weak module** `M ⧸ N` (Gannon Def. 5.3.1a–b). Every axiom descends from
`M` through the surjective intertwiner `mkQ`: the vacuum/truncation/Jacobi identities are
all images of the corresponding identities on `M`. -/
def quotient : WeakModule W (M ⧸ N.carrier) where
  YM := YMquot A N
  vacuum_YM := by
    -- Coefficient-wise: `Y_{M/N} 𝟙` is `(Y_M 𝟙) = 1` pushed through `mapQ`, and `mapQ`
    -- sends the identity to the identity and `0` to `0`.
    apply FormalDist.ext
    intro j
    change YMquotCoeff A N W.vacuum j = (1 : (End ℂ (M ⧸ N.carrier))⟦z^±⟧) j
    -- `A.YM 𝟙 j` is the `M`-level identity-or-zero coefficient (`A.vacuum_YM`).
    have hvac : A.YM W.vacuum j = (1 : (End ℂ M)⟦z^±⟧) j := by rw [A.vacuum_YM]
    rw [FormalDist.one_apply] at hvac
    rw [FormalDist.one_apply]
    -- Compare endomorphisms of `M ⧸ N` by quotient extensionality.
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    change YMquotCoeff A N W.vacuum j (Submodule.Quotient.mk x)
      = (if j = 0 then (1 : End ℂ (M ⧸ N.carrier)) else 0) (Submodule.Quotient.mk x)
    rw [YMquotCoeff_mk, hvac]
    split_ifs with hj
    · simp only [Module.End.one_eq_id, LinearMap.id_apply]
    · simp only [LinearMap.zero_apply, Submodule.Quotient.mk_zero]
  truncation := by
    intro a x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨Nb, hNb⟩ := A.truncation a x
      exact ⟨Nb, fun n hn => by
        rw [quotient_action_mk, hNb n hn, Submodule.Quotient.mk_zero]⟩
  jacobi := by
    intro u v x ℓ m n
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      have key := A.jacobi u v x ℓ m n
      -- `mk = mkQ` as the surjective intertwiner; both sides are its image of the `M`-identity.
      set mk : M →ₗ[ℂ] M ⧸ N.carrier := N.carrier.mkQ with hmk
      have hmkx : (Submodule.Quotient.mk x : M ⧸ N.carrier) = mk x := rfl
      rw [hmkx]
      -- Each quotient mode = `mk` of the `M`-side mode (`quotient_action_mk`).
      have hL : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
            (mode (YMquot A N u) (ℓ + m - i) (mode (YMquot A N v) (n + i) (mk x))
              - negOnePow ℓ • mode (YMquot A N v) (ℓ + n - i)
                  (mode (YMquot A N u) (m + i) (mk x))))
          = mk (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
            (mode (A.YM u) (ℓ + m - i) (mode (A.YM v) (n + i) x)
              - negOnePow ℓ • mode (A.YM v) (ℓ + n - i) (mode (A.YM u) (m + i) x))) := by
        rw [show mk (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
              (mode (A.YM u) (ℓ + m - i) (mode (A.YM v) (n + i) x)
                - negOnePow ℓ • mode (A.YM v) (ℓ + n - i) (mode (A.YM u) (m + i) x)))
            = mk.toAddMonoidHom (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
              (mode (A.YM u) (ℓ + m - i) (mode (A.YM v) (n + i) x)
                - negOnePow ℓ • mode (A.YM v) (ℓ + n - i) (mode (A.YM u) (m + i) x)))
            from rfl,
          map_finsum mk.toAddMonoidHom (jacL_fin A u v x ℓ m n)]
        refine finsum_congr fun i => ?_
        rw [hmk]
        simp only [LinearMap.toAddMonoidHom_coe, map_smul, map_sub, Submodule.mkQ_apply,
          quotient_action_mk]
      have hR : (∑ᶠ i : ℤ, cbz m i • mode (YMquot A N (W.smul u (ℓ + i) v)) (m + n - i) (mk x))
          = mk (∑ᶠ i : ℤ, cbz m i • mode (A.YM (W.smul u (ℓ + i) v)) (m + n - i) x) := by
        rw [show mk (∑ᶠ i : ℤ, cbz m i • mode (A.YM (W.smul u (ℓ + i) v)) (m + n - i) x)
            = mk.toAddMonoidHom (∑ᶠ i : ℤ, cbz m i •
              mode (A.YM (W.smul u (ℓ + i) v)) (m + n - i) x) from rfl,
          map_finsum mk.toAddMonoidHom (jacR_fin A u v x ℓ m n)]
        refine finsum_congr fun i => ?_
        rw [hmk]
        simp only [LinearMap.toAddMonoidHom_coe, map_smul, Submodule.mkQ_apply,
          quotient_action_mk]
      rw [hL, hR, key]

/-- **The quotient action commutes with the projection**, restated for the bundled quotient
module `quotient A N` (the `act`-level intertwining identity, load-bearing for `M̄(U)`,
`L(U)`, and Game Two): `(M/N)`-mode of `⟦x⟧` is the class of the `M`-mode of `x`. -/
@[simp] theorem quotient_act_mk (a : 𝒱) (k : ℤ) (x : M) :
    (quotient A N).act a k (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (A.act a k x) := by
  change mode (YMquot A N a) k (Submodule.Quotient.mk x)
    = Submodule.Quotient.mk (mode (A.YM a) k x)
  exact quotient_action_mk A N a k x

/-- **The canonical projection `M ↠ M ⧸ N` as a homomorphism of weak modules**: the
surjective `ℂ`-linear intertwiner `mkQ`. This is "the quotient projection as a module hom"
(unblocks `M̄(U) = induced/defect`, `L(U) = M(U)/J`, Game Two). -/
def quotientMk : A.Hom (quotient A N) where
  toLinearMap := N.carrier.mkQ
  map_act a k x := by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, quotient_act_mk]

@[simp] theorem quotientMk_apply (x : M) :
    (quotientMk A N).toLinearMap x = Submodule.Quotient.mk x := rfl

/-- The projection homomorphism is surjective (`mkQ` is surjective). -/
theorem quotientMk_surjective :
    Function.Surjective (quotientMk A N).toLinearMap :=
  N.carrier.mkQ_surjective

end WeakModule

/-! ## The graded `OrdVModule` quotient

For a graded `OrdVModule`, the quotient `M ⧸ N` inherits the *weak* structure above. The
remaining graded data is the image grading `(M/N)_α := mkQ '' M_α = map mkQ (M_α)`: the
`L₀`-eigenspace property descends (it is the image of `L₀ x = α x` under the intertwiner
`mkQ`), and the bounded-below / finite-dimensional / internal-direct-sum repackaging is the
sole remaining graded obligation. We record the weak descent (complete) and the precise
grading target. -/

namespace OrdVModule

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- The **weak module underlying the quotient** of a graded `OrdVModule` `N` by an invariant
submodule `P` (the complete weak descent; the grading repackaging is `OrdVModule.quotient`,
the remaining graded obligation). -/
def quotientWeak (N : OrdVModule W M) (P : WeakModule.Submodule' N.toWeakModule) :
    WeakModule W (M ⧸ P.carrier) :=
  WeakModule.quotient N.toWeakModule P

/-- The image grading on the quotient: `(M/P)_α := map mkQ (N_α)`, the descended
`L₀`-eigenspace. (The full graded `OrdVModule` packages this with internal-direct-sum +
bounded-below + finite-dimensional; the eigenspace equation itself descends through the
surjective intertwiner `mkQ`.) -/
def quotientWeight (N : OrdVModule W M) (P : WeakModule.Submodule' N.toWeakModule) (α : ℂ) :
    Submodule ℂ (M ⧸ P.carrier) :=
  (N.weight α).map P.carrier.mkQ

/-- **The descended `L₀`-eigenspace property** (5.3.1c on the quotient): on the image
grading `(M/P)_α`, `L₀` acts as the scalar `α`. This is the image under the intertwiner
`mkQ` of the `M`-level eigenvalue equation `N.L0_weight`. -/
theorem quotient_L0_weight (N : OrdVModule W M) (P : WeakModule.Submodule' N.toWeakModule)
    (α : ℂ) (y : M ⧸ P.carrier) (hy : y ∈ quotientWeight N P α) :
    mode ((quotientWeak N P).YM W.conformalVector) 1 y = α • y := by
  obtain ⟨x, hx, rfl⟩ := (Submodule.mem_map).mp hy
  rw [Submodule.mkQ_apply]
  -- the conformal mode `L₀ = (ω)₍₁₎` intertwines: `(ω)₍₁₎ ⟦x⟧ = ⟦(ω)₍₁₎ x⟧ = ⟦α • x⟧`.
  have hint : mode ((quotientWeak N P).YM W.conformalVector) 1 (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (mode (N.YM W.conformalVector) 1 x) :=
    WeakModule.quotient_action_mk N.toWeakModule P W.conformalVector 1 x
  rw [hint, N.L0_weight α x hx, Submodule.Quotient.mk_smul]

end OrdVModule

end VOA
