/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJCarrier
import Mathlib.Algebra.DirectSum.Module

/-!
# The graded Dong–Jiang carrier `M(U) = ⨁_{n ∈ ℤ₊} A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U`

`ZhuVermaAnArchDJCarrier` built Dong–Jiang's level piece
`DJPiece W U n = A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U` (`math/0601626`, §4) over the **full** ideal
`OnmFull = O' + O'' + O'''` and with the **balanced** tensor at the **general** base level `m`.
This file assembles the graded carrier itself,

```
  M(U) = ⨁_{n ∈ ℤ₊} A_{n,m}(V) ⊗_{A_m(V)} U ,    M(U)(n) = A_{n,m}(V) ⊗_{A_m(V)} U ,
```

verbatim DJ §4 ("Then `M(U)` is naturally `ℤ₊`-graded such that
`M(U)(n) = A_{n,m}(V) ⊗_{A_m(V)} U`").

## Contents (axiom-clean, `pbw`-free)

* **`DJCarrier W U := ⨁ n : ℕ, DJPiece W U n`** — the graded carrier, with the canonical
  `DirectSum` `AddCommGroup`/`Module ℂ`.
* **`DJCarrier.incl` / `DJCarrier.proj`** — the level-`n` inclusion/projection
  (`proj_incl_same` / `proj_incl_ne`).
* **`DJCarrier.deg n`** — the `ℕ`-grading `M(U)(n)` as a submodule of `M(U)`.
* **`DJCarrier.isInternal_deg`** — DJ's `M(U) = ⊕ₙ M(U)(n)` as a genuine
  `DirectSum.IsInternal`.
* **`DJCarrier.degEquivPiece`** — the graded subspace `M(U)(n)` is the level piece.
* **`DJCarrier.degMEquiv`** — the level-`m` graded piece is `U`, given `DJAnnEqAn W m`
  (DJ Prop. 4.6).  This is DJ's `M(U)(m) = U`, the statement that makes `M(U)` the generalized
  Verma module induced from `U`.

The grading mirrors the proved `MUBal` (`ZhuVermaAnArchMUBal`); the difference is that the pieces
here are DJ's genuine ones (full ideal, general base level `m`).

`#print axioms` on every headline is `[propext, Classical.choice, Quot.sound]`.  No `sorry`, no new
axiom, no `pbw`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §4 (the definition of `M(U)`, Prop.
`pa4.5` = printed Prop. 4.6, Thm 4.10); Dong–Li–Mason, J. Algebra 206 (1998) 67–96.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators TensorProduct DirectSum

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {m : ℕ}

/-! ## The graded carrier -/

/-- **Dong–Jiang's induced-module carrier** `M(U) = ⨁_{n ∈ ℤ₊} A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U`
(`math/0601626`, §4).  The `ℕ`-grading is the level `n`; the level-`m` piece is `U` itself
(`DJCarrier.degMEquiv`, given DJ Prop. 4.6).  Carries the canonical `DirectSum`
`AddCommGroup`/`Module ℂ`. -/
abbrev DJCarrier (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) : Type u :=
  ⨁ n : ℕ, DJPiece W U n

/-- The canonical inclusion of the level-`n` piece into `M(U)`. -/
noncomputable def DJCarrier.incl (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) (n : ℕ) :
    DJPiece W U n →ₗ[ℂ] DJCarrier W U :=
  DirectSum.lof ℂ ℕ (DJPiece W U) n

/-- The canonical projection of `M(U)` onto the level-`n` piece. -/
noncomputable def DJCarrier.proj (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) (n : ℕ) :
    DJCarrier W U →ₗ[ℂ] DJPiece W U n :=
  DirectSum.component ℂ ℕ (DJPiece W U) n

@[simp] theorem DJCarrier.proj_incl_same (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) (n : ℕ)
    (x : DJPiece W U n) : DJCarrier.proj W U n (DJCarrier.incl W U n x) = x :=
  DirectSum.component.lof_self ℂ n x

theorem DJCarrier.proj_incl_ne (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) {n k : ℕ}
    (h : n ≠ k) (x : DJPiece W U k) : DJCarrier.proj W U n (DJCarrier.incl W U k x) = 0 := by
  rw [DJCarrier.proj, DJCarrier.incl, DirectSum.component.of]
  exact dif_neg (Ne.symm h)

/-! ## The `ℕ`-grading is an internal direct sum -/

/-- The level-`n` graded subspace `M(U)(n)` of `M(U)`: the range of `DJCarrier.incl … n`.
This is DJ's grading `M(U) = ⊕ₙ M(U)(n)`. -/
noncomputable def DJCarrier.deg (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) (n : ℕ) :
    Submodule ℂ (DJCarrier W U) := LinearMap.range (DJCarrier.incl W U n)

/-- **`M(U) = ⊕ₙ M(U)(n)` is a genuine internal direct-sum decomposition**
(`DirectSum.IsInternal`) — Dong–Jiang's "`M(U)` is naturally `ℤ₊`-graded such that
`M(U)(n) = A_{n,m}(V) ⊗_{A_m(V)} U`". -/
theorem DJCarrier.isInternal_deg (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) :
    DirectSum.IsInternal (DJCarrier.deg W U) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  have hproj_sup : ∀ (n : ℕ) (z : DJCarrier W U),
      z ∈ (⨆ (j : ℕ) (_ : j ≠ n), DJCarrier.deg W U j) → DJCarrier.proj W U n z = 0 := by
    intro n z hz
    refine Submodule.iSup_induction _ (motive := fun w => DJCarrier.proj W U n w = 0) hz
      ?_ (map_zero _) (fun a b ha hb => by simp only [map_add, ha, hb, add_zero])
    intro j z hjz
    refine Submodule.iSup_induction _ (motive := fun w => DJCarrier.proj W U n w = 0) hjz
      ?_ (map_zero _) (fun a b ha hb => by simp only [map_add, ha, hb, add_zero])
    intro hjn w hw
    obtain ⟨v, rfl⟩ := hw
    exact DJCarrier.proj_incl_ne W U (Ne.symm hjn) v
  constructor
  · refine iSupIndep_def.mpr (fun n => ?_)
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    rintro x ⟨⟨y, rfl⟩, hxsup⟩
    rw [Submodule.mem_bot]
    have h0 : DJCarrier.proj W U n (DJCarrier.incl W U n y) = 0 := hproj_sup n _ hxsup
    rw [DJCarrier.proj_incl_same] at h0
    rw [h0, map_zero]
  · rw [eq_top_iff]
    intro x _
    refine DirectSum.induction_on x (Submodule.zero_mem _) ?_
      (fun a b ha hb => Submodule.add_mem _ ha hb)
    intro n y
    exact Submodule.mem_iSup_of_mem n ⟨y, rfl⟩

/-! ## The graded subspace `M(U)(n)` is the level piece -/

/-- **`M(U)(n) ≃ A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U`** — the graded subspace of `M(U)` at level `n` is the
Dong–Jiang level piece.  Inverse pair: the projection restricted to `deg n`, and the inclusion
corestricted to its range. -/
noncomputable def DJCarrier.degEquivPiece (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) (n : ℕ) :
    DJCarrier.deg W U n ≃ₗ[ℂ] DJPiece W U n :=
  LinearEquiv.ofLinear
    ((DJCarrier.proj W U n).comp (DJCarrier.deg W U n).subtype)
    (LinearMap.codRestrict (DJCarrier.deg W U n) (DJCarrier.incl W U n) (fun x => ⟨x, rfl⟩))
    (by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
        DJCarrier.proj_incl_same, LinearMap.id_apply])
    (by
      refine LinearMap.ext fun z => ?_
      obtain ⟨w, hw⟩ := z
      obtain ⟨y, rfl⟩ := hw
      refine Subtype.ext ?_
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
        DJCarrier.proj_incl_same, LinearMap.id_apply])

@[simp] theorem DJCarrier.degEquivPiece_incl (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) (n : ℕ)
    (x : DJPiece W U n) :
    DJCarrier.degEquivPiece W U n ⟨DJCarrier.incl W U n x, ⟨x, rfl⟩⟩ = x := by
  rw [DJCarrier.degEquivPiece, LinearEquiv.ofLinear_apply]
  exact DJCarrier.proj_incl_same W U n x

/-! ## The level-`m` graded piece is `U` -/

/-- **`M(U)(m) ≅ U`** on the graded carrier — Dong–Jiang's "By Proposition 4.6, `M(U)(m)` and `U`
are isomorphic `A_m(V)`-modules".  Composes `M(U)(m) ≃ DJPiece W U m` with the payoff
`djPieceMEquiv` of `ZhuVermaAnArchDJCarrier`.  This is DJ's statement that `M(U)` is the
generalized Verma module *induced from* `U`. -/
noncomputable def DJCarrier.degMEquiv (W : VertexOperatorAlgebra 𝒱) (m : ℕ) (h : DJAnnEqAn W m)
    (U : AmMod W m) : DJCarrier.deg W U m ≃ₗ[ℂ] U.carrier :=
  (DJCarrier.degEquivPiece W U m).trans (djPieceMEquiv W m h U)

/-- The graded level-`m` isomorphism, computed on the image of a level-`m` vector. -/
@[simp] theorem DJCarrier.degMEquiv_incl (h : DJAnnEqAn W m) (U : AmMod W m)
    (x : DJPiece W U m) :
    DJCarrier.degMEquiv W m h U ⟨DJCarrier.incl W U m x, ⟨x, rfl⟩⟩ = djPieceMEquiv W m h U x := by
  rw [DJCarrier.degMEquiv, LinearEquiv.trans_apply, DJCarrier.degEquivPiece_incl]

/-- The graded level-`m` isomorphism on a generator: `[x]_{m,m} ⊗ w ↦ ρ([x]_m)·w`. -/
theorem DJCarrier.degMEquiv_incl_tmul (h : DJAnnEqAn W m) (U : AmMod W m) (x : 𝒱)
    (w : U.carrier) :
    DJCarrier.degMEquiv W m h U
        ⟨DJCarrier.incl W U m (mkDJPiece W U m (mkAnmFull W m m x ⊗ₜ[ℂ] w)),
          ⟨mkDJPiece W U m (mkAnmFull W m m x ⊗ₜ[ℂ] w), rfl⟩⟩
      = U.ρ (mkAnFull W m x) w := by
  rw [DJCarrier.degMEquiv_incl, djPieceMEquiv_mk]

end VOA
