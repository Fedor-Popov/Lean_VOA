/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGateAnnN0
import VOA.Modules.ZhuVermaAnArchDJCarrier
import VOA.Modules.ZhuVermaAnArchDJCarrierGraded

/-!
# The per-level descended zero-mode map `A_{n,0}(𝒱) → M` — a scaffold for the M(U) universal property.

The universal property of the generalized-Verma module `M(U)` (DJ Thm 4.13's second half) attaches to
every weak module `M` with a distinguished bottom vector `w ∈ Ω(M)` the induced map
`φ̄([v] ⊗ u) = o_{n,0}(v)·(emb u)`.  Its level-`n` component is *linear in the class `[v] ∈ A_{n,0}(𝒱)`*
because the zero mode `o_{n,0}(x)` of every `x ∈ O_{n,0}(𝒱)` kills the bottom
(`oLevW_OnmFull_n0_vanish_uncond`).  This file packages exactly that quotient descent:

  `oLevAnmFullDescend A L n hw : A_{n,0}(𝒱) →ₗ[ℂ] M`,  `[v] ↦ o_{n,0}(v)·w`,

well-defined for any bottom vector `w ∈ L.lev 0`, landing in the level-`n` piece `L.lev n`.  It is the
`A_{n,0}(𝒱)`-linear building block of the induced map `φ̄`; the remaining ingredients (the
`⊗_{A(𝒱)}`-balancing and the weak-module intertwining) are DJ Cor 4.2 / DJ Lemma 4.1, both proved.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), `sorry`-free, `pbw`-free; no existing file
mutated.

## References
Dong–Jiang math/0601626 Thm 4.13; DLM3 §4.  `ZhuVermaAnArchGateAnnN0`
(`oLevW_OnmFull_n0_vanish_uncond`), `ZhuVermaAnArchGate` (`oLevW`, `AdmLev`, `oLevW_mem_level`),
`ZhuVermaAnArchAnmFull` (`AnmFull`, `mkAnmFull`, `OnmFull`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {A : WeakModule W M}

/-- **The per-level descended zero-mode map** `A_{n,0}(𝒱) →ₗ M`, `[v] ↦ o_{n,0}(v)·w`, for a bottom
vector `w ∈ L.lev 0`.  Well-defined by the `(n,0)` ideal-descent `oLevW_OnmFull_n0_vanish_uncond`
(the zero mode of `O_{n,0}(𝒱)` annihilates the bottom). -/
noncomputable def oLevAnmFullDescend (A : WeakModule W M) (L : AdmLev W A) (n : ℕ) {w : M}
    (hw : w ∈ L.lev 0) : AnmFull W n 0 →ₗ[ℂ] M :=
  Submodule.liftQ (OnmFull W n 0) ((oLevW A (((0 : ℕ) : ℤ) - (n : ℤ))).flip w)
    (fun x hx => oLevW_OnmFull_n0_vanish_uncond L n hx hw)

@[simp] theorem oLevAnmFullDescend_mk (L : AdmLev W A) (n : ℕ) {w : M} (hw : w ∈ L.lev 0) (v : 𝒱) :
    oLevAnmFullDescend A L n hw (mkAnmFull W n 0 v) = oLevW A (((0 : ℕ) : ℤ) - (n : ℤ)) v w := by
  simp only [oLevAnmFullDescend, mkAnmFull, Submodule.mkQ_apply, Submodule.liftQ_apply,
    LinearMap.flip_apply]

/-- The descended map lands in the level-`n` piece `L.lev n`. -/
theorem oLevAnmFullDescend_mem_lev (L : AdmLev W A) (n : ℕ) {w : M} (hw : w ∈ L.lev 0) (x : 𝒱) :
    oLevAnmFullDescend A L n hw (mkAnmFull W n 0 x) ∈ L.lev (n : ℤ) := by
  rw [oLevAnmFullDescend_mk]
  have hw0 : w ∈ L.lev ((0 : ℕ) : ℤ) := by simpa using hw
  exact oLevW_mem_level L 0 n x hw0

/-! ## The `⊗_ℂ`-cover map `A_{n,0}(𝒱) ⊗ X → M`, `[v] ⊗ x ↦ o_{n,0}(v)·(φ x)`.

For any `ℂ`-space `X` with an `M`-valued bottom embedding `φ : X →ₗ M` (`φ x ∈ Ω(M)` for all `x`),
the descended `A_{n,0}(𝒱)`-linear-in-`[v]` map extends to the whole `⊗_ℂ` cover.  This is the level-`n`
component of the induced map `φ̄` on the *cover* `A_{n,0}(𝒱) ⊗_ℂ X` of DJ's balanced piece
`A_{n,0}(𝒱) ⊗_{A(𝒱)} X`; the balancing (DJ Cor 4.2) descends it to the balanced quotient. -/

variable {X : Type u} [AddCommGroup X] [Module ℂ X]

/-- The `[v]`-linear bilinear form `A_{n,0}(𝒱) →ₗ (X →ₗ M)`, `[v] ↦ (x ↦ o_{n,0}(v)·(φ x))`,
well-defined by the `(n,0)` ideal-descent (with `φ x` in the bottom). -/
noncomputable def oLevCoverBil (A : WeakModule W M) (L : AdmLev W A) (n : ℕ) (φ : X →ₗ[ℂ] M)
    (hφ : ∀ x, φ x ∈ L.lev 0) : AnmFull W n 0 →ₗ[ℂ] (X →ₗ[ℂ] M) :=
  Submodule.liftQ (OnmFull W n 0)
    { toFun := fun v => (oLevW A (((0 : ℕ) : ℤ) - (n : ℤ)) v).comp φ
      map_add' := fun v v' => by ext x; simp [map_add]
      map_smul' := fun c v => by ext x; simp [map_smul] }
    (by
      intro v hv
      ext x
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, LinearMap.zero_apply]
      exact oLevW_OnmFull_n0_vanish_uncond L n hv (hφ x))

@[simp] theorem oLevCoverBil_mk (L : AdmLev W A) (n : ℕ) (φ : X →ₗ[ℂ] M) (hφ : ∀ x, φ x ∈ L.lev 0)
    (v : 𝒱) (x : X) :
    oLevCoverBil A L n φ hφ (mkAnmFull W n 0 v) x = oLevW A (((0 : ℕ) : ℤ) - (n : ℤ)) v (φ x) := by
  simp only [oLevCoverBil, mkAnmFull, Submodule.mkQ_apply, Submodule.liftQ_apply,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]

/-- **The `⊗_ℂ`-cover map** `A_{n,0}(𝒱) ⊗ X →ₗ M`, `[v] ⊗ x ↦ o_{n,0}(v)·(φ x)`. -/
noncomputable def oLevCoverMap (A : WeakModule W M) (L : AdmLev W A) (n : ℕ) (φ : X →ₗ[ℂ] M)
    (hφ : ∀ x, φ x ∈ L.lev 0) : TensorProduct ℂ (AnmFull W n 0) X →ₗ[ℂ] M :=
  TensorProduct.lift (oLevCoverBil A L n φ hφ)

@[simp] theorem oLevCoverMap_tmul (L : AdmLev W A) (n : ℕ) (φ : X →ₗ[ℂ] M) (hφ : ∀ x, φ x ∈ L.lev 0)
    (v : 𝒱) (x : X) :
    oLevCoverMap A L n φ hφ (mkAnmFull W n 0 v ⊗ₜ[ℂ] x)
      = oLevW A (((0 : ℕ) : ℤ) - (n : ℤ)) v (φ x) := by
  simp only [oLevCoverMap, TensorProduct.lift.tmul, oLevCoverBil_mk]

end

/-! ## The `⊗_{A(𝒱)}`-balancing descent (DJ Cor 4.2): the cover map descends to `M(U)(n) = DJPiece`.

For a bottom embedding `φ : U → Ω(M)` that is `A(𝒱)`-equivariant (`φ([a]·u) = o(a)·φ(u)`), the cover
map kills the balancing generators `[x *ⁿ₀ a] ⊗ u − [x] ⊗ [a]·u`, so it descends to the balanced piece
`M(U)(n) = A_{n,0}(𝒱) ⊗_{A(𝒱)} U`.  The vanishing is DJ Lemma 4.1 (`oLevW_anmGen_law_lev`) applied to
`anmRight W n 0 x a = anmGen W n 0 0 x a`, together with the equivariance of `φ`. -/

section Piece
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {A : WeakModule W M}

/-- **DJ Cor 4.2 — the cover map respects the `A(𝒱)`-balancing.**  For an `A(𝒱)`-equivariant bottom
embedding `φ`, `o_{n,0}(x *ⁿ₀ a)·(φ u) = o_{n,0}(x)·(φ([a]·u))`. -/
theorem oLevCoverMap_balance (L : AdmLev W A) (n : ℕ) (U : AmMod W 0) (φ : U.carrier →ₗ[ℂ] M)
    (hφlev : ∀ u, φ u ∈ L.lev 0)
    (hφact : ∀ (a : 𝒱) (u : U.carrier), φ (U.ρ (mkAnFull W 0 a) u) = oLevW A (0 : ℤ) a (φ u))
    (x a : 𝒱) (w : U.carrier) :
    oLevCoverMap A L n φ hφlev (mkAnmFull W n 0 (anmRight W n 0 x a) ⊗ₜ[ℂ] w)
      = oLevCoverMap A L n φ hφlev (mkAnmFull W n 0 x ⊗ₜ[ℂ] U.ρ (mkAnFull W 0 a) w) := by
  rw [oLevCoverMap_tmul, oLevCoverMap_tmul, hφact, ← anmGen_eq_anmRight,
    oLevW_anmGen_law_lev L n 0 0 x a (hφlev w)]
  norm_num

/-- **The descended level-`n` induced map** `M(U)(n) = A_{n,0}(𝒱) ⊗_{A(𝒱)} U →ₗ M`,
`[x] ⊗ u ↦ o_{n,0}(x)·(φ u)`, for an `A(𝒱)`-equivariant bottom embedding `φ`.  This is the level-`n`
component of the universal map `φ̄` of DJ Thm 4.13's second half. -/
noncomputable def oLevPieceMap (A : WeakModule W M) (L : AdmLev W A) (n : ℕ) (U : AmMod W 0)
    (φ : U.carrier →ₗ[ℂ] M) (hφlev : ∀ u, φ u ∈ L.lev 0)
    (hφact : ∀ (a : 𝒱) (u : U.carrier), φ (U.ρ (mkAnFull W 0 a) u) = oLevW A (0 : ℤ) a (φ u)) :
    DJPiece W U n →ₗ[ℂ] M :=
  Submodule.liftQ (djBalancing W U n) (oLevCoverMap A L n φ hφlev)
    (by
      rw [djBalancing, Submodule.span_le]
      rintro z ⟨x, a, w, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact oLevCoverMap_balance L n U φ hφlev hφact x a w)

@[simp] theorem oLevPieceMap_mk (L : AdmLev W A) (n : ℕ) (U : AmMod W 0) (φ : U.carrier →ₗ[ℂ] M)
    (hφlev : ∀ u, φ u ∈ L.lev 0)
    (hφact : ∀ (a : 𝒱) (u : U.carrier), φ (U.ρ (mkAnFull W 0 a) u) = oLevW A (0 : ℤ) a (φ u))
    (v : 𝒱) (u : U.carrier) :
    oLevPieceMap A L n U φ hφlev hφact (mkDJPiece W U n (mkAnmFull W n 0 v ⊗ₜ[ℂ] u))
      = oLevW A (((0 : ℕ) : ℤ) - (n : ℤ)) v (φ u) := by
  simp only [oLevPieceMap, mkDJPiece, Submodule.mkQ_apply, Submodule.liftQ_apply, oLevCoverMap_tmul]

/-! ## The full induced linear map `φ̄ : M(U) → M` (the direct sum over levels).

Assembling the level-`n` components `oLevPieceMap` over `n : ℕ` gives the induced `ℂ`-linear map
`φ̄ : M(U) = ⨁ₙ M(U)(n) → M`.  It is the `ℂ`-linear underlying map of DJ Thm 4.13's universal map;
what remains for the full universal property is that it *intertwines the `𝒱`-action* (DJ Lemma 4.1 at
the operator level) — the last deep analytic input — and the surjectivity/kernel argument identifying
`ker φ̄ = J(U)` for an irreducible target `M`. -/

/-- **The full induced linear map** `φ̄ : M(U) →ₗ M`, `Σ_n [x]ₙ ⊗ u ↦ o_{n,0}(x)·(φ u)`, the direct sum
of the level-`n` components `oLevPieceMap`. -/
noncomputable def oLevUnivMap (A : WeakModule W M) (L : AdmLev W A) (U : AmMod W 0)
    (φ : U.carrier →ₗ[ℂ] M) (hφlev : ∀ u, φ u ∈ L.lev 0)
    (hφact : ∀ (a : 𝒱) (u : U.carrier), φ (U.ρ (mkAnFull W 0 a) u) = oLevW A (0 : ℤ) a (φ u)) :
    DJCarrier W U →ₗ[ℂ] M :=
  DirectSum.toModule ℂ ℕ M (fun n => oLevPieceMap A L n U φ hφlev hφact)

@[simp] theorem oLevUnivMap_incl (L : AdmLev W A) (U : AmMod W 0) (φ : U.carrier →ₗ[ℂ] M)
    (hφlev : ∀ u, φ u ∈ L.lev 0)
    (hφact : ∀ (a : 𝒱) (u : U.carrier), φ (U.ρ (mkAnFull W 0 a) u) = oLevW A (0 : ℤ) a (φ u))
    (n : ℕ) (z : DJPiece W U n) :
    oLevUnivMap A L U φ hφlev hφact (DJCarrier.incl W U n z)
      = oLevPieceMap A L n U φ hφlev hφact z := by
  rw [oLevUnivMap, DJCarrier.incl, DirectSum.toModule_lof]

end Piece

end VOA
