/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteCharge
import VOA.Examples.Sl2SemiInfiniteTranslation
import VOA.Core.SuperNthProduct
import VOA.Core.BRSTCohomology

/-!
# The zero-mode derivation required by semi-infinite BRST

`ZeroModeCommutator` is the precise missing state-field compatibility of the bare
`SuperVertexAlgebra` interface. It quantifies over every pair of homogeneous
states, independently of a choice of BRST current, level, or differential.
It follows from the existing Borcherds theory for any `SuperNearVOA`.
An odd residue is then a super derivation on arbitrary, also inhomogeneous, states.
The translation-covariance construction supplies this formula on the tensor
algebra from matter translation data alone; the ghost translation is proved.

The square identity below is a reduction to an actual state product, not a
nilpotency hypothesis. That product is evaluated in `Sl2SemiInfiniteNilpotency`;
`Sl2SemiInfiniteComplex` assembles the complex for translated matter at `-4`.
-/

namespace VOA.Sl2SemiInfinite

open Module (End)
open scoped TensorProduct

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The zero-mode slice of the super commutator formula, for all homogeneous
states and every mode of the second field. This is additional compatibility
data when only a bare `SuperVertexAlgebra` is supplied. -/
def ZeroModeCommutator (V : SuperVertexAlgebra M) : Prop :=
  ∀ {p q : ZMod 2} {u v : M}, u ∈ V.parity p → v ∈ V.parity q → ∀ n : ℤ,
    mode (V.Y u) 0 * mode (V.Y v) n -
        koszul p q • (mode (V.Y v) n * mode (V.Y u) 0) =
      mode (V.Y (mode (V.Y u) 0 v)) n

/-- The standard super Borcherds theory supplies this compatibility; no special
assumption on the chosen residue is used. -/
theorem zeroModeCommutator_of_superNearVOA (V : SuperNearVOA M) :
    ZeroModeCommutator V.toSuperVertexAlgebra := by
  intro p q u v hu hv n
  have h := V.mode_iterate_nonneg_chooseε hu hv 0 n
  simpa [Finset.sum_range_one, SuperVertexAlgebra.smul_def] using h.symm

/-- Translation covariance already suffices; a conformal vector is unnecessary. -/
theorem zeroModeCommutator_of_translation {V : SuperVertexAlgebra M}
    (H : TranslationCovariant V) : ZeroModeCommutator V :=
  fun hu hv n => H.zero_mode_commutator hu hv n

/-- A stronger matter structure with precisely the missing translation input.
It imposes no identity on the BRST charge and no square-zero assumption. -/
structure TranslatedAffineSl2Action (V : SuperVertexAlgebra M) (k : ℂ)
    extends AffineSl2Action V k where
  translation : TranslationCovariant V

/-- The universal affine example inhabits the stronger input structure at
every noncritical level, including `-4`. -/
noncomputable def translatedAffineAction (k : ℂ) (hk : k + 2 ≠ 0) :
    TranslatedAffineSl2Action (DSsl2.affSVA k hk) k where
  toAffineSl2Action := affineAction k hk
  translation := {
    T := AffineVOA.Ltrans k
    vacuum_zero := AffineVOA.Ltrans_vacuum k
    covariant := AffineVOA.YA_DCov k hk }

/-- The homogeneous Leibniz rule for an odd zero mode. -/
theorem odd_zeroMode_deriv_homogeneous {V : SuperVertexAlgebra M}
    (hV : ZeroModeCommutator V) {q : M} (hq : q ∈ V.parity 1)
    {p : ZMod 2} {u : M} (hu : u ∈ V.parity p) (v : M) (n : ℤ) :
    mode (V.Y q) 0 (mode (V.Y u) n v) =
      mode (V.Y (mode (V.Y q) 0 u)) n v +
        mode (V.Y (BRST.sgn V u)) n (mode (V.Y q) 0 v) := by
  have h := congrArg (fun f : End ℂ M => f v) (hV hq hu n)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply] at h
  rw [BRST.sgn_homog hu, map_smul, mode_smul, LinearMap.smul_apply]
  have hs : koszul 1 p = parSign p := by simp [koszul]
  rw [hs] at h
  exact sub_eq_iff_eq_add.mp h

/-- An odd zero mode is a derivation on all states. The proof decomposes only
the first argument into its two parity components. -/
theorem odd_zeroMode_deriv {V : SuperVertexAlgebra M}
    (hV : ZeroModeCommutator V) {q : M} (hq : q ∈ V.parity 1)
    (u v : M) (n : ℤ) :
    mode (V.Y q) 0 (mode (V.Y u) n v) =
      mode (V.Y (mode (V.Y q) 0 u)) n v +
        mode (V.Y (BRST.sgn V u)) n (mode (V.Y q) 0 v) := by
  obtain ⟨u₀, h₀, u₁, h₁, rfl⟩ := (BRST.parGrading V).exists_parity_decomp u
  have h0 := odd_zeroMode_deriv_homogeneous hV hq h₀ v n
  have h1 := odd_zeroMode_deriv_homogeneous hV hq h₁ v n
  simp only [map_add, mode_add, LinearMap.add_apply]
  rw [h0, h1]
  abel

/-- An even zero mode is an ordinary derivation, also on inhomogeneous states. -/
theorem even_zeroMode_deriv {V : SuperVertexAlgebra M}
    (hV : ZeroModeCommutator V) {q : M} (hq : q ∈ V.parity 0)
    (u v : M) (n : ℤ) :
    mode (V.Y q) 0 (mode (V.Y u) n v) =
      mode (V.Y (mode (V.Y q) 0 u)) n v +
        mode (V.Y u) n (mode (V.Y q) 0 v) := by
  have hom : ∀ {p : ZMod 2} {w : M}, w ∈ V.parity p →
      mode (V.Y q) 0 (mode (V.Y w) n v) =
        mode (V.Y (mode (V.Y q) 0 w)) n v +
          mode (V.Y w) n (mode (V.Y q) 0 v) := by
    intro p w hw
    have h := congrArg (fun f : End ℂ M => f v) (hV hq hw n)
    simp only [koszul_zero_left, one_smul, LinearMap.sub_apply,
      Module.End.mul_apply] at h
    exact sub_eq_iff_eq_add.mp h
  obtain ⟨u₀, h₀, u₁, h₁, rfl⟩ := (BRST.parGrading V).exists_parity_decomp u
  simp only [map_add, mode_add, LinearMap.add_apply]
  rw [hom h₀, hom h₁]
  abel

/-- The square of an odd residue is one half the residue of its zero product
with itself. This does not assert that either side vanishes. -/
theorem odd_zeroMode_square {V : SuperVertexAlgebra M}
    (hV : ZeroModeCommutator V) {q : M} (hq : q ∈ V.parity 1) :
    mode (V.Y q) 0 * mode (V.Y q) 0 =
      (1 / 2 : ℂ) • mode (V.Y (mode (V.Y q) 0 q)) 0 := by
  have h := hV hq hq 0
  rw [koszul_one_one, neg_one_smul, sub_neg_eq_add] at h
  rw [← h, smul_add]
  module

variable {V : SuperVertexAlgebra M} {k : ℂ}

/-- The actual semi-infinite residue is a super derivation if the tensor SVA
has the all-fields zero-mode commutator formula. This hypothesis is stronger
than the bare matter-current commutator and is explicitly retained. -/
theorem semiInfiniteQ_deriv (A : AffineSl2Action V k)
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (hcomm : ZeroModeCommutator (matterGhostSVA V hV hg))
    (u v : M ⊗[ℂ] Sl2GhostSpace) (n : ℤ) :
    semiInfiniteQ A (mode ((matterGhostSVA V hV hg).Y u) n v) =
      mode ((matterGhostSVA V hV hg).Y (semiInfiniteQ A u)) n v +
        mode ((matterGhostSVA V hV hg).Y (BRST.sgn (matterGhostSVA V hV hg) u)) n
          (semiInfiniteQ A v) :=
  odd_zeroMode_deriv hcomm (brstState_odd A) u v n

/-- Exact square reduction for the actual tensor charge, with its state-field
compatibility hypothesis visible. The level has not yet been specialized. -/
theorem semiInfiniteQ_square_eq_residue (A : AffineSl2Action V k)
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (hcomm : ZeroModeCommutator (matterGhostSVA V hV hg)) :
    semiInfiniteQ A * semiInfiniteQ A =
      (1 / 2 : ℂ) • mode (TensorVA.tenY V sl2GhostSVA (semiInfiniteQ A (brstState A))) 0 :=
  odd_zeroMode_square hcomm (brstState_odd A)

/-- The all-fields commutator on matter times ghosts follows from translation
covariance of matter. The ghost compatibility and tensor transfer are proved. -/
theorem matterGhost_zeroModeCommutator (H : TranslationCovariant V)
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA) :
    ZeroModeCommutator (matterGhostSVA V hV hg) :=
  zeroModeCommutator_of_translation
    (translationCovariant_tensorSVA H translationCovariant_sl2GhostSVA
      hV parityCompatible_sl2GhostSVA hg)

/-- The BRST derivation obligation is discharged for translated matter,
without requiring a BRST-specific commutator or a nilpotency hypothesis. -/
theorem semiInfiniteQ_deriv_of_translation (A : TranslatedAffineSl2Action V k)
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (u v : M ⊗[ℂ] Sl2GhostSpace) (n : ℤ) :
    semiInfiniteQ A.toAffineSl2Action (mode ((matterGhostSVA V hV hg).Y u) n v) =
      mode ((matterGhostSVA V hV hg).Y (semiInfiniteQ A.toAffineSl2Action u)) n v +
        mode ((matterGhostSVA V hV hg).Y (BRST.sgn (matterGhostSVA V hV hg) u)) n
          (semiInfiniteQ A.toAffineSl2Action v) :=
  semiInfiniteQ_deriv A.toAffineSl2Action hV hg
    (matterGhost_zeroModeCommutator A.translation hV hg) u v n

end VOA.Sl2SemiInfinite
