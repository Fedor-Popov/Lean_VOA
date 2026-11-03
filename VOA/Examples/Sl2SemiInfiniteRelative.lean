/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteDifferential
import VOA.Examples.Sl2SemiInfiniteGhostEmbeddings

/-!
# The relative semi-infinite carrier and its Cartan reduction

The relative carrier is the intersection of the three actual total-current
zero-mode kernels and the three actual antighost zero-mode kernels. It contains
the tensor vacuum. The operators are defined from the tensor state-field map,
with no independently postulated action.

This file gives the stability reduction using two explicitly displayed
finite-state Cartan calculations and the all-fields zero-mode commutator.
`Sl2SemiInfiniteRelativeCharge` proves the antighost identity, and
`Sl2SemiInfiniteComplex` proves the second identity and relative stability at
level `-4` from actual nilpotency. No square-zero hypothesis is introduced here.
-/

namespace VOA.Sl2SemiInfinite

open Module (End)
open scoped TensorProduct

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}

/-- Matter plus ghost current state for the diagonal horizontal action. -/
noncomputable def totalCurrentState (A : AffineSl2Action V k) (a : Fin 3) :
    M ⊗[ℂ] Sl2GhostSpace :=
  A.current a ⊗ₜ[ℂ] sl2GhostSVA.vacuum + V.vacuum ⊗ₜ[ℂ] ghostCurrent a

/-- The antighost state in the tensor algebra. -/
noncomputable def tensorAntighost (V : SuperVertexAlgebra M) (a : Fin 3) :
    M ⊗[ℂ] Sl2GhostSpace := V.vacuum ⊗ₜ[ℂ] bGhost a

/-- The total horizontal current, with mode index zero. -/
noncomputable def totalCurrentZero (A : AffineSl2Action V k) (a : Fin 3) :
    End ℂ (M ⊗[ℂ] Sl2GhostSpace) :=
  mode (TensorVA.tenY V sl2GhostSVA (totalCurrentState A a)) 0

/-- The actual antighost zero mode, including the tensor Koszul sign. -/
noncomputable def antighostZero (V : SuperVertexAlgebra M) (a : Fin 3) :
    End ℂ (M ⊗[ℂ] Sl2GhostSpace) :=
  mode (TensorVA.tenY V sl2GhostSVA (tensorAntighost V a)) 0

/-- The six simultaneous kernel conditions defining relative states. -/
noncomputable def relativeCarrier (A : AffineSl2Action V k) :
    Submodule ℂ (M ⊗[ℂ] Sl2GhostSpace) :=
  (⨅ a : Fin 3, LinearMap.ker (totalCurrentZero A a)) ⊓
    ⨅ a : Fin 3, LinearMap.ker (antighostZero V a)

theorem mem_relativeCarrier (A : AffineSl2Action V k) (x : M ⊗[ℂ] Sl2GhostSpace) :
    x ∈ relativeCarrier A ↔
      (∀ a, totalCurrentZero A a x = 0) ∧ (∀ a, antighostZero V a x = 0) := by
  simp [relativeCarrier, Submodule.mem_iInf, LinearMap.mem_ker]

/-- The relative conditions hold on the vacuum at every matter level. -/
theorem vacuum_mem_relativeCarrier (A : AffineSl2Action V k) :
    V.vacuum ⊗ₜ[ℂ] sl2GhostSVA.vacuum ∈ relativeCarrier A := by
  rw [mem_relativeCarrier]
  constructor <;> intro a
  · change TensorVA.tenY V sl2GhostSVA (totalCurrentState A a) (-1)
      (V.vacuum ⊗ₜ[ℂ] sl2GhostSVA.vacuum) = 0
    exact (TensorVA.tenY_creation V sl2GhostSVA (totalCurrentState A a)).2 (-1)
      (by omega)
  · change TensorVA.tenY V sl2GhostSVA (tensorAntighost V a) (-1)
      (V.vacuum ⊗ₜ[ℂ] sl2GhostSVA.vacuum) = 0
    exact (TensorVA.tenY_creation V sl2GhostSVA (tensorAntighost V a)).2 (-1)
      (by omega)

/-- The total horizontal current is the sum of the two factor actions. -/
theorem totalCurrentZero_tmul (A : AffineSl2Action V k) (a : Fin 3)
    (x : M) (y : Sl2GhostSpace) :
    totalCurrentZero A a (x ⊗ₜ[ℂ] y) =
      mode (V.Y (A.current a)) 0 x ⊗ₜ[ℂ] y +
        x ⊗ₜ[ℂ] mode (ghostCurrentField a) 0 y := by
  unfold totalCurrentZero totalCurrentState
  rw [map_add, mode_add, LinearMap.add_apply]
  change TensorVA.tenY V sl2GhostSVA (A.current a ⊗ₜ[ℂ] sl2GhostSVA.vacuum) (-1)
      (x ⊗ₜ[ℂ] y) +
    TensorVA.tenY V sl2GhostSVA (V.vacuum ⊗ₜ[ℂ] ghostCurrent a) (-1)
      (x ⊗ₜ[ℂ] y) = _
  rw [tenY_left_unit, tenY_right_unit_even V sl2GhostSVA (ghostCurrent_even a)]
  rfl

/-- The antighost zero mode has the sign of the matter parity. -/
theorem antighostZero_tmul (a : Fin 3) {p : ZMod 2} {x : M}
    (hx : x ∈ V.parity p) (y : Sl2GhostSpace) :
    antighostZero V a (x ⊗ₜ[ℂ] y) =
      koszul 1 p • (x ⊗ₜ[ℂ] mode (sl2GhostSVA.Y (bGhost a)) 0 y) := by
  change TensorVA.tenY V sl2GhostSVA (V.vacuum ⊗ₜ[ℂ] bGhost a) (-1)
    (x ⊗ₜ[ℂ] y) = _
  rw [TensorVA.tenY_tmul_parity V sl2GhostSVA V.vacuum (bGhost_odd a),
    TensorVA.kappaTen_tmul, (TensorVA.parGr V).koszulOp_homog 1 hx,
    ← TensorProduct.smul_tmul', map_smul, TensorVA.rawCoeff_tmul]
  congr 1
  rw [finsum_eq_single _ 0 (fun j hj => by
    rw [DSMor.Y_vacuum_applySVA, if_neg hj, TensorProduct.zero_tmul])]
  rw [sub_zero, DSMor.Y_vacuum_applySVA, if_pos rfl]
  rfl

theorem totalCurrentState_even (A : AffineSl2Action V k) (a : Fin 3) :
    totalCurrentState A a ∈ TensorVA.tenParity V sl2GhostSVA 0 := by
  apply Submodule.add_mem
  · exact TensorVA.tmul_mem_tenParity V sl2GhostSVA (A.current_even a)
      sl2GhostSVA.vacuum_parity
  · exact TensorVA.tmul_mem_tenParity V sl2GhostSVA V.vacuum_parity
      (ghostCurrent_even a)

theorem tensorAntighost_odd (a : Fin 3) :
    tensorAntighost V a ∈ TensorVA.tenParity V sl2GhostSVA 1 :=
  TensorVA.tmul_mem_tenParity V sl2GhostSVA V.vacuum_parity (bGhost_odd a)

/-- The relative carrier is closed under every vertex product for translated
matter. This uses the even and odd zero-mode derivations and does not require
any BRST or Cartan calculation. -/
theorem relativeCarrier_mode (A : AffineSl2Action V k) (H : TranslationCovariant V)
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    {u v : M ⊗[ℂ] Sl2GhostSpace} (hu : u ∈ relativeCarrier A)
    (hv : v ∈ relativeCarrier A) (n : ℤ) :
    mode (TensorVA.tenY V sl2GhostSVA u) n v ∈ relativeCarrier A := by
  rw [mem_relativeCarrier] at hu hv ⊢
  have hcomm : ZeroModeCommutator (matterGhostSVA V hV hg) :=
    matterGhost_zeroModeCommutator H hV hg
  constructor
  · intro a
    have h := even_zeroMode_deriv hcomm (totalCurrentState_even A a) u v n
    change totalCurrentZero A a (mode (TensorVA.tenY V sl2GhostSVA u) n v) =
      mode (TensorVA.tenY V sl2GhostSVA (totalCurrentZero A a u)) n v +
        mode (TensorVA.tenY V sl2GhostSVA u) n (totalCurrentZero A a v) at h
    simpa only [hu.1 a, hv.1 a, map_zero, mode_zero, LinearMap.zero_apply, add_zero] using h
  · intro a
    have h := odd_zeroMode_deriv hcomm (tensorAntighost_odd (V := V) a) u v n
    change antighostZero V a (mode (TensorVA.tenY V sl2GhostSVA u) n v) =
      mode (TensorVA.tenY V sl2GhostSVA (antighostZero V a u)) n v +
        mode (TensorVA.tenY V sl2GhostSVA (BRST.sgn (matterGhostSVA V hV hg) u)) n
          (antighostZero V a v) at h
    simpa only [hu.2 a, hv.2 a, map_zero, mode_zero, LinearMap.zero_apply, add_zero] using h

/-- The finite state Cartan identity implies the full anticommutator of the
actual charge with an actual antighost zero mode. -/
theorem semiInfiniteQ_antighostZero (A : AffineSl2Action V k)
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (hcomm : ZeroModeCommutator (matterGhostSVA V hV hg)) (a : Fin 3)
    (hb : semiInfiniteQ A (tensorAntighost V a) = totalCurrentState A a) :
    semiInfiniteQ A * antighostZero V a + antighostZero V a * semiInfiniteQ A =
      totalCurrentZero A a := by
  have h := hcomm (brstState_odd A) (tensorAntighost_odd (V := V) a) 0
  change semiInfiniteQ A * antighostZero V a -
      koszul 1 1 • (antighostZero V a * semiInfiniteQ A) =
    mode (TensorVA.tenY V sl2GhostSVA (semiInfiniteQ A (tensorAntighost V a))) 0 at h
  simpa only [koszul_one_one, neg_one_smul, sub_neg_eq_add, hb] using h

/-- The finite state invariance calculation implies commutation of the charge
with the total horizontal action. -/
theorem semiInfiniteQ_totalCurrentZero (A : AffineSl2Action V k)
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (hcomm : ZeroModeCommutator (matterGhostSVA V hV hg)) (a : Fin 3)
    (hJ : semiInfiniteQ A (totalCurrentState A a) = 0) :
    semiInfiniteQ A * totalCurrentZero A a = totalCurrentZero A a * semiInfiniteQ A := by
  have h := hcomm (brstState_odd A) (totalCurrentState_even A a) 0
  change semiInfiniteQ A * totalCurrentZero A a -
      koszul 1 0 • (totalCurrentZero A a * semiInfiniteQ A) =
    mode (TensorVA.tenY V sl2GhostSVA (semiInfiniteQ A (totalCurrentState A a))) 0 at h
  rw [koszul_zero_right, one_smul, hJ, map_zero] at h
  exact sub_eq_zero.mp h

/-- Relative states are preserved once the two finite state Cartan
calculations are supplied. These calculations remain explicit hypotheses;
this theorem does not claim that they have been proved for the cubic charge. -/
theorem semiInfiniteQ_mem_relativeCarrier_of_cartan (A : AffineSl2Action V k)
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (hcomm : ZeroModeCommutator (matterGhostSVA V hV hg))
    (hb : ∀ a, semiInfiniteQ A (tensorAntighost V a) = totalCurrentState A a)
    (hJ : ∀ a, semiInfiniteQ A (totalCurrentState A a) = 0)
    {x : M ⊗[ℂ] Sl2GhostSpace} (hx : x ∈ relativeCarrier A) :
    semiInfiniteQ A x ∈ relativeCarrier A := by
  rw [mem_relativeCarrier] at hx ⊢
  constructor
  · intro a
    have h := congrArg (fun f : End ℂ (M ⊗[ℂ] Sl2GhostSpace) => f x)
      (semiInfiniteQ_totalCurrentZero A hV hg hcomm a (hJ a))
    simpa only [Module.End.mul_apply, hx.1 a, map_zero] using h.symm
  · intro a
    have h := congrArg (fun f : End ℂ (M ⊗[ℂ] Sl2GhostSpace) => f x)
      (semiInfiniteQ_antighostZero A hV hg hcomm a (hb a))
    simpa only [LinearMap.add_apply, Module.End.mul_apply, hx.1 a, hx.2 a,
      map_zero, zero_add] using h

/-- For translated matter, only the two concrete finite-state Cartan
calculations remain in the relative stability reduction. -/
theorem semiInfiniteQ_mem_relativeCarrier_of_translation
    (A : TranslatedAffineSl2Action V k)
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (hb : ∀ a, semiInfiniteQ A.toAffineSl2Action (tensorAntighost V a) =
      totalCurrentState A.toAffineSl2Action a)
    (hJ : ∀ a, semiInfiniteQ A.toAffineSl2Action
      (totalCurrentState A.toAffineSl2Action a) = 0)
    {x : M ⊗[ℂ] Sl2GhostSpace} (hx : x ∈ relativeCarrier A.toAffineSl2Action) :
    semiInfiniteQ A.toAffineSl2Action x ∈ relativeCarrier A.toAffineSl2Action :=
  semiInfiniteQ_mem_relativeCarrier_of_cartan A.toAffineSl2Action hV hg
    (matterGhost_zeroModeCommutator A.translation hV hg) hb hJ hx

end VOA.Sl2SemiInfinite
