/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteRelative
import VOA.Examples.Sl2SemiInfiniteCubicMixed
import VOA.Examples.Sl2SemiInfiniteCartan

/-! # The matter contribution to the relative Cartan identity

On a tensor antighost state the matter-current part of the charge contracts
exactly one `c` ghost. The remaining term is the actual cubic ghost residue.
-/

namespace VOA.Sl2SemiInfinite

open Module (End)
open scoped BigOperators TensorProduct

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}

/-- The matter contribution to `Q b` is the matching matter-current state. -/
theorem rawCurrentCharge_vacuum_antighost (A : AffineSl2Action V k) (a b : Fin 3) :
    TensorVA.rawCoeff V sl2GhostSVA (A.current a) (cGhost a) (-1)
      (V.vacuum ⊗ₜ[ℂ] bGhost b) =
      if a = b then A.current a ⊗ₜ[ℂ] sl2GhostSVA.vacuum else 0 := by
  rw [rawCurrentCharge_tmul, finsum_eq_single _ (-1)]
  · rw [(V.creation _).1]
    change A.current a ⊗ₜ[ℂ] mode (sl2GhostSVA.Y (cGhost a)) 0 (bGhost b) = _
    rw [cGhost_bGhost_product a b 0 (by omega)]
    by_cases hab : a = b <;> simp [hab]
  · intro n hn
    by_cases hnonneg : 0 ≤ n
    · rw [(V.creation _).2 n hnonneg, TensorProduct.zero_tmul]
    · rw [cGhost_bGhost_product a b (-n - 1) (by omega),
        if_neg (by omega), TensorProduct.tmul_zero]

/-- The actual charge on an actual tensor antighost. The only unevaluated
term is the cubic ghost residue on that generator. -/
theorem semiInfiniteQ_tensorAntighost_expansion (A : AffineSl2Action V k) (b : Fin 3) :
    semiInfiniteQ A (tensorAntighost V b) =
      A.current b ⊗ₜ[ℂ] sl2GhostSVA.vacuum +
        V.vacuum ⊗ₜ[ℂ] mode (sl2GhostSVA.Y ghostBRSTState) 0 (bGhost b) := by
  rw [tensorAntighost, semiInfiniteQ_eq_modeCharges, Module.End.mul_apply,
    TensorVA.kappaTen_tmul, (TensorVA.parGr V).koszulOp_homog 1 V.vacuum_parity,
    koszul_zero_right, one_smul, LinearMap.add_apply]
  simp only [matterModeCharge, LinearMap.sum_apply, rawCurrentCharge_vacuum_antighost,
    cubicModeCharge, TensorProduct.map_tmul, LinearMap.id_apply]
  simp

/-- The finite state Cartan identity is true for the actual charge at every
level. Its proof uses the concrete matter contraction and cubic ghost product. -/
theorem semiInfiniteQ_tensorAntighost (A : AffineSl2Action V k) (a : Fin 3) :
    semiInfiniteQ A (tensorAntighost V a) = totalCurrentState A a := by
  rw [semiInfiniteQ_tensorAntighost_expansion, ghostBRSTState_zero_bGhost]
  rfl

/-- The actual anticommutator of the charge with each antighost zero mode.
Translation of matter supplies the state-to-field commutator formula. -/
theorem semiInfiniteQ_antighostZero_of_translation (A : TranslatedAffineSl2Action V k)
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (a : Fin 3) :
    semiInfiniteQ A.toAffineSl2Action * antighostZero V a +
        antighostZero V a * semiInfiniteQ A.toAffineSl2Action =
      totalCurrentZero A.toAffineSl2Action a :=
  semiInfiniteQ_antighostZero A.toAffineSl2Action hV hg
    (matterGhost_zeroModeCommutator A.translation hV hg) a
    (semiInfiniteQ_tensorAntighost A.toAffineSl2Action a)

end VOA.Sl2SemiInfinite
