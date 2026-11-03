/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2L0Cov
import VOA.Core.BorcherdsIdentity

/-!
# The affine `𝔰𝔩₂` VOA `𝒱(𝔰𝔩₂, k)` — VOA1 (Sugawara Virasoro) and the closed instance

This file proves the **last** axiom hypothesis of the affine `𝔰𝔩₂` VOA shell — VOA1, the full
Sugawara Virasoro relation
`[Lₘ, Lₙ] = (m−n)·L_{m+n} + δ_{m+n,0}·(m³−m)/12·c·1`,  `c = centralChargeA k = 3k/(k+2)`
(`Lₙ := mode (YA ω)(n+1)`) — and assembles the **closed** instance
`affineSl2VOA_closed k hk : VertexOperatorAlgebra (WakModule k)`.

## Route (`Lₘ`–`Lₙ` Borcherds + current primality)
* **§A — `VARec`.**  A `PreVertexAlgebra`-level reconstruction of the `nth_product`/`mode_commutator`
  chain, parametric in a translation operator `Tr` with operator covariance (breaking the bare-VA
  circularity).  `smul_zero_ge` returns the commutator sum *and* the OPE-order locality vanishing
  `u₍ⱼ₎v = 0` for `j ≥ N`.  `comm_eq_range4` collapses `[Lₘ,Lₙ] = ∑_{j<4} commTermⱼ`.
* **§C — current primality** `mode (YA ω) 2 (J^c₋₁|0⟩) = 0` (a `(-3)`-coefficient finsum collapse to
  `p = -1`, killed by `∑_a fabc(a,c,a) = 0`).
* **§D — current covariance** `[Lₘ, J^c_μ] = -μ J^c_{m+μ}` via `VARec` + primality (`J^c` is a
  weight-`1` primary).
* **§E — the four OPE coefficients** of `T(z)T(w)`: `ω₍₀₎ω = L₋₁ω`, `ω₍₁₎ω = 2ω`, `ω₍₂₎ω = 0`,
  `ω₍₃₎ω = (c/2)|0⟩` (the central charge from the dual-Coxeter Casimir `∑κ⁻¹κ = dim 𝔰𝔩₂ = 3`).
* **§F — VOA1** `hYA_virasoro`, then **§G — the closed instance** `affineSl2VOA_closed`.

## Axioms
`hYA_virasoro` is `pbw`-free (`[propext, Classical.choice, Quot.sound]`), and so is the closed
instance: `#print axioms affineSl2VOA_closed` reports exactly
`[propext, Classical.choice, Quot.sound]` — **no `pbw`**.  (The closed instance does not carry `VOA.pbw` through the vacuum
module.  The distinction matters: `pbw` is the project's single trust boundary, so a VOA resting on it and one
not resting on it have different standing.)  Everything here is `sorry`-free and axiom-clean.

## References
* Gannon §3.2, §5.1.3, §5.2.2 (Sugawara, eq. 5.2.6); Kac §10, §12; Frenkel–Zhu; Lepowsky–Li Ch. 6.
-/

set_option maxHeartbeats 1600000

open VOA VOA.AffineVOA VOA.AffineVOA.SugawaraCov
open scoped BigOperators
open Module (End)
open VOA.AffineLie

namespace VOA.AffineVOA.Vir

/-! ## SUBTASK A — the PreVertexAlgebra instance `affineVA k hk` on `WakModule k` -/

/-- The affine `𝔰𝔩₂` vertex algebra `𝒱(𝔰𝔩₂, k)` from the proved VA1–VA5 axioms.  All seven
fields are theorems already in `AffineSl2Assembly`/`AffineSl2VOA`. -/
noncomputable def affineVA (k : ℂ) (hk : k + 2 ≠ 0) : PreVertexAlgebra (WakModule k) where
  grading := gradingZA k
  isInternal := gradingZA_isInternal k
  finrank := gradingZA_finiteDimensional k
  Y := YA k hk
  vacuum := vacuumA k
  vacuum_mem := vacuumA_mem_gradingZA_zero k
  grading_mode := fun u hu v hv n => hYA_grading k hk u hu v hv n
  vacuum_Y := YA_vacuum k hk
  creation := YA_creation k hk
  locality := YA_local k hk
  regularity := YA_regularity k hk

/-- The vertex map of `affineVA` is definitionally `YA k hk`. -/
theorem affineVA_Y (k : ℂ) (hk : k + 2 ≠ 0) : (affineVA k hk).Y = YA k hk := rfl

/-- The `n`-th product of `affineVA` is `mode (YA u) n v`. -/
theorem affineVA_smul (k : ℂ) (hk : k + 2 ≠ 0) (u : WakModule k) (j : ℤ) (v : WakModule k) :
    (affineVA k hk).smul u j v = mode (YA k hk u) j v := rfl

/-! ### Translation operator facts for `affineVA`

`Ltrans k = mode (YA ω) 0` is the translation operator.  We need:
* `htr` : `⁅Ltrans k, (YA u) s⁆ = (s+1) • (YA u) (s+1)` (operator covariance, the `L_comm_Ycoeff`
  analog), and
* `htrvac` : `Ltrans k |0⟩ = 0`.
Both come from `YA_translation : YA (Ltrans k v) = deriv (YA v)` + `Ltrans_vacuum`. -/

/-- Operator translation covariance, coefficient form (the `L_comm_Ycoeff` analog):
`[Ltrans k, (YA u) s] = (s+1) • (YA u) (s+1)`.  This is exactly `YA_DCov` (the proved
`DCovariant (Ltrans k) (YA u)`) written with the ring bracket. -/
theorem Ltrans_comm_Ycoeff (k : ℂ) (hk : k + 2 ≠ 0) (u : WakModule k) (s : ℤ) :
    ⁅Ltrans k, (YA k hk u) s⁆ = (s + 1) • (YA k hk u) (s + 1) := by
  rw [LieRing.of_associative_ring_bracket]
  exact YA_DCov k hk u s

/-- The translation operator annihilates the vacuum. -/
theorem Ltrans_vac (k : ℂ) : Ltrans k (vacuumA k) = 0 := Ltrans_vacuum k

/-! ## Generic VA-level reconstruction chain (parametric in a translation operator)

We re-prove the `nth_product`/`mode_commutator` chain at the `PreVertexAlgebra` level,
parametric in a translation operator `Tr : End ℂ 𝒱` satisfying the operator covariance
`htr : ⁅Tr, (V.Y u) s⁆ = (s+1) • (V.Y u)(s+1)` and `htrvac : Tr V.vacuum = 0`.  The bare-VA
circularity (`Core.Identities` design note) is broken because we *supply* `htr`. -/

namespace VARec

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- `commL`-style bracket of a two-variable distribution with `Tr`. -/
noncomputable def commLT (Tr : End ℂ 𝒱) (G : FormalDist₂ (End ℂ 𝒱)) : FormalDist₂ (End ℂ 𝒱) :=
  fun s t => ⁅Tr, G s t⁆

/-- Taking a coefficient of the distribution commutator means taking the
commutator of that coefficient with the supplied translation operator. -/
@[simp] theorem commLT_apply (Tr : End ℂ 𝒱) (G : FormalDist₂ (End ℂ 𝒱)) (s t : ℤ) :
    commLT Tr G s t = ⁅Tr, G s t⁆ := rfl

/-- Multiplication by the formal variable difference commutes with taking
the translation commutator, since translation acts on operator coefficients. -/
theorem commLT_mulBySub (Tr : End ℂ 𝒱) (G : FormalDist₂ (End ℂ 𝒱)) :
    commLT Tr (mulBySub G) = mulBySub (commLT Tr G) := by
  apply FormalDist₂.ext; intro s t
  simp only [commLT_apply, mulBySub_apply, lie_sub]

/-- The same compatibility holds for every power of the variable difference.
This allows extraction of higher OPE coefficients after taking translation. -/
theorem commLT_mulBySubPow (Tr : End ℂ 𝒱) (j : ℕ) (G : FormalDist₂ (End ℂ 𝒱)) :
    commLT Tr (mulBySubPow j G) = mulBySubPow j (commLT Tr G) := by
  induction j generalizing G with
  | zero => rfl
  | succ p ih => rw [mulBySubPow_succ, LinearMap.comp_apply, commLT_mulBySub, ih,
      ← LinearMap.comp_apply, ← mulBySubPow_succ]

/-- Translation covariance of the OPE bracket: `[Tr, [Y(u),Y(v)]] = ∂[Y(u),Y(v)]`. -/
theorem commLT_bracketDist (V : PreVertexAlgebra 𝒱) (Tr : End ℂ 𝒱)
    (htr : ∀ (u : 𝒱) (s : ℤ), ⁅Tr, (V.Y u) s⁆ = (s + 1) • (V.Y u) (s + 1)) (u v : 𝒱) :
    commLT Tr (bracketDist (V.Y u) (V.Y v)) = deriv2 (bracketDist (V.Y u) (V.Y v)) := by
  have leib : ∀ (a b c : End ℂ 𝒱), ⁅a, b * c⁆ = ⁅a, b⁆ * c + b * ⁅a, c⁆ := fun a b c => by
    simp only [LieRing.of_associative_ring_bracket]; noncomm_ring
  apply FormalDist₂.ext; intro s t
  simp only [commLT_apply, deriv2_apply, bracketDist_apply, lie_sub, leib, htr,
    smul_mul_assoc, mul_smul_comm, smul_sub]
  abel

/-- The recursion `[Tr, A_m] = (m+1)•A_{m+1}` for `A = cCoeff k (bracketDist (Yu)(Yv))`. -/
theorem Tr_comm_cCoeff (V : PreVertexAlgebra 𝒱) (Tr : End ℂ 𝒱)
    (htr : ∀ (u : 𝒱) (s : ℤ), ⁅Tr, (V.Y u) s⁆ = (s + 1) • (V.Y u) (s + 1))
    (u v : 𝒱) (k : ℕ) (m : ℤ) :
    ⁅Tr, cCoeff k (bracketDist (V.Y u) (V.Y v)) m⁆
      = (m + 1) • cCoeff k (bracketDist (V.Y u) (V.Y v)) (m + 1) := by
  show commLT Tr (mulBySubPow k (bracketDist (V.Y u) (V.Y v))) (-1) m = _
  rw [commLT_mulBySubPow, commLT_bracketDist V Tr htr, resByParts]
  rfl

/-! ### Vacuum action of the field `k`-th product -/

/-- Both products in the field commutator kill the vacuum in this coefficient
quadrant. The statement uses the package's Laurent coefficient convention. -/
theorem applyVec_bracketDist_quadrant (V : PreVertexAlgebra 𝒱) (u v : 𝒱) (s t : ℤ)
    (hs : s ≤ -1) (ht : t ≤ -1) :
    applyVec V.vacuum (bracketDist (V.Y u) (V.Y v)) s t = 0 := by
  rw [applyVec_apply, bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, PreVertexAlgebra.Y_apply_vacuum_eq_zero V v (by omega),
    PreVertexAlgebra.Y_apply_vacuum_eq_zero V u (by omega), map_zero, map_zero, sub_zero]

/-- Extracting an OPE coefficient and applying it to the vacuum can be done
in either order. The right side is a vector-valued distribution calculation. -/
theorem cCoeff_apply_vacuum (V : PreVertexAlgebra 𝒱) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    cCoeff k (bracketDist (V.Y u) (V.Y v)) m V.vacuum
      = mulBySubPow k (applyVec V.vacuum (bracketDist (V.Y u) (V.Y v))) (-1) m := by
  show mulBySubPow k (bracketDist (V.Y u) (V.Y v)) (-1) m V.vacuum = _
  rw [← applyVec_apply, applyVec_mulBySubPow]

/-- The extracted OPE coefficient field has no negative Laurent powers on
the vacuum. This is the regularity part of the creation condition. -/
theorem cCoeff_vacuum_neg (V : PreVertexAlgebra 𝒱) (u v : 𝒱) (k : ℕ) {m : ℤ} (hm : m < 0) :
    cCoeff k (bracketDist (V.Y u) (V.Y v)) m V.vacuum = 0 := by
  rw [cCoeff_apply_vacuum]
  exact mulBySubPow_zero_of_quadrant (applyVec_bracketDist_quadrant V u v) k (-1) m (by omega)
    (by omega)

/-- The constant vacuum coefficient of the kth OPE field is the state u_(k)v.
This identifies which state the reconstructed coefficient field must represent. -/
theorem cCoeff_vacuum_base (V : PreVertexAlgebra 𝒱) (u v : 𝒱) (k : ℕ) :
    cCoeff k (bracketDist (V.Y u) (V.Y v)) 0 V.vacuum = V.smul u k v := by
  rw [cCoeff_apply_vacuum,
    mulBySubPow_diag_of_quadrant (applyVec_bracketDist_quadrant V u v) k (-1) (by omega),
    applyVec_apply, bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, PreVertexAlgebra.Y_apply_vacuum_zero,
    PreVertexAlgebra.Y_apply_vacuum_eq_zero V u (by omega), map_zero, sub_zero]
  rw [PreVertexAlgebra.smul_def, mode_apply, show (-1 - (k : ℤ)) = -(k : ℤ) - 1 from by ring]

/-- The vacuum condition for the field `k`-th product. -/
theorem cCoeff_vacuum_eq (V : PreVertexAlgebra 𝒱) (Tr : End ℂ 𝒱)
    (htr : ∀ (u : 𝒱) (s : ℤ), ⁅Tr, (V.Y u) s⁆ = (s + 1) • (V.Y u) (s + 1))
    (htrvac : Tr V.vacuum = 0) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    cCoeff k (bracketDist (V.Y u) (V.Y v)) m V.vacuum = (V.Y (V.smul u k v)) m V.vacuum := by
  by_cases hm : m < 0
  · rw [cCoeff_vacuum_neg V u v k hm,
      PreVertexAlgebra.Y_apply_vacuum_eq_zero V (V.smul u k v) hm]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = (j : ℤ) := ⟨m.toNat, by omega⟩
    clear hm
    induction j with
    | zero =>
        rw [Nat.cast_zero, cCoeff_vacuum_base]
        exact (PreVertexAlgebra.Y_apply_vacuum_zero _ _).symm
    | succ i ih =>
        have expand : ∀ (X : End ℂ 𝒱), ⁅Tr, X⁆ V.vacuum = Tr (X V.vacuum) := by
          intro X
          rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
            Module.End.mul_apply, htrvac, map_zero, sub_zero]
        have hA := DFunLike.congr_fun (congrArg (fun (e : End ℂ 𝒱) => e)
          (Tr_comm_cCoeff V Tr htr u v k (i : ℤ))) V.vacuum
        -- Y(u₍ₖ₎v) is also Tr-covariant via htr.
        have hB : ⁅Tr, (V.Y (V.smul u k v)) (i : ℤ)⁆
            = ((i : ℤ) + 1) • (V.Y (V.smul u k v)) ((i : ℤ) + 1) := htr (V.smul u k v) (i : ℤ)
        have hBapp := DFunLike.congr_fun (congrArg (fun (e : End ℂ 𝒱) => e) hB) V.vacuum
        rw [expand, LinearMap.smul_apply] at hA hBapp
        have key : ((i : ℤ) + 1) • cCoeff k (bracketDist (V.Y u) (V.Y v)) ((i : ℤ) + 1) V.vacuum
            = ((i : ℤ) + 1) • (V.Y (V.smul u k v)) ((i : ℤ) + 1) V.vacuum := by
          rw [← hA, ih, hBapp]
        have hc : (((i : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
        rw [← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1),
          ← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1)] at key
        rw [Nat.cast_succ]
        exact smul_right_injective 𝒱 hc key

/-- **The field `n`-th-product theorem** at the VA level (parametric in `Tr`):
`cCoeff k (bracketDist (Yu)(Yv)) = Y(u₍ₖ₎v)`. -/
theorem nth_product (V : PreVertexAlgebra 𝒱) (Tr : End ℂ 𝒱)
    (htr : ∀ (u : 𝒱) (s : ℤ), ⁅Tr, (V.Y u) s⁆ = (s + 1) • (V.Y u) (s + 1))
    (htrvac : Tr V.vacuum = 0) (u v : 𝒱) (k : ℕ) :
    cCoeff k (bracketDist (V.Y u) (V.Y v)) = V.Y (V.smul u k v) := by
  refine V.goddard_uniqueness _ (V.smul u k v) ?_ (cCoeff_vacuum_eq V Tr htr htrvac u v k)
  intro b
  exact dong_nonneg (V.locality u v) (V.locality u b) (V.locality v b) k

/-- **The commutator formula** at the VA level (parametric in `Tr`):
`[u₍ₐ₎, v₍ᵦ₎] = ∑_j C(a,j)·(u₍ⱼ₎v)₍ₐ₊ᵦ₋ⱼ₎`. -/
theorem mode_commutator (V : PreVertexAlgebra 𝒱) (Tr : End ℂ 𝒱)
    (htr : ∀ (u : 𝒱) (s : ℤ), ⁅Tr, (V.Y u) s⁆ = (s + 1) • (V.Y u) (s + 1))
    (htrvac : Tr V.vacuum = 0) (u v : 𝒱) (a b : ℤ) :
    ∃ N : ℕ, ⁅mode (V.Y u) a, mode (V.Y v) b⁆
      = ∑ j : Fin N, gBinom a (j : ℕ) • mode (V.Y (V.smul u (j : ℕ) v)) (a + b - (j : ℕ)) := by
  obtain ⟨N, c, hdecomp⟩ := bracket_deltaSum V u v
  refine ⟨N, ?_⟩
  rw [mode_bracket_ope V u v hdecomp a b]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hne : ((j : ℕ).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hcj : c j = (((j : ℕ).factorial : ℂ)⁻¹) • V.Y (V.smul u (j : ℕ) v) := by
    have hrec := cCoeff_deltaSum c j
    rw [← hdecomp, nth_product V Tr htr htrvac] at hrec
    rw [hrec, ← Int.cast_smul_eq_zsmul ℂ ((j : ℕ).factorial : ℤ), Int.cast_natCast, smul_smul,
      inv_mul_cancel₀ hne, one_smul]
  rw [hcj, mode_smul,
    ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range (j : ℕ), (a - (i : ℤ))), smul_smul]
  congr 1
  rw [gBinom, div_eq_mul_inv]
  congr 1
  push_cast
  rfl

/-- **The commutator formula together with the locality bound** (parametric in `Tr`): the same
finite sum as `mode_commutator`, *and* the locality vanishing `u₍ⱼ₎v = 0` for `j ≥ N` (the OPE
order).  The vanishing comes from `cCoeff j (bracketDist) = Y(u₍ⱼ₎v) = 0` for `j ≥ N` (a
`δ`-derivative decomposition of order `N`), plus creation `Y w = 0 ⟹ w = 0`. -/
theorem smul_zero_ge (V : PreVertexAlgebra 𝒱) (Tr : End ℂ 𝒱)
    (htr : ∀ (u : 𝒱) (s : ℤ), ⁅Tr, (V.Y u) s⁆ = (s + 1) • (V.Y u) (s + 1))
    (htrvac : Tr V.vacuum = 0) (u v : 𝒱) (a b : ℤ) :
    ∃ N : ℕ, (⁅mode (V.Y u) a, mode (V.Y v) b⁆
      = ∑ j : Fin N, gBinom a (j : ℕ) • mode (V.Y (V.smul u (j : ℕ) v)) (a + b - (j : ℕ)))
      ∧ ∀ j : ℕ, N ≤ j → V.smul u j v = 0 := by
  obtain ⟨N, c, hdecomp⟩ := bracket_deltaSum V u v
  refine ⟨N, ?_, ?_⟩
  · rw [mode_bracket_ope V u v hdecomp a b]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hne : ((j : ℕ).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hcj : c j = (((j : ℕ).factorial : ℂ)⁻¹) • V.Y (V.smul u (j : ℕ) v) := by
      have hrec := cCoeff_deltaSum c j
      rw [← hdecomp, nth_product V Tr htr htrvac] at hrec
      rw [hrec, ← Int.cast_smul_eq_zsmul ℂ ((j : ℕ).factorial : ℤ), Int.cast_natCast, smul_smul,
        inv_mul_cancel₀ hne, one_smul]
    rw [hcj, mode_smul,
      ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range (j : ℕ), (a - (i : ℤ))), smul_smul]
    congr 1
    rw [gBinom, div_eq_mul_inv]
    congr 1
    push_cast
    rfl
  · intro j hj
    have hY : V.Y (V.smul u j v) = cCoeff j (bracketDist (V.Y u) (V.Y v)) :=
      (nth_product V Tr htr htrvac u v j).symm
    rw [hdecomp, cCoeff_sum] at hY
    have hzero : (∑ i : Fin N, cCoeff j (deltaDeriv (i : ℕ) (c i)))
        = (0 : FormalDist (End ℂ 𝒱)) := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [cCoeff_deltaDeriv, if_neg (by have := i.isLt; omega : ¬ (i : ℕ) = j)]
    rw [hzero] at hY
    have hcre := (V.creation (V.smul u j v)).1
    rw [hY, mode_zero, LinearMap.zero_apply] at hcre
    exact hcre.symm

end VARec

/-! ## Specialization to the affine Sugawara modes -/

/-- `ω₍ⱼ₎ω = mode (YA ω) j ω`, the state the commutator formula feeds into `YA`. -/
noncomputable def omegaJomega (k : ℂ) (hk : k + 2 ≠ 0) (j : ℤ) : WakModule k :=
  mode (YA k hk (omegaA k)) j (omegaA k)

/-- The explicitly named Sugawara self-product is the same state product
provided by the affine vertex algebra structure. -/
theorem omegaJomega_eq (k : ℂ) (hk : k + 2 ≠ 0) (j : ℤ) :
    omegaJomega k hk j = (affineVA k hk).smul (omegaA k) j (omegaA k) := rfl

/-- `ω₍ⱼ₎ω ∈ gradingZA (3-j)` (VA1, since `ω ∈ gradingZA 2`). -/
theorem omegaJomega_mem (k : ℂ) (hk : k + 2 ≠ 0) (j : ℤ) :
    omegaJomega k hk j ∈ gradingZA k (3 - j) := by
  have h := hYA_grading k hk (omegaA k) (omegaA_mem k) (omegaA k) (omegaA_mem k) j
  rwa [show (2 : ℤ) + 2 - j - 1 = 3 - j from by ring] at h

/-- For `j ≥ 4`, `ω₍ⱼ₎ω = 0` (lands in negative degree). -/
theorem omegaJomega_eq_zero (k : ℂ) (hk : k + 2 ≠ 0) {j : ℤ} (hj : 4 ≤ j) :
    omegaJomega k hk j = 0 := by
  have hmem := omegaJomega_mem k hk j
  rw [gradingZA_positivity k (3 - j) (by omega), Submodule.mem_bot] at hmem
  exact hmem

/-- `ω₍₁₎ω = 2 • ω` (since `L₀ω = mode(YA ω) 1 ω = 2ω`, ω ∈ gradingZA 2). -/
theorem omegaJomega_one (k : ℂ) (hk : k + 2 ≠ 0) :
    omegaJomega k hk 1 = (2 : ℂ) • omegaA k := by
  rw [omegaJomega, hYA_L0 k hk (omegaA k) (omegaA_mem k)]
  norm_num

/-- `ω₍₀₎ω = Ltrans k ω` (the `L₋₁`-descendant; `mode (YA ω) 0 = Ltrans k`). -/
theorem omegaJomega_zero (k : ℂ) (hk : k + 2 ≠ 0) :
    omegaJomega k hk 0 = Ltrans k (omegaA k) := by
  rw [omegaJomega, mode_YA_omega_zero]

/-- `mode (YA (ω₍₀₎ω)) c = -(c:ℂ) • mode (YA ω) (c-1)` (the `j=0` translation term):
`YA(ω₍₀₎ω) = YA(L₋₁ω) = ∂(YA ω)`, then `mode (∂ g) c = -c • mode g (c-1)`. -/
theorem mode_YA_omegaJomega_zero (k : ℂ) (hk : k + 2 ≠ 0) (c : ℤ) :
    mode (YA k hk (omegaJomega k hk 0)) c = (-(c : ℂ)) • mode (YA k hk (omegaA k)) (c - 1) := by
  rw [omegaJomega_zero, ← mode_YA_omega_zero k hk, hYA_translation k hk, mode_deriv,
    ← Int.cast_smul_eq_zsmul ℂ (-c)]
  push_cast
  rfl

/-! ## The commutator sum collapses to `j ∈ {0,1,2,3}` -/

/-- The `j`-th term of the commutator formula, as a function of `j : ℕ`. -/
noncomputable def commTerm (k : ℂ) (hk : k + 2 ≠ 0) (m n : ℤ) (j : ℕ) : End ℂ (WakModule k) :=
  gBinom (m + 1) j • mode (YA k hk (omegaJomega k hk (j : ℤ))) (m + 1 + (n + 1) - (j : ℤ))

/-- The commutator term vanishes for `j ≥ 4` (the state `ω₍ⱼ₎ω = 0`). -/
theorem commTerm_eq_zero (k : ℂ) (hk : k + 2 ≠ 0) (m n : ℤ) {j : ℕ} (hj : 4 ≤ j) :
    commTerm k hk m n j = 0 := by
  rw [commTerm, omegaJomega_eq_zero k hk (by exact_mod_cast hj), map_zero]
  show gBinom (m + 1) j • mode (0 : FormalDist (End ℂ (WakModule k)))
      (m + 1 + (n + 1) - (j : ℤ)) = 0
  rw [mode_zero, smul_zero]

/-- The commutator term vanishes when `ω₍ⱼ₎ω = 0` (the OPE-order locality vanishing, `j ≥ N`). -/
theorem commTerm_zero_of_smul_zero (k : ℂ) (hk : k + 2 ≠ 0) (m n : ℤ) {j : ℕ}
    (h : (affineVA k hk).smul (omegaA k) (j : ℤ) (omegaA k) = 0) : commTerm k hk m n j = 0 := by
  rw [commTerm, show omegaJomega k hk (j : ℤ) = 0 from by rw [omegaJomega_eq]; exact h, map_zero]
  show gBinom (m + 1) j • mode (0 : FormalDist (End ℂ (WakModule k)))
      (m + 1 + (n + 1) - (j : ℤ)) = 0
  rw [mode_zero, smul_zero]

/-- **The commutator formula collapsed**: `[Lₘ, Lₙ] = ∑_{j<4} commTerm j`.  Robust to the OPE
order `N`: terms with `j ≥ 4` vanish (`commTerm_eq_zero`, grading) and terms with `N ≤ j < 4`
vanish (`commTerm_zero_of_smul_zero`, locality), so `range N` and `range 4` agree either way. -/
theorem comm_eq_range4 (k : ℂ) (hk : k + 2 ≠ 0) (m n : ℤ) :
    ⁅mode (YA k hk (omegaA k)) (m + 1), mode (YA k hk (omegaA k)) (n + 1)⁆
      = ∑ j ∈ Finset.range 4, commTerm k hk m n j := by
  obtain ⟨N, hN, hvan⟩ := VARec.smul_zero_ge (affineVA k hk) (Ltrans k)
    (fun u s => Ltrans_comm_Ycoeff k hk u s) (Ltrans_vac k) (omegaA k) (omegaA k) (m + 1) (n + 1)
  rw [show (affineVA k hk).Y = YA k hk from rfl] at hN
  rw [hN]
  rw [show (∑ j : Fin N, gBinom (m + 1) (j : ℕ)
        • mode (YA k hk ((affineVA k hk).smul (omegaA k) (j : ℕ) (omegaA k)))
            (m + 1 + (n + 1) - (j : ℕ)))
      = ∑ j ∈ Finset.range N, commTerm k hk m n j from by
    rw [← Fin.sum_univ_eq_sum_range (fun j => commTerm k hk m n j) N]
    rfl]
  rcases le_total N 4 with hle | hle
  · refine Finset.sum_subset
      (fun j hj => Finset.mem_range.mpr (by rw [Finset.mem_range] at hj; omega))
      (fun j _ hjn => ?_)
    rw [Finset.mem_range, not_lt] at hjn
    exact commTerm_zero_of_smul_zero k hk m n (hvan j hjn)
  · refine (Finset.sum_subset
      (fun j hj => Finset.mem_range.mpr (by rw [Finset.mem_range] at hj; omega))
      (fun j _ hj4 => ?_)).symm
    rw [Finset.mem_range, not_lt] at hj4
    exact commTerm_eq_zero k hk m n hj4

/-! ## §B  Generalized binomial values `gBinom (n) k` for `k = 1, 2, 3` -/

/-- The first generalized binomial coefficient is n, for any integer n.
This remains valid for negative mode indices. -/
theorem gBinom_one (n : ℤ) : gBinom n 1 = (n : ℂ) := by
  simp [gBinom]

/-- The second generalized binomial coefficient is n(n-1)/2. This explicit
polynomial supplies the quadratic mode coefficient in the commutator. -/
theorem gBinom_two (n : ℤ) : gBinom n 2 = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
  simp [gBinom, Finset.prod_range_succ]

/-- The third generalized binomial coefficient is n(n-1)(n-2)/6. It provides
the cubic polynomial needed in the Virasoro central term. -/
theorem gBinom_three (n : ℤ) :
    gBinom n 3 = (n : ℂ) * ((n : ℂ) - 1) * ((n : ℂ) - 2) / 6 := by
  rw [gBinom, show (3 : ℕ).factorial = 6 from rfl]
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero]
  push_cast; ring

/-! ## §C  Current primality `L₁(J^c₋₁|0⟩) = 0` (the weight-1 primary condition) -/

/-- `∑_aa fabc(aa,c,aa) = 0` (the diagonal trace of the structure constants). -/
theorem fabc_diag_sum (c : Fin 3) : (∑ aa : Fin 3, fabc aa c aa) = 0 := by
  fin_cases c <;> simp [Fin.sum_univ_three, fabc]

/-- `J^c₋₁|0⟩ ∈ gradingZA 1`. -/
theorem current_state_mem (k : ℂ) (c : Fin 3) : J k c (-1) (vacuumA k) ∈ gradingZA k 1 := by
  have h := J_mem_gradingZA k c (-1) 0 (vacuumA_mem_gradingZA_zero k)
  rwa [show (0 : ℤ) - (-1) = 1 from by ring] at h

/-- A zero-mode current annihilates degree-`0` states (`= ℂ·|0⟩`). -/
theorem J_zero_grading0 (k : ℂ) (bb : Fin 3) {y : WakModule k} (hy : y ∈ gradingZA k 0) :
    J k bb 0 y = 0 := by
  rw [gradingZA_zero_eq_span_vacuum] at hy
  induction hy using Submodule.span_induction with
  | mem z hz => rw [Set.mem_singleton_iff] at hz; subst hz; exact J_vacuum_nonneg k bb (le_refl 0)
  | zero => rw [map_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

/-- `J^aa₀ (J^c₋₁|0⟩) = ∑_d f(aa,c,d) • J^d₋₁|0⟩` (zero mode acting; no central, modes `0,-1`). -/
theorem J0_current (k : ℂ) (c aa : Fin 3) :
    J k aa 0 (J k c (-1) (vacuumA k))
      = ∑ d : Fin 3, fabc aa c d • J k d (-1) (vacuumA k) := by
  have hb := J_bracket k aa c 0 (-1)
  rw [if_neg (by norm_num : ¬ (0 : ℤ) + (-1) = 0), add_zero,
    show (0 : ℤ) + (-1) = -1 from by ring] at hb
  have happ := congrArg (fun (R : End ℂ (WakModule k)) => R (vacuumA k)) hb
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
    LinearMap.smul_apply] at happ
  rw [J_vacuum_nonneg k aa (le_refl 0), map_zero, sub_zero] at happ
  exact happ

/-- `J^bb₁ (J^d₋₁|0⟩) = (k·κ(bb,d)) • |0⟩` (central term, modes `1,-1`). -/
theorem J1_neg1_vac (k : ℂ) (bb d : Fin 3) :
    J k bb 1 (J k d (-1) (vacuumA k)) = (k * kappa bb d) • vacuumA k := by
  have hb := J_bracket k bb d 1 (-1)
  rw [if_pos (by norm_num : (1 : ℤ) + (-1) = 0), show (1 : ℤ) + (-1) = 0 from by ring] at hb
  have happ := congrArg (fun (R : End ℂ (WakModule k)) => R (vacuumA k)) hb
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.id_apply] at happ
  rw [J_vacuum_nonneg k bb (by norm_num : (0 : ℤ) ≤ 1), map_zero, sub_zero] at happ
  rw [show (∑ x : Fin 3, fabc bb d x • J k x 0 (vacuumA k)) = 0 from
    Finset.sum_eq_zero (fun x _ => by
      rw [J_vacuum_nonneg k x (by norm_num : (0 : ℤ) ≤ 0), smul_zero]),
    zero_add] at happ
  rw [happ, show ((1 : ℤ) : ℂ) = 1 from by norm_num, one_mul]

/-- The `p`-summand of `(nprod (Jfield aa)(Jfield bb))(-3)`: modes `(-p-1, p+2)`. -/
noncomputable def sug1TermJ (k : ℂ) (aa bb : Fin 3) (p : ℤ) : End ℂ (WakModule k) :=
  if 0 ≤ p then J k aa (-p - 1) * J k bb (p + 2) else J k bb (p + 2) * J k aa (-p - 1)

/-- Evaluate one quadratic current summand on a module state. Normal ordering chooses the
composition order from the sign of p, while the two mode indices sum to one; this is the
summand used to compute L1 on current states. -/
theorem sug1TermJ_apply (k : ℂ) (aa bb : Fin 3) (p : ℤ) (x : WakModule k) :
    sug1TermJ k aa bb p x
      = if 0 ≤ p then J k aa (-p - 1) (J k bb (p + 2) x) else J k bb (p + 2) (J k aa (-p - 1) x) := by
  rw [sug1TermJ]; split_ifs <;> rw [Module.End.mul_apply]

/-- The `(-3)`-coefficient of `nprod (Jfield aa)(Jfield bb)` acting on `x`. -/
theorem nprod_neg_three_coeff (k : ℂ) (aa bb : Fin 3) (x : WakModule k) :
    nprod (Jfield_isField k aa) (Jfield_isField k bb) (-3) x
      = ∑ᶠ p : ℤ, sug1TermJ k aa bb p x := by
  rw [nprod_apply]
  refine finsum_congr fun p => ?_
  rw [normalOrdered_apply, Jfield_apply, Jfield_apply, sug1TermJ_apply,
      show -(-3 - p) - 1 = p + 2 from by ring]
  by_cases hp : 0 ≤ p
  · rw [if_pos hp, if_pos hp, Module.End.mul_apply]
  · rw [if_neg hp, if_neg hp, Module.End.mul_apply]

/-- The `Lsug 1` action (the `(-3)`-coefficient analog of `Lsug0_apply`). -/
theorem Lsug1_apply (k : ℂ) (x : WakModule k) :
    Lsug k 1 x
      = c0 k • ∑ aa : Fin 3, ∑ bb : Fin 3,
          kappaInv aa bb • ∑ᶠ p : ℤ, sug1TermJ k aa bb p x := by
  rw [Lsug_def, mode_apply, show (-((1 : ℤ) + 1) - 1 : ℤ) = -3 from by ring, sugawaraField]
  show (c0 k • (Reconstruction.evalAt (-3) x
      (∑ aa : Fin 3, ∑ bb : Fin 3,
        kappaInv aa bb • nprod (Jfield_isField k aa) (Jfield_isField k bb)))) = _
  rw [map_sum]
  refine congrArg (c0 k • ·) ?_
  refine Finset.sum_congr rfl fun aa _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun bb _ => ?_
  rw [map_smul]
  refine congrArg (kappaInv aa bb • ·) ?_
  rw [Reconstruction.evalAt_apply, nprod_neg_three_coeff]

/-- For `p ≠ -1`, `sug1TermJ aa bb p (J^c₋₁|0⟩) = 0`. -/
theorem sug1TermJ_current_off (k : ℂ) (c aa bb : Fin 3) {p : ℤ} (hp : p ≠ -1) :
    sug1TermJ k aa bb p (J k c (-1) (vacuumA k)) = 0 := by
  rw [sug1TermJ_apply]
  by_cases h0 : 0 ≤ p
  · rw [if_pos h0,
      J_gradingZA_eq_zero k bb (show (1 : ℤ) < p + 2 from by omega) (current_state_mem k c),
      map_zero]
  · rw [if_neg h0]
    rw [not_le] at h0
    rcases lt_or_eq_of_le (show p ≤ -2 from by omega) with hlt | heq
    · rw [J_gradingZA_eq_zero k aa (show (1 : ℤ) < -p - 1 from by omega) (current_state_mem k c),
        map_zero]
    · rw [show p + 2 = 0 from by rw [heq]; norm_num, show -p - 1 = 1 from by rw [heq]; norm_num]
      refine J_zero_grading0 k bb ?_
      have h := J_mem_gradingZA k aa 1 1 (current_state_mem k c)
      rwa [show (1 : ℤ) - 1 = 0 from by ring] at h

/-- The value of `sug1TermJ` at `p = -1`. -/
theorem sug1TermJ_current_at_neg1 (k : ℂ) (c aa bb : Fin 3) :
    sug1TermJ k aa bb (-1) (J k c (-1) (vacuumA k))
      = (∑ d : Fin 3, fabc aa c d * k * kappa bb d) • vacuumA k := by
  rw [sug1TermJ_apply, if_neg (by norm_num : ¬ (0 : ℤ) ≤ -1),
    show (-1 : ℤ) + 2 = 1 from by ring, show (-(-1) - 1 : ℤ) = 0 from by ring,
    J0_current, map_sum]
  rw [show (∑ d : Fin 3, J k bb 1 (fabc aa c d • J k d (-1) (vacuumA k)))
      = ∑ d : Fin 3, (fabc aa c d * k * kappa bb d) • vacuumA k from
    Finset.sum_congr rfl (fun d _ => by
      rw [map_smul, J1_neg1_vac, smul_smul]
      congr 1; ring)]
  rw [Finset.sum_smul]

/-- The collapse: `∑ᶠ_p sug1TermJ aa bb p (J^c₋₁|0⟩) = (∑_d f(aa,c,d) k κ(bb,d)) • |0⟩`. -/
theorem sug1TermJ_current_finsum (k : ℂ) (c aa bb : Fin 3) :
    (∑ᶠ p : ℤ, sug1TermJ k aa bb p (J k c (-1) (vacuumA k)))
      = (∑ d : Fin 3, fabc aa c d * k * kappa bb d) • vacuumA k := by
  rw [finsum_eq_single _ (-1) (fun p hp => sug1TermJ_current_off k c aa bb hp)]
  exact sug1TermJ_current_at_neg1 k c aa bb

/-- **Current primality**: `mode (YA ω) 2 (J^c₋₁|0⟩) = 0` (the current `J^c` is a weight-`1`
primary; `ω₍₂₎(J^c₋₁|0⟩) = 0`). -/
theorem current_primary (k : ℂ) (hk : k + 2 ≠ 0) (c : Fin 3) :
    mode (YA k hk (omegaA k)) 2 (J k c (-1) (vacuumA k)) = 0 := by
  have hmode : mode (YA k hk (omegaA k)) 2 = Lsug k 1 := by
    rw [YA_omega_eq, Lsug_def]; rfl
  rw [hmode, Lsug1_apply]
  have key : (∑ aa : Fin 3, ∑ bb : Fin 3,
        kappaInv aa bb • ∑ᶠ p : ℤ, sug1TermJ k aa bb p (J k c (-1) (vacuumA k)))
      = (∑ aa : Fin 3, ∑ bb : Fin 3, ∑ d : Fin 3,
          kappaInv aa bb * (fabc aa c d * k * kappa bb d)) • vacuumA k := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun aa _ => ?_)
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun bb _ => ?_)
    rw [sug1TermJ_current_finsum, smul_smul, Finset.mul_sum]
  rw [key, show (∑ aa : Fin 3, ∑ bb : Fin 3, ∑ d : Fin 3,
        kappaInv aa bb * (fabc aa c d * k * kappa bb d)) = 0 from by
    fin_cases c <;> simp [Fin.sum_univ_three, fabc, kappa, kappaInv],
    zero_smul, smul_zero]

/-! ## §D  The current covariance `[Lₘ, J^c_μ] = -μ J^c_{m+μ}` via Borcherds + primality -/

/-- `:a(z) 1: = a(z)`: the normal-ordered product with the identity field is the identity. -/
theorem nprod_idFieldA {k : ℂ} {a : FormalDist (End ℂ (WakModule k))} (ha : IsField a) :
    nprod ha (idFieldA_isField k) = a := by
  funext s
  apply LinearMap.ext; intro x
  rw [nprod_apply, finsum_eq_single _ s]
  · rw [normalOrdered_apply]
    have hid : (idFieldA k) (s - s) = LinearMap.id := by
      change (if s - s = 0 then (LinearMap.id : End ℂ (WakModule k)) else 0) = LinearMap.id
      rw [if_pos (by ring)]
    by_cases h : 0 ≤ s
    · rw [if_pos h, hid]; rfl
    · rw [if_neg h, hid]; rfl
  · intro m hm
    rw [normalOrdered_apply]
    have hid : (idFieldA k) (s - m) = 0 := by
      change (if s - m = 0 then (LinearMap.id : End ℂ (WakModule k)) else 0) = 0
      rw [if_neg (by omega)]
    by_cases h : 0 ≤ m
    · rw [if_pos h, hid]; simp
    · rw [if_neg h, hid]; simp

/-- The vertex field of the current state `J^c₋₁|0⟩` is the current field `J^c(z)`. -/
theorem YA_current_state (k : ℂ) (hk : k + 2 ≠ 0) (c : Fin 3) :
    YA k hk (J k c (-1) (vacuumA k)) = Jfield k c := by
  have hws : wordStateA k [(c, 0)] = J k c (-1) (vacuumA k) := by
    rw [wordStateA_cons, wordStateA_nil]; norm_num
  rw [← hws, YA_wordState, YwordA_cons]
  show nprod (genFieldA_isField k c 0) (idFieldA_isField k) = Jfield k c
  rw [nprod_idFieldA, genFieldA_zero]

/-- `mode (Jfield c) μ = J^c_μ`. -/
theorem mode_Jfield (k : ℂ) (c : Fin 3) (μ : ℤ) : mode (Jfield k c) μ = J k c μ := by
  rw [mode_apply, Jfield_apply, show -(-μ - 1) - 1 = μ from by ring]

/-- The `j`-th term of the current commutator formula (the OPE-coefficient feeds the current
state `J^c₋₁|0⟩` into `YA`). -/
noncomputable def covTerm (k : ℂ) (hk : k + 2 ≠ 0) (c : Fin 3) (m μ : ℤ) (j : ℕ) :
    End ℂ (WakModule k) :=
  gBinom (m + 1) j • mode (YA k hk ((affineVA k hk).smul (omegaA k) (j : ℤ)
    (J k c (-1) (vacuumA k)))) (m + 1 + μ - (j : ℤ))

/-- If a conformal-current operator-product coefficient is the zero state, its entire contribution
to the mode commutator vanishes. Linearity of the state-field map and of mode extraction
removes it, regardless of the binomial coefficient. -/
theorem covTerm_zero_of_smul (k : ℂ) (hk : k + 2 ≠ 0) (c : Fin 3) (m μ : ℤ) {j : ℕ}
    (h : (affineVA k hk).smul (omegaA k) (j : ℤ) (J k c (-1) (vacuumA k)) = 0) :
    covTerm k hk c m μ j = 0 := by
  rw [covTerm, h, map_zero]
  show gBinom (m + 1) j • mode (0 : FormalDist (End ℂ (WakModule k))) (m + 1 + μ - (j : ℤ)) = 0
  rw [mode_zero, smul_zero]

/-- `ω₍ⱼ₎(J^c₋₁|0⟩) = 0` for `j ≥ 2`: at `j = 2` it is primality `current_primary`; for `j ≥ 3`
the state lands in negative degree. -/
theorem smul_omega_current_ge2 (k : ℂ) (hk : k + 2 ≠ 0) (c : Fin 3) {j : ℕ} (hj : 2 ≤ j) :
    (affineVA k hk).smul (omegaA k) (j : ℤ) (J k c (-1) (vacuumA k)) = 0 := by
  rw [affineVA_smul]
  rcases Nat.lt_or_ge j 3 with h3 | h3
  · obtain rfl : j = 2 := by omega
    exact_mod_cast current_primary k hk c
  · have hmem := hYA_grading k hk (omegaA k) (omegaA_mem k)
      (J k c (-1) (vacuumA k)) (current_state_mem k c) (j : ℤ)
    rw [show (2 : ℤ) + 1 - (j : ℤ) - 1 = 2 - (j : ℤ) from by ring] at hmem
    rw [gradingZA_positivity k (2 - (j : ℤ)) (by omega), Submodule.mem_bot] at hmem
    exact hmem

/-- `covTerm 0 = -(m+1+μ) • J^c_{m+μ}` (the translation/derivative term `ω₍₀₎ = L₋₁`). -/
theorem covTerm_zero_eq (k : ℂ) (hk : k + 2 ≠ 0) (c : Fin 3) (m μ : ℤ) :
    covTerm k hk c m μ 0 = ((-(m + 1 + μ) : ℤ) : ℂ) • J k c (m + μ) := by
  rw [covTerm, Nat.cast_zero, gBinom_zero, one_smul, sub_zero, affineVA_smul,
    hYA_translation k hk (J k c (-1) (vacuumA k)), mode_deriv,
    show m + 1 + μ - 1 = m + μ from by ring, YA_current_state, mode_Jfield,
    ← Int.cast_smul_eq_zsmul ℂ (-(m + 1 + μ))]

/-- `covTerm 1 = (m+1) • J^c_{m+μ}` (the weight term `ω₍₁₎ = L₀`, weight `1`). -/
theorem covTerm_one_eq (k : ℂ) (hk : k + 2 ≠ 0) (c : Fin 3) (m μ : ℤ) :
    covTerm k hk c m μ 1 = ((m + 1 : ℤ) : ℂ) • J k c (m + μ) := by
  rw [covTerm, Nat.cast_one, gBinom_one, affineVA_smul,
    hYA_L0 k hk (J k c (-1) (vacuumA k)) (current_state_mem k c), Int.cast_one, one_smul,
    show m + 1 + μ - 1 = m + μ from by ring, YA_current_state, mode_Jfield]

/-- **The current covariance** (the weight-`1` primary OPE): `[Lₘ, J^c_μ] = -μ • J^c_{m+μ}`. -/
theorem Lcomm_J (k : ℂ) (hk : k + 2 ≠ 0) (m : ℤ) (c : Fin 3) (μ : ℤ) :
    ⁅mode (YA k hk (omegaA k)) (m + 1), J k c μ⁆ = ((-μ : ℤ) : ℂ) • J k c (m + μ) := by
  obtain ⟨N, hN, hvan⟩ := VARec.smul_zero_ge (affineVA k hk) (Ltrans k)
    (fun u s => Ltrans_comm_Ycoeff k hk u s) (Ltrans_vac k) (omegaA k) (J k c (-1) (vacuumA k))
    (m + 1) μ
  rw [show (affineVA k hk).Y = YA k hk from rfl] at hN
  rw [show mode (YA k hk (J k c (-1) (vacuumA k))) μ = J k c μ from by
    rw [YA_current_state, mode_Jfield]] at hN
  rw [hN]
  rw [show (∑ j : Fin N, gBinom (m + 1) (j : ℕ)
        • mode (YA k hk ((affineVA k hk).smul (omegaA k) (j : ℕ) (J k c (-1) (vacuumA k))))
            (m + 1 + μ - (j : ℕ)))
      = ∑ j ∈ Finset.range N, covTerm k hk c m μ j from by
    rw [← Fin.sum_univ_eq_sum_range (fun j => covTerm k hk c m μ j) N]; rfl]
  have hcollapse : (∑ j ∈ Finset.range N, covTerm k hk c m μ j)
      = ∑ j ∈ Finset.range 2, covTerm k hk c m μ j := by
    rcases le_total N 2 with hle | hle
    · refine Finset.sum_subset
        (fun j hj => Finset.mem_range.mpr (by rw [Finset.mem_range] at hj; omega))
        (fun j _ hjn => ?_)
      rw [Finset.mem_range, not_lt] at hjn
      exact covTerm_zero_of_smul k hk c m μ (hvan j hjn)
    · refine (Finset.sum_subset
        (fun j hj => Finset.mem_range.mpr (by rw [Finset.mem_range] at hj; omega))
        (fun j _ hj2 => ?_)).symm
      rw [Finset.mem_range, not_lt] at hj2
      exact covTerm_zero_of_smul k hk c m μ (smul_omega_current_ge2 k hk c hj2)
  rw [hcollapse, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    covTerm_zero_eq, covTerm_one_eq, ← add_smul]
  congr 1
  push_cast; ring

/-! ## §E  `ω₍₂₎ω = 0` and `ω₍₃₎ω = (c/2)|0⟩` -/

/-- The conformal vector in creation form: `ω = c₀ ∑_{a,b} κ⁻¹(a,b) J^a₋₁ J^b₋₁|0⟩`. -/
theorem omegaA_creation_form (k : ℂ) :
    omegaA k = c0 k • ∑ aa : Fin 3, ∑ bb : Fin 3,
      kappaInv aa bb • J k aa (-1) (J k bb (-1) (vacuumA k)) := by
  rw [omegaA_eq, sugawaraField]
  show (c0 k • (Reconstruction.evalAt 0 (vacuumA k)
      (∑ aa : Fin 3, ∑ bb : Fin 3,
        kappaInv aa bb • nprod (Jfield_isField k aa) (Jfield_isField k bb)))) = _
  rw [map_sum]
  refine congrArg (c0 k • ·) ?_
  refine Finset.sum_congr rfl fun aa _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun bb _ => ?_
  rw [map_smul]
  refine congrArg (kappaInv aa bb • ·) ?_
  rw [Reconstruction.evalAt_apply,
    nprod_vacuum_base_gen (Jfield_isField k aa) (Jfield_isField k bb) (vacuumA k)
      (fun q hq => Jfield_vacuum_neg k aa hq) (fun q hq => Jfield_vacuum_neg k bb hq),
    Jfield_apply, Jfield_apply, show (-(0 : ℤ) - 1) = -1 from by ring]

/-- The current covariance applied to a state:
`Lₘ(J^a_ν y) = J^a_ν(Lₘ y) + (-ν)•J^a_{m+ν} y`. -/
theorem Lcomm_J_apply (k : ℂ) (hk : k + 2 ≠ 0) (m : ℤ) (a : Fin 3) (ν : ℤ) (y : WakModule k) :
    mode (YA k hk (omegaA k)) (m + 1) (J k a ν y)
      = J k a ν (mode (YA k hk (omegaA k)) (m + 1) y) + ((-ν : ℤ) : ℂ) • J k a (m + ν) y := by
  have h := Lcomm_J k hk m a ν
  rw [LieRing.of_associative_ring_bracket] at h
  have happ := congrArg (fun (R : End ℂ (WakModule k)) => R y) h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at happ
  rw [sub_eq_iff_eq_add] at happ
  rw [happ]; abel

/-- `∑_{aa,bb} κ⁻¹(aa,bb) • ∑_d f(aa,bb,d) • V d = 0` (κ⁻¹ symmetric · `f` antisymmetric). -/
theorem contract_antisymm (k : ℂ) (V : Fin 3 → WakModule k) :
    (∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb • ∑ d : Fin 3, fabc aa bb d • V d) = 0 := by
  have e1 : (∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb • ∑ d : Fin 3, fabc aa bb d • V d)
      = ∑ aa : Fin 3, ∑ bb : Fin 3, ∑ d : Fin 3, (kappaInv aa bb * fabc aa bb d) • V d := by
    refine Finset.sum_congr rfl (fun aa _ => Finset.sum_congr rfl (fun bb _ => ?_))
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun d _ => by rw [smul_smul])
  rw [e1, Finset.sum_congr rfl (fun aa _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_eq_zero (fun d _ => ?_)
  rw [show (∑ aa : Fin 3, ∑ bb : Fin 3, (kappaInv aa bb * fabc aa bb d) • V d)
      = (∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb * fabc aa bb d) • V d from by
    rw [Finset.sum_smul]; exact Finset.sum_congr rfl (fun aa _ => by rw [Finset.sum_smul])]
  rw [kappaInv_fabc_antisymm_zero, zero_smul]

/-- `L₁(J^a₋₁ J^b₋₁|0⟩) = ∑_d f(a,b,d) • J^d₋₁|0⟩` (Leibniz: `[L₁,J^a₋₁]=J^a₀`, primality kills
the other term). -/
theorem L1_on_two_currents (k : ℂ) (hk : k + 2 ≠ 0) (aa bb : Fin 3) :
    mode (YA k hk (omegaA k)) 2 (J k aa (-1) (J k bb (-1) (vacuumA k)))
      = ∑ d : Fin 3, fabc aa bb d • J k d (-1) (vacuumA k) := by
  have h := Lcomm_J_apply k hk 1 aa (-1) (J k bb (-1) (vacuumA k))
  rw [show (1 : ℤ) + 1 = 2 from by ring, show (1 : ℤ) + (-1) = 0 from by ring,
    show ((-(-1) : ℤ) : ℂ) = 1 from by norm_num, one_smul, current_primary k hk bb, map_zero,
    zero_add, J0_current k bb aa] at h
  exact h

/-- `L₂(J^a₋₁ J^b₋₁|0⟩) = (k·κ(a,b)) • |0⟩` (Leibniz: `[L₂,J^a₋₁]=J^a₁`, grading kills the other
term; the central level-`k` term survives). -/
theorem L2_on_two_currents (k : ℂ) (hk : k + 2 ≠ 0) (aa bb : Fin 3) :
    mode (YA k hk (omegaA k)) 3 (J k aa (-1) (J k bb (-1) (vacuumA k)))
      = (k * kappa aa bb) • vacuumA k := by
  have hinner : mode (YA k hk (omegaA k)) 3 (J k bb (-1) (vacuumA k)) = 0 := by
    have hmem := hYA_grading k hk (omegaA k) (omegaA_mem k) (J k bb (-1) (vacuumA k))
      (current_state_mem k bb) 3
    rw [show (2 : ℤ) + 1 - 3 - 1 = -1 from by ring,
      gradingZA_positivity k (-1) (by norm_num), Submodule.mem_bot] at hmem
    exact hmem
  have h := Lcomm_J_apply k hk 2 aa (-1) (J k bb (-1) (vacuumA k))
  rw [show (2 : ℤ) + 1 = 3 from by ring, show (2 : ℤ) + (-1) = 1 from by ring,
    show ((-(-1) : ℤ) : ℂ) = 1 from by norm_num, one_smul, J1_neg1_vac, hinner, map_zero,
    zero_add] at h
  exact h

/-- **`ω₍₂₎ω = 0`** (the OPE coefficient `T₍₂₎T = 0`). -/
theorem omegaJomega_two_eq_zero (k : ℂ) (hk : k + 2 ≠ 0) : omegaJomega k hk 2 = 0 := by
  show mode (YA k hk (omegaA k)) 2 (omegaA k) = 0
  nth_rewrite 2 [omegaA_creation_form]
  rw [map_smul, map_sum]
  rw [show (∑ aa : Fin 3, mode (YA k hk (omegaA k)) 2
        (∑ bb : Fin 3, kappaInv aa bb • J k aa (-1) (J k bb (-1) (vacuumA k))))
      = ∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb •
          (∑ d : Fin 3, fabc aa bb d • J k d (-1) (vacuumA k)) from
    Finset.sum_congr rfl (fun aa _ => by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun bb _ => by rw [map_smul, L1_on_two_currents]))]
  rw [contract_antisymm, smul_zero]

/-- **`ω₍₃₎ω = (c/2)|0⟩`** (the OPE coefficient `T₍₃₎T = (c/2)·1`; `c = 3k/(k+2)`). -/
theorem omegaJomega_three (k : ℂ) (hk : k + 2 ≠ 0) :
    omegaJomega k hk 3 = (centralChargeA k / 2) • vacuumA k := by
  show mode (YA k hk (omegaA k)) 3 (omegaA k) = (centralChargeA k / 2) • vacuumA k
  nth_rewrite 2 [omegaA_creation_form]
  rw [map_smul, map_sum]
  rw [show (∑ aa : Fin 3, mode (YA k hk (omegaA k)) 3
        (∑ bb : Fin 3, kappaInv aa bb • J k aa (-1) (J k bb (-1) (vacuumA k))))
      = ∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb • ((k * kappa aa bb) • vacuumA k) from
    Finset.sum_congr rfl (fun aa _ => by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun bb _ => by rw [map_smul, L2_on_two_currents]))]
  rw [show (∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb • ((k * kappa aa bb) • vacuumA k))
      = (k * ∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb * kappa aa bb) • vacuumA k from by
    rw [show (∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb • ((k * kappa aa bb) • vacuumA k))
        = ∑ aa : Fin 3, ∑ bb : Fin 3, (k * (kappaInv aa bb * kappa aa bb)) • vacuumA k from
      Finset.sum_congr rfl (fun aa _ => Finset.sum_congr rfl (fun bb _ => by
        rw [smul_smul]; congr 1; ring))]
    rw [show (∑ aa : Fin 3, ∑ bb : Fin 3, (k * (kappaInv aa bb * kappa aa bb)) • vacuumA k)
        = (∑ aa : Fin 3, ∑ bb : Fin 3, k * (kappaInv aa bb * kappa aa bb)) • vacuumA k from by
      rw [Finset.sum_smul]; exact Finset.sum_congr rfl (fun aa _ => by rw [Finset.sum_smul])]
    congr 1
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun aa _ => by rw [Finset.mul_sum])]
  rw [show (∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb * kappa aa bb) = 3 from by
    simp [Fin.sum_univ_three, kappaInv, kappa]; norm_num, smul_smul,
    show c0 k * (k * 3) = centralChargeA k / 2 from by
      rw [c0, centralChargeA, dimSl2, dualCoxeter]; field_simp]

/-! ## §F  VOA1: the Sugawara Virasoro relation `hYA_virasoro` -/

/-- **VOA1** (`hYA_virasoro`): the full Sugawara Virasoro relation
`[Lₘ, Lₙ] = (m−n)·L_{m+n} + δ_{m+n,0}·(m³−m)/12·c·1`, with `c = centralChargeA k = 3k/(k+2)`.
Obtained from the collapsed Borcherds commutator `[Lₘ,Lₙ] = ∑_{j<4} commTermⱼ` by evaluating the
four OPE coefficients: `ω₍₀₎ω = L₋₁ω` (translation), `ω₍₁₎ω = 2ω` (weight), `ω₍₂₎ω = 0`, and
`ω₍₃₎ω = (c/2)|0⟩` (central charge). -/
theorem hYA_virasoro (k : ℂ) (hk : k + 2 ≠ 0) (m n : ℤ) :
    ⁅mode (YA k hk (omegaA k)) (m + 1), mode (YA k hk (omegaA k)) (n + 1)⁆
      = ((m : ℂ) - n) • mode (YA k hk (omegaA k)) (m + n + 1)
        + (if m + n = 0 then
            (((m : ℂ) ^ 3 - m) / 12 * centralChargeA k) • (1 : End ℂ (WakModule k))
           else 0) := by
  have hct0 : commTerm k hk m n 0
      = (-((m + n + 2 : ℤ) : ℂ)) • mode (YA k hk (omegaA k)) (m + n + 1) := by
    rw [commTerm]
    simp only [Nat.cast_zero]
    rw [gBinom_zero, one_smul, sub_zero, show m + 1 + (n + 1) = m + n + 2 from by ring,
      mode_YA_omegaJomega_zero, show (m + n + 2 : ℤ) - 1 = m + n + 1 from by ring]
  have hct1 : commTerm k hk m n 1
      = ((m + 1 : ℤ) : ℂ) • ((2 : ℂ) • mode (YA k hk (omegaA k)) (m + n + 1)) := by
    rw [commTerm]
    simp only [Nat.cast_one]
    rw [gBinom_one, omegaJomega_one, map_smul, mode_smul,
      show m + 1 + (n + 1) - 1 = m + n + 1 from by ring]
  have hct2 : commTerm k hk m n 2 = 0 := by
    rw [commTerm]
    simp only [Nat.cast_ofNat]
    rw [omegaJomega_two_eq_zero k hk, map_zero, mode_zero, smul_zero]
  have hct3 : commTerm k hk m n 3
      = if m + n = 0 then
          (((m : ℂ) ^ 3 - m) / 12 * centralChargeA k) • (1 : End ℂ (WakModule k)) else 0 := by
    rw [commTerm]
    simp only [Nat.cast_ofNat]
    rw [gBinom_three, omegaJomega_three, map_smul, YA_vacuum, mode_smul,
      show m + 1 + (n + 1) - 3 = m + n - 1 from by ring]
    by_cases hmn : m + n = 0
    · rw [if_pos hmn]
      have hone : mode (1 : FormalDist (End ℂ (WakModule k))) (m + n - 1)
          = (1 : End ℂ (WakModule k)) := by
        rw [mode_apply, show -(m + n - 1) - 1 = -(m + n) from by ring, hmn, neg_zero,
          FormalDist.one_apply, if_pos rfl]
      rw [hone, smul_smul]
      congr 1
      push_cast; ring
    · rw [if_neg hmn]
      have hone : mode (1 : FormalDist (End ℂ (WakModule k))) (m + n - 1) = 0 := by
        rw [mode_apply, FormalDist.one_apply, if_neg (by omega : ¬ -(m + n - 1) - 1 = 0)]
      rw [hone, smul_zero, smul_zero]
  rw [comm_eq_range4, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hct2, add_zero, hct0, hct1, hct3]
  congr 1
  rw [smul_smul, ← add_smul]
  congr 1
  push_cast; ring

end VOA.AffineVOA.Vir

/-! ## §G  The closed affine `𝔰𝔩₂` VOA instance -/

namespace VOA.AffineVOA

/-- **The closed affine `𝔰𝔩₂` VOA** `𝒱(𝔰𝔩₂, k)` at level `k` (`k + 2 ≠ 0`): feeding the
unconditional vertex map `YA k hk` and ALL nine proved `YA`-axioms — VA2 vacuum (`YA_vacuum`),
VA1 grading (`hYA_grading`), VA3 creation (`YA_creation`), VA4 locality (`YA_local`), VA5
regularity (`YA_regularity`), `ω ∈ grading 2` (`omegaA_mem`), VOA1 Virasoro (`Vir.hYA_virasoro`),
VOA2 `L₀ = energy` (`hYA_L0`), VOA3 translation (`hYA_translation`) — into the shell
`affineSl2VOA` produces a complete `VertexOperatorAlgebra (WakModule k)` with central charge
`c = 3k/(k+2)`. -/
noncomputable def affineSl2VOA_closed (k : ℂ) (hk : k + 2 ≠ 0) :
    VertexOperatorAlgebra (WakModule k) :=
  affineSl2VOA k hk (YA k hk) (YA_vacuum k hk)
    (fun {_ _} u hu v hv n => hYA_grading k hk u hu v hv n)
    (YA_creation k hk) (YA_local k hk) (YA_regularity k hk) (omegaA_mem k)
    (Vir.hYA_virasoro k hk) (fun {_} v hv => hYA_L0 k hk v hv) (hYA_translation k hk)

/-- **The central charge of the closed affine `𝔰𝔩₂` VOA is `3k/(k+2)`** (Gannon §5.2.2). -/
theorem affineSl2VOA_closed_central_charge (k : ℂ) (hk : k + 2 ≠ 0) :
    (affineSl2VOA_closed k hk).centralCharge = 3 * k / (k + 2) :=
  centralChargeA_eq k

end VOA.AffineVOA
