/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.SuperTranslationCovariance

/-!
# The super `n`-th product, the commutator formula, and the nonnegative iterate

Layer 3 of the super Borcherds chain: the port of the second half of `Core.Reconstruction`
(`nth_product`, `mode_commutator`, `mode_iterate_borcherds_nonneg`) with the Koszul sign.

## Where the sign sits, and where it does not

The only place the sign enters is the **bracket**: `bracketDistε ε a b m n = aₘbₙ − ε•(bₙaₘ)`.
Two consequences shape the whole file:

* The vacuum tower of `cCoeff k (bracketDistε ε (Yu) (Yv))` is **sign-free**: on the quadrant
  `{s ≤ -1, t ≤ -1}` the `ε`-term dies by the *same* creation vanishing that kills the
  unsigned one, and at the base only the unsigned term survives.  This is why
  `nth_productε` has **no sign on its right-hand side**: `cCoeff k ⁅Yu,Yv⁆_ε = Y(u₍ₖ₎v)`.
* Consequently `mode_commutatorε` also carries no sign on the right: the `ε` lives entirely
  in the twisted mode bracket on the left.

## Main results

* `nth_productε` — `Y(u₍ₖ₎v, z) = Res_{z₁}((z₁-z)ᵏ ⁅Y(u,z₁),Y(v,z)⁆_ε)`.
* `bracket_deltaSumε`, `mode_bracket_opeε` — the OPE δ-decomposition and its coefficient
  extraction for the twisted bracket.
* `mode_commutatorε` / `commBoundε` — `u₍ₐ₎v₍ᵦ₎ − ε·v₍ᵦ₎u₍ₐ₎ = ∑_j C(a,j)(u₍ⱼ₎v)₍ₐ₊ᵦ₋ⱼ₎`.
* `mode_iterate_borcherds_nonnegε` — the `ℓ = k ≥ 0` iterate in Borcherds form, with the
  Koszul sign on the exchanged term.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §0  Bracketing a two-variable distribution against a fixed operator -/

/-- The bracket of a two-variable distribution with a fixed operator, coefficient-wise.
(The bosonic `commL` is bundled with a `VertexOperatorAlgebra`; this is the same operation
taking the operator as a bare argument.) -/
def commT (T : End ℂ 𝒱) (G : FormalDist₂ (End ℂ 𝒱)) : FormalDist₂ (End ℂ 𝒱) :=
  fun s t => ⁅T, G s t⁆

@[simp] theorem commT_apply (T : End ℂ 𝒱) (G : FormalDist₂ (End ℂ 𝒱)) (s t : ℤ) :
    commT T G s t = ⁅T, G s t⁆ := rfl

/-- `commT` commutes with `(z₁-z₂)·` (it acts on the operator value, not on the indices). -/
theorem commT_mulBySub (T : End ℂ 𝒱) (G : FormalDist₂ (End ℂ 𝒱)) :
    commT T (mulBySub G) = mulBySub (commT T G) := by
  apply FormalDist₂.ext; intro s t
  simp only [commT_apply, mulBySub_apply, lie_sub]

/-- Iterated: `commT` commutes with `(z₁-z₂)ᵏ`. -/
theorem commT_mulBySubPow (T : End ℂ 𝒱) (k : ℕ) (G : FormalDist₂ (End ℂ 𝒱)) :
    commT T (mulBySubPow k G) = mulBySubPow k (commT T G) := by
  induction k generalizing G with
  | zero => rfl
  | succ j ih => rw [mulBySubPow_succ, LinearMap.comp_apply, commT_mulBySub, ih,
      ← LinearMap.comp_apply, ← mulBySubPow_succ]

namespace SuperNearVOA

/-! ## §1  Translation covariance of the twisted OPE bracket -/

/-- **Translation covariance of the twisted OPE bracket**:
`[L₋₁, ⁅Y(u,z₁),Y(v,z₂)⁆_ε] = ∂⁅Y(u,z₁),Y(v,z₂)⁆_ε` with `∂ = ∂₁+∂₂`.  The `ε` rides through
as a scalar; the content is the Leibniz rule plus `L_comm_Ycoeffε`. -/
theorem commT_bracketDistε (V : SuperNearVOA 𝒱) (ε : ℂ) (u v : 𝒱) :
    commT (V.L (-1)) (bracketDistε ε (V.Y u) (V.Y v))
      = deriv2 (bracketDistε ε (V.Y u) (V.Y v)) := by
  have leib : ∀ (a b c : End ℂ 𝒱), ⁅a, b * c⁆ = ⁅a, b⁆ * c + b * ⁅a, c⁆ := fun a b c => by
    simp only [LieRing.of_associative_ring_bracket]; noncomm_ring
  apply FormalDist₂.ext; intro s t
  simp only [commT_apply, deriv2_apply, bracketDistε_apply, lie_sub, lie_smul, leib,
    L_comm_Ycoeffε, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add, smul_comm ε]
  abel

/-- **The recursion** `[L₋₁, A_m] = (m+1)·A_{m+1}` for the twisted field `k`-th product. -/
theorem L_comm_cCoeffε (V : SuperNearVOA 𝒱) (ε : ℂ) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    ⁅V.L (-1), cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) m⁆
      = (m + 1) • cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) (m + 1) := by
  show commT (V.L (-1)) (mulBySubPow k (bracketDistε ε (V.Y u) (V.Y v))) (-1) m = _
  rw [commT_mulBySubPow, commT_bracketDistε, resByParts]
  rfl

/-! ## §2  The vacuum tower of the twisted field `k`-th product (sign-free) -/

/-- The vacuum-applied twisted OPE bracket vanishes on the quadrant `{s≤-1, t≤-1}`: **both**
terms die by creation, so the `ε` never gets to act. -/
theorem applyVec_bracketDistε_quadrant (V : SuperNearVOA 𝒱) (ε : ℂ) (u v : 𝒱) (s t : ℤ)
    (hs : s ≤ -1) (ht : t ≤ -1) :
    applyVec V.vacuum (bracketDistε ε (V.Y u) (V.Y v)) s t = 0 := by
  rw [applyVec_apply, bracketDistε_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, Module.End.mul_apply,
    V.toSuperVertexAlgebra.Y_apply_vacuum_eq_zero v (by omega),
    V.toSuperVertexAlgebra.Y_apply_vacuum_eq_zero u (by omega), map_zero, map_zero, smul_zero,
    sub_zero]

/-- Reduce the twisted field `k`-th product on the vacuum to a `(z₁-z₂)ᵏ`-power. -/
theorem cCoeff_apply_vacuumε (V : SuperNearVOA 𝒱) (ε : ℂ) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) m V.vacuum
      = mulBySubPow k (applyVec V.vacuum (bracketDistε ε (V.Y u) (V.Y v))) (-1) m := by
  show mulBySubPow k (bracketDistε ε (V.Y u) (V.Y v)) (-1) m V.vacuum = _
  rw [← applyVec_apply, applyVec_mulBySubPow]

/-- `A_m 𝟙 = 0` for `m < 0`. -/
theorem cCoeff_vacuum_negε (V : SuperNearVOA 𝒱) (ε : ℂ) (u v : 𝒱) (k : ℕ) {m : ℤ} (hm : m < 0) :
    cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) m V.vacuum = 0 := by
  rw [cCoeff_apply_vacuumε]
  exact mulBySubPow_zero_of_quadrant (applyVec_bracketDistε_quadrant V ε u v) k (-1) m
    (by omega) (by omega)

/-- `A_0 𝟙 = u₍ₖ₎v` — **no sign**: the `ε`-term of the bracket dies on the vacuum. -/
theorem cCoeff_vacuum_baseε (V : SuperNearVOA 𝒱) (ε : ℂ) (u v : 𝒱) (k : ℕ) :
    cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) 0 V.vacuum = V.smul u k v := by
  rw [cCoeff_apply_vacuumε,
    mulBySubPow_diag_of_quadrant (applyVec_bracketDistε_quadrant V ε u v) k (-1) (by omega),
    applyVec_apply, bracketDistε_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, Module.End.mul_apply,
    V.toSuperVertexAlgebra.Y_apply_vacuum_zero,
    V.toSuperVertexAlgebra.Y_apply_vacuum_eq_zero u (by omega), map_zero, smul_zero, sub_zero]
  rw [SuperVertexAlgebra.smul_def, mode_apply, show (-1 - (k : ℤ)) = -(k : ℤ) - 1 from by ring]

/-- **The vacuum condition** for the twisted field `k`-th product: `A_m 𝟙 = Y(u₍ₖ₎v)_m 𝟙`. -/
theorem cCoeff_vacuum_eqε (V : SuperNearVOA 𝒱) (ε : ℂ) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) m V.vacuum
      = (V.Y (V.smul u k v)) m V.vacuum := by
  by_cases hm : m < 0
  · rw [cCoeff_vacuum_negε V ε u v k hm,
      V.toSuperVertexAlgebra.Y_apply_vacuum_eq_zero (V.smul u k v) hm]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = (j : ℤ) := ⟨m.toNat, by omega⟩
    clear hm
    induction j with
    | zero =>
        rw [Nat.cast_zero, cCoeff_vacuum_baseε]
        exact (V.toSuperVertexAlgebra.Y_apply_vacuum_zero _).symm
    | succ i ih =>
        have expand : ∀ (X : End ℂ 𝒱), ⁅V.L (-1), X⁆ V.vacuum = V.L (-1) (X V.vacuum) := by
          intro X
          rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
            Module.End.mul_apply, L_neg_one_vacuumε, map_zero, sub_zero]
        have hA := DFunLike.congr_fun (L_comm_cCoeffε V ε u v k (i : ℤ)) V.vacuum
        have hB := DFunLike.congr_fun (L_comm_Ycoeffε V (V.smul u k v) (i : ℤ)) V.vacuum
        rw [expand, LinearMap.smul_apply] at hA hB
        have key : ((i : ℤ) + 1) • cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) ((i : ℤ) + 1)
              V.vacuum
            = ((i : ℤ) + 1) • (V.Y (V.smul u k v)) ((i : ℤ) + 1) V.vacuum := by
          rw [← hA, ih, hB]
        have hc : (((i : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
        rw [← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1),
          ← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1)] at key
        rw [Nat.cast_succ]
        exact smul_right_injective 𝒱 hc key

/-! ## §3  The `n`-th product theorem -/

/-- **The super field `n`-th-product theorem** (`n = k ≥ 0`):
`Y(u₍ₖ₎v, z) = Res_{z₁}((z₁-z)ᵏ ⁅Y(u,z₁),Y(v,z)⁆_ε)` with `ε = (-1)^{|u||v|}`.

Note the **absence of any sign on the right**: the Koszul factor lives in the bracket only.
Goddard uniqueness (`goddard_uniquenessε`) applies because Dong's lemma
(`SuperVertexAlgebra.dong_fields`) delivers exactly the `Localε (koszul (p+q) r)` the parity
`|u₍ₖ₎v| = p + q` demands. -/
theorem nth_productε (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ V.parity p)
    (hv : v ∈ V.parity q) (k : ℕ) :
    cCoeff k (bracketDistε (koszul p q) (V.Y u) (V.Y v)) = V.Y (V.smul u k v) := by
  refine V.toSuperVertexAlgebra.goddard_uniquenessε _ (V.smul u k v)
    (V.smul_mem_parity hu hv (k : ℤ)) (fun r b hb => ?_)
    (cCoeff_vacuum_eqε V (koszul p q) u v k)
  exact V.toSuperVertexAlgebra.dong_fields hu hv hb k

/-! ## §4  The OPE δ-decomposition and the commutator formula -/

/-- The **twisted mode bracket** `u₍ₘ₎v₍ₙ₎ − ε·v₍ₙ₎u₍ₘ₎`. -/
def modeBracketε (ε : ℂ) (a b : FormalDist (End ℂ 𝒱)) (m n : ℤ) : End ℂ 𝒱 :=
  mode a m * mode b n - ε • (mode b n * mode a m)

@[simp] theorem modeBracketε_apply (ε : ℂ) (a b : FormalDist (End ℂ 𝒱)) (m n : ℤ) :
    modeBracketε ε a b m n = mode a m * mode b n - ε • (mode b n * mode a m) := rfl

/-- The twisted mode bracket is the twisted bracket distribution at the mode indices. -/
theorem modeBracketε_eq (ε : ℂ) (a b : FormalDist (End ℂ 𝒱)) (m n : ℤ) :
    modeBracketε ε a b m n = bracketDistε ε a b (-m - 1) (-n - 1) := rfl

/-- **The operator product expansion, super case.**  Super-locality VA4 plus Proposition
5.1.2 gives a finite `δ`-decomposition of the *twisted* bracket. -/
theorem bracket_deltaSumε (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ V.parity p)
    (hv : v ∈ V.parity q) :
    ∃ (N : ℕ) (c : Fin N → FormalDist (End ℂ 𝒱)),
      bracketDistε (koszul p q) (V.Y u) (V.Y v) = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j) := by
  obtain ⟨N, hN⟩ := V.locality u hu v hv
  exact ⟨N, (local_iff_deltaSum _ N).mp hN⟩

/-- **The commutator formula, OPE form**, for the twisted bracket. -/
theorem mode_bracket_opeε (V : SuperNearVOA 𝒱) (ε : ℂ) (u v : 𝒱) {N : ℕ}
    {c : Fin N → FormalDist (End ℂ 𝒱)}
    (h : bracketDistε ε (V.Y u) (V.Y v) = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j)) (a b : ℤ) :
    modeBracketε ε (V.Y u) (V.Y v) a b = ∑ j : Fin N,
      (∏ i ∈ Finset.range (j : ℕ), (a - (i : ℤ))) • mode (c j) (a + b - ((j : ℕ) : ℤ)) := by
  rw [modeBracketε_eq, h, formalDist₂_sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [deltaDeriv_apply,
    show (∏ i ∈ Finset.range (j : ℕ), (-(-a - 1) - 1 - (i : ℤ)))
        = ∏ i ∈ Finset.range (j : ℕ), (a - (i : ℤ)) from
      Finset.prod_congr rfl (fun i _ => by ring)]
  congr 1
  rw [mode_apply]
  congr 1
  ring

/-- **The super commutator formula with a shared bound.**  One `bracket_deltaSumε` yields
*both* the vanishing `u₍ₖ₎v = 0` for `k ≥ N` and the commutator formula with the same `N` —
the form the Pascal induction consumes.  The right-hand side carries **no** Koszul sign. -/
theorem commBoundε (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ V.parity p)
    (hv : v ∈ V.parity q) (m n : ℤ) :
    ∃ N : ℕ, (∀ k : ℕ, N ≤ k → V.smul u k v = 0)
      ∧ modeBracketε (koszul p q) (V.Y u) (V.Y v) m n
        = ∑ j : Fin N, gBinom m (j : ℕ) • mode (V.Y (V.smul u (j : ℕ) v)) (m + n - (j : ℕ)) := by
  obtain ⟨N, c, hdecomp⟩ := bracket_deltaSumε V hu hv
  refine ⟨N, ?_, ?_⟩
  · intro k hk
    have h1 : V.Y (V.smul u k v) = cCoeff k (bracketDistε (koszul p q) (V.Y u) (V.Y v)) :=
      (nth_productε V hu hv k).symm
    rw [hdecomp, cCoeff_sum, Finset.sum_eq_zero (fun j _ => by
        rw [cCoeff_deltaDeriv, if_neg (by have h := j.2; omega)])] at h1
    have h2 : V.smul u k v = mode (V.Y (V.smul u k v)) (-1) V.vacuum :=
      (V.smul_neg_one_vacuum (V.smul u k v)).symm
    rw [h2, h1, mode_apply]; rfl
  · rw [mode_bracket_opeε V (koszul p q) u v hdecomp m n]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hne : ((j : ℕ).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hcj : c j = (((j : ℕ).factorial : ℂ)⁻¹) • V.Y (V.smul u (j : ℕ) v) := by
      have hrec := cCoeff_deltaSum c j
      rw [← hdecomp, nth_productε V hu hv] at hrec
      rw [hrec, ← Int.cast_smul_eq_zsmul ℂ ((j : ℕ).factorial : ℤ), Int.cast_natCast, smul_smul,
        inv_mul_cancel₀ hne, one_smul]
    rw [hcj, mode_smul,
      ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range (j : ℕ), (m - (i : ℤ))), smul_smul]
    congr 1
    rw [gBinom, div_eq_mul_inv]
    congr 1
    push_cast
    rfl

/-- **The super commutator formula 5.1.7c**: `u₍ₐ₎v₍ᵦ₎ − ε·v₍ᵦ₎u₍ₐ₎
= ∑_j C(a,j)·(u₍ⱼ₎v)₍ₐ₊ᵦ₋ⱼ₎`, with `ε = (-1)^{|u||v|}` and no sign on the right. -/
theorem mode_commutatorε (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ V.parity p)
    (hv : v ∈ V.parity q) (a b : ℤ) :
    ∃ N : ℕ, modeBracketε (koszul p q) (V.Y u) (V.Y v) a b
      = ∑ j : Fin N, gBinom a (j : ℕ) • mode (V.Y (V.smul u (j : ℕ) v)) (a + b - (j : ℕ)) := by
  obtain ⟨N, _, h⟩ := commBoundε V hu hv a b
  exact ⟨N, h⟩

/-! ## §5  The nonnegative iterate -/

/-- The nonnegative iterate in `Nat.choose` form. -/
theorem mode_iterate_nonneg_chooseε (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u v : 𝒱}
    (hu : u ∈ V.parity p) (hv : v ∈ V.parity q) (k : ℕ) (n : ℤ) :
    mode (V.Y (V.smul u (k : ℤ) v)) n =
      ∑ r ∈ Finset.range (k + 1), (((-1 : ℤ) ^ (k - r)) * (k.choose r : ℤ)) •
        (mode (V.Y u) (r : ℤ) * mode (V.Y v) (n + ((k - r : ℕ) : ℤ))
          - koszul p q • (mode (V.Y v) (n + ((k - r : ℕ) : ℤ)) * mode (V.Y u) (r : ℤ))) := by
  rw [← nth_productε V hu hv k, mode_apply, cCoeff_apply, mulBySubPow_apply_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [bracketDistε_apply, show (-1 : ℤ) - (r : ℤ) = -(r : ℤ) - 1 from by ring,
    show (-n - 1) - ((k - r : ℕ) : ℤ) = -(n + ((k - r : ℕ) : ℤ)) - 1 from by ring]
  simp only [mode_apply]

/-- The nonnegative iterate in the project's generalized-binomial convention. -/
theorem mode_iterate_nonnegε (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u v : 𝒱}
    (hu : u ∈ V.parity p) (hv : v ∈ V.parity q) (k : ℕ) (n : ℤ) :
    mode (V.Y (V.smul u (k : ℤ) v)) n =
      ∑ r ∈ Finset.range (k + 1), (((-1 : ℂ) ^ (k - r)) * gBinom (k : ℤ) r) •
        (mode (V.Y u) (r : ℤ) * mode (V.Y v) (n + ((k - r : ℕ) : ℤ))
          - koszul p q • (mode (V.Y v) (n + ((k - r : ℕ) : ℤ)) * mode (V.Y u) (r : ℤ))) := by
  rw [mode_iterate_nonneg_chooseε V hu hv]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  have hrle : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  rw [gBinom_natCast_eq_choose hrle,
    ← Int.cast_smul_eq_zsmul ℂ (((-1 : ℤ) ^ (k - r)) * (k.choose r : ℤ))]
  congr 1
  push_cast
  rfl

/-- **The super iterate formula 5.1.7d, `ℓ = k ≥ 0`, in Borcherds form.**  The Koszul sign
multiplies `(-1)^k` on the exchanged term — exactly the `koszul p q * negOnePow ℓ` of the
`SuperWeakModule.jacobi` shape. -/
theorem mode_iterate_borcherds_nonnegε (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u v : 𝒱}
    (hu : u ∈ V.parity p) (hv : v ∈ V.parity q) (k : ℕ) (n : ℤ) :
    mode (V.Y (V.smul u (k : ℤ) v)) n =
      ∑ i ∈ Finset.range (k + 1), ((-1 : ℂ) ^ i * gBinom (k : ℤ) i) •
        (mode (V.Y u) ((k : ℤ) - i) * mode (V.Y v) (n + i)
          - (koszul p q * (-1 : ℂ) ^ k) • (mode (V.Y v) ((k : ℤ) + n - i) * mode (V.Y u) i)) := by
  rw [mode_iterate_nonnegε V hu hv]
  simp only [smul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  · -- A-part (`u·v`): reflect `r ↦ k - r`
    rw [← Finset.sum_range_reflect
      (fun r => (((-1 : ℂ) ^ (k - r)) * gBinom (k : ℤ) r) •
        (mode (V.Y u) (r : ℤ) * mode (V.Y v) (n + ((k - r : ℕ) : ℤ)))) (k + 1)]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [show k + 1 - 1 - i = k - i from by omega, Nat.sub_sub_self hik, gBinom_symm_nat hik,
      Nat.cast_sub hik]
  · -- B-part (`v·u`): index `r = i`, sign/symmetry identity, `ε` a spectator scalar
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Nat.cast_sub hik, smul_smul, smul_smul,
      show n + ((k : ℤ) - i) = (k : ℤ) + n - i from by ring]
    congr 1
    rw [show ((-1 : ℂ) ^ (k - i) * gBinom (k : ℤ) i) * koszul p q
          = koszul p q * ((-1 : ℂ) ^ (k - i) * gBinom (k : ℤ) i) from by ring,
      show ((-1 : ℂ) ^ i * gBinom (k : ℤ) i) * (koszul p q * (-1 : ℂ) ^ k)
          = koszul p q * ((-1 : ℂ) ^ i * (-1 : ℂ) ^ k * gBinom (k : ℤ) i) from by ring]
    congr 2
    rw [← pow_add, show i + k = (k - i) + 2 * i from by omega, pow_add, pow_mul]
    simp

end SuperNearVOA

end VOA
