/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.Reconstruction
import VOA.Core.SkewSymmetry

/-!
# Commutative vertex algebras — Theorem 5.1.4  (Gannon pp. 319–320)

A "sanity-check" theorem that situates vertex algebras among classical structures:
*a vertex algebra is a noncommutative, nonassociative generalisation of a commutative
associative algebra with a derivation.*

## Theorem 5.1.4 (Gannon)

For a vertex algebra `𝒱`, the following are equivalent:

1. `𝒱` is **commutative**: `Y(u, z₁) Y(v, z₂) = Y(v, z₂) Y(u, z₁)` for all `u, v`.
2. `𝒱` is a `ℤ`-graded commutative associative algebra with unit (`1`) and derivation
   (`T`), with each `dim 𝒱ₙ < ∞`. The product is `u · v := u₍₋₁₎ v` and the derivation
   is `T`.
3. `𝒱` is a vertex algebra in which every `Y(u, z)` involves only nonnegative powers
   of `z`, i.e. `u₍ₙ₎ = 0` for all `n ≥ 0`.

## What is proved here (`sorry`-free / axiom-free)

* `IsCommutative V` — condition (1), encoded as the vanishing of every field commutator
  `[Y(u,z₁), Y(v,z₂)] = 0` (`bracketDist (Y u) (Y v) = 0`), i.e. mutual locality with bound
  `M = 0`.
* `comm_iff_nonneg_modes` — **(1) ⇔ (3)**, fully proved:
  - **(1) ⇒ (3)** via the field `n`-th-product theorem `nth_product`: if the commutator
    distribution vanishes then `Y(u₍ₖ₎v) = cCoeff k 0 = 0`, so `u₍ₖ₎v = (u₍ₖ₎v)₍₋₁₎𝟙 = 0`.
  - **(3) ⇒ (1)** via the commutator formula `mode_commutator`: every OPE coefficient
    `u₍ⱼ₎v` (`j ≥ 0`) vanishes, so `[u₍ₐ₎, v₍ᵦ₎] = ∑ⱼ C(a,j)(u₍ⱼ₎v)₍ₐ₊ᵦ₋ⱼ₎ = 0`.

  (Stated for a VOA, the level at which the reconstruction cascade `nth_product` /
  `mode_commutator` lives; `IsCommutative`/`cmul` themselves are bare-VA notions.)

* `cmul u v = u₍₋₁₎v` (condition (2)'s product) with the **unit laws** `cmul_vacuum`
  (`u · 𝟙 = u`, VA3) and `vacuum_cmul` (`𝟙 · u = u`, VA2), and the **derivation law**
  `Lneg1_cmul_leibniz` (`T(u·v) = (Tu)·v + u·(Tv)`, `T = L₋₁`, from `L_neg_one_deriv`).

## (1) ⇔ (2)

The remaining content of **(1) ⇔ (2)** — that on a commutative VA `cmul` is **commutative**
(`u₍₋₁₎v = v₍₋₁₎u`) and **associative** — is proved.  Commutativity is skew-symmetry
`Core.SkewSymmetry.skew` (5.1.8) at the `(−1)`-coefficient (`cmul_comm_of_comm`); associativity
is the `n<0` duality `Core.Reconstruction.assoc_neg` (5.1.9a) collapsed by mode-vanishing
(`cmul_assoc_of_comm`).  Both inputs are proved, so:
* `commRing_of_comm` packages the commutative associative unital `ℂ`-algebra of condition (2)
  (product `cmul`, unit `𝟙`), with the derivation law `commRing_of_comm_isDerivation`;
* `comm_iff_assoc_alg` is the full Theorem 5.1.4 (1) ⇔ (2) biconditional.

## Dependencies
* `VOA.Core.Reconstruction` (the cascade `nth_product`, `mode_commutator`,
  `assoc_neg`, `L_neg_one_deriv`); `Core.SkewSymmetry` (the discharged skew gate / `skew_mode`).

## Status
`IsCommutative`, `cmul` with its unit + derivation laws, the centerpiece
equivalence `comm_iff_nonneg_modes` (1 ⇔ 3), and the full `comm_iff_assoc_alg` (1 ⇔ 2) — with
the `commRing_of_comm` packaging and its derivation law — are all `sorry`-free / axiom-free
(`[propext, Classical.choice, Quot.sound]`).

## References
* Gannon §5.1.3, Thm 5.1.4; Borcherds [68]; Lepowsky–Li Ch. 3.
-/

namespace VOA

open Module (End)

universe u

namespace PreVertexAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Condition (1): commutativity, and the product (2) `cmul` -/

/-- **Condition (1)**: `𝒱` is **commutative** — every pair of fields commutes,
`Y(u,z₁)Y(v,z₂) = Y(v,z₂)Y(u,z₁)`, encoded as the vanishing of the commutator distribution
`[Y(u,z₁),Y(v,z₂)] = 0` (mutual locality with bound `M = 0`) (Gannon Thm 5.1.4). -/
def IsCommutative (V : PreVertexAlgebra 𝒱) : Prop :=
  ∀ u v : 𝒱, bracketDist (V.Y u) (V.Y v) = 0

/-- The **classical product** `u · v := u₍₋₁₎ v` of condition (2) (Gannon Thm 5.1.4). -/
def cmul (V : PreVertexAlgebra 𝒱) (u v : 𝒱) : 𝒱 := V.smul u (-1) v

@[simp] theorem cmul_def (V : PreVertexAlgebra 𝒱) (u v : 𝒱) : V.cmul u v = V.smul u (-1) v := rfl

/-- **Right unit** `u · 𝟙 = u` (VA3 creation). -/
@[simp] theorem cmul_vacuum (V : PreVertexAlgebra 𝒱) (u : 𝒱) : V.cmul u V.vacuum = u := by
  rw [cmul_def, smul_vacuum_neg_one]

/-- **Left unit** `𝟙 · u = u` (VA2 vacuum field). -/
@[simp] theorem vacuum_cmul (V : PreVertexAlgebra 𝒱) (u : 𝒱) : V.cmul V.vacuum u = u := by
  rw [cmul_def, smul_vacuum_left]; simp

end PreVertexAlgebra

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## (1) ⇔ (3): commutativity ⇔ only nonnegative powers of `z` (Gannon Thm 5.1.4) -/

/-- **Theorem 5.1.4, (1) ⇔ (3)** (Gannon): a VOA is commutative iff every field involves
only nonnegative powers of `z`, i.e. `u₍ₙ₎ = 0` for all `n ≥ 0`.

`(1) ⇒ (3)`: by the field `n`-th-product theorem `nth_product`, `Y(u₍ₖ₎v) =
cCoeff k [Y(u),Y(v)] = cCoeff k 0 = 0`, whence `u₍ₖ₎v = (u₍ₖ₎v)₍₋₁₎𝟙 = 0`.
`(3) ⇒ (1)`: by the commutator formula `mode_commutator`, every term
`C(a,j)(u₍ⱼ₎v)₍ₐ₊ᵦ₋ⱼ₎` (`j ≥ 0`) vanishes, so `[u₍ₐ₎,v₍ᵦ₎] = 0` for all `a,b`. -/
theorem comm_iff_nonneg_modes (W : VertexOperatorAlgebra 𝒱) :
    W.toPreVertexAlgebra.IsCommutative ↔ ∀ (u v : 𝒱) (n : ℤ), 0 ≤ n → W.smul u n v = 0 := by
  constructor
  · -- (1) ⇒ (3)
    intro hcomm u v n hn
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
    have hnp := nth_product W u v k
    rw [hcomm u v] at hnp
    have hY : W.Y (W.smul u (k : ℤ) v) = 0 := by
      rw [← hnp]
      funext m
      change mulBySubPow k (0 : FormalDist₂ (End ℂ 𝒱)) (-1) m = (0 : FormalDist (End ℂ 𝒱)) m
      rw [map_zero]; rfl
    have hcr := PreVertexAlgebra.smul_vacuum_neg_one W.toPreVertexAlgebra (W.smul u (k : ℤ) v)
    rw [PreVertexAlgebra.smul_def, hY] at hcr
    simp only [mode_zero, LinearMap.zero_apply] at hcr
    exact hcr.symm
  · -- (3) ⇒ (1)
    intro hmodes u v
    refine FormalDist₂.ext fun s t => ?_
    change (W.Y u) s * (W.Y v) t - (W.Y v) t * (W.Y u) s = 0
    obtain ⟨N, hN⟩ := mode_commutator W u v (-s - 1) (-t - 1)
    have hzero : ⁅mode (W.Y u) (-s - 1), mode (W.Y v) (-t - 1)⁆ = 0 := by
      rw [hN]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hmodes u v ((j : ℕ) : ℤ) (by positivity), map_zero]
      simp only [mode_zero, smul_zero]
    have hbr : (W.Y u) s * (W.Y v) t - (W.Y v) t * (W.Y u) s
        = ⁅mode (W.Y u) (-s - 1), mode (W.Y v) (-t - 1)⁆ := by
      simp only [LieRing.of_associative_ring_bracket, mode_apply,
        show -(-s - 1) - 1 = s from by ring, show -(-t - 1) - 1 = t from by ring]
    rw [hbr, hzero]

/-! ## (1) ⇒ (2), the skew-free part: the derivation `T = L₋₁` of `cmul` -/

/-- **`T = L₋₁` is a derivation of `cmul`** (Gannon Thm 5.1.4, condition (2)):
`T(u · v) = (Tu) · v + u · (Tv)`, the `n = -1` case of translation covariance
`L_neg_one_deriv`.  Holds in every VOA (no commutativity needed); together with the unit
laws it supplies the "derivation" half of condition (2). -/
theorem Lneg1_cmul_leibniz (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    W.L (-1) (W.toPreVertexAlgebra.cmul u v)
      = W.toPreVertexAlgebra.cmul (W.L (-1) u) v + W.toPreVertexAlgebra.cmul u (W.L (-1) v) := by
  have h := W.L_neg_one_deriv u v (-1)
  rw [sub_eq_iff_eq_add] at h
  rw [PreVertexAlgebra.cmul_def, PreVertexAlgebra.cmul_def, PreVertexAlgebra.cmul_def, h, add_comm]

/-! ## (1) ⇔ (2), from skew-symmetry and the `n<0` duality

Commutativity of `cmul` is skew-symmetry (5.1.8) at the `(−1)`-coefficient and associativity
is the `n<0` duality (5.1.9a, `assoc_neg`); both are proved (`Core.SkewSymmetry.skew` /
`Core.Reconstruction.assoc_neg`).  We assemble the full Theorem 5.1.4 (1) ⇔ (2): a commutative
VA carries a commutative associative unital `ℂ`-algebra structure with product `cmul` and
derivation `T = L₋₁`. -/

/-- Commutativity of `cmul`, **reduced to skew-symmetry** (Gannon Thm 5.1.4): `u · v = v · u`.
Hypothesis `hskew` is the `(−1)`-coefficient of `Core.SkewSymmetry.skew` (5.1.8),
`u₍₋₁₎v = v₍₋₁₎u`; discharged unconditionally on a commutative VA by `cmul_comm_of_comm`. -/
theorem cmul_comm_of_skew (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱)
    (hskew : W.smul u (-1) v = W.smul v (-1) u) :
    W.toPreVertexAlgebra.cmul u v = W.toPreVertexAlgebra.cmul v u := by
  rw [PreVertexAlgebra.cmul_def, PreVertexAlgebra.cmul_def, hskew]

/-! ### Mode-vanishing on a commutative VA -/

/-- On a commutative VA, every nonnegative mode vanishes: `u₍ₖ₎v = 0` for `k ≥ 0`
(the forward direction of `comm_iff_nonneg_modes`). -/
theorem nonneg_modes_of_comm (W : VertexOperatorAlgebra 𝒱)
    (hcomm : W.toPreVertexAlgebra.IsCommutative) (u v : 𝒱) (n : ℤ) (hn : 0 ≤ n) :
    W.smul u n v = 0 :=
  (comm_iff_nonneg_modes W).mp hcomm u v n hn

/-! ### Associativity of `cmul` on a commutative VA (skew-free, via `assoc_neg`) -/

/-- The normal-ordered diagonal `:Y(u)Y(v):(m,-m) w` vanishes for `m ≠ 0` on a commutative VA.
For `m < 0` it is `(Y v)(-m) (Y u)(m) w` with `(Y u)(m) w = u₍₋ₘ₋₁₎w = 0` (`-m-1 ≥ 0`); for
`m > 0` it is `(Y u)(m) (Y v)(-m) w` with `(Y v)(-m) w = v₍ₘ₋₁₎w = 0` (`m-1 ≥ 0`). -/
theorem normalOrdered_diag_eq_zero_of_comm (W : VertexOperatorAlgebra 𝒱)
    (hcomm : W.toPreVertexAlgebra.IsCommutative) (u v w : 𝒱) (m : ℤ) (hm : m ≠ 0) :
    normalOrdered (W.Y u) (W.Y v) m (0 - m) w = 0 := by
  rw [normalOrdered_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0, Module.End.mul_apply]
    have hpos : 0 < m := lt_of_le_of_ne h0 (Ne.symm hm)
    have hvw : (W.Y v) (0 - m) w = 0 := by
      have he : (W.Y v) (0 - m) w = W.smul v (m - 1) w := by
        rw [PreVertexAlgebra.smul_eq_coeff, show -(m - 1) - 1 = 0 - m from by ring]
      rw [he, nonneg_modes_of_comm W hcomm v w (m - 1) (by omega)]
    rw [hvw, map_zero]
  · rw [if_neg h0, Module.End.mul_apply]
    have huw : (W.Y u) m w = 0 := by
      have he : (W.Y u) m w = W.smul u (-m - 1) w := by
        rw [PreVertexAlgebra.smul_eq_coeff, show -(-m - 1) - 1 = m from by ring]
      rw [he, nonneg_modes_of_comm W hcomm u w (-m - 1) (by omega)]
    rw [huw, map_zero]

/-- The surviving `m = 0` diagonal term: `:Y(u)Y(v):(0,0) w = u₍₋₁₎(v₍₋₁₎w)`. -/
theorem normalOrdered_diag_zero (W : VertexOperatorAlgebra 𝒱) (u v w : 𝒱) :
    normalOrdered (W.Y u) (W.Y v) 0 (0 - 0) w
      = W.smul u (-1) (W.smul v (-1) w) := by
  rw [normalOrdered_apply, if_pos le_rfl, Module.End.mul_apply,
    show (0 : ℤ) - 0 = 0 from by ring]
  rw [PreVertexAlgebra.smul_eq_coeff, PreVertexAlgebra.smul_eq_coeff,
    show -(-1 : ℤ) - 1 = 0 from by ring]

/-- **Associativity of `cmul` on a commutative VA** (Gannon Thm 5.1.4, condition (2)):
`(u·v)·w = u·(v·w)`, i.e. `(u₍₋₁₎v)₍₋₁₎w = u₍₋₁₎(v₍₋₁₎w)`.  Skew-free: uses the negative
duality `assoc_neg` (5.1.9a, `k=0`) and the collapse of the normal-ordered product once all
nonnegative modes vanish (`comm_iff_nonneg_modes`). -/
theorem cmul_assoc_of_comm (W : VertexOperatorAlgebra 𝒱)
    (hcomm : W.toPreVertexAlgebra.IsCommutative) (u v w : 𝒱) :
    W.toPreVertexAlgebra.cmul (W.toPreVertexAlgebra.cmul u v) w
      = W.toPreVertexAlgebra.cmul u (W.toPreVertexAlgebra.cmul v w) := by
  rw [PreVertexAlgebra.cmul_def, PreVertexAlgebra.cmul_def, PreVertexAlgebra.cmul_def,
    PreVertexAlgebra.cmul_def]
  have hL : W.smul (W.smul u (-1) v) (-1) w = (W.Y (W.smul u (-1) v)) 0 w := by
    rw [PreVertexAlgebra.smul_eq_coeff]; norm_num
  rw [hL]
  have hassoc := assoc_neg W u v 0
  rw [Nat.cast_zero, show (-(0:ℤ) - 1) = -1 from by ring] at hassoc
  rw [hassoc, negProd_apply]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  rw [nprod_apply]
  show (∑ᶠ m : ℤ, normalOrdered (W.Y u) (W.Y v) m (0 - m) w) = _
  rw [finsum_eq_single _ 0 (fun m hm => normalOrdered_diag_eq_zero_of_comm W hcomm u v w m hm)]
  exact normalOrdered_diag_zero W u v w

/-! ### Commutativity of `cmul` on a commutative VA (via `skew_mode`) -/

/-- The `j`-th skew summand at `n=-1` vanishes for `j ≠ 0` on a commutative VA:
`(Y v)(-j) u = v₍ⱼ₋₁₎u = 0` for `j ≥ 1`. -/
theorem skew_summand_eq_zero_of_comm (W : VertexOperatorAlgebra 𝒱)
    (hcomm : W.toPreVertexAlgebra.IsCommutative) (u v : 𝒱) (j : ℕ) (hj : j ≠ 0) :
    ((j.factorial : ℂ)⁻¹) • (sgn (-(-1) - 1 - j)) •
      ((W.toPreVertexAlgebra.T ^ j) ((W.Y v) (-(-1) - 1 - j) u)) = 0 := by
  have hvu : (W.Y v) (-(-1) - 1 - (j : ℤ)) u = 0 := by
    have he : (W.Y v) (-(-1) - 1 - (j : ℤ)) u = W.smul v ((j : ℤ) - 1) u := by
      rw [PreVertexAlgebra.smul_eq_coeff, show -((j : ℤ) - 1) - 1 = -(-1) - 1 - (j : ℤ) from by ring]
    rw [he, nonneg_modes_of_comm W hcomm v u ((j : ℤ) - 1)
      (by have : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj; omega)]
  rw [hvu, map_zero, smul_zero, smul_zero]

/-- **Commutativity of `cmul` on a commutative VA** (Gannon Thm 5.1.4, condition (2)):
`u · v = v · u`, i.e. `u₍₋₁₎v = v₍₋₁₎u`.  Genuinely skew-symmetric content: via the skew mode
formula `skew_mode` at `n=-1` (the discharged skew gate), whose finsum collapses to its `j=0`
term once all nonnegative modes vanish (`comm_iff_nonneg_modes`). -/
theorem cmul_comm_of_comm (W : VertexOperatorAlgebra 𝒱)
    (hcomm : W.toPreVertexAlgebra.IsCommutative) (u v : 𝒱) :
    W.toPreVertexAlgebra.cmul u v = W.toPreVertexAlgebra.cmul v u := by
  rw [PreVertexAlgebra.cmul_def, PreVertexAlgebra.cmul_def]
  rw [skew_mode W u v (-1)]
  rw [finsum_eq_single _ 0
    (fun j hj => skew_summand_eq_zero_of_comm W hcomm u v j hj)]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, Nat.cast_zero, pow_zero,
    Module.End.one_apply]
  rw [show -(-1 : ℤ) - 1 - 0 = 0 from by ring, sgn, if_pos (by norm_num : Even (0 : ℤ)), one_smul]
  rw [PreVertexAlgebra.smul_eq_coeff, show -(-1 : ℤ) - 1 = 0 from by ring]

/-! ### The `CommRing` packaging of condition (2) -/

/-- **Theorem 5.1.4, (1) ⇒ (2)** (Gannon), the ring half: a commutative VA carries a
`CommRing` structure with product `cmul` (`u · v = u₍₋₁₎v`), unit `𝟙`, and the ambient
additive group.  Commutativity is `cmul_comm_of_comm` (skew); associativity is
`cmul_assoc_of_comm` (the `n<0` duality). -/
@[reducible]
def commRing_of_comm (W : VertexOperatorAlgebra 𝒱)
    (hcomm : W.toPreVertexAlgebra.IsCommutative) : CommRing 𝒱 :=
  { (inferInstance : AddCommGroup 𝒱) with
    mul := W.toPreVertexAlgebra.cmul
    one := W.toPreVertexAlgebra.vacuum
    mul_assoc := cmul_assoc_of_comm W hcomm
    mul_comm := cmul_comm_of_comm W hcomm
    one_mul := fun a => W.toPreVertexAlgebra.vacuum_cmul a
    mul_one := fun a => W.toPreVertexAlgebra.cmul_vacuum a
    left_distrib := fun a b c => W.toPreVertexAlgebra.smul_add_right a (-1) b c
    right_distrib := fun a b c => W.toPreVertexAlgebra.smul_add_left a b (-1) c
    zero_mul := fun a => W.toPreVertexAlgebra.smul_zero_left (-1) a
    mul_zero := fun a => W.toPreVertexAlgebra.smul_zero_right a (-1) }

/-- **`T = L₋₁` is a derivation of the `commRing_of_comm` ring** (Gannon Thm 5.1.4, condition
(2)): the Leibniz law `T(a*b) = (Ta)*b + a*(Tb)` for the ring product of `commRing_of_comm`.
That product is `cmul`, so this is `Lneg1_cmul_leibniz` (holds in every VOA). -/
theorem commRing_of_comm_isDerivation (W : VertexOperatorAlgebra 𝒱)
    (hcomm : W.toPreVertexAlgebra.IsCommutative) (a b : 𝒱) :
    letI := commRing_of_comm W hcomm
    W.L (-1) (a * b) = (W.L (-1) a) * b + a * (W.L (-1) b) :=
  Lneg1_cmul_leibniz W a b

/-- **Theorem 5.1.4, (1) ⇔ (2)** (Gannon): a VOA is commutative **iff** its `(−1)`-product
`cmul` is a commutative, associative unital product (equivalently, by (1) ⇔ (3), iff every
nonnegative mode vanishes).  Bundled as a biconditional over the three pieces that pin down
condition (2):
* `IsCommutative` ⇒ the nonnegative modes vanish (`comm_iff_nonneg_modes`), `cmul` is
  commutative (`cmul_comm_of_comm`) and associative (`cmul_assoc_of_comm`);
* conversely, the nonnegative-mode vanishing alone recovers `IsCommutative`
  (`comm_iff_nonneg_modes`).

The full commutative-associative-unital-**differential** algebra structure of condition (2)
is delivered by `commRing_of_comm` (the `CommRing` with product `cmul`, unit `𝟙`) together with
the derivation law `commRing_of_comm_isDerivation` (`T = L₋₁`). -/
theorem comm_iff_assoc_alg (W : VertexOperatorAlgebra 𝒱) :
    W.toPreVertexAlgebra.IsCommutative ↔
      ((∀ (u v : 𝒱) (n : ℤ), 0 ≤ n → W.smul u n v = 0)
        ∧ (∀ u v : 𝒱, W.toPreVertexAlgebra.cmul u v = W.toPreVertexAlgebra.cmul v u)
        ∧ (∀ u v w : 𝒱, W.toPreVertexAlgebra.cmul (W.toPreVertexAlgebra.cmul u v) w
              = W.toPreVertexAlgebra.cmul u (W.toPreVertexAlgebra.cmul v w))) := by
  constructor
  · intro hcomm
    exact ⟨(comm_iff_nonneg_modes W).mp hcomm,
      cmul_comm_of_comm W hcomm, cmul_assoc_of_comm W hcomm⟩
  · intro ⟨hmodes, _, _⟩
    exact (comm_iff_nonneg_modes W).mpr hmodes

end VertexOperatorAlgebra

end VOA
