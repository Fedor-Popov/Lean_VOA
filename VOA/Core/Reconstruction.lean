/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.Goddard
import VOA.Core.Identities
import VOA.Core.Dong
import VOA.Core.OPE
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.Module

/-!
# The reconstruction cascade  (Gannon §5.1.3, eqs. 5.1.7–5.1.9)

With **Dong's lemma** (`Core.Dong.dong_nonneg`) discharging the "local with every `Y(b,z)`"
hypothesis of **Goddard uniqueness** (`Core.Goddard.goddard_uniqueness`), the whole
reconstruction cascade opens up.

This file builds, in dependency order:

* **Translation covariance** `[L₋₁, Y(u,z)] = ∂_z Y(u,z)` (bracket form): the field
  `[L₋₁, Y(u,·)] = Res_{z₁}[Y(ω,z₁),Y(u,·)]` is local with everything (Dong) and creates
  `L₋₁u` from the vacuum (clean, since `ω₍₀₎ = L₋₁ = T` commutes with `Tᵐ`), so Goddard
  identifies it with `Y(L₋₁u,·)`.

## Dependencies
* `VOA.Core.Goddard`, `VOA.Core.Identities`, `VOA.Core.Dong`.

## Status
Every target in this file is proved `sorry`-free / axiom-free
(`#print axioms = [propext, Classical.choice, Quot.sound]`): translation covariance, the
nonnegative duality **`assoc_nonneg`** (5.1.9b) and **`nth_product`**, **`mode_commutator`**
(5.1.7c), the nonnegative iterate, and — via the **`n<0` Dong's lemma**
(`Core.Dong.dong_neg`), the normal-ordered product `negProd`, and `goddard_uniqueness` — the
negative duality **`assoc_neg`** (5.1.9a).  The `e^{z₀T}`-conjugation iterate
`(ad L₋₁)^j Y(u,z) = ∂_z^j Y(u,z)` (`adLneg1_pow_Ycoeff`, `adLneg1_pow_eq_deriv_pow`) — the
field/operator companion of the state-side `Y_Tpow` — is also proved.  Skew-symmetry
(`Core.SkewSymmetry.skew`) and the full arbitrary-`(ℓ,m,n)` Borcherds identity
(`Core.Borcherds.borcherds`) build on this cascade and are likewise closed.

## References
* Gannon §5.1.3; Kac, *VA for Beginners*, §4; Lepowsky–Li, Ch. 3.
-/

namespace VOA

open Module (End)

universe u

/-! ## The two-variable total derivative and residue-by-parts -/

section Deriv2

variable {𝒲 : Type*} [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-- The total derivative `∂ = ∂₁ + ∂₂` on a two-variable distribution:
`(∂G)(s,t) = (s+1)·G(s+1,t) + (t+1)·G(s,t+1)`.  It annihilates `(z₁-z₂)`, hence commutes
with multiplication by `(z₁-z₂)` (`deriv2_mulBySub`). -/
def deriv2 (G : FormalDist₂ 𝒲) : FormalDist₂ 𝒲 :=
  fun s t => (s + 1) • G (s + 1) t + (t + 1) • G s (t + 1)

@[simp] theorem deriv2_apply (G : FormalDist₂ 𝒲) (s t : ℤ) :
    deriv2 G s t = (s + 1) • G (s + 1) t + (t + 1) • G s (t + 1) := rfl

/-- The total derivative commutes with `(z₁-z₂)·` (because `∂(z₁-z₂) = 0`). -/
theorem deriv2_mulBySub (G : FormalDist₂ 𝒲) : deriv2 (mulBySub G) = mulBySub (deriv2 G) := by
  apply FormalDist₂.ext; intro s t
  simp only [deriv2_apply, mulBySub_apply, smul_sub,
    show ∀ x : ℤ, x + 1 - 1 = x from fun x => by ring,
    show ∀ x : ℤ, x - 1 + 1 = x from fun x => by ring]
  module

/-- Iterated: `∂` commutes with `(z₁-z₂)ᵏ`. -/
theorem deriv2_mulBySubPow (k : ℕ) (G : FormalDist₂ 𝒲) :
    deriv2 (mulBySubPow k G) = mulBySubPow k (deriv2 G) := by
  induction k generalizing G with
  | zero => rfl
  | succ j ih => rw [mulBySubPow_succ, LinearMap.comp_apply, deriv2_mulBySub, ih,
      ← LinearMap.comp_apply, ← mulBySubPow_succ]

/-- **Residue-by-parts** (Gannon 5.1.3b): `Res_{z₁}((z₁-z₂)ᵏ ∂F) = (m+1)·Res_{z₁}((z₁-z₂)ᵏF)`
read off at the `z₂^m`-coefficient.  (The `∂₁` part dies at the residue `z₁=-1` because its
weight is `0`; only the `∂₂` part survives.) -/
theorem resByParts (k : ℕ) (F : FormalDist₂ 𝒲) (m : ℤ) :
    mulBySubPow k (deriv2 F) (-1) m = (m + 1) • mulBySubPow k F (-1) (m + 1) := by
  rw [← deriv2_mulBySubPow, deriv2_apply, show (-1 + 1 : ℤ) = 0 by ring, zero_smul, zero_add]

/-- If `g` vanishes on the quadrant `{s≤-1, t≤-1}`, so does `(z₁-z₂)ʲ·g` (the quadrant is
preserved by the index shifts). -/
theorem mulBySubPow_zero_of_quadrant {g : FormalDist₂ 𝒲}
    (hg : ∀ s t : ℤ, s ≤ -1 → t ≤ -1 → g s t = 0) (j : ℕ) :
    ∀ s t : ℤ, s ≤ -1 → t ≤ -1 → mulBySubPow j g s t = 0 := by
  induction j with
  | zero => intro s t hs ht; exact hg s t hs ht
  | succ i ih =>
      intro s t hs ht
      rw [mulBySubPow_succ, LinearMap.comp_apply, mulBySub_apply, ih (s - 1) t (by omega) ht,
        ih s (t - 1) hs (by omega), sub_zero]

/-- On the line `t=0`, `(z₁-z₂)ʲ·g` shifts the `z₁`-index: `((z₁-z₂)ʲg)(a,0) = g(a-j,0)` for
`a≤-1` (the `t=-1` boundary term dies by `mulBySubPow_zero_of_quadrant`). -/
theorem mulBySubPow_diag_of_quadrant {g : FormalDist₂ 𝒲}
    (hg : ∀ s t : ℤ, s ≤ -1 → t ≤ -1 → g s t = 0) (j : ℕ) :
    ∀ a : ℤ, a ≤ -1 → mulBySubPow j g a 0 = g (a - j) 0 := by
  induction j with
  | zero => intro a ha; simp
  | succ i ih =>
      intro a ha
      rw [mulBySubPow_succ, LinearMap.comp_apply, mulBySub_apply,
        mulBySubPow_zero_of_quadrant hg i a (0 - 1) ha (by omega), sub_zero, ih (a - 1) (by omega),
        show a - 1 - (i : ℤ) = a - ((i + 1 : ℕ) : ℤ) from by push_cast; ring]

/-- At the residue `z₁=-1`, a `j`-th `δ`-derivative with `j≥1` vanishes (the falling
factorial `∏_{i<j}(-i)` has a zero factor). -/
theorem deltaDeriv_neg_one_zero {m : ℕ} (hm : 1 ≤ m) (c : FormalDist 𝒲) (n : ℤ) :
    deltaDeriv m c (-1) n = 0 := by
  have hp : (∏ i ∈ Finset.range m, (-(-1 : ℤ) - 1 - (i : ℤ))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_range.mpr hm) (by norm_num)
  rw [deltaDeriv_apply, hp, zero_smul]

/-- Peeling `(z₁-z₂)ᵏ` off a `j`-th `δ`-derivative (`k≤j`):
`(z₁-z₂)ᵏ·(c·∂ʲδ) = (∏_{i<k}(j-i))·(c·∂^{j-k}δ)`. -/
theorem mulBySubPow_deltaDeriv_peel (c : FormalDist 𝒲) (k : ℕ) :
    ∀ j : ℕ, k ≤ j →
      mulBySubPow k (deltaDeriv j c)
        = (∏ i ∈ Finset.range k, ((j : ℤ) - i)) • deltaDeriv (j - k) c := by
  induction k with
  | zero => intro j _; simp
  | succ k ih =>
      intro j h
      rw [mulBySubPow_succ, LinearMap.comp_apply, ih j (by omega), map_zsmul,
        show j - k = (j - (k + 1)) + 1 by omega, mulBySub_deltaDeriv, smul_smul,
        Finset.prod_range_succ]
      congr 1
      rw [show ((j - (k + 1) : ℕ) : ℤ) + 1 = (j : ℤ) - (k : ℤ) by omega]

/-- The `cCoeff k` of a `j`-th `δ`-derivative: `k!·c` if `j=k`, else `0`. -/
theorem cCoeff_deltaDeriv (k j : ℕ) (c : FormalDist 𝒲) :
    cCoeff k (deltaDeriv j c) = if j = k then ((k.factorial : ℤ) • c) else 0 := by
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · rw [if_neg (by omega)]
    funext n
    rw [cCoeff_apply, mulBySubPow_deltaDeriv_eq_zero (by omega)]
    rfl
  · subst hjk
    rw [if_pos rfl]
    funext n
    rw [cCoeff_apply, mulBySubPow_deltaDeriv_self]
    show (j.factorial : ℤ) • deltaDeriv 0 c (-1) n = (j.factorial : ℤ) • c n
    rw [deltaDeriv_apply]; simp
  · rw [if_neg (by omega)]
    funext n
    rw [cCoeff_apply, mulBySubPow_deltaDeriv_peel c k j (by omega)]
    show (∏ i ∈ Finset.range k, ((j : ℤ) - i)) • deltaDeriv (j - k) c (-1) n = 0
    rw [deltaDeriv_neg_one_zero (by omega) c n, smul_zero]

/-- `cCoeff k` is additive. -/
theorem cCoeff_add (k : ℕ) (f g : FormalDist₂ 𝒲) :
    cCoeff k (f + g) = cCoeff k f + cCoeff k g := by
  funext n; rw [cCoeff_apply, map_add]; rfl

/-- `cCoeff k` commutes with finite sums. -/
theorem cCoeff_sum {ι : Type*} (s : Finset ι) (k : ℕ) (f : ι → FormalDist₂ 𝒲) :
    cCoeff k (∑ i ∈ s, f i) = ∑ i ∈ s, cCoeff k (f i) := by
  classical
  induction s using Finset.induction with
  | empty => funext n; rw [cCoeff_apply]; show mulBySubPow k 0 (-1) n = (0 : FormalDist 𝒲) n
             rw [map_zero]; rfl
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cCoeff_add, ih]

/-- **OPE-coefficient recovery**: in a `δ`-derivative decomposition
`f = ∑_{j<N} cⱼ·∂ʲδ`, the `cₖ` are recovered by `cCoeff k f = k!·cₖ`. -/
theorem cCoeff_deltaSum {N : ℕ} (c : Fin N → FormalDist 𝒲) (k : Fin N) :
    cCoeff (k : ℕ) (∑ j : Fin N, deltaDeriv (j : ℕ) (c j)) = ((k : ℕ).factorial : ℤ) • c k := by
  rw [cCoeff_sum, Finset.sum_eq_single k]
  · rw [cCoeff_deltaDeriv, if_pos rfl]
  · intro j _ hjk
    rw [cCoeff_deltaDeriv, if_neg (fun h => hjk (Fin.ext h))]
  · intro h; exact absurd (Finset.mem_univ k) h

end Deriv2

/-! ## A two-variable binomial expansion for `(z₁-z₂)ᴺ` -/

section MulBySubPowSum

variable {𝒲 : Type*} [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-- Powers of the `z₁`-shift translate the first coefficient index. -/
theorem shiftZ₁_pow_apply (k : ℕ) (f : FormalDist₂ 𝒲) (m n : ℤ) :
    (((shiftZ₁ : Module.End ℂ (FormalDist₂ 𝒲)) ^ k) f) m n = f (m - (k : ℤ)) n := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, shiftZ₁_apply, ih]
      congr 1
      omega

/-- Powers of the negative `z₂`-shift translate the second coefficient index and contribute
the sign `(-1)^k`. -/
theorem neg_shiftZ₂_pow_apply (k : ℕ) (f : FormalDist₂ 𝒲) (m n : ℤ) :
    (((-shiftZ₂ : Module.End ℂ (FormalDist₂ 𝒲)) ^ k) f) m n =
      ((-1 : ℤ) ^ k) • f m (n - (k : ℤ)) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      change - ((((-shiftZ₂ : Module.End ℂ (FormalDist₂ 𝒲)) ^ k) f) m (n - 1)) = _
      rw [ih]
      rw [← neg_zsmul]
      congr 2
      · rw [pow_succ]
        ring
      · omega

/-- The two coordinate shifts commute. -/
theorem shiftZ₁_comm_shiftZ₂ : Commute (shiftZ₁ : Module.End ℂ (FormalDist₂ 𝒲)) shiftZ₂ := by
  show shiftZ₁ * shiftZ₂ = shiftZ₂ * shiftZ₁
  ext f m n
  simp only [Module.End.mul_apply, shiftZ₁_apply, shiftZ₂_apply]

/-- `mulBySubPow N` is the `N`-th power of the endomorphism `mulBySub`. -/
theorem mulBySubPow_eq_npow (N : ℕ) :
    (mulBySubPow N : Module.End ℂ (FormalDist₂ 𝒲))
      = (mulBySub : Module.End ℂ (FormalDist₂ 𝒲)) ^ N := by
  induction N with
  | zero => rfl
  | succ k ih =>
      rw [mulBySubPow_succ, ih, pow_succ']
      rfl

/-- Unfolding `mulBySub` as `z₁ - z₂` at the endomorphism level. -/
theorem mulBySub_eq_shiftZ₁_sub_shiftZ₂ :
    (mulBySub : Module.End ℂ (FormalDist₂ 𝒲)) = shiftZ₁ - shiftZ₂ := rfl

/-- **Coefficient binomial expansion** for `(z₁-z₂)ᴺ·f`. -/
theorem mulBySubPow_apply_sum (N : ℕ) (f : FormalDist₂ 𝒲) (m n : ℤ) :
    mulBySubPow N f m n =
      ∑ r ∈ Finset.range (N + 1), (((-1 : ℤ) ^ (N - r)) * (N.choose r : ℤ)) •
        f (m - (r : ℤ)) (n - ((N - r : ℕ) : ℤ)) := by
  rw [mulBySubPow_eq_npow, mulBySub_eq_shiftZ₁_sub_shiftZ₂]
  rw [sub_eq_add_neg]
  let S₁ : Module.End ℂ (FormalDist₂ 𝒲) := shiftZ₁
  let S₂ : Module.End ℂ (FormalDist₂ 𝒲) := shiftZ₂
  change (((S₁ + -S₂) ^ N) f) m n = _
  have hcomm : Commute S₁ (-S₂) := by
    dsimp [S₁, S₂]
    exact shiftZ₁_comm_shiftZ₂.neg_right
  rw [hcomm.add_pow N]
  rw [LinearMap.sum_apply (Finset.range (N + 1))
    (fun r => S₁ ^ r * (-S₂) ^ (N - r)
      * (↑(N.choose r) : Module.End ℂ (FormalDist₂ 𝒲))) f]
  rw [formalDist₂_sum_apply (Finset.range (N + 1))
    (fun d => (S₁ ^ d * (-S₂) ^ (N - d)
      * (↑(N.choose d) : Module.End ℂ (FormalDist₂ 𝒲))) f) m n]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Module.End.mul_apply, Module.End.mul_apply]
  dsimp [S₁, S₂]
  rw [shiftZ₁_pow_apply, neg_shiftZ₂_pow_apply]
  change ((-1 : ℤ) ^ (N - r)) •
      ((N.choose r : ℕ) • f (m - (r : ℤ)) (n - ((N - r : ℕ) : ℤ))) = _
  rw [← Nat.cast_smul_eq_nsmul ℤ, smul_smul]

end MulBySubPowSum

/-! ## Natural top-index binomial coefficients -/

/-- For a nonnegative top index, the generalized binomial coefficient agrees with
`Nat.choose`. -/
theorem gBinom_natCast_eq_choose {n k : ℕ} (hk : k ≤ n) :
    gBinom (n : ℤ) k = (n.choose k : ℂ) := by
  rw [gBinom]
  have hprod : (∏ i ∈ Finset.range k, (((n : ℤ) : ℂ) - (i : ℂ)))
      = (n.descFactorial k : ℂ) := by
    rw [Nat.descFactorial_eq_prod_range]
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hin : i ≤ n := le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) hk
    rw [Nat.cast_sub hin]
    rfl
  rw [hprod, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp [Nat.factorial_ne_zero]

/-- Binomial symmetry for the generalized binomial at a natural top index:
`gBinom (k:ℤ) (k-i) = gBinom (k:ℤ) i` for `i ≤ k`. -/
theorem gBinom_symm_nat {k i : ℕ} (hik : i ≤ k) :
    gBinom (k : ℤ) (k - i) = gBinom (k : ℤ) i := by
  rw [gBinom_natCast_eq_choose (Nat.sub_le k i), gBinom_natCast_eq_choose hik,
    Nat.choose_symm hik]

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The vacuum action of `L₋₁` (the clean creation computation) -/

/-- `L₋₁` is a "derivation on the vacuum descendants": `L₋₁(u₍ₛ₎𝟙) = (L₋₁u)₍ₛ₎𝟙` for all `s`.
Proved directly from the creation theorem `creation_pow` (`u₍₋ⱼ₋₁₎𝟙 = Tʲu/j!`) and
`T = L₋₁` (`T_eq_Lneg1`): both sides are `T^{j+1}u/j!` when `s = -j-1 ≤ -1`, and `0` when
`s ≥ 0`.  No reconstruction is used. -/
theorem L_neg_one_smul_vacuum (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (s : ℤ) :
    W.L (-1) (W.smul u s W.vacuum) = W.smul (W.L (-1) u) s W.vacuum := by
  have hT : (W.L (-1) : 𝒱 → 𝒱) = W.toPreVertexAlgebra.T := by rw [T_eq_Lneg1]
  rcases lt_or_ge s 0 with hs | hs
  · -- s ≤ -1: write s = -(j)-1
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, s = -(j : ℤ) - 1 := ⟨(-s - 1).toNat, by omega⟩
    rw [creation_pow, creation_pow, map_smul, hT]
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ', ← pow_succ]
  · -- s ≥ 0: both products vanish on the vacuum
    rw [W.toPreVertexAlgebra.smul_vacuum_nonneg u hs, W.toPreVertexAlgebra.smul_vacuum_nonneg _ hs,
      map_zero]

/-! ## Translation covariance -/

/-- The field `Res_{z₁}[Y(ω,z₁), Y(u,z₂)] = [ω₍₀₎, Y(u,z₂)] = [L₋₁, Y(u,z₂)]`, as
`cCoeff 0` of the `ω,u` commutator. -/
theorem cCoeff_zero_omega_apply (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (m : ℤ) :
    cCoeff 0 (bracketDist (W.Y W.conformalVector) (W.Y u)) m
      = W.L (-1) * (W.Y u) m - (W.Y u) m * W.L (-1) := by
  show mulBySubPow 0 (bracketDist (W.Y W.conformalVector) (W.Y u)) (-1) m = _
  rw [mulBySubPow_zero]
  show bracketDist (W.Y W.conformalVector) (W.Y u) (-1) m = _
  rw [bracketDist_apply]
  rfl

/-- **Translation covariance** (Gannon 5.1.8a, bracket form): in a VOA,
`[L₋₁, Y(u,z)] = Y(L₋₁u, z)`, i.e. `Res_{z₁}[Y(ω,z₁),Y(u,z)] = Y(L₋₁u, z)`.  Proved by
Goddard uniqueness: the left field is local with every `Y(b,z)` (Dong's lemma) and creates
`L₋₁u` from the vacuum (`L_neg_one_smul_vacuum`). -/
theorem translation_covariance (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) :
    cCoeff 0 (bracketDist (W.Y W.conformalVector) (W.Y u)) = W.Y (W.L (-1) u) := by
  refine W.toPreVertexAlgebra.goddard_uniqueness _ (W.L (-1) u) ?_ ?_
  · -- locality of the candidate with every `Y(b)` is Dong's lemma
    intro b
    exact dong_nonneg (W.locality W.conformalVector u) (W.locality W.conformalVector b)
      (W.locality u b) 0
  · -- vacuum condition: the field creates `L₋₁u`
    intro m
    rw [cCoeff_zero_omega_apply]
    show W.L (-1) ((W.Y u) m W.vacuum) - (W.Y u) m (W.L (-1) W.vacuum) = (W.Y (W.L (-1) u)) m W.vacuum
    have hvac : W.L (-1) W.vacuum = 0 := by
      have : W.L (-1) W.vacuum = W.toPreVertexAlgebra.T W.vacuum := by rw [T_eq_Lneg1]
      rw [this, PreVertexAlgebra.T_vacuum]
    have e1 : (W.Y u) m W.vacuum = W.smul u (-m - 1) W.vacuum := by
      rw [PreVertexAlgebra.smul_def, mode_apply]; norm_num
    have e2 : (W.Y (W.L (-1) u)) m W.vacuum = W.smul (W.L (-1) u) (-m - 1) W.vacuum := by
      rw [PreVertexAlgebra.smul_def, mode_apply]; norm_num
    rw [hvac, map_zero, sub_zero, e1, e2, L_neg_one_smul_vacuum]

/-- **Translation covariance, mode form** (Gannon 5.1.8): `[L₋₁, u₍ₙ₎] = (L₋₁u)₍ₙ₎`, i.e.
`L₋₁` is a derivation of every product `u₍ₙ₎w`.  Immediate from `translation_covariance` by
reading off the `z^{-n-1}`-coefficient. -/
theorem L_neg_one_deriv (W : VertexOperatorAlgebra 𝒱) (u w : 𝒱) (n : ℤ) :
    W.L (-1) (W.smul u n w) - W.smul u n (W.L (-1) w) = W.smul (W.L (-1) u) n w := by
  have ys : ∀ (a x : 𝒱), (W.Y a) (-n - 1) x = W.smul a n x := fun a x => by
    rw [PreVertexAlgebra.smul_def]; rfl
  have h := DFunLike.congr_fun (congrFun (translation_covariance W u) (-n - 1)) w
  rw [cCoeff_zero_omega_apply] at h
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, ys, ys] at h
  rw [← ys (W.L (-1) u) w]
  exact h

/-- Operator translation covariance, mode form: `[L₋₁, u₍ₙ₎] = -n·u₍ₙ₋₁₎`. -/
theorem L_comm_mode (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (n : ℤ) :
    ⁅W.L (-1), mode (W.Y u) n⁆ = (-n) • mode (W.Y u) (n - 1) := by
  apply LinearMap.ext; intro w
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, LinearMap.smul_apply]
  show W.L (-1) (W.smul u n w) - W.smul u n (W.L (-1) w) = (-n) • W.smul u (n - 1) w
  rw [L_neg_one_deriv, show W.L (-1) u = W.toPreVertexAlgebra.T u from by rw [T_eq_Lneg1],
    PreVertexAlgebra.smul_def, mode_Y_T, LinearMap.smul_apply, ← PreVertexAlgebra.smul_def]

/-- Operator translation covariance, coefficient form: `[L₋₁, (Yu)ₛ] = (s+1)·(Yu)_{s+1}`. -/
theorem L_comm_Ycoeff (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (s : ℤ) :
    ⁅W.L (-1), (W.Y u) s⁆ = (s + 1) • (W.Y u) (s + 1) := by
  have h := L_comm_mode W u (-s - 1)
  rw [show mode (W.Y u) (-s - 1) = (W.Y u) s from by
        rw [mode_apply, show (-(-s - 1) - 1 : ℤ) = s from by ring],
    show (-(-s - 1) : ℤ) = s + 1 from by ring,
    show mode (W.Y u) (-s - 1 - 1) = (W.Y u) (s + 1) from by
        rw [mode_apply, show (-(-s - 1 - 1) - 1 : ℤ) = s + 1 from by ring]] at h
  exact h

/-! ## The `e^{z₀T}`-conjugation iterate calculus (M1(a))

The operator conjugation `e^{z₀T} Y(u,z) e^{-z₀T} = Y(u, z+z₀)` (Gannon, after 5.1.8b)
cannot be phrased with a standalone operator `e^{z₀T}` (the `Foundations` expose no
finite-sum exponential), but its rigorous content is the family of coefficient identities
obtained by reading off the `z₀^j`-coefficient: `(1/j!)(ad L₋₁)^j Y(u,z) = (1/j!)∂_z^j Y(u,z)`,
i.e. `(ad L₋₁)^j Y(u,z) = ∂_z^j Y(u,z)`.  The `j = 1` case is `L_comm_Ycoeff`; the iterate is
proved below by induction.  This is the field/operator-side companion of the state-side
substrate `Y_Tpow` (`Y(Tʲu,z) = ∂_z^j Y(u,z)`) and is the `(a)` ingredient the skew-symmetry
proof consumes. -/

/-- The `j`-th `z`-derivative of a one-variable distribution, coefficient form:
`(∂^j f)_s = (s+1)(s+2)⋯(s+j)·f_{s+j}` (the rising-factorial weight). -/
theorem deriv_pow_apply {𝒲 : Type*} [AddCommGroup 𝒲] [Module ℂ 𝒲] (f : FormalDist 𝒲)
    (j : ℕ) (s : ℤ) :
    (deriv^[j] f) s = (∏ i ∈ Finset.range j, (s + 1 + (i : ℤ))) • f (s + (j : ℤ)) := by
  induction j generalizing s with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ', Function.comp_apply, deriv_apply, ih, smul_smul,
        Finset.prod_range_succ']
      have hidx : (s + 1) + (k : ℤ) = s + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hidx]
      congr 1
      rw [Nat.cast_zero, add_zero, mul_comm]
      congr 1
      exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)

/-- **The `e^{z₀T}`-conjugation iterate, coefficient form** (Gannon, after 5.1.8b):
`(ad L₋₁)^j (Y(u,z)_s) = (s+1)(s+2)⋯(s+j)·Y(u,z)_{s+j}`.  Built by induction on `j` from the
infinitesimal `L_comm_Ycoeff` (`j = 1`) with `lie_zsmul` linearity.  This is the
`z₀^j`-coefficient of the operator conjugation `e^{z₀T} Y(u,z) e^{-z₀T} = Y(u, z+z₀)`. -/
theorem adLneg1_pow_Ycoeff (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (j : ℕ) (s : ℤ) :
    ((fun X => ⁅W.L (-1), X⁆)^[j]) ((W.Y u) s)
      = (∏ i ∈ Finset.range j, (s + 1 + (i : ℤ))) • (W.Y u) (s + (j : ℤ)) := by
  induction j generalizing s with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih, lie_zsmul, L_comm_Ycoeff,
        smul_smul, Finset.prod_range_succ]
      have hidx : (s + (k : ℤ)) + 1 = s + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hidx]
      congr 1
      push_cast
      ring

/-- **The `e^{z₀T}`-conjugation iterate = `∂^j`** (Gannon, after 5.1.8b): the operator
conjugation `(ad L₋₁)^j Y(u,z) = ∂_z^j Y(u,z)`, read off coefficient-by-coefficient.
Combines `adLneg1_pow_Ycoeff` with `deriv_pow_apply`. -/
theorem adLneg1_pow_eq_deriv_pow (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (j : ℕ) (s : ℤ) :
    ((fun X => ⁅W.L (-1), X⁆)^[j]) ((W.Y u) s) = (deriv^[j] (W.Y u)) s := by
  rw [adLneg1_pow_Ycoeff, deriv_pow_apply]

/-- The bracket with `L₋₁` of a two-variable distribution, coefficient-wise. -/
def commL (W : VertexOperatorAlgebra 𝒱) (G : FormalDist₂ (End ℂ 𝒱)) : FormalDist₂ (End ℂ 𝒱) :=
  fun s t => ⁅W.L (-1), G s t⁆

@[simp] theorem commL_apply (W : VertexOperatorAlgebra 𝒱) (G : FormalDist₂ (End ℂ 𝒱)) (s t : ℤ) :
    commL W G s t = ⁅W.L (-1), G s t⁆ := rfl

/-- `commL` commutes with `(z₁-z₂)·` (it acts on the operator value, not the indices). -/
theorem commL_mulBySub (W : VertexOperatorAlgebra 𝒱) (G : FormalDist₂ (End ℂ 𝒱)) :
    commL W (mulBySub G) = mulBySub (commL W G) := by
  apply FormalDist₂.ext; intro s t
  simp only [commL_apply, mulBySub_apply, lie_sub]

/-- Iterated: `commL` commutes with `(z₁-z₂)ᵏ`. -/
theorem commL_mulBySubPow (W : VertexOperatorAlgebra 𝒱) (k : ℕ) (G : FormalDist₂ (End ℂ 𝒱)) :
    commL W (mulBySubPow k G) = mulBySubPow k (commL W G) := by
  induction k generalizing G with
  | zero => rfl
  | succ j ih => rw [mulBySubPow_succ, LinearMap.comp_apply, commL_mulBySub, ih,
      ← LinearMap.comp_apply, ← mulBySubPow_succ]

/-- **Translation covariance of the OPE bracket**: `[L₋₁, [Y(u,z₁),Y(v,z₂)]] = ∂[Y(u),Y(v)]`,
where `∂ = ∂₁+∂₂` (`deriv2`).  From the Leibniz rule + coefficient translation covariance. -/
theorem commL_bracketDist (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    commL W (bracketDist (W.Y u) (W.Y v)) = deriv2 (bracketDist (W.Y u) (W.Y v)) := by
  have leib : ∀ (a b c : End ℂ 𝒱), ⁅a, b * c⁆ = ⁅a, b⁆ * c + b * ⁅a, c⁆ := fun a b c => by
    simp only [LieRing.of_associative_ring_bracket]; noncomm_ring
  apply FormalDist₂.ext; intro s t
  simp only [commL_apply, deriv2_apply, bracketDist_apply, lie_sub, leib, L_comm_Ycoeff,
    smul_mul_assoc, mul_smul_comm, smul_sub]
  abel

/-- **The recursion** `[L₋₁, A_m] = (m+1)·A_{m+1}` for `A = cCoeff k (bracketDist (Yu)(Yv))`:
the field `k`-th product is translation covariant. -/
theorem L_comm_cCoeff (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    ⁅W.L (-1), cCoeff k (bracketDist (W.Y u) (W.Y v)) m⁆
      = (m + 1) • cCoeff k (bracketDist (W.Y u) (W.Y v)) (m + 1) := by
  show commL W (mulBySubPow k (bracketDist (W.Y u) (W.Y v))) (-1) m = _
  rw [commL_mulBySubPow, commL_bracketDist, resByParts]
  rfl

/-! ## The vacuum action of the field `k`-th product -/

/-- The vacuum-applied OPE bracket `[Y(u,z₁),Y(v,z₂)]𝟙` vanishes on `{s≤-1, t≤-1}`. -/
theorem applyVec_bracketDist_quadrant (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (s t : ℤ)
    (hs : s ≤ -1) (ht : t ≤ -1) :
    applyVec W.vacuum (bracketDist (W.Y u) (W.Y v)) s t = 0 := by
  rw [applyVec_apply, bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, PreVertexAlgebra.Y_apply_vacuum_eq_zero W.toPreVertexAlgebra v (by omega),
    PreVertexAlgebra.Y_apply_vacuum_eq_zero W.toPreVertexAlgebra u (by omega), map_zero, map_zero,
    sub_zero]

/-- Reduce the field `k`-th product on the vacuum to a `(z₁-z₂)ᵏ`-power of the vacuum bracket. -/
theorem cCoeff_apply_vacuum (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    cCoeff k (bracketDist (W.Y u) (W.Y v)) m W.vacuum
      = mulBySubPow k (applyVec W.vacuum (bracketDist (W.Y u) (W.Y v))) (-1) m := by
  show mulBySubPow k (bracketDist (W.Y u) (W.Y v)) (-1) m W.vacuum = _
  rw [← applyVec_apply, applyVec_mulBySubPow]

/-- `A_m 𝟙 = 0` for `m < 0`. -/
theorem cCoeff_vacuum_neg (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) {m : ℤ} (hm : m < 0) :
    cCoeff k (bracketDist (W.Y u) (W.Y v)) m W.vacuum = 0 := by
  rw [cCoeff_apply_vacuum]
  exact mulBySubPow_zero_of_quadrant (applyVec_bracketDist_quadrant W u v) k (-1) m (by omega)
    (by omega)

/-- `A_0 𝟙 = u₍ₖ₎v` (the base of the vacuum recursion). -/
theorem cCoeff_vacuum_base (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) :
    cCoeff k (bracketDist (W.Y u) (W.Y v)) 0 W.vacuum = W.smul u k v := by
  rw [cCoeff_apply_vacuum,
    mulBySubPow_diag_of_quadrant (applyVec_bracketDist_quadrant W u v) k (-1) (by omega),
    applyVec_apply, bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, PreVertexAlgebra.Y_apply_vacuum_zero,
    PreVertexAlgebra.Y_apply_vacuum_eq_zero W.toPreVertexAlgebra u (by omega), map_zero, sub_zero]
  rw [PreVertexAlgebra.smul_def, mode_apply, show (-1 - (k : ℤ)) = -(k : ℤ) - 1 from by ring]

/-- `L₋₁` annihilates the vacuum (helper). -/
theorem L_neg_one_vacuum (W : VertexOperatorAlgebra 𝒱) : W.L (-1) W.vacuum = 0 := by
  rw [show W.L (-1) W.vacuum = W.toPreVertexAlgebra.T W.vacuum from by rw [T_eq_Lneg1],
    PreVertexAlgebra.T_vacuum]

/-- **The vacuum condition** for the field `k`-th product: `A_m 𝟙 = Y(u₍ₖ₎v)_m 𝟙` for all `m`.
By induction on `m≥0` from the base `A_0𝟙 = u₍ₖ₎v` and the recursion `(m+1)A₍ₘ₊₁₎𝟙 = L₋₁(Aₘ𝟙)`
(both `A` and `Y(u₍ₖ₎v)` are translation covariant), with `m<0` handled by vanishing. -/
theorem cCoeff_vacuum_eq (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    cCoeff k (bracketDist (W.Y u) (W.Y v)) m W.vacuum = (W.Y (W.smul u k v)) m W.vacuum := by
  by_cases hm : m < 0
  · rw [cCoeff_vacuum_neg W u v k hm,
      PreVertexAlgebra.Y_apply_vacuum_eq_zero W.toPreVertexAlgebra (W.smul u k v) hm]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = (j : ℤ) := ⟨m.toNat, by omega⟩
    clear hm
    induction j with
    | zero =>
        rw [Nat.cast_zero, cCoeff_vacuum_base]
        exact (PreVertexAlgebra.Y_apply_vacuum_zero _ _).symm
    | succ i ih =>
        have expand : ∀ (X : End ℂ 𝒱), ⁅W.L (-1), X⁆ W.vacuum = W.L (-1) (X W.vacuum) := by
          intro X
          rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
            Module.End.mul_apply, L_neg_one_vacuum, map_zero, sub_zero]
        have hA := DFunLike.congr_fun (L_comm_cCoeff W u v k (i : ℤ)) W.vacuum
        have hB := DFunLike.congr_fun (L_comm_Ycoeff W (W.smul u k v) (i : ℤ)) W.vacuum
        rw [expand, LinearMap.smul_apply] at hA hB
        have key : ((i : ℤ) + 1) • cCoeff k (bracketDist (W.Y u) (W.Y v)) ((i : ℤ) + 1) W.vacuum
            = ((i : ℤ) + 1) • (W.Y (W.smul u k v)) ((i : ℤ) + 1) W.vacuum := by
          rw [← hA, ih, hB]
        have hc : (((i : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
        rw [← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1),
          ← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1)] at key
        rw [Nat.cast_succ]
        exact smul_right_injective 𝒱 hc key

/-- **The field `n`-th-product theorem** (`n = k ≥ 0`) (Gannon §5.1.2; Kac §4): in a VOA,
`Y(u₍ₖ₎v, z) = Res_{z₁}((z₁-z)ᵏ[Y(u,z₁),Y(v,z)]) = cCoeff k (bracketDist (Yu)(Yv))`.  Proved by
Goddard uniqueness: the field `k`-th product is local with every `Y(b,z)` (Dong's lemma) and
creates `u₍ₖ₎v` from the vacuum (`cCoeff_vacuum_eq`). -/
theorem nth_product (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) :
    cCoeff k (bracketDist (W.Y u) (W.Y v)) = W.Y (W.smul u k v) := by
  refine W.toPreVertexAlgebra.goddard_uniqueness _ (W.smul u k v) ?_ (cCoeff_vacuum_eq W u v k)
  intro b
  exact dong_nonneg (W.locality u v) (W.locality u b) (W.locality v b) k

/-- **Duality 5.1.9b** (Gannon): for `n = k ≥ 0`,
`Y(u₍ₖ₎v, z) = Res_{z₁}((z₁-z)ᵏ [Y(u,z₁), Y(v,z)])`.  This is the field `n`-th-product
theorem `nth_product` read as a duality statement. -/
theorem assoc_nonneg (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) :
    W.Y (W.smul u k v) = cCoeff k (bracketDist (W.Y u) (W.Y v)) :=
  (nth_product W u v k).symm

/-- **The commutator formula 5.1.7c** (Gannon): `[u₍ₐ₎, v₍ᵦ₎] = ∑_{j} C(a,j)·(u₍ⱼ₎v)₍ₐ₊ᵦ₋ⱼ₎`
(a finite sum; `N` is the locality bound).  From the structural commutator formula
(`mode_commutator_structural`) + the identification `cⱼ = (1/j!)·Y(u₍ⱼ₎v)` (the OPE-coefficient
recovery `cCoeff_deltaSum` and the `n`-th-product theorem `nth_product`). -/
theorem mode_commutator (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (a b : ℤ) :
    ∃ N : ℕ, ⁅mode (W.Y u) a, mode (W.Y v) b⁆
      = ∑ j : Fin N, gBinom a (j : ℕ) • mode (W.Y (W.smul u (j : ℕ) v)) (a + b - (j : ℕ)) := by
  obtain ⟨N, c, hdecomp⟩ := bracket_deltaSum W.toPreVertexAlgebra u v
  refine ⟨N, ?_⟩
  rw [mode_bracket_ope W.toPreVertexAlgebra u v hdecomp a b]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hne : ((j : ℕ).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hcj : c j = (((j : ℕ).factorial : ℂ)⁻¹) • W.Y (W.smul u (j : ℕ) v) := by
    have hrec := cCoeff_deltaSum c j
    rw [← hdecomp, nth_product] at hrec
    rw [hrec, ← Int.cast_smul_eq_zsmul ℂ ((j : ℕ).factorial : ℤ), Int.cast_natCast, smul_smul,
      inv_mul_cancel₀ hne, one_smul]
  rw [hcj, mode_smul,
    ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range (j : ℕ), (a - (i : ℤ))), smul_smul]
  congr 1
  rw [gBinom, div_eq_mul_inv]
  congr 1
  push_cast
  rfl

/-- **Iterate formula, nonnegative case** (Gannon 5.1.7d with `ℓ = k ≥ 0`, written with
ordinary binomial coefficients).  This is `nth_product` plus the finite binomial expansion
of `(z₁-z₂)^k`, read coefficient-wise:
`(u₍ₖ₎v)₍ₙ₎ = ∑_{r=0}^k (-1)^{k-r} choose(k,r)
  (u₍ᵣ₎ v₍ₙ+k-r₎ - v₍ₙ+k-r₎ u₍ᵣ₎)`.

The all-integer Borcherds iterate formula is proved in `Core.BorcherdsIdentity`
(`mode_iterate`, all `ℓ ∈ ℤ`); this theorem records the polynomial (`k ≥ 0`) part it builds on. -/
theorem mode_iterate_nonneg_choose (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱)
    (k : ℕ) (n : ℤ) :
    mode (W.Y (W.smul u (k : ℤ) v)) n =
      ∑ r ∈ Finset.range (k + 1), (((-1 : ℤ) ^ (k - r)) * (k.choose r : ℤ)) •
        (mode (W.Y u) (r : ℤ) * mode (W.Y v) (n + ((k - r : ℕ) : ℤ))
          - mode (W.Y v) (n + ((k - r : ℕ) : ℤ)) * mode (W.Y u) (r : ℤ)) := by
  rw [← nth_product W u v k]
  rw [mode_apply, cCoeff_apply, mulBySubPow_apply_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [bracketDist_apply]
  simp only [mode_apply]
  congr 1
  all_goals ring_nf

/-- **Iterate formula, nonnegative case**, in the project's generalized-binomial convention.
This is the same statement as `mode_iterate_nonneg_choose`, with
`choose(k,r) = gBinom k r` for `r ≤ k` and the integer scalar action converted to complex
scalar multiplication. -/
theorem mode_iterate_nonneg (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) (n : ℤ) :
    mode (W.Y (W.smul u (k : ℤ) v)) n =
      ∑ r ∈ Finset.range (k + 1), (((-1 : ℂ) ^ (k - r)) * gBinom (k : ℤ) r) •
        (mode (W.Y u) (r : ℤ) * mode (W.Y v) (n + ((k - r : ℕ) : ℤ))
          - mode (W.Y v) (n + ((k - r : ℕ) : ℤ)) * mode (W.Y u) (r : ℤ)) := by
  rw [mode_iterate_nonneg_choose]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  have hrle : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  rw [gBinom_natCast_eq_choose hrle]
  rw [← Int.cast_smul_eq_zsmul ℂ (((-1 : ℤ) ^ (k - r)) * (k.choose r : ℤ))]
  congr 1
  push_cast
  rfl

/-- **Borcherds iterate formula 5.1.7d, the `ℓ = k ≥ 0` case in exact Borcherds form**
(Gannon, eq. 5.1.7d): `(u₍ₖ₎v)₍ₙ₎ = ∑_{i=0}^{k} (-1)ⁱ C(k,i) (u₍ₖ₋ᵢ₎ v₍ₙ₊ᵢ₎ - (-1)ᵏ v₍ₖ₊ₙ₋ᵢ₎ u₍ᵢ₎)`.
Obtained from the proven commutator-form iterate `mode_iterate_nonneg` by the reflection
reindex `r ↦ k - r` on the first (`u·v`) part — using the binomial symmetry `gBinom_symm_nat`
— and the sign identity `(-1)^{k-i} = (-1)^{i+k}` on the second (`v·u`) part.  This is the
`ℓ ≥ 0` slice of the full Borcherds identity (`borcherds`, 5.1.7b); the `ℓ < 0` slice runs
through the normal-ordered duality `assoc_neg`. -/
theorem mode_iterate_borcherds_nonneg (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) (n : ℤ) :
    mode (W.Y (W.smul u (k : ℤ) v)) n =
      ∑ i ∈ Finset.range (k + 1), ((-1 : ℂ) ^ i * gBinom (k : ℤ) i) •
        (mode (W.Y u) ((k : ℤ) - i) * mode (W.Y v) (n + i)
          - ((-1 : ℂ) ^ k) • (mode (W.Y v) ((k : ℤ) + n - i) * mode (W.Y u) (i))) := by
  rw [mode_iterate_nonneg]
  simp only [smul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  · -- A-part (`u·v`): reflect `r ↦ k - r`
    rw [← Finset.sum_range_reflect
      (fun r => (((-1 : ℂ) ^ (k - r)) * gBinom (k : ℤ) r) •
        (mode (W.Y u) (r : ℤ) * mode (W.Y v) (n + ((k - r : ℕ) : ℤ)))) (k + 1)]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [show k + 1 - 1 - i = k - i from by omega, Nat.sub_sub_self hik, gBinom_symm_nat hik,
      Nat.cast_sub hik]
  · -- B-part (`v·u`): index `r = i`, sign/symmetry identity
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Nat.cast_sub hik, smul_smul, show n + ((k : ℤ) - i) = (k : ℤ) + n - i from by ring]
    congr 1
    rw [mul_right_comm ((-1 : ℂ) ^ i) (gBinom (k : ℤ) i) ((-1 : ℂ) ^ k)]
    congr 1
    rw [← pow_add, show i + k = (k - i) + 2 * i from by omega, pow_add, pow_mul]
    simp

end VertexOperatorAlgebra

namespace PreVertexAlgebra

/-- **The vertex operators are fields** (Gannon §5.1.2; VA5 regularity): `Y(u,z)` is
lower-truncated on every vector, `(Y u)ₙ x = 0` for `n ≪ 0`.  This is the hypothesis that
makes the same-variable normal-ordered product `:Y(u,z)Y(v,z):` (`Core.Dong.nprod`) — and
hence the `n < 0` field products `negProd` — algebraically defined for vertex operators. -/
theorem isField_Y {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : PreVertexAlgebra 𝒱) (u : 𝒱) :
    IsField (V.Y u) := by
  intro x
  obtain ⟨N, hN⟩ := V.regularity u x
  refine ⟨-N, fun n hn => ?_⟩
  have h := hN (-n - 1) (by omega)
  rwa [mode_apply, show (-(-n - 1) - 1 : ℤ) = n by ring] at h

end PreVertexAlgebra

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Translation covariance of the normal-ordered product (toward `assoc_neg`, 5.1.9a)

The same-variable normal-ordered product `:Y(a,z)Y(b,z):` (`nprod`) is translation covariant,
`[L₋₁, :ab:_s] = (s+1)·:ab:_{s+1}` — the field-derivative `∂_z :ab: = :(∂a)b: + :a(∂b):` read
off coefficient-wise.  This is the engine of the vacuum recursion that `goddard_uniqueness`
consumes to identify `:(∂^{m-1}Y(u))Y(v): / (m-1)!` with `Y(u₍₋ₘ₎v)` (the `n<0` duality). -/

/-- The atom of translation covariance: `[L₋₁, :a b:_{m,n}] = (m+1)·:a b:_{m+1,n} +
(n+1)·:a b:_{m,n+1}` for the two-variable normal-ordered coefficient (Leibniz +
`L_comm_Ycoeff`; the `m`-gate boundary at `m=-1` is absorbed by the vanishing `(m+1)` factor). -/
theorem normalOrdered_L_comm (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (m n : ℤ) :
    ⁅W.L (-1), normalOrdered (W.Y a) (W.Y b) m n⁆
      = (m + 1) • normalOrdered (W.Y a) (W.Y b) (m + 1) n
        + (n + 1) • normalOrdered (W.Y a) (W.Y b) m (n + 1) := by
  have leib : ∀ X Y : End ℂ 𝒱, ⁅W.L (-1), X * Y⁆ = ⁅W.L (-1), X⁆ * Y + X * ⁅W.L (-1), Y⁆ :=
    fun X Y => by simp only [LieRing.of_associative_ring_bracket]; noncomm_ring
  simp only [normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, if_pos (show (0:ℤ) ≤ m + 1 by omega), if_pos hm, leib, L_comm_Ycoeff,
      L_comm_Ycoeff, smul_mul_assoc, mul_smul_comm]
  · rw [if_neg hm, if_neg hm, leib, L_comm_Ycoeff, L_comm_Ycoeff, smul_mul_assoc, mul_smul_comm]
    by_cases hm1 : 0 ≤ m + 1
    · rw [if_pos hm1, show m + 1 = (0:ℤ) by omega, zero_smul, zero_smul, add_zero, zero_add]
    · rw [if_neg hm1, add_comm]

/-- The `z₁`-shifted antidiagonal of `:ab:` applied to `x` has finite support. -/
theorem nodiag_shift_finite {a b : FormalDist (End ℂ 𝒱)} (ha : IsField a) (hb : IsField b)
    (s : ℤ) (x : 𝒱) :
    (Function.support (fun m : ℤ => normalOrdered a b (m + 1) (s - m) x)).Finite := by
  apply Set.Finite.subset ((normalOrdered_diag_support_finite ha hb (s + 1) x).image (· - 1))
  intro m hm
  rw [Function.mem_support] at hm
  rw [Set.mem_image]
  refine ⟨m + 1, ?_, by ring⟩
  rw [Function.mem_support, show s + 1 - (m + 1) = s - m from by ring]
  exact hm

/-- **Translation covariance of `:Y(a,z)Y(b,z):`** (toward Gannon 5.1.9a):
`[L₋₁, :ab:_s] = (s+1)·:ab:_{s+1}`.  Proved coefficient-wise by distributing `L₋₁` through the
algebraically-summable sum, applying `normalOrdered_L_comm`, and reindexing the antidiagonal. -/
theorem nprod_L_comm (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (s : ℤ) :
    ⁅W.L (-1), nprod (W.isField_Y a) (W.isField_Y b) s⁆
      = (s + 1) • nprod (W.isField_Y a) (W.isField_Y b) (s + 1) := by
  apply LinearMap.ext; intro x
  rw [LinearMap.smul_apply]
  set a' := W.Y a; set b' := W.Y b
  have ha : IsField a' := W.isField_Y a
  have hb : IsField b' := W.isField_Y b
  have hxf := normalOrdered_diag_support_finite ha hb s x
  have hLf := normalOrdered_diag_support_finite ha hb s (W.L (-1) x)
  have step1 : ⁅W.L (-1), nprod ha hb s⁆ x
      = ∑ᶠ m : ℤ, ⁅W.L (-1), normalOrdered a' b' m (s - m)⁆ x := by
    rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply]
    show W.L (-1) (nprod ha hb s x) - nprod ha hb s (W.L (-1) x) = _
    rw [nprod_apply, nprod_apply, map_finsum (W.L (-1)) hxf,
      ← finsum_sub_distrib (hxf.subset (fun m hm => by
        rw [Function.mem_support] at hm ⊢; exact fun h => hm (by rw [h, map_zero]))) hLf]
    refine finsum_congr fun m => ?_
    rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply]
  rw [step1]
  have hf1 : (Function.support
      (fun m : ℤ => ((m + 1 : ℤ)) • normalOrdered a' b' (m+1) (s-m) x)).Finite :=
    (nodiag_shift_finite ha hb s x).subset (fun m hm => by
      rw [Function.mem_support] at hm ⊢; exact fun h => hm (by rw [h, smul_zero]))
  have hdiag1 : (Function.support (fun m : ℤ => normalOrdered a' b' m (s+1-m) x)).Finite :=
    normalOrdered_diag_support_finite ha hb (s+1) x
  have hf2 : (Function.support
      (fun m : ℤ => ((s - m + 1 : ℤ)) • normalOrdered a' b' m (s-m+1) x)).Finite :=
    hdiag1.subset (fun m hm => by
      rw [Function.mem_support] at hm ⊢
      simp only [show s - m + 1 = s + 1 - m from by ring] at hm ⊢
      exact fun h => hm (by rw [h, smul_zero]))
  have hg1 : (Function.support
      (fun m : ℤ => (m : ℤ) • normalOrdered a' b' m (s+1-m) x)).Finite :=
    hdiag1.subset (fun m hm => by
      rw [Function.mem_support] at hm ⊢; exact fun h => hm (by rw [h, smul_zero]))
  have hg2 : (Function.support
      (fun m : ℤ => ((s + 1 - m : ℤ)) • normalOrdered a' b' m (s+1-m) x)).Finite :=
    hdiag1.subset (fun m hm => by
      rw [Function.mem_support] at hm ⊢; exact fun h => hm (by rw [h, smul_zero]))
  rw [show (∑ᶠ m : ℤ, ⁅W.L (-1), normalOrdered a' b' m (s - m)⁆ x)
        = ∑ᶠ m : ℤ, (((m + 1 : ℤ)) • normalOrdered a' b' (m+1) (s-m) x
            + ((s - m + 1 : ℤ)) • normalOrdered a' b' m (s-m+1) x) from
      finsum_congr fun m => by
        rw [normalOrdered_L_comm, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]]
  rw [finsum_add_distrib hf1 hf2]
  rw [show (∑ᶠ m : ℤ, ((m + 1 : ℤ)) • normalOrdered a' b' (m+1) (s-m) x)
        = ∑ᶠ m : ℤ, ((m : ℤ)) • normalOrdered a' b' m (s+1-m) x from by
      rw [← finsum_int_succ_shift (fun m : ℤ => ((m : ℤ)) • normalOrdered a' b' m (s+1-m) x)]
      exact finsum_congr fun m => by rw [show s + 1 - (m + 1) = s - m from by ring]]
  rw [show (∑ᶠ m : ℤ, ((s - m + 1 : ℤ)) • normalOrdered a' b' m (s-m+1) x)
        = ∑ᶠ m : ℤ, ((s + 1 - m : ℤ)) • normalOrdered a' b' m (s+1-m) x from
      finsum_congr fun m => by rw [show s - m + 1 = s + 1 - m from by ring]]
  rw [← finsum_add_distrib hg1 hg2, nprod_apply, smul_finsum' (s + 1) hdiag1]
  refine finsum_congr fun m => ?_
  rw [← add_smul]
  congr 1
  ring

/-! ### The vacuum recursion and the negative duality `assoc_neg` (Gannon 5.1.9a) -/

/-- A scalar multiple of a field is local with whatever the field is local with. -/
theorem Local.smul' (c : ℂ) {F G : FormalDist (End ℂ 𝒱)} (h : Local F G) : Local (c • F) G := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  have he : bracketDist (c • F) G = c • bracketDist F G := by
    apply FormalDist₂.ext; intro m n
    show (c • F m) * G n - G n * (c • F m) = c • (F m * G n - G n * F m)
    rw [smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [he, map_smul, hN, smul_zero]

/-- `nprod` depends only on the underlying distributions, not the `IsField` witnesses. -/
theorem nprod_congr {a a' b : FormalDist (End ℂ 𝒱)} (ha : IsField a) (ha' : IsField a')
    (hb : IsField b) (h : a = a') : nprod ha hb = nprod ha' hb := by
  subst h; rfl

/-- **Creation determines a field on the vacuum.**  If `B` vanishes below `0` on `𝟙`, creates
`w` at `0`, and is translation covariant on `𝟙` (`L₋₁(Bₛ𝟙) = (s+1)·B_{s+1}𝟙`), then
`Bₛ𝟙 = Y(w,z)ₛ𝟙`: both satisfy the same recursion off the same base. -/
theorem vacuum_recursion_eq (W : VertexOperatorAlgebra 𝒱) (B : FormalDist (End ℂ 𝒱)) (w : 𝒱)
    (hneg : ∀ s : ℤ, s < 0 → B s W.vacuum = 0)
    (hbase : B 0 W.vacuum = w)
    (hrec : ∀ s : ℤ, W.L (-1) (B s W.vacuum) = (s + 1) • B (s + 1) W.vacuum)
    (s : ℤ) : B s W.vacuum = (W.Y w) s W.vacuum := by
  by_cases hs : s < 0
  · rw [hneg s hs, PreVertexAlgebra.Y_apply_vacuum_eq_zero W.toPreVertexAlgebra w hs]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, s = (j : ℤ) := ⟨s.toNat, by omega⟩
    clear hs
    induction j with
    | zero => rw [Nat.cast_zero, hbase]; exact (PreVertexAlgebra.Y_apply_vacuum_zero _ _).symm
    | succ i ih =>
        have hYrec : W.L (-1) ((W.Y w) (i:ℤ) W.vacuum)
            = ((i:ℤ) + 1) • (W.Y w) ((i:ℤ)+1) W.vacuum := by
          have h := DFunLike.congr_fun (L_comm_Ycoeff W w (i:ℤ)) W.vacuum
          rw [LinearMap.smul_apply, LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
            Module.End.mul_apply, Module.End.mul_apply, L_neg_one_vacuum, map_zero, sub_zero] at h
          exact h
        have key : ((i:ℤ)+1) • B ((i:ℤ)+1) W.vacuum = ((i:ℤ)+1) • (W.Y w) ((i:ℤ)+1) W.vacuum := by
          rw [← hrec, ih, hYrec]
        have hc : (((i:ℤ)+1 : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
        rw [← Int.cast_smul_eq_zsmul ℂ ((i:ℤ)+1), ← Int.cast_smul_eq_zsmul ℂ ((i:ℤ)+1)] at key
        rw [Nat.cast_succ]
        exact smul_right_injective 𝒱 hc key

/-- The mode form of the translation property on a product: `(Tw)₍ₙ₎v = -n·w₍ₙ₋₁₎v`. -/
theorem smul_T_apply (W : VertexOperatorAlgebra 𝒱) (w v : 𝒱) (n : ℤ) :
    W.smul (W.toPreVertexAlgebra.T w) n v = (-n) • W.smul w (n - 1) v := by
  rw [PreVertexAlgebra.smul_def, mode_Y_T, LinearMap.smul_apply, ← PreVertexAlgebra.smul_def]

/-- Iterated: `(Tᵏw)₍ₙ₎v = (∏_{i<k} -(n-i))·w₍ₙ₋ₖ₎v`. -/
theorem smul_Tpow (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) (n : ℤ) :
    W.smul ((W.toPreVertexAlgebra.T ^ k) u) n v
      = (∏ i ∈ Finset.range k, (-(n - (i:ℤ)))) • W.smul u (n - (k:ℤ)) v := by
  induction k generalizing n with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, smul_T_apply, ih, smul_smul,
        Finset.prod_range_succ' (fun i => -(n - (i:ℤ))) j]
      have hidx : n - 1 - (j:ℤ) = n - ((j+1:ℕ):ℤ) := by push_cast; ring
      rw [hidx]
      congr 1
      rw [show (-(n - ((0:ℕ):ℤ))) = -n by push_cast; ring, mul_comm]
      congr 1
      exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)

/-- `∏_{i<k}(1+i) = k!`. -/
theorem prod_one_add_factorial (k : ℕ) :
    (∏ i ∈ Finset.range k, ((1:ℤ) + (i:ℤ))) = (k.factorial : ℤ) := by
  induction k with
  | zero => simp
  | succ j ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ]; push_cast; ring

/-- The creation identity for translates: `(Tᵏu)₍₋₁₎v = k!·u₍₋ₖ₋₁₎v` (the `k!` that the
normal-ordered `negProd` divides out). -/
theorem smul_Tpow_neg_one (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) :
    W.smul ((W.toPreVertexAlgebra.T ^ k) u) (-1) v
      = (k.factorial : ℤ) • W.smul u (-(k:ℤ) - 1) v := by
  rw [smul_Tpow]
  congr 1
  · rw [← prod_one_add_factorial]; exact Finset.prod_congr rfl (fun i _ => by ring)
  · congr 1; ring

/-- `:a(z)b(z):` annihilates the vacuum below degree `0` (all antidiagonal terms vanish). -/
theorem nprod_vacuum_neg (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) {s : ℤ} (hs : s < 0) :
    nprod (W.isField_Y a) (W.isField_Y b) s W.vacuum = 0 := by
  rw [nprod_apply]
  have hz : ∀ m : ℤ, normalOrdered (W.Y a) (W.Y b) m (s - m) W.vacuum = 0 := by
    intro m
    rw [normalOrdered_apply]
    by_cases hm : 0 ≤ m
    · rw [if_pos hm, Module.End.mul_apply,
        PreVertexAlgebra.Y_apply_vacuum_eq_zero W.toPreVertexAlgebra b (show s - m < 0 by omega), map_zero]
    · rw [if_neg hm, Module.End.mul_apply,
        PreVertexAlgebra.Y_apply_vacuum_eq_zero W.toPreVertexAlgebra a (show m < 0 by omega), map_zero]
  rw [finsum_congr hz, finsum_zero]

/-- The vacuum value `:a(z)b(z):₀ 𝟙 = a₍₋₁₎b` (only the `m=0` antidiagonal term survives). -/
theorem nprod_vacuum_base (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) :
    nprod (W.isField_Y a) (W.isField_Y b) 0 W.vacuum = W.smul a (-1) b := by
  rw [nprod_apply]
  have hsingle : ∀ m : ℤ, m ≠ 0 → normalOrdered (W.Y a) (W.Y b) m (0 - m) W.vacuum = 0 := by
    intro m hm
    rw [normalOrdered_apply]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0, Module.End.mul_apply,
        PreVertexAlgebra.Y_apply_vacuum_eq_zero W.toPreVertexAlgebra b (show 0 - m < 0 by omega), map_zero]
    · rw [if_neg h0, Module.End.mul_apply,
        PreVertexAlgebra.Y_apply_vacuum_eq_zero W.toPreVertexAlgebra a (show m < 0 by omega), map_zero]
  rw [finsum_eq_single _ 0 hsingle, normalOrdered_apply, if_pos le_rfl, Module.End.mul_apply,
    show (W.Y b) (0 - 0) W.vacuum = b from by
      rw [show (0:ℤ) - 0 = 0 by ring]; exact W.toPreVertexAlgebra.Y_apply_vacuum_zero b]
  rfl

/-- **The negative duality 5.1.9a** (Gannon): `Y(u₍₋ₖ₋₁₎v, z) = (1/k!):(∂_z^k Y(u,z))Y(v,z):`
(`= negProd`).  Proved by `goddard_uniqueness`: the candidate field
`(1/k!):(∂^k Y u)(Y v):` is local with every `Y(b,z)` (full Dong `dong_neg`, with the
derivative locality `∂^k Y(u) = Y(Tᵏu)` reduced to VA4 via `Y_Tpow`) and creates `u₍₋ₖ₋₁₎v`
from the vacuum (the recursion `vacuum_recursion_eq` off the base `(Tᵏu)₍₋₁₎v = k!·u₍₋ₖ₋₁₎v`
and the translation covariance `nprod_L_comm`). -/
theorem assoc_neg (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) :
    W.Y (W.smul u (-(k:ℤ) - 1) v) = negProd (W.isField_Y u) (W.isField_Y v) k := by
  set Tu := (W.toPreVertexAlgebra.T ^ k) u with hTu
  have hAeq : ((k.factorial : ℂ)⁻¹ • nprod (W.isField_Y Tu) (W.isField_Y v))
      = negProd (W.isField_Y u) (W.isField_Y v) k := by
    rw [negProd]
    congr 1
    exact nprod_congr (W.isField_Y Tu) ((W.isField_Y u).deriv_iterate k) (W.isField_Y v)
      (by rw [hTu]; exact Y_Tpow W u k)
  rw [← hAeq]
  symm
  refine W.toPreVertexAlgebra.goddard_uniqueness _ (W.smul u (-(k:ℤ)-1) v) (fun b => ?_) (fun m => ?_)
  · exact Local.smul' _ (dong_neg (W.isField_Y Tu) (W.isField_Y v)
      (W.locality Tu v) (W.locality Tu b) (W.locality v b))
  · refine vacuum_recursion_eq W ((k.factorial : ℂ)⁻¹ • nprod (W.isField_Y Tu) (W.isField_Y v))
      (W.smul u (-(k:ℤ)-1) v) (fun s hs => ?_) ?_ (fun s => ?_) m
    · show ((k.factorial : ℂ)⁻¹ • nprod (W.isField_Y Tu) (W.isField_Y v) s) W.vacuum = 0
      rw [LinearMap.smul_apply, nprod_vacuum_neg W Tu v hs, smul_zero]
    · show ((k.factorial : ℂ)⁻¹ • nprod (W.isField_Y Tu) (W.isField_Y v) 0) W.vacuum = _
      rw [LinearMap.smul_apply, nprod_vacuum_base W Tu v, hTu, smul_Tpow_neg_one,
        ← Int.cast_smul_eq_zsmul ℂ (k.factorial : ℤ), Int.cast_natCast, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul]
    · show W.L (-1) (((k.factorial : ℂ)⁻¹ • nprod (W.isField_Y Tu) (W.isField_Y v) s) W.vacuum)
        = (s + 1) • ((k.factorial : ℂ)⁻¹ • nprod (W.isField_Y Tu) (W.isField_Y v) (s+1)) W.vacuum
      rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
      have hrec := DFunLike.congr_fun (nprod_L_comm W Tu v s) W.vacuum
      rw [LinearMap.smul_apply, LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
        Module.End.mul_apply, Module.End.mul_apply, L_neg_one_vacuum, map_zero, sub_zero] at hrec
      rw [hrec, smul_comm]

end VertexOperatorAlgebra

end VOA
