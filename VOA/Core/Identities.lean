/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.OPE
import VOA.Core.VertexOperatorAlgebra

/-!
# The translation operator, skew-symmetry, and duality  (Gannon pp. 320–321)

The standard derived identities of a vertex algebra, obtained from the
Jacobi/Borcherds identity (`Core.BorcherdsIdentity`).

* **Translation operator** `T : 𝒱 → 𝒱`, `T u := u₍₋₂₎ 1` (5.1.8a). In a VOA, `T = L₋₁`
  (5.1.8b), i.e. `L₋₁ u = u₍₋₂₎ 1`.
* **Derivative property.** `Y(Tu, z) = ∂_z Y(u, z)`, and `[L₋₁, Y(u,z)] = ∂_z Y(u,z)`.
* **Skew-symmetry.** `Y(u, z) v = e^{zT} Y(v, -z) u` (Gannon, after 5.1.8b) — **proved** in
  `Core.SkewSymmetry` (`skew`/`skew_mode`), via the discharged weak-associativity engine
  `Core.WeakAssoc` (downstream of this file).
* **Duality / associativity** (5.1.9) — **proved** in `Core.Reconstruction`:
  `Y(u₍₋ₘ₎ v, z) = (1/(m-1)!) :(∂_z^{m-1} Y(u,z)) Y(v,z):` for `m ≥ 1` (`assoc_neg`, 5.1.9a), and
  `Y(u₍ₙ₎ v, z) = Res_{z₁} (z₁-z)ⁿ [Y(u,z₁), Y(v,z)]` for `n ≥ 0` (`assoc_nonneg`, 5.1.9b). These
  let one build the whole VOA from a few generators.
* **Grading of products.** for `u ∈ 𝒱ₖ`, `v ∈ 𝒱ₗ`: `L₀(u₍ₙ₎v) = (k+ℓ-n-1)(u₍ₙ₎v)`,
  re-deriving VA1.
* `L₋₁, L₀, L₁` span a copy of `𝔰𝔩₂(ℂ)` (Question 5.1.5b).

## Provided here vs. downstream (the advertised API, reconciled)

This file (upstream of the reconstruction cascade) provides the **translation operator** `T` and
its calculus, the identification **`T = L₋₁`** (`T_eq_Lneg1`, 5.1.8b), the derivative property
**`Y(Tu,z)=∂_z Y(u,z)`** (`Y_T`, 5.1.8a) and its iterate `Y_Tpow`, and the **creation theorem**
`creation_pow` (`a₍₋k₋₁₎𝟙 = Tᵏa/k!`).  All are proved `sorry`-free / axiom-free below.

The remaining derived identities named in the title — **skew-symmetry** (5.1.8) and the
**duality 5.1.9** — are **proved downstream** of this file (they consume the full reconstruction
cascade), so they are *not* restated here:

* `assoc_neg` (5.1.9a) and `assoc_nonneg` (5.1.9b) — `Core.Reconstruction` (via full Dong
  `dong_neg` / normal-ordered `negProd` + `goddard_uniqueness`);
* `skew` / `skew_mode` (5.1.8) — `Core.SkewSymmetry` (via `Core.WeakAssoc`).

`Core.Reconstruction` and `Core.WeakAssoc` *import this file*, so a re-export here would be
circular — consume these names from their home modules.  All are axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## What is proved here (`sorry`-free / axiom-free)

* `PreVertexAlgebra.T` — the translation operator `T u = u₍₋₂₎ 1` (5.1.8a) as a
  `ℂ`-linear endomorphism of `𝒱`, with `T_apply`, `T_vacuum` (`T 1 = 0`), and the
  grading shift `T_mem_grading` (`T : 𝒱ₖ → 𝒱_{k+1}`, from VA1).
* `mode_deriv` — the mode form `(∂_z f)₍ₘ₎ = -m·f₍ₘ₋₁₎` of the formal derivative.
* **`T_eq_Lneg1` (5.1.8b)** — `T = L₋₁` in a VOA, **proved** directly from VOA3 + VA3.
* **`Y_T` (5.1.8a)** / `mode_Y_T` — the derivative property `Y(Tu,z)=∂_z Y(u,z)`, i.e.
  `(Tu)₍ₙ₎ = -n·u₍ₙ₋₁₎`, **proved** at the VOA level (immediate from `T_eq_Lneg1` + VOA3).
* **`Y_Tpow` (5.1.8a, iterated)** — `Y(Tʲu,z)=∂_z^j Y(u,z)`, **proved** by induction off `Y_T`;
  the power-series companion of `creation_pow` and the infinitesimal content of the `e^{zT}`
  conjugation that skew-symmetry consumes.
* **`creation_pow`** — the creation theorem `a₍₋k₋₁₎𝟙 = Tᵏa/k!` (the power-series form of
  `Y(a,z)𝟙 = e^{zT}a`), **proved** by induction using only `mode_Y_T` + VA3.
* The `𝔰𝔩₂(ℂ)`-triple of `L₋₁, L₀, L₁` is recorded in `Core.VertexOperatorAlgebra`.

## Design decision (why these live at the VOA level)

We develop the reconstruction at the **VOA level**: Gannon's bare VA has
no translation-covariance axiom, so at the bare-VA level `Y(Tu,z)=∂_z Y(u,z)` is circular,
but axiom VOA3 supplies it directly, giving `T_eq_Lneg1`, `Y_T` and `creation_pow` above
*without* reconstruction.

`creation_pow` is exactly the vacuum-expansion hypothesis that **Goddard uniqueness**
(`Core.Goddard.goddard_uniqueness`) consumes.  With Goddard plus **Dong's lemma for all `n`**
(`Core.Dong.dong_nonneg` + `dong_neg`), every downstream identity follows:
skew-symmetry `skew` (`Core.SkewSymmetry`), the duality `assoc_neg`/`assoc_nonneg` 5.1.9
(`Core.Reconstruction`), and the fully-identified commutator/iterate/Borcherds cluster
(`Core.BorcherdsIdentity`, `Core.Borcherds`) — all `sorry`-free / axiom-clean.

## Dependencies
* `VOA.Core.BorcherdsIdentity` (hence `PreVertexAlgebra`); the VOA statements also
  use `VOA.Core.VertexOperatorAlgebra`.

## Status
Everything this file defines is proved `sorry`-free / axiom-free
(`#print axioms = [propext, Classical.choice, Quot.sound]`): the translation operator `T` and
its calculus (`T_apply`/`T_vacuum`/`T_mem_grading`), `mode_deriv`, **`T_eq_Lneg1` (5.1.8b)**,
**`Y_T` (5.1.8a)** + `mode_Y_T`, the iterate `Y_Tpow`, and the **creation theorem
`creation_pow`**; the `𝔰𝔩₂`-span is in `Core.VertexOperatorAlgebra`.  The further identities
this file's title advertises — skew-symmetry (5.1.8) and the duality 5.1.9 — are proved
downstream (`Core.SkewSymmetry`, `Core.Reconstruction`); see "Provided here vs. downstream".

Both former gates that once blocked them are discharged: the `ι_z` substitution
multiplicativity (`Foundations.Substitution.subst_mulBySub`) and **Dong's lemma for all `n`**
(`Core.Dong.dong_nonneg` + `dong_neg`).  The `n ≥ 0` cascade (`nth_product`, `assoc_nonneg`,
`mode_commutator`) and the `n < 0` normal-ordered branch (`assoc_neg` via `negProd` +
`goddard_uniqueness`) are both closed, as is `skew` — the two-sided `ι_{z,w}`/`ι_{w,z}`
completion that Gannon calls the "more subtle argument", handled in `Core.WeakAssoc`.

## References
* Gannon §5.1.3, eqs. (5.1.8)–(5.1.9); Lepowsky–Li Ch. 3 (prop. 3.1.19 etc.).
-/

namespace VOA

open Module (End)

universe u

/-- The mode form of the formal derivative `∂_z` (Gannon 5.1.3): `(∂_z f)₍ₘ₎ = -m·f₍ₘ₋₁₎`.
This is the coefficient identity behind the translation property `Y(Tu,z)=∂_z Y(u,z)`. -/
theorem mode_deriv {𝒲 : Type*} [AddCommGroup 𝒲] [Module ℂ 𝒲] (f : FormalDist 𝒲) (m : ℤ) :
    mode (deriv f) m = (-m) • mode f (m - 1) := by
  rw [mode_apply, deriv_apply, mode_apply,
    show ((-m - 1) + 1 : ℤ) = -m by ring, show (-(m - 1) - 1 : ℤ) = -m by ring]

namespace PreVertexAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The translation operator `T u = u₍₋₂₎ 1` (Gannon 5.1.8a) -/

/-- The **translation operator** `T u := u₍₋₂₎ 1` (Gannon 5.1.8a), a `ℂ`-linear
endomorphism of `𝒱`.  In a VOA it coincides with `L₋₁` (5.1.8b, `T_eq_Lneg1`, proved below). -/
def T (V : PreVertexAlgebra 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun u := V.smul u (-2) V.vacuum
  map_add' u₁ u₂ := by exact smul_add_left V u₁ u₂ (-2) V.vacuum
  map_smul' c u := by exact smul_smul_left V c u (-2) V.vacuum

/-- Unfolding of the translation operator: `T u = u₍₋₂₎ 1` (Gannon 5.1.8a). -/
@[simp] theorem T_apply (V : PreVertexAlgebra 𝒱) (u : 𝒱) : V.T u = V.smul u (-2) V.vacuum := rfl

/-- `T 1 = 0`: the translation operator annihilates the vacuum (from VA2,
`𝟙₍₋₂₎𝟙 = δ_{-2,-1}𝟙 = 0`). -/
@[simp] theorem T_vacuum (V : PreVertexAlgebra 𝒱) : V.T V.vacuum = 0 := by
  simp only [T_apply, smul_vacuum_left]
  norm_num

/-- The translation operator raises the conformal grading by one: `T : 𝒱ₖ → 𝒱_{k+1}`
(from VA1, since `T u = u₍₋₂₎𝟙` with `𝟙 ∈ 𝒱₀`, landing in `𝒱_{k+0-(-2)-1} = 𝒱_{k+1}`). -/
theorem T_mem_grading (V : PreVertexAlgebra 𝒱) {k : ℤ} {u : 𝒱} (hu : u ∈ V.grading k) :
    V.T u ∈ V.grading (k + 1) := by
  have h := V.smul_mem_grading hu V.vacuum_mem (-2)
  rw [show k + 0 - (-2) - 1 = k + 1 by ring] at h
  rw [T_apply]
  exact h

end PreVertexAlgebra

/-! ## `T = L₋₁` and the derivative property, at the VOA level (Gannon 5.1.8)

Design decision.  Gannon's *bare* vertex algebra has no
translation-covariance axiom, so `Y(Tu,z)=∂_z Y(u,z)` must be *derived* and the argument
is genuinely circular at the bare-VA level.  At the **VOA level** axiom VOA3
(`Y_L_neg_one : Y(L₋₁v,z)=∂_z Y(v,z)`) *supplies* translation covariance, which breaks the
circularity.  We therefore develop the reconstruction at the VOA level: `T = L₋₁` and the
derivative property below are immediate, and the creation theorem `Y(a,z)𝟙 = e^{zT}a`
follows by induction (see `creation_pow`).  The engine for full duality (5.1.9), Goddard
uniqueness (`Core.Goddard`), then consumes `creation_pow`; the duality is proved downstream in
`Core.Reconstruction`. -/

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **`T = L₋₁`** (Gannon 5.1.8b): in a VOA the translation operator `T u = u₍₋₂₎𝟙`
coincides with `L₋₁ = ω₍₀₎`.  Proved directly from VOA3 (`Y_L_neg_one`, i.e.
`Y(L₋₁v,z)=∂_z Y(v,z)`) and VA3 (creation), with **no reconstruction**:
`L₋₁u = (L₋₁u)₍₋₁₎𝟙 = (∂_z Y(u))₍₋₁₎𝟙 = u₍₋₂₎𝟙 = Tu`. -/
theorem T_eq_Lneg1 (W : VertexOperatorAlgebra 𝒱) : W.toPreVertexAlgebra.T = W.L (-1) := by
  ext u
  have h1 : W.L (-1) u = mode (deriv (W.Y u)) (-1) W.vacuum := by
    rw [← Y_L_neg_one]
    exact (PreVertexAlgebra.smul_vacuum_neg_one W.toPreVertexAlgebra (W.L (-1) u)).symm
  rw [h1, PreVertexAlgebra.T_apply, PreVertexAlgebra.smul_def, mode_deriv]
  norm_num

/-- **The derivative property `Y(Tu,z)=∂_z Y(u,z)`** (Gannon 5.1.8a) at the VOA level:
since `T = L₋₁` (`T_eq_Lneg1`), this is exactly VOA3 (`Y_L_neg_one`). -/
theorem Y_T (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) :
    W.Y (W.toPreVertexAlgebra.T u) = deriv (W.Y u) := by
  have h : W.toPreVertexAlgebra.T u = W.L (-1) u := by rw [T_eq_Lneg1]
  rw [h]
  exact Y_L_neg_one W u

/-- The mode form of the derivative property: `(Tu)₍ₙ₎ = -n·u₍ₙ₋₁₎` (Gannon 5.1.8a). -/
theorem mode_Y_T (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (n : ℤ) :
    mode (W.Y (W.toPreVertexAlgebra.T u)) n = (-n) • mode (W.Y u) (n - 1) := by
  rw [Y_T, mode_deriv]

/-- **The iterated derivative property** `Y(Tʲu, z) = ∂_z^j Y(u, z)` (Gannon 5.1.8a,
iterated): the field of the `j`-th translate `Tʲu` is the `j`-th `z`-derivative of `Y(u,z)`.
Immediate induction off `Y_T` (the `j = 1` case, VOA3); it packages the relation between the
translation operator `T = L₋₁` and the formal derivative `∂_z` at all orders, the
power-series companion of `creation_pow`'s `Y(u,z)𝟙 = e^{zT}u`. -/
theorem Y_Tpow (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (j : ℕ) :
    W.Y ((W.toPreVertexAlgebra.T ^ j) u) = (deriv^[j]) (W.Y u) := by
  induction j with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, Y_T, ih, Function.iterate_succ', Function.comp_apply]

/-- **The creation theorem** (Gannon, after 5.1.8; the power-series form of
`Y(a,z)𝟙 = e^{zT}a`): `a₍₋k₋₁₎𝟙 = Tᵏa / k!` for `k ≥ 0`.  Proved by induction on `k` using
only the derivative property `mode_Y_T` (from VOA3) and VA3 creation — **no
reconstruction**.  This is the input the Goddard uniqueness theorem needs (the vacuum
expansion of any field). -/
theorem creation_pow (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (k : ℕ) :
    W.smul a (-(k : ℤ) - 1) W.vacuum
      = ((k.factorial : ℂ)⁻¹) • ((W.toPreVertexAlgebra.T ^ k) a) := by
  induction k generalizing a with
  | zero =>
      rw [show (-(↑(0 : ℕ) : ℤ) - 1) = -1 by norm_num, PreVertexAlgebra.smul_vacuum_neg_one]
      simp
  | succ k ih =>
      have key : W.smul (W.toPreVertexAlgebra.T a) (-(k : ℤ) - 1) W.vacuum
          = ((k : ℤ) + 1) • W.smul a (-(k : ℤ) - 2) W.vacuum := by
        rw [PreVertexAlgebra.smul_def, PreVertexAlgebra.smul_def, mode_Y_T,
          show (-(-(k : ℤ) - 1)) = (k : ℤ) + 1 by ring,
          show ((-(k : ℤ) - 1) - 1) = -(k : ℤ) - 2 by ring, LinearMap.smul_apply]
      have hih := ih (W.toPreVertexAlgebra.T a)
      have hTk : (W.toPreVertexAlgebra.T ^ k) (W.toPreVertexAlgebra.T a)
          = (W.toPreVertexAlgebra.T ^ (k + 1)) a := by rw [pow_succ]; rfl
      rw [key, hTk] at hih
      rw [show (-(↑(k + 1) : ℤ) - 1) = -(k : ℤ) - 2 by push_cast; ring]
      have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      rw [← Int.cast_smul_eq_zsmul ℂ ((k : ℤ) + 1)] at hih
      push_cast at hih
      have hX : W.smul a (-(k : ℤ) - 2) W.vacuum
          = ((k : ℂ) + 1)⁻¹ • ((k.factorial : ℂ)⁻¹ • (W.toPreVertexAlgebra.T ^ (k + 1)) a) := by
        rw [← hih, inv_smul_smul₀ hk1]
      rw [hX, smul_smul]
      congr 1
      rw [← mul_inv, Nat.factorial_succ]
      push_cast
      ring

end VertexOperatorAlgebra

end VOA
