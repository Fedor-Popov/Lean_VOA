/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.SymplecticFermion
import Mathlib.Algebra.DualNumber

/-!
# The translation operator `T = L₋₁` for symplectic fermions

`reconstructε` needs a `T` with `T|0⟩ = 0` and each generator field `T`-covariant,
`[T, aₘ] = (m+1)·a_{m+1}`.  On states `T` is the derivation extending the mode shift
`χᵃ_{-k-1} ↦ (k+1)·χᵃ_{-k-2}`.

## Why dual numbers

Building a **derivation** on a Clifford algebra from a linear map on the generating space is not
in Mathlib — `CliffordAlgebra.lift` produces *algebra maps*.  The standard device recovers one
from the other: an algebra map into the dual numbers `A[ε]` is exactly a pair (algebra map,
derivation along it), so `T := snd ∘ Φ` for a suitable `Φ : FockSF →ₐ FockSF[ε]`.

The Clifford condition costs nothing here.  With `g v = (ι v, ι (f v))`,

`g v * g v = (ι v · ι v, ι v · ι (f v) + ι (f v) · ι v)`,

and at `Q = 0` the first entry is `ι_sq_scalar` and the second the polar form — **both vanish**.
-/

namespace VOA.SympFerm

open CliffordAlgebra
open scoped DualNumber

/-- The mode shift `(k,a) ↦ (k+1)·(k+1,a)` underlying `L₋₁`. -/
noncomputable def shiftMap : SFModes →ₗ[ℂ] SFModes :=
  Finsupp.lsum ℂ fun p =>
    LinearMap.toSpanSingleton ℂ SFModes
      (((p.1 : ℂ) + 1) • Finsupp.single ((p.1 + 1, p.2) : ℕ × Fin 2) (1 : ℂ))

@[simp] theorem shiftMap_single (p : ℕ × Fin 2) (c : ℂ) :
    shiftMap (Finsupp.single p c)
      = c • (((p.1 : ℂ) + 1) • Finsupp.single ((p.1 + 1, p.2) : ℕ × Fin 2) (1 : ℂ)) := by
  simp [shiftMap]

/-- The generator map into dual numbers: `v ↦ (ι v, ι (shift v))`. -/
noncomputable def tGen : SFModes →ₗ[ℂ] FockSF[ε] where
  toFun v := TrivSqZeroExt.inl (ι QSF v) + TrivSqZeroExt.inr (ι QSF (shiftMap v))
  map_add' u v := by
    simp only [map_add, TrivSqZeroExt.inl_add, TrivSqZeroExt.inr_add]
    abel
  map_smul' c v := by
    simp only [RingHom.id_apply, map_smul, TrivSqZeroExt.inl_smul, TrivSqZeroExt.inr_smul,
      smul_add]

@[simp] theorem tGen_fst (v : SFModes) : (tGen v).fst = ι QSF v := by
  change (TrivSqZeroExt.inl (ι QSF v) + TrivSqZeroExt.inr (ι QSF (shiftMap v))).fst = _
  rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]

@[simp] theorem tGen_snd (v : SFModes) : (tGen v).snd = ι QSF (shiftMap v) := by
  change (TrivSqZeroExt.inl (ι QSF v) + TrivSqZeroExt.inr (ι QSF (shiftMap v))).snd = _
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

/-- The Clifford condition — free at `Q = 0`: the `fst` entry is `ι_sq_scalar` and the `snd`
entry is the polar form, and both vanish. -/
theorem tGen_sq (v : SFModes) : tGen v * tGen v = algebraMap ℂ FockSF[ε] (QSF v) := by
  have hQ : QSF v = 0 := rfl
  rw [hQ, map_zero]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, tGen_fst, ι_sq_scalar]
    change (algebraMap ℂ FockSF) (QSF v) = (0 : FockSF[ε]).fst
    rw [hQ, map_zero]; rfl
  · rw [TrivSqZeroExt.snd_mul, tGen_fst, tGen_snd]
    change (ι QSF v) * (ι QSF (shiftMap v)) + (ι QSF (shiftMap v)) * (ι QSF v) = (0 : FockSF[ε]).snd
    rw [ι_mul_ι_add_swap]
    change (algebraMap ℂ FockSF) (QuadraticMap.polar (⇑QSF) v (shiftMap v)) = 0
    rw [show QuadraticMap.polar (⇑QSF) v (shiftMap v) = 0 by simp [QuadraticMap.polar], map_zero]

/-- The algebra map whose `ε`-component is `T`. -/
noncomputable def tHom : FockSF →ₐ[ℂ] FockSF[ε] := CliffordAlgebra.lift QSF ⟨tGen, tGen_sq⟩

@[simp] theorem tHom_ι (v : SFModes) : tHom (ι QSF v) = tGen v := by
  rw [tHom, CliffordAlgebra.lift_ι_apply]

/-- `tHom` has first component the identity — both sides are algebra maps agreeing on
generators. -/
theorem tHom_fst (x : FockSF) : (tHom x).fst = x := by
  have h : (TrivSqZeroExt.fstHom ℂ FockSF FockSF).comp tHom = AlgHom.id ℂ FockSF := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext; intro v
    change (tHom (ι QSF v)).fst = ι QSF v
    rw [tHom_ι, tGen_fst]
  exact congrArg (fun (f : FockSF →ₐ[ℂ] FockSF) => f x) h

/-- **The translation operator** `T = L₋₁`, as the `ε`-component of `tHom`. -/
noncomputable def T : Module.End ℂ FockSF where
  toFun x := (tHom x).snd
  map_add' x y := by simp only [map_add, TrivSqZeroExt.snd_add]
  map_smul' c x := by simp only [RingHom.id_apply, map_smul, TrivSqZeroExt.snd_smul]

@[simp] theorem T_apply (x : FockSF) : T x = (tHom x).snd := rfl

/-- **`T` is an even derivation** — this is the whole point of the dual-number route:
`snd_mul` in `TrivSqZeroExt` *is* the Leibniz rule. -/
theorem T_mul (x y : FockSF) : T (x * y) = x * T y + T x * y := by
  rw [T_apply, map_mul, TrivSqZeroExt.snd_mul, tHom_fst, tHom_fst]
  rfl

@[simp] theorem T_one : T (1 : FockSF) = 0 := by
  rw [T_apply, map_one]; rfl

@[simp] theorem T_ι (v : SFModes) : T (ι QSF v) = ι QSF (shiftMap v) := by
  rw [T_apply, tHom_ι, tGen_snd]

/-! ## The commutators of `T` with creation and annihilation

`T_mul`, `T_one`, `T_ι`, `T_algebraMap` are a complete interface, so `tHom` is sealed here.
Without that, the `mul` case of the Clifford induction below lets tactics unfold `T` into a
`CliffordAlgebra.lift` application and elaboration blows up (two earlier attempts each ran 35+
minutes on this file). -/

attribute [irreducible] tHom

/-- `T` kills scalars. -/
theorem T_algebraMap (c : ℂ) : T ((algebraMap ℂ FockSF) c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, T_one, smul_zero]

set_option maxHeartbeats 1000000 in
/-- `T` commutes with the grading involution. -/
theorem T_involute (x : FockSF) : T (involute x) = involute (T x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, T_algebraMap, map_zero]
  | ι v => rw [involute_ι, map_neg, T_ι, involute_ι]
  | mul x y hx hy =>
      have h1 : T (involute (x * y))
          = involute x * involute (T y) + involute (T x) * involute y := by
        rw [map_mul, T_mul, hx, hy]
      have h2 : involute (T (x * y))
          = involute x * involute (T y) + involute (T x) * involute y := by
        rw [T_mul, map_add, map_mul, map_mul]
      rw [h1, h2]
  | add x y hx hy => simp only [map_add, hx, hy]

set_option maxHeartbeats 1000000 in
/-- **The commutator of `T` with a contraction** is again a contraction, along the shifted
functional: `[T, d⌋] = -(d ∘ shift)⌋`.  Both sides are odd derivations agreeing on generators;
the `mul` case closes by using `T_involute` to move `T` past the sign, after which the whole
expression telescopes. -/
theorem T_contractLeft (d : SFModes →ₗ[ℂ] ℂ) (x : FockSF) :
    T (contractLeft d x) - contractLeft d (T x) = -contractLeft (d ∘ₗ shiftMap) x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      simp only [contractLeft_algebraMap, T_algebraMap, map_zero, sub_zero, neg_zero]
  | ι v =>
      simp only [contractLeft_ι, T_ι, T_algebraMap, LinearMap.comp_apply, zero_sub]
  | mul x y hx hy =>
      have e1 : T (contractLeft d (x * y))
          = (contractLeft d x * T y + T (contractLeft d x) * y)
            + (involute x * T (contractLeft d y) + T (involute x) * contractLeft d y) := by
        rw [contractLeft_mul' d x y, map_add, T_mul, T_mul]
      have e2 : contractLeft d (T (x * y))
          = (contractLeft d x * T y + involute x * contractLeft d (T y))
            + (contractLeft d (T x) * y + involute (T x) * contractLeft d y) := by
        rw [T_mul x y, map_add, contractLeft_mul' d x (T y), contractLeft_mul' d (T x) y]
      have hx' : T (contractLeft d x)
          = contractLeft d (T x) - contractLeft (d ∘ₗ shiftMap) x := by
        have h := hx; rw [sub_eq_iff_eq_add] at h; rw [h]; abel
      have hy' : T (contractLeft d y)
          = contractLeft d (T y) - contractLeft (d ∘ₗ shiftMap) y := by
        have h := hy; rw [sub_eq_iff_eq_add] at h; rw [h]; abel
      rw [e1, e2, T_involute, hx', hy', contractLeft_mul' (d ∘ₗ shiftMap) x y]
      simp only [sub_mul, mul_sub, neg_add]
      abel
  | add x y hx hy =>
      simp only [map_add, neg_add]
      rw [← hx, ← hy]
      abel

/-! ## Translation covariance of the generator fields

`DCovariant T a` is `[T, aₘ] = (m+1)•a_{m+1}`.  Specialising `T_contractLeft` and the derivation
property gives it for `chi`, closing the last `reconstructε` hypothesis at generator level. -/

/-- The shifted functional: `lapply (k,c) ∘ shift = k · lapply (k-1,c)`.  At `k = 0` both sides
vanish — no generator shifts *into* level `0`. -/
theorem lapply_comp_shiftMap (k : ℕ) (c : Fin 2) :
    (Finsupp.lapply ((k, c) : ℕ × Fin 2) : SFModes →ₗ[ℂ] ℂ) ∘ₗ shiftMap
      = (k : ℂ) • (Finsupp.lapply ((k - 1, c) : ℕ × Fin 2) : SFModes →ₗ[ℂ] ℂ) := by
  apply Finsupp.lhom_ext
  intro q b
  rw [LinearMap.comp_apply, shiftMap_single, LinearMap.smul_apply, map_smul, map_smul]
  simp only [Finsupp.lapply_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases hk : k = 0
  · subst hk
    rw [if_neg (by intro h; exact absurd (congrArg Prod.fst h) (by simp))]
    simp
  · by_cases hq : q = ((k - 1, c) : ℕ × Fin 2)
    · subst hq
      rw [if_pos (by simp [Prod.ext_iff]; omega), if_pos rfl]
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      push_cast
      ring
    · rw [if_neg (by
        intro h
        exact hq (by
          rw [Prod.ext_iff] at h ⊢
          exact ⟨by omega, h.2⟩)), if_neg hq]
      simp

/-- `[T, creation] `: the derivation property applied to a single generator. -/
theorem T_creBase (p : ℕ × Fin 2) :
    T * creBase p - creBase p * T = ((p.1 : ℂ) + 1) • creBase (p.1 + 1, p.2) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  change T (ι QSF (Finsupp.single p (1 : ℂ)) * x)
      - ι QSF (Finsupp.single p (1 : ℂ)) * T x = _
  rw [T_mul, add_sub_cancel_left, T_ι, shiftMap_single, one_smul, map_smul, smul_mul_assoc]
  rfl

/-- `[T, annihilation]`: `T_contractLeft` with the shifted functional evaluated. -/
theorem T_annBase (k : ℕ) (c : Fin 2) :
    T * annBase (k, c) - annBase (k, c) * T = -((k : ℂ) • annBase (k - 1, c)) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  change T (contractLeft (Finsupp.lapply ((k, c) : ℕ × Fin 2)) x)
      - contractLeft (Finsupp.lapply ((k, c) : ℕ × Fin 2)) (T x) = _
  rw [T_contractLeft, lapply_comp_shiftMap]
  change -(contractLeft ((k : ℂ) • (Finsupp.lapply ((k - 1, c) : ℕ × Fin 2)
      : SFModes →ₗ[ℂ] ℂ))) x = _
  rw [map_smul]
  rfl

/-- Conjugation by `T` is `ℂ`-linear in the operator. -/
theorem T_bracket_smul (c : ℂ) (S : Module.End ℂ FockSF) :
    T * (c • S) - (c • S) * T = c • (T * S - S * T) := by
  rw [mul_smul_comm, smul_mul_assoc, smul_sub]

/-- **Translation covariance of the generator fields** — the last `reconstructε` hypothesis
at generator level.  Creation modes shift up with weight `k+1`; annihilation modes shift down,
and the arithmetic matches because `annSF` already carries the mode as a coefficient. -/
theorem chi_DCovariant (a : Fin 2) : VOA.Reconstruction.DCovariant T (chi a) := by
  intro m
  by_cases hm : 0 ≤ m
  · -- creation side
    have h1 : chi a m = creBase (m.toNat, a) := by rw [chi, if_pos hm]; rfl
    have h2 : chi a (m + 1) = creBase ((m + 1).toNat, a) := by
      rw [chi, if_pos (by omega)]; rfl
    rw [h1, h2, T_creBase, show ((m.toNat, a) : ℕ × Fin 2).1 + 1 = (m + 1).toNat by omega,
      ← Int.cast_smul_eq_zsmul ℂ (m + 1)]
    congr 1
    rw [show ((m.toNat : ℕ) : ℂ) = (m : ℂ) by exact_mod_cast Int.toNat_of_nonneg hm]
    push_cast
    ring
  · by_cases hm1 : m = -1
    · -- the zero mode: both sides vanish
      subst hm1
      have h0 : chi a (-1) = 0 := by
        rw [chi, if_neg (by norm_num)]
        change annSF a (-(-1) - 1).toNat = 0
        norm_num
      rw [h0, mul_zero, zero_mul, sub_zero, show ((-1 : ℤ) + 1) = 0 by ring, zero_smul]
    · -- annihilation side
      have hm2 : m ≤ -2 := by omega
      have hj1 : 1 ≤ (-m - 1).toNat := by omega
      have h1 : chi a m
          = (((((-m - 1).toNat) : ℕ) : ℂ) * sfSign a) • annBase ((-m - 1).toNat - 1, a + 1) := by
        rw [chi, if_neg hm]; rfl
      have h2 : chi a (m + 1)
          = ((((((-m - 1).toNat) - 1 : ℕ)) : ℂ) * sfSign a)
              • annBase ((-m - 1).toNat - 1 - 1, a + 1) := by
        rw [chi, if_neg (by omega)]
        have hidx : (-(m + 1) - 1).toNat = (-m - 1).toNat - 1 := by omega
        rw [hidx]; rfl
      rw [h1, h2, T_bracket_smul, T_annBase, ← Int.cast_smul_eq_zsmul ℂ (m + 1), smul_smul,
        smul_neg, smul_smul]
      congr 1
      have hc : ((((-m - 1).toNat : ℕ) : ℂ)) = -(m : ℂ) - 1 := by
        have h : (((-m - 1).toNat : ℕ) : ℤ) = -m - 1 := Int.toNat_of_nonneg (by omega)
        exact_mod_cast h
      have hc2 : (((((-m - 1).toNat) - 1 : ℕ)) : ℂ) = -(m : ℂ) - 2 := by
        have h : ((((-m - 1).toNat) - 1 : ℕ) : ℤ) = -m - 2 := by omega
        exact_mod_cast h
      rw [hc, hc2]
      push_cast
      module

end VOA.SympFerm
