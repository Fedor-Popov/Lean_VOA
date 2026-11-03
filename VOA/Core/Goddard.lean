/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.Fields

/-!
# Goddard's uniqueness theorem  (Gannon §5.1.2–5.1.3; Kac §4.4)

The engine of the reconstruction/duality theorems.  **Goddard uniqueness**: a field
`A(z)` that is mutually local with every vertex operator `Y(b,z)` and creates the *same*
vacuum vector as `Y(a,z)` (i.e. `A(z)𝟙 = Y(a,z)𝟙`) must already equal `Y(a,z)`.

The proof needs only the lower-truncation cancellation
(`Foundations.IteratedLaurent.eq_zero_of_mulBySubPow_of_bddBelow`) — *not* the general-`n`
`ι_z` calculus.  For each `b`, locality of `A` (and of `Y(a,·)`) with `Y(b,·)`, applied to
the vacuum, shows that the two product fields `A(z)Y(b,w)𝟙` and `Y(a,z)Y(b,w)𝟙` agree
after multiplication by `(z-w)ᴺ`.  Both lie in `𝒱((z))((w))` because `Y(b,w)𝟙 = e^{wT}b`
has only non-negative `w`-powers; so the cancellation forces them equal, and reading off
the `w⁰`-coefficient (`Y(b,w)𝟙|_{w=0} = b`, creation) gives `A(z)b = Y(a,z)b`.

## Dependencies
* `VOA.Core.Fields` (hence `PreVertexAlgebra`, `Foundations.IteratedLaurent`).

## Status
Complete & `sorry`-free / axiom-free.  `goddard_uniqueness` is proved — the engine of the
reconstruction cascade.  Combined with Dong's lemma for all `n` (`Core.Dong`) it discharges
the locality hypothesis and drives the duality `nth_product`/`assoc_nonneg` (`n ≥ 0`) and the
normal-ordered duality (`n < 0`) in `Core.Reconstruction`; see `README.md`.

## References
* Gannon §5.1.2–5.1.3; Kac, *VA for Beginners* §4.4 (uniqueness theorem); Frenkel–Ben-Zvi
  §3.1 (the "Goddard uniqueness" / reconstruction lemma).
-/

namespace VOA

open Module (End)

universe u

/-! ## Raising the power in `(z₁-z₂)ᴺ`-annihilation -/

section Pow

variable {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-- `(z₁-z₂)^{a+b} = (z₁-z₂)ᵃ · (z₁-z₂)ᵇ` as operators on `FormalDist₂`. -/
theorem mulBySubPow_add (a b : ℕ) (f : FormalDist₂ 𝒲) :
    mulBySubPow (a + b) f = mulBySubPow a (mulBySubPow b f) := by
  induction a with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_add, mulBySubPow_succ, LinearMap.comp_apply, ih,
        ← LinearMap.comp_apply, ← mulBySubPow_succ]

/-- If `(z₁-z₂)ᴺ f = 0` then `(z₁-z₂)ᴹ f = 0` for any `M ≥ N`. -/
theorem mulBySubPow_eq_zero_mono {N M : ℕ} (h : N ≤ M) {f : FormalDist₂ 𝒲}
    (hf : mulBySubPow N f = 0) : mulBySubPow M f = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm, mulBySubPow_add, hf, map_zero]

end Pow

/-! ## Evaluating an operator-valued two-variable distribution on a vector -/

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- Apply an `End ℂ 𝒱`-valued two-variable distribution to a fixed vector `x`, coefficient
by coefficient: `(applyVec x f) m n = (f m n) x`. -/
def applyVec (x : 𝒱) (f : FormalDist₂ (End ℂ 𝒱)) : FormalDist₂ 𝒱 := fun m n => (f m n) x

@[simp] theorem applyVec_apply (x : 𝒱) (f : FormalDist₂ (End ℂ 𝒱)) (m n : ℤ) :
    applyVec x f m n = (f m n) x := rfl

@[simp] theorem applyVec_zero (x : 𝒱) : applyVec x (0 : FormalDist₂ (End ℂ 𝒱)) = 0 := by
  ext m n; exact LinearMap.zero_apply x

/-- Evaluation on a vector commutes with multiplication by `(z₁-z₂)`. -/
theorem applyVec_mulBySub (x : 𝒱) (f : FormalDist₂ (End ℂ 𝒱)) :
    applyVec x (mulBySub f) = mulBySub (applyVec x f) := by
  ext m n
  simp only [applyVec_apply, mulBySub_apply, LinearMap.sub_apply]

/-- Evaluation on a vector commutes with multiplication by `(z₁-z₂)ᴺ`. -/
theorem applyVec_mulBySubPow (N : ℕ) (x : 𝒱) (f : FormalDist₂ (End ℂ 𝒱)) :
    applyVec x (mulBySubPow N f) = mulBySubPow N (applyVec x f) := by
  induction N with
  | zero => simp
  | succ k ih =>
      rw [mulBySubPow_succ, LinearMap.comp_apply, applyVec_mulBySub, ih,
        ← LinearMap.comp_apply, ← mulBySubPow_succ]

namespace PreVertexAlgebra

/-! ## The vacuum expansion `Y(b,w)𝟙 = e^{wT}b` (only non-negative `w`-powers) -/

/-- `Y(b,w)𝟙` has no negative powers of `w`: `(Y b)ₙ 𝟙 = 0` for `n < 0` (creation, VA3). -/
theorem Y_apply_vacuum_eq_zero (V : PreVertexAlgebra 𝒱) (b : 𝒱) {n : ℤ} (hn : n < 0) :
    (V.Y b) n V.vacuum = 0 := by
  have h : (V.Y b) n V.vacuum = V.smul b (-n - 1) V.vacuum := by
    rw [smul_def, mode_apply, show (-(-n - 1) - 1 : ℤ) = n by ring]
  rw [h]
  exact V.smul_vacuum_nonneg b (by omega)

/-- `Y(b,w)𝟙|_{w=0} = b`: the `w⁰`-coefficient of `Y(b,w)𝟙` is `b` (creation, VA3). -/
theorem Y_apply_vacuum_zero (V : PreVertexAlgebra 𝒱) (b : 𝒱) : (V.Y b) 0 V.vacuum = b := by
  have h : (V.Y b) 0 V.vacuum = V.smul b (-1) V.vacuum := by
    rw [smul_def, mode_apply]; norm_num
  rw [h, smul_vacuum_neg_one]

/-! ## Goddard uniqueness -/

/-- The difference field `A(z)Y(b,w)𝟙 - Y(a,z)Y(b,w)𝟙` of the Goddard argument. -/
private def goddardDiff (V : PreVertexAlgebra 𝒱) (A : FormalDist (End ℂ 𝒱)) (a b : 𝒱) :
    FormalDist₂ 𝒱 := fun p q => A p ((V.Y b) q V.vacuum) - (V.Y a) p ((V.Y b) q V.vacuum)

@[simp] private theorem goddardDiff_apply (V : PreVertexAlgebra 𝒱) (A : FormalDist (End ℂ 𝒱))
    (a b : 𝒱) (p q : ℤ) :
    goddardDiff V A a b p q = A p ((V.Y b) q V.vacuum) - (V.Y a) p ((V.Y b) q V.vacuum) := rfl

/-- **Goddard's uniqueness theorem** (Gannon §5.1.2–5.1.3; Kac §4.4).  If a field `A(z)`
is mutually local with every `Y(b,z)` and creates the same vacuum vector as `Y(a,z)`
(`A(z)𝟙 = Y(a,z)𝟙`, i.e. `A m 𝟙 = (Y a) m 𝟙` for all `m`), then `A = Y(a,·)`.  The proof
uses only the `(z-w)ᴺ` cancellation on `𝒱((z))((w))`. -/
theorem goddard_uniqueness (V : PreVertexAlgebra 𝒱) (A : FormalDist (End ℂ 𝒱)) (a : 𝒱)
    (hAloc : ∀ b : 𝒱, Local A (V.Y b))
    (hAvac : ∀ m : ℤ, A m V.vacuum = (V.Y a) m V.vacuum) :
    A = V.Y a := by
  funext m
  refine LinearMap.ext fun b => ?_
  obtain ⟨N₁, hN₁⟩ := hAloc b
  obtain ⟨N₂, hN₂⟩ := V.locality a b
  -- The difference field, written as a difference of two `applyVec`-bracket distributions.
  have hDeq : goddardDiff V A a b = applyVec V.vacuum (bracketDist A (V.Y b))
      - applyVec V.vacuum (bracketDist (V.Y a) (V.Y b)) := by
    ext p q
    have hsub : (applyVec V.vacuum (bracketDist A (V.Y b))
        - applyVec V.vacuum (bracketDist (V.Y a) (V.Y b))) p q
        = applyVec V.vacuum (bracketDist A (V.Y b)) p q
          - applyVec V.vacuum (bracketDist (V.Y a) (V.Y b)) p q := rfl
    rw [hsub]
    simp only [goddardDiff_apply, applyVec_apply, bracketDist_apply, LinearMap.sub_apply,
      Module.End.mul_apply]
    rw [hAvac p]
    abel
  -- It is annihilated by `(z-w)^(N₁+N₂)`.
  have hkill : mulBySubPow (N₁ + N₂) (goddardDiff V A a b) = 0 := by
    rw [hDeq, map_sub]
    have e1 : mulBySubPow (N₁ + N₂) (applyVec V.vacuum (bracketDist A (V.Y b))) = 0 :=
      mulBySubPow_eq_zero_mono (Nat.le_add_right N₁ N₂)
        (by rw [← applyVec_mulBySubPow, hN₁, applyVec_zero])
    have e2 : mulBySubPow (N₁ + N₂) (applyVec V.vacuum (bracketDist (V.Y a) (V.Y b))) = 0 :=
      mulBySubPow_eq_zero_mono (Nat.le_add_left N₂ N₁)
        (by rw [← applyVec_mulBySubPow, hN₂, applyVec_zero])
    rw [e1, e2, sub_zero]
  -- It lies in `𝒱((z))((w))` (lower-truncated in `w`), since `Y(b,w)𝟙` is a power series.
  have hbb : IsBddBelow₂ (goddardDiff V A a b) := by
    refine ⟨0, fun p q hq => ?_⟩
    rw [goddardDiff_apply, V.Y_apply_vacuum_eq_zero b hq, map_zero, map_zero, sub_zero]
  -- Cancellation: the difference field is zero.
  have hD0 : goddardDiff V A a b = 0 :=
    eq_zero_of_mulBySubPow_of_bddBelow (N₁ + N₂) _ hkill hbb
  -- Read off the `w⁰`-coefficient.
  have hfin : goddardDiff V A a b m 0 = 0 := congrFun (congrFun hD0 m) 0
  rw [goddardDiff_apply, V.Y_apply_vacuum_zero b, sub_eq_zero] at hfin
  exact hfin

end PreVertexAlgebra

/-! ## The existence companion: standalone Goddard uniqueness (abstract test fields)

The *existence*-direction reconstruction (building `Y` on a cyclic module from generating local
fields) needs the Goddard identification **before** any `PreVertexAlgebra` is available, so it cannot
invoke `goddard_uniqueness` (which consumes the structure's own `V.Y b` as test fields — circular).
The fix is the **non-circular** version below: it takes an *abstract* family of test fields `G b`
that each create `b` from the vacuum as a power series in `w`.  This is the engine that proves the
all-states map `YA` of the reconstruction theorem is well-defined and linear (a difference of word
fields creating the zero vacuum-tower is the zero field). -/

/-- **Standalone Goddard uniqueness** (abstract test fields, non-circular).  If a field `A` on a
`ℂ`-module `𝒱` with vacuum `vac` is mutually local with each test field `G b`, where each `G b`
*creates* `b` from the vacuum as a power series in `w` (`(G b) 0 vac = b` and `(G b) q vac = 0` for
`q < 0`), and `A` annihilates the vacuum (`A p vac = 0` for all `p`), then `A m b = 0` for every
`b, m`.  Uses only the `(z-w)ᴺ` cancellation on `𝒱((z))((w))` (no `PreVertexAlgebra` structure, no
`n < 0` Dong machinery). -/
theorem goddard_zero (vac : 𝒱) (A : FormalDist (End ℂ 𝒱)) (G : 𝒱 → FormalDist (End ℂ 𝒱))
    (hloc : ∀ b, Local A (G b))
    (hcre0 : ∀ b, (G b) 0 vac = b)
    (hcreneg : ∀ b, ∀ q : ℤ, q < 0 → (G b) q vac = 0)
    (hAvac : ∀ p : ℤ, A p vac = 0)
    (m : ℤ) (b : 𝒱) : A m b = 0 := by
  obtain ⟨N, hN⟩ := hloc b
  have hDeq : (fun p q : ℤ => A p ((G b) q vac)) = applyVec vac (bracketDist A (G b)) := by
    apply FormalDist₂.ext; intro p q
    show A p ((G b) q vac) = applyVec vac (bracketDist A (G b)) p q
    rw [applyVec_apply, bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply, hAvac, map_zero, sub_zero]
  have hkill : mulBySubPow N (fun p q : ℤ => A p ((G b) q vac)) = 0 := by
    rw [hDeq, ← applyVec_mulBySubPow, hN, applyVec_zero]
  have hbb : IsBddBelow₂ (fun p q : ℤ => A p ((G b) q vac)) :=
    ⟨0, fun p q hq => by change A p ((G b) q vac) = 0; rw [hcreneg b q hq, map_zero]⟩
  have hD0 : (fun p q : ℤ => A p ((G b) q vac)) = 0 :=
    eq_zero_of_mulBySubPow_of_bddBelow N _ hkill hbb
  have hfin := congrFun (congrFun hD0 m) 0
  change A m b = 0
  rw [← hcre0 b]
  exact hfin

end VOA
