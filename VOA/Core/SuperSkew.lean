/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.SuperGoddard
import VOA.Core.SuperVertexOperatorAlgebra
import VOA.Core.Skew

/-!
# Super skew-symmetry (Gannon 5.1.8 with the Koszul sign)

Skew-symmetry for a super vertex operator algebra:
`Y(u,z)v = (-1)^{|u||v|} e^{zT} Y(v,-z) u`.

## The one structural difference from the bosonic case

The Koszul sign depends on the *argument* `v`, so it cannot be a scalar multiple of the
bosonic candidate field.  It is instead `(-1)^F` raised to `|u|`, i.e. the operator
`ParityGrading.koszulOp` — which is exactly why `Foundations/Parity` carries the fermion-number
involution.  The candidate field is therefore

  `skewDistε W u p := (bosonic-shaped candidate) ∘ koszulOp p`,

whose value on a parity-`q` vector is `koszul p q •` the bosonic value.

## What is proved here, and what is left

Everything except the locality of the candidate field:

* `skewCoeffFunε_vacuum` / `skewDistε_vacuum` — the vacuum condition, discharged;
* `skewε_eq_Y_of_localε` — **the reduction**: the candidate field *is* `Y(u,·)` as soon as it
  is Koszul-local against every `Y(b,·)`, via `goddard_uniquenessε`;
* `skew_modeε` — the super mode formula, read off the field identity.

The remaining gate of *this route* is `WeakAssocLocε`, the exact analogue of the bosonic
`WeakAssocLoc`; it is not discharged here.  ⚠ **Not the main route:** super skew-symmetry is proved
unconditionally, by another route, as `superSmul_eq_skew_Lpow` (`Modularity/SuperZhuCommutator.lean`,
derived from `superJacobi`, `Core/SuperBorcherds.lean`).  So `skew_modeε` is conditional only as
stated here; the content is available without the gate.

The translation operator is taken to be `L₋₁` directly rather than `u ↦ u₍₋₂₎𝟙`; the two agree
(bosonically this is `T_eq_Lneg1`), and taking `L₋₁` makes `Y(Tu,z) = ∂_z Y(u,z)` *literally*
the VOA3 axiom, so no port of that equivalence is needed.

## References
* Gannon §5.1.3, eq. (5.1.8); Kac, *VA for Beginners* §4.2 (super skew-symmetry);
  Frenkel–Huang–Lepowsky §8.8–8.10.
-/

namespace VOA

open scoped BigOperators
open Module (End)

universe u

namespace SuperVertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Translation and the vacuum expansion -/

/-- **VOA3, as stated**: `Y(L₋₁u, z) = ∂_z Y(u,z)`. -/
theorem Y_Tr (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) :
    W.Y (W.L (-1) u) = deriv (W.Y u) := by
  rw [L_def, show (-1 : ℤ) + 1 = 0 by ring]
  exact W.translation u

/-- The mode form of the derivative property. -/
theorem mode_Y_Tr (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) (n : ℤ) :
    mode (W.Y (W.L (-1) u)) n = (-n) • mode (W.Y u) (n - 1) := by
  rw [Y_Tr, mode_deriv]

/-- `Y(𝟙,z)` is the identity field, coefficient-wise. -/
theorem Y_vacuum_applyε (W : SuperVertexOperatorAlgebra 𝒱) (k : ℤ) (v : 𝒱) :
    (W.Y W.vacuum) k v = if k = 0 then v else 0 := by
  rw [W.vacuum_Y]
  show (1 : FormalDist (End ℂ 𝒱)) k v = _
  rw [FormalDist.one_apply]
  split_ifs with h
  · rfl
  · rfl

/-- **The creation theorem**: `a₍₋k₋₁₎𝟙 = Tᵏa / k!`, the power-series form of
`Y(a,z)𝟙 = e^{zT}a`.  Induction on `k` using only VOA3 and VA3. -/
theorem creation_powε (W : SuperVertexOperatorAlgebra 𝒱) (a : 𝒱) (k : ℕ) :
    W.smul a (-(k : ℤ) - 1) W.vacuum
      = ((k.factorial : ℂ)⁻¹) • ((W.L (-1) ^ k) a) := by
  induction k generalizing a with
  | zero =>
      rw [show (-(↑(0 : ℕ) : ℤ) - 1) = -1 by norm_num,
        SuperVertexAlgebra.smul_neg_one_vacuum]
      simp
  | succ k ih =>
      have key : W.smul (W.L (-1) a) (-(k : ℤ) - 1) W.vacuum
          = ((k : ℤ) + 1) • W.smul a (-(k : ℤ) - 2) W.vacuum := by
        rw [SuperVertexAlgebra.smul_def, SuperVertexAlgebra.smul_def, mode_Y_Tr,
          show (-(-(k : ℤ) - 1)) = (k : ℤ) + 1 by ring,
          show ((-(k : ℤ) - 1) - 1) = -(k : ℤ) - 2 by ring, LinearMap.smul_apply]
      have hih := ih (W.L (-1) a)
      have hTk : (W.L (-1) ^ k) (W.L (-1) a) = (W.L (-1) ^ (k + 1)) a := by
        rw [pow_succ]; rfl
      rw [key, hTk] at hih
      rw [show (-(↑(k + 1) : ℤ) - 1) = -(k : ℤ) - 2 by push_cast; ring]
      have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      rw [← Int.cast_smul_eq_zsmul ℂ ((k : ℤ) + 1)] at hih
      push_cast at hih
      have hX : W.smul a (-(k : ℤ) - 2) W.vacuum
          = ((k : ℂ) + 1)⁻¹ • ((k.factorial : ℂ)⁻¹ • (W.L (-1) ^ (k + 1)) a) := by
        rw [← hih, inv_smul_smul₀ hk1]
      rw [hX, smul_smul]
      congr 1
      rw [← mul_inv, Nat.factorial_succ]
      push_cast
      ring

/-! ## The candidate skew field -/

/-- The `z^t`-coefficient of the bosonic-shaped skew candidate, applied to `b`. -/
noncomputable def skewBase (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) (t : ℤ) (b : 𝒱) : 𝒱 :=
  ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (t - j)) • ((W.L (-1) ^ j) ((W.Y b) (t - j) u))

/-- Only finitely many `j` contribute, by VA5 regularity. -/
theorem skewBase_support_finite (W : SuperVertexOperatorAlgebra 𝒱) (u b : 𝒱) (t : ℤ) :
    (Function.support (fun j : ℕ => ((j.factorial : ℂ)⁻¹) • (sgn (t - j)) •
      ((W.L (-1) ^ j) ((W.Y b) (t - j) u)))).Finite := by
  obtain ⟨N, hN⟩ := W.regularity b u
  apply Set.Finite.subset (Set.finite_Icc 0 (N + t).toNat)
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hlt
  push_neg at hlt
  apply hj
  have hmode : (W.Y b) (t - j) u = 0 := by
    have h := hN (-(t - (j : ℤ)) - 1) (by omega)
    rwa [mode_apply, show (-(-(t - (j : ℤ)) - 1) - 1) = t - (j : ℤ) by ring] at h
  rw [hmode, map_zero, smul_zero, smul_zero]

/-- `skewBase` is linear in `b`, hence an endomorphism. -/
noncomputable def skewOpε (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) (t : ℤ) : End ℂ 𝒱 where
  toFun b := skewBase W u t b
  map_add' b₁ b₂ := by
    rw [skewBase, skewBase, skewBase,
      ← finsum_add_distrib (skewBase_support_finite W u b₁ t) (skewBase_support_finite W u b₂ t)]
    refine finsum_congr fun j => ?_
    rw [show (W.Y (b₁ + b₂)) (t - (j:ℤ)) u = (W.Y b₁) (t - (j:ℤ)) u + (W.Y b₂) (t - (j:ℤ)) u from by
          rw [map_add]; rfl, map_add, smul_add, smul_add]
  map_smul' c b := by
    rw [RingHom.id_apply, skewBase, skewBase, smul_finsum' c (skewBase_support_finite W u b t)]
    refine finsum_congr fun j => ?_
    rw [show (W.Y (c • b)) (t - (j:ℤ)) u = c • (W.Y b) (t - (j:ℤ)) u from by
          rw [map_smul]; rfl, map_smul]
    rw [smul_comm (sgn (t - (j:ℤ))) c, smul_comm ((j.factorial:ℂ)⁻¹) c]

@[simp] theorem skewOpε_apply (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) (t : ℤ) (b : 𝒱) :
    skewOpε W u t b = skewBase W u t b := rfl

/-- **The vacuum condition.**  On `𝟙` the candidate creates `e^{zT}u`, i.e. agrees with
`Y(u,·)`.  This is the Goddard input that is *not* a gate. -/
theorem skewBase_vacuum (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) (t : ℤ) :
    skewBase W u t W.vacuum = (W.Y u) t W.vacuum := by
  rw [skewBase]
  by_cases ht : 0 ≤ t
  · obtain ⟨T₀, rfl⟩ : ∃ T₀ : ℕ, t = (T₀ : ℤ) := ⟨t.toNat, by omega⟩
    rw [finsum_eq_single _ T₀ (fun j hj => ?_)]
    · rw [show ((T₀ : ℤ) - (T₀ : ℕ)) = 0 by ring, Y_vacuum_applyε, if_pos rfl,
        sgn, if_pos (by norm_num : Even (0 : ℤ)), one_smul]
      rw [show (W.Y u) (T₀ : ℤ) W.vacuum = W.smul u (-(T₀:ℤ) - 1) W.vacuum from by
            rw [SuperVertexAlgebra.smul_def, mode_apply,
              show (-(-(T₀:ℤ) - 1) - 1) = (T₀:ℤ) by ring]]
      rw [creation_powε]
    · rw [Y_vacuum_applyε, if_neg (by intro h; apply hj; omega), map_zero, smul_zero, smul_zero]
  · rw [not_le] at ht
    rw [show (∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn ((t : ℤ) - j)) •
          ((W.L (-1) ^ j) ((W.Y W.vacuum) ((t : ℤ) - j) u))) = 0 from ?_,
      SuperVertexAlgebra.Y_apply_vacuum_eq_zero W.toSuperVertexAlgebra u ht]
    refine finsum_eq_zero_of_forall_eq_zero (fun j => ?_)
    rw [Y_vacuum_applyε, if_neg (by omega), map_zero, smul_zero, smul_zero]

/-- **The super skew candidate field.**  The bosonic-shaped candidate precomposed with the
Koszul-sign operator, so that its value on a parity-`q` vector carries `(-1)^{|u|q}`. -/
noncomputable def skewDistε (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) (p : ZMod 2) :
    FormalDist (End ℂ 𝒱) :=
  fun t => (skewOpε W u t).comp (W.toSuperVertexAlgebra.toParityGrading.koszulOp p)

/-- On a parity-homogeneous vector the candidate is the bosonic one times the Koszul sign. -/
theorem skewDistε_homog (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) (p : ZMod 2) (t : ℤ)
    {q : ZMod 2} {b : 𝒱} (hb : b ∈ W.parity q) :
    skewDistε W u p t b = koszul p q • skewBase W u t b := by
  show skewOpε W u t (W.toSuperVertexAlgebra.toParityGrading.koszulOp p b) = _
  rw [ParityGrading.koszulOp_homog _ _ hb, map_smul, skewOpε_apply]

/-- The candidate satisfies the Goddard vacuum condition. -/
theorem skewDistε_vacuum (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) (p : ZMod 2) (t : ℤ) :
    skewDistε W u p t W.vacuum = (W.Y u) t W.vacuum := by
  rw [skewDistε_homog W u p t (q := 0) W.vacuum_parity, koszul_zero_right, one_smul,
    skewBase_vacuum]

/-! ## The reduction -/

/-- **The gate.**  Koszul-locality of the super skew candidate against every vertex operator.
The exact analogue of the bosonic `WeakAssocLoc`, and the one thing not proved here. -/
def WeakAssocLocε (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) (p : ZMod 2) : Prop :=
  ∀ (q : ZMod 2) (b : 𝒱), b ∈ W.parity q → Localε (koszul p q) (skewDistε W u p) (W.Y b)

/-- **THE REDUCTION.**  Given the gate, the super skew candidate *is* the vertex operator.
This is `goddard_uniquenessε` fed the vacuum condition proved above. -/
theorem skewDistε_eq_Y (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) {p : ZMod 2}
    (hu : u ∈ W.parity p) (hloc : WeakAssocLocε W u p) :
    skewDistε W u p = W.Y u :=
  SuperVertexAlgebra.goddard_uniquenessε W.toSuperVertexAlgebra (skewDistε W u p) u hu hloc
    (fun t => skewDistε_vacuum W u p t)

/-- **Super skew-symmetry, in mode form** (Gannon 5.1.8 with the Koszul sign):
`u₍ₙ₎v = (-1)^{|u||v|} ∑ⱼ (1/j!) (-1)^{-n-1-j} Tʲ (v₍₋ₙ₋₁₋ⱼ₎u)`.

Conditional on the gate `WeakAssocLocε`, exactly as the bosonic `skew_mode` was conditional
on `WeakAssocLoc` before `Core.WeakAssoc` discharged it. -/
theorem skew_modeε (W : SuperVertexOperatorAlgebra 𝒱) (u v : 𝒱) {p q : ZMod 2}
    (hu : u ∈ W.parity p) (hv : v ∈ W.parity q) (hloc : WeakAssocLocε W u p) (n : ℤ) :
    W.smul u n v
      = koszul p q • ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-n - 1 - j)) •
          ((W.L (-1) ^ j) ((W.Y v) (-n - 1 - j) u)) := by
  have hfield := skewDistε_eq_Y W u hu hloc
  have h := congrFun hfield (-n - 1)
  have hv' : skewDistε W u p (-n - 1) v = koszul p q • skewBase W u (-n - 1) v :=
    skewDistε_homog W u p (-n - 1) hv
  rw [h] at hv'
  rw [SuperVertexAlgebra.smul_def, mode_apply, hv', skewBase]

end SuperVertexOperatorAlgebra

end VOA
