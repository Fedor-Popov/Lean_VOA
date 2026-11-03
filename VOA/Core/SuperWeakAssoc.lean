/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.SuperSkew

/-!
# Reducing the super skew gate to a sign-free statement

`Core.SuperSkew` proves super skew-symmetry modulo the gate `WeakAssocLocε`.  This file
reduces that gate twice, and the second reduction is the substantive one:

1. **Locality ⟶ vacuum-locality.**  Following `Core.WeakAssoc` §A, Goddard uniqueness needs
   only the bracket *applied to the vacuum*, which is a strictly weaker hypothesis
   (`goddard_uniqueness_vacε`, `SkewVacLocalε`).
2. **Vacuum-locality ⟶ a statement with no sign in it.**  `skewVacLocalε_iff_signFree`.

## Why the second reduction matters

The Koszul sign enters the super skew candidate through `koszulOp`, which reads the parity of
its argument.  In the vacuum bracket the only arguments that ever appear are `𝟙` — which is
even, so the sign is `1` — and `(Y c)ₙ𝟙` — which has parity `|c|`, so the sign is the *same*
`koszul p q` that the bracket itself carries.  The two therefore factor out as a single scalar:

  `applyVec 𝟙 ⁅skewDistε u p, Y c⁆_{koszul p q}  =  koszul p q • applyVec 𝟙 ⁅skewDist₀ u, Y c⁆`

and since `koszul p q ≠ 0`, the two vanish together.

**Consequence.** What remains of the super skew gate is `SkewVacLocal₀`, in which no sign
appears at all — it is the literal analogue of the bosonic `Core.WeakAssoc.skewVacLocal`, whose
proof (the `vconv`/`negPowJump` kill engine, `Gfield_eq_jumpSum`, ~880 lines) uses neither
locality nor any sign. That port is therefore mechanical rather than mathematical, and this
file is the certificate that it is.

## References
* Gannon §5.1.3, eq. (5.1.8); FLM §8.8–8.10; Lepowsky–Li Ch. 2–3; and `Core/WeakAssoc.lean`,
  whose architecture this mirrors.
-/

namespace VOA

open Module (End)

universe u

namespace SuperVertexAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- `(Y c)ₙ𝟙` has the parity of `c`: modes add parities and the vacuum is even. -/
theorem Y_apply_vacuum_parity (V : SuperVertexAlgebra 𝒱) {q : ZMod 2} {c : 𝒱}
    (hc : c ∈ V.parity q) (n : ℤ) : (V.Y c) n V.vacuum ∈ V.parity q := by
  have h := V.parity_mode c hc V.vacuum V.vacuum_parity (-n - 1)
  rw [add_zero] at h
  rwa [mode_apply, show (-(-n - 1) - 1 : ℤ) = n by ring] at h

/-- **Goddard uniqueness from vacuum-locality only, `ε`-generically.**  The bracket need only
be annihilated *after* evaluation on the vacuum — strictly weaker than `Localε`. -/
theorem goddard_pointwise_vacε (V : SuperVertexAlgebra 𝒱) (A : FormalDist (End ℂ 𝒱)) (a : 𝒱)
    (ε : ℂ) (b : 𝒱)
    (hAloc : ∃ N : ℕ, mulBySubPow N (applyVec V.vacuum (bracketDistε ε A (V.Y b))) = 0)
    (hVloc : Localε ε (V.Y a) (V.Y b))
    (hAvac : ∀ m : ℤ, A m V.vacuum = (V.Y a) m V.vacuum) (m : ℤ) :
    A m b = (V.Y a) m b := by
  obtain ⟨N₁, hN₁⟩ := hAloc
  obtain ⟨N₂, hN₂⟩ := hVloc
  set D : FormalDist₂ 𝒱 :=
    fun p q => A p ((V.Y b) q V.vacuum) - (V.Y a) p ((V.Y b) q V.vacuum) with hD
  have hDeq : D = applyVec V.vacuum (bracketDistε ε A (V.Y b))
      - applyVec V.vacuum (bracketDistε ε (V.Y a) (V.Y b)) := by
    ext p q
    have hsub : (applyVec V.vacuum (bracketDistε ε A (V.Y b))
        - applyVec V.vacuum (bracketDistε ε (V.Y a) (V.Y b))) p q
        = applyVec V.vacuum (bracketDistε ε A (V.Y b)) p q
          - applyVec V.vacuum (bracketDistε ε (V.Y a) (V.Y b)) p q := rfl
    rw [hsub, hD]
    simp only [applyVec_apply, bracketDistε_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.mul_apply]
    rw [hAvac p]
    abel
  have hkill : mulBySubPow (N₁ + N₂) D = 0 := by
    rw [hDeq, map_sub]
    have e1 : mulBySubPow (N₁ + N₂) (applyVec V.vacuum (bracketDistε ε A (V.Y b))) = 0 :=
      mulBySubPow_eq_zero_mono (Nat.le_add_right N₁ N₂) hN₁
    have e2 : mulBySubPow (N₁ + N₂)
        (applyVec V.vacuum (bracketDistε ε (V.Y a) (V.Y b))) = 0 :=
      mulBySubPow_eq_zero_mono (Nat.le_add_left N₂ N₁)
        (by rw [← applyVec_mulBySubPow, hN₂, applyVec_zero])
    rw [e1, e2, sub_zero]
  have hbb : IsBddBelow₂ D := by
    refine ⟨0, fun p q hq => ?_⟩
    show A p ((V.Y b) q V.vacuum) - (V.Y a) p ((V.Y b) q V.vacuum) = 0
    rw [V.Y_apply_vacuum_eq_zero b hq, map_zero, map_zero, sub_zero]
  have hD0 : D = 0 := eq_zero_of_mulBySubPow_of_bddBelow (N₁ + N₂) _ hkill hbb
  have hfin : D m 0 = 0 := congrFun (congrFun hD0 m) 0
  rw [hD] at hfin
  simp only at hfin
  rw [V.Y_apply_vacuum_zero b, sub_eq_zero] at hfin
  exact hfin

end SuperVertexAlgebra

namespace SuperVertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The **sign-free** skew candidate: the bosonic-shaped field, with no `koszulOp`. -/
noncomputable def skewDist₀ (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) :
    FormalDist (End ℂ 𝒱) := fun t => skewOpε W u t

@[simp] theorem skewDist₀_apply (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) (t : ℤ) (b : 𝒱) :
    skewDist₀ W u t b = skewBase W u t b := rfl

/-- **The gate, after reduction 1**: vacuum-locality of the super skew candidate. -/
def SkewVacLocalε (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) (p : ZMod 2) : Prop :=
  ∀ (q : ZMod 2) (c : 𝒱), c ∈ W.parity q → ∃ N : ℕ,
    mulBySubPow N (applyVec W.vacuum
      (bracketDistε (koszul p q) (skewDistε W u p) (W.Y c))) = 0

/-- **The gate, after reduction 2**: the same statement with the sign removed.  This is the
literal analogue of the bosonic `Core.WeakAssoc.skewVacLocal`. -/
def SkewVacLocal₀ (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) : Prop :=
  ∀ c : 𝒱, ∃ N : ℕ,
    mulBySubPow N (applyVec W.vacuum (bracketDist (skewDist₀ W u) (W.Y c))) = 0

/-- **The sign factors out of the vacuum bracket.**

In the vacuum bracket the candidate is only ever applied to `𝟙` (even, sign `1`) and to
`(Y c)ₙ𝟙` (parity `|c|`, sign `koszul p q`) — the very sign the bracket carries.  So the whole
two-variable distribution is `koszul p q` times its sign-free counterpart. -/
theorem applyVec_bracketDistε_factor (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) (p : ZMod 2)
    {q : ZMod 2} {c : 𝒱} (hc : c ∈ W.parity q) :
    applyVec W.vacuum (bracketDistε (koszul p q) (skewDistε W u p) (W.Y c))
      = koszul p q • applyVec W.vacuum (bracketDist (skewDist₀ W u) (W.Y c)) := by
  ext m n
  have hsmul : (koszul p q • applyVec W.vacuum (bracketDist (skewDist₀ W u) (W.Y c))) m n
      = koszul p q • (applyVec W.vacuum (bracketDist (skewDist₀ W u) (W.Y c)) m n) := rfl
  rw [hsmul]
  simp only [applyVec_apply, bracketDistε_apply, bracketDist_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.mul_apply]
  -- the candidate on `(Y c)ₙ𝟙` picks up `koszul p q`; on `𝟙` it picks up `1`
  rw [skewDistε_homog W u p m (W.toSuperVertexAlgebra.Y_apply_vacuum_parity hc n),
    skewDistε_homog W u p m (q := 0) W.vacuum_parity, koszul_zero_right, one_smul]
  simp only [skewDist₀_apply, smul_sub, map_smul]

/-- **The two gates are equivalent.**  Hence what remains of super skew-symmetry contains no
sign at all. -/
theorem skewVacLocalε_iff_signFree (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) (p : ZMod 2) :
    SkewVacLocalε W u p ↔ ∀ (q : ZMod 2) (c : 𝒱), c ∈ W.parity q → ∃ N : ℕ,
      mulBySubPow N (applyVec W.vacuum (bracketDist (skewDist₀ W u) (W.Y c))) = 0 := by
  constructor <;> intro h q c hc <;> obtain ⟨N, hN⟩ := h q c hc <;> refine ⟨N, ?_⟩
  · rw [applyVec_bracketDistε_factor W u p hc, map_smul, smul_eq_zero] at hN
    exact hN.resolve_left (koszul_ne_zero p q)
  · rw [applyVec_bracketDistε_factor W u p hc, map_smul, hN, smul_zero]

/-- The sign-free gate `SkewVacLocal₀` implies the super one. -/
theorem skewVacLocalε_of_signFree (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) (p : ZMod 2)
    (h : SkewVacLocal₀ W u) : SkewVacLocalε W u p :=
  (skewVacLocalε_iff_signFree W u p).2 fun _ c _ => h c

/-! ## From vacuum-locality to the skew gate -/

/-- Vacuum-locality already forces the field identity, via `goddard_pointwise_vacε`. -/
theorem skewDistε_eq_Y_of_vacLocalε (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) {p : ZMod 2}
    (hu : u ∈ W.parity p) (h : SkewVacLocalε W u p) : skewDistε W u p = W.Y u := by
  funext m
  refine LinearMap.ext fun b => ?_
  obtain ⟨b₀, hb₀, b₁, hb₁, rfl⟩ :=
    W.toSuperVertexAlgebra.toParityGrading.exists_parity_decomp b
  have h0 : skewDistε W u p m b₀ = (W.Y u) m b₀ :=
    SuperVertexAlgebra.goddard_pointwise_vacε W.toSuperVertexAlgebra _ u (koszul p 0) b₀
      (h 0 b₀ hb₀) (W.locality u hu b₀ hb₀) (fun t => skewDistε_vacuum W u p t) m
  have h1 : skewDistε W u p m b₁ = (W.Y u) m b₁ :=
    SuperVertexAlgebra.goddard_pointwise_vacε W.toSuperVertexAlgebra _ u (koszul p 1) b₁
      (h 1 b₁ hb₁) (W.locality u hu b₁ hb₁) (fun t => skewDistε_vacuum W u p t) m
  rw [map_add, map_add, h0, h1]

/-- **Reduction 1.**  Vacuum-locality implies the full skew gate `WeakAssocLocε`. -/
theorem weakAssocLocε_of_vacLocalε (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) {p : ZMod 2}
    (hu : u ∈ W.parity p) (h : SkewVacLocalε W u p) : WeakAssocLocε W u p := by
  intro q c hc
  rw [skewDistε_eq_Y_of_vacLocalε W u hu h]
  exact W.locality u hu c hc

/-- **The whole super skew gate, reduced to a sign-free statement.**  If the sign-free vacuum
bracket is local — the literal analogue of the bosonic `skewVacLocal`, whose proof uses neither
locality nor any sign — then super skew-symmetry holds. -/
theorem weakAssocLocε_of_signFree (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) {p : ZMod 2}
    (hu : u ∈ W.parity p) (h : SkewVacLocal₀ W u) : WeakAssocLocε W u p :=
  weakAssocLocε_of_vacLocalε W u hu (skewVacLocalε_of_signFree W u p h)

/-- **Super skew-symmetry from the sign-free gate.**  The end of the chain: `skew_modeε`
holds as soon as the sign-free vacuum computation does. -/
theorem skew_modeε_of_signFree (W : SuperVertexOperatorAlgebra 𝒱) (u v : 𝒱) {p q : ZMod 2}
    (hu : u ∈ W.parity p) (hv : v ∈ W.parity q) (h : SkewVacLocal₀ W u) (n : ℤ) :
    W.smul u n v
      = koszul p q • ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-n - 1 - j)) •
          ((W.L (-1) ^ j) ((W.Y v) (-n - 1 - j) u)) :=
  skew_modeε W u v hu hv (weakAssocLocε_of_signFree W u hu h) n

end SuperVertexOperatorAlgebra

end VOA
