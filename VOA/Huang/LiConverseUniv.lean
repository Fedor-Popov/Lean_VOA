import VOA.Huang.LiRegularAdm
import VOA.Huang.LiFusionInduced

/-! # The universal property of an irreducible lowest-weight module

For an admissibly rational VOA (with the explicit regular-module PBW datum `Pr`), an irreducible
lowest-weight module `P` is its own generalized Verma module (`pPhiBar_bijective_of_admissiblyRational`).
Composing the inverse with the Dong–Jiang induced map `oLevUnivMap` gives:

* `exists_hom_of_bottom` — every `A(V)`-equivariant map from the bottom `Ω(P)` into the level-`0`
  piece of an admissible level structure on a weak module `E` extends to a module map `P → E`;
* `hom_ext_of_bottom` — two module maps out of an irreducible `P` agreeing on the bottom agree.

These are the two universal-property steps of Li's construction (math/9909007, §4).

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.Huang.LiFusion VHat VHat.DLM3

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- On any weak module, the level-`0` zero mode of the vacuum is the identity. -/
theorem oLevW_vacuum (A : WeakModule W E) (x : E) : oLevW A 0 W.vacuum x = x := by
  rw [oLevW_homogeneous A 0 W.vacuum_mem_grading_zero]
  simp [A.vacuum_YM, mode_one]

/-- **Extension from the bottom.** -/
theorem exists_hom_of_bottom (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hrat : AdmissiblyRational W) (P : LWModule W) (hP : P.IsIrreducibleLW)
    (A : WeakModule W E) (L : AdmLev W A)
    (φ : (pBotAmMod P).carrier →ₗ[ℂ] E) (hlev : ∀ u, φ u ∈ L.lev 0)
    (hact : ∀ (a : V) (u : (pBotAmMod P).carrier),
      φ ((pBotAmMod P).ρ (mkAnFull W 0 a) u) = oLevW A (0 : ℤ) a (φ u)) :
    ∃ Φ : P.carrier →ₗ[ℂ] E,
      (∀ (a : V) (p : ℤ) (y : P.carrier),
        Φ (mode (P.isMod.YM a) p y) = mode (A.YM a) p (Φ y)) ∧
      ∀ u, Φ (pBotIncl P u) = φ u := by
  let e := LinearEquiv.ofBijective (pPhiBar P)
    (pPhiBar_bijective_of_admissiblyRational Pr hrat P hP)
  let U := oLevUnivMap A L (pBotAmMod P) φ hlev hact
  refine ⟨U.comp e.symm.toLinearMap, fun a p y => ?_, fun u => ?_⟩
  · obtain ⟨x, rfl⟩ := e.surjective y
    have h1 : mode (P.isMod.YM a) p (e x) = e (djModeZero W (pBotAmMod P) p a x) := by
      change _ = pPhiBar P _
      rw [pPhiBar_intertwine]; rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, LinearEquiv.symm_apply_apply]
    have := oLevUnivMap_intertwine L (pBotAmMod P) φ hlev hact p a x
    rw [WeakModule.act_def] at this
    exact this
  · have hb := pPhiBar_bottom P u
    have h2 : e.symm (pBotIncl P u) = DJCarrier.incl W (pBotAmMod P) 0
        (mkDJPiece W (pBotAmMod P) 0 (mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] u)) := by
      rw [← hb]; exact e.symm_apply_apply _
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h2, U, oLevUnivMap_incl,
      oLevPieceMap_mk, Nat.cast_zero, sub_zero]
    exact oLevW_vacuum A (φ u)

/-- **Uniqueness from the bottom.** -/
theorem hom_ext_of_bottom (P : LWModule W) (hP : P.IsIrreducibleLW) (A : WeakModule W E)
    (Φ Ψ : P.carrier →ₗ[ℂ] E)
    (hΦ : ∀ (a : V) (p : ℤ) (y : P.carrier), Φ (mode (P.isMod.YM a) p y) = mode (A.YM a) p (Φ y))
    (hΨ : ∀ (a : V) (p : ℤ) (y : P.carrier), Ψ (mode (P.isMod.YM a) p y) = mode (A.YM a) p (Ψ y))
    (hb : ∀ u, Φ (pBotIncl P u) = Ψ (pBotIncl P u)) : Φ = Ψ := by
  let K : WeakModule.Submodule' P.isMod.toWeakModule :=
    { carrier := LinearMap.ker (Φ - Ψ)
      act_mem := fun a n x hx => by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx ⊢
        change Φ (mode (P.isMod.YM a) n x) = Ψ (mode (P.isMod.YM a) n x)
        rw [hΦ, hΨ, hx] }
  rcases hP.2 K with h | h
  · exfalso
    obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.realized
    have : x ∈ K.carrier := by
      change x ∈ LinearMap.ker (Φ - Ψ)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      exact hb ⟨x, hx⟩
    rw [h] at this
    exact hne ((Submodule.mem_bot ℂ).1 this)
  · ext y
    have : y ∈ K.carrier := by rw [h]; trivial
    change y ∈ LinearMap.ker (Φ - Ψ) at this
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this

end VOA.Huang.LiRegular
