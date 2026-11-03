/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.AModBridge
import VOA.Modularity.WedderburnSimples
import VOA.Modularity.SemisimpleTrace
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Link **L1**: a semisimple `A(𝒱)` has `dim A(𝒱)/[A(𝒱),A(𝒱)]` pairwise non-isomorphic
simple `AMod`s

`Modularity.SemisimpleTrace` computes the Wedderburn factor count intrinsically as
`dim A(𝒱)/[A(𝒱),A(𝒱)]`; `Modularity.AModBridge` identifies the `Modules` predicate `IsSimpleAMod`
with Mathlib's
`IsSimpleModule`.  This file closes L1 by realising each Wedderburn factor as a **simple bundled
`AMod W`**, in the language of `Modules.ZhuBijection` and in the ambient universe (`ULift`), and
showing the `n` of
them are pairwise non-isomorphic — the central idempotents `Pi.single i 1` separate them.

Everything is proved directly from `exists_matrix_mulVec_eq`, so neither `piSimple` nor the bridge
is needed here; the bridge is what lets the *statement* be read as `#(Wedderburn factors) ≤ #Irr`.

## Main results

* `wedderburnAMod e j` — the `j`-th Wedderburn simple, as an `AMod W`;
* `isSimpleAMod_wedderburnAMod`;
* `wedderburnAMod_isEmpty_amodEquiv` — pairwise non-isomorphic;
* `exists_pairwise_nonIso_simple_aMod` — Artin–Wedderburn form, with the count read off as
  `dim A(𝒱)/[A(𝒱),A(𝒱)]`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Carried: `IsSemisimpleRing (A W)` +
`FiniteDimensional ℂ (A W)` (i.e. rationality — a genuine hypothesis of Zhu's theorem).
-/

namespace VOA

open Module (End)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

section Wedderburn

variable {n : ℕ} {d : Fin n → ℕ}

/-- The carrier of the `j`-th Wedderburn simple, lifted to the ambient universe. -/
def wedderburnCarrier (d : Fin n → ℕ) (j : Fin n) : Type u := ULift.{u} (Fin (d j) → ℂ)

noncomputable instance : AddCommGroup (wedderburnCarrier.{u} d j) :=
  inferInstanceAs (AddCommGroup (ULift.{u} (Fin (d j) → ℂ)))

noncomputable instance : Module ℂ (wedderburnCarrier.{u} d j) :=
  inferInstanceAs (Module ℂ (ULift.{u} (Fin (d j) → ℂ)))

variable (W)

/-- The `j`-th Wedderburn simple as a bundled `A(𝒱)`-module. -/
noncomputable def wedderburnAMod
    (e : letI := instRingA W; letI := instAlgebraA W;
      A W ≃ₐ[ℂ] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ) (j : Fin n) : AMod W :=
  letI := instRingA W
  letI := instAlgebraA W
  { carrier := wedderburnCarrier.{u} d j
    ρ :=
      { toFun := fun a =>
          { toFun := fun x => ULift.up (Matrix.mulVec ((e a) j) x.down)
            map_add' := fun x y => by
              refine congrArg ULift.up ?_
              exact Matrix.mulVec_add _ _ _
            map_smul' := fun c x => by
              refine congrArg ULift.up ?_
              exact Matrix.mulVec_smul _ c _ }
        map_add' := fun a b => by
          refine LinearMap.ext (fun x => ?_)
          show ULift.up (Matrix.mulVec ((e (a + b)) j) x.down) = _
          rw [map_add]
          exact congrArg ULift.up (Matrix.add_mulVec _ _ _)
        map_smul' := fun c a => by
          refine LinearMap.ext (fun x => ?_)
          show ULift.up (Matrix.mulVec ((e (c • a)) j) x.down) = _
          rw [map_smul]
          exact congrArg ULift.up (Matrix.smul_mulVec c _ _) }
    ρ_one := by
      refine LinearMap.ext (fun x => ?_)
      show ULift.up (Matrix.mulVec ((e (one W)) j) x.down) = x
      rw [show (one W) = (1 : A W) from rfl, map_one]
      show ULift.up (Matrix.mulVec (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ) x.down) = x
      rw [Matrix.one_mulVec]
      rfl
    ρ_mul := fun u v => by
      refine LinearMap.ext (fun x => ?_)
      show ULift.up (Matrix.mulVec ((e (mk W (zhuMul W u v))) j) x.down) = _
      have hmul : (mk W (zhuMul W u v) : A W) = mk W u * mk W v := by
        show _ = Amul (zhuRingData_holds W) (mk W u) (mk W v)
        rw [Amul_mk]
      rw [hmul, map_mul]
      show _ = ULift.up (Matrix.mulVec ((e (mk W u)) j)
        (Matrix.mulVec ((e (mk W v)) j) x.down))
      exact congrArg ULift.up (Matrix.mulVec_mulVec _ _ _).symm }

variable {W}

theorem wedderburnAMod_ρ_apply
    (e : letI := instRingA W; letI := instAlgebraA W;
      A W ≃ₐ[ℂ] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ) (j : Fin n)
    (a : A W) (x : (wedderburnAMod W e j).carrier) :
    (wedderburnAMod W e j).ρ a x
      = ULift.up (Matrix.mulVec ((e a) j) (ULift.down x)) := rfl

/-- **Each Wedderburn factor gives a simple `AMod`.** -/
theorem isSimpleAMod_wedderburnAMod (hd : ∀ i, NeZero (d i))
    (e : letI := instRingA W; letI := instAlgebraA W;
      A W ≃ₐ[ℂ] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ) (j : Fin n) :
    IsSimpleAMod (wedderburnAMod W e j) := by
  classical
  letI := instRingA W
  letI := instAlgebraA W
  haveI : NeZero (d j) := hd j
  constructor
  · refine ⟨ULift.up 0, ULift.up (Pi.single ⟨0, Nat.pos_of_ne_zero (hd j).out⟩ 1), ?_⟩
    intro hc
    have := congrArg (fun z => (ULift.down z) ⟨0, Nat.pos_of_ne_zero (hd j).out⟩) hc
    simp only [Pi.single_eq_same] at this
    exact one_ne_zero this.symm
  · intro S
    by_cases hS : S.carrier = ⊥
    · exact Or.inl hS
    · right
      obtain ⟨x, hxS, hx0⟩ : ∃ x ∈ S.carrier, x ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hS (Submodule.eq_bot_iff _ |>.mpr hc)
      have hxd : (ULift.down x : Fin (d j) → ℂ) ≠ 0 := by
        intro hc
        exact hx0 (ULift.ext x 0 hc)
      rw [eq_top_iff]
      intro y _
      obtain ⟨A, hA⟩ := exists_matrix_mulVec_eq hxd (ULift.down y)
      have hmem := S.ρ_mem (e.symm (Pi.single j A)) hxS
      rw [wedderburnAMod_ρ_apply] at hmem
      have hval : ((e (e.symm (Pi.single j A))) j) = A := by
        rw [AlgEquiv.apply_symm_apply, Pi.single_eq_same]
      rw [hval, hA] at hmem
      simpa using hmem

/-- **Distinct Wedderburn factors give non-isomorphic simple `AMod`s.**  The central
idempotent `Pi.single i 1` acts as the identity on the `i`-th and as zero on the `j`-th. -/
theorem wedderburnAMod_isEmpty_amodEquiv (hd : ∀ i, NeZero (d i))
    (e : letI := instRingA W; letI := instAlgebraA W;
      A W ≃ₐ[ℂ] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ) {i j : Fin n} (hij : i ≠ j) :
    IsEmpty (AModEquiv W (wedderburnAMod W e i) (wedderburnAMod W e j)) := by
  classical
  letI := instRingA W
  letI := instAlgebraA W
  haveI : NeZero (d i) := hd i
  refine ⟨fun φ => ?_⟩
  set a : A W := e.symm (Pi.single i 1) with ha
  have hone : ∀ x : (wedderburnAMod W e i).carrier, (wedderburnAMod W e i).ρ a x = x := by
    intro x
    rw [wedderburnAMod_ρ_apply, ha, AlgEquiv.apply_symm_apply, Pi.single_eq_same,
      Matrix.one_mulVec]
    rfl
  have hzero : ∀ y : (wedderburnAMod W e j).carrier, (wedderburnAMod W e j).ρ a y = 0 := by
    intro y
    rw [wedderburnAMod_ρ_apply, ha, AlgEquiv.apply_symm_apply, Pi.single_eq_of_ne (Ne.symm hij)]
    show ULift.up (Matrix.mulVec (0 : Matrix (Fin (d j)) (Fin (d j)) ℂ) (ULift.down y)) = 0
    rw [Matrix.zero_mulVec]
    rfl
  have hall : ∀ x : (wedderburnAMod W e i).carrier, φ.toLinearEquiv x = 0 := by
    intro x
    rw [← hone x, φ.map_ρ, hzero]
  have hne : (0 : (wedderburnAMod W e i).carrier)
      ≠ ULift.up (Pi.single ⟨0, Nat.pos_of_ne_zero (hd i).out⟩ 1) := by
    intro hc
    have := congrArg (fun z => (ULift.down z) ⟨0, Nat.pos_of_ne_zero (hd i).out⟩) hc
    simp only [Pi.single_eq_same] at this
    exact one_ne_zero this.symm
  exact hne (φ.toLinearEquiv.injective (by rw [hall, hall]))

/-- **L1, Artin–Wedderburn form**: a finite-dimensional semisimple `A(𝒱)` carries
`dim A(𝒱)/[A(𝒱),A(𝒱)]` pairwise non-isomorphic simple bundled `A(𝒱)`-modules. -/
theorem exists_pairwise_nonIso_simple_aMod
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W))
    (hss : letI := instRingA W; IsSemisimpleRing (A W)) :
    ∃ (m : ℕ) (U : Fin m → AMod W),
      (letI := instRingA W; letI := instAlgebraA W;
        m = Module.finrank ℂ (A W ⧸ commSpan ℂ (A W))) ∧
      (∀ j, IsSimpleAMod (U j)) ∧
      (∀ i j, i ≠ j → IsEmpty (AModEquiv W (U i) (U j))) := by
  letI := instRingA W
  letI := instAlgebraA W
  haveI := hfd
  haveI := hss
  obtain ⟨m, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (A W)
  exact ⟨m, wedderburnAMod W e,
    (finrank_quot_commSpan_eq_of_algEquiv_pi_matrix hd e).symm,
    isSimpleAMod_wedderburnAMod hd e,
    fun i j hij => wedderburnAMod_isEmpty_amodEquiv hd e hij⟩

end Wedderburn

end VOA
