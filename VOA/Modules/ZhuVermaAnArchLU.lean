/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLUGraded
import VOA.Modules.ZhuVermaAnArchLeaf3

/-!
# C5, layer 2 — `J(U)`, `L(U) = M(U)/J(U)` and its irreducibility for Dong–Jiang's `M(U)`

`ZhuVermaAnArchLUGraded` built, over the finrank-free `GradedLWWeakModule`, the maximal
bottom-trivial graded submodule `maxJ`, the graded quotient `LU`, and the implication

  `GeneratedByBottom N` + `BottomIrreducible N`  ⟹  `LU N` is irreducible.

This file **instantiates that at Dong–Jiang's `M(U) = ⨁ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U`** and discharges
both inputs:

* **`djGeneratedByBottom` — discharged** off the proved `djCarrierWeak_generated_by_bottom`
  (DJ Thm 4.13's generation sentence). Its only input is the independent `BottomProjection`
  assumption, already an argument of the carrier itself.
* **`djBottomIrreducible` — discharged from the simplicity of `U`**, via the new bottom
  equivariance `djCarrierWeak_bottom_equiv_rho` (§3): the bottom identification `M(U)(0) ≅ U`
  intertwines the module zero mode `a₍wt a − 1₎` with the `A_0(𝒱)`-action `ρ([a])`.  This is
  Dong–Jiang's "`M(U)(m)` and `U` are isomorphic **`A_m(V)`-modules**" — not only the
  `ℂ`-linear half.

## Contents

### §1 Simplicity of a bundled `A_m(𝒱)`-module
`AmModSubmodule`, `IsSimpleAmMod` — the level-`m` mirror of `ZhuVermaAnArchLeaf3`'s
`AModSubmodule` / `IsSimpleAMod`.

### §2 The missing bridge `AMod W → AmMod W 0`
`anFullZeroEquiv` (`A_0(𝒱) ≃ A(𝒱)`, off `OnFull_zero_eq_O`), `AMod.toAmModZero`,
`isSimpleAmMod_toAmModZero`.  This closes a gap explicitly recorded as open: the Dong–Jiang
carrier consumes `AmMod W 0` while the Zhu-bijection chain quantifies over `AMod W`, and no
translation existed.

### §3 The bottom is `U` **as an `A_0(𝒱)`-module** (conditional on `BottomProjection`)
`djCarrier_zeroMode_incl`, `djPieceMEquiv_zero_rho`, `djCarrierWeak_bottom_equiv_rho`.

### §4–§5 The two inputs, discharged
`djGeneratedByBottom`, `djBottomIrreducible`.

### §6 `J(U)`, `L(U)`, irreducibility, and `L(U)(0) ≅ U`
`djJ`, `djLU`, `djLU_isIrreducible`, `djLU_bottom_equiv`, `djLU_bottom_equiv_rho`.

## The carried hypotheses (all displayed in every signature)

* `Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))` — the sole remaining explicit
  input of the `(0,0)` gate. Every declaration carrying `Pr` is conditional,
  even when its proof term is `#print axioms`-clean. The project-level witness
  `voaPBWBottomProjection` is supplied from the generic relative-induction field of the theorem
  `VOA.pbw : PBWPrinciple`.
* `hU : Nontrivial U.carrier` and `hsimple : IsSimpleAmMod U` — the `AModScope` scope of Theorem
  5.3.4 (the *unscoped* statements are refuted there by `zeroAMod`).
* `hL0` — the grading scalar `L₀ = h + n` on `M(U)(n)`, i.e. `[ω]` acts on `U` by the single scalar
  `h`.  A datum about `U`, not about `𝒱`; its unscoped `∃ h` form is refuted in
  `ZhuVermaAnArchAModScope` (`not_forall_exists_omegaScalar`).

⚠ **DLM3's own simplicity proof is NOT used.**  DLM3 Lemma 4.8 (and Dong–Jiang Thm 4.16) derive
simplicity of `L(U)` from complete reducibility of `M(U)`, available only for **rational** `V`.
Nothing here uses rationality, complete reducibility, or finite-dimensionality.

## References
Dong–Jiang `math/0601626` Thm 4.13 (generation, `M(U)(m) ≅ U` as `A_m(V)`-modules); DLM3
`q-alg/9612010` §4 (Thm 4.1/4.2 and Lemma 4.8 — the rational argument, deliberately not imported);
Gannon §5.3.2 Thm 5.3.4.  Repo: `ZhuVermaAnArchLUGraded`, `ZhuVermaAnArchDJCarrierWeak`,
`ZhuVermaAnArchDJCarrierGraded` (`DJCarrier.degMEquiv`), `ZhuVermaAnArchDJAction`
(`djMode_apply_incl`, `djPieceAct_mk`, `djPiece_ext`), `ZhuVermaAnArchLeaf3` (`IsSimpleAMod`),
`ZhuVermaAnArchAModScope` (why the scope is genuine).
-/

namespace VOA

open scoped BigOperators TensorProduct DirectSum
open VertexOperatorAlgebra

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1 Simplicity of a bundled `A_m(𝒱)`-module -/

/-- An **`A_m(𝒱)`-submodule** of a bundled `AmMod`: a `ℂ`-subspace closed under every `U.ρ b`.
The level-`m` mirror of `AModSubmodule`. -/
structure AmModSubmodule {W : VertexOperatorAlgebra 𝒱} {m : ℕ} (U : AmMod W m) where
  /-- The underlying `ℂ`-subspace. -/
  carrier : Submodule ℂ U.carrier
  /-- Closure under the action. -/
  ρ_mem : ∀ (b : AnFull W m) {x : U.carrier}, x ∈ carrier → U.ρ b x ∈ carrier

/-- **`IsSimpleAmMod U`** — `U` is nonzero and has no `A_m(𝒱)`-submodule besides `⊥` and `⊤`.
The level-`m` mirror of `IsSimpleAMod`; at `m = 0` this is the codomain predicate `Irr A(𝒱)` of
Theorem 5.3.4. -/
def IsSimpleAmMod {W : VertexOperatorAlgebra 𝒱} {m : ℕ} (U : AmMod W m) : Prop :=
  Nontrivial U.carrier ∧ ∀ S : AmModSubmodule U, S.carrier = ⊥ ∨ S.carrier = ⊤

/-- A simple `A_m(𝒱)`-module is in particular nontrivial. -/
theorem IsSimpleAmMod.nontrivial {W : VertexOperatorAlgebra 𝒱} {m : ℕ} {U : AmMod W m}
    (hs : IsSimpleAmMod U) : Nontrivial U.carrier := hs.1

/-! ## §2 The bridge `AMod W → AmMod W 0` -/

section Bridge

variable (W : VertexOperatorAlgebra 𝒱)

/-- **`A_0(𝒱) ≃ A(𝒱)`** — at level `0` the Frenkel–Zhu ideal `O_0(𝒱)` *is* Zhu's `O(𝒱)`
(`OnFull_zero_eq_O`), so the two quotients agree. -/
noncomputable def anFullZeroEquiv : AnFull W 0 ≃ₗ[ℂ] A W :=
  Submodule.quotEquivOfEq _ _ (OnFull_zero_eq_O W)

@[simp] theorem anFullZeroEquiv_mk (x : 𝒱) :
    anFullZeroEquiv W (mkAnFull W 0 x) = VOA.mk W x := rfl

variable {W}

/-- **The missing translation `AMod W → AmMod W 0`.**  Dong–Jiang's carrier `DJCarrier` consumes
an `AmMod W 0` (action over `A_0(𝒱)`, multiplicative for `leftProd W 0`) while the Zhu-bijection
chain quantifies over `AMod W` (action over `A(𝒱)`, multiplicative for `zhuMul`).  The two agree:
`OnFull W 0 = O(𝒱)` and `leftProd W 0 = zhuMul` (`leftProd_zero`). -/
noncomputable def AMod.toAmModZero (U : AMod W) : AmMod W 0 where
  carrier := U.carrier
  ρ := (U.ρ).comp (anFullZeroEquiv W).toLinearMap
  ρ_one := U.ρ_one
  ρ_mul u v := by
    show U.ρ (VOA.mk W (leftProd W 0 u v))
      = U.ρ (VOA.mk W u) * U.ρ (VOA.mk W v)
    rw [leftProd_zero]
    exact U.ρ_mul u v

@[simp] theorem AMod.toAmModZero_carrier (U : AMod W) : (U.toAmModZero).carrier = U.carrier := rfl

@[simp] theorem AMod.toAmModZero_ρ (U : AMod W) (x : 𝒱) :
    (U.toAmModZero).ρ (mkAnFull W 0 x) = U.ρ (VOA.mk W x) := rfl

/-- Simplicity transports along the bridge. -/
theorem isSimpleAmMod_toAmModZero {U : AMod W} (hs : IsSimpleAMod U) :
    IsSimpleAmMod U.toAmModZero := by
  refine ⟨hs.1, fun S => ?_⟩
  refine hs.2 ⟨S.carrier, ?_⟩
  intro a x hx
  have hb := S.ρ_mem ((anFullZeroEquiv W).symm a) hx
  rwa [show (U.toAmModZero).ρ ((anFullZeroEquiv W).symm a) = U.ρ a from by
    show U.ρ ((anFullZeroEquiv W) ((anFullZeroEquiv W).symm a)) = U.ρ a
    rw [LinearEquiv.apply_symm_apply]] at hb

end Bridge

/-! ## §3 The bottom of `M(U)` is `U` **as an `A_0(𝒱)`-module** -/

section Bottom

open VHat VHat.DLM3

variable {W : VertexOperatorAlgebra 𝒱}

/-- The **module zero mode on the bottom**: for `a ∈ 𝒱ₖ`, `a₍ₖ₋₁₎` maps `M(U)(0)` to `M(U)(0)`, and
does so through the level-piece action `djPieceAct` at `(N, n) = (0, 0)`. -/
theorem djCarrier_zeroMode_incl (U : AmMod W 0) {k : ℤ} {a : 𝒱} (ha : a ∈ W.grading k)
    (y : DJPiece W U 0) :
    djModeZero W U (k - 1) a (DJCarrier.incl W U 0 y)
      = DJCarrier.incl W U 0 (djPieceAct W U 0 0 (djActionDescent_zero W 0 0) a y) := by
  have hN : muTargetLevel k (k - 1) 0 = ((0 : ℕ) : ℤ) := by
    simp only [muTargetLevel, Nat.cast_zero]; ring
  rw [djModeZero, djMode_apply_incl U (djActionDescent_zero W) (k - 1) ha,
    djLevelIncl_eq_of_target U (djActionDescent_zero W) hN a, LinearMap.comp_apply]

/-- **The level-`0` piece identification is `A_0(𝒱)`-equivariant.**  Under
`M(U)(0) ≅ U` the action `djPieceAct … a` becomes `ρ([a])`.  The scalar content is
`anmGen W 0 0 0 = anmRight W 0 0` together with the module axiom `AmMod.ρ_mul_anmRight`. -/
theorem djPieceMEquiv_zero_rho (hann : DJAnnEqAn W 0) (U : AmMod W 0) (a : 𝒱)
    (y : DJPiece W U 0) :
    djPieceMEquiv W 0 hann U (djPieceAct W U 0 0 (djActionDescent_zero W 0 0) a y)
      = U.ρ (mkAnFull W 0 a) (djPieceMEquiv W 0 hann U y) := by
  have hmaps : (djPieceMEquiv W 0 hann U).toLinearMap.comp
        (djPieceAct W U 0 0 (djActionDescent_zero W 0 0) a)
      = (U.ρ (mkAnFull W 0 a)).comp (djPieceMEquiv W 0 hann U).toLinearMap := by
    refine djPiece_ext (fun v w => ?_)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, djPieceAct_mk, djPieceMEquiv_mk]
    rw [anmGen_eq_anmRight, U.ρ_mul_anmRight]
    rfl
  exact congrArg (fun f : DJPiece W U 0 →ₗ[ℂ] U.carrier => f y) hmaps

/-- **`M(U)(0) ≅ U` as `A_0(𝒱)`-modules.**  The proved `ℂ`-linear identification
`djCarrierWeak_bottom_equiv` intertwines the module zero mode `a₍wt a − 1₎` on the bottom with the
`A_0(𝒱)`-action `ρ([a])` on `U`.  This is Dong–Jiang Theorem 4.13's "isomorphic `A_m(V)`-modules";
not only the underlying linear isomorphism.

Carried input: the independent `BottomProjection` assumption `Pr` (it enters only through the
bottom identification); this required `regularAMod` instance is not currently established. -/
theorem djCarrierWeak_bottom_equiv_rho
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) (U : AmMod W 0)
    {k : ℤ} {a : 𝒱} (ha : a ∈ W.grading k) (z : DJCarrier.deg W U 0)
    (hmem : djModeZero W U (k - 1) a (z : DJCarrier W U) ∈ DJCarrier.deg W U 0) :
    djCarrierWeak_bottom_equiv Pr U ⟨djModeZero W U (k - 1) a (z : DJCarrier W U), hmem⟩
      = U.ρ (mkAnFull W 0 a) (djCarrierWeak_bottom_equiv Pr U z) := by
  obtain ⟨z0, hz0⟩ := z
  obtain ⟨y, rfl⟩ := hz0
  have hkey : (⟨djModeZero W U (k - 1) a (DJCarrier.incl W U 0 y), hmem⟩ :
        DJCarrier.deg W U 0)
      = ⟨DJCarrier.incl W U 0 (djPieceAct W U 0 0 (djActionDescent_zero W 0 0) a y),
          ⟨djPieceAct W U 0 0 (djActionDescent_zero W 0 0) a y, rfl⟩⟩ :=
    Subtype.ext (djCarrier_zeroMode_incl U ha y)
  show djCarrierDegZeroEquivOfPbwDatum Pr U _ = _
  rw [hkey]
  show DJCarrier.degMEquiv W 0 (djAnnEqAn_zero_of_pbwDatum Pr) U _
      = U.ρ (mkAnFull W 0 a) (DJCarrier.degMEquiv W 0 (djAnnEqAn_zero_of_pbwDatum Pr) U _)
  rw [DJCarrier.degMEquiv_incl, DJCarrier.degMEquiv_incl]
  exact djPieceMEquiv_zero_rho (djAnnEqAn_zero_of_pbwDatum Pr) U a y

end Bottom

/-! ## §4 `GeneratedByBottom`, discharged -/

section Inputs

open VHat VHat.DLM3 GradedLWWeakModule

variable {W : VertexOperatorAlgebra 𝒱}

/-- **DJ Theorem 4.13's generation sentence in the abstract form `GeneratedByBottom`.**  A weak
submodule of `M(U)` containing the bottom weight space is everything. Carried input: the
independent `BottomProjection` assumption `Pr` (already an argument of the carrier). -/
theorem djGeneratedByBottom
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) (U : AmMod W 0)
    (hU : Nontrivial U.carrier) (h : ℂ)
    (hL0 : ∀ (n : ℕ) (x : DJCarrier W U), x ∈ DJCarrier.deg W U n →
      djModeZero W U 1 W.conformalVector x = (h + n) • x) :
    GeneratedByBottom (djGradedLW_of_pbwDatum Pr U hU h hL0) := by
  intro Q hQ
  refine djCarrierWeak_generated_by_bottom Pr U Q (fun w => ?_)
  refine hQ ?_
  show _ ∈ djCWeight W U h h
  rw [djCWeight_zero]
  exact Subtype.coe_prop _

/-- **`BottomIrreducible` from the simplicity of `U`.**  A nonzero subspace of the bottom `M(U)(0)`
that is stable under every mode keeping it inside the bottom transports, through the
`A_0(𝒱)`-equivariant identification `M(U)(0) ≅ U` of §3, to a nonzero `A_0(𝒱)`-submodule of `U`;
simplicity of `U` forces it to be everything.

Carried inputs: the independent `BottomProjection` assumption `Pr`, the scope
`hsimple : IsSimpleAmMod U`, and `hL0`. -/
theorem djBottomIrreducible
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) (U : AmMod W 0)
    (hU : Nontrivial U.carrier) (h : ℂ)
    (hL0 : ∀ (n : ℕ) (x : DJCarrier W U), x ∈ DJCarrier.deg W U n →
      djModeZero W U 1 W.conformalVector x = (h + n) • x)
    (hsimple : IsSimpleAmMod U) :
    BottomIrreducible (djGradedLW_of_pbwDatum Pr U hU h hL0) := by
  classical
  intro S hSle hS0 hstab
  -- The bottom weight space *is* the level-`0` piece, and the abstract action is `djModeZero`.
  have hw : (djGradedLW_of_pbwDatum Pr U hU h hL0).weight h = DJCarrier.deg W U 0 :=
    djCWeight_zero U h
  have hact : ∀ (a : 𝒱) (p : ℤ) (x : DJCarrier W U),
      (djGradedLW_of_pbwDatum Pr U hU h hL0).toWeakModule.act a p x = djModeZero W U p a x :=
    fun a p x => djCarrierWeak_act W U a p x
  simp only [hact, hw] at hstab
  rw [hw] at hSle ⊢
  -- Transport `S` to a subspace of `U`.
  set T : Submodule ℂ U.carrier :=
    Submodule.map (djCarrierWeak_bottom_equiv Pr U).toLinearMap
      (Submodule.comap (DJCarrier.deg W U 0).subtype S) with hT
  have hmemT : ∀ (z : DJCarrier.deg W U 0), (z : DJCarrier W U) ∈ S →
      djCarrierWeak_bottom_equiv Pr U z ∈ T := by
    intro z hz
    exact ⟨z, hz, rfl⟩
  -- `T` is `A_0(𝒱)`-stable.
  have hstabHom : ∀ (k : ℤ) (a : 𝒱), a ∈ W.grading k →
      ∀ x ∈ T, U.ρ (mkAnFull W 0 a) x ∈ T := by
    intro k a ha x hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hzS : (z : DJCarrier W U) ∈ S := hz
    have hmem : djModeZero W U (k - 1) a (z : DJCarrier W U) ∈ DJCarrier.deg W U 0 := by
      have hN : muTargetLevel k (k - 1) 0 = ((0 : ℕ) : ℤ) := by
        simp only [muTargetLevel, Nat.cast_zero]; ring
      have hm := djCarrierWeak_act_deg_mem (W := W) U ha hN (x := (z : DJCarrier W U)) z.2
      rwa [djCarrierWeak_act] at hm
    have hin : djModeZero W U (k - 1) a (z : DJCarrier W U) ∈ S :=
      hstab a (k - 1) _ hzS hmem
    have hEq := djCarrierWeak_bottom_equiv_rho Pr U ha z hmem
    have hgoal := hmemT ⟨djModeZero W U (k - 1) a (z : DJCarrier W U), hmem⟩ hin
    rw [hEq] at hgoal
    exact hgoal
  have hstabAll : ∀ (b : AnFull W 0) {x : U.carrier}, x ∈ T → U.ρ b x ∈ T := by
    intro b x hx
    refine Submodule.Quotient.induction_on (OnFull W 0) b (fun c => ?_)
    show U.ρ (mkAnFull W 0 c) x ∈ T
    refine reduce_homogeneous (W := W)
      (P := fun c => U.ρ (mkAnFull W 0 c) x ∈ T) ?_ ?_ ?_ c
    · intro k a ha; exact hstabHom k a ha x hx
    · simp only [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
    · intro y₁ y₂ h₁ h₂
      simp only [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ h₁ h₂
  -- `T ≠ ⊥`.
  have hTne : T ≠ ⊥ := by
    rw [Submodule.ne_bot_iff] at hS0 ⊢
    obtain ⟨x, hxS, hx0⟩ := hS0
    refine ⟨djCarrierWeak_bottom_equiv Pr U ⟨x, hSle hxS⟩, hmemT ⟨x, hSle hxS⟩ hxS,
      fun hcontra => hx0 ?_⟩
    have hz0 : (⟨x, hSle hxS⟩ : DJCarrier.deg W U 0) = 0 :=
      (djCarrierWeak_bottom_equiv Pr U).injective (by rw [hcontra, map_zero])
    exact congrArg Subtype.val hz0
  -- Simplicity of `U` forces `T = ⊤`.
  have hTtop : T = ⊤ := (hsimple.2 ⟨T, hstabAll⟩).resolve_left hTne
  -- Pull `T = ⊤` back to `S = M(U)(0)`.
  refine le_antisymm hSle (fun y hy => ?_)
  have hy' : djCarrierWeak_bottom_equiv Pr U ⟨y, hy⟩ ∈ T := by rw [hTtop]; exact Submodule.mem_top
  obtain ⟨z, hz, hze⟩ := hy'
  have hzy : z = (⟨y, hy⟩ : DJCarrier.deg W U 0) :=
    (djCarrierWeak_bottom_equiv Pr U).injective hze
  have hzS : (z : DJCarrier W U) ∈ S := hz
  rwa [hzy] at hzS

end Inputs

/-! ## §5 `J(U)`, `L(U)`, irreducibility, and the bottom -/

section LU

open VHat VHat.DLM3 GradedLWWeakModule

variable {W : VertexOperatorAlgebra 𝒱}
variable (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) (U : AmMod W 0)
  (hU : Nontrivial U.carrier) (h : ℂ)
  (hL0 : ∀ (n : ℕ) (x : DJCarrier W U), x ∈ DJCarrier.deg W U n →
    djModeZero W U 1 W.conformalVector x = (h + n) • x)

/-- **`J(U)`** — the maximal graded submodule of `M(U)` meeting the bottom `M(U)(0)` trivially.
Conditional on the data already carried by the graded packaging of `M(U)`, including the
independent `BottomProjection` assumption `Pr`. -/
noncomputable def djJ : WeakModule.Submodule' (djCarrierWeak W U) :=
  maxJ (djGradedLW_of_pbwDatum Pr U hU h hL0)

/-- `J(U)` meets the bottom trivially (a THEOREM — see `maxJ_bottom_disjoint`). -/
theorem djJ_bottom_disjoint :
    (djJ Pr U hU h hL0).carrier ⊓ DJCarrier.deg W U 0 = ⊥ := by
  have hw : (djGradedLW_of_pbwDatum Pr U hU h hL0).weight h = DJCarrier.deg W U 0 :=
    djCWeight_zero U h
  have := maxJ_bottom_disjoint (djGradedLW_of_pbwDatum Pr U hU h hL0)
  rwa [hw] at this

/-- **`L(U) = M(U)/J(U)`** as a `ℂ`-graded lowest-weight weak module at the same lowest weight
`h`.  Its bottom is still `M(U)(0) ≅ U`. -/
noncomputable def djLU :
    GradedLWWeakModule W (DJCarrier W U ⧸ (djJ Pr U hU h hL0).carrier) h :=
  LU (djGradedLW_of_pbwDatum Pr U hU h hL0)

/-- The action on `L(U)` is Dong–Jiang's mode, pushed through the projection. -/
@[simp] theorem djLU_act_mk (a : 𝒱) (p : ℤ) (x : DJCarrier W U) :
    (djLU Pr U hU h hL0).toWeakModule.act a p (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (djModeZero W U p a x) := by
  refine Eq.trans (LU_act_mk (djGradedLW_of_pbwDatum Pr U hU h hL0) a p x) ?_
  exact congrArg Submodule.Quotient.mk (djCarrierWeak_act W U a p x)

/-- **`L(U)` IS IRREDUCIBLE.**  Every weak submodule of `L(U)` is `⊥` or `⊤`.

Carried inputs, all displayed: the independent `BottomProjection` assumption `Pr`, the scope
`hU`/`hsimple` (`U` a *simple*
`A_0(𝒱)`-module) and the grading scalar `hL0`.  Generation-from-the-bottom is discharged, not
carried.

⚠ Proved by the maximal-graded-proper-submodule route.  DLM3's own Lemma 4.8 argument (complete
reducibility of `M(U)`) is valid only for rational `V` and is **not** used. -/
theorem djLU_isIrreducible (hsimple : IsSimpleAmMod U) :
    IsIrreducible (djLU Pr U hU h hL0) :=
  LU_isIrreducible (djGeneratedByBottom Pr U hU h hL0) (djBottomIrreducible Pr U hU h hL0 hsimple)

/-- **`L(U)`'s bottom weight space is `M(U)`'s bottom weight space** (`J(U)` meets it trivially). -/
noncomputable def djLU_bottom_equiv :
    (djGradedLW_of_pbwDatum Pr U hU h hL0).weight h ≃ₗ[ℂ] (djLU Pr U hU h hL0).weight h :=
  LU_bottom_equiv (djGradedLW_of_pbwDatum Pr U hU h hL0)

/-- **`L(U)(0) ≅ U`** — the composite `L(U)_h ≅ M(U)(0) ≅ U`.  This is the round-trip statement
"`forwardMap [L(U)] = [U]`" at the level of the underlying `A_0(𝒱)`-modules; the `A_0(𝒱)`-linearity
of the second factor is `djCarrierWeak_bottom_equiv_rho` (§3). -/
noncomputable def djLU_bottom_U : (djLU Pr U hU h hL0).weight h ≃ₗ[ℂ] U.carrier :=
  ((djLU_bottom_equiv Pr U hU h hL0).symm).trans
    ((LinearEquiv.ofEq _ _ (djCWeight_zero U h)).trans (djCarrierWeak_bottom_equiv Pr U))

/-- The composite `L(U)_h ≅ U`, computed on the class of a bottom vector of `M(U)`. -/
theorem djLU_bottom_U_apply (y : (djLU Pr U hU h hL0).weight h)
    (z : DJCarrier W U) (hz : z ∈ DJCarrier.deg W U 0)
    (hy : (y : DJCarrier W U ⧸ (djJ Pr U hU h hL0).carrier) = Submodule.Quotient.mk z) :
    djLU_bottom_U Pr U hU h hL0 y = djCarrierWeak_bottom_equiv Pr U ⟨z, hz⟩ := by
  have hzw : z ∈ (djGradedLW_of_pbwDatum Pr U hU h hL0).weight h := by
    rw [show (djGradedLW_of_pbwDatum Pr U hU h hL0).weight h = DJCarrier.deg W U 0 from
      djCWeight_zero U h]
    exact hz
  have hsymm : (djLU_bottom_equiv Pr U hU h hL0).symm y = ⟨z, hzw⟩ :=
    LU_bottom_equiv_symm_eq (djGradedLW_of_pbwDatum Pr U hU h hL0) ⟨z, hzw⟩ y hy
  rw [djLU_bottom_U]
  simp only [LinearEquiv.trans_apply, hsymm]
  rfl

/-- **`L(U)(0) ≅ U` AS `A₀(𝒱)`-MODULES** — the round trip `forwardMap [L(U)] = [U]` at the level
of the underlying bundled `A₀(𝒱)`-modules.  The equivalence `djLU_bottom_U` intertwines the module
zero mode `a₍wt a − 1₎` on the bottom of `L(U)` with `ρ([a])` on `U`.

Carried inputs: the independent `BottomProjection` assumption `Pr`, `hU`, `hL0` — exactly those of
the carrier itself. (Simplicity
of `U` is *not* needed for this statement; it is needed only for irreducibility of `L(U)`.) -/
theorem djLU_bottom_U_rho {k : ℤ} {a : 𝒱} (ha : a ∈ W.grading k)
    (y : (djLU Pr U hU h hL0).weight h)
    (hmem : (djLU Pr U hU h hL0).toWeakModule.act a (k - 1)
        (y : DJCarrier W U ⧸ (djJ Pr U hU h hL0).carrier) ∈ (djLU Pr U hU h hL0).weight h) :
    djLU_bottom_U Pr U hU h hL0
        ⟨(djLU Pr U hU h hL0).toWeakModule.act a (k - 1) (y : _), hmem⟩
      = U.ρ (mkAnFull W 0 a) (djLU_bottom_U Pr U hU h hL0 y) := by
  -- Name the bottom vector of `M(U)` whose class is `y`.
  set N := djGradedLW_of_pbwDatum Pr U hU h hL0 with hN
  set z : N.weight h := (djLU_bottom_equiv Pr U hU h hL0).symm y with hz
  have hydec : (y : DJCarrier W U ⧸ (djJ Pr U hU h hL0).carrier)
      = Submodule.Quotient.mk ((z : DJCarrier W U)) :=
    LU_bottom_equiv_symm_coe N y
  have hzdeg : (z : DJCarrier W U) ∈ DJCarrier.deg W U 0 := by
    have hw : N.weight h = DJCarrier.deg W U 0 := djCWeight_zero U h
    rw [← hw]; exact z.2
  -- The mode of `y` is the class of the mode of `z`.
  have hact : (djLU Pr U hU h hL0).toWeakModule.act a (k - 1) (y : _)
      = Submodule.Quotient.mk (djModeZero W U (k - 1) a (z : DJCarrier W U)) := by
    rw [hydec, djLU_act_mk]
  have hmemdeg : djModeZero W U (k - 1) a (z : DJCarrier W U) ∈ DJCarrier.deg W U 0 := by
    have hNlev : muTargetLevel k (k - 1) 0 = ((0 : ℕ) : ℤ) := by
      simp only [muTargetLevel, Nat.cast_zero]; ring
    have hm := djCarrierWeak_act_deg_mem (W := W) U ha hNlev
      (x := (z : DJCarrier W U)) hzdeg
    rwa [djCarrierWeak_act] at hm
  rw [djLU_bottom_U_apply Pr U hU h hL0 _ _ hmemdeg hact,
    djLU_bottom_U_apply Pr U hU h hL0 y _ hzdeg hydec]
  exact djCarrierWeak_bottom_equiv_rho Pr U ha ⟨(z : DJCarrier W U), hzdeg⟩ hmemdeg

/-! ### The other bijection direction, and exactly what is still missing

`eq_maxJ_of_maximal` (`ZhuVermaAnArchLUGraded`) is the abstract half of "every irreducible
lowest-weight module `P` is `L(P_h)`": if `K` is a weak submodule of `M(U)` meeting the bottom
trivially and maximal among proper weak submodules — precisely what the kernel of a
bottom-injective surjection onto an irreducible module is — then `K = J(U)`, hence `M(U)/K = L(U)`.
`djJ_unique` below is that statement for Dong–Jiang's carrier.

⚠ **The remaining input is the UNIVERSAL PROPERTY of `M(U)`** (Dong–Jiang Theorem 4.13's second
half): for a weak module `P` and an `A₀(𝒱)`-morphism `φ : U → Ω(P)`, a weak-module map
`φ̄ : M(U) → P` extending `φ`.  It is **not** built here, and nothing is asserted about it.  Its
exact status in this repo:

* Dong–Jiang's computation `φ̄(u₍ₚ₎(v ⊗ w)) = o_{N,0}(u ∗^N_{0,n} v)φ(w)`
  `= o_{N,n}(u) o_{n,0}(v)φ(w)` is DJ Lemma 4.1 at general indices, together with
  DJ Corollary 4.2 for well-definedness against
  the balancing relation.  **Both are already THEOREMS**: `djCompositionLev_holds`,
  `oLevW_anmGen_law_lev`, `oLevW_anmRight_law_lev` (`ZhuVermaAnArchGateB1Ann`).  (⚠ `PHASE4_PLAN`
  C-10 still records general DJ Lemma 4.1 as unproved; that entry is **stale** — C-9's B1Ann
  discharged it, axiom-clean.)
* What is *not* proved is the descent of `o_{n,0}` through the ideal at the off-diagonal indices:
  `x ∈ OnmFull W n 0 ⟹ o_{n,0}(x)` kills the bottom.  `GateAnnihilationLev`
  (`gateAnnihilationLev_holds`) is exactly this at `(n, m) = (0, 0)`; its `Onm`-summand is general
  (`OnmW_annihilates_lev`), but the `OnmAssoc` / `OnmLevel` summands are assembled only at `(0,0)`
  (`oLevW_assocDefect_vanish`, `oLevW_levelMix_vanish`).  Those two proofs consume only `hdj`,
  which is a theorem, so the `(n, 0)` versions look reachable — NOT ESTABLISHED, not attempted
  here. -/

/-- **`J(U)` is THE bottom-trivial maximal submodule.**  Instantiation of `eq_maxJ_of_maximal`:
a weak submodule `K ⊆ M(U)` missing the bottom and maximal among proper weak submodules equals
`J(U)`, so `M(U)/K = L(U)`. Conditional on the data of the carrier, including `Pr`. -/
theorem djJ_unique (K : WeakModule.Submodule' (djCarrierWeak W U))
    (hK : K.carrier ⊓ DJCarrier.deg W U 0 = ⊥)
    (hmax : ∀ Q : WeakModule.Submodule' (djCarrierWeak W U), K.carrier ≤ Q.carrier →
      Q.carrier = K.carrier ∨ Q.carrier = ⊤) :
    K.carrier = (djJ Pr U hU h hL0).carrier := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition
    (djGradedLW_of_pbwDatum Pr U hU h hL0).weight
    (djGradedLW_of_pbwDatum Pr U hU h hL0).isInternal
  refine eq_maxJ_of_maximal (djGradedLW_of_pbwDatum Pr U hU h hL0) K ?_ hmax
  rwa [show (djGradedLW_of_pbwDatum Pr U hU h hL0).weight h = DJCarrier.deg W U 0 from
    djCWeight_zero U h]

end LU

end VOA
