/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VOA
import VOA.Core.ReconstructionExistence

/-!
# The basis-free vertex map `YA` of the affine `𝔰𝔩₂` VOA, via the reconstruction theorem

## Status
The affine instantiation of the reconstruction theorem — the `DCovariant` liftings,
`wordStateA_span`, and the conditional `affineYA_of_currentCov` — proved axiom-clean (`pbw`-free).
The gate `hJ` (`SugawaraCov.Jfield_DCovariant`) is discharged downstream, yielding the unconditional
`AffineSl2Assembly.YA` and the closed `affineSl2VOA_closed`.

This file applies the `Core` operator-first reconstruction theorem
(`VOA.Reconstruction.reconstruct`) to the cyclic module `WakModule k = U(ĝ)⧸J(k)`,
building the all-states vertex map `YA` basis-free from the generating word fields `YwordA`
(STEP 1 locality `YwordA_local` + STEP 2 creation tower `YwordA_vacuum_base/_neg` are in
`Examples.AffineSl2VOA`).

The reconstruction needs a **translation operator** `T` with `T |0⟩ = 0` and the field
covariance `[T, Jᵃ(z)] = ∂_z Jᵃ(z)` (i.e. `[T, Jᵃ_m] = -m Jᵃ_{m-1}`).  We take the Sugawara
`T = L₋₁ = mode (sugawaraField k) 0` (`Ltrans`).  `Ltrans |0⟩ = 0` is immediate (the
normal-ordered Sugawara modes annihilate the vacuum below degree `0`).  The current-covariance
input — the **Sugawara current covariance** `DCovariant (Ltrans k) (Jfield k a)` — is the affine
energy–momentum identity (discharged downstream as `SugawaraCov.Jfield_DCovariant`); once supplied
it lifts through `nprod`/`deriv` (the `Core` `DCovariant` closure) to every word field, and
`reconstruct` then yields `YA` and the basis-free VA axioms (VA3 creation, VA4 locality, VA5
regularity, translation covariance).

## Provenance
STEP 1–2 (locality, creation tower) and the `Core` reconstruction theorem are complete.
`Ltrans_vacuum` (`T|0⟩=0`) and the word-state spanning `wordStateA_span` are proved here; the
`DCovariant` lifting feeds the conditional `affineYA_of_currentCov`, whose Sugawara
current-covariance input `hJ` is discharged downstream by `SugawaraCov.Jfield_DCovariant`
(unconditional at `k+2≠0`).
-/

namespace VOA.AffineVOA

open scoped BigOperators
open Module (End)
open VOA.AffineLie

universe u

/-! ## §1  The Sugawara translation operator `T = L₋₁` and `T|0⟩ = 0` -/

/-- The Sugawara translation operator `T = L₋₁ = mode (sugawaraField k) 0` on `WakModule k`. -/
noncomputable def Ltrans (k : ℂ) : End ℂ (WakModule k) := Lsug k (-1)

/-- `Ltrans` is the constant term of the Sugawara field: `L₋₁ = T(z)|_{z⁰} = (sugawaraField)₍₋₁₎`. -/
theorem Ltrans_eq (k : ℂ) : Ltrans k = (sugawaraField k) (-1) := by
  rw [Ltrans, Lsug_def, mode_apply]
  norm_num

/-- **`L₋₁` annihilates the vacuum** (`T|0⟩ = 0`): each normal-ordered Sugawara mode
`:JᵃJᵇ:₍₋₁₎` kills `|0⟩` (degree `-1 < 0`), so the whole Sugawara constant term does. -/
theorem Ltrans_vacuum (k : ℂ) : Ltrans k (vacuumA k) = 0 := by
  have hz : ∀ a b : Fin 3,
      nprod (Jfield_isField k a) (Jfield_isField k b) (-1) (vacuumA k) = 0 := by
    intro a b
    exact nprod_vacuum_neg_gen (Jfield_isField k a) (Jfield_isField k b) (vacuumA k)
      (fun q hq => Jfield_vacuum_neg k a hq) (fun q hq => Jfield_vacuum_neg k b hq) (by norm_num)
  rw [Ltrans_eq, sugawaraField]
  show (2 * (k + dualCoxeter))⁻¹ • (Reconstruction.evalAt (-1) (vacuumA k)
      (∑ a : Fin 3, ∑ b : Fin 3,
        kappaInv a b • nprod (Jfield_isField k a) (Jfield_isField k b))) = 0
  refine smul_eq_zero_of_right _ ?_
  rw [map_sum]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  rw [map_sum]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  rw [map_smul]
  show kappaInv a b • (nprod (Jfield_isField k a) (Jfield_isField k b) (-1) (vacuumA k)) = 0
  rw [hz a b, smul_zero]

/-! ## §2  Lifting the Sugawara current covariance to every word field

GIVEN the Sugawara current covariance `DCovariant (Ltrans k) (Jfield k a)` (the affine
energy–momentum identity `[L₋₁, Jᵃ_m] = -m Jᵃ_{m-1}`), the `Core` `DCovariant` closure under
scaling/derivative/`nprod` lifts it to the generator fields `genFieldA` and then to every
iterated word field `YwordA` — supplying `reconstruct`'s `hTcov` input. -/

/-- The identity field is `T`-covariant for any `T` (`[T, 1_m] = 0 = ∂_z 1`). -/
theorem idFieldA_DCovariant (k : ℂ) : Reconstruction.DCovariant (Ltrans k) (idFieldA k) := by
  have e : ∀ j : ℤ, idFieldA k j = if j = 0 then (1 : End ℂ (WakModule k)) else 0 :=
    fun j => rfl
  intro m
  show Ltrans k * (idFieldA k m) - (idFieldA k m) * Ltrans k = ((m + 1 : ℤ)) • (idFieldA k (m + 1))
  rw [e m, e (m + 1)]
  split_ifs with h0 h1 h1
  · omega
  · simp
  · rw [show (m + 1 : ℤ) = 0 from h1]; simp
  · simp

/-- The generator fields `genFieldA = (i!)⁻¹ ∂_z^i Jᵃ(z)` inherit `T`-covariance from `Jᵃ(z)`. -/
theorem genFieldA_DCovariant (k : ℂ)
    (hJ : ∀ a : Fin 3, Reconstruction.DCovariant (Ltrans k) (Jfield k a)) (a : Fin 3) (i : ℕ) :
    Reconstruction.DCovariant (Ltrans k) (genFieldA k a i) := by
  rw [genFieldA]
  exact Reconstruction.DCovariant.smul ((i.factorial : ℂ)⁻¹)
    (Reconstruction.DCovariant.deriv_iterate (hJ a) i)

/-- Every iterated word field `YwordA k l` is `T`-covariant (induction over the word, the
`Core` `DCovariant.nprod` closure for the step, `idFieldA_DCovariant` for the base). -/
theorem YwordA_DCovariant (k : ℂ)
    (hJ : ∀ a : Fin 3, Reconstruction.DCovariant (Ltrans k) (Jfield k a)) :
    ∀ l : List (Fin 3 × ℕ), Reconstruction.DCovariant (Ltrans k) (YwordA k l)
  | [] => by rw [YwordA_nil]; exact idFieldA_DCovariant k
  | (ai :: rest) => by
      rw [YwordA_cons]
      exact Reconstruction.DCovariant.nprod (genFieldA_isField k ai.1 ai.2)
        (YwordA_isField k rest) (genFieldA_DCovariant k hJ ai.1 ai.2)
        (YwordA_DCovariant k hJ rest)

/-! ## §3  The word states span `WakModule k` (`hspan` for the reconstruction)

The creation monomials `negWord` span `WakModule k` (`negSpan_eq_top`); each is a `ℂ`-combination
of the basis-word states `wordStateA` (Chevalley-basis decomposition of each loop generator),
so the `wordStateA l` span — the cyclicity datum the reconstruction consumes. -/

/-- Chevalley-basis decomposition: `x = ∑_c x_c·eₐ`. -/
theorem basis_decomp (x : Sl2) : x = ∑ c : Fin 3, x c • basis c := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, basis, smul_eq_mul]
  rw [Finset.sum_eq_single j (fun c _ hc => by rw [Pi.single_eq_of_ne (Ne.symm hc), mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one]

/-- Each current mode `Jᵃ_{-n-1}` maps `span(range wordStateA)` into itself (a word state maps
to a longer word state). -/
theorem J_mem_span_wordState (k : ℂ) (a : Fin 3) (n : ℕ) {y : WakModule k}
    (hy : y ∈ Submodule.span ℂ (Set.range (wordStateA k))) :
    J k a (-(n : ℤ) - 1) y ∈ Submodule.span ℂ (Set.range (wordStateA k)) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, rfl⟩ := hz
      exact Submodule.subset_span ⟨(a, n) :: l, wordStateA_cons k (a, n) l⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add p q _ _ ihp ihq => rw [map_add]; exact Submodule.add_mem _ ihp ihq
  | smul c p _ ihp => rw [map_smul]; exact Submodule.smul_mem _ c ihp

/-- Every creation monomial `negWord L` lies in `span(range wordStateA)` (induction over the
word, basis-decomposing each loop generator). -/
theorem negWord_mem_span (k : ℂ) (L : List (Sl2 × ℕ)) :
    negWord kappaForm kappaForm_isInvariant k L ∈
      Submodule.span ℂ (Set.range (wordStateA k)) := by
  induction L with
  | nil => rw [negWord_nil]; exact Submodule.subset_span ⟨[], rfl⟩
  | cons xn L' ih =>
      obtain ⟨x, n⟩ := xn
      rw [negWord_cons]
      have heq : vacuumRho kappaForm kappaForm_isInvariant k
            (ofLoop kappaForm kappaForm_isInvariant x (-(n : ℤ) - 1))
            (negWord kappaForm kappaForm_isInvariant k L')
          = ∑ c : Fin 3, x c • (J k c (-(n : ℤ) - 1)
              (negWord kappaForm kappaForm_isInvariant k L')) := by
        rw [← loopMul_apply]
        conv_lhs => rw [basis_decomp x]
        rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [map_smul, LinearMap.smul_apply]
        rfl
      rw [heq]
      exact Submodule.sum_mem _ (fun c _ =>
        Submodule.smul_mem _ _ (J_mem_span_wordState k c n ih))

/-- **The word states span** `WakModule k` (`hspan`): `span(range wordStateA) = ⊤`. -/
theorem wordStateA_span (k : ℂ) : Submodule.span ℂ (Set.range (wordStateA k)) = ⊤ := by
  rw [eq_top_iff, ← negSpan_eq_top kappaForm kappaForm_isInvariant k, negSpan, Submodule.span_le]
  rintro _ ⟨L, rfl⟩
  exact negWord_mem_span k L

/-! ## §4  The basis-free vertex map `YA`, conditional on the Sugawara current covariance

GIVEN the Sugawara current covariance `hJ : ∀ a, DCovariant (Ltrans k) (Jfield k a)` (the affine
energy–momentum identity `[L₋₁, Jᵃ_m] = -m Jᵃ_{m-1}`), the `Core` reconstruction theorem produces
the basis-free all-states vertex map `YA` and its VA3 creation, VA4 locality, VA5 regularity, and
translation covariance — `YA |0⟩` data ready for the `affineSl2VOA` shell.  This isolates the
remaining affine obligation to `hJ` (and the conformal VA1/Virasoro/L₀ inputs handled in the
shell). -/

/-- **The basis-free affine `YA`** from the reconstruction theorem (gated on the Sugawara current
covariance `hJ`).  Yields `YA (wordStateA l) = YwordA l`, `IsField`, mutual locality, the VA3
creation tower, and translation covariance. -/
theorem affineYA_of_currentCov (k : ℂ)
    (hJ : ∀ a : Fin 3, Reconstruction.DCovariant (Ltrans k) (Jfield k a)) :
    ∃ YA : WakModule k →ₗ[ℂ] FormalDist (End ℂ (WakModule k)),
      (∀ l : List (Fin 3 × ℕ), YA (wordStateA k l) = YwordA k l) ∧
      (∀ u : WakModule k, IsField (YA u)) ∧
      (∀ u v : WakModule k, Local (YA u) (YA v)) ∧
      (∀ u : WakModule k, (YA u) 0 (vacuumA k) = u) ∧
      (∀ u : WakModule k, ∀ q : ℤ, q < 0 → (YA u) q (vacuumA k) = 0) ∧
      (∀ u : WakModule k, Reconstruction.DCovariant (Ltrans k) (YA u)) :=
  Reconstruction.reconstruct (vacuumA k) (wordStateA k) (YwordA k) (Ltrans k)
    (wordStateA_span k) (YwordA_isField k) (YwordA_local k)
    (fun l => YwordA_vacuum_base k l) (fun l q hq => YwordA_vacuum_neg k l hq)
    (Ltrans_vacuum k) (YwordA_DCovariant k hJ)

end VOA.AffineVOA
