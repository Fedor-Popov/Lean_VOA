/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2Virasoro
import VOA.Examples.AffineSl2Singular
import VOA.Core.SingularVector

/-!
# The affine `𝔰𝔩₂` VOA instance: structure bridges, non-degeneracy, and the level `k = -4/3`

`Examples/AffineSl2Virasoro` closes `affineSl2VOA_closed k hk : VertexOperatorAlgebra
(WakModule k)` for every non-critical level `k + 2 ≠ 0`.  This file does three things that the
construction files deliberately do not:

1. **Bridges.** It records the (definitional) identifications of every `VertexOperatorAlgebra`
   field of `affineSl2VOA_closed k hk` with its concrete affine counterpart, so that downstream
   statements phrased in VOA language (`W.Y`, `W.smul`, `W.L`, `W.grading`) can be discharged by
   the affine lemmas without unfolding the shell.
2. **Non-degeneracy.**  A `PreVertexAlgebra` instance is worthless if its vertex map is degenerate —
   every VOA axiom is satisfied by the zero module, and a map `Y` that collapses states would
   satisfy several of them vacuously.  §B proves that `YA k hk` is **injective**, that it sends
   the vacuum to the *unit* field `1` and each current state `Jᵃ₋₁|0⟩` to the *current* field
   `Jᵃ(z)`, and that `Y(u,z) = 0 ↔ u = 0`.
3. **The admissible level `k = -4/3`.**  §C instantiates the VOA there, computes its central
   charge (`c = -6`), and places the weight-3 singular vector `Sl2Sing.sl2Singular` of
   `Examples/AffineSl2Singular` inside it — as a vector of `voaSl2Adm.grading 3` annihilated by
   every non-weight-raising mode of every *current* field, and by `Lₙ` for `n ≥ 4`.

## Main results

* `YA_injective` — the affine vertex map is injective; `YA_eq_zero_iff`, `Y_ne_zero`.
* `Y_vacuum_eq_one` / `Y_currentState_eq_Jfield` — the two anti-degeneracy sanity checks, in
  VOA language: `Y(|0⟩,z) = 1` and `Y(Jᵃ₋₁|0⟩, z) = Jᵃ(z)`; `smul_currentState_eq_J` turns the
  latter into `(Jᵃ₋₁|0⟩)₍ₙ₎ = Jᵃₙ` as operators.
* `smul_currentState_comm` — the affine Kac–Moody relations of `𝔰𝔩₂^` at level `k`, including
  the central term, hold between VOA modes; the structural proof that `Y` did not collapse.
* `voaSl2Adm : VertexOperatorAlgebra (WakModule (-4/3 : ℂ))` and
  `voaSl2Adm_centralCharge : voaSl2Adm.centralCharge = -6`.
* `sl2Singular_smul_currentState` — every mode `n ≥ 1` of every current field annihilates the
  singular vector, i.e. the `m = 1` case of `SingVec.IsStronglySingularOfWeight.annihilated`.
* `sl2Singular_mem_grading`, `sl2Singular_L0`, `sl2Singular_L_of_four_le`.
* `sl2Singular_isSingularOfWeight_of` — `s` is a `SingVec.IsSingularOfWeight voaSl2Adm 3` vector
  as soon as four explicitly named finite facts hold: `s ≠ 0` and `L₁s = L₂s = L₃s = 0`.

## Status

Everything here is `sorry`-free.  No new axiom is introduced.  Exactly **two** declarations in
this file use `VOA.pbw` — `closed_vacuum_ne_zero`
and its
specialisation `voaSl2Adm_vacuum_ne_zero`, both of which are `vacuumA_ne_zero` verbatim.  Every
other declaration, including the whole VOA instance and all of §A/§B, is
`pbw`-free.  Since `VOA.pbw` is a theorem, all of them are `[propext, Classical.choice,
Quot.sound]`.
See §D.

⚠ **What is NOT claimed in this file.**  `SingVec.IsSingularOfWeight voaSl2Adm 3 sl2Singular` is
not stated unconditionally here; `sl2Singular_isSingularOfWeight_of` takes the inputs as
hypotheses.  Both inputs are available elsewhere in the library:

* `sl2Singular ≠ 0` is `Wak.sl2Singular_ne_zero` (`Examples.WakimotoFree`, `pbw`-free);
* for `Lₙ s = 0`, `n = 1, 2, 3`, the general Sugawara commutator `⁅Lₙ, Jᶜ_μ⁆ = -μ Jᶜ_{n+μ}` is
  `AffineVOA.Vir.Lcomm_J` (`Examples.AffineSl2Virasoro`).  The three instances are not stated
  as separate theorems; the downstream consequence `s ∈ maxGradedIdeal` is
  `LQ43.sl2Singular_mem_maxGradedIdeal` (`Examples.AffineSl2Rigidity43`).

## References
* Gannon §5.1.3, §5.2.2; Kac §12; Arakawa–Kawasetsu; Linshaw–Qi (arXiv:2601.12017).
-/

namespace VOA.AffineVOA.Inst

open VOA
open VOA.AffineVOA
open VOA.AffineLie
open Module (End)

universe u

/-! ## §A  The structure bridges

Every field of `affineSl2VOA_closed k hk` is *definitionally* its affine counterpart (the shell
`affineSl2VOA` sets `grading := gradingZA k`, `Y := YA`, `vacuum := vacuumA k`,
`conformalVector := omegaA k`).  Recording that as named `rfl` lemmas means no downstream proof
has to unfold the shell. -/

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- The VOA's vertex map is the reconstructed affine vertex map `YA`. -/
theorem closed_Y : (affineSl2VOA_closed k hk).Y = YA k hk := rfl

/-- The VOA's vacuum is the affine vacuum `|0⟩`. -/
theorem closed_vacuum : (affineSl2VOA_closed k hk).vacuum = vacuumA k := rfl

/-- The VOA's `ℤ`-grading is the `ℓ₀`-energy grading `gradingZA`. -/
theorem closed_grading : (affineSl2VOA_closed k hk).grading = gradingZA k := rfl

/-- The VOA's conformal vector is the Sugawara vector `ω`. -/
theorem closed_conformalVector :
    (affineSl2VOA_closed k hk).conformalVector = omegaA k := rfl

/-- The VOA's state–field product `u₍ₙ₎v` is the `n`-th mode of `YA u`. -/
theorem closed_smul (u : WakModule k) (n : ℤ) (v : WakModule k) :
    (affineSl2VOA_closed k hk).smul u n v = mode (YA k hk u) n v := rfl

/-- The VOA's Virasoro mode `Lₙ = ω₍ₙ₊₁₎` is the Sugawara mode `Lsug k n`. -/
theorem closed_L (n : ℤ) : (affineSl2VOA_closed k hk).L n = Lsug k n := by
  rw [VertexOperatorAlgebra.L_def, closed_Y, closed_conformalVector, YA_omega_eq, Lsug_def]

/-- The VOA's central charge is `3k/(k+2)` (restated from `affineSl2VOA_closed_central_charge`
so that this file is self-contained). -/
theorem closed_centralCharge :
    (affineSl2VOA_closed k hk).centralCharge = 3 * k / (k + 2) :=
  affineSl2VOA_closed_central_charge k hk

/-! ## §B  Non-degeneracy of the vertex map

The reconstruction theorem builds `YA` as *the* linear map with `(YA u)₀|0⟩ = u`.  That single
identity already forbids every degenerate `YA`: it makes `YA` injective, so no two distinct
states share a field and no nonzero state has the zero field.  Together with the two explicit
values below — the vacuum goes to the unit field, a current state goes to the current field —
this is what distinguishes the construction from a shell. -/

/-- **`YA` is injective.**  If two states have the same vertex operator they are equal: read the
state back off the field by `(YA u)₀|0⟩ = u` (VA3 creation). -/
theorem YA_injective : Function.Injective (YA k hk) := by
  intro u v huv
  have h : (YA k hk u) 0 (vacuumA k) = (YA k hk v) 0 (vacuumA k) := by rw [huv]
  rwa [YA_creation0, YA_creation0] at h

/-- **`YA` kills only `0`**: `Y(u,z) = 0 ↔ u = 0`.  In particular `YA` is not the zero map on
any nonzero state, the crudest degeneracy that a fake instance would exhibit. -/
theorem YA_eq_zero_iff (u : WakModule k) : YA k hk u = 0 ↔ u = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  exact YA_injective k hk (by rw [h, map_zero])

/-- A nonzero state has a nonzero vertex operator. -/
theorem YA_ne_zero {u : WakModule k} (hu : u ≠ 0) : YA k hk u ≠ 0 :=
  fun h => hu ((YA_eq_zero_iff k hk u).mp h)

/-- The VOA's vertex map is injective. -/
theorem closed_Y_injective : Function.Injective (affineSl2VOA_closed k hk).Y :=
  YA_injective k hk

/-- **Sanity check 1 (vacuum ↦ unit field).**  `Y(|0⟩, z) = 1` in the assembled VOA. -/
theorem Y_vacuum_eq_one :
    (affineSl2VOA_closed k hk).Y (affineSl2VOA_closed k hk).vacuum
      = (1 : FormalDist (End ℂ (WakModule k))) :=
  YA_vacuum k hk

/-- The state `Jᵃ₋₁|0⟩ ∈ 𝒱₁` created by the current `Jᵃ`. -/
noncomputable def currentState (a : Fin 3) : WakModule k := J k a (-1) (vacuumA k)

theorem currentState_def (a : Fin 3) : currentState k a = J k a (-1) (vacuumA k) := rfl

/-- **Sanity check 2 (current state ↦ current field).**  `Y(Jᵃ₋₁|0⟩, z) = Jᵃ(z)` in the assembled
VOA: the reconstructed all-states map really does restrict to the generating fields it was built
from. -/
theorem Y_currentState_eq_Jfield (a : Fin 3) :
    (affineSl2VOA_closed k hk).Y (currentState k a) = Jfield k a :=
  Vir.YA_current_state k hk a

/-- Sanity check 2, in mode form: the VOA product `(Jᵃ₋₁|0⟩)₍ₙ₎` **is** the affine current mode
`Jᵃₙ`, as an operator on `WakModule k`.  This is the identity that ties the VOA structure back to
the affine Lie algebra it is supposed to represent. -/
theorem smul_currentState_eq_J (a : Fin 3) (n : ℤ) (v : WakModule k) :
    (affineSl2VOA_closed k hk).smul (currentState k a) n v = J k a n v := by
  rw [closed_smul, ← closed_Y, Y_currentState_eq_Jfield, Vir.mode_Jfield]

/-- The current states are homogeneous of conformal weight `1` — they span the degree-1 part of
the grading that carries `𝔰𝔩₂`. -/
theorem currentState_mem_grading (a : Fin 3) :
    currentState k a ∈ (affineSl2VOA_closed k hk).grading 1 := by
  rw [closed_grading, currentState_def]
  have h0 : vacuumA k ∈ gradingZA k 0 := vacuumA_mem_gradingZA_zero k
  simpa using J_mem_gradingZA k a (-1) 0 h0

/-- **The affine Kac–Moody relations hold between VOA modes.**  Restating `current_comm` through
`smul_currentState_eq_J`:
`⁅(Jᵃ₋₁|0⟩)₍ₘ₎, (Jᵇ₋₁|0⟩)₍ₙ₎⁆ = ∑_c f^{ab}_c (Jᶜ₋₁|0⟩)₍ₘ₊ₙ₎ + m·k·κ(a,b)·δ_{m+n,0}`.

This is the structural anti-degeneracy check.  A collapsed vertex map would force the right-hand
side to vanish identically; here the level-`k` central term survives, so the VOA product on the
weight-1 subspace reproduces the affine Lie algebra `𝔰𝔩₂^` at level `k` exactly. -/
theorem smul_currentState_comm (a b : Fin 3) (m n : ℤ) (v : WakModule k) :
    (affineSl2VOA_closed k hk).smul (currentState k a) m
        ((affineSl2VOA_closed k hk).smul (currentState k b) n v)
      - (affineSl2VOA_closed k hk).smul (currentState k b) n
        ((affineSl2VOA_closed k hk).smul (currentState k a) m v)
      = (∑ c, fabc a b c • J k c (m + n) v)
        + (if m + n = 0 then ((m : ℂ) * k * kappa a b) • v else 0) := by
  simp only [smul_currentState_eq_J]
  have h := congrArg (fun T : End ℂ (WakModule k) => T v) (current_comm k a b m n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply] at h
  rw [h]
  split_ifs <;> simp

/-- **The VOA is nonzero** — the one statement in this file that uses the theorem
`VOA.pbw`.  It is inherited verbatim from `vacuumA_ne_zero`
(`= AffineLie.vacuumVector_ne_zero`), which is where `pbw` supplies affine-vacuum nonvanishing.

Everything else in this file is `pbw`-free — and necessarily *weaker* for it, since a zero module
satisfies every VOA axiom.  Combining this lemma with `smul_currentState_comm` at `k ≠ 0` is what
turns "the axioms hold" into "the axioms hold on something". -/
theorem closed_vacuum_ne_zero : (affineSl2VOA_closed k hk).vacuum ≠ 0 :=
  vacuumA_ne_zero k

/-! ## §C  The admissible level `k = -4/3`

`k = -4/3` is the first admissible non-integral level of `𝔰𝔩₂` (`k + 2 = 2/3 ≠ 0`, so the
Sugawara construction applies) and the level at which `Examples/AffineSl2Singular` produces the
weight-3 singular vector.  Its simple quotient `L₋₄⁄₃(𝔰𝔩₂)` is the canonical quasi-lisse,
non-lisse VOA: associated variety the nilpotent cone of `𝔰𝔩₂`, i.e. `ℂ²/ℤ₂`, with exactly two
symplectic leaves.  This section puts the singular vector inside an honest VOA. -/

/-- The admissible level `k = -4/3` is non-critical: `-4/3 + 2 = 2/3 ≠ 0`. -/
theorem admLevel_noncritical : (-4 / 3 : ℂ) + 2 ≠ 0 := by norm_num

/-- **The affine `𝔰𝔩₂` VOA at the admissible level `k = -4/3`** — the universal (not yet simple)
vertex operator algebra `V^{-4/3}(𝔰𝔩₂)`. -/
noncomputable def voaSl2Adm : VertexOperatorAlgebra (WakModule (-4 / 3 : ℂ)) :=
  affineSl2VOA_closed (-4 / 3 : ℂ) admLevel_noncritical

/-- **The central charge at `k = -4/3` is `c = -6`**: `3k/(k+2) = 3·(-4/3)/(2/3) = -6`. -/
theorem voaSl2Adm_centralCharge : voaSl2Adm.centralCharge = -6 := by
  rw [voaSl2Adm, closed_centralCharge]
  norm_num

/-- The vacuum of `V^{-4/3}(𝔰𝔩₂)`. -/
theorem voaSl2Adm_vacuum : voaSl2Adm.vacuum = vacuumA (-4 / 3 : ℂ) := rfl

/-- The grading of `V^{-4/3}(𝔰𝔩₂)` is the `ℓ₀`-energy grading. -/
theorem voaSl2Adm_grading : voaSl2Adm.grading = gradingZA (-4 / 3 : ℂ) := rfl

/-- **The singular vector lives in the VOA**, homogeneous of conformal weight `3`. -/
theorem sl2Singular_mem_grading :
    Sl2Sing.sl2Singular ∈ voaSl2Adm.grading 3 :=
  Sl2Sing.sl2Singular_mem

/-- **The VOA-level singularity statement that is unconditionally true**: every mode `n ≥ 1` of
every current field annihilates `s`.  Since the current states `Jᵃ₋₁|0⟩` lie in `𝒱₁`, this is
exactly the `m = 1` instance of `SingVec.IsStronglySingularOfWeight.annihilated` — the
non-weight-raising modes of the degree-1 generators.

The proof is `smul_currentState_eq_J` (sanity check 2) composed with
`Sl2Sing.sl2Singular_pos`; it is precisely the point at which the abstract VOA product is
identified with the concrete affine mode. -/
theorem sl2Singular_smul_currentState (a : Fin 3) {n : ℤ} (hn : 1 ≤ n) :
    voaSl2Adm.smul (currentState (-4 / 3 : ℂ) a) n Sl2Sing.sl2Singular = 0 := by
  rw [voaSl2Adm, smul_currentState_eq_J]
  exact Sl2Sing.sl2Singular_pos a hn

/-- **`L₀ s = 3 s`** — the singular vector has conformal weight `3` for the Sugawara Virasoro
algebra (VOA2 applied to `sl2Singular_mem_grading`). -/
theorem sl2Singular_L0 :
    voaSl2Adm.L 0 Sl2Sing.sl2Singular = (3 : ℂ) • Sl2Sing.sl2Singular := by
  have h := voaSl2Adm.L0_grading Sl2Sing.sl2Singular sl2Singular_mem_grading
  rw [VertexOperatorAlgebra.L_def, show (0 : ℤ) + 1 = 1 from rfl]
  rw [h]
  norm_num

/-- **`Lₙ s = 0` for `n ≥ 4`, from the grading alone.**  `ω ∈ 𝒱₂` and `s ∈ 𝒱₃` give
`Lₙ s = ω₍ₙ₊₁₎ s ∈ 𝒱_{3-n}`, and `𝒱_{<0} = 0` by CFT-type positivity.  Only `n = 1, 2, 3`
remain (see §D). -/
theorem sl2Singular_L_of_four_le {n : ℤ} (hn : 4 ≤ n) :
    voaSl2Adm.L n Sl2Sing.sl2Singular = 0 := by
  have hmem := voaSl2Adm.toPreVertexAlgebra.grading_mode
    voaSl2Adm.conformalVector voaSl2Adm.conformal_mem
    Sl2Sing.sl2Singular sl2Singular_mem_grading (n + 1)
  rw [voaSl2Adm.positivity _ (by omega : (2 : ℤ) + 3 - (n + 1) - 1 < 0),
    Submodule.mem_bot] at hmem
  rw [VertexOperatorAlgebra.L_def]
  exact hmem

/-- **The singular vector is a `SingVec.IsSingularOfWeight` vector of `V^{-4/3}(𝔰𝔩₂)` as soon as
four explicit finite facts hold.**  Weight positivity and homogeneity are proved here; `n ≥ 4` is
proved here; what remains is exactly `s ≠ 0` and the three middle Virasoro modes.

Stated as a conditional.  `hne` is available as `Wak.sl2Singular_ne_zero`; `h₁ h₂ h₃` follow
from the commutator `AffineVOA.Vir.Lcomm_J` but are not stated as theorems.  See §D. -/
theorem sl2Singular_isSingularOfWeight_of
    (hne : Sl2Sing.sl2Singular ≠ 0)
    (h₁ : voaSl2Adm.L 1 Sl2Sing.sl2Singular = 0)
    (h₂ : voaSl2Adm.L 2 Sl2Sing.sl2Singular = 0)
    (h₃ : voaSl2Adm.L 3 Sl2Sing.sl2Singular = 0) :
    SingVec.IsSingularOfWeight voaSl2Adm 3 Sl2Sing.sl2Singular where
  ne_zero := hne
  weight_pos := by norm_num
  homogeneous := sl2Singular_mem_grading
  annihilated := by
    intro n hn
    rcases (by omega : n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n) with h | h | h | h
    · rw [h]; exact h₁
    · rw [h]; exact h₂
    · rw [h]; exact h₃
    · exact sl2Singular_L_of_four_le h

/-- `V^{-4/3}(𝔰𝔩₂)` is a nonzero VOA (uses the theorem `VOA.pbw`, via
`closed_vacuum_ne_zero`). -/
theorem voaSl2Adm_vacuum_ne_zero : voaSl2Adm.vacuum ≠ 0 :=
  closed_vacuum_ne_zero (-4 / 3 : ℂ) admLevel_noncritical

/-- The ideal generated by the singular vector is nontrivial once `s ≠ 0` — the first half of
"`V^{-4/3}(𝔰𝔩₂)` is not simple".  (The *other* half, properness of `(s)`, is the invariant-form
route of `Core.SingularVector` and is not attempted here.) -/
theorem sl2Singular_idealGen_ne_bot (hne : Sl2Sing.sl2Singular ≠ 0) :
    SingVec.idealGen voaSl2Adm Sl2Sing.sl2Singular ≠ ⊥ :=
  SingVec.idealGen_ne_bot hne

/-- Packaging the PBW-independence gate of `Examples/AffineSl2Singular` with the ideal statement:
linear independence of the five weight-3 charge-2 monomials makes the ideal generated by `s`
inside the VOA nontrivial. -/
theorem sl2Singular_idealGen_ne_bot_of_indep
    (hli : LinearIndependent ℂ
      ![Sl2Sing.M1 (-4 / 3 : ℂ), Sl2Sing.M2 (-4 / 3 : ℂ), Sl2Sing.M3 (-4 / 3 : ℂ),
        Sl2Sing.M4 (-4 / 3 : ℂ), Sl2Sing.M5 (-4 / 3 : ℂ)]) :
    SingVec.idealGen voaSl2Adm Sl2Sing.sl2Singular ≠ ⊥ :=
  sl2Singular_idealGen_ne_bot (Sl2Sing.sl2Singular_ne_zero_of_indep hli)

/-! ## §D  Axiom and completeness audit

**Axioms.**  `VOA.pbw` is a theorem
(`Foundations/AffineLie.lean`), so every declaration here is
`[propext, Classical.choice, Quot.sound]`.  It is used here in exactly
two places — `closed_vacuum_ne_zero` and `voaSl2Adm_vacuum_ne_zero` — and in both it is inherited
verbatim from `vacuumA_ne_zero = AffineLie.vacuumVector_ne_zero`, the affine-vacuum-nonvanishing
field of `PBWPrinciple`.  Everything else, `affineSl2VOA_closed` and `YA` included, is `pbw`-free.

The split is not an accident: a *zero* module satisfies every VOA axiom, so nonvanishing of this
VOA needs a PBW-type input — `VOA.pbw` here, or the explicit Wakimoto PBW basis in
`AffineSl2BoundaryMaximalIdeal.affineSl2_vacuum_ne_zero`.  `smul_currentState_comm` (`pbw`-free)
says the VOA product
reproduces `𝔰𝔩₂^` at level `k` including the central term; `closed_vacuum_ne_zero` (`pbw`) says
there is something for it to act on.  Together they are the nondegeneracy statement.

**What is proved.**  The `PreVertexAlgebra`/`VertexOperatorAlgebra` instance for `V^k(𝔰𝔩₂)` was
already closed in `Examples/AffineSl2Virasoro` (`affineSl2VOA_closed`); this file adds the
bridges, the non-degeneracy of `YA` (`YA_injective`), and the `k = -4/3` specialisation.

**What is not proved in this file.**
* `Sl2Sing.sl2Singular ≠ 0` — proved elsewhere, `pbw`-free, as `Wak.sl2Singular_ne_zero`.
* `Lₙ s = 0` for `n = 1, 2, 3` — not stated; the general Sugawara commutator they reduce to is
  `AffineVOA.Vir.Lcomm_J`.  `sl2Singular_isSingularOfWeight_of` is the interface they meet.
-/

end VOA.AffineVOA.Inst
