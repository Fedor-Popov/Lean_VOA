/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import VOA.Core.SimpleImage
import VOA.Examples.DSReductionSl2
import VOA.Examples.TripletLattice
import VOA.Examples.TripletScreening

/-!
# The Drinfeld–Sokolov morphism for `𝔰𝔩₂`: the map, not the bookkeeping

`Examples/DSReductionSl2` proves the *arithmetic* of the Drinfeld–Sokolov reduction of
`V^k(𝔰𝔩₂)` — the central charge `dsCentralCharge k = 13 − 6(k+2) − 6/(k+2)`, its
identification with the `(p,q)` minimal-model value, and the BRST anomaly count — and it
builds the BRST charge `dsQ` with `dsQ² = 0`.  What it does *not* build is a **map**.  This
file builds maps.

Both routes advance here.  §1 relocates the screening to a setting that actually has nonzero
momentum and proves the resulting kernel is a non-trivial vertex operator algebra of the right
central charge, with a morphism.  §2–§4 assemble the BRST complex `V^k(𝔰𝔩₂) ⊗ (bc)` as a
genuine super vertex algebra and embed `V^k(𝔰𝔩₂)` into it.  §5 records exactly where the BRST
route stops, including one obstruction not identified in the literature consulted.

## Main results

### Route 2 — the screening, relocated (§1)

* `dsScreeningState`, `dsScreeningOp` — the genuine Drinfeld–Sokolov screening `∮ e^{α₊φ}` as
  the zero mode of a **nonzero-momentum** vertex operator, inside `tripletLatticeVOA p`.
* `dsLatticeScreening` — its kernel, as a `VertexOperatorAlgebra`.
* `dsLatticeScreening_centralCharge` — that kernel has central charge exactly
  `dsCentralCharge (p − 2)`, i.e. the Drinfeld–Sokolov value at `k + 2 = p`
  (`latticeCentralCharge_eq_ds` is the arithmetic).
* `dsScreeningOp_ne_zero`, `dsLatticeScreening_ne_top` — **non-vacuity**: the screening
  operator is not zero and its kernel is a proper subalgebra.  `Examples/DSReductionSl2` §5
  records that in the zero-momentum `Fock` this fails; here it does not.
* `dsScreeningIncl_isVOAHom`, `dsScreeningIncl_map_L` — a **morphism**: the inclusion
  `ker Q ↪ V_{L_p}^{λ_p}` is an `IsVOAHom`, and it preserves `ω`, so all Virasoro modes are
  intertwined.

### Route 1 — the BRST complex (§2–§5)

* `tenGrading_iSupIndep`, `tenGrading_isInternal` — the `iSupIndep` clause of
  `Core/TensorVOA.TensorGradingHyp` is a **theorem**, proved unconditionally.  This contradicts
  that file's closing note, which conjectures no separating operator exists for the `ℂ`-indexed
  weight grading; the canonical weight operator `wtOp` of the grading is one.
* `tenGrading_finiteDimensional_of_natSupported` — the remaining `finrank` clause, for
  factors with weight support in `ℕ`.  It is genuinely not a formal consequence of the axioms,
  as `Core/TensorVOA` says; this discharges it under a discreteness hypothesis that both
  Drinfeld–Sokolov factors satisfy.
* `dsComplex` — **the Drinfeld–Sokolov complex** `𝒞^k = V^k(𝔰𝔩₂) ⊗ (bc)` as a
  `SuperVertexAlgebra`, all hypotheses discharged.
* `dsEmbed`, `dsEmbed_mode`, `dsEmbed_smul_dsComplex`, `dsEmbed_injective` — **THE
  MORPHISM**: `ι_k : V^k(𝔰𝔩₂) → 𝒞^k`, `x ↦ x ⊗ 𝟙`, an injective homomorphism of vertex
  superalgebras (vacuum preserved, every mode intertwined).
* `dsQ_sq_on_dsComplex` — `Q² = 0` on the assembled complex, **proved** (it is
  `DSReductionSl2.dsQ_mul_self`, not assumed).
* `dsQ_odd`, `dsQ_vacuum` — two more `BRSTComplex` obligations discharged.
* `dsQ_split`, `dsQwt_preserves_grading`, `dsQlow_lowers_grading` — ⚠ the obstruction, see §5.

## Status section (read this first)

**Nothing here identifies the Drinfeld–Sokolov reduction with a minimal model, or with the
Virasoro vertex operator algebra.**  Equality of central charges is *not* that statement, and
this file never claims it; compare the same distinction drawn in `Examples/TripletWp` for the
`W(p)`/triplet pair.  In particular `dsLatticeScreening p hp` is *not* claimed to be
`virasoroVOA (dsCentralCharge (p−2))`; what is proved is that it is a proper, non-trivial
subalgebra of the lattice VOA with that central charge.

**The BRST cohomology is not constructed.**  The complex is built and the differential squares
to zero, but `Core/BRSTCohomology.BRSTComplex` cannot be instantiated, for **two independent**
reasons:

1. ⚠ `Q_wt` is **false** for `dsQ` on the convolution grading of `dsComplex` — the BRST current
   `(e + 𝟙) ⊗ c` is not weight-homogeneous, since `e ⊗ c` has weight `1` and `𝟙 ⊗ c` has weight
   `0`.  Both halves are proved in §5.  The fix is the *improved* Drinfeld–Sokolov grading
   (ghosts at `λ = 0`, affine weight shifted by `ρ^∨`), which is not built anywhere in this
   repository.  Note this is a **new** obstruction: it is independent of, and logically prior
   to, the `Q_deriv` gap that `Examples/DSReductionSl2` §5 names.
2. `Q_deriv` — the super Leibniz rule — still needs the non-negative super `n`-th product
   theorem, which the repository does not have.  Nothing here changes that.

`dsComplex` is a bare `SuperVertexAlgebra`: `Core/TensorVOA` builds no conformal layer, so the
complex has **no conformal vector and no central charge** here.  Consequently the central
charge of the Drinfeld–Sokolov reduction is connected to `dsCentralCharge` only on the
*screening* side (`dsLatticeScreening_centralCharge`), not on the BRST side.

The Lee–Yang level `k = −8/5` is reached by `dsComplex` and `dsEmbed` (which are uniform in `k`
with `k + 2 ≠ 0`) but **not** by `dsLatticeScreening`, whose levels are `k + 2 = p ∈ ℤ_{>0}`;
`latticeVOAGen` requires an even positive-definite lattice, and `α₊² = 2(k+2) = 4/5` is not an
even integer.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`); no use
of the theorem `VOA.pbw`.

## Dependencies

`Core/SimpleImage` (`IsVOAHom`), `Core/TensorVOA` (`tenY`, `tenSub`, `tenGrading`, `tensorSVA`),
`Core/ScreeningKernel` (`screeningKernelVOA`), `Examples/DSReductionSl2` (`dsCentralCharge`,
`dsQ`, `dsQ_mul_self`, `tenY_tmul_toSuper`), `Examples/TripletLattice` (`tripletLatticeVOA`),
`Examples/TripletScreening` (`Qscr`, `Hscr_ne_zero`), `Examples/GhostSystem` (`bcGhostSVA`),
`Examples/AffineSl2Virasoro` / `Examples/AffineSl2VOA` (`affineVA`, `gradingZA_positivity`).
-/

namespace VOA.DSMor

open scoped TensorProduct
open Module (End)

/-! ## §1  Route 2, relocated: the screening in a **nonzero-momentum** setting

`Examples/DSReductionSl2` §5 records the defect of its own screening construction: the genuine
Drinfeld–Sokolov screening state is `e^{α₊φ}`, which carries nonzero momentum, while
`FBgc.freeBosonVOA` lives on the zero-momentum Fock space, whose weight-one space is spanned by
`a₋₁|0⟩` with zero mode `a₀ = 0`.  Every screening operator actually available there is the zero
operator, and its kernel is the whole algebra.

The repository already contains a home with nonzero-momentum sectors: the **deformed rank-one
lattice vertex operator algebra** `tripletLatticeVOA p` of `Examples/TripletLattice`, on
`L_p = ℤα` with `⟨α,α⟩ = 2p` and the Feigin–Fuchs conformal vector `ω_{λ_p}`.  There
`latChargeGen_alpha_mem_grade_one` proves that `e^α` is a genuine weight-one state of nonzero
momentum, so `Q = (e^α)₍₀₎` is a genuine, generally nonzero, screening operator.

The dictionary is `t = k + 2 = p`, i.e. `k = p − 2`, and it is exact: see `dsLevelOfP` and
`latticeCentralCharge_eq_ds`.
-/

/-- **The Drinfeld–Sokolov level realised by the rank-one lattice `L_p`.**  The deformed lattice
VOA on `L_p = ℤα`, `⟨α,α⟩ = 2p`, sits at `t = k + 2 = p`, i.e. at level `k = p − 2`. -/
noncomputable def dsLevelOfP (p : ℕ) : ℂ := (p : ℂ) - 2

@[simp] theorem dsLevelOfP_add_two (p : ℕ) : dsLevelOfP p + 2 = (p : ℂ) := by
  rw [dsLevelOfP]; ring

/-- `k + 2 ≠ 0` for the lattice levels, since `p ≥ 1`. -/
theorem dsLevelOfP_add_two_ne_zero {p : ℕ} (hp : 1 ≤ p) : dsLevelOfP p + 2 ≠ 0 := by
  rw [dsLevelOfP_add_two]
  exact_mod_cast Nat.one_le_iff_ne_zero.mp hp

/-- **The arithmetic bridge.**  The Feigin–Fuchs central charge of the deformed rank-one
lattice VOA at `⟨α,α⟩ = 2p` *is* the Drinfeld–Sokolov central charge at level `k = p − 2`:

`1 − 6(p−1)²/p = 13 − 6p − 6/p = dsCentralCharge (p − 2)`. -/
theorem latticeCentralCharge_eq_ds {p : ℕ} (hp : 1 ≤ p) :
    1 - 6 * ((p : ℂ) - 1) ^ 2 / (p : ℂ) = DSsl2.dsCentralCharge (dsLevelOfP p) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hp
  rw [DSsl2.dsCentralCharge, dsLevelOfP_add_two]
  field_simp
  ring

/-- **The Drinfeld–Sokolov screening state** at level `k = p − 2`: the momentum-`α` vertex
operator `e^α` of the deformed lattice VOA.  Unlike every weight-one state of the zero-momentum
Fock space, this one has **nonzero momentum**. -/
noncomputable def dsScreeningState (p : ℕ) : LatGen.LatModuleGen (LatGen.Triplet.latP p) :=
  LatGen.latChargeGen (LatGen.Triplet.latP p) (LatGen.Triplet.alphaP p)

/-- The Drinfeld–Sokolov screening state has conformal weight exactly `1` for the deformed
(background-charge) grading — the condition `α²/2 − λ·α = 1` that makes `∮ e^{αφ}` a screening
current. -/
theorem dsScreeningState_mem_grade_one (p : ℕ) (hp : 1 ≤ p) :
    dsScreeningState p ∈ (LatGen.Triplet.tripletLatticeVOA p hp).grading 1 :=
  LatGen.Triplet.latChargeGen_alpha_mem_grade_one p hp

/-- **The Drinfeld–Sokolov screening operator** `Q = ∮ e^{α₊φ(z)} dz = (e^α)₍₀₎`, as an
endomorphism of the deformed lattice VOA.  This is `TripletScreening.Qscr`, i.e. the honest
zero mode of the momentum-`α` vertex operator, not a zero-momentum stand-in. -/
noncomputable def dsScreeningOp (p : ℕ) :
    End ℂ (LatGen.LatModuleGen (LatGen.Triplet.latP p)) :=
  LatGen.Screen.Qscr (LatGen.Triplet.latP p) (LatGen.Triplet.alphaP p)

/-- **The Drinfeld–Sokolov screening kernel as a vertex operator algebra.**  `ker Q` inside
the deformed rank-one lattice VOA, with its induced VOA structure.  This is the object
`DSReductionSl2.dsScreeningSl2` was reaching for, with the *genuine* screening state. -/
noncomputable def dsLatticeScreening (p : ℕ) (hp : 1 ≤ p) :
    VertexOperatorAlgebra
      (Screening.screeningKernel (LatGen.Triplet.tripletLatticeVOA p hp)
        (dsScreeningState p) (dsScreeningState_mem_grade_one p hp)).carrier :=
  Screening.screeningKernelVOA (LatGen.Triplet.tripletLatticeVOA p hp) _ _

/-- **Target (f) for the screening route, with a genuine screening.**  The central
charge of the Drinfeld–Sokolov screening kernel at `k + 2 = p` is exactly `dsCentralCharge k`. -/
theorem dsLatticeScreening_centralCharge (p : ℕ) (hp : 1 ≤ p) :
    (dsLatticeScreening p hp).centralCharge = DSsl2.dsCentralCharge (dsLevelOfP p) := by
  rw [dsLatticeScreening, Screening.screeningKernelVOA_centralCharge,
    LatGen.Triplet.tripletLatticeVOA_centralCharge]
  exact latticeCentralCharge_eq_ds hp

/-- The screening kernel really is the kernel of `dsScreeningOp`: membership in the carrier is
exactly annihilation by `Q`. -/
theorem mem_dsLatticeScreening_iff (p : ℕ) (hp : 1 ≤ p)
    (x : LatGen.LatModuleGen (LatGen.Triplet.latP p)) :
    x ∈ (Screening.screeningKernel (LatGen.Triplet.tripletLatticeVOA p hp)
        (dsScreeningState p) (dsScreeningState_mem_grade_one p hp)).carrier
      ↔ dsScreeningOp p x = 0 := by
  rw [dsScreeningOp, LatGen.Screen.Qscr_eq_mode_YfullGen (LatGen.Triplet.latP p)
    (LatGen.Triplet.latP_even p) (LatGen.Triplet.latP_posDef p hp)]
  exact Iff.rfl

/-! ### The construction is not vacuous

This is the point of relocating.  `DSReductionSl2` §5 records that inside `Fock` the only
available screening operator is the zero operator, whose kernel is everything.  Here `Q ≠ 0`
and `ker Q ≠ ⊤`, both proved, using
`TripletScreening.Hscr_ne_zero`: `Q(e^{−α}) = ε·S_{2p−1}(α) ⊗ e⁰ ≠ 0`, the middle triplet
generator, whose non-vanishing rests on the non-vanishing of the vector Schur polynomials.
-/

/-- The generator `α = 1` of `L_p` is non-zero. -/
theorem alphaP_ne_zero (p : ℕ) : LatGen.Triplet.alphaP p ≠ 0 := by
  show (1 : ℤ) ≠ 0
  exact one_ne_zero

/-- **The Drinfeld–Sokolov screening operator is genuinely non-zero.**  It sends
`F = e^{−α}` to the non-zero Schur state `H = ε(α,−α)·S_{2p−1}(α) ⊗ e⁰`.  Contrast the
zero-momentum free-boson setting, where every available screening operator vanishes
identically. -/
theorem dsScreeningOp_ne_zero (p : ℕ) (hp : 1 ≤ p) : dsScreeningOp p ≠ 0 := by
  intro h
  refine LatGen.Screen.Hscr_ne_zero (LatGen.Triplet.latP p) (LatGen.Triplet.latP_posDef p hp)
    (LatGen.Triplet.alphaP p) (alphaP_ne_zero p) p hp (LatGen.Triplet.latP_form_alpha p) ?_
  have : dsScreeningOp p
      (LatGen.Screen.Fscr (LatGen.Triplet.latP p) (LatGen.Triplet.alphaP p)) = 0 := by
    rw [h, LinearMap.zero_apply]
  exact this

/-- **The Drinfeld–Sokolov screening kernel is a proper subalgebra**: `e^{−α}` lies outside
it.  So `dsLatticeScreening` is a genuinely smaller vertex operator algebra than the ambient
lattice VOA, not a restatement of it. -/
theorem dsLatticeScreening_ne_top (p : ℕ) (hp : 1 ≤ p) :
    (Screening.screeningKernel (LatGen.Triplet.tripletLatticeVOA p hp)
      (dsScreeningState p) (dsScreeningState_mem_grade_one p hp)).carrier ≠ ⊤ := by
  intro htop
  refine LatGen.Screen.Hscr_ne_zero (LatGen.Triplet.latP p) (LatGen.Triplet.latP_posDef p hp)
    (LatGen.Triplet.alphaP p) (alphaP_ne_zero p) p hp (LatGen.Triplet.latP_form_alpha p) ?_
  exact (mem_dsLatticeScreening_iff p hp _).mp (by rw [htop]; exact Submodule.mem_top)

/-! ### The morphism on the screening side: the inclusion `W ↪ V_{L_p}^{λ_p}`

The screening kernel comes with a canonical map — its inclusion into the ambient lattice VOA —
and this one *does* preserve the conformal vector (unlike the affine-to-reduction direction),
because `Screening.screeningKernelVOA` gives the subalgebra the ambient `ω_{λ_p}`.  So all
Virasoro modes are intertwined, by `IsVOAHom.map_L`.
-/

/-- The inclusion of the Drinfeld–Sokolov screening kernel into the ambient deformed lattice
VOA, as a linear map. -/
noncomputable def dsScreeningIncl (p : ℕ) (hp : 1 ≤ p) :
    (Screening.screeningKernel (LatGen.Triplet.tripletLatticeVOA p hp)
        (dsScreeningState p) (dsScreeningState_mem_grade_one p hp)).carrier
      →ₗ[ℂ] LatGen.LatModuleGen (LatGen.Triplet.latP p) :=
  (Screening.screeningKernel (LatGen.Triplet.tripletLatticeVOA p hp)
    (dsScreeningState p) (dsScreeningState_mem_grade_one p hp)).carrier.subtype

/-- **A morphism for the screening route.**  The inclusion of the Drinfeld–Sokolov screening
kernel into the deformed lattice VOA is a homomorphism of vertex operator algebras in the sense
of `Core/SimpleImage.IsVOAHom`: it preserves the vacuum and intertwines every mode. -/
theorem dsScreeningIncl_isVOAHom (p : ℕ) (hp : 1 ≤ p) :
    IsVOAHom (dsLatticeScreening p hp) (LatGen.Triplet.tripletLatticeVOA p hp)
      (dsScreeningIncl p hp) where
  map_vacuum := rfl
  map_smul u n v := by
    show ((mode ((dsLatticeScreening p hp).Y u) n v :
        (Screening.screeningKernel _ _ _).carrier) : LatGen.LatModuleGen (LatGen.Triplet.latP p))
      = mode ((LatGen.Triplet.tripletLatticeVOA p hp).Y (u : _)) n (v : _)
    rfl

/-- The inclusion also preserves the conformal vector — the screening kernel inherits `ω_{λ_p}`
verbatim.  (`IsVOAHom` deliberately does **not** demand this; here it happens to be true.) -/
theorem dsScreeningIncl_conformalVector (p : ℕ) (hp : 1 ≤ p) :
    dsScreeningIncl p hp (dsLatticeScreening p hp).conformalVector
      = (LatGen.Triplet.tripletLatticeVOA p hp).conformalVector := rfl

/-- Hence every Virasoro mode is intertwined by the inclusion: `L_n` computed inside the
Drinfeld–Sokolov screening kernel is the restriction of `L_n` of the ambient lattice VOA. -/
theorem dsScreeningIncl_map_L (p : ℕ) (hp : 1 ≤ p) (n : ℤ)
    (v : (Screening.screeningKernel (LatGen.Triplet.tripletLatticeVOA p hp)
        (dsScreeningState p) (dsScreeningState_mem_grade_one p hp)).carrier) :
    dsScreeningIncl p hp ((dsLatticeScreening p hp).L n v)
      = (LatGen.Triplet.tripletLatticeVOA p hp).L n (dsScreeningIncl p hp v) :=
  (dsScreeningIncl_isVOAHom p hp).map_L (dsScreeningIncl_conformalVector p hp) n v

/-- The inclusion is injective, so the Drinfeld–Sokolov screening kernel is a genuine vertex
operator subalgebra of the deformed lattice VOA. -/
theorem dsScreeningIncl_injective (p : ℕ) (hp : 1 ≤ p) :
    Function.Injective (dsScreeningIncl p hp) :=
  Subtype.val_injective

/-! ## §2  Route 1, step 0: the convolution weight grading really is a direct sum

`Core/TensorVOA` leaves two linear-algebraic facts about the convolution weight grading
`(V ⊗ W)_h = ⨆_{h₁} V_{h₁} ⊗ W_{h−h₁}` as hypotheses, packaged in `TensorGradingHyp`, and its
closing note asserts that the `ℂ`-indexed weight case "admits no separating operator analogous
to `totInvol`".  **It does.**  The separating operator is the canonical weight operator of the
grading itself, which exists for free from `isInternal`; the argument is exactly the one the
repository already runs twice, at `Ghost.gradingGh_iSupIndep` and
`AffineVOA.eigenspaces_iSupIndep_A`, merely never applied to the convolution.

So `TensorGradingHyp.iSupIndep` is a **theorem** (`tenGrading_iSupIndep`), and only the
`finrank` clause — a genuine discreteness obligation, see §3 — remains.  Nothing in
`Core/TensorVOA` is edited; the theorem is proved here and consumed here.
-/

section TensorGrading

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- **The canonical weight operator of an internal `ℂ`-grading**: the endomorphism acting on the
`h`-component by the scalar `h`.  Built from the decomposition supplied by `IsInternal`, so it
needs no extra input. -/
noncomputable def wtOp (G : ℂ → Submodule ℂ A) (hG : DirectSum.IsInternal G) : End ℂ A :=
  letI := hG.chooseDecomposition G
  (DirectSum.toModule ℂ ℂ A (fun h => h • (G h).subtype)).comp
    (DirectSum.decomposeLinearEquiv G).toLinearMap

/-- Each graded piece sits inside the corresponding eigenspace of `wtOp`.  This is the
"separating operator" whose absence `Core/TensorVOA`'s closing note conjectures. -/
theorem grading_le_eigen_wtOp (G : ℂ → Submodule ℂ A) (hG : DirectSum.IsInternal G) (h : ℂ) :
    G h ≤ Module.End.eigenspace (wtOp G hG) h := by
  letI := hG.chooseDecomposition G
  intro x hx
  rw [Module.End.mem_eigenspace_iff]
  show (DirectSum.toModule ℂ ℂ A (fun j => j • (G j).subtype))
      ((DirectSum.decomposeLinearEquiv G) x) = h • x
  have hdec : (DirectSum.decomposeLinearEquiv G) x
      = DirectSum.of (fun j => (G j : Submodule ℂ A)) h ⟨x, hx⟩ := by
    change DirectSum.decompose G x = _
    exact DirectSum.decompose_coe (ℳ := fun j => (G j : Submodule ℂ A)) (⟨x, hx⟩ : G h)
  rw [hdec, show (DirectSum.of (fun j => (G j : Submodule ℂ A)) h ⟨x, hx⟩)
      = DirectSum.lof ℂ ℂ (fun j => (G j : Submodule ℂ A)) h ⟨x, hx⟩ from rfl,
    DirectSum.toModule_lof]
  rfl

/-- The **total** weight operator `L₀ ⊗ 1 + 1 ⊗ L₀` on the tensor product. -/
noncomputable def L0tot (LA : End ℂ A) (LB : End ℂ B) : End ℂ (A ⊗[ℂ] B) :=
  TensorProduct.map LA (LinearMap.id) + TensorProduct.map (LinearMap.id) LB

/-- A product of eigenspaces lands in the eigenspace of `L0tot` for the *sum* of the
eigenvalues.  This is the whole content: weights add under the convolution. -/
theorem tenSub_le_eigen (LA : End ℂ A) (LB : End ℂ B) (h₁ h₂ : ℂ)
    (P : Submodule ℂ A) (Q : Submodule ℂ B)
    (hP : P ≤ Module.End.eigenspace LA h₁) (hQ : Q ≤ Module.End.eigenspace LB h₂) :
    TensorVA.tenSub P Q ≤ Module.End.eigenspace (L0tot LA LB) (h₁ + h₂) := by
  intro u hu
  refine TensorVA.tenSub_induction (P := P) (Q := Q)
    (motive := fun w => w ∈ Module.End.eigenspace (L0tot LA LB) (h₁ + h₂))
    (Submodule.zero_mem _) (fun x y hx hy => Submodule.add_mem _ hx hy)
    (fun c x hx => Submodule.smul_mem _ c hx) ?_ hu
  intro a ha b hb
  have hA : LA a = h₁ • a := Module.End.mem_eigenspace_iff.mp (hP ha)
  have hB : LB b = h₂ • b := Module.End.mem_eigenspace_iff.mp (hQ hb)
  rw [Module.End.mem_eigenspace_iff, L0tot, LinearMap.add_apply,
    TensorProduct.map_tmul, TensorProduct.map_tmul, hA, hB]
  simp only [LinearMap.id_coe, id_eq, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    add_smul]

/-- Independence of the convolution grading, from any pair of separating weight operators. -/
theorem tenGrading_iSupIndep_of_eigen (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (LA : End ℂ A) (LB : End ℂ B)
    (hA : ∀ h : ℂ, V.grading h ≤ Module.End.eigenspace LA h)
    (hB : ∀ h : ℂ, W.grading h ≤ Module.End.eigenspace LB h) :
    iSupIndep (TensorVA.tenGrading V W) := by
  refine (Module.End.eigenspaces_iSupIndep (L0tot LA LB)).mono ?_
  intro h
  refine iSup_le fun h₁ => ?_
  have := tenSub_le_eigen LA LB h₁ (h - h₁) (V.grading h₁) (W.grading (h - h₁))
    (hA h₁) (hB (h - h₁))
  rwa [show h₁ + (h - h₁) = h from by ring] at this

/-- **`TensorGradingHyp.iSupIndep` is a theorem, not a hypothesis.**  The convolution weight
components of a tensor product of vertex superalgebras are independent, unconditionally. -/
theorem tenGrading_iSupIndep (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) :
    iSupIndep (TensorVA.tenGrading V W) :=
  tenGrading_iSupIndep_of_eigen V W (wtOp V.grading V.isInternal) (wtOp W.grading W.isInternal)
    (grading_le_eigen_wtOp V.grading V.isInternal) (grading_le_eigen_wtOp W.grading W.isInternal)

/-- Hence the convolution weight grading is an internal direct sum, unconditionally. -/
theorem tenGrading_isInternal (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) :
    DirectSum.IsInternal (TensorVA.tenGrading V W) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨tenGrading_iSupIndep V W, TensorVA.tenGrading_iSup_eq_top V W⟩

/-- **`TensorGradingHyp` is a one-clause hypothesis.**  Only finite-dimensionality of the
convolution weight spaces has to be supplied by hand; independence comes for free. -/
theorem tensorGradingHyp_of_finrank (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (hfin : ∀ h : ℂ, FiniteDimensional ℂ (TensorVA.tenGrading V W h)) :
    TensorVA.TensorGradingHyp V W where
  iSupIndep := tenGrading_iSupIndep V W
  finrank := hfin

end TensorGrading

/-! ## §3  THE MORPHISM: `V^k(𝔰𝔩₂)` embeds in the Drinfeld–Sokolov complex

The Drinfeld–Sokolov complex is `𝒞^k = V^k(𝔰𝔩₂) ⊗ (bc)`, and the map the construction affords
is the **unit embedding** `ι : x ↦ x ⊗ 𝟙_{bc}`.  It is a homomorphism of vertex superalgebras
on the nose: `Y_{𝒞}(ι a, z)(ι x) = ι (Y(a,z)x)`, because over a purely even first factor `tenY`
is `rawCoeff` with no Koszul sign (`DSsl2.tenY_tmul_toSuper`) and because `Y_{bc}(𝟙,z)𝟙 = 𝟙`
collapses the convolution sum to its single term `m = s`.

**None of this needs `TensorGradingHyp`.**  `tenY` is defined unconditionally in
`Core/TensorVOA`, so the morphism exists and is proved even where the tensor product has not yet
been assembled into a `SuperVertexAlgebra`.  That is why this section comes before §4.
-/

section UnitEmbed

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- `Y(𝟙,z)` is the identity field, coefficientwise, for a bare vertex superalgebra.  (The
repository has this for `VertexOperatorAlgebra` and `SuperVertexOperatorAlgebra` only.) -/
theorem Y_vacuum_applySVA (W : SuperVertexAlgebra B) (j : ℤ) (v : B) :
    (W.Y W.vacuum) j v = if j = 0 then v else 0 := by
  rw [W.vacuum_Y]
  show (1 : FormalDist (End ℂ B)) j v = _
  rw [FormalDist.one_apply]
  split_ifs with h
  · rfl
  · rfl

/-- **The unit embedding** `ι : A → A ⊗ B`, `x ↦ x ⊗ 𝟙_B`. -/
noncomputable def unitEmbed (W : SuperVertexAlgebra B) : A →ₗ[ℂ] A ⊗[ℂ] B :=
  (TensorProduct.mk ℂ A B).flip W.vacuum

@[simp] theorem unitEmbed_apply (W : SuperVertexAlgebra B) (x : A) :
    unitEmbed W x = x ⊗ₜ[ℂ] W.vacuum := rfl

/-- The convolution sum collapses when both `B`-arguments are the vacuum: only `m = s`
survives, because `Y_B(𝟙,z)𝟙` is the identity field applied to `𝟙`. -/
theorem rawCoeff_unitEmbed (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A)
    (s : ℤ) (x : A) :
    TensorVA.rawCoeff V W a W.vacuum s (unitEmbed W x) = unitEmbed W (V.Y a s x) := by
  have hkey : ∀ m : ℤ, m ≠ s →
      (V.Y a m x) ⊗ₜ[ℂ] (W.Y W.vacuum (s - m) W.vacuum) = (0 : A ⊗[ℂ] B) := by
    intro m hm
    rw [Y_vacuum_applySVA, if_neg (by omega), TensorProduct.tmul_zero]
  rw [unitEmbed_apply, TensorVA.rawCoeff_tmul, finsum_eq_single _ s hkey,
    sub_self, Y_vacuum_applySVA, if_pos rfl, unitEmbed_apply]

/-- **The unit embedding intertwines the vertex operators.**  For a purely even left factor,
`Y_{A ⊗ B}(a ⊗ 𝟙, z)(x ⊗ 𝟙) = (Y_A(a,z)x) ⊗ 𝟙`, with no Koszul sign anywhere. -/
theorem unitEmbed_tenY (V : PreVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A) (s : ℤ)
    (x : A) :
    TensorVA.tenY V.toSuper W (unitEmbed W a) s (unitEmbed W x)
      = unitEmbed W (V.Y a s x) := by
  rw [unitEmbed_apply (W := W) a, DSsl2.tenY_tmul_toSuper]
  exact rawCoeff_unitEmbed V.toSuper W a s x

/-- The same statement in mode form: `ι(a)₍ₙ₎ ι(x) = ι(a₍ₙ₎x)`. -/
theorem unitEmbed_mode (V : PreVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A) (n : ℤ)
    (x : A) :
    mode (TensorVA.tenY V.toSuper W (unitEmbed W a)) n (unitEmbed W x)
      = unitEmbed W (mode (V.Y a) n x) := by
  rw [mode_apply, mode_apply]
  exact unitEmbed_tenY V W a (-n - 1) x

/-- The unit embedding takes the vacuum of `A` to the vacuum `𝟙 ⊗ 𝟙` of the tensor product. -/
@[simp] theorem unitEmbed_vacuum (V : PreVertexAlgebra A) (W : SuperVertexAlgebra B) :
    unitEmbed W V.vacuum = V.toSuper.vacuum ⊗ₜ[ℂ] W.vacuum := rfl

/-- **The unit embedding is injective** whenever `𝟙_B ≠ 0`: a dual functional `f` with
`f 𝟙_B = 1` produces the retraction `x ⊗ b ↦ f(b) • x`. -/
theorem unitEmbed_injective (W : SuperVertexAlgebra B) (hW : W.vacuum ≠ 0) :
    Function.Injective (unitEmbed (A := A) W) := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hW
  have hret : ∀ x : A,
      (TensorProduct.rid ℂ A) (TensorProduct.map (LinearMap.id (R := ℂ) (M := A)) f
        (unitEmbed W x)) = x := by
    intro x
    rw [unitEmbed_apply, TensorProduct.map_tmul, hf]
    simp
  intro x y hxy
  rw [← hret x, ← hret y, hxy]

end UnitEmbed

/-! ### The Drinfeld–Sokolov instance -/

/-- **The Drinfeld–Sokolov embedding** `ι_k : V^k(𝔰𝔩₂) → 𝒞^k = V^k(𝔰𝔩₂) ⊗ (bc)`,
`x ↦ x ⊗ 𝟙_{bc}`.  This is the map the BRST construction affords: the affine vertex algebra
sitting inside the Drinfeld–Sokolov complex as the ghost-number-zero, ghost-vacuum sector. -/
noncomputable def dsEmbed (k : ℂ) :
    AffineVOA.WakModule k →ₗ[ℂ] AffineVOA.WakModule k ⊗[ℂ] SympFerm.FockSF :=
  unitEmbed Ghost.bcGhostSVA

@[simp] theorem dsEmbed_apply (k : ℂ) (x : AffineVOA.WakModule k) :
    dsEmbed k x = x ⊗ₜ[ℂ] SympFerm.vacSF := rfl

/-- **`ι_k` is a homomorphism of vertex superalgebras into the Drinfeld–Sokolov complex**:
every mode is intertwined, `ι(a)₍ₙ₎ι(x) = ι(a₍ₙ₎x)`, for the tensor vertex operator `tenY` of
`Core/TensorVOA`.  No hypothesis beyond `k + 2 ≠ 0` (which is what makes `V^k(𝔰𝔩₂)` exist in
this repository); in particular **no `TensorGradingHyp`**. -/
theorem dsEmbed_mode (k : ℂ) (hk : k + 2 ≠ 0) (a : AffineVOA.WakModule k) (n : ℤ)
    (x : AffineVOA.WakModule k) :
    mode (TensorVA.tenY (DSsl2.affSVA k hk) Ghost.bcGhostSVA (dsEmbed k a)) n (dsEmbed k x)
      = dsEmbed k (mode ((AffineVOA.Vir.affineVA k hk).Y a) n x) :=
  unitEmbed_mode (AffineVOA.Vir.affineVA k hk) Ghost.bcGhostSVA a n x

/-- The unshifted (`Y`-index) form of `dsEmbed_mode`. -/
theorem dsEmbed_tenY (k : ℂ) (hk : k + 2 ≠ 0) (a : AffineVOA.WakModule k) (s : ℤ)
    (x : AffineVOA.WakModule k) :
    TensorVA.tenY (DSsl2.affSVA k hk) Ghost.bcGhostSVA (dsEmbed k a) s (dsEmbed k x)
      = dsEmbed k ((AffineVOA.Vir.affineVA k hk).Y a s x) :=
  unitEmbed_tenY (AffineVOA.Vir.affineVA k hk) Ghost.bcGhostSVA a s x

/-- `ι_k` takes the affine vacuum to the vacuum of the complex. -/
@[simp] theorem dsEmbed_vacuum (k : ℂ) (hk : k + 2 ≠ 0) :
    dsEmbed k (DSsl2.affSVA k hk).vacuum
      = (DSsl2.affSVA k hk).vacuum ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum := rfl

/-- **`ι_k` is injective**: `V^k(𝔰𝔩₂)` really is a vertex subalgebra of the Drinfeld–Sokolov
complex, not a quotient of one. -/
theorem dsEmbed_injective (k : ℂ) : Function.Injective (dsEmbed k) :=
  unitEmbed_injective Ghost.bcGhostSVA (by
    show (1 : SympFerm.FockSF) ≠ 0
    exact one_ne_zero)

/-! ## §4  The Drinfeld–Sokolov complex as a super vertex algebra

`TensorGradingHyp` is down to its `finrank` clause after §2, and that clause is **not** a formal
consequence of the axioms: `SuperVertexAlgebra` bounds each factor's weight spaces but says
nothing about how many splittings `h = h₁ + h₂` can contribute.  It *is* dischargeable whenever
both factors have weight support in `ℕ`, which is exactly the situation for
`V^k(𝔰𝔩₂) ⊗ (bc)`: `AffineVOA.gradingZA_positivity` bounds the affine side below by `0`, and the
ghost weights are the natural numbers `ghWeight l`.
-/

section Finrank

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- `tenSub P Q` is the image of `P ⊗ Q` under the inclusion of both factors. -/
theorem tenSub_eq_range (P : Submodule ℂ A) (Q : Submodule ℂ B) :
    TensorVA.tenSub P Q = LinearMap.range (TensorProduct.map P.subtype Q.subtype) := by
  refine le_antisymm ?_ ?_
  · rw [TensorVA.tenSub, Submodule.span_le]
    rintro t ⟨a, ha, b, hb, rfl⟩
    exact ⟨(⟨a, ha⟩ : P) ⊗ₜ[ℂ] (⟨b, hb⟩ : Q), by rw [TensorProduct.map_tmul]; rfl⟩
  · rintro t ⟨u, rfl⟩
    induction u using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul a b =>
        rw [TensorProduct.map_tmul]
        exact TensorVA.tmul_mem_tenSub a.2 b.2
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- A product of finite-dimensional weight spaces is finite-dimensional. -/
theorem tenSub_finiteDimensional (P : Submodule ℂ A) (Q : Submodule ℂ B)
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ Q] :
    FiniteDimensional ℂ (TensorVA.tenSub P Q) := by
  rw [tenSub_eq_range]
  infer_instance

/-- `⊥ ⊗ Q = ⊥`. -/
theorem tenSub_bot_left (Q : Submodule ℂ B) : TensorVA.tenSub (⊥ : Submodule ℂ A) Q = ⊥ := by
  rw [TensorVA.tenSub, Submodule.span_eq_bot]
  rintro t ⟨a, ha, b, _, rfl⟩
  rw [Submodule.mem_bot] at ha
  rw [ha, TensorProduct.zero_tmul]

/-- `P ⊗ ⊥ = ⊥`. -/
theorem tenSub_bot_right (P : Submodule ℂ A) : TensorVA.tenSub P (⊥ : Submodule ℂ B) = ⊥ := by
  rw [TensorVA.tenSub, Submodule.span_eq_bot]
  rintro t ⟨a, _, b, hb, rfl⟩
  rw [Submodule.mem_bot] at hb
  rw [hb, TensorProduct.tmul_zero]

/-- **Weight support in `ℕ`**: the grading vanishes outside the non-negative integers. -/
def NatSupported (G : ℂ → Submodule ℂ A) : Prop :=
  ∀ h : ℂ, (¬ ∃ n : ℕ, (n : ℂ) = h) → G h = ⊥

/-- If a convolution weight `h` is itself not a natural number, no splitting contributes. -/
theorem tenGrading_eq_bot_of_not_nat (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (hV : NatSupported V.grading) (hW : NatSupported W.grading) {h : ℂ}
    (hh : ¬ ∃ n : ℕ, (n : ℂ) = h) : TensorVA.tenGrading V W h = ⊥ := by
  rw [TensorVA.tenGrading, iSup_eq_bot]
  intro h₁
  by_cases h1 : ∃ n : ℕ, (n : ℂ) = h₁
  · obtain ⟨n, rfl⟩ := h1
    rw [hW (h - (n : ℂ)) (by
      rintro ⟨m, hm⟩
      exact hh ⟨n + m, by push_cast; linear_combination hm⟩), tenSub_bot_right]
  · rw [hV h₁ h1, tenSub_bot_left]

/-- **The `finrank` clause of `TensorGradingHyp`, for `ℕ`-supported factors.**  Only the
`N + 1` splittings `h = i + (N − i)` with `0 ≤ i ≤ N` can contribute, and each contributes a
finite-dimensional piece. -/
theorem tenGrading_finiteDimensional_of_natSupported (V : SuperVertexAlgebra A)
    (W : SuperVertexAlgebra B) (hV : NatSupported V.grading) (hW : NatSupported W.grading)
    (h : ℂ) : FiniteDimensional ℂ (TensorVA.tenGrading V W h) := by
  classical
  by_cases hh : ∃ n : ℕ, (n : ℂ) = h
  · obtain ⟨N, rfl⟩ := hh
    set S : Fin (N + 1) → Submodule ℂ (A ⊗[ℂ] B) := fun i =>
      TensorVA.tenSub (V.grading ((i : ℕ) : ℂ)) (W.grading (((N : ℕ) : ℂ) - ((i : ℕ) : ℂ)))
      with hSdef
    haveI hSfin : ∀ i : Fin (N + 1), FiniteDimensional ℂ (S i) := by
      intro i
      haveI := V.finrank ((i : ℕ) : ℂ)
      haveI := W.finrank (((N : ℕ) : ℂ) - ((i : ℕ) : ℂ))
      rw [hSdef]
      exact tenSub_finiteDimensional _ _
    have hle : TensorVA.tenGrading V W ((N : ℕ) : ℂ) ≤ ⨆ i, S i := by
      rw [TensorVA.tenGrading]
      refine iSup_le fun h₁ => ?_
      by_cases h1 : ∃ n : ℕ, (n : ℂ) = h₁
      · obtain ⟨n, rfl⟩ := h1
        by_cases hn : n ≤ N
        · exact le_iSup S (⟨n, by omega⟩ : Fin (N + 1))
        · rw [hW (((N : ℕ) : ℂ) - ((n : ℕ) : ℂ)) (by
            rintro ⟨m, hm⟩
            have hc : ((m + n : ℕ) : ℂ) = ((N : ℕ) : ℂ) := by
              push_cast
              linear_combination hm
            have hNm : m + n = N := by exact_mod_cast hc
            omega), tenSub_bot_right]
          exact bot_le
      · rw [hV h₁ h1, tenSub_bot_left]
        exact bot_le
    exact Submodule.finiteDimensional_of_le hle
  · rw [tenGrading_eq_bot_of_not_nat V W hV hW hh]
    infer_instance

/-- **The one-hypothesis form of `TensorGradingHyp`**: two `ℕ`-supported vertex superalgebras
have a legitimate convolution bigrading, with nothing left to assume. -/
theorem tensorGradingHyp_of_natSupported (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (hV : NatSupported V.grading) (hW : NatSupported W.grading) :
    TensorVA.TensorGradingHyp V W :=
  tensorGradingHyp_of_finrank V W
    (tenGrading_finiteDimensional_of_natSupported V W hV hW)

end Finrank

/-! ### Discharging the hypotheses for the Drinfeld–Sokolov pair -/

/-- A positive-energy ordinary vertex algebra is `ℕ`-supported in the `ℂ`-graded reading:
`gradingC` is `⊥` off the integers, and `⊥` at the negative ones. -/
theorem natSupported_toSuper {A : Type*} [AddCommGroup A] [Module ℂ A] (V : PreVertexAlgebra A)
    (hpos : ∀ n : ℤ, n < 0 → V.grading n = ⊥) : NatSupported V.toSuper.grading := by
  intro h hh
  show V.gradingC h = ⊥
  by_cases hz : ∃ n : ℤ, (n : ℂ) = h
  · obtain ⟨n, rfl⟩ := hz
    rw [V.gradingC_intCast]
    refine hpos n ?_
    by_contra hn
    have hnn : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (by omega)
    exact hh ⟨n.toNat, by exact_mod_cast hnn⟩
  · exact V.gradingC_of_not_int hz

/-- **The affine factor is `ℕ`-supported**: `V^k(𝔰𝔩₂)` is of CFT type, by
`AffineVOA.gradingZA_positivity`. -/
theorem natSupported_affSVA (k : ℂ) (hk : k + 2 ≠ 0) :
    NatSupported (DSsl2.affSVA k hk).grading :=
  natSupported_toSuper (AffineVOA.Vir.affineVA k hk)
    (fun n hn => AffineVOA.gradingZA_positivity k n hn)

/-- **The ghost factor is `ℕ`-supported**: `gradingGh h` is spanned by the words of ghost weight
`h`, and `ghWeight l` is a natural number, so there are no words at all off `ℕ`. -/
theorem natSupported_bcGhostSVA : NatSupported Ghost.bcGhostSVA.grading := by
  intro h hh
  show Ghost.gradingGh h = ⊥
  rw [Ghost.gradingGh, Submodule.span_eq_bot]
  rintro x ⟨l, hl, rfl⟩
  exact absurd ⟨Ghost.ghWeight l, hl⟩ hh

/-- The purely even reading of an ordinary vertex algebra is parity-compatible: its parity
involution is the identity (`DSsl2.parityInvol_toSuper`). -/
theorem parityCompatible_toSuper {A : Type*} [AddCommGroup A] [Module ℂ A] (V : PreVertexAlgebra A) :
    TensorVA.ParityCompatible V.toSuper := by
  intro h u hu
  rw [DSsl2.parityInvol_toSuper V, LinearMap.id_coe, id_eq]
  exact hu

/-- **The ghost system is parity-compatible.**  Each spanning word `stWordSF l` is
parity-homogeneous (parity `= |l| mod 2`, by `SympFerm.stWordSF_mem_evenOdd`), so `(-1)^F` acts
on it by a scalar and cannot move it out of its weight space. -/
theorem parityCompatible_bcGhostSVA : TensorVA.ParityCompatible Ghost.bcGhostSVA := by
  intro h u hu
  have hu' : u ∈ Submodule.span ℂ (SympFerm.stWordSF '' Ghost.ghWtWordsAt h) := hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      have hpar : SympFerm.stWordSF l
          ∈ (TensorVA.parGr Ghost.bcGhostSVA).parity ((l.length : ℕ) : ZMod 2) :=
        SympFerm.stWordSF_mem_evenOdd l
      rw [(TensorVA.parGr Ghost.bcGhostSVA).parityInvol_homog hpar]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hl, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- The convolution bigrading of the Drinfeld–Sokolov pair is legitimate — both clauses of
`TensorGradingHyp` discharged, `iSupIndep` by §2 and `finrank` by `ℕ`-support. -/
theorem dsTensorGradingHyp (k : ℂ) (hk : k + 2 ≠ 0) :
    TensorVA.TensorGradingHyp (DSsl2.affSVA k hk) Ghost.bcGhostSVA :=
  tensorGradingHyp_of_natSupported _ _ (natSupported_affSVA k hk) natSupported_bcGhostSVA

/-- **THE DRINFELD–SOKOLOV COMPLEX** `𝒞^k = V^k(𝔰𝔩₂) ⊗ (bc)`, as a genuine super vertex
algebra: state space `WakModule k ⊗ FockSF`, vertex operator `tenY`, convolution weight and
parity gradings, vacuum `𝟙 ⊗ 𝟙`.  All fifteen vertex-algebra axioms come from
`TensorVA.tensorSVA`; the two hypotheses it carried are discharged above.

This is a bare `SuperVertexAlgebra`, not a `SuperNearVOA`: `Core/TensorVOA` does not build the
conformal layer `ω = ω ⊗ 𝟙 + 𝟙 ⊗ ω`, so the complex has no conformal vector here.  See §5. -/
noncomputable def dsComplex (k : ℂ) (hk : k + 2 ≠ 0) :
    SuperVertexAlgebra (AffineVOA.WakModule k ⊗[ℂ] SympFerm.FockSF) :=
  TensorVA.tensorSVA (DSsl2.affSVA k hk) Ghost.bcGhostSVA
    (parityCompatible_toSuper (AffineVOA.Vir.affineVA k hk)) parityCompatible_bcGhostSVA
    (dsTensorGradingHyp k hk)

@[simp] theorem dsComplex_Y (k : ℂ) (hk : k + 2 ≠ 0) :
    (dsComplex k hk).Y = TensorVA.tenY (DSsl2.affSVA k hk) Ghost.bcGhostSVA := rfl

@[simp] theorem dsComplex_vacuum (k : ℂ) (hk : k + 2 ≠ 0) :
    (dsComplex k hk).vacuum
      = (DSsl2.affSVA k hk).vacuum ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum := rfl

/-- **The morphism, restated inside the complex.**  `ι_k : V^k(𝔰𝔩₂) → 𝒞^k` intertwines
every mode of the *assembled* super vertex algebra `dsComplex k hk` and sends vacuum to vacuum:
`V^k(𝔰𝔩₂)` is a vertex subalgebra of the Drinfeld–Sokolov complex. -/
theorem dsEmbed_smul_dsComplex (k : ℂ) (hk : k + 2 ≠ 0) (a : AffineVOA.WakModule k) (n : ℤ)
    (x : AffineVOA.WakModule k) :
    (dsComplex k hk).smul (dsEmbed k a) n (dsEmbed k x)
      = dsEmbed k ((AffineVOA.Vir.affineVA k hk).smul a n x) :=
  dsEmbed_mode k hk a n x

/-- `ι_k` takes the affine vacuum to the vacuum of `dsComplex k hk`. -/
theorem dsEmbed_vacuum_dsComplex (k : ℂ) (hk : k + 2 ≠ 0) :
    dsEmbed k (AffineVOA.Vir.affineVA k hk).vacuum = (dsComplex k hk).vacuum := rfl

/-! ### The BRST differential lives on the complex -/

/-- **`Q² = 0` on the assembled complex.**  `DSReductionSl2.dsQ_mul_self` proves this for the
charge as an endomorphism of `WakModule k ⊗ FockSF`; since the tensor product carries a super
vertex algebra structure, this is a statement about the Drinfeld–Sokolov complex itself.  The
proof there is honest: `[e_m, e_n] = 0` (no structure constant *and* no level term) and
`{c_j, c_k} = 0`, antisymmetrised over `ℤ × ℤ`. -/
theorem dsQ_sq_on_dsComplex (k : ℂ) (hk : k + 2 ≠ 0) :
    DSsl2.dsQ k hk * DSsl2.dsQ k hk = 0 :=
  DSsl2.dsQ_mul_self k hk

/-- `Q` is the zero mode of the vertex operator of the BRST current `(e + 𝟙) ⊗ c` of the
complex — not a hand-written formula but the honest residue. -/
theorem dsQ_eq_mode_dsComplex (k : ℂ) (hk : k + 2 ≠ 0) :
    DSsl2.dsQ k hk
      = mode ((dsComplex k hk).Y (DSsl2.ePlusOne k ⊗ₜ[ℂ] DSsl2.cGhost)) 0 :=
  (DSsl2.dsQ_eq_mode_tenY k hk).symm

/-! ## §5  How much of `BRSTComplex` the differential satisfies — and the one place it does not

`Core/BRSTCohomology.BRSTComplex` asks for eight fields.  Two are supplied already
(`Q := dsQ`, `Q_sq := dsQ_mul_self`).  `Q_odd` is proved below.  And here is a fact that has
to be recorded plainly, because it changes the shape of the remaining work:

⚠ **`Q_wt` is FALSE for `dsQ` on the convolution grading of `dsComplex`.**

The Drinfeld–Sokolov BRST current is `j = (e + 𝟙) ⊗ c`, and it is **not weight-homogeneous**
for the convolution grading, because `e` and `𝟙` sit at different affine weights:

* `e ⊗ c` has weight `1 + 0 = 1`, so its zero mode preserves the weight;
* `𝟙 ⊗ c` has weight `0 + 0 = 0`, so its zero mode **lowers the weight by one**.

(The ghost weights here are the repository's `λ = 1` assignment, `wt b = 1`, `wt c = 0`; see
`Ghost.ghWt`.)  Both statements are proved below, as `dsQwt_preserves_grading` and
`dsQlow_lowers_grading`, with `dsQ_split` decomposing `Q` into exactly those two halves.

This is the standard Drinfeld–Sokolov phenomenon, not a defect of the formalisation: the BRST
current is homogeneous only for the **improved** conformal weight
`Δ_DS = Δ_sug + Δ_gh − (ρ^∨ | h₀)`, equivalently for the ghost assignment `wt b = 0`,
`wt c = 1` together with the `ρ^∨`-shifted affine grading, under which `e` drops to weight `0`
and `c` rises to weight `1` so that *both* halves of the current sit at weight `1`.  The two
central charges are unaffected (`c_bc(λ) = −2(6λ² − 6λ + 1)` takes the same value `−2` at
`λ = 0` and `λ = 1`), which is why `DSReductionSl2.dsCentralCharge_eq_affine_add_ghost` is
untouched by this.

**Consequence for the plan.**  A `BRSTComplex (dsComplex k hk)` cannot be assembled from
`dsQ` as things stand, *independently* of the `Q_deriv` question: it first needs the improved
grading, which means either regrading `Ghost.bcGhostSVA` at `λ = 0` or building the
`ρ^∨`-shifted conformal vector on the affine factor.  Neither is built here.
-/

/-- The `e`-half of the Drinfeld–Sokolov BRST current: `e = e₍₋₁₎|0⟩`. -/
noncomputable def eState (k : ℂ) : AffineVOA.WakModule k :=
  AffineVOA.J k AffineVOA.colE (-1) (AffineVOA.vacuumA k)

/-- `e + 𝟙` really is the sum of its two halves. -/
theorem ePlusOne_eq_add (k : ℂ) :
    DSsl2.ePlusOne k = eState k + AffineVOA.vacuumA k := rfl

/-- The raising current has affine conformal weight `1`. -/
theorem eState_mem_grading (k : ℂ) (hk : k + 2 ≠ 0) :
    eState k ∈ (DSsl2.affSVA k hk).grading 1 := by
  have h := AffineVOA.J_mem_gradingZA k AffineVOA.colE (-1) 0
    (AffineVOA.vacuumA_mem_gradingZA_zero k)
  rw [show (0 : ℤ) - (-1) = (1 : ℤ) from by ring] at h
  have hc : ((1 : ℤ) : ℂ) = 1 := by norm_num
  have hg : (DSsl2.affSVA k hk).grading 1 = AffineVOA.gradingZA k 1 := by
    show (AffineVOA.Vir.affineVA k hk).gradingC 1 = _
    rw [← hc, (AffineVOA.Vir.affineVA k hk).gradingC_intCast]
    rfl
  rw [hg]
  exact h

/-- The affine vacuum has affine conformal weight `0`. -/
theorem vacuumA_mem_grading (k : ℂ) (hk : k + 2 ≠ 0) :
    AffineVOA.vacuumA k ∈ (DSsl2.affSVA k hk).grading 0 :=
  (DSsl2.affSVA k hk).vacuum_mem

/-- **The ghost `c₍₋₁₎|0⟩` has conformal weight `0`** in the repository's `λ = 1` ghost
system (`wt c = 1 − λ = 0`).  This is the source of the inhomogeneity of the BRST current. -/
theorem cGhost_mem_grading : DSsl2.cGhost ∈ Ghost.bcGhostSVA.grading 0 := by
  have h := Ghost.stWordSF_mem_gradingGh [((0, 1) : ℕ × Fin 2)]
  rwa [show Ghost.ghWeight [((0, 1) : ℕ × Fin 2)] = 0 from rfl, Nat.cast_zero] at h

/-- The ghost `c₍₋₁₎|0⟩` is **odd**: it is a word of length one. -/
theorem cGhost_mem_parity : DSsl2.cGhost ∈ Ghost.bcGhostSVA.parity 1 := by
  have h := SympFerm.stWordSF_mem_evenOdd [((0, 1) : ℕ × Fin 2)]
  rwa [show (([((0, 1) : ℕ × Fin 2)].length : ℕ) : ZMod 2) = 1 from by decide] at h

/-- Everything in a purely even vertex algebra is even. -/
theorem mem_parity_zero_toSuper {A : Type*} [AddCommGroup A] [Module ℂ A] (V : PreVertexAlgebra A)
    (u : A) : u ∈ V.toSuper.parity 0 := by
  show u ∈ (ParityGrading.even A).parity 0
  rw [ParityGrading.even_parity_zero]
  exact Submodule.mem_top

/-- The weight-preserving half of `Q`, `Q₀ = ∮ c(z)e(z)`. -/
noncomputable def dsQwt (k : ℂ) (hk : k + 2 ≠ 0) :
    End ℂ (AffineVOA.WakModule k ⊗[ℂ] SympFerm.FockSF) :=
  TensorVA.rawCoeff (DSsl2.affSVA k hk) Ghost.bcGhostSVA (eState k) DSsl2.cGhost (-1)

/-- The weight-lowering half of `Q`, `Q₋₁ = ∮ c(z)`. -/
noncomputable def dsQlow (k : ℂ) (hk : k + 2 ≠ 0) :
    End ℂ (AffineVOA.WakModule k ⊗[ℂ] SympFerm.FockSF) :=
  TensorVA.rawCoeff (DSsl2.affSVA k hk) Ghost.bcGhostSVA (AffineVOA.vacuumA k) DSsl2.cGhost (-1)

/-- **The BRST charge splits into a weight-preserving and a weight-lowering half.** -/
theorem dsQ_split (k : ℂ) (hk : k + 2 ≠ 0) :
    DSsl2.dsQ k hk = dsQwt k hk + dsQlow k hk := by
  rw [DSsl2.dsQ, dsQwt, dsQlow, ePlusOne_eq_add, TensorVA.rawCoeff_add_left]

/-- `rawCoeff … (−1)` on a pure tensor is the zero mode of the tensor vertex operator. -/
theorem rawCoeff_neg_one_eq_mode (k : ℂ) (hk : k + 2 ≠ 0) (a : AffineVOA.WakModule k)
    (b : SympFerm.FockSF) :
    TensorVA.rawCoeff (DSsl2.affSVA k hk) Ghost.bcGhostSVA a b (-1)
      = mode ((dsComplex k hk).Y (a ⊗ₜ[ℂ] b)) 0 := by
  rw [mode_apply, show (-(0 : ℤ) - 1) = -1 from by ring]
  exact (DSsl2.tenY_tmul_toSuper (AffineVOA.Vir.affineVA k hk) Ghost.bcGhostSVA a b (-1)).symm

/-- **`Q₀` preserves the conformal weight**: the current `e ⊗ c` sits at weight `1`, so its
zero mode has weight `0`.  This is the half of `Q` for which `BRSTComplex.Q_wt` does hold. -/
theorem dsQwt_preserves_grading (k : ℂ) (hk : k + 2 ≠ 0) (h : ℂ) (v : _)
    (hv : v ∈ (dsComplex k hk).grading h) : dsQwt k hk v ∈ (dsComplex k hk).grading h := by
  have hj : eState k ⊗ₜ[ℂ] DSsl2.cGhost ∈ (dsComplex k hk).grading 1 := by
    refine TensorVA.tmul_mem_tenGrading _ _ (h₁ := 1) (eState_mem_grading k hk) ?_
    rw [sub_self]
    exact cGhost_mem_grading
  have hmode := (dsComplex k hk).grading_mode _ hj v hv 0
  rw [dsQwt, rawCoeff_neg_one_eq_mode]
  rwa [show (1 : ℂ) + h - ((0 : ℤ) : ℂ) - 1 = h from by push_cast; ring] at hmode

/-- ⚠ **`Q₋₁` lowers the conformal weight by one**: the current `𝟙 ⊗ c` sits at weight `0`, so
its zero mode has weight `−1`.  This is why `BRSTComplex.Q_wt` fails for `dsQ` on the
convolution grading, and why the improved Drinfeld–Sokolov grading is needed. -/
theorem dsQlow_lowers_grading (k : ℂ) (hk : k + 2 ≠ 0) (h : ℂ) (v : _)
    (hv : v ∈ (dsComplex k hk).grading h) : dsQlow k hk v ∈ (dsComplex k hk).grading (h - 1) := by
  have hj : AffineVOA.vacuumA k ⊗ₜ[ℂ] DSsl2.cGhost ∈ (dsComplex k hk).grading 0 := by
    refine TensorVA.tmul_mem_tenGrading _ _ (h₁ := 0) (vacuumA_mem_grading k hk) ?_
    rw [sub_self]
    exact cGhost_mem_grading
  have hmode := (dsComplex k hk).grading_mode _ hj v hv 0
  rw [dsQlow, rawCoeff_neg_one_eq_mode]
  rwa [show (0 : ℂ) + h - ((0 : ℤ) : ℂ) - 1 = h - 1 from by push_cast; ring] at hmode

/-- **`BRSTComplex.Q_odd` holds**: the Drinfeld–Sokolov differential is odd, because the
BRST current `(e + 𝟙) ⊗ c` is odd (the affine factor is purely even, and `c` is a length-one
ghost word).  This is one of the eight fields of `BRSTComplex`, discharged. -/
theorem dsQ_odd (k : ℂ) (hk : k + 2 ≠ 0) (p : ZMod 2) (v : _)
    (hv : v ∈ (dsComplex k hk).parity p) :
    DSsl2.dsQ k hk v ∈ (dsComplex k hk).parity (p + 1) := by
  have hj : DSsl2.ePlusOne k ⊗ₜ[ℂ] DSsl2.cGhost ∈ (dsComplex k hk).parity 1 := by
    refine TensorVA.tmul_mem_tenParity _ _ (p₁ := 0)
      (mem_parity_zero_toSuper (AffineVOA.Vir.affineVA k hk) _) ?_
    rw [sub_zero]
    exact cGhost_mem_parity
  have hmode := (dsComplex k hk).parity_mode _ hj v hv 0
  rw [dsQ_eq_mode_dsComplex]
  rwa [add_comm (1 : ZMod 2) p] at hmode

/-- **The vacuum of the Drinfeld–Sokolov complex is BRST-closed**, `Q(𝟙 ⊗ 𝟙) = 0`.

`Core/BRSTCohomology.Q_vacuum` derives this from the `BRSTComplex` axioms; since those cannot
be instantiated here (see the `Q_wt` obstruction above), it is proved directly, and it needs
nothing but the creation axiom on each factor.  Every term `((e+𝟙)₍ₘ₎𝟙) ⊗ (c₍₋₁₋ₘ₎𝟙)` of the
convolution dies: the ghost factor for `m ≥ 0`, the affine factor for `m < 0`. -/
theorem dsQ_vacuum (k : ℂ) (hk : k + 2 ≠ 0) :
    DSsl2.dsQ k hk (dsComplex k hk).vacuum = 0 := by
  rw [dsComplex_vacuum, DSsl2.dsQ_tmul]
  have hz : ∀ m : ℤ,
      ((DSsl2.affSVA k hk).Y (DSsl2.ePlusOne k) m (DSsl2.affSVA k hk).vacuum)
        ⊗ₜ[ℂ] (Ghost.bcGhostSVA.Y DSsl2.cGhost (-1 - m) Ghost.bcGhostSVA.vacuum)
      = (0 : AffineVOA.WakModule k ⊗[ℂ] SympFerm.FockSF) := by
    intro m
    rcases le_or_gt 0 m with hm | hm
    · have hgh : Ghost.bcGhostSVA.Y DSsl2.cGhost (-1 - m) Ghost.bcGhostSVA.vacuum = 0 := by
        have h := (Ghost.bcGhostSVA.creation DSsl2.cGhost).2 (-(-1 - m) - 1) (by omega)
        rwa [mode_apply, show -(-(-1 - m) - 1) - 1 = -1 - m from by ring] at h
      rw [hgh, TensorProduct.tmul_zero]
    · have haf : (DSsl2.affSVA k hk).Y (DSsl2.ePlusOne k) m (DSsl2.affSVA k hk).vacuum = 0 := by
        have h := ((DSsl2.affSVA k hk).creation (DSsl2.ePlusOne k)).2 (-m - 1) (by omega)
        rwa [mode_apply, show -(-m - 1) - 1 = m from by ring] at h
      rw [haf, TensorProduct.zero_tmul]
  rw [finsum_congr hz, finsum_zero]

end VOA.DSMor
