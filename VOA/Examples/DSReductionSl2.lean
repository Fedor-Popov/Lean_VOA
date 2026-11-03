/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.TensorVOA
import VOA.Core.BRSTCohomology
import VOA.Core.ScreeningKernel
import VOA.Examples.AffineSl2Virasoro
import VOA.Examples.GhostSystem
import VOA.Examples.FreeBosonGeneralC

/-!
# Drinfeld–Sokolov reduction for `𝔰𝔩₂`, by both routes

`W^k(𝔰𝔩₂, f_prin)` is the Virasoro vertex algebra at

  `c(k) = 13 − 6(k+2) − 6/(k+2)`,

and at the admissible level `k = −2 + p/q` this is the `(p,q)` minimal-model central charge
`1 − 6(p−q)²/(pq)`.  Two constructions produce it:

* **Route 1 (BRST / quantum Hamiltonian reduction).**  `W^k = H⁰_{BRST}(V^k(𝔰𝔩₂) ⊗ Ghosts)`.
  For `𝔰𝔩₂` with the principal nilpotent `f`, `𝔤_{>0} = ℂe` is one-dimensional and there are
  no neutral fermions, so the ghost sector is a **single** `bc` pair.
* **Route 2 (screening / Feigin–Frenkel).**  `W^k` is the kernel of one screening operator
  inside a rank-`1` Heisenberg algebra carrying a background charge.

This file builds as much of each as the current foundations support and says precisely where
each one stops.  Nothing here is a theorem with a hole: every unproved statement is carried
either as an explicit hypothesis or as a `def … : Prop`.

## What is proved

### §1 Arithmetic (complete)

* `dsCentralCharge k = 13 − 6(k+2) − 6/(k+2)` — the target central charge, as a **definition**
  (targets **c** and the `c`-half of **f**).
* `dsCentralCharge_eq_minimalModel` — at `k = −2 + p/q`,
  `13 − 6(k+2) − 6/(k+2) = 1 − 6(p−q)²/(pq)`.  This is the identity target **f** asks for
  "regardless"; `dsCentralCharge_ising` and `dsCentralCharge_leeYang` are the `(3,4)` and
  `(2,5)` instances.
* `dsCentralCharge_eq_affine_add_ghost` — the **BRST anomaly count**
  `c_W = c_{𝔰𝔩₂,k} + c_{bc} − 12 k ⟨ρ^∨,ρ^∨⟩`, stated against the *actual repository objects*
  `(affineSl2VOA_closed k hk).centralCharge = 3k/(k+2)` and `Ghost.ghostCentralCharge 1 = −2`,
  with `⟨ρ^∨,ρ^∨⟩ = κ(h,h)/4 = 1/2` read off `AffineVOA.kappa`.  This is a genuine
  cross-check that Route 1 can only give the stated answer.
* `one_sub_twelve_bgChargeSq` — `1 − 12 λ² = c(k)` for `λ² = ((k+2) + (k+2)⁻¹ − 2)/2`, and
  `exists_bgCharge`.
* `dsCentralCharge_dual` — **Feigin–Frenkel level duality** `t ↦ 1/t` (`k ↦ −2 + (k+2)⁻¹`)
  fixes `c(k)`, matching `minimalModelCentralCharge_symm` (`(p,q) ↦ (q,p)`).

### §2 Route 2, the free-field side

`Examples/FreeBosonGeneralC` supplies exactly the object
`Core/ScreeningKernel` was missing: `FBgc.freeBosonVOA lam : VertexOperatorAlgebra Fock`, the
linear-dilaton free boson whose conformal vector is `ω^λ = ω − λ a₋₂|0⟩` and whose central
charge is `1 − 12λ²`.  Hence:

* `dsFreeBoson_centralCharge` — for `λ² = bgChargeSq k` the free boson sits at exactly
  `dsCentralCharge k`.
* `dsScreeningSl2` / `dsScreeningSl2_centralCharge` — the screening-kernel VOA of any
  weight-one state of that free boson, **with central charge `dsCentralCharge k`**, and
  `dsScreeningSl2_conformalVector_mem`: it contains the Virasoro vector `ω^λ`.  Together
  these are target **f** for the screening route, modulo the caveat in §5 below.
* `IsScreeningMomentum`, `screeningMomentum_sum`, `screeningMomentum_mul`,
  `bgCharge_of_screening_pair`, `exists_screening_pair` — the momenta `α±` of the two
  weight-one vertex operators: `α₊α₋ = −2`, `α₊ + α₋ = −2λ`, `α₊² = 2(k+2)`, and the
  background charge is recovered as `λ = −(α₊+α₋)/2`.

### §3–§4 Route 1, BRST

* `rawCoeff_mul_self_eq_zero` — the abstract nilpotency theorem.  If the coefficients of
  `Y_A(a,z)` **commute** with one another and those of `Y_B(b,z)` **anticommute**, then every
  coefficient `∑_m a_m ⊗ b_{s−m}` of the naive tensor field squares to zero.  Proved by an
  antisymmetrisation over `ℤ × ℤ`: the swap `(m,n) ↦ (n,m)` negates the summand, and the two
  hypotheses are exactly what makes the double support finite (each of the four bounds needs
  one of them).
* `dsQ k hk` — the BRST charge, **derived** rather than quoted: it is
  `TensorVA.rawCoeff (V^k(𝔰𝔩₂)) (bc) (e + 𝟙) c (−1)`, and `dsQ_eq_mode_tenY` proves this is
  literally `mode (Y((e + 𝟙) ⊗ c, z)) 0` for D1's tensor-product vertex operator.
* `dsQ_mul_self` — **`Q² = 0`**.  The two inputs are `J_colE_comm`
  (`[e_m, e_n] = 0`, because `f^{ee}{}_c = 0` **and** `κ(e,e) = 0` in `AffineSl2.fabc`/`kappa`
  — the second is why the level drops out) and `Ghost.cc_anticomm` (`{c_j, c_k} = 0`).
* `dsReductionSl2` — `H⁰` of a BRST complex pinned to this differential by
  `IsDSComplexSl2`.

### §5 What blocks each route (both honest, neither forced)

**Route 1.**  `Q² = 0` is done, and it is the crux.  What is *not* done is assembling a
`BRST.BRSTComplex`, which additionally needs `Q_deriv` — the super Leibniz rule
`Q(u₍ₙ₎v) = (Qu)₍ₙ₎v + (−1)^{|u|}u₍ₙ₎(Qv)`.  That is the `ℓ = 0` slice of a **super**
Borcherds/commutator formula.  The library has both: the super Jacobi identity
`superJacobi` and its `ℓ = 0` slice `commBoundε` (`Core/SuperBorcherds.lean`), and unconditional
super skew-symmetry `superSmul_eq_skew_Lpow` (`Modularity/SuperZhuCommutator.lean`; the older
`Core/SuperSkew.skew_modeε` route is still stated conditionally on `WeakAssocLocε`).  What is
missing is deriving `Q_deriv` for this `Q` from them; that has not been done.  Independently, `TensorVA.tensorSVA` still needs
`TensorGradingHyp.iSupIndep` and `.finrank` (D1's two open clauses).  Both are carried as
hypotheses here, never as holes.

**Route 2.**  The screening machine is fully assembled and has the right central charge, but
the *specific* DS screening state is not available: the genuine screening charge is
`∮ e^{α₊φ}`, and `Fock` is the **zero-momentum** Heisenberg vacuum module, which contains no
vertex operator `e^{αφ}` at all.  Its weight-one space is spanned by `a₋₁|0⟩`, whose zero mode
is `a₀ = 0` (`osc 1 0 = 0`, a definitional feature of the model), so every screening operator
actually available inside `Fock` is the zero operator and its kernel is everything.  The
missing object is the **momentum extension** — the Fock modules `F_α` of nonzero momentum, or
equivalently a lattice VOA carrying the deformed conformal vector `ω^λ` rather than the
undeformed one.  §2 records the momenta `α±` that the missing states must carry, so the
instantiation is a one-line substitution once such a module exists.

**Both.**  `RoutesAgreeSl2` records — as a `Prop`, deliberately unproved — that the two
constructions produce isomorphic vertex superalgebras.  That is the Feigin–Frenkel comparison
theorem, a research statement (target **g**).

## Dependencies

`Core/TensorVOA` (D1: `rawCoeff`, `tenY`), `Core/BRSTCohomology` (D2: `BRSTComplex`, `H0`),
`Core/ScreeningKernel` (D4), `Examples/GhostSystem` (D3: `bcGhostSVA`, `cc_anticomm`),
`Examples/AffineSl2Virasoro` (`affineVA`, `affineSl2VOA_closed`, `YA_current_state`),
`Examples/FreeBosonGeneralC` (`freeBosonVOA`).
-/

namespace VOA.DSsl2

open scoped TensorProduct
open Module (End)

/-! ## §1  The central charge of `W^k(𝔰𝔩₂, f_prin)`

Everything in this section is an identity in `ℂ`; none of it depends on any vertex-algebra
structure, and all of it is proved.
-/

/-- **The Drinfeld–Sokolov central charge for `𝔰𝔩₂`**, `c(k) = 13 − 6(k+2) − 6/(k+2)`.

Recorded as a *definition*, per target **c**: that the BRST cohomology actually carries this
central charge is a further theorem, not claimed here. -/
noncomputable def dsCentralCharge (k : ℂ) : ℂ := 13 - 6 * (k + 2) - 6 / (k + 2)

/-- **The `(p,q)` minimal-model central charge** `1 − 6(p−q)²/(pq)`. -/
noncomputable def minimalModelCentralCharge (p q : ℂ) : ℂ := 1 - 6 * (p - q) ^ 2 / (p * q)

/-- **The admissible-level identity** (target **f**).  At `k = −2 + p/q`,

  `13 − 6(k+2) − 6/(k+2) = 1 − 6(p−q)²/(pq)`,

i.e. the Drinfeld–Sokolov central charge at an admissible level is exactly the `(p,q)`
minimal-model central charge.  This is the arithmetic bridge between the `W`-algebra route
and the minimal models the project builds as simple quotients. -/
theorem dsCentralCharge_eq_minimalModel {p q : ℂ} (hp : p ≠ 0) (hq : q ≠ 0) :
    dsCentralCharge (-2 + p / q) = minimalModelCentralCharge p q := by
  have hpq : p / q ≠ 0 := div_ne_zero hp hq
  have h : (-2 + p / q) + 2 = p / q := by ring
  rw [dsCentralCharge, h, minimalModelCentralCharge]
  field_simp
  try ring

/-- **Sanity check `(p,q) = (3,4)`**: the Ising model, `c = 1/2`. -/
theorem dsCentralCharge_ising : dsCentralCharge (-2 + 3 / 4) = 1 / 2 := by
  rw [dsCentralCharge]; norm_num

/-- **Sanity check `(p,q) = (2,5)`**: the Lee–Yang model, `c = −22/5`. -/
theorem dsCentralCharge_leeYang : dsCentralCharge (-2 + 2 / 5) = -22 / 5 := by
  rw [dsCentralCharge]; norm_num

/-- **Sanity check `(p,q) = (2,3)`**: the trivial model, `c = 0`. -/
theorem dsCentralCharge_trivial : dsCentralCharge (-2 + 2 / 3) = 0 := by
  rw [dsCentralCharge]; norm_num

/-- **Feigin–Frenkel duality, at the level of central charges.**  `c(k) = 13 − 6t − 6/t`
with `t = k+2` is invariant under `t ↦ 1/t`, i.e. under `k ↦ −2 + (k+2)⁻¹`.  This is the
level-duality `W^k(𝔰𝔩₂) ≅ W^{k^∨}(𝔰𝔩₂)` seen numerically; on the minimal-model side it is
the exchange `(p,q) ↦ (q,p)` (`minimalModelCentralCharge_symm`). -/
theorem dsCentralCharge_dual (k : ℂ) :
    dsCentralCharge (-2 + (k + 2)⁻¹) = dsCentralCharge k := by
  have h : (-2 + (k + 2)⁻¹) + 2 = (k + 2)⁻¹ := by ring
  rw [dsCentralCharge, dsCentralCharge, h, div_eq_mul_inv, inv_inv, div_eq_mul_inv]
  ring

/-- The minimal-model central charge is symmetric in `(p,q)` — the shadow of
`dsCentralCharge_dual`. -/
theorem minimalModelCentralCharge_symm (p q : ℂ) :
    minimalModelCentralCharge p q = minimalModelCentralCharge q p := by
  rw [minimalModelCentralCharge, minimalModelCentralCharge,
    show (q - p) ^ 2 = (p - q) ^ 2 from by ring, mul_comm q p]

/-! ### The BRST anomaly count

The Drinfeld–Sokolov stress tensor is the Sugawara one twisted by `∂(ρ^∨ · J)`, which shifts
the central charge by `−12 k ⟨ρ^∨,ρ^∨⟩`; adding the `bc` ghost contribution `−2` must then
land on `c(k)`.  For `𝔰𝔩₂`, `ρ^∨ = h/2` and `⟨ρ^∨,ρ^∨⟩ = κ(h,h)/4 = 1/2`.
-/

/-- `⟨ρ^∨,ρ^∨⟩` for `𝔰𝔩₂` with the normalised Killing form: `ρ^∨ = h/2`, so this is
`κ(h,h)/4`, read directly off `AffineVOA.kappa`. -/
noncomputable def rhoCheckNormSq : ℂ := AffineVOA.kappa AffineVOA.colH AffineVOA.colH / 4

theorem rhoCheckNormSq_eq : rhoCheckNormSq = 1 / 2 := by
  have h : AffineVOA.kappa AffineVOA.colH AffineVOA.colH = 2 := rfl
  rw [rhoCheckNormSq, h]
  norm_num

/-- The bare arithmetic of the anomaly count: `13 − 6t − 6/t = 3k/t − 2 − 6k` for `t = k+2`. -/
theorem dsCentralCharge_eq_count (k : ℂ) (hk : k + 2 ≠ 0) :
    dsCentralCharge k = 3 * k / (k + 2) + (-2) - 12 * k * (1 / 2) := by
  rw [dsCentralCharge]
  field_simp
  try ring

/-- **The BRST anomaly count against the actual repository objects.**

  `c_W(k) = c(𝒱(𝔰𝔩₂,k)) + c(bc at λ=1) − 12 k ⟨ρ^∨,ρ^∨⟩`,

with `c(𝒱(𝔰𝔩₂,k)) = 3k/(k+2)` from `affineSl2VOA_closed_central_charge`, `c(bc) = −2` from
`Ghost.ghostCentralCharge_one`, and `⟨ρ^∨,ρ^∨⟩ = 1/2` from `AffineVOA.kappa`.  Route 1 can
therefore only produce `dsCentralCharge k`. -/
theorem dsCentralCharge_eq_affine_add_ghost (k : ℂ) (hk : k + 2 ≠ 0) :
    dsCentralCharge k
      = (AffineVOA.affineSl2VOA_closed k hk).centralCharge
        + Ghost.ghostCentralCharge 1 - 12 * k * rhoCheckNormSq := by
  rw [AffineVOA.affineSl2VOA_closed_central_charge, Ghost.ghostCentralCharge_one,
    rhoCheckNormSq_eq]
  exact dsCentralCharge_eq_count k hk

/-! ### The background charge -/

/-- **The square of the Drinfeld–Sokolov background charge** at level `k`:
`λ² = ((k+2) + (k+2)⁻¹ − 2)/2`, i.e. `λ = (√t − 1/√t)/√2` with `t = k+2`.

Stated as the *square* so that no choice of square root enters a definition. -/
noncomputable def bgChargeSq (k : ℂ) : ℂ := ((k + 2) + (k + 2)⁻¹ - 2) / 2

/-- `1 − 12λ² = 13 − 6(k+2) − 6/(k+2)` for the Drinfeld–Sokolov background charge:
the free boson at background charge `λ` is at exactly the `W`-algebra central charge. -/
theorem one_sub_twelve_bgChargeSq (k : ℂ) (hk : k + 2 ≠ 0) :
    1 - 12 * bgChargeSq k = dsCentralCharge k := by
  rw [bgChargeSq, dsCentralCharge]
  field_simp
  try ring

/-- A background charge realising `dsCentralCharge k` exists (solve `λ² = bgChargeSq k`
over the algebraically closed field `ℂ`). -/
theorem exists_bgCharge (k : ℂ) : ∃ lam : ℂ, lam ^ 2 = bgChargeSq k :=
  IsAlgClosed.exists_pow_nat_eq (bgChargeSq k) (n := 2) (by norm_num)

/-! ## §2  Route 2 — the free boson with the Drinfeld–Sokolov background charge

`Examples/FreeBosonGeneralC.freeBosonVOA lam` is the rank-`1` Heisenberg vertex algebra on
`Fock` re-graded by the linear-dilaton conformal vector `ω^λ = ω − λ a₋₂|0⟩`, with central
charge `1 − 12λ²`.  Setting `λ² = bgChargeSq k` puts it at `dsCentralCharge k`.
-/

/-- **The free boson at the Drinfeld–Sokolov background charge has central charge
`13 − 6(k+2) − 6/(k+2)`.** -/
theorem dsFreeBoson_centralCharge {k lam : ℂ} (hk : k + 2 ≠ 0) (hlam : lam ^ 2 = bgChargeSq k) :
    (FBgc.freeBosonVOA lam).centralCharge = dsCentralCharge k := by
  rw [FBgc.freeBosonVOA_centralCharge, hlam]
  exact one_sub_twelve_bgChargeSq k hk

/-- The screening-kernel VOA inside the Drinfeld–Sokolov free boson, for a weight-one state
`a`.  This is `dsScreeningSl2` of target **e**: `Screening.screeningKernelVOA` applied to the
background-charge free boson.

The state `a` is left as a parameter on purpose — see §5 and the module docstring: the
genuine Drinfeld–Sokolov screening state `e^{α₊φ}` carries nonzero momentum and therefore does
not live in the zero-momentum Fock space `Fock`.  Everything downstream of the choice of `a`
is proved. -/
noncomputable def dsScreeningSl2 (lam : ℂ) (a : Fock)
    (ha : a ∈ (FBgc.freeBosonVOA lam).grading 1) :
    VertexOperatorAlgebra (Screening.screeningKernel (FBgc.freeBosonVOA lam) a ha).carrier :=
  Screening.screeningKernelVOA (FBgc.freeBosonVOA lam) a ha

/-- **Target f for the screening route.**  The screening kernel inside the
background-charge free boson is a VOA of central charge exactly
`13 − 6(k+2) − 6/(k+2)`. -/
theorem dsScreeningSl2_centralCharge {k lam : ℂ} (hk : k + 2 ≠ 0) (hlam : lam ^ 2 = bgChargeSq k)
    (a : Fock) (ha : a ∈ (FBgc.freeBosonVOA lam).grading 1) :
    (dsScreeningSl2 lam a ha).centralCharge = dsCentralCharge k := by
  rw [dsScreeningSl2, Screening.screeningKernelVOA_centralCharge]
  exact dsFreeBoson_centralCharge hk hlam

/-- The Virasoro vector realising that central charge lies **inside** the screening kernel:
`Q_a ω^λ = 0` for every weight-one `a` (`Screening.screening_conformalVector`). -/
theorem dsScreeningSl2_conformalVector_mem (lam : ℂ) (a : Fock)
    (ha : a ∈ (FBgc.freeBosonVOA lam).grading 1) :
    (FBgc.freeBosonVOA lam).conformalVector
      ∈ (Screening.screeningKernel (FBgc.freeBosonVOA lam) a ha).carrier :=
  Screening.conformalVector_mem_screeningKernel _ _ _

/-! ### The screening momenta `α±`

The linear-dilaton weight of a momentum-`α` vertex operator is
`L₀^λ = L₀ + λ a₀ ↦ α²/2 + λα` (the repo convention is `Lld λ n = Lᵥᵢᵣ n + λ(n+1)aₙ`,
so `L₀^λ = L₀ + λ a₀`, and on a momentum-`α` state `a₀ = α`, `L₀ = α²/2`).  Requiring weight
`1` gives the two Feigin–Fuks screening momenta.
-/

/-- The linear-dilaton conformal weight of the momentum-`α` vertex operator: `α²/2 + λα`. -/
noncomputable def vertexWeight (lam alpha : ℂ) : ℂ := alpha ^ 2 / 2 + lam * alpha

/-- `α` is a **screening momentum** for background charge `λ` when `e^{αφ}` has weight `1`. -/
def IsScreeningMomentum (lam alpha : ℂ) : Prop := vertexWeight lam alpha = 1

theorem isScreeningMomentum_iff (lam alpha : ℂ) :
    IsScreeningMomentum lam alpha ↔ alpha ^ 2 + 2 * lam * alpha - 2 = 0 := by
  rw [IsScreeningMomentum, vertexWeight]
  constructor
  · intro h; linear_combination 2 * h
  · intro h; linear_combination h / 2

/-- The two screening momenta sum to `−2λ` (Vieta). -/
theorem screeningMomentum_sum {lam a b : ℂ} (ha : IsScreeningMomentum lam a)
    (hb : IsScreeningMomentum lam b) (hab : a ≠ b) : a + b = -2 * lam := by
  rw [isScreeningMomentum_iff] at ha hb
  have hsub : (a - b) * (a + b + 2 * lam) = 0 := by linear_combination ha - hb
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (sub_eq_zero.mp h) hab
  · linear_combination h

/-- The two screening momenta multiply to `−2`: `α₊α₋ = −2`. -/
theorem screeningMomentum_mul {lam a b : ℂ} (ha : IsScreeningMomentum lam a)
    (hb : IsScreeningMomentum lam b) (hab : a ≠ b) : a * b = -2 := by
  have hsum := screeningMomentum_sum ha hb hab
  rw [isScreeningMomentum_iff] at ha
  linear_combination -ha + a * hsum

/-- **The Drinfeld–Sokolov screening pair.**  If `α₊² = 2(k+2)` and `α₊α₋ = −2`, then
`λ := −(α₊+α₋)/2` is a background charge with `λ² = bgChargeSq k`, and **both** `α₊` and `α₋`
are screening momenta for it.  (Concretely `α₊ = √(2t)`, `α₋ = −√(2/t)` with `t = k+2`.) -/
theorem bgCharge_of_screening_pair {k ap am : ℂ} (hk : k + 2 ≠ 0)
    (hp : ap ^ 2 = 2 * (k + 2)) (hprod : ap * am = -2) :
    (-(ap + am) / 2) ^ 2 = bgChargeSq k
      ∧ IsScreeningMomentum (-(ap + am) / 2) ap
      ∧ IsScreeningMomentum (-(ap + am) / 2) am := by
  have hinv : (k + 2) * (k + 2)⁻¹ = 1 := mul_inv_cancel₀ hk
  have hamsq : (k + 2) * am ^ 2 = 2 := by
    have h0 : (ap * am) ^ 2 = 4 := by rw [hprod]; norm_num
    have h2 : (2 * (k + 2)) * am ^ 2 = 4 := by rw [← hp]; linear_combination h0
    linear_combination h2 / 2
  refine ⟨?_, ?_, ?_⟩
  · rw [bgChargeSq]
    refine mul_left_cancel₀ hk ?_
    have e1 : (k + 2) * ((-(ap + am) / 2) ^ 2)
        = ((k + 2) * ap ^ 2 + 2 * (k + 2) * (ap * am) + (k + 2) * am ^ 2) / 4 := by ring
    have e2 : (k + 2) * (((k + 2) + (k + 2)⁻¹ - 2) / 2)
        = ((k + 2) ^ 2 + (k + 2) * (k + 2)⁻¹ - 2 * (k + 2)) / 2 := by ring
    rw [e1, e2, hp, hprod, hamsq, hinv]
    ring
  · rw [isScreeningMomentum_iff]
    linear_combination -hprod
  · rw [isScreeningMomentum_iff]
    linear_combination -hprod

/-- A Drinfeld–Sokolov screening pair exists for every level with `k + 2 ≠ 0`. -/
theorem exists_screening_pair (k : ℂ) (hk : k + 2 ≠ 0) :
    ∃ ap am : ℂ, ap ^ 2 = 2 * (k + 2) ∧ ap * am = -2 := by
  obtain ⟨ap, hap⟩ := IsAlgClosed.exists_pow_nat_eq (2 * (k + 2)) (n := 2) (by norm_num)
  have hap0 : ap ≠ 0 := by
    intro h
    have hz : (0 : ℂ) = 2 * (k + 2) := by rw [← hap, h]; ring
    exact hk (by linear_combination -hz / 2)
  refine ⟨ap, -2 / ap, hap, ?_⟩
  field_simp

/-! ## §3  The abstract nilpotency theorem for a tensor BRST charge

D1's `TensorVA.rawCoeff V W a b s` is the sign-free coefficient

  `(x ⊗ y) ↦ ∑ᶠ m, (a₍ₘ₎x) ⊗ (b₍ₛ₋ₘ₎y)`

of the naive product `Y_A(a,z) ⊗ Y_B(b,z)` (finite by lower truncation).  When the first
factor is purely even this is *literally* the tensor-product vertex operator (§4), so the
BRST charge of any complex of the shape `V ⊗ (ghosts)` is one of these coefficients.

The theorem below says such a coefficient squares to zero as soon as `Y_A(a,z)` has mutually
commuting coefficients and `Y_B(b,z)` has mutually anticommuting ones.  That is exactly the
structure of the `𝔰𝔩₂` complex: `[e_m, e_n] = 0` (no structure constant *and* no level term,
since `κ(e,e) = 0`), and `{c_j, c_k} = 0` (the `bc` system has no `cc` contraction).
-/

section AbstractSquare

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- The coefficients of `Y(a,z)` commute with one another. -/
def CoeffCommute (V : SuperVertexAlgebra A) (a : A) : Prop :=
  ∀ i j : ℤ, V.Y a i * V.Y a j = V.Y a j * V.Y a i

/-- The coefficients of `Y(b,z)` anticommute with one another. -/
def CoeffAnticommute (W : SuperVertexAlgebra B) (b : B) : Prop :=
  ∀ i j : ℤ, W.Y b i * W.Y b j + W.Y b j * W.Y b i = 0

variable (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)

/-- Pointwise form of `CoeffCommute`. -/
theorem coeffCommute_apply {a : A} (hA : CoeffCommute V a) (i j : ℤ) (w : A) :
    V.Y a i (V.Y a j w) = V.Y a j (V.Y a i w) := by
  have h := congrArg (fun T : End ℂ A => T w) (hA i j)
  simpa only [Module.End.mul_apply] using h

/-- Pointwise form of `CoeffAnticommute`. -/
theorem coeffAnticommute_apply {b : B} (hB : CoeffAnticommute W b) (i j : ℤ) (w : B) :
    W.Y b i (W.Y b j w) = -(W.Y b j (W.Y b i w)) := by
  have h := congrArg (fun T : End ℂ B => T w) (hB i j)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.zero_apply] at h
  rwa [add_eq_zero_iff_eq_neg] at h

/-- **Nilpotency on a pure tensor.**  The crux of Route 1: the double sum
`∑_{m,n} (a_n a_m x) ⊗ (b_{s−n} b_{s−m} y)` vanishes because the swap `(m,n) ↦ (n,m)`
negates every summand — `a` contributes `+1` and `b` contributes `−1`.

The same two hypotheses also make the double support finite: pushing the offending operator
to the *right* through the (anti)commutation relation converts each of the four escapes
`m ≪ 0`, `n ≪ 0`, `m ≫ 0`, `n ≫ 0` into a lower-truncation zero. -/
theorem rawCoeff_sq_tmul {a : A} {b : B} (hA : CoeffCommute V a) (hB : CoeffAnticommute W b)
    (s : ℤ) (x : A) (y : B) :
    TensorVA.rawCoeff V W a b s (TensorVA.rawCoeff V W a b s (x ⊗ₜ[ℂ] y)) = 0 := by
  classical
  obtain ⟨N₁, hN₁⟩ := TensorVA.isField_superY V a x
  obtain ⟨N₂, hN₂⟩ := TensorVA.isField_superY W b y
  have hAx := coeffCommute_apply V hA
  have hBy := coeffAnticommute_apply W hB
  set F : ℤ × ℤ → A ⊗[ℂ] B :=
    fun p => (V.Y a p.2 (V.Y a p.1 x)) ⊗ₜ[ℂ] (W.Y b (s - p.2) (W.Y b (s - p.1) y)) with hFdef
  -- The double support is contained in a square box.
  have hsupp : (Function.support F).Finite := by
    refine Set.Finite.subset
      ((Set.finite_Icc N₁ (s - N₂)).prod (Set.finite_Icc N₁ (s - N₂))) ?_
    intro p hp
    rw [Function.mem_support] at hp
    simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · by_contra hc
      refine hp ?_
      rw [hFdef]
      simp only []
      rw [hN₁ p.1 (by omega), map_zero, TensorProduct.zero_tmul]
    · by_contra hc
      refine hp ?_
      rw [hFdef]
      simp only []
      rw [hN₂ (s - p.1) (by omega), map_zero, TensorProduct.tmul_zero]
    · by_contra hc
      refine hp ?_
      rw [hFdef]
      simp only []
      rw [hAx p.2 p.1 x, hN₁ p.2 (by omega), map_zero, TensorProduct.zero_tmul]
    · by_contra hc
      refine hp ?_
      rw [hFdef]
      simp only []
      rw [hBy (s - p.2) (s - p.1) y, hN₂ (s - p.2) (by omega), map_zero, neg_zero,
        TensorProduct.tmul_zero]
  -- The swap negates the summand.
  have hswapneg : ∀ p : ℤ × ℤ, F ((Equiv.prodComm ℤ ℤ) p) = -(F p) := by
    rintro ⟨m, n⟩
    change (V.Y a m (V.Y a n x)) ⊗ₜ[ℂ] (W.Y b (s - m) (W.Y b (s - n) y))
        = -((V.Y a n (V.Y a m x)) ⊗ₜ[ℂ] (W.Y b (s - n) (W.Y b (s - m) y)))
    rw [hAx m n x, hBy (s - m) (s - n) y, TensorProduct.tmul_neg]
  -- Hence the total sum equals its own negative, so it vanishes.
  have hzero : (∑ᶠ p : ℤ × ℤ, F p) = 0 := by
    have h1 : (∑ᶠ p : ℤ × ℤ, F ((Equiv.prodComm ℤ ℤ) p)) = ∑ᶠ p : ℤ × ℤ, F p :=
      finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
    have h3 : (∑ᶠ p : ℤ × ℤ, (-1 : ℂ) • F p) = (-1 : ℂ) • ∑ᶠ p : ℤ × ℤ, F p :=
      (smul_finsum' (-1 : ℂ) hsupp).symm
    simp only [neg_one_smul] at h3
    have hneg : (∑ᶠ p : ℤ × ℤ, F p) = -(∑ᶠ p : ℤ × ℤ, F p) :=
      calc (∑ᶠ p : ℤ × ℤ, F p)
          = ∑ᶠ p : ℤ × ℤ, F ((Equiv.prodComm ℤ ℤ) p) := h1.symm
        _ = ∑ᶠ p : ℤ × ℤ, -(F p) := by simp only [hswapneg]
        _ = -(∑ᶠ p : ℤ × ℤ, F p) := h3
    have htwo : (2 : ℂ) • (∑ᶠ p : ℤ × ℤ, F p) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hneg]
      exact add_neg_cancel _
    have h4 : ((2 : ℂ)⁻¹ * 2) • (∑ᶠ p : ℤ × ℤ, F p)
        = (2 : ℂ)⁻¹ • ((2 : ℂ) • ∑ᶠ p : ℤ × ℤ, F p) := mul_smul _ _ _
    rw [htwo, smul_zero, show ((2 : ℂ)⁻¹ * 2) = 1 from by norm_num, one_smul] at h4
    exact h4
  -- Assemble: expand both applications and curry.
  rw [TensorVA.rawCoeff_tmul V W a b s x y,
    map_finsum _ (TensorVA.raw_support V W a b s x y)]
  have hinner : ∀ m : ℤ,
      TensorVA.rawCoeff V W a b s ((V.Y a m x) ⊗ₜ[ℂ] (W.Y b (s - m) y))
        = ∑ᶠ n : ℤ, F (m, n) := by
    intro m
    rw [TensorVA.rawCoeff_tmul]
  simp only [hinner]
  rw [← finsum_curry F hsupp]
  exact hzero

/-- **`Q² = 0`, abstractly.**  Every coefficient of the naive tensor field
`Y_A(a,z) ⊗ Y_B(b,z)` is nilpotent when `a`'s coefficients commute and `b`'s anticommute. -/
theorem rawCoeff_mul_self_eq_zero {a : A} {b : B} (hA : CoeffCommute V a)
    (hB : CoeffAnticommute W b) (s : ℤ) :
    TensorVA.rawCoeff V W a b s * TensorVA.rawCoeff V W a b s = 0 := by
  refine LinearMap.ext fun z => ?_
  rw [LinearMap.zero_apply, Module.End.mul_apply]
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x y => exact rawCoeff_sq_tmul V W hA hB s x y
  | add u v hu hv => rw [map_add, map_add, hu, hv, add_zero]

end AbstractSquare

/-! ### `tenY` collapses to `rawCoeff` over a purely even first factor

D1 notes this; here it is proved.  `PreVertexAlgebra.toSuper` gives the *even* parity grading,
whose involution `(−1)^F` is the identity, so the Koszul dressing `κ_q ⊗ 1` is the identity
for **both** values of `q` and no parity bookkeeping on the ghost state is needed.
-/

section EvenLeft

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- The parity involution of a purely even vertex algebra is the identity. -/
theorem parityInvol_toSuper (V : PreVertexAlgebra A) :
    (TensorVA.parGr V.toSuper).parityInvol = (LinearMap.id : A →ₗ[ℂ] A) := by
  refine LinearMap.ext fun u => ?_
  rw [LinearMap.id_coe, id_eq]
  refine (TensorVA.parGr V.toSuper).parityInvol_even ?_
  change u ∈ (ParityGrading.even A).parity 0
  rw [ParityGrading.even_parity_zero]
  exact Submodule.mem_top

/-- The Koszul dressing operator is the identity when the first factor is purely even. -/
theorem kappaTen_toSuper (V : PreVertexAlgebra A) (W : SuperVertexAlgebra B) (q : ZMod 2) :
    TensorVA.kappaTen V.toSuper W q = (LinearMap.id : A ⊗[ℂ] B →ₗ[ℂ] A ⊗[ℂ] B) := by
  rw [TensorVA.kappaTen]
  rcases zmod2_cases q with h | h <;> subst h
  · rw [TensorVA.koszulOp_zero, TensorProduct.map_id]
  · rw [TensorVA.koszulOp_one, parityInvol_toSuper, TensorProduct.map_id]

/-- **Over a purely even first factor, `Y(a ⊗ b, z) = Y_A(a,z) ⊗ Y_B(b,z)` on the nose.**
No Koszul sign survives, so D1's `tenY` is exactly `rawCoeff`. -/
theorem tenY_tmul_toSuper (V : PreVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A) (b : B)
    (s : ℤ) :
    TensorVA.tenY V.toSuper W (a ⊗ₜ[ℂ] b) s = TensorVA.rawCoeff V.toSuper W a b s := by
  refine LinearMap.ext fun z => ?_
  rw [TensorVA.tenY_tmul_apply, kappaTen_toSuper]
  simp only [LinearMap.id_coe, id_eq, sub_self, map_zero, add_zero]
  rw [show z + z = (2 : ℂ) • z from by rw [two_smul], map_smul, smul_smul]
  norm_num

end EvenLeft

/-! ## §4  Route 1 — the `𝔰𝔩₂` BRST complex

For `𝔰𝔩₂` with the principal nilpotent `f`, `𝔤_{>0} = ℂ e` is one-dimensional and there are no
neutral fermions, so the complex is `𝒱(𝔰𝔩₂,k) ⊗ (one bc pair)` and the BRST current is

  `j_{BRST}(z) = c(z) (e(z) + 1)`,

the `+1` being the value `⟨f_prin, e⟩ = 1` of the principal nilpotent on `e` (there is no
cubic ghost term, since `[e,e] = 0`).  Its zero mode is the coefficient
`∑_m (e + 𝟙)_m ⊗ c_{−1−m}` — i.e. exactly `TensorVA.rawCoeff … (−1)`, which is what `dsQ` is
*defined* to be; `dsQ_eq_mode_tenY` then proves this really is `mode (Y((e+𝟙) ⊗ c, z)) 0`.
-/

/-- The level-`k` affine `𝔰𝔩₂` vacuum module as a (purely even) vertex superalgebra. -/
noncomputable def affSVA (k : ℂ) (hk : k + 2 ≠ 0) :
    SuperVertexAlgebra (AffineVOA.WakModule k) :=
  (AffineVOA.Vir.affineVA k hk).toSuper

theorem affSVA_eq (k : ℂ) (hk : k + 2 ≠ 0) :
    affSVA k hk = (AffineVOA.Vir.affineVA k hk).toSuper := rfl

/-- The state `e + 𝟙 = e₍₋₁₎|0⟩ + |0⟩` of the affine factor: the raising current shifted by
the value of the principal nilpotent, `⟨f_prin, e⟩ = 1`. -/
noncomputable def ePlusOne (k : ℂ) : AffineVOA.WakModule k :=
  AffineVOA.J k AffineVOA.colE (-1) (AffineVOA.vacuumA k) + AffineVOA.vacuumA k

/-- The ghost state `c₍₋₁₎|0⟩` of the single `bc` pair. -/
noncomputable def cGhost : SympFerm.FockSF := SympFerm.stWordSF [((0, 1) : ℕ × Fin 2)]

/-! ### The two inputs to `Q² = 0` -/

/-- **`[e_m, e_n] = 0` on `𝒱(𝔰𝔩₂,k)`, for every level `k`.**  Two things vanish at once in
`AffineSl2.current_comm`: the structure constant `f^{ee}{}_c = 0` (because `[e,e] = 0`) and
the Killing form `κ(e,e) = 0` — the latter is why the *level* drops out and the raising
currents commute exactly, not just modulo the centre. -/
theorem J_colE_comm (k : ℂ) (m n : ℤ) :
    AffineVOA.J k AffineVOA.colE m * AffineVOA.J k AffineVOA.colE n
      = AffineVOA.J k AffineVOA.colE n * AffineVOA.J k AffineVOA.colE m := by
  have h := AffineVOA.current_comm k AffineVOA.colE AffineVOA.colE m n
  have hsum : (∑ c, AffineVOA.fabc AffineVOA.colE AffineVOA.colE c
      • AffineVOA.J k c (m + n)) = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    have hf : AffineVOA.fabc AffineVOA.colE AffineVOA.colE c = 0 := by
      fin_cases c <;> rfl
    rw [hf, zero_smul]
  have hcen : (if m + n = 0 then
      ((m : ℂ) * k * AffineVOA.kappa AffineVOA.colE AffineVOA.colE)
        • (LinearMap.id : End ℂ (AffineVOA.WakModule k)) else 0) = 0 := by
    have hkap : AffineVOA.kappa AffineVOA.colE AffineVOA.colE = 0 := rfl
    rw [hkap]
    by_cases hmn : m + n = 0
    · rw [if_pos hmn, mul_zero, zero_smul]
    · rw [if_neg hmn]
  rw [hsum, hcen, add_zero] at h
  exact eq_of_sub_eq_zero h

/-- The vertex operator of `e + 𝟙` is `J^e(z) + 1`. -/
theorem Y_ePlusOne (k : ℂ) (hk : k + 2 ≠ 0) :
    (affSVA k hk).Y (ePlusOne k)
      = AffineVOA.Jfield k AffineVOA.colE
        + (1 : FormalDist (End ℂ (AffineVOA.WakModule k))) := by
  change AffineVOA.YA k hk (ePlusOne k) = _
  rw [ePlusOne, map_add, AffineVOA.Vir.YA_current_state, AffineVOA.YA_vacuum]

/-- A commuting pair stays commuting after adding central elements on both sides. -/
theorem mul_comm_add_central {R : Type*} [Ring R] {x y u v : R} (hxy : x * y = y * x)
    (hu : ∀ r : R, u * r = r * u) (hv : ∀ r : R, v * r = r * v) :
    (x + u) * (y + v) = (y + v) * (x + u) := by
  have h1 : (x + u) * (y + v) = x * y + x * v + u * y + u * v := by
    rw [add_mul, mul_add, mul_add]; abel
  have h2 : (y + v) * (x + u) = y * x + y * u + v * x + v * u := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [h1, h2, hxy, ← hv x, hu y, hu v]
  abel

/-- Every coefficient of the unit field is `0` or `1`, hence central. -/
theorem one_coeff_central {X : Type*} [Ring X] (i : ℤ) (r : X) :
    (1 : FormalDist X) i * r = r * (1 : FormalDist X) i := by
  rw [FormalDist.one_apply]
  split_ifs
  · rw [one_mul, mul_one]
  · rw [zero_mul, mul_zero]

/-- The coefficients of `Y(e + 𝟙, z)` commute with one another. -/
theorem coeffCommute_ePlusOne (k : ℂ) (hk : k + 2 ≠ 0) :
    CoeffCommute (affSVA k hk) (ePlusOne k) := by
  intro i j
  have hY : ∀ m : ℤ, (affSVA k hk).Y (ePlusOne k) m
      = AffineVOA.Jfield k AffineVOA.colE m
        + (1 : FormalDist (End ℂ (AffineVOA.WakModule k))) m := by
    intro m; rw [Y_ePlusOne k hk]; rfl
  rw [hY i, hY j]
  refine mul_comm_add_central ?_ (one_coeff_central i) (one_coeff_central j)
  change AffineVOA.J k AffineVOA.colE (-i - 1) * AffineVOA.J k AffineVOA.colE (-j - 1)
      = AffineVOA.J k AffineVOA.colE (-j - 1) * AffineVOA.J k AffineVOA.colE (-i - 1)
  exact J_colE_comm k _ _

/-- The vertex operator of `c₍₋₁₎|0⟩` is the ghost field `c(z)`. -/
theorem Y_cGhost : Ghost.bcGhostSVA.Y cGhost = Ghost.cfield := by
  have h0 : Ghost.YGh cGhost = Ghost.YwordGh [((0, 1) : ℕ × Fin 2)] := Ghost.YGh_word _
  have h1 : Ghost.YwordGh [((0, 1) : ℕ × Fin 2)] = Ghost.ghGenField 1 0 := by
    rw [Ghost.YwordGh_cons]
    have hkz : koszul 1 ((List.length ([] : SympFerm.SFWord) : ℕ) : ZMod 2) = 1 := by
      rw [List.length_nil, Nat.cast_zero, koszul_zero_right]
    rw [hkz]
    exact (nprodε_one _ _).trans (nprod_idField _)
  have h2 : Ghost.ghGenField 1 0 = Ghost.cfield := by
    rw [Ghost.ghGenField, Ghost.cfield]
    simp
  change Ghost.YGh cGhost = Ghost.cfield
  rw [h0, h1, h2]

/-- The coefficients of `Y(c, z)` anticommute with one another: the `bc` system has no
`cc` contraction, so `{c_j, c_k} = 0` exactly. -/
theorem coeffAnticommute_cGhost : CoeffAnticommute Ghost.bcGhostSVA cGhost := by
  intro i j
  rw [Y_cGhost]
  exact Ghost.cc_anticomm i j

/-! ### The BRST charge and its nilpotency -/

/-- **The `𝔰𝔩₂` Drinfeld–Sokolov BRST charge**, `Q = ∮ c(z)(e(z) + 1)`.

Written out: `Q (x ⊗ y) = ∑ᶠ m, ((e + 𝟙)_m x) ⊗ (c_{−1−m} y)`, the `z^{−1}`-coefficient of
`Y(e + 𝟙, z) ⊗ Y(c, z)` — see `dsQ_eq_mode_tenY` for the identification with the zero mode of
the honest tensor-product vertex operator. -/
noncomputable def dsQ (k : ℂ) (hk : k + 2 ≠ 0) :
    End ℂ (AffineVOA.WakModule k ⊗[ℂ] SympFerm.FockSF) :=
  TensorVA.rawCoeff (affSVA k hk) Ghost.bcGhostSVA (ePlusOne k) cGhost (-1)

/-- Explicit form of the BRST charge on a pure tensor. -/
theorem dsQ_tmul (k : ℂ) (hk : k + 2 ≠ 0) (x : AffineVOA.WakModule k) (y : SympFerm.FockSF) :
    dsQ k hk (x ⊗ₜ[ℂ] y)
      = ∑ᶠ m : ℤ, ((affSVA k hk).Y (ePlusOne k) m x)
          ⊗ₜ[ℂ] (Ghost.bcGhostSVA.Y cGhost (-1 - m) y) :=
  TensorVA.rawCoeff_tmul _ _ _ _ _ _ _

/-- **The BRST charge is the zero mode of `Y((e + 𝟙) ⊗ c, z)`** for D1's tensor-product
vertex operator — the schematic formula, derived. -/
theorem dsQ_eq_mode_tenY (k : ℂ) (hk : k + 2 ≠ 0) :
    mode (TensorVA.tenY (affSVA k hk) Ghost.bcGhostSVA ((ePlusOne k) ⊗ₜ[ℂ] cGhost)) 0
      = dsQ k hk := by
  rw [mode_apply, show (-(0 : ℤ) - 1) = -1 from by ring, dsQ, affSVA]
  exact tenY_tmul_toSuper (AffineVOA.Vir.affineVA k hk) Ghost.bcGhostSVA _ _ _

/-- **`Q² = 0`** — the crux of Route 1.

The two inputs are `J_colE_comm` (the raising currents commute exactly, structure constant
*and* level both vanishing) and `Ghost.cc_anticomm` (the `bc` ghosts have no `cc`
contraction).  Nilpotency then follows from `rawCoeff_mul_self_eq_zero`. -/
theorem dsQ_mul_self (k : ℂ) (hk : k + 2 ≠ 0) : dsQ k hk * dsQ k hk = 0 :=
  rawCoeff_mul_self_eq_zero _ _ (coeffCommute_ePlusOne k hk) coeffAnticommute_cGhost (-1)

/-- Pointwise nilpotency. -/
theorem dsQ_dsQ_apply (k : ℂ) (hk : k + 2 ≠ 0)
    (z : AffineVOA.WakModule k ⊗[ℂ] SympFerm.FockSF) : dsQ k hk (dsQ k hk z) = 0 := by
  have h := congrArg (fun T : End ℂ (AffineVOA.WakModule k ⊗[ℂ] SympFerm.FockSF) => T z)
    (dsQ_mul_self k hk)
  simpa only [Module.End.mul_apply, LinearMap.zero_apply] using h

/-! ### `H⁰` of the complex

`BRST.BRSTComplex` (D2) packages a differential together with the ghost grading and the
three compatibility axioms.  `Q_sq` is `dsQ_mul_self` above.  The one field that is **not**
available is `Q_deriv`, the super Leibniz rule; see §5 of the module docstring.  Rather than
hide that, `dsReductionSl2` takes a complex and a proof that its differential *is* `dsQ`.
-/

/-- The property that pins a BRST complex on `𝒱(𝔰𝔩₂,k) ⊗ (bc)` down to the Drinfeld–Sokolov
one: its differential is the charge `dsQ` derived above. -/
def IsDSComplexSl2 (k : ℂ) (hk : k + 2 ≠ 0)
    {V : SuperVertexAlgebra (AffineVOA.WakModule k ⊗[ℂ] SympFerm.FockSF)}
    (C : BRST.BRSTComplex V) : Prop := C.Q = dsQ k hk

/-- **`W^k(𝔰𝔩₂, f_prin)` by Route 1** (target **b**): the ghost-number-zero BRST cohomology
of the Drinfeld–Sokolov complex, via D2's `BRSTComplex.H0`. -/
noncomputable def dsReductionSl2 (k : ℂ) (hk : k + 2 ≠ 0)
    {V : SuperVertexAlgebra (AffineVOA.WakModule k ⊗[ℂ] SympFerm.FockSF)}
    (C : BRST.BRSTComplex V) (_h : IsDSComplexSl2 k hk C) : Submodule ℂ C.Coh := C.H0

/-- The `Q_sq` axiom of any Drinfeld–Sokolov complex is discharged by `dsQ_mul_self` — it is
not an extra assumption. -/
theorem isDSComplexSl2_Q_sq (k : ℂ) (hk : k + 2 ≠ 0)
    {V : SuperVertexAlgebra (AffineVOA.WakModule k ⊗[ℂ] SympFerm.FockSF)}
    (C : BRST.BRSTComplex V) (h : IsDSComplexSl2 k hk C) : C.Q * C.Q = 0 := by
  rw [h]; exact dsQ_mul_self k hk

/-! ## §5  The comparison of the two routes (recorded, not proved)

Target **g**.  The Feigin–Frenkel theorem says the BRST cohomology of §4 and the screening
kernel of §2 are the *same* vertex algebra.  That is a research theorem; it is recorded here
as a `Prop`, with the notion of isomorphism spelled out, and deliberately left unproved.
-/

/-- An isomorphism of vertex superalgebras: a linear equivalence matching the vacua and every
`n`-th product. -/
structure SVAEquiv {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (V : SuperVertexAlgebra X) (W : SuperVertexAlgebra Y) where
  /-- The underlying linear equivalence. -/
  toLinearEquiv : X ≃ₗ[ℂ] Y
  /-- The vacua correspond. -/
  map_vacuum : toLinearEquiv V.vacuum = W.vacuum
  /-- Every `n`-th product is intertwined. -/
  map_smul : ∀ (u : X) (n : ℤ) (v : X),
    toLinearEquiv (V.smul u n v) = W.smul (toLinearEquiv u) n (toLinearEquiv v)

/-- **The Feigin–Frenkel comparison, recorded not proved.**  `RoutesAgreeSl2 V W` asserts that
the BRST-cohomology vertex superalgebra `V` of Route 1 and the screening-kernel vertex
superalgebra `W` of Route 2 are isomorphic.  Proving it for the objects built above is the
research theorem; the two central-charge computations `dsCentralCharge_eq_affine_add_ghost`
and `dsScreeningSl2_centralCharge` are the (already proved) numerical shadow of it. -/
def RoutesAgreeSl2 {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (V : SuperVertexAlgebra X) (W : SuperVertexAlgebra Y) : Prop := Nonempty (SVAEquiv V W)

end VOA.DSsl2
