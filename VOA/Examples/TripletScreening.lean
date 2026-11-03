/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeBackgroundChargeB
import VOA.Examples.LatticeGenVOAInstance

/-!
# The long screening operator and the triplet generators `E`, `H`, `F`

Inside the general lattice VOA `V_L` deformed by a background charge `λ`
(`Examples.LatticeBackgroundChargeB`), fix a lattice vector `α` with `⟨α,α⟩ = 2p` and a background
charge normalized by `wt(e^α) = 1`, i.e.

  `½⟨α,α⟩ − ⟨λ,α⟩ = 1`.

(For the triplet lattice `L = ℤα`, `λ = (p−1)/(2p)·α` this is `p − (p−1) = 1`; see
`BgB.bgWeight_triplet`.)  This file builds

* `Qscr α := (e^α)₍₀₎ = mode (Y(e^α,z)) 0` — the **long screening operator** (in Adamović–Milas'
  terminology; the short screening is `(e^{−α/p})₍₀₎`, which is not constructed here);
* `Fscr α := e^{−α}`, `Hscr α := Q F`, `Escr α := Q H` — the three triplet generators.

## Main results

* `Qscr_eq_mode_YfullGen` — `Qscr` really is the zero mode of the reconstructed vertex operator
  `YfullGen (e^α)` of the lattice VOA, not just of the hand-built `Yeαvec`.
* `LBG_zero_comm_Qscr` — **`[L^λ₀, Q] = 0`**: the screening operator commutes with the deformed
  weight operator, i.e. it *preserves the deformed weight grading*.  The only input is
  `½⟨α,α⟩ − ⟨λ,α⟩ = 1`, exactly the statement `wt(e^α) = 1`.
* `LBG_zero_Fscr`, `LBG_zero_Hscr`, `LBG_zero_Escr` — all three generators are `L^λ₀`-eigenvectors
  of eigenvalue `2p − 1`.
* `Hscr_eq` — the explicit formula `H = ε(α,−α) · S_{2p−1}(α) ⊗ e⁰`, the vector Schur polynomial
  `vSchur α (2p−1)` of `Examples.LatticeGenChargeFields` applied to the vacuum.
* `Escr_eq` — `E = ε(α,−α) · (E⁻E⁺(α)_{−1} S_{2p−1}(α)) ⊗ e^α`.
* `Hscr_ne_zero` — **`H ≠ 0`**, via `vSchur_ne_zero` (the vector Schur polynomials never
  vanish for `α ≠ 0`, proved from the lynchpin `pderiv_vSchur`).
* `Qscr_cube_Fscr` — **`Q³F = 0`**, for weight/charge reasons: the charge-`2α` sector has no
  state at weight `2p−1` (the boson degree needed would be `−3`).
* `Qscr_preserves_weight` — the eigenvector form of `LBG_zero_comm_Qscr`; `triplet_wt_one` turns the
  triplet data `⟨α,α⟩ = 2p`, `⟨λ,α⟩ = p−1` into its hypothesis.

## What is *not* here

`Escr_ne_zero` is **not** proved: it needs `EE(α)_{−1} S_{2p−1}(α) ≠ 0`, i.e. a non-vanishing
statement for the full (annihilation-dressed) charge operator, which the `pderiv_vSchur` argument
behind `vSchur_ne_zero` does not reach.  Neither is the derivation property of `Q`, nor the closure
of `span{E,H,F}` under the VOA products (the `W`-algebra structure itself).

## Grading infrastructure (§1)

The proofs need the boson-degree bookkeeping of the charge dressing, which is not in the repo yet:

* `vSchur_mem_gradingWN` — `S_N(α)` is weighted-homogeneous of Fock degree `N`;
* `EminusVec_mem_gradingZN`, `EEVec_mem_gradingZN` — `E⁻(α)_N` raises the boson degree by `N` and
  the full dressing `EE(α)_r` raises it by `r`.

All `sorry`-free, axiom-clean.
-/

set_option linter.style.longLine false

namespace VOA.LatGen.Screen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen VOA.LatGen.BgB
open MvPolynomial

variable (L : IntegralLattice)

/-! ## §0  Two elementary lattice/background-charge identities -/

/-- `⟨β+γ,β+γ⟩ = ⟨β,β⟩ + 2⟨β,γ⟩ + ⟨γ,γ⟩`. -/
theorem form_add_self (β γ : L.carrier) :
    L.form (β + γ) (β + γ) = L.form β β + 2 * L.form β γ + L.form γ γ := by
  have h1 : L.form (β + γ) = L.form β + L.form γ := map_add L.form β γ
  rw [h1]
  simp only [LinearMap.add_apply, map_add]
  rw [form_symm L γ β]
  ring

/-- `⟨-β,-β⟩ = ⟨β,β⟩`. -/
theorem form_neg_self (β : L.carrier) : L.form (-β) (-β) = L.form β β := by
  have h1 : L.form (-β) = -(L.form β) := map_neg L.form β
  rw [h1, LinearMap.neg_apply, map_neg, neg_neg]

/-- The background-charge pairing is additive in the lattice vector. -/
theorem bgPair_add (lam : Fin (rank L) → ℂ) (β γ : L.carrier) :
    bgPair L lam (β + γ) = bgPair L lam β + bgPair L lam γ := by
  rw [bgPair_eq, bgPair_eq, bgPair_eq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [chargeCoord_add, mul_add]

/-- `⟨λ,0⟩ = 0`. -/
theorem bgPair_zero (lam : Fin (rank L) → ℂ) : bgPair L lam 0 = 0 := by
  rw [bgPair_eq]
  exact Finset.sum_eq_zero fun a _ => by rw [chargeCoord_zero, mul_zero]

/-- `⟨λ,−β⟩ = −⟨λ,β⟩`. -/
theorem bgPair_neg (lam : Fin (rank L) → ℂ) (β : L.carrier) :
    bgPair L lam (-β) = - bgPair L lam β := by
  have h := bgPair_add L lam β (-β)
  rw [add_neg_cancel, bgPair_zero] at h
  linear_combination -h

/-! ## §1  The boson degree of the charge dressing

`vSchur α N` has Fock degree `N`, `E⁻(α)_N` raises the degree by `N`, `E⁺(α)_{-N}` lowers it by `N`
(already in the repo as `aExpVec_mem_gradingZN`), hence the normal-ordered dressing `EE(α)_r` raises
the degree by exactly `r`. -/

/-- `vVar α m` is weighted-homogeneous of Fock degree `m+1` (it is a combination of the creation
variables `X_{(m,a)}`, each of weight `m+1`). -/
theorem vVar_mem_gradingWN (α : L.carrier) (m : ℕ) :
    vVar L α m ∈ gradingWN (rank L) (m + 1) := by
  rw [vVar]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
  rw [mem_gradingWN]
  have h := isWeightedHomogeneous_X ℂ (weightFnN (r := rank L)) ((m, a))
  simpa using h

/-- **The vector Schur polynomial `S_N(α)` has Fock degree exactly `N`.**  Induction on the
Newton recursion `(N+1)·S_{N+1} = ∑_{m≤N} vVar α m · S_{N−m}`: each summand has degree
`(m+1) + (N−m) = N+1`. -/
theorem vSchur_mem_gradingWN (α : L.carrier) (N : ℕ) :
    vSchur L α N ∈ gradingWN (rank L) N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 =>
        rw [vSchur_zero, mem_gradingWN]
        exact isWeightedHomogeneous_one ℂ _
    | (M + 1) =>
        rw [vSchur_succ]
        refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_)
        simp only [Finset.mem_range] at hm
        have h1 := vVar_mem_gradingWN L α m
        have h2 := ih (M - m) (by omega)
        rw [mem_gradingWN] at h1 h2 ⊢
        have h3 := h1.mul h2
        rwa [show m + 1 + (M - m) = M + 1 from by omega] at h3

/-- `E⁻(α)_N` (multiplication by `S_N(α)`) raises the boson degree by `N`. -/
theorem EminusVec_mem_gradingZN (α : L.carrier) (N : ℕ) {d : ℤ} {q : FockN (rank L)}
    (hq : q ∈ gradingZN (rank L) d) :
    EminusVec L α N q ∈ gradingZN (rank L) (d + N) := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [gradingZN_of_neg hd, Submodule.mem_bot] at hq
    rw [hq, map_zero]
    exact zero_mem_gradingZN (rank L) _
  · rw [gradingZN_of_nonneg hd] at hq
    have h : vSchur L α N * q ∈ gradingWN (rank L) (N + d.toNat) := by
      rw [mem_gradingWN]
      exact (mem_gradingWN.mp (vSchur_mem_gradingWN L α N)).mul (mem_gradingWN.mp hq)
    have h2 := mem_gradingZN_of_gradingWN h
    rw [EminusVec, LinearMap.mulLeft_apply]
    rwa [show ((N + d.toNat : ℕ) : ℤ) = d + N from by omega] at h2

/-- **The charge dressing raises the boson degree by its index**: `EE(α)_r : F_w → F_{w+r}`
(with `F_{<0} = 0`).  Each normal-ordered summand `E⁻(α)_m E⁺(α)_{r−m}` moves the degree by
`m + (r − m) = r`. -/
theorem EEVec_mem_gradingZN_of_gradingWN (α : L.carrier) (r : ℤ) {w : ℕ} {q : FockN (rank L)}
    (hq : q ∈ gradingWN (rank L) w) :
    EEVec L α r q ∈ gradingZN (rank L) ((w : ℤ) + r) := by
  rw [EEVec, nprod_apply,
    finsum_eq_sum _ (normalOrdered_diag_support_finite (EminusVecField_isField L α)
      (EplusVecField_isField L α) r q)]
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [normalOrdered_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0, Module.End.mul_apply]
    by_cases hrm : r - m ≤ 0
    · rw [EplusVecField_nonpos L α hrm, EminusVecField_apply, if_pos h0]
      have h1 := aExpVec_mem_gradingZN L α ((-(r - m)).toNat) hq
      have h2 := EminusVec_mem_gradingZN L α m.toNat h1
      rwa [show (w : ℤ) - (((-(r - m)).toNat : ℕ) : ℤ) + ((m.toNat : ℕ) : ℤ) = (w : ℤ) + r from
        by omega] at h2
    · rw [EplusVecField_apply, if_neg hrm, LinearMap.zero_apply, map_zero]
      exact zero_mem_gradingZN (rank L) _
  · rw [if_neg h0, Module.End.mul_apply, EminusVecField_neg L α (by omega : m < 0),
      LinearMap.zero_apply, map_zero]
    exact zero_mem_gradingZN (rank L) _

/-- The `gradingZN`-to-`gradingZN` form of `EEVec_mem_gradingZN_of_gradingWN`. -/
theorem EEVec_mem_gradingZN (α : L.carrier) (r : ℤ) {d : ℤ} {q : FockN (rank L)}
    (hq : q ∈ gradingZN (rank L) d) :
    EEVec L α r q ∈ gradingZN (rank L) (d + r) := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [gradingZN_of_neg hd, Submodule.mem_bot] at hq
    rw [hq, map_zero]
    exact zero_mem_gradingZN (rank L) _
  · rw [gradingZN_of_nonneg hd] at hq
    have h := EEVec_mem_gradingZN_of_gradingWN L α r hq
    rwa [show ((d.toNat : ℕ) : ℤ) + r = d + r from by omega] at h

/-! ## §2  The long screening operator `Q = (e^α)₍₀₎` -/

/-- **The long screening operator** `Q = (e^α)₍₀₎ = mode (Y(e^α,z)) 0`.  Since `wt(e^α) = 1` under
the background-charge Virasoro, `Q` has weight `0`; it shifts the lattice charge by `+α`. -/
noncomputable def Qscr (α : L.carrier) : End ℂ (LatModuleGen L) := mode (Yeαvec L α) 0

theorem Qscr_eq_Yeαvec (α : L.carrier) : Qscr L α = Yeαvec L α (-1) := by
  rw [Qscr, mode_apply]
  norm_num

/-- `Q` is the zero mode of the **reconstructed** lattice vertex operator `Y(e^α, z)`, i.e. of the
`YfullGen` of the `latticeVOAGen` instance. -/
theorem Qscr_eq_mode_YfullGen (hEven : L.Even) (hPos : L.PosDef) (α : L.carrier) :
    Qscr L α = mode (YfullGen L hEven hPos (latChargeGen L α)) 0 := by
  have h : YfullGen L hEven hPos (latChargeGen L α) = Yeαvec L α := by
    have hw := YfullGen_word L hEven hPos [] α
    rwa [wordStateLatGen_nil, YwordLatGen_nil] at hw
  rw [Qscr, h]

/-- The action of `Q` on a charged basis state `q ⊗ e^β`. -/
theorem Qscr_latStateGen (α β : L.carrier) (q : FockN (rank L)) :
    Qscr L α (latStateGen L q β)
      = latticeCocycle L α β • latStateGen L (EEVec L α (-1 - L.form α β) q) (α + β) := by
  rw [Qscr_eq_Yeαvec, Yeαvec_tmul]

/-- The action of `Q` on a charged vacuum `e^β`. -/
theorem Qscr_latChargeGen (α β : L.carrier) :
    Qscr L α (latChargeGen L β)
      = latticeCocycle L α β •
          latStateGen L (EEVec L α (-1 - L.form α β) (vacuumN (rank L))) (α + β) :=
  Qscr_latStateGen L α β (vacuumN (rank L))

/-! ## §3  The deformed weight operator on a charged basis state -/

/-- **The deformed weight of `q ⊗ e^γ`**: if `q` has boson degree `d`, then
`L^λ₀ (q ⊗ e^γ) = (d + ½⟨γ,γ⟩ − ⟨λ,γ⟩)·(q ⊗ e^γ)`.  (At `d = 0` this is `BgB.LBG_zero_latChargeGen`.) -/
theorem LBG_zero_mkEα (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (γ : L.carrier)
    {d : ℤ} {q : FockN (rank L)} (hq : q ∈ gradingZN (rank L) d) :
    LBG L lam 0 (mkEα L γ q)
      = ((d : ℂ) + (1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ) - bgPair L lam γ) • mkEα L γ q := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [gradingZN_of_neg hd, Submodule.mem_bot] at hq
    rw [hq, map_zero, map_zero, smul_zero]
  · rw [gradingZN_of_nonneg hd] at hq
    have hcast : ((d.toNat : ℕ) : ℂ) = (d : ℂ) := by
      have hz : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg hd
      exact_mod_cast hz
    have hL : LFock L γ 0 q = ((d : ℂ) + (1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ)) • q := by
      rw [LFock, if_pos rfl, LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LvirN_zero_gradingWN (rank L) 1 one_ne_zero hq, chargeOsc_eq_bgOsc,
        bgOsc_zero_mode, LinearMap.zero_apply, add_zero, hcast, ← add_smul]
    have hb : bgFock L lam γ 0 q = (bgPair L lam γ) • q := by
      rw [bgFock, if_pos rfl, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
        bgOsc_zero_mode, LinearMap.zero_apply, zero_add]
    rw [LBG, LinearMap.sub_apply, LLGen_mkEα L hPos, LinearMap.smul_apply, bgMode_mkEα, hL, hb,
      map_smul, map_smul]
    push_cast
    module

/-! ## §4  `Q` preserves the deformed weight grading -/

/-- Extensionality against boson-**homogeneous** vectors: two linear maps out of the Fock space
agreeing on every weighted-homogeneous vector are equal (a polynomial is the sum of its monomials,
and a monomial is homogeneous). -/
theorem fockHomExt {M : Type*} [AddCommGroup M] [Module ℂ M]
    {f g : FockN (rank L) →ₗ[ℂ] M}
    (h : ∀ (w : ℕ) (q : FockN (rank L)), q ∈ gradingWN (rank L) w → f q = g q) : f = g := by
  classical
  refine LinearMap.ext fun q => ?_
  conv_lhs => rw [q.as_sum]
  conv_rhs => rw [q.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact h (Finsupp.weight weightFnN a) _
    (mem_gradingWN.mpr (isWeightedHomogeneous_monomial _ _ _ rfl))

/-- Extensionality on `V_L` against boson-homogeneous charged basis states. -/
theorem latHomExt {f g : End ℂ (LatModuleGen L)}
    (h : ∀ (γ : L.carrier) (w : ℕ) (q : FockN (rank L)), q ∈ gradingWN (rank L) w →
      f (mkEα L γ q) = g (mkEα L γ q)) : f = g := by
  refine latExt L fun q γ => ?_
  exact LinearMap.congr_fun
    (fockHomExt L (f := f.comp (mkEα L γ)) (g := g.comp (mkEα L γ))
      (fun w q hq => h γ w q hq)) q

/-- **The screening operator preserves the deformed weight grading**: `[L^λ₀, Q] = 0`.

The sole input is `hwt : ½⟨α,α⟩ − ⟨λ,α⟩ = 1`, i.e. that `e^α` has deformed weight `1`; then the
mode `(e^α)₍₀₎` has weight `1 − 0 − 1 = 0`.  Concretely, on the charge sector `γ` the operator `Q`
shifts the boson degree by `−1 − ⟨α,γ⟩` and the charge by `+α`, and
`(−1 − ⟨α,γ⟩) + (½⟨α+γ,α+γ⟩ − ⟨λ,α+γ⟩) − (½⟨γ,γ⟩ − ⟨λ,γ⟩) = −1 + (½⟨α,α⟩ − ⟨λ,α⟩) = 0`. -/
theorem LBG_zero_comm_Qscr (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (α : L.carrier)
    (hwt : (1 / 2 : ℂ) * ((L.form α α : ℤ) : ℂ) - bgPair L lam α = 1) :
    LBG L lam 0 * Qscr L α = Qscr L α * LBG L lam 0 := by
  refine latHomExt L fun γ w q hq => ?_
  have hqz : q ∈ gradingZN (rank L) (w : ℤ) := mem_gradingZN_of_gradingWN hq
  have hQ : Qscr L α (mkEα L γ q)
      = latticeCocycle L α γ • mkEα L (α + γ) (EEVec L α (-1 - L.form α γ) q) := by
    rw [← latStateGen_eq_mkEα, Qscr_latStateGen, latStateGen_eq_mkEα]
  have hE : EEVec L α (-1 - L.form α γ) q
      ∈ gradingZN (rank L) ((w : ℤ) + (-1 - L.form α γ)) := EEVec_mem_gradingZN L α _ hqz
  rw [Module.End.mul_apply, Module.End.mul_apply, hQ, map_smul,
    LBG_zero_mkEα L hPos lam (α + γ) hE, LBG_zero_mkEα L hPos lam γ hqz, map_smul, hQ,
    smul_comm]
  congr 1
  rw [form_add_self L α γ, bgPair_add L lam α γ]
  push_cast
  linear_combination hwt

/-! ## §5  The three triplet generators `F`, `H`, `E` -/

/-- `F := e^{−α}`, the bottom of the triplet.  Its deformed weight is `½⟨α,α⟩ + ⟨λ,α⟩ = 2p − 1`. -/
noncomputable def Fscr (α : L.carrier) : LatModuleGen L := latChargeGen L (-α)

/-- `H := Q F`. -/
noncomputable def Hscr (α : L.carrier) : LatModuleGen L := Qscr L α (Fscr L α)

/-- `E := Q H = Q² F`. -/
noncomputable def Escr (α : L.carrier) : LatModuleGen L := Qscr L α (Hscr L α)

/-- **`H` is a Schur state**: `H = ε(α,−α)·S_{2p−1}(α) ⊗ e⁰`, with `S_N(α) = vSchur α N` the
vector Schur polynomial of `Examples.LatticeGenChargeFields`.  (`Q` moves `e^{−α}` into the charge-`0`
sector, and `EE(α)_{2p−1}|0⟩ = S_{2p−1}(α)` by `EEVec_vacuum`.) -/
theorem Hscr_eq (α : L.carrier) (p : ℕ) (hp : 1 ≤ p) (hαα : L.form α α = 2 * (p : ℤ)) :
    Hscr L α = latticeCocycle L α (-α) • latStateGen L (vSchur L α (2 * p - 1)) 0 := by
  have hform : (-1 : ℤ) - L.form α (-α) = 2 * (p : ℤ) - 1 := by
    rw [map_neg, hαα]; ring
  rw [Hscr, Fscr, Qscr_latChargeGen, hform, EEVec_vacuum,
    if_pos (by omega : (0 : ℤ) ≤ 2 * (p : ℤ) - 1),
    show (2 * (p : ℤ) - 1).toNat = 2 * p - 1 from by omega, add_neg_cancel]

/-- `E = ε(α,−α)·(EE(α)_{−1} S_{2p−1}(α)) ⊗ e^α`. -/
theorem Escr_eq (α : L.carrier) (p : ℕ) (hp : 1 ≤ p) (hαα : L.form α α = 2 * (p : ℤ)) :
    Escr L α
      = latticeCocycle L α (-α) •
          latStateGen L (EEVec L α (-1) (vSchur L α (2 * p - 1))) α := by
  rw [Escr, Hscr_eq L α p hp hαα, map_smul, Qscr_latStateGen,
    show L.form α (0 : L.carrier) = 0 from map_zero _, latticeCocycle_zero_right, one_smul,
    sub_zero, add_zero]

/-! ## §6  The deformed weights: all three generators sit at `2p − 1` -/

/-- `wt F = ½⟨α,α⟩ + ⟨λ,α⟩ = p + (p−1) = 2p − 1`. -/
theorem LBG_zero_Fscr (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (α : L.carrier) (p : ℕ)
    (hαα : L.form α α = 2 * (p : ℤ)) (hlam : bgPair L lam α = (p : ℂ) - 1) :
    LBG L lam 0 (Fscr L α) = (2 * (p : ℂ) - 1) • Fscr L α := by
  have hv : Fscr L α = mkEα L (-α) (vacuumN (rank L)) := rfl
  have h0 : vacuumN (rank L) ∈ gradingZN (rank L) (0 : ℤ) := by
    have := mem_gradingZN_of_gradingWN (vacuumN_mem_gradingWN (rank L))
    rwa [Nat.cast_zero] at this
  rw [hv, LBG_zero_mkEα L hPos lam (-α) h0, form_neg_self, hαα, bgPair_neg, hlam]
  congr 1
  push_cast
  ring

/-- `wt H = (2p−1) + 0 − 0 = 2p − 1`. -/
theorem LBG_zero_Hscr (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (α : L.carrier) (p : ℕ)
    (hp : 1 ≤ p) (hαα : L.form α α = 2 * (p : ℤ)) :
    LBG L lam 0 (Hscr L α) = (2 * (p : ℂ) - 1) • Hscr L α := by
  have hS : vSchur L α (2 * p - 1) ∈ gradingZN (rank L) (((2 * p - 1 : ℕ) : ℤ)) :=
    mem_gradingZN_of_gradingWN (vSchur_mem_gradingWN L α (2 * p - 1))
  have hW : ((((2 * p - 1 : ℕ) : ℤ)) : ℂ)
        + (1 / 2 : ℂ) * ((L.form (0 : L.carrier) (0 : L.carrier) : ℤ) : ℂ)
        - bgPair L lam 0 = 2 * (p : ℂ) - 1 := by
    rw [show L.form (0 : L.carrier) (0 : L.carrier) = 0 from by simp, bgPair_zero]
    push_cast [Nat.cast_sub (show 1 ≤ 2 * p from by omega)]
    ring
  rw [Hscr_eq L α p hp hαα, map_smul, latStateGen_eq_mkEα,
    LBG_zero_mkEα L hPos lam 0 hS, hW, smul_comm]

/-- `wt E = (2p−2) + p − (p−1) = 2p − 1`. -/
theorem LBG_zero_Escr (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (α : L.carrier) (p : ℕ)
    (hp : 1 ≤ p) (hαα : L.form α α = 2 * (p : ℤ)) (hlam : bgPair L lam α = (p : ℂ) - 1) :
    LBG L lam 0 (Escr L α) = (2 * (p : ℂ) - 1) • Escr L α := by
  have hS : vSchur L α (2 * p - 1) ∈ gradingZN (rank L) (((2 * p - 1 : ℕ) : ℤ)) :=
    mem_gradingZN_of_gradingWN (vSchur_mem_gradingWN L α (2 * p - 1))
  have hE := EEVec_mem_gradingZN L α (-1) hS
  have hW : (((((2 * p - 1 : ℕ) : ℤ) + (-1 : ℤ)) : ℤ) : ℂ)
        + (1 / 2 : ℂ) * ((L.form α α : ℤ) : ℂ) - bgPair L lam α = 2 * (p : ℂ) - 1 := by
    rw [hαα, hlam]
    push_cast [Nat.cast_sub (show 1 ≤ 2 * p from by omega)]
    ring
  rw [Escr_eq L α p hp hαα, map_smul, latStateGen_eq_mkEα,
    LBG_zero_mkEα L hPos lam α hE, hW, smul_comm]

/-! ## §7  `H ≠ 0` -/

/-- For `α ≠ 0` in a positive-definite lattice some frame coordinate of `α` is non-zero (else
`⟨α,α⟩ = ∑_b (α_b)² = 0`). -/
theorem exists_chargeCoord_ne_zero (hPos : L.PosDef) (α : L.carrier) (hα : α ≠ 0) :
    ∃ b : Fin (rank L), chargeCoord L α b ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hsum := sum_chargeCoord L hPos α α
  rw [Finset.sum_eq_zero (fun b _ => by rw [hcon b, zero_mul])] at hsum
  have h0 : (L.form α α : ℤ) = 0 := by exact_mod_cast hsum.symm
  have hpos := hPos α hα
  omega

/-- **The vector Schur polynomials never vanish** (for `α ≠ 0`).  Induction via the lynchpin
`pderiv_vSchur`: `∂_{X_{(0,b)}} S_{N+1}(α) = α_b · S_N(α)`, so a vanishing `S_{N+1}(α)` would force
a vanishing `S_N(α)` once some frame coordinate `α_b ≠ 0`. -/
theorem vSchur_ne_zero (hPos : L.PosDef) (α : L.carrier) (hα : α ≠ 0) (N : ℕ) :
    vSchur L α N ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_chargeCoord_ne_zero L hPos α hα
  induction N with
  | zero => rw [vSchur_zero]; exact one_ne_zero
  | succ M ih =>
      intro hz
      have h := pderiv_vSchur L α 0 b (M + 1)
      rw [hz, map_zero, if_pos (show 0 + 1 ≤ M + 1 from by omega),
        show M + 1 - (0 + 1) = M from by omega] at h
      simp only [Nat.cast_zero, zero_add, inv_one, one_smul] at h
      rcases smul_eq_zero.mp h.symm with h1 | h1
      · exact hb h1
      · exact ih h1

/-- A charged basis state `q ⊗ e^γ` with `q ≠ 0` is non-zero (project onto the charge-`γ` sector). -/
theorem latStateGen_ne_zero {q : FockN (rank L)} (hq : q ≠ 0) (γ : L.carrier) :
    latStateGen L q γ ≠ 0 := by
  intro h
  apply hq
  have hc : coordEα L γ (latStateGen L q γ) = q := by
    rw [latStateGen, coordEα_apply, if_pos rfl]
  rw [h, map_zero] at hc
  exact hc.symm

/-- The FLM cocycle is a sign, hence non-zero. -/
theorem latticeCocycle_ne_zero (α β : L.carrier) : latticeCocycle L α β ≠ 0 := by
  intro h
  have hsq := latticeCocycle_sq L α β
  rw [h, mul_zero] at hsq
  exact zero_ne_one hsq

/-- **`H ≠ 0`** — the middle triplet generator is a genuine state.  It is the Schur state
`S_{2p−1}(α) ⊗ e⁰` up to the (non-zero) cocycle sign, and `S_{2p−1}(α) ≠ 0`. -/
theorem Hscr_ne_zero (hPos : L.PosDef) (α : L.carrier) (hα : α ≠ 0) (p : ℕ) (hp : 1 ≤ p)
    (hαα : L.form α α = 2 * (p : ℤ)) : Hscr L α ≠ 0 := by
  rw [Hscr_eq L α p hp hαα]
  simp only [ne_eq, smul_eq_zero, not_or]
  exact ⟨latticeCocycle_ne_zero L α (-α),
    latStateGen_ne_zero L (vSchur_ne_zero L hPos α hα (2 * p - 1)) 0⟩

/-! ## §8  `Q³F = 0` -/

/-- **`Q³F = 0`.**  `Q` preserves the deformed weight `2p−1` but raises the lattice charge by
`α`; the charge-`2α` sector has `½⟨2α,2α⟩ − ⟨λ,2α⟩ = 4p − 2(p−1) = 2p + 2 > 2p − 1`, so it carries
no state of weight `2p−1`.  Concretely the boson degree of `Q³F` would have to be
`(2p−1) + (−1) + (−1 − 2p) = −3 < 0`. -/
theorem Qscr_Escr (α : L.carrier) (p : ℕ) (hp : 1 ≤ p) (hαα : L.form α α = 2 * (p : ℤ)) :
    Qscr L α (Escr L α) = 0 := by
  have hS : vSchur L α (2 * p - 1) ∈ gradingZN (rank L) (((2 * p - 1 : ℕ) : ℤ)) :=
    mem_gradingZN_of_gradingWN (vSchur_mem_gradingWN L α (2 * p - 1))
  have h1 := EEVec_mem_gradingZN L α (-1) hS
  have h2 := EEVec_mem_gradingZN L α (-1 - 2 * (p : ℤ)) h1
  rw [gradingZN_of_neg
      (show ((2 * p - 1 : ℕ) : ℤ) + (-1) + (-1 - 2 * (p : ℤ)) < 0 from by omega),
    Submodule.mem_bot] at h2
  rw [Escr_eq L α p hp hαα, map_smul, Qscr_latStateGen, hαα, h2, latStateGen,
    TensorProduct.zero_tmul, smul_zero, smul_zero]

/-- `Q³F = 0`, spelled out. -/
theorem Qscr_cube_Fscr (α : L.carrier) (p : ℕ) (hp : 1 ≤ p) (hαα : L.form α α = 2 * (p : ℤ)) :
    Qscr L α (Qscr L α (Qscr L α (Fscr L α))) = 0 :=
  Qscr_Escr L α p hp hαα

/-! ## §9  Packaging for the triplet normalization -/

/-- The triplet normalization `⟨α,α⟩ = 2p`, `⟨λ,α⟩ = p − 1` is exactly `wt(e^α) = 1`, the hypothesis
of `LBG_zero_comm_Qscr`. -/
theorem triplet_wt_one (lam : Fin (rank L) → ℂ) (α : L.carrier) (p : ℕ)
    (hαα : L.form α α = 2 * (p : ℤ)) (hlam : bgPair L lam α = (p : ℂ) - 1) :
    (1 / 2 : ℂ) * ((L.form α α : ℤ) : ℂ) - bgPair L lam α = 1 := by
  rw [hαα, hlam]
  push_cast
  ring

/-- **`Q` maps deformed-weight-`k` vectors to deformed-weight-`k` vectors** (the eigenvector form
of `LBG_zero_comm_Qscr`). -/
theorem Qscr_preserves_weight (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (α : L.carrier)
    (hwt : (1 / 2 : ℂ) * ((L.form α α : ℤ) : ℂ) - bgPair L lam α = 1)
    {v : LatModuleGen L} {k : ℂ} (hv : LBG L lam 0 v = k • v) :
    LBG L lam 0 (Qscr L α v) = k • Qscr L α v := by
  have h := congrArg (fun T : End ℂ (LatModuleGen L) => T v)
    (LBG_zero_comm_Qscr L hPos lam α hwt)
  simp only [Module.End.mul_apply] at h
  rw [h, hv, map_smul]

/-- `F = e^{−α} ≠ 0`. -/
theorem Fscr_ne_zero (α : L.carrier) : Fscr L α ≠ 0 :=
  latStateGen_ne_zero L (by rw [vacuumN]; exact one_ne_zero) (-α)

end VOA.LatGen.Screen


