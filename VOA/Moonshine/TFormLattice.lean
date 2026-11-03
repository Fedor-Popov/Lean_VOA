/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TFormAlg

/-!
# The invariant symmetric form on `T` for an even unimodular lattice  (Moonshine step M8c)

Let `L` be even unimodular and `T = Rep (cocMat L) _` the extraspecial module, with operators
`e_α = eT α`.  Write `Q(α) = ⟨α,α⟩/2` (`halfNorm`).

* `signQ` — the sign function `ᾱ ↦ (-1)^{Q(α)}` on `L/2L ≅ (ZMod 2)^rank`; well defined
  (`signQ_red`) and a quadratic sign for the commutator cocycle (`isQuadSign_signQ`,
  from `Q(α+β) = Q(α) + Q(β) + ⟨α,β⟩` and `ε(α,β)ε(β,α) = (-1)^{⟨α,β⟩}`).
* `iotaL` — the anti-involution of `End(T)` with `iotaL (e_α) = (-1)^{Q(α)} e_α` (`iotaL_eT`).
* `Lagrangian L` — data `γ₀,…,γ_{m-1} ∈ L` with `⟨γᵢ,γⱼ⟩` even, `Q(γᵢ)` even, and "partners"
  `gᵢ` with `⟨gᵢ,γⱼ⟩` even for `j < i` and odd for `j = i`, and `2^m = dim T`.  (Its image in
  `L/2L` is a maximal totally singular subspace of `Q`; the partners certify independence.)
* From it, `projP k = ∏_{i<k} (1 + F_i)/2` with `F_i = σᵢ e_{γᵢ}`, `σᵢ² = ε(γᵢ,γᵢ)`:
  commuting ι-fixed involutions, so `projP m` is a ι-fixed idempotent (`isIdempotentElem_projP`,
  `iotaL_projP`); conjugating by the anticommuting `e_{gₖ}` kills `tr(projP k · F_k)`, so
  `tr(projP k) = dim T / 2^k` (`trace_projP`) and `tr(projP m) = 1`.
* `exists_TForm` — **a nondegenerate symmetric form with
  `B(e_α t, t') = (-1)^{⟨α,α⟩/2} B(t, e_α t')`**, conditional on a `Lagrangian L`.

## The sign
The invariance sign is `(-1)^{⟨α,α⟩/2}`, i.e. the transpose of `e_α` is `(-1)^{⟨α,α⟩/2} e_α`
(`= (-1)^{⟨α,α⟩/2} e_{-α}`, as `eT_neg`), which is the factor `(-1)^{L₀}` of the contragredient
vertex operator `Y(e^{zL₁}(-z^{-2})^{L₀} e^α, z^{-1})`.  The *group* anti-involution
`e_α ↦ e_α^{-1} = ε(α,α) e_α` is **not** used: its sign function `ᾱ ↦ ε(α,α)` differs from
`(-1)^{Q}` by a basis-dependent character, and its form is symmetric or alternating according to
the Arf invariant of `x ↦ x·(cocMat) x`, which depends on the (noncomputable) `latticeBasis`.
Checked numerically for `E₈` (rank 8, `T` of dimension 16, Pauli model): for random
`GL₈(ℤ)`-bases, `#{x : x·Mx = 0}` is `136` or `120`, so the `ε(α,α)`-form is alternating for some
bases, while the `(-1)^Q`-form (`#{Q even} = 136`) is always symmetric, unique up to scalar.

## Status
All declarations proved, no `sorry`; `exists_TForm` is conditional on `Lagrangian L`, discharged
for the Leech lattice in `TForm.lean`.  Reached from the umbrella `VOA/Moonshine.lean`.
-/

namespace VOA.IntegralLattice

open Module LinearMap VOA.Moonshine.Extraspecial

variable (L : VOA.IntegralLattice)

/-- `Q(α) = ⟨α,α⟩/2`. -/
def halfNorm (α : L.carrier) : ℤ := L.form α α / 2

variable {L}

theorem two_mul_halfNorm (hEven : L.Even) (α : L.carrier) : 2 * halfNorm L α = L.form α α :=
  Int.mul_ediv_cancel' (hEven α)

theorem halfNorm_add (hEven : L.Even) (α β : L.carrier) :
    halfNorm L (α + β) = halfNorm L α + halfNorm L β + L.form α β := by
  have h1 := two_mul_halfNorm hEven (α + β)
  have h2 := two_mul_halfNorm hEven α
  have h3 := two_mul_halfNorm hEven β
  have hs := form_symm L β α
  simp only [map_add, LinearMap.add_apply] at h1
  omega

theorem neg_one_zpow_halfNorm_add_two_nsmul (hEven : L.Even) (α γ : L.carrier) :
    (-1 : ℂ) ^ halfNorm L (α + 2 • γ) = (-1 : ℂ) ^ halfNorm L α := by
  have h : halfNorm L (α + 2 • γ) = halfNorm L α + 2 * (2 * halfNorm L γ + L.form α γ) := by
    rw [halfNorm_add hEven, two_nsmul, halfNorm_add hEven, map_add]
    have := two_mul_halfNorm hEven γ
    ring_nf; omega
  rw [h, zpow_add₀ (by norm_num), zpow_mul, show ((-1 : ℂ) ^ (2 : ℤ)) = 1 by norm_num, one_zpow,
    mul_one]

variable (L)

/-- The sign `ᾱ ↦ (-1)^{Q(α)}` on `L/2L`. -/
noncomputable def signQ (x : Fin L.bRank → ZMod 2) : ℂ :=
  (-1 : ℂ) ^ halfNorm L (red_surjective L x).choose

variable {L}

theorem signQ_red (hEven : L.Even) (α : L.carrier) :
    signQ L (red L α) = (-1 : ℂ) ^ halfNorm L α := by
  set β := (red_surjective L (red L α)).choose
  have hβ : red L β = red L α := (red_surjective L (red L α)).choose_spec
  obtain ⟨γ, hγ⟩ := (red_eq_zero_iff L (β - α)).mp (by rw [map_sub, hβ, sub_self])
  have : β = α + 2 • γ := by rw [← hγ]; abel
  rw [signQ, show (red_surjective L (red L α)).choose = α + 2 • γ from this,
    neg_one_zpow_halfNorm_add_two_nsmul hEven]

theorem isQuadSign_signQ (hEven : L.Even) : IsQuadSign (cocMat L) (signQ L) where
  zero := by
    rw [← map_zero (red L), signQ_red hEven]
    simp [halfNorm]
  add x y := by
    obtain ⟨α, rfl⟩ := red_surjective L x
    obtain ⟨β, rfl⟩ := red_surjective L y
    rw [← map_add, signQ_red hEven, signQ_red hEven, signQ_red hEven, ← latticeCocycle_eq_coc,
      ← latticeCocycle_eq_coc, latticeCocycle_comm L hEven, halfNorm_add hEven,
      zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]

section Unimodular

variable (L) (hEven : L.Even) (hU : IsUnit (gramMat L).det)

/-- The anti-involution `e_α ↦ (-1)^{⟨α,α⟩/2} e_α` of `End(T)`. -/
noncomputable def iotaL :
    Module.End ℂ (Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) →ₗ[ℂ]
      Module.End ℂ (Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :=
  iotaT (cocMat L) (isUnit_det_cocMat L hEven hU) (signQ L)

theorem iotaL_mul (X Y : Module.End ℂ (Rep (cocMat L) (isUnit_det_cocMat L hEven hU))) :
    iotaL L hEven hU (X * Y) = iotaL L hEven hU Y * iotaL L hEven hU X :=
  iotaT_mul _ (isQuadSign_signQ hEven) X Y

theorem iotaL_one : iotaL L hEven hU 1 = 1 := iotaT_one _ (isQuadSign_signQ hEven)

theorem eA_eq_algBasis (α : L.carrier) : eA L α = algBasis (cocMat L) (red L α) := by
  rw [algBasis_apply]; rfl

theorem iotaL_eT (α : L.carrier) :
    iotaL L hEven hU (eT L hEven hU α) = (-1 : ℂ) ^ halfNorm L α • eT L hEven hU α := by
  rw [iotaL, eT, eA_eq_algBasis, iotaT_op, signQ_red hEven]

/-- `e_a e_b = (-1)^{⟨a,b⟩} e_b e_a`. -/
theorem eT_comm_sign' (a b : L.carrier) :
    eT L hEven hU a * eT L hEven hU b
      = ((-1 : ℂ) ^ (L.form a b)) • (eT L hEven hU b * eT L hEven hU a) := by
  rw [eT_mul, eT_mul, smul_smul, ← latticeCocycle_comm L hEven a b, add_comm b a, mul_assoc,
    latticeCocycle_sq, mul_one]

theorem eT_mul_self' (a : L.carrier) :
    eT L hEven hU a * eT L hEven hU a = latticeCocycle L a a • 1 := by
  rw [eT_mul]
  congr 1
  have h := eT_add_two_nsmul L hEven hU 0 a
  rw [zero_add, eT_zero, two_nsmul] at h
  exact h

theorem commute_eT_of_even {a b : L.carrier} (h : _root_.Even (L.form a b)) :
    Commute (eT L hEven hU a) (eT L hEven hU b) := by
  rw [Commute, SemiconjBy, eT_comm_sign', h.neg_one_zpow, one_smul]

theorem eT_anticomm_of_odd {a b : L.carrier} (h : Odd (L.form a b)) :
    eT L hEven hU a * eT L hEven hU b = -(eT L hEven hU b * eT L hEven hU a) := by
  rw [eT_comm_sign', h.neg_one_zpow, neg_one_smul]

end Unimodular

/-- **Lagrangian data** for `L`: `γᵢ` spanning a totally singular subspace of `(L/2L, Q)` with
partners `gᵢ` (`⟨gᵢ,γⱼ⟩` even for `j < i`, odd for `j = i`), of size `2^m = dim T`. -/
structure Lagrangian (L : VOA.IntegralLattice) where
  m : ℕ
  γ : ℕ → L.carrier
  g : ℕ → L.carrier
  form_even : ∀ i < m, ∀ j < m, _root_.Even (L.form (γ i) (γ j))
  halfNorm_even : ∀ i < m, _root_.Even (halfNorm L (γ i))
  partner_even : ∀ i < m, ∀ j < i, _root_.Even (L.form (g i) (γ j))
  partner_odd : ∀ i < m, Odd (L.form (g i) (γ i))
  two_mul_m : 2 * m = L.bRank

section Construction

variable (L) (hEven : L.Even) (hU : IsUnit (gramMat L).det) (D : Lagrangian L)

local notation "TT" => Rep (cocMat L) (isUnit_det_cocMat L hEven hU)

/-- A square root of `ε(γᵢ,γᵢ)`. -/
noncomputable def sqrtEpsL (a : L.carrier) : ℂ :=
  (IsAlgClosed.exists_eq_mul_self (latticeCocycle L a a)).choose

theorem sqrtEpsL_mul_self (a : L.carrier) :
    sqrtEpsL L a * sqrtEpsL L a = latticeCocycle L a a :=
  (IsAlgClosed.exists_eq_mul_self (latticeCocycle L a a)).choose_spec.symm

/-- The involutions `F_i = σᵢ e_{γᵢ}`. -/
noncomputable def lagF (i : ℕ) : Module.End ℂ TT :=
  sqrtEpsL L (D.γ i) • eT L hEven hU (D.γ i)

/-- `projP k = ∏_{i<k} (1 + F_i)/2`. -/
noncomputable def projP : ℕ → Module.End ℂ TT
  | 0 => 1
  | k + 1 => projP k * ((1 / 2 : ℂ) • (1 + lagF L hEven hU D k))

variable {L}

theorem lagF_mul_self (i : ℕ) : lagF L hEven hU D i * lagF L hEven hU D i = 1 := by
  rw [lagF, smul_mul_smul_comm, eT_mul_self', smul_smul, sqrtEpsL_mul_self, latticeCocycle_sq,
    one_smul]

theorem commute_lagF {i j : ℕ} (hi : i < D.m) (hj : j < D.m) :
    Commute (lagF L hEven hU D i) (lagF L hEven hU D j) :=
  ((commute_eT_of_even L hEven hU (D.form_even i hi j hj)).smul_left _).smul_right _

theorem iotaL_lagF {i : ℕ} (hi : i < D.m) : iotaL L hEven hU (lagF L hEven hU D i) =
    lagF L hEven hU D i := by
  rw [lagF, map_smul, iotaL_eT, (D.halfNorm_even i hi).neg_one_zpow, one_smul]

theorem commute_lagF_projP {j : ℕ} (hj : j < D.m) :
    ∀ k ≤ D.m, Commute (lagF L hEven hU D j) (projP L hEven hU D k)
  | 0, _ => Commute.one_right _
  | k + 1, hk => by
      refine (commute_lagF_projP hj k (by omega)).mul_right ?_
      exact ((Commute.one_right _).add_right (commute_lagF hEven hU D hj (by omega))).smul_right _

theorem isIdempotentElem_half {F : Module.End ℂ TT} (hF : F * F = 1) :
    IsIdempotentElem ((1 / 2 : ℂ) • (1 + F)) := by
  rw [IsIdempotentElem, smul_mul_smul_comm, add_mul, mul_add, mul_add, hF, one_mul, mul_one,
    one_mul]
  module

theorem isIdempotentElem_projP : ∀ k ≤ D.m, IsIdempotentElem (projP L hEven hU D k)
  | 0, _ => IsIdempotentElem.one
  | k + 1, hk => by
      refine IsIdempotentElem.mul_of_commute ?_ (isIdempotentElem_projP k (by omega))
        (isIdempotentElem_half hEven hU (lagF_mul_self hEven hU D k))
      exact ((Commute.one_right _).add_right
        (commute_lagF_projP hEven hU D (j := k) (by omega) k (by omega)).symm).smul_right _

theorem iotaL_projP : ∀ k ≤ D.m, iotaL L hEven hU (projP L hEven hU D k) = projP L hEven hU D k
  | 0, _ => iotaL_one L hEven hU
  | k + 1, hk => by
      rw [projP, iotaL_mul, iotaL_projP k (by omega), map_smul, map_add, iotaL_one,
        iotaL_lagF hEven hU D (by omega)]
      exact ((Commute.one_left _).add_left
        (commute_lagF_projP hEven hU D (j := k) (by omega) k (by omega))).smul_left _

theorem commute_partner_projP {k : ℕ} (hk : k < D.m) :
    ∀ l ≤ k, Commute (eT L hEven hU (D.g k)) (projP L hEven hU D l)
  | 0, _ => Commute.one_right _
  | l + 1, hl => by
      refine (commute_partner_projP hk l (by omega)).mul_right ?_
      refine ((Commute.one_right _).add_right ?_).smul_right _
      exact (commute_eT_of_even L hEven hU (D.partner_even k hk l (by omega))).smul_right _

theorem trace_projP_mul_lagF {k : ℕ} (hk : k < D.m) :
    trace ℂ TT (projP L hEven hU D k * lagF L hEven hU D k) = 0 := by
  set G := eT L hEven hU (D.g k)
  set P := projP L hEven hU D k
  set F := lagF L hEven hU D k
  have hGP : G * P = P * G := commute_partner_projP hEven hU D hk k le_rfl
  have hGF : G * F = -(F * G) := by
    simp only [G, F, lagF, mul_smul_comm, smul_mul_assoc, ← smul_neg]
    rw [eT_anticomm_of_odd L hEven hU (D.partner_odd k hk)]
  have hGG : G * G = latticeCocycle L (D.g k) (D.g k) • 1 := eT_mul_self' L hEven hU _
  have h1 : trace ℂ TT (P * F * G * G) = trace ℂ TT (G * (P * F * G)) :=
    trace_mul_comm ℂ (P * F * G) G
  have hX : G * (P * F * G) = -(P * F * G * G) := by
    rw [← mul_assoc, ← mul_assoc, hGP, mul_assoc P G F, hGF]; noncomm_ring
  rw [hX, map_neg, mul_assoc (P * F), hGG, mul_smul_comm, mul_one, map_smul] at h1
  have hc : latticeCocycle L (D.g k) (D.g k) ≠ 0 := by
    intro h; have := latticeCocycle_sq L (D.g k) (D.g k); rw [h, zero_mul] at this
    exact zero_ne_one this
  have h2 : latticeCocycle L (D.g k) (D.g k) * trace ℂ TT (P * F) = 0 := by
    rw [smul_eq_mul] at h1
    linear_combination h1 / 2
  exact (mul_eq_zero.mp h2).resolve_left hc

theorem trace_projP : ∀ k ≤ D.m,
    trace ℂ TT (projP L hEven hU D k) * 2 ^ k = (finrank ℂ TT : ℂ)
  | 0, _ => by simp [projP, trace_one]
  | k + 1, hk => by
      rw [projP, mul_smul_comm, mul_add, mul_one, map_smul, map_add,
        trace_projP_mul_lagF hEven hU D (by omega), add_zero, ← trace_projP k (by omega),
        smul_eq_mul, pow_succ]
      ring

theorem trace_projP_m : trace ℂ TT (projP L hEven hU D D.m) = 1 := by
  have h := trace_projP hEven hU D D.m le_rfl
  have hb : L.bRank / 2 = D.m := by have := D.two_mul_m; omega
  have h3 : ((2 ^ (L.bRank / 2) : ℕ) : ℂ) = 2 ^ D.m := by rw [hb]; push_cast; rfl
  rw [finrank_rep, h3] at h
  have h2 : (2 : ℂ) ^ D.m ≠ 0 := pow_ne_zero _ two_ne_zero
  calc _ = trace ℂ TT (projP L hEven hU D D.m) * 2 ^ D.m / 2 ^ D.m := by field_simp
    _ = 1 := by rw [h, div_self h2]

/-- **The invariant form** (conditional on Lagrangian data): there is a nondegenerate
**symmetric** bilinear form `B` on `T` with `B(e_α t, t') = (-1)^{⟨α,α⟩/2} B(t, e_α t')`; more
generally `B(X t, t') = B(t, ι(X) t')` for all `X ∈ End(T)`. -/
theorem exists_TForm (D : Lagrangian L) :
    ∃ B : LinearMap.BilinForm ℂ TT, (∀ t t', B t t' = B t' t) ∧ B.Nondegenerate ∧
      ∀ X t t', B (X t) t' = B t (iotaL L hEven hU X t') :=
  exists_form_of_idempotent _ (isQuadSign_signQ hEven)
    (isIdempotentElem_projP hEven hU D D.m le_rfl) (iotaL_projP hEven hU D D.m le_rfl)
    (trace_projP_m hEven hU D)

end Construction

end VOA.IntegralLattice
