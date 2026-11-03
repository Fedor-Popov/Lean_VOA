/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.LatticeIntertwiners

/-!
# The fusion rules of `V_{2m}`

For the rank-one lattice VOA `V_{2m} = V_L`, `L = √(2m)ℤ = ℤα`, and its modules
`V_{L+λ_j} = latticeModule m hm j` (`λ_j = j/(2m)·α`), we prove the exact fusion rules

  `fusionRule_latticeModule : N^{λ_l}_{λ_j λ_k} = if (l − j − k) % (2m) = 0 then 1 else 0`,

with `fusionRule = finrank` of the space of FHL intertwining operators, which is **proved**
finite-dimensional (`finiteDimensional_intertwiningSpace`, an instance), so the `finrank` is
honest.  The lower bound is the H1b lattice intertwiner, transported along
`V_{L+λ_{j+k}} ≅ V_{L+λ_l}` (`nontrivial_of_dvd`).

## Route (Dong–Lepowsky / FHL uniqueness), all at the level of modes

Write `e^{n}` for `𝟙 ⊗ e^{nα}` (`xv m n`) in any of the modules, `b₀ = −⌊k/2m⌋` (`bz`), so that
`0 ≤ 2m b₀ + k < 2m`.

1. **Generic vanishing lemmas** (any VOA, any modules; §1): from the Jacobi identity at `m = 0`
   (`assoc_vanish`) and the commutator formula (`comm_vanish`), the commutator with a state whose
   positive modes kill `w₁` (`comm_of_top`), the `L₀`-commutator (`comm_L0`, using the
   `L₋₁`-derivative), and: the right annihilator of `𝒴` is a submodule (`rightKer`), so `𝒴 = 0`
   as soon as it kills one nonzero vector of an irreducible `M₂` (`eq_zero_of_rightKer`).
2. **Propagation through charge sectors** (§3).  If `𝒴(e^{0}, z) e^{b₀} = 0` then: Heisenberg
   descendants in the first slot also vanish (`sector_vanish`); the first slot can be raised by
   `e^{α}` while `⟨α, λ_{b₀}⟩ ≥ 0` (`step_first`); the second slot can be lowered by `e^{−α}`
   using the commutator (`step_second`); in the sector `b₀ − 1` (where `⟨α, λ⟩ < 0`) the first slot
   can be lowered indefinitely.  Hence `e^{b₀−1}` is killed by every `𝒴(w₁, z)`, and `𝒴 = 0` by
   irreducibility of `V_{L+λ_k}` (`eq_zero_of_vac`).
3. **Heisenberg determination** (§4, `vac_of_coeff`): the annihilators act on
   `v_q = 𝒴(e^{0})₍q₎ e^{b₀}` by `α(p) v_q = χ_j(0) v_{q+p}`, so every Taylor coefficient of the
   Fock component of `v_q` is (up to a nonzero factor) a vacuum coefficient of some `v_{q'}`.
4. **Selection rule** (§4, `coeff_support`): `α(0)` forces the charge `2mn + l = j + 2mb₀ + k`
   of a nonzero vacuum coefficient, and `L₀` forces the mode `q = h_j + h_{k,b₀} − h_{l,n} − 1`.
   For `l ≢ j + k` nothing survives (`intertwiner_eq_zero`); for `l ≡ j + k` exactly one
   coefficient survives, and the linear functional `leadingCoeff` (that coefficient) is injective
   (`leadingCoeff_injective`), so `dim ≤ 1`.

## Status
No `sorry`, no new axioms; `#print axioms fusionRule_latticeModule` is
`[propext, Classical.choice, Quot.sound]`.  Unconditional: the only hypothesis is `1 ≤ m`.
-/

set_option linter.style.longLine false

namespace VOA.Huang.LatFus

open VOA VOA.IntegralLattice VOA.LatGen HeisenbergN MvPolynomial
open Module (End)
open scoped BigOperators TensorProduct

/-! ## §1  Vanishing consequences of the Jacobi identity (any VOA, any modules) -/

section Generic

universe u v₁ v₂ v₃

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]
variable {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}
  {Y : IntertwiningModes M₁ M₂ M₃}

theorem finsum_eq_zero_of_forall {M : Type*} [AddCommGroup M] {f : ℤ → M} (h : ∀ i, f i = 0) :
    ∑ᶠ i, f i = 0 := by
  rw [show f = fun _ => 0 from funext h, finsum_zero]

/-- **Associativity vanishing** (Jacobi identity at `m = 0`): if `𝒴(w₁,z)w₂ = 0` and
`𝒴(w₁,z) u₍ᵢ₎w₂ = 0` for all `i ≥ 0`, then `𝒴(u₍ℓ₎w₁, z) w₂ = 0` for every `ℓ`. -/
theorem assoc_vanish (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (h1 : ∀ p : ℂ, Y p w₁ w₂ = 0)
    (h2 : ∀ i : ℤ, 0 ≤ i → ∀ p : ℂ, Y p w₁ (mode (A₂.YM u) i w₂) = 0) (ℓ : ℤ) (n : ℂ) :
    Y n (mode (A₁.YM u) ℓ w₁) w₂ = 0 := by
  have h := hY.jacobi u w₁ w₂ ℓ 0 n
  have hR : (∑ᶠ i : ℤ, cbz 0 i • Y (((0 : ℤ) : ℂ) + n - i) (mode (A₁.YM u) (ℓ + i) w₁) w₂)
      = Y n (mode (A₁.YM u) ℓ w₁) w₂ := by
    rw [finsum_eq_single _ (0 : ℤ)]
    · simp
    · intro i hi
      simp [cbz_zero_left, hi]
  rw [hR, finsum_eq_zero_of_forall] at h
  · exact h.symm
  · intro i
    rcases lt_or_ge i 0 with hi | hi
    · rw [cbz_apply_neg ℓ hi, mul_zero, zero_smul]
    · rw [h1, map_zero, zero_add, h2 i hi, smul_zero, sub_zero, smul_zero]

/-- **Commutator vanishing**: if `𝒴(w₁,z)w₂ = 0` and `𝒴(u₍ᵢ₎w₁,z)w₂ = 0` for all `i ≥ 0`, then
`𝒴(w₁,z) u₍ₘ₎w₂ = 0` for every `m`. -/
theorem comm_vanish (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (h1 : ∀ p : ℂ, Y p w₁ w₂ = 0)
    (h2 : ∀ i : ℤ, 0 ≤ i → ∀ p : ℂ, Y p (mode (A₁.YM u) i w₁) w₂ = 0) (m : ℤ) (n : ℂ) :
    Y n w₁ (mode (A₂.YM u) m w₂) = 0 := by
  have h := hY.commutator u w₁ w₂ m n
  rw [h1, map_zero, zero_sub, finsum_eq_zero_of_forall] at h
  · exact neg_eq_zero.mp h
  · intro i
    rcases lt_or_ge i 0 with hi | hi
    · rw [cbz_apply_neg m hi, zero_smul]
    · rw [h2 i hi, smul_zero]

/-- The **Heisenberg-type commutator**: if `u₍ᵢ₎w₁ = 0` for `i > 0` and `u₍₀₎w₁ = c w₁`, then
`u₍ₘ₎ 𝒴(w₁)₍ₙ₎ w₂ − 𝒴(w₁)₍ₙ₎ u₍ₘ₎ w₂ = c 𝒴(w₁)₍ₘ₊ₙ₎ w₂`. -/
theorem comm_of_top (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (c : ℂ) (hpos : ∀ i : ℤ, 0 < i → mode (A₁.YM u) i w₁ = 0)
    (h0 : mode (A₁.YM u) 0 w₁ = c • w₁) (m : ℤ) (n : ℂ) :
    mode (A₃.YM u) m (Y n w₁ w₂) - Y n w₁ (mode (A₂.YM u) m w₂) = c • Y (m + n) w₁ w₂ := by
  rw [hY.commutator u w₁ w₂ m n, finsum_eq_single _ (0 : ℤ)]
  · rw [h0, cbz_apply_nonneg m le_rfl, Int.toNat_zero, gBinom_zero, one_smul, map_smul,
      LinearMap.smul_apply]
    simp
  · intro i hi
    rcases lt_or_gt_of_ne hi with hi | hi
    · rw [cbz_apply_neg m hi, zero_smul]
    · rw [hpos i hi, map_zero, LinearMap.zero_apply, smul_zero]

/-- The **`L₀`-commutator**: `L₀ 𝒴(w₁)₍ₙ₎ w₂ − 𝒴(w₁)₍ₙ₎ L₀ w₂ = 𝒴(L₀w₁)₍ₙ₎w₂ − (n+1) 𝒴(w₁)₍ₙ₎w₂`
(commutator formula with `ω`, `m = 1`, and the `L₋₁`-derivative property). -/
theorem comm_L0 (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) (w₁ : M₁) (w₂ : M₂) (n : ℂ) :
    mode (A₃.YM W.conformalVector) 1 (Y n w₁ w₂)
        - Y n w₁ (mode (A₂.YM W.conformalVector) 1 w₂)
      = Y n (mode (A₁.YM W.conformalVector) 1 w₁) w₂ - (n + 1) • Y n w₁ w₂ := by
  rw [hY.commutator W.conformalVector w₁ w₂ 1 n,
    finsum_eq_sum_of_support_subset _ (s := ({0, 1} : Finset ℤ))]
  · rw [Finset.sum_pair (by norm_num)]
    have hL := hY.L_neg_one w₁ (n + 1)
    simp only [OrdVModule.Lm1] at hL
    rw [cbz_apply_nonneg 1 le_rfl, cbz_apply_nonneg 1 zero_le_one]
    simp only [Int.toNat_zero, gBinom_zero, one_smul, Int.cast_one, Int.cast_zero, sub_zero]
    have e1 : (1 : ℂ) + n = n + 1 := add_comm _ _
    have e2 : (1 : ℂ) + n - 1 = n := by ring
    have e3 : n + 1 - 1 = n := by ring
    rw [e2, e1]
    have hb : gBinom 1 (Int.toNat 1) = 1 := by simp [gBinom]
    rw [hL, e3, hb, one_smul, LinearMap.smul_apply]
    module
  · intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra hne
    push Not at hne
    apply hi
    rcases lt_or_ge i 0 with h | h
    · rw [cbz_apply_neg 1 h, zero_smul]
    · have h2 : 2 ≤ i := by omega
      rw [cbz_apply_nonneg 1 h]
      have : gBinom 1 i.toNat = 0 := by
        rw [gBinom]
        rw [Finset.prod_eq_zero (i := 1) (Finset.mem_range.mpr (by omega)) (by push_cast; ring)]
        simp
      rw [this, zero_smul]

/-- The **annihilator in the second slot** `{w₂ | 𝒴(w₁,z)w₂ = 0 ∀ w₁}` is a submodule. -/
noncomputable def rightKer (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) :
    WeakModule.Submodule' A₂.toWeakModule where
  carrier :=
    { carrier := {w₂ | ∀ (w₁ : M₁) (p : ℂ), Y p w₁ w₂ = 0}
      add_mem' := by
        intro a b ha hb w₁ p
        simp only [Set.mem_setOf_eq] at ha hb
        rw [map_add, ha, hb, add_zero]
      zero_mem' := by intro w₁ p; simp
      smul_mem' := by
        intro c a ha w₁ p
        simp only [Set.mem_setOf_eq] at ha
        rw [map_smul, ha, smul_zero] }
  act_mem := by
    intro u n x hx w₁ p
    rw [WeakModule.act_def]
    have h := hY.commutator u w₁ x n p
    rw [hx w₁ p, map_zero, zero_sub, finsum_eq_zero_of_forall] at h
    · exact neg_eq_zero.mp h
    · intro i; rw [hx, smul_zero]

/-- If the second module is irreducible and some nonzero `w₂` is killed by every `𝒴(w₁,z)`,
then `𝒴 = 0`. -/
theorem eq_zero_of_rightKer (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) (hirr : A₂.IsIrreducible)
    {w₂ : M₂} (hw : w₂ ≠ 0) (h : ∀ (w₁ : M₁) (p : ℂ), Y p w₁ w₂ = 0) : Y = 0 := by
  rcases hirr.2 (rightKer hY) with hb | ht
  · exact absurd ((Submodule.eq_bot_iff _).mp hb w₂ h) hw
  · funext p
    ext w₁ x
    have hx : x ∈ (rightKer hY).carrier := by rw [ht]; trivial
    exact hx w₁ p

end Generic


/-! ## §2  The rank-one lattice modules: modes on the charged vacua -/

section Lattice

open Classification.COne Classification.COne.LatMod VOA.LatGen.Triplet VOA.Moonshine

variable (m : ℕ) (hm : 1 ≤ m)

/-- The Heisenberg state `α(-1)𝟙` of `V_{2m}`. -/
noncomputable abbrev hV : LatModuleGen (latP m) := hVec (latP m) (a0 m)

/-- The charged vacuum `𝟙 ⊗ e^{nα}` (in `V_{L+λ_j}` it stands for `e^{nα + λ_j}`). -/
noncomputable abbrev xv (n : ℤ) : LatModuleGen (latP m) := latChargeGen (latP m) n

theorem xv_ne_zero (n : ℤ) : xv m n ≠ 0 := by
  intro h
  have := congrArg (coordEα (latP m) n) h
  rw [xv, latChargeGen, latStateGen, coordEα_apply, if_pos rfl, map_zero] at this
  exact one_ne_zero this

theorem hmode_pos (j : ℤ) (n : ℤ) {i : ℤ} (hi : 0 < i) :
    mode ((latticeModule m hm j).YM (hV m)) i (xv m n) = 0 := by
  rw [xv, latChargeGen, latticeModule_hVec_mode, if_neg (by omega), add_zero,
    oscN_apply_pos _ _ _ hi]
  simp [vacuumN, latStateGen]

theorem hmode_zero (j : ℤ) (n : ℤ) :
    mode ((latticeModule m hm j).YM (hV m)) 0 (xv m n) = chi m j n • xv m n :=
  latticeModule_zeroMode m hm j _ n

/-- Charge modes on a general state: `e^β₍ᵢ₎ (p ⊗ e^{nα}) ∝ (EE p) ⊗ e^{(β+n)α}`. -/
theorem cmode (j β n i : ℤ) (p : FockN (rank (latP m))) :
    mode ((latticeModule m hm j).YM (latChargeGen (latP m) β)) i (latStateGen (latP m) p n)
      = (latCob (latP m) (glueLat m j) (glueIota m j) β
          * latticeCocycle (glueLat m j) (glueIota m j β) (glueIota m j n + glueDelta m j)) •
          latStateGen (latP m) (EEVec (latP m) β (-i - 1 - 2 * m * β * n - j * β) p) (β + n) := by
  rw [mode_apply, latticeModule_latChargeGen]

theorem cmode_xv_zero (j β n : ℤ) (hβ : 0 ≤ β * (2 * m * n + j)) {i : ℤ} (hi : 0 ≤ i) :
    mode ((latticeModule m hm j).YM (latChargeGen (latP m) β)) i (xv m n) = 0 := by
  change mode ((latticeModule m hm j).YM (latChargeGen (latP m) β)) i
    (latStateGen (latP m) (vacuumN (rank (latP m))) n) = 0
  rw [cmode, EEVec_vacuum, if_neg (by nlinarith)]
  simp [latStateGen]

theorem cmode_xv_top (j β n : ℤ) :
    ∃ c : ℂ, c ≠ 0 ∧
      mode ((latticeModule m hm j).YM (latChargeGen (latP m) β)) (-1 - β * (2 * m * n + j)) (xv m n)
        = c • xv m (β + n) := by
  refine ⟨latCob (latP m) (glueLat m j) (glueIota m j) β
          * latticeCocycle (glueLat m j) (glueIota m j β) (glueIota m j n + glueDelta m j),
    mul_ne_zero (latCob_ne_zero _ _ _ _) (LatMod.latticeCocycle_ne_zero _ _ _), ?_⟩
  change mode ((latticeModule m hm j).YM (latChargeGen (latP m) β)) _
    (latStateGen (latP m) (vacuumN (rank (latP m))) n) = _
  rw [cmode, show (-(-1 - β * (2 * m * n + j)) - 1 - 2 * m * β * n - j * β) = 0 by ring,
    EEVec_vacuum, if_pos le_rfl, Int.toNat_zero, vSchur_zero]
  rfl

theorem cmode_mem (j β n i : ℤ) (p : FockN (rank (latP m))) :
    ∃ p' : FockN (rank (latP m)),
      mode ((latticeModule m hm j).YM (latChargeGen (latP m) β)) i (latStateGen (latP m) p n)
        = latStateGen (latP m) p' (β + n) := by
  rw [cmode, ← latStateGen_csmul]
  exact ⟨_, rfl⟩


/-! ## §3  Propagation of vanishing through the charge sectors -/

section Reach

variable {j k l : ℤ}
  {Y : IntertwiningModes (LatModuleGen (latP m)) (LatModuleGen (latP m)) (LatModuleGen (latP m))}
  (hY : IsIntertwiningOperator (latticeModule m hm j) (latticeModule m hm k)
    (latticeModule m hm l) Y)

include hY in
/-- **Heisenberg descendants in the first slot**: if `𝒴(e^{a}, z) e^{b} = 0` then
`𝒴(p ⊗ e^{a}, z) e^{b} = 0` for every Fock state `p`. -/
theorem sector_vanish (a b : ℤ) (h : ∀ q : ℂ, Y q (xv m a) (xv m b) = 0)
    (p : FockN (rank (latP m))) : ∀ q : ℂ, Y q (latStateGen (latP m) p a) (xv m b) = 0 := by
  refine MvPolynomial.induction_on (motive := fun p =>
    ∀ q : ℂ, Y q (latStateGen (latP m) p a) (xv m b) = 0) p ?_ ?_ ?_
  · intro c q
    rw [show latStateGen (latP m) (MvPolynomial.C c) a = c • xv m a by
      rw [MvPolynomial.C_eq_smul_one, latStateGen_csmul]; rfl]
    rw [map_smul, LinearMap.smul_apply, h, smul_zero]
  · intro p₁ p₂ h₁ h₂ q
    rw [latStateGen_add_boson, map_add, LinearMap.add_apply, h₁, h₂, add_zero]
  · intro p₁ x h₁
    obtain ⟨k', a'⟩ := x
    have ha : a' = a0 m := by
      have h1 : a'.val < 1 := lt_of_lt_of_eq a'.isLt (rank_latP m)
      exact Fin.ext (by simp only [a0]; omega)
    subst ha
    have hx : latStateGen (latP m) (p₁ * X (k', a0 m)) a
        = mode ((latticeModule m hm j).YM (hV m)) (-((k' : ℤ) + 1)) (latStateGen (latP m) p₁ a) := by
      rw [latticeModule_hVec_mode, if_neg (by omega), add_zero, oscN_apply_neg _ _ _ (by omega),
        show (-(-((k' : ℤ) + 1)) - 1).toNat = k' by omega, mul_comm]
    intro q
    rw [hx]
    refine assoc_vanish hY (hV m) _ _ h₁ (fun i hi p' => ?_) _ q
    rcases hi.lt_or_eq with hi | hi
    · rw [hmode_pos m hm k b hi, map_zero]
    · subst hi
      rw [hmode_zero, map_smul, h₁, smul_zero]

include hY in
/-- **Charge step in the first slot** (associativity): if `β ⟨α, λ_b⟩ ≥ 0` then
`𝒴(e^{a},z)e^{b} = 0 ⟹ 𝒴(e^{a+β},z)e^{b} = 0`. -/
theorem step_first (a b β : ℤ) (hβ : 0 ≤ β * (2 * m * b + k))
    (h : ∀ q : ℂ, Y q (xv m a) (xv m b) = 0) : ∀ q : ℂ, Y q (xv m (β + a)) (xv m b) = 0 := by
  intro q
  obtain ⟨c, hc, htop⟩ := cmode_xv_top m hm j β a
  have := assoc_vanish hY (latChargeGen (latP m) β) (xv m a) (xv m b) h
    (fun i hi p => by rw [cmode_xv_zero m hm k β b hβ hi, map_zero]) (-1 - β * (2 * m * a + j)) q
  rw [htop, map_smul, LinearMap.smul_apply] at this
  exact (smul_eq_zero.mp this).resolve_left hc

include hY in
/-- **Charge step in the second slot** (commutator): `𝒴(e^{a},z)e^{b} = 0` and
`𝒴(Fock ⊗ e^{a+β},z)e^{b} = 0` give `𝒴(e^{a},z)e^{b+β} = 0`. -/
theorem step_second (a b β : ℤ) (h : ∀ q : ℂ, Y q (xv m a) (xv m b) = 0)
    (h' : ∀ (p : FockN (rank (latP m))) (q : ℂ), Y q (latStateGen (latP m) p (β + a)) (xv m b) = 0) :
    ∀ q : ℂ, Y q (xv m a) (xv m (β + b)) = 0 := by
  intro q
  obtain ⟨c, hc, htop⟩ := cmode_xv_top m hm k β b
  have := comm_vanish hY (latChargeGen (latP m) β) (xv m a) (xv m b) h
    (fun i _ p => by
      obtain ⟨p', hp'⟩ := cmode_mem m hm j β a i (vacuumN (rank (latP m)))
      rw [show xv m a = latStateGen (latP m) (vacuumN (rank (latP m))) a from rfl, hp']
      exact h' p' p) (-1 - β * (2 * m * b + k)) q
  rw [htop, map_smul] at this
  exact (smul_eq_zero.mp this).resolve_left hc

include hY in
/-- **Propagation**: for `0 ≤ 2m b₀ + k < 2m`, the single vanishing `𝒴(e^{λ_j}, z) e^{b₀} = 0`
forces `𝒴 = 0`.  (Raise the first slot along `b₀`; move down one sector in the second slot by the
commutator; sweep the first slot through all of `ℤ` there; conclude by irreducibility of
`V_{L+λ_k}`.) -/
theorem eq_zero_of_vac (b₀ : ℤ) (h0 : 0 ≤ 2 * m * b₀ + k) (h1 : 2 * m * b₀ + k < 2 * m)
    (h : ∀ q : ℂ, Y q (xv m 0) (xv m b₀) = 0) : Y = 0 := by
  have s1 : ∀ a : ℕ, ∀ q : ℂ, Y q (xv m a) (xv m b₀) = 0 := by
    intro a
    induction a with
    | zero => simpa using h
    | succ a ih =>
      have := step_first m hm hY a b₀ 1 (by linarith) ih
      rwa [show (1 : ℤ) + a = ((a + 1 : ℕ) : ℤ) by push_cast; ring] at this
  have s3 : ∀ a : ℕ, ∀ q : ℂ, Y q (xv m ((a : ℤ) + 1)) (xv m (b₀ - 1)) = 0 := by
    intro a
    have h1' := s1 (a + 1)
    rw [show ((a + 1 : ℕ) : ℤ) = (a : ℤ) + 1 by push_cast; ring] at h1'
    have := step_second m hm hY ((a : ℤ) + 1) b₀ (-1) h1' (by
      rw [show (-1 : ℤ) + ((a : ℤ) + 1) = a by ring]
      exact sector_vanish m hm hY _ _ (s1 a))
    rwa [show (-1 : ℤ) + b₀ = b₀ - 1 by ring] at this
  have s4 : ∀ t : ℕ, ∀ q : ℂ, Y q (xv m (1 - t)) (xv m (b₀ - 1)) = 0 := by
    intro t
    induction t with
    | zero => simpa using s3 0
    | succ t ih =>
      have := step_first m hm hY (1 - t) (b₀ - 1) (-1) (by nlinarith) ih
      rwa [show (-1 : ℤ) + (1 - t) = 1 - ((t + 1 : ℕ) : ℤ) by push_cast; ring] at this
  have s5 : ∀ a : ℤ, ∀ q : ℂ, Y q (xv m a) (xv m (b₀ - 1)) = 0 := by
    intro a
    rcases le_or_gt 1 a with ha | ha
    · have := s3 (a - 1).toNat
      rwa [show (((a - 1).toNat : ℕ) : ℤ) + 1 = a by omega] at this
    · have := s4 (1 - a).toNat
      rwa [show (1 : ℤ) - (((1 - a).toNat : ℕ) : ℤ) = a by omega] at this
  refine eq_zero_of_rightKer hY (latticeModule_isIrreducible m hm k) (xv_ne_zero m (b₀ - 1))
    (fun w q => ?_)
  have hf : (Y q).flip (xv m (b₀ - 1)) = 0 := by
    refine linearMap_ext_latStateGen (latP m) (fun p a => ?_)
    rw [LinearMap.flip_apply, LinearMap.zero_apply]
    exact sector_vanish m hm hY a (b₀ - 1) (s5 a) p q
  exact LinearMap.congr_fun hf w

end Reach


/-! ## §4  The vacuum coefficients: Heisenberg, `α(0)` and `L₀` -/

section Coeff

/-- The conformal weight `(2mn+j)²/(4m)` of `e^{nα + λ_j}`. -/
noncomputable def wt (j n : ℤ) : ℂ := ((((2 * m * n + j : ℤ) : ℝ) ^ 2 / (4 * m) : ℝ) : ℂ)

theorem L0_latStateGen (j : ℤ) {w : ℕ} {q : FockN (rank (latP m))}
    (hq : q ∈ HeisenbergN.gradingWN (rank (latP m)) w) (n : ℤ) :
    mode ((latticeModule m hm j).YM (V2m m hm).conformalVector) 1 (latStateGen (latP m) q n)
      = ((w : ℂ) + wt m j n) • latStateGen (latP m) q n := by
  rw [latticeModule_L0 m hm j hq n, wt]
  congr 1
  push_cast
  ring

theorem L0_xv (j n : ℤ) :
    mode ((latticeModule m hm j).YM (V2m m hm).conformalVector) 1 (xv m n) = wt m j n • xv m n := by
  rw [xv, latChargeGen, L0_latStateGen m hm j (vacuumN_mem_gradingWN _) n, Nat.cast_zero, zero_add]

/-- The Heisenberg modes in the charge coordinates. -/
theorem coordEα_hmode (l n p : ℤ) (y : LatModuleGen (latP m)) :
    coordEα (latP m) n (mode ((latticeModule m hm l).YM (hV m)) p y)
      = oscN (rank (latP m)) 1 (a0 m) p (coordEα (latP m) n y)
        + (if p = 0 then chi m l n • coordEα (latP m) n y else 0) := by
  have hext := linearMap_ext_latStateGen (latP m)
    (f := coordEα (latP m) n ∘ₗ mode ((latticeModule m hm l).YM (hV m)) p)
    (g := oscN (rank (latP m)) 1 (a0 m) p ∘ₗ coordEα (latP m) n
      + (if p = 0 then chi m l n • coordEα (latP m) n else 0)) (fun P (γ : ℤ) => by
      rw [LinearMap.comp_apply, latticeModule_hVec_mode, LinearMap.add_apply, LinearMap.comp_apply]
      by_cases hp : p = 0
      · subst hp
        simp only [latStateGen, coordEα_apply]
        have e := coordEα_apply (latP m) n γ P
        split_ifs with hn'
        · rw [LinearMap.smul_apply, e, if_pos hn']; subst hn'; rfl
        · rw [LinearMap.smul_apply, e, if_neg hn', smul_zero]; simp
      · simp only [if_neg hp, LinearMap.zero_apply, add_zero, latStateGen, coordEα_apply]
        split_ifs <;> simp)
  have := LinearMap.congr_fun hext y
  rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply] at this
  rw [this]
  by_cases hp : p = 0
  · simp [hp]
  · simp [hp]

/-- The `L₀`-eigenvalue of the vacuum coefficient of the charge-`n` sector. -/
theorem coeff0_L0 (l n : ℤ) (y : LatModuleGen (latP m)) :
    MvPolynomial.coeff 0 (coordEα (latP m) n
        (mode ((latticeModule m hm l).YM (V2m m hm).conformalVector) 1 y))
      = wt m l n * MvPolynomial.coeff 0 (coordEα (latP m) n y) := by
  set f : LatModuleGen (latP m) →ₗ[ℂ] ℂ :=
    MvPolynomial.lcoeff ℂ 0 ∘ₗ coordEα (latP m) n ∘ₗ
        mode ((latticeModule m hm l).YM (V2m m hm).conformalVector) 1
      - wt m l n • (MvPolynomial.lcoeff ℂ 0 ∘ₗ coordEα (latP m) n) with hf
  have hk : ∀ k, bigradα (latP m) k ≤ LinearMap.ker f := by
    intro k y hy
    obtain ⟨q, hq, rfl⟩ := mem_bigradα_exists hy
    rw [LinearMap.mem_ker]
    rcases lt_or_ge k.1 0 with h1 | h1
    · rw [HeisenbergN.gradingZN_of_neg h1, Submodule.mem_bot] at hq
      subst hq
      simp [latStateGen]
    · rw [HeisenbergN.gradingZN_of_nonneg h1] at hq
      rw [hf, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        L0_latStateGen m hm l hq, LinearMap.smul_apply, LinearMap.comp_apply]
      simp only [latStateGen, map_smul, coordEα_apply, MvPolynomial.lcoeff_apply, smul_eq_mul]
      by_cases hn : n = k.2
      · subst hn
        simp only [↓reduceIte]
        by_cases hw : k.1.toNat = 0
        · rw [hw]; simp
        · have hc : MvPolynomial.coeff 0 q = 0 := by
            by_contra hne
            have := (mem_gradingWN.mp hq) hne
            rw [map_zero] at this
            exact hw this.symm
          rw [hc]; simp
      · split_ifs with h'
        · exact absurd h' hn
        · simp
  have htop : LinearMap.ker f = ⊤ := by
    rw [eq_top_iff, ← bigradα_iSup_eq_top]
    exact iSup_le hk
  have := LinearMap.mem_ker.mp (htop ▸ Submodule.mem_top : y ∈ LinearMap.ker f)
  rw [hf, LinearMap.sub_apply, sub_eq_zero] at this
  simpa using this

variable {j k l : ℤ}
  {Y : IntertwiningModes (LatModuleGen (latP m)) (LatModuleGen (latP m)) (LatModuleGen (latP m))}
  (hY : IsIntertwiningOperator (latticeModule m hm j) (latticeModule m hm k)
    (latticeModule m hm l) Y)

include hY in
/-- **Heisenberg determination**: if every charge-sector vacuum coefficient of
`𝒴(e^{λ_j}, z) e^{b}` vanishes, then `𝒴(e^{λ_j}, z) e^{b} = 0`.  (The annihilators act on
`𝒴(e^{λ_j},z)e^b` as `α(p) ↦ χ z^p`, so every Taylor coefficient is a vacuum coefficient.) -/
theorem vac_of_coeff (b : ℤ)
    (h : ∀ (n : ℤ) (q : ℂ), MvPolynomial.coeff 0 (coordEα (latP m) n (Y q (xv m 0) (xv m b))) = 0) :
    ∀ q : ℂ, Y q (xv m 0) (xv m b) = 0 := by
  have hV1 : ∀ (p : ℤ), 0 < p → ∀ q : ℂ,
      mode ((latticeModule m hm l).YM (hV m)) p (Y q (xv m 0) (xv m b))
        = chi m j 0 • Y (p + q) (xv m 0) (xv m b) := by
    intro p hp q
    have := comm_of_top hY (hV m) (xv m 0) (xv m b) (chi m j 0)
      (fun i hi => hmode_pos m hm j 0 hi) (hmode_zero m hm j 0) p q
    rwa [hmode_pos m hm k b hp, map_zero, sub_zero] at this
  have key : ∀ d : ℕ, ∀ s : (ℕ × Fin (rank (latP m))) →₀ ℕ, Finsupp.degree s = d →
      ∀ (n : ℤ) (q : ℂ), MvPolynomial.coeff s (coordEα (latP m) n (Y q (xv m 0) (xv m b))) = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
    intro s hs n q
    by_cases hs0 : s = 0
    · subst hs0; exact h n q
    obtain ⟨x, hx⟩ : ∃ x, s x ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hs0 (Finsupp.ext hne)
    have hle : Finsupp.single x 1 ≤ s := by
      rw [Finsupp.single_le_iff]; omega
    set t : (ℕ × Fin (rank (latP m))) →₀ ℕ := s - Finsupp.single x 1 with ht
    have hst : s = t + Finsupp.single x 1 := (tsub_add_cancel_of_le hle).symm
    have hdeg : Finsupp.degree t < d := by
      rw [← hs, hst, map_add, Finsupp.degree_single]; omega
    obtain ⟨k', a'⟩ := x
    have ha : a' = a0 m := by
      have h1 : a'.val < 1 := lt_of_lt_of_eq a'.isLt (rank_latP m)
      exact Fin.ext (by simp only [a0]; omega)
    subst ha
    set p : ℤ := (k' : ℤ) + 1 with hpdef
    have hp : 0 < p := by omega
    have e1 := congrArg (coordEα (latP m) n) (hV1 p hp q)
    rw [coordEα_hmode, if_neg hp.ne', add_zero, oscN_apply_pos _ _ _ hp,
      show (p - 1).toNat = k' by omega, map_smul] at e1
    have e2 := congrArg (MvPolynomial.coeff t) e1
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      coeff_pderivN, IH _ hdeg t rfl n (p + q), ← hst] at e2
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have ht0 : ((t (k', a0 m) : ℕ) : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
    simp only [smul_eq_mul, one_mul, mul_zero] at e2
    rcases mul_eq_zero.mp e2 with h3 | h3
    · exact absurd h3 hp0
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 ht0
      · exact h4
  intro q
  refine LatMod.eq_zero_of_coordEα (latP m) (fun n => ?_)
  ext s
  rw [MvPolynomial.coeff_zero]
  exact key _ s rfl n q

include hY in
/-- **Selection rule for the vacuum coefficients**: a nonzero vacuum coefficient of
`𝒴(e^{λ_j})₍q₎ e^{b}` in the charge-`n` sector of `V_{L+λ_l}` forces charge conservation
`2mn + l = j + 2mb + k` (from `α(0)`) and `q = h_j + h_{k,b} − h_{l,n} − 1` (from `L₀`). -/
theorem coeff_support (b n : ℤ) (q : ℂ)
    (hne : MvPolynomial.coeff 0 (coordEα (latP m) n (Y q (xv m 0) (xv m b))) ≠ 0) :
    2 * m * n + l = j + (2 * m * b + k) ∧ q = wt m j 0 + wt m k b - wt m l n - 1 := by
  set c := MvPolynomial.coeff 0 (coordEα (latP m) n (Y q (xv m 0) (xv m b))) with hc
  constructor
  · have hZ := comm_of_top hY (hV m) (xv m 0) (xv m b) (chi m j 0)
      (fun i hi => hmode_pos m hm j 0 hi) (hmode_zero m hm j 0) 0 q
    rw [hmode_zero m hm k b, map_smul, Int.cast_zero, zero_add, sub_eq_iff_eq_add] at hZ
    have e1 := congrArg (fun y => MvPolynomial.coeff 0 (coordEα (latP m) n y)) hZ
    simp only at e1
    rw [coordEα_hmode, if_pos rfl, oscN_zero, LinearMap.zero_apply, zero_add, map_add, map_smul,
      map_smul, MvPolynomial.coeff_smul, MvPolynomial.coeff_add, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, ← hc, smul_eq_mul, smul_eq_mul, smul_eq_mul] at e1
    have e2 : chi m l n = chi m j 0 + chi m k b := by
      have : (chi m l n - (chi m j 0 + chi m k b)) * c = 0 := by linear_combination e1
      rcases mul_eq_zero.mp this with h3 | h3
      · linear_combination h3
      · exact absurd h3 hne
    have e3 := congrArg (· * chargeCoord (latP m) (1 : ℤ) (a0 m)) e2
    simp only [add_mul, chi_mul m hm] at e3
    push_cast at e3
    have : ((2 * m * n + l : ℤ) : ℂ) = ((j + (2 * m * b + k) : ℤ) : ℂ) := by
      push_cast; linear_combination e3
    exact_mod_cast this
  · have hL := comm_L0 hY (xv m 0) (xv m b) q
    rw [L0_xv m hm k b, L0_xv m hm j 0, map_smul, map_smul, LinearMap.smul_apply,
      sub_eq_iff_eq_add] at hL
    have e1 := congrArg (fun y => MvPolynomial.coeff 0 (coordEα (latP m) n y)) hL
    simp only at e1
    rw [coeff0_L0, map_add, map_sub, map_smul, map_smul, map_smul, MvPolynomial.coeff_add,
      MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_smul, ← hc, smul_eq_mul, smul_eq_mul, smul_eq_mul] at e1
    have : (wt m l n - (wt m j 0 + wt m k b - q - 1)) * c = 0 := by linear_combination e1
    rcases mul_eq_zero.mp this with h3 | h3
    · linear_combination h3
    · exact absurd h3 hne

end Coeff


/-! ## §5  The fusion rules -/

section Fusion

/-- The base charge sector `b₀ = −⌊k/2m⌋` of `V_{L+λ_k}`, with `0 ≤ 2m b₀ + k < 2m`. -/
def bz (k : ℤ) : ℤ := -(k / (2 * m))

include hm in
theorem bz_bounds (k : ℤ) : 0 ≤ 2 * m * bz m k + k ∧ 2 * m * bz m k + k < 2 * m := by
  have h2m : (0 : ℤ) < 2 * m := by have : (1 : ℤ) ≤ m := by exact_mod_cast hm
                                   omega
  have he : 2 * m * bz m k + k = k % (2 * m) := by
    rw [bz, Int.emod_def]; ring
  rw [he]
  exact ⟨Int.emod_nonneg _ h2m.ne', Int.emod_lt_of_pos _ h2m⟩

variable {j k l : ℤ}
  {Y : IntertwiningModes (LatModuleGen (latP m)) (LatModuleGen (latP m)) (LatModuleGen (latP m))}

/-- **Uniqueness**: an intertwiner of type `(V_{L+λ_l} / V_{L+λ_j} V_{L+λ_k})` all of whose
vacuum coefficients `⟨e^{n}*, 𝒴(e^{λ_j})₍q₎ e^{b₀}⟩` vanish is zero. -/
theorem eq_zero_of_coeffs (hY : IsIntertwiningOperator (latticeModule m hm j) (latticeModule m hm k)
      (latticeModule m hm l) Y)
    (h : ∀ (n : ℤ) (q : ℂ),
      MvPolynomial.coeff 0 (coordEα (latP m) n (Y q (xv m 0) (xv m (bz m k)))) = 0) : Y = 0 :=
  eq_zero_of_vac m hm hY (bz m k) (bz_bounds m hm k).1 (bz_bounds m hm k).2
    (vac_of_coeff m hm hY _ h)

/-- **Charge conservation**: for `l ≢ j + k (mod 2m)` every intertwiner of type
`(V_{L+λ_l} / V_{L+λ_j} V_{L+λ_k})` vanishes. -/
theorem intertwiner_eq_zero (hjkl : ¬ (2 * (m : ℤ)) ∣ l - j - k)
    (hY : IsIntertwiningOperator (latticeModule m hm j) (latticeModule m hm k)
      (latticeModule m hm l) Y) : Y = 0 := by
  refine eq_zero_of_coeffs m hm hY (fun n q => ?_)
  by_contra hne
  obtain ⟨h1, _⟩ := coeff_support m hm hY _ n q hne
  exact hjkl ⟨bz m k - n, by linarith⟩

/-- Evaluation of mode data at `(q, w₁, w₂)`, a linear map. -/
noncomputable def evalModes {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂]
    [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃] (q : ℂ) (w₁ : M₁) (w₂ : M₂) :
    IntertwiningModes M₁ M₂ M₃ →ₗ[ℂ] M₃ where
  toFun Y := Y q w₁ w₂
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (j k l)

/-- The target charge sector `n' = b₀ + (j + k − l)/(2m)` of the leading coefficient. -/
def nTop : ℤ := bz m k + (j + k - l) / (2 * m)

/-- The leading mode `q* = h_j + h_{k,b₀} − h_{l,n'} − 1`. -/
noncomputable def qTop : ℂ := wt m j 0 + wt m k (bz m k) - wt m l (nTop m j k l) - 1

/-- **The leading-coefficient functional** `𝒴 ↦ ⟨e^{n'}*, 𝒴(e^{λ_j})₍q*₎ e^{b₀}⟩` on the space
of intertwining operators of type `(V_{L+λ_l} / V_{L+λ_j} V_{L+λ_k})`. -/
noncomputable def leadingCoeff :
    IntertwiningOperator (latticeModule m hm j) (latticeModule m hm k) (latticeModule m hm l)
      →ₗ[ℂ] ℂ :=
  MvPolynomial.lcoeff ℂ 0 ∘ₗ coordEα (latP m) (nTop m j k l) ∘ₗ
    evalModes (qTop m j k l) (xv m 0) (xv m (bz m k)) ∘ₗ
    (intertwiningSpace (latticeModule m hm j) (latticeModule m hm k) (latticeModule m hm l)).subtype

include hm in
/-- **The leading coefficient determines the intertwiner** (`l ≡ j + k mod 2m`), on mode data. -/
theorem eq_zero_of_leading (hdiv : (2 * (m : ℤ)) ∣ l - j - k)
    {Y : IntertwiningModes (LatModuleGen (latP m)) (LatModuleGen (latP m)) (LatModuleGen (latP m))}
    (hY : IsIntertwiningOperator (latticeModule m hm j) (latticeModule m hm k)
      (latticeModule m hm l) Y)
    (h0 : MvPolynomial.coeff 0 (coordEα (latP m) (nTop m j k l)
      (Y (qTop m j k l) (xv m 0) (xv m (bz m k)))) = 0) : Y = 0 := by
  refine eq_zero_of_coeffs m hm hY (fun n q => ?_)
  by_contra hne
  obtain ⟨h1, h2⟩ := coeff_support m hm hY _ n q hne
  obtain ⟨t, ht⟩ := hdiv
  have h2m : (2 * (m : ℤ)) ≠ 0 := by have : (1 : ℤ) ≤ m := by exact_mod_cast hm
                                     omega
  have hn : n = nTop m j k l := by
    rw [nTop, show j + k - l = 2 * m * (-t) by linarith, Int.mul_ediv_cancel_left _ h2m]
    have : 2 * (m : ℤ) * (n - bz m k + t) = 0 := by linarith
    rcases mul_eq_zero.mp this with h3 | h3
    · exact absurd h3 h2m
    · linarith
  subst hn
  rw [← qTop] at h2
  subst h2
  exact hne h0

include hm in
/-- The leading-coefficient functional is injective (`l ≡ j + k mod 2m`). -/
theorem leadingCoeff_injective (hdiv : (2 * (m : ℤ)) ∣ l - j - k) :
    Function.Injective (leadingCoeff m hm j k l) := by
  rintro ⟨Y₁, h₁⟩ ⟨Y₂, h₂⟩ h
  have hs : IsIntertwiningOperator (latticeModule m hm j) (latticeModule m hm k)
      (latticeModule m hm l) (Y₁ - Y₂) :=
    (intertwiningSpace (latticeModule m hm j) (latticeModule m hm k)
      (latticeModule m hm l)).sub_mem h₁ h₂
  have hz := eq_zero_of_leading m hm j k l hdiv hs (by
    change MvPolynomial.coeff 0 (coordEα (latP m) (nTop m j k l)
      (Y₁ (qTop m j k l) (xv m 0) (xv m (bz m k)) - Y₂ (qTop m j k l) (xv m 0) (xv m (bz m k)))) = 0
    rw [map_sub, MvPolynomial.coeff_sub, sub_eq_zero]
    exact h)
  exact Subtype.ext (sub_eq_zero.mp hz)

/-- **Finite-dimensionality** of every intertwiner space among the `V_{L+λ_j}` (proved, not
assumed): it injects into `ℂ` (or is zero). -/
instance finiteDimensional_intertwiningSpace :
    FiniteDimensional ℂ
      (IntertwiningOperator (latticeModule m hm j) (latticeModule m hm k) (latticeModule m hm l)) := by
  by_cases hdiv : (2 * (m : ℤ)) ∣ l - j - k
  · exact Module.Finite.of_injective _ (leadingCoeff_injective m hm j k l hdiv)
  · refine Module.Finite.of_injective
      (0 : IntertwiningOperator (latticeModule m hm j) (latticeModule m hm k)
        (latticeModule m hm l) →ₗ[ℂ] ℂ) (fun Y₁ Y₂ _ => Subtype.ext ?_)
    rw [intertwiner_eq_zero m hm hdiv Y₁.2, intertwiner_eq_zero m hm hdiv Y₂.2]

/-- For `l ≡ j + k (mod 2m)` there is a nonzero intertwiner of type
`(V_{L+λ_l} / V_{L+λ_j} V_{L+λ_k})`: the lattice intertwiner of H1b, transported along
`V_{L+λ_{j+k}} ≅ V_{L+λ_l}`. -/
theorem nontrivial_of_dvd (hdiv : (2 * (m : ℤ)) ∣ l - j - k) :
    Nontrivial
      (IntertwiningOperator (latticeModule m hm j) (latticeModule m hm k) (latticeModule m hm l)) := by
  obtain ⟨e⟩ := (latticeModule_iso_iff m hm (j + k) l).mpr (by
    obtain ⟨t, ht⟩ := hdiv
    exact ⟨-t, by linarith⟩)
  have hW : LatInt.IsIntertwiningW (latticeModule m hm j).toWeakModule
      (latticeModule m hm k).toWeakModule (latticeModule m hm (j + k)).toWeakModule
      (LatInt.latticeIntwModes m hm j k) :=
    let h := LatInt.isIntertwiningOperator_latticeIntwModes m hm j k
    ⟨h.truncation, h.L_neg_one, h.jacobi⟩
  have hT := hW.transport (B₁ := (latticeModule m hm j).toWeakModule)
    (B₂ := (latticeModule m hm k).toWeakModule) (B₃ := (latticeModule m hm l).toWeakModule)
    (LinearEquiv.refl ℂ _) (LinearEquiv.refl ℂ _) e.toLinearEquiv
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun u n x => e.map_act u n x)
  refine ⟨⟨⟨_, hT.toIsIntertwiningOperator⟩, 0, fun h0 => ?_⟩⟩
  have hne := LatInt.transportModes_ne_zero (LinearEquiv.refl ℂ _) (LinearEquiv.refl ℂ _)
    e.toLinearEquiv (LatInt.latticeIntwModes_leading_ne_zero m hm j k)
  apply hne
  have h1 := congrArg Subtype.val h0
  simp only [ZeroMemClass.coe_zero] at h1
  rw [h1]
  rfl

/-- **H2a: the fusion rules of `V_{2m}`** (`L = √(2m)ℤ`):

  `N^{λ_l}_{λ_j λ_k} = 1` if `l ≡ j + k (mod 2m)`, and `0` otherwise,

with `fusionRule = finrank` of the space of FHL intertwining operators, which is proved
finite-dimensional (`finiteDimensional_intertwiningSpace`), so the `finrank` is honest. -/
theorem fusionRule_latticeModule :
    fusionRule (latticeModule m hm j) (latticeModule m hm k) (latticeModule m hm l)
      = if (l - j - k) % (2 * (m : ℤ)) = 0 then 1 else 0 := by
  split_ifs with h
  · have hdiv : (2 * (m : ℤ)) ∣ l - j - k := Int.dvd_of_emod_eq_zero h
    have hnt := nontrivial_of_dvd m hm j k l hdiv
    refine le_antisymm ?_ ?_
    · have := LinearMap.finrank_le_finrank_of_injective (leadingCoeff_injective m hm j k l hdiv)
      rwa [Module.finrank_self] at this
    · exact (Module.finrank_pos_iff (R := ℂ) (M := IntertwiningOperator (latticeModule m hm j)
        (latticeModule m hm k) (latticeModule m hm l))).mpr hnt
  · have hnd : ¬ (2 * (m : ℤ)) ∣ l - j - k := fun hd => h (Int.emod_eq_zero_of_dvd hd)
    haveI : Subsingleton
        (IntertwiningOperator (latticeModule m hm j) (latticeModule m hm k)
          (latticeModule m hm l)) :=
      ⟨fun Y₁ Y₂ => Subtype.ext (by
        rw [intertwiner_eq_zero m hm hnd Y₁.2, intertwiner_eq_zero m hm hnd Y₂.2])⟩
    exact Module.finrank_zero_of_subsingleton

end Fusion

end Lattice

end VOA.Huang.LatFus
