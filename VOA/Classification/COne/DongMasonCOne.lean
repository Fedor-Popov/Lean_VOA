/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.Inputs
import VOA.Classification.COne.LatticeRational

/-!
# Dong–Mason at `c = 1`: staged reduction of `IDongMason`

`IDongMason` (`Inputs.lean`): a nice VOA `W` with `c = 1` and `W₁ ≠ 0` is isomorphic to some
`V_{2m}`. This file proves the algebraic front end of the Dong–Mason argument and isolates the
rest as two named, published facts.

## Proved here (no `sorry`, no new axioms)

* §1 `DMCOne.exists_heisVector`: a strongly rational `W` with `W₁ ≠ 0` has `h ∈ W₁` with
  `h₍₁₎h = 𝟙` (self-duality: the normalized invariant form gives `u₍₁₎v = -(u|v)𝟙` on `W₁`,
  nondegenerate and symmetric there; take an anisotropic vector and rescale).
* §2 `DMCOne.IsHeisVector.smul_self` (`h₍ᵢ₎h = δ_{i,1}𝟙`), `DMCOne.heis_comm_of` (Heisenberg
  relations on every weak `W`-module), `DMCOne.heisRep` (`W` is a positive-energy Heisenberg
  module), `DMCOne.fock_decomposition` (`W ≅ M(1) ⊗ Ω`, via `HeisSvN.fockEquiv`).
* §3 `DMCOne.heis_smul_conformal` (`h₍q₎ω = q h₍q₋₂₎𝟙`), `DMCOne.heis_smul_omegaH`,
  `DMCOne.conformal_sub_omegaH_mem_commutant` (`ω − ω_h ∈ Com⟨h⟩`),
  `DMCOne.commutant_le_iff`: `Com⟨h⟩ = ℂ𝟙 ⟺ ω = ω_h := ½ h₍₋₁₎h`.
* §4 (with `ω = ω_h`) `DMCOne.L0_on_vac_of_conformal_eq` (`L₀ = ½ h₍₀₎²` on `Ω`),
  `DMCOne.vac_charge_sq` (a vacuum vector of charge `λ` lies in `Wₙ` with `λ² = 2n`),
  `DMCOne.vac_split` (`h₍₀₎` is semisimple on `Ω`).
* §5 non-vacuity: `V2m_isHeisVector`, `V2m_conformal_eq_omegaH` (`ω = ½h₍₋₁₎h` in `V_{2m}`),
  `V2m_commutant_le`.
* §6 `iDongMason_of_facts : HeisCommutantTrivial → HeisLatticeReconstruction → IDongMason`.

## The named facts (true, published; see their docstrings)

* `HeisCommutantTrivial` (DM-1, analytic): nice, `c = 1`, `h₍₁₎h = 𝟙` ⟹ `Com⟨h⟩ = ℂ𝟙`
  (Dong–Mason 2004, proof of Thm 3: effective central charge of the commutant).
* `HeisLatticeReconstruction` (DM-2, algebraic): strongly rational and `ω = ½h₍₋₁₎h` ⟹
  `W ≅ V_{2m}` (multiplicity one, charge lattice, uniqueness of lattice VOAs).

DM-1 is where modular invariance enters; it is not provable from the present library.
DM-2 is algebraic; its next brick is the `W`-analog of `proj_charge_der` (`LatticeRational2`):
for `e ∈ Ω_α`, `L₋₁e = α h₍₋₁₎e` (from `ω = ω_h`), so the vacuum projection of `e₍ₖ₎x`, `x ∈ Ω_β`,
vanishes unless `k = −αβ − 1`.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

namespace DMCOne

open VOA VOA.VertexOperatorAlgebra Module

universe u

variable {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲] {W : VertexOperatorAlgebra 𝒲}

/-! ## §1 A normalized Heisenberg vector in `W₁` -/

/-- A nonzero vector of `W₁` pairs nontrivially with some vector of `W₁` under a nondegenerate
invariant form. -/
theorem exists_grading_one_pair {B : InvariantForm W} (hrad : InvariantForm.leftRadical B = ⊥)
    {u : 𝒲} (hu : u ∈ W.grading 1) (hu0 : u ≠ 0) : ∃ v ∈ W.grading 1, B.form u v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hu0 ?_
  have hmem : u ∈ InvariantForm.leftRadical B := by
    rw [InvariantForm.mem_leftRadical]
    refine LinearMap.ext fun b => ?_
    simp only [LinearMap.zero_apply]
    have hbtop : b ∈ ⨆ i, W.grading i := by
      rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction W.grading (motive := fun b => B.form u b = 0) hbtop ?_ ?_ ?_
    · intro i x hx
      rcases eq_or_ne (1 : ℤ) i with rfl | hne
      · exact hcon x hx
      · exact InvariantForm.orthogonal_of_ne B hne hu hx
    · exact map_zero _
    · intro x y hx hy; rw [map_add, hx, hy, add_zero]
  rw [hrad, Submodule.mem_bot] at hmem
  exact hmem

/-- **A normalized Heisenberg vector.** If `W` is strongly rational and `W₁ ≠ 0`, there is
`h ∈ W₁` with `h₍₁₎h = 𝟙`. (Self-duality gives a nondegenerate fully invariant form, normalized
so that `u₍₁₎v = -(u|v)𝟙` on `W₁`; the pairing is symmetric on `W₁`, hence anisotropic somewhere;
rescale by a square root.) -/
theorem exists_heisVector (hW : StronglyRational W) (h1 : finrank ℂ (W.grading 1) ≠ 0) :
    ∃ h ∈ W.grading 1, W.smul h 1 h = W.vacuum := by
  obtain ⟨B, hBf, hrad⟩ := hW.selfDual
  have hvac : W.vacuum ≠ 0 := hW.toStronglyFinite.vacuum_ne_zero
  have hκ : B.form W.vacuum W.vacuum ≠ 0 := form_vacuum_ne_zero_of_leftRadical_eq_bot hvac hrad
  set κ := B.form W.vacuum W.vacuum
  set B' := InvariantForm.scale κ⁻¹ B
  have hB'f : B'.IsFullyInvariant := hBf.scale κ⁻¹
  have hB'n : B'.Normalized := by
    rw [InvariantForm.Normalized, InvariantForm.NormalizedAt, InvariantForm.scale_form_apply,
      smul_eq_mul, inv_mul_cancel₀ hκ]
  have heval : ∀ {u v : 𝒲}, u ∈ W.grading 1 → v ∈ W.grading 1 →
      W.smul u 1 v = -B'.form u v • W.vacuum := fun hu hv =>
    InvariantForm.eval_oneMode_grading1 hB'f hB'n hu hv
  have hsymm : ∀ {u v : 𝒲}, u ∈ W.grading 1 → v ∈ W.grading 1 → B'.form u v = B'.form v u := by
    intro u v hu hv
    have h := oneMode_symm_grading1 W hu hv
    rw [heval hu hv, heval hv hu] at h
    have h' := smul_left_injective ℂ hvac h
    simpa using h'
  -- a nonzero `u ∈ W₁`
  have hne : W.grading 1 ≠ ⊥ := by
    intro hbot; apply h1; rw [hbot]; simp
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨v, hv, huv⟩ := exists_grading_one_pair hrad hu hu0
  have huv' : B'.form u v ≠ 0 := by
    rw [InvariantForm.scale_form_apply, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero hκ) huv
  -- an anisotropic vector
  obtain ⟨x, hx, hxx⟩ : ∃ x ∈ W.grading 1, B'.form x x ≠ 0 := by
    by_cases hu' : B'.form u u ≠ 0
    · exact ⟨u, hu, hu'⟩
    by_cases hv' : B'.form v v ≠ 0
    · exact ⟨v, hv, hv'⟩
    push Not at hu' hv'
    refine ⟨u + v, add_mem hu hv, ?_⟩
    simp only [map_add, LinearMap.add_apply]
    rw [hu', hv', hsymm hv hu]
    intro h0
    apply huv'
    have : (2 : ℂ) * B'.form u v = 0 := by rw [← h0]; ring
    simpa using this
  -- rescale
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (-(B'.form x x)⁻¹) (by norm_num : 0 < 2)
  refine ⟨s • x, Submodule.smul_mem _ s hx, ?_⟩
  rw [W.smul_smul_left, W.smul_smul_right, heval hx hx]
  simp only [smul_smul]
  convert one_smul ℂ W.vacuum using 2
  have : s * (s * -(B'.form x) x) = -(s ^ 2 * B'.form x x) := by ring
  rw [this, hs]; field_simp


/-! ## §2 The Heisenberg algebra of `h` -/

/-- A **unit Heisenberg vector**: `h ∈ W₁` with `h₍₁₎h = 𝟙`. -/
structure IsHeisVector (W : VertexOperatorAlgebra 𝒲) (h : 𝒲) : Prop where
  mem : h ∈ W.grading 1
  one : W.smul h 1 h = W.vacuum

/-- The nonnegative products of a unit Heisenberg vector with itself: `h₍ᵢ₎h = δ_{i,1} 𝟙`. -/
theorem IsHeisVector.smul_self {h : 𝒲} (hh : IsHeisVector W h) {i : ℤ} (hi : 0 ≤ i) :
    W.smul h i h = if i = 1 then W.vacuum else 0 := by
  rcases eq_or_lt_of_le hi with rfl | hi'
  · rw [if_neg (by norm_num)]
    have h2 := smul_zero_add_swap_eq_zero W hh.mem hh.mem
    have : (2 : ℂ) • W.smul h 0 h = 0 := by rw [two_smul]; exact h2
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  · by_cases h1 : i = 1
    · rw [if_pos h1, h1, hh.one]
    · rw [if_neg h1]
      have hmem := W.smul_mem_grading hh.mem hh.mem i
      rw [W.positivity _ (by omega), Submodule.mem_bot] at hmem
      exact hmem

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- **The Heisenberg relations on every weak `W`-module**: `[h(p), h(q)] = p δ_{p+q,0}`. -/
theorem heis_comm_of (N : WeakModule W M) {h : 𝒲} (hh : IsHeisVector W h) (p q : ℤ) (x : M) :
    N.act h p (N.act h q x) - N.act h q (N.act h p x)
      = (if p + q = 0 then (p : ℂ) else 0) • x := by
  have hJ := N.jacobi h h x 0 p q
  rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul]),
    finsum_eq_single _ (1 : ℤ) (fun i hi => by
      rcases lt_or_ge i 0 with hneg | hnn
      · rw [cbz_apply_neg _ hneg, zero_smul]
      · rw [zero_add, hh.smul_self hnn, if_neg hi, map_zero]
        simp)] at hJ
  simp only [zero_add, add_zero, sub_zero, cbz_zero, negOnePow, mul_one] at hJ
  rw [if_pos (Even.zero : Even (0 : ℤ)), one_smul, one_smul] at hJ
  rw [hh.smul_self (by norm_num : (0 : ℤ) ≤ 1), if_pos rfl, N.vacuum_YM, mode_one,
    cbz_apply_nonneg _ (by norm_num)] at hJ
  rw [WeakModule.act_def, WeakModule.act_def, WeakModule.act_def, WeakModule.act_def, hJ]
  simp only [gBinom, Finset.range_one, Finset.prod_singleton, Nat.cast_zero, sub_zero,
    Nat.factorial_one, Nat.cast_one, div_one, Int.toNat_one]
  by_cases hpq : p + q = 0
  · rw [if_pos (by omega), if_pos hpq]; simp
  · rw [if_neg (by omega), if_neg hpq]; simp

/-- Modes of a weight-one vector lower the degree: `h₍ₙ₎ Wₖ ⊆ W_{k-n}`. -/
theorem heis_mode_mem {h : 𝒲} (hh : IsHeisVector W h) {k : ℤ} {x : 𝒲} (hx : x ∈ W.grading k)
    (n : ℤ) : mode (W.Y h) n x ∈ W.grading (k - n) := by
  have := W.smul_mem_grading hh.mem hx n
  rw [show (1 : ℤ) + k - n - 1 = k - n by ring] at this
  exact this

/-- **`W` is a positive-energy Heisenberg module** over the modes of a unit Heisenberg vector
(`κ = 1`), so the abstract Stone–von Neumann theorem `HeisSvN` applies to `W` itself. -/
noncomputable def heisRep {h : 𝒲} (hh : IsHeisVector W h) : HeisSvN.HeisRep 𝒲 where
  a n := mode (W.Y h) n
  κ := 1
  κ_ne := one_ne_zero
  comm p q := by
    refine LinearMap.ext fun x => ?_
    have hc := heis_comm_of (adjointWeakModule W) hh p q x
    simp only [WeakModule.act_def] at hc
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply, mul_one]
    exact hc
  bdd x := by
    have hx : x ∈ ⨆ k, W.grading k := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
    induction hx using Submodule.iSup_induction' with
    | mem k y hy =>
      refine ⟨k.toNat, fun n hn => ?_⟩
      have h' := heis_mode_mem hh hy n
      rw [W.positivity _ (by omega), Submodule.mem_bot] at h'
      exact h'
    | zero => exact ⟨0, fun n _ => map_zero _⟩
    | add y z _ _ hy hz =>
      obtain ⟨Ny, hNy⟩ := hy
      obtain ⟨Nz, hNz⟩ := hz
      refine ⟨max Ny Nz, fun n hn => ?_⟩
      rw [map_add, hNy n (by omega), hNz n (by omega), add_zero]
  nilp x n hn := by
    have hx : x ∈ ⨆ k, W.grading k := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
    induction hx using Submodule.iSup_induction' with
    | mem k y hy =>
      have hlev : ∀ J : ℕ, (mode (W.Y h) n ^ J) y ∈ W.grading (k - n * J) := by
        intro J
        induction J with
        | zero => simpa using hy
        | succ J ih =>
          rw [pow_succ', Module.End.mul_apply]
          have h' := heis_mode_mem hh ih n
          convert h' using 2
          push_cast; ring
      refine ⟨k.toNat + 1, ?_⟩
      have h' := hlev (k.toNat + 1)
      have hle : ((k.toNat + 1 : ℕ) : ℤ) ≤ n * ((k.toNat + 1 : ℕ) : ℤ) :=
        le_mul_of_one_le_left (by positivity) (by omega)
      rw [W.positivity _ (by push_cast at hle ⊢; omega), Submodule.mem_bot] at h'
      exact h'
    | zero => exact ⟨0, map_zero _⟩
    | add y z _ _ hy hz =>
      obtain ⟨Jy, hJy⟩ := hy
      obtain ⟨Jz, hJz⟩ := hz
      refine ⟨Jy + Jz, ?_⟩
      have e1 : (mode (W.Y h) n ^ (Jy + Jz)) y = 0 := by
        rw [add_comm, pow_add, Module.End.mul_apply, hJy, map_zero]
      have e2 : (mode (W.Y h) n ^ (Jy + Jz)) z = 0 := by
        rw [pow_add, Module.End.mul_apply, hJz, map_zero]
      rw [map_add, e1, e2, add_zero]

@[simp] theorem heisRep_a {h : 𝒲} (hh : IsHeisVector W h) (n : ℤ) :
    (heisRep hh).a n = mode (W.Y h) n := rfl

/-- **Fock decomposition of `W`** (Stone–von Neumann for the Heisenberg subalgebra):
`W ≅ M(1) ⊗ Ω` with `Ω = {x : h₍ₙ₎x = 0, n > 0}`, compatibly with `h₍₀₎`. -/
theorem fock_decomposition {h : 𝒲} (hh : IsHeisVector W h) :
    Function.Bijective (heisRep hh).fockMap ∧
      ∀ f, (heisRep hh).fockMap (Finsupp.mapRange.linearMap (heisRep hh).vacZero f)
        = mode (W.Y h) 0 ((heisRep hh).fockMap f) :=
  ⟨⟨(heisRep hh).fockMap_injective, (heisRep hh).fockMap_surjective⟩,
    (heisRep hh).fockMap_vacZero⟩


/-! ## §3 The Heisenberg conformal vector and the commutant -/

/-- The Heisenberg conformal vector `ω_h = ½ h₍₋₁₎h` (central charge `1`). -/
noncomputable def omegaH (W : VertexOperatorAlgebra 𝒲) (h : 𝒲) : 𝒲 :=
  (1 / 2 : ℂ) • W.smul h (-1) h

/-- The **Heisenberg commutant** `Com(⟨h⟩) = {x : h₍ₙ₎x = 0 for all n ≥ 0}`: the vacuum space
`Ω` intersected with `ker h₍₀₎` (charge zero). -/
def commutant (W : VertexOperatorAlgebra 𝒲) (h : 𝒲) : Submodule ℂ 𝒲 :=
  ⨅ (n : ℤ) (_ : 0 ≤ n), LinearMap.ker (mode (W.Y h) n)

theorem mem_commutant {h x : 𝒲} : x ∈ commutant W h ↔ ∀ n : ℤ, 0 ≤ n → W.smul h n x = 0 := by
  simp [commutant, Submodule.mem_iInf, PreVertexAlgebra.smul_def]

theorem vacuum_mem_commutant (h : 𝒲) : W.vacuum ∈ commutant W h :=
  mem_commutant.mpr fun _ hn => W.smul_vacuum_nonneg h hn

/-- The products `ω₍ᵢ₎h` for a unit Heisenberg vector of a strongly rational `W`
(`h` is primary of weight one: `L₁h = 0` by self-duality). -/
theorem conformal_smul_heis (hW : StronglyRational W) {h : 𝒲} (hh : IsHeisVector W h) {i : ℤ}
    (hi0 : 0 ≤ i) : W.smul W.conformalVector i h =
      if i = 0 then W.toPreVertexAlgebra.T h else if i = 1 then h else 0 := by
  rcases eq_or_lt_of_le hi0 with rfl | hi
  · rw [if_pos rfl, T_eq_Lneg1, W.L_def]
    rfl
  rcases eq_or_lt_of_le (show 1 ≤ i by omega) with rfl | hi
  · rw [if_neg (by norm_num), if_pos rfl]
    have := W.L_zero_grading h hh.mem
    rw [W.L_def] at this
    simpa using this
  · rw [if_neg (by omega), if_neg (by omega)]
    rcases eq_or_lt_of_le (show 2 ≤ i by omega) with rfl | hi2
    · have := hW.L_one_grading_one_eq_zero hh.mem
      rw [W.L_def] at this
      exact this
    · have hmem := W.smul_mem_grading W.conformal_mem hh.mem i
      rw [W.positivity _ (by omega), Submodule.mem_bot] at hmem
      exact hmem

/-- `h₍q₎ω = q · h₍q₋₂₎𝟙` for `q ≥ 0`: hence `h₍₁₎ω = h` and `h₍q₎ω = 0` otherwise. From the
commutator formula `[ω₍₋₁₎, h₍q₎]𝟙 = Σᵢ C(-1,i) (ω₍ᵢ₎h)₍q₋₁₋ᵢ₎𝟙`. -/
theorem heis_smul_conformal (hW : StronglyRational W) {h : 𝒲} (hh : IsHeisVector W h) {q : ℤ}
    (hq : 0 ≤ q) : W.smul h q W.conformalVector = (q : ℂ) • W.smul h (q - 2) W.vacuum := by
  have hJ := W.jacobi W.conformalVector h W.vacuum 0 (-1) q
  rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])] at hJ
  have hsupp : (Function.support fun i : ℤ => cbz (-1) i •
      W.smul (W.smul W.conformalVector (0 + i) h) (-1 + q - i) W.vacuum) ⊆
      (({0, 1} : Finset ℤ) : Set ℤ) := by
    intro i hi
    rw [Function.mem_support] at hi
    by_contra hcon
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hcon
    apply hi
    rcases lt_or_ge i 0 with hneg | hnn
    · rw [cbz_apply_neg _ hneg, zero_smul]
    · rw [zero_add, conformal_smul_heis hW hh hnn, if_neg hcon.1, if_neg hcon.2]
      simp
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_pair (by norm_num)] at hJ
  simp only [add_zero, zero_add, sub_zero] at hJ
  rw [conformal_smul_heis hW hh le_rfl, if_pos rfl,
    conformal_smul_heis hW hh zero_le_one, if_neg one_ne_zero, if_pos rfl, cbz_zero,
    cbz_apply_nonneg _ zero_le_one, gBinom_neg_one, smul_T_apply] at hJ
  simp only [negOnePow, cbz_zero, mul_one, if_pos (Even.zero : Even (0 : ℤ)), one_smul] at hJ
  rw [W.smul_vacuum_nonneg h hq, W.smul_zero_right, W.smul_vacuum_neg_one] at hJ
  rw [zero_sub, Int.toNat_one, pow_one, neg_one_smul, ← Int.cast_smul_eq_zsmul ℂ] at hJ
  have := congrArg Neg.neg hJ
  rw [neg_neg, show (-1 : ℤ) + q - 1 = q - 2 by ring] at this
  rw [this]
  push_cast
  module

/-- The Heisenberg relations inside `W`, in the `smul` API. -/
theorem heis_comm {h : 𝒲} (hh : IsHeisVector W h) (p q : ℤ) (x : 𝒲) :
    W.smul h p (W.smul h q x) - W.smul h q (W.smul h p x)
      = (if p + q = 0 then (p : ℂ) else 0) • x :=
  heis_comm_of (adjointWeakModule W) hh p q x

/-- `h₍ₙ₎ω_h = δ_{n,1} h` for `n ≥ 0`. -/
theorem heis_smul_omegaH {h : 𝒲} (hh : IsHeisVector W h) {n : ℤ} (hn : 0 ≤ n) :
    W.smul h n (omegaH W h) = if n = 1 then h else 0 := by
  have hc := heis_comm hh n (-1) h
  rw [hh.smul_self hn] at hc
  rw [omegaH, W.smul_smul_right, sub_eq_iff_eq_add.mp hc]
  by_cases h1 : n = 1
  · subst h1
    rw [if_pos rfl, if_pos (by norm_num), if_pos rfl, W.smul_vacuum_neg_one]
    module
  · rw [if_neg h1, if_neg (by omega), if_neg h1, W.smul_zero_right]
    simp

theorem omegaH_mem {h : 𝒲} (hh : IsHeisVector W h) : omegaH W h ∈ W.grading 2 := by
  have := W.smul_mem_grading hh.mem hh.mem (-1)
  rw [show (1 : ℤ) + 1 - -1 - 1 = 2 by ring] at this
  exact Submodule.smul_mem _ _ this

/-- **`ω − ω_h` lies in the Heisenberg commutant.** -/
theorem conformal_sub_omegaH_mem_commutant (hW : StronglyRational W) {h : 𝒲}
    (hh : IsHeisVector W h) : W.conformalVector - omegaH W h ∈ commutant W h := by
  rw [mem_commutant]
  intro n hn
  rw [PreVertexAlgebra.smul_def, map_sub, ← PreVertexAlgebra.smul_def, ← PreVertexAlgebra.smul_def,
    heis_smul_conformal hW hh hn, heis_smul_omegaH hh hn]
  by_cases h1 : n = 1
  · subst h1; rw [if_pos rfl]; norm_num
  · rw [if_neg h1, sub_zero]
    rcases lt_or_ge n 2 with h2 | h2
    · have : n = 0 := by omega
      subst this; simp
    · rw [W.smul_vacuum_nonneg h (by omega), smul_zero]

/-- Distinct homogeneous pieces of `W` intersect trivially. -/
theorem grading_disjoint {m n : ℤ} (hmn : m ≠ n) : Disjoint (W.grading m) (W.grading n) :=
  W.isInternal.submodule_iSupIndep.pairwiseDisjoint hmn

/-- **Trivial commutant forces `ω = ω_h`.** -/
theorem conformal_eq_omegaH_of_commutant (hW : StronglyRational W) {h : 𝒲}
    (hh : IsHeisVector W h) (hC : commutant W h ≤ ℂ ∙ W.vacuum) :
    W.conformalVector = omegaH W h := by
  have h1 := hC (conformal_sub_omegaH_mem_commutant hW hh)
  rw [← W.vacuum_grade] at h1
  have h2 : W.conformalVector - omegaH W h ∈ W.grading 2 :=
    sub_mem W.conformal_mem (omegaH_mem hh)
  have := (Submodule.disjoint_def.mp (grading_disjoint (W := W) (by norm_num : (0 : ℤ) ≠ 2))) _ h1 h2
  exact sub_eq_zero.mp this

/-- On the Heisenberg vacuum space, `(h₍₋₁₎h)₍₁₎ = h₍₀₎²` (the normal-ordered product, from the
iterate formula `mode_iterate`). -/
theorem normalOrder_one_on_vac {h : 𝒲} {x : 𝒲} (hx : ∀ n : ℤ, 0 < n → W.smul h n x = 0) :
    W.smul (W.smul h (-1) h) 1 x = W.smul h 0 (W.smul h 0 x) := by
  rw [VOA.VertexOperatorAlgebra.mode_iterate W h h (-1) 1 x, finsum_eq_single _ 0 (fun i hi => by
    rw [hx _ (by omega), W.smul_zero_right, hx _ (by omega), W.smul_zero_right, smul_zero,
      sub_zero, smul_zero])]
  rw [hx _ (by norm_num), W.smul_zero_right]
  simp

/-- **`L₀ = ½ h₍₀₎²` on the vacuum space when `ω = ω_h`.** -/
theorem L0_on_vac_of_conformal_eq {h : 𝒲} (hω : W.conformalVector = omegaH W h) {x : 𝒲}
    (hx : ∀ n : ℤ, 0 < n → W.smul h n x = 0) :
    W.L 0 x = (1 / 2 : ℂ) • W.smul h 0 (W.smul h 0 x) := by
  rw [W.L_def, hω, omegaH, map_smul, mode_smul, LinearMap.smul_apply, zero_add,
    ← PreVertexAlgebra.smul_def, normalOrder_one_on_vac hx]

/-- `L₀ x = n x` forces `x ∈ Wₙ` (the grading is the `L₀`-eigenspace decomposition). -/
theorem mem_grading_of_L0 {n : ℤ} {x : 𝒲} (hx : W.L 0 x = (n : ℂ) • x) : x ∈ W.grading n := by
  have hle : ∀ k : ℤ, W.grading k ≤ (W.L 0).eigenspace (k : ℂ) := fun k y hy =>
    Module.End.mem_eigenspace_iff.mpr (W.L_zero_grading y hy)
  have hxtop : x ∈ ⨆ k, W.grading k := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
  rw [iSup_split_single _ n, Submodule.mem_sup] at hxtop
  obtain ⟨a, ha, b, hb, rfl⟩ := hxtop
  have hb' : b ∈ ⨆ (μ : ℂ) (_ : μ ≠ (n : ℂ)), (W.L 0).eigenspace μ := by
    have hle2 : (⨆ (k : ℤ) (_ : k ≠ n), W.grading k) ≤
        ⨆ (μ : ℂ) (_ : μ ≠ (n : ℂ)), (W.L 0).eigenspace μ :=
      iSup₂_le fun k hk => (hle k).trans
        (le_iSup₂_of_le (f := fun (μ : ℂ) (_ : μ ≠ (n : ℂ)) => (W.L 0).eigenspace μ) (k : ℂ)
          (by exact_mod_cast hk) le_rfl)
    exact hle2 hb
  have hbe : b ∈ (W.L 0).eigenspace (n : ℂ) := by
    rw [Module.End.mem_eigenspace_iff]
    have ha' := W.L_zero_grading a ha
    rw [map_add, ha', smul_add] at hx
    exact add_left_cancel hx
  have := (Submodule.disjoint_def.mp ((Module.End.eigenspaces_iSupIndep (W.L 0)) (n : ℂ))) b hbe hb'
  rw [this, add_zero]
  exact ha

/-- **`ω = ω_h` forces a trivial commutant.** Together with
`conformal_eq_omegaH_of_commutant`: for strongly rational `W`, `Com(⟨h⟩) = ℂ𝟙 ⟺ ω = ω_h`. -/
theorem commutant_le_of_conformal_eq {h : 𝒲} (hω : W.conformalVector = omegaH W h) :
    commutant W h ≤ ℂ ∙ W.vacuum := by
  intro x hx
  rw [mem_commutant] at hx
  have hL : W.L 0 x = ((0 : ℤ) : ℂ) • x := by
    rw [L0_on_vac_of_conformal_eq hω (fun n hn => hx n hn.le), hx 0 le_rfl, W.smul_zero_right]
    simp
  rw [← W.vacuum_grade]
  exact mem_grading_of_L0 hL

/-- **The two forms of the Dong–Mason step agree**: for a unit Heisenberg vector of a strongly
rational `W`, the commutant is `ℂ𝟙` iff `ω = ω_h`. -/
theorem commutant_le_iff (hW : StronglyRational W) {h : 𝒲} (hh : IsHeisVector W h) :
    commutant W h ≤ ℂ ∙ W.vacuum ↔ W.conformalVector = omegaH W h :=
  ⟨conformal_eq_omegaH_of_commutant hW hh, commutant_le_of_conformal_eq⟩

/-! ## §4 The vacuum space when `ω = ω_h`: charges and semisimplicity of `h₍₀₎` -/

/-- An `L₀`-eigenvector has an integer eigenvalue and lies in the corresponding `Wₖ`. -/
theorem exists_int_of_L0_eigen {μ : ℂ} {x : 𝒲} (hx : W.L 0 x = μ • x) (hx0 : x ≠ 0) :
    ∃ k : ℤ, μ = k ∧ x ∈ W.grading k := by
  by_cases hμ : ∃ k : ℤ, μ = k
  · obtain ⟨k, rfl⟩ := hμ
    exact ⟨k, rfl, mem_grading_of_L0 hx⟩
  · exfalso
    push Not at hμ
    have hle : (⨆ k, W.grading k) ≤ ⨆ (ν : ℂ) (_ : ν ≠ μ), (W.L 0).eigenspace ν :=
      iSup_le fun k y hy => (le_iSup₂_of_le (f := fun (ν : ℂ) (_ : ν ≠ μ) => (W.L 0).eigenspace ν)
        (k : ℂ) (fun h => hμ k h.symm) le_rfl)
          (Module.End.mem_eigenspace_iff.mpr (W.L_zero_grading y hy))
    have hxtop : x ∈ ⨆ k, W.grading k := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
    exact hx0 ((Submodule.disjoint_def.mp ((Module.End.eigenspaces_iSupIndep (W.L 0)) μ)) x
      (Module.End.mem_eigenspace_iff.mpr hx) (hle hxtop))

/-- **Charges of vacuum vectors.** If `ω = ω_h`, a nonzero vacuum vector `x` with `h₍₀₎x = λx`
lies in `Wₙ` with `λ² = 2n`, `n ∈ ℕ`. -/
theorem vac_charge_sq {h : 𝒲} (hω : W.conformalVector = omegaH W h) {x : 𝒲}
    (hx : ∀ n : ℤ, 0 < n → W.smul h n x = 0) (hx0 : x ≠ 0) {c : ℂ} (hc : W.smul h 0 x = c • x) :
    ∃ n : ℕ, c ^ 2 = 2 * n ∧ x ∈ W.grading n := by
  have hL : W.L 0 x = ((1 / 2 : ℂ) * c ^ 2) • x := by
    rw [L0_on_vac_of_conformal_eq hω hx, hc, W.smul_smul_right, hc, smul_smul, smul_smul]
    ring_nf
  obtain ⟨k, hk, hxk⟩ := exists_int_of_L0_eigen hL hx0
  have hk0 : 0 ≤ k := by
    by_contra hneg
    rw [W.positivity k (by omega), Submodule.mem_bot] at hxk
    exact hx0 hxk
  refine ⟨k.toNat, ?_, ?_⟩
  · have : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hk0
    rw [this, ← hk]; ring
  · rwa [Int.toNat_of_nonneg hk0]

/-- If `ω = ω_h`, then `h₍₀₎² = 2n` on `Ω ∩ Wₙ`. -/
theorem h0_sq_on_vac {h : 𝒲} (hω : W.conformalVector = omegaH W h) {n : ℤ} {x : 𝒲}
    (hx : ∀ k : ℤ, 0 < k → W.smul h k x = 0) (hxn : x ∈ W.grading n) :
    W.smul h 0 (W.smul h 0 x) = (2 * n : ℂ) • x := by
  have h1 := L0_on_vac_of_conformal_eq hω hx
  rw [W.L_zero_grading x hxn] at h1
  have := congrArg ((2 : ℂ) • ·) h1
  simp only [smul_smul] at this
  rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_smul] at this
  rw [← this]

/-- **`h₍₀₎` is semisimple on the vacuum space** when `ω = ω_h`: every `x ∈ Ω ∩ Wₙ` splits as
`x₊ + x₋` with `h₍₀₎x_± = ±s x_±`, `s² = 2n`. (For `n = 0`, `s = 0`.) -/
theorem vac_split {h : 𝒲} (hω : W.conformalVector = omegaH W h) {n : ℕ} {x : 𝒲}
    (hx : ∀ k : ℤ, 0 < k → W.smul h k x = 0) (hxn : x ∈ W.grading n) :
    ∃ s : ℂ, s ^ 2 = 2 * n ∧ ∃ xp xm : 𝒲, x = xp + xm ∧
      W.smul h 0 xp = s • xp ∧ W.smul h 0 xm = (-s) • xm := by
  have hsq := h0_sq_on_vac hω hx hxn
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: `Ω ∩ W₀ = ℂ𝟙` and `h₍₀₎𝟙 = 0`
    refine ⟨0, by simp, x, 0, by simp, ?_, by simp⟩
    rw [Nat.cast_zero, W.vacuum_grade] at hxn
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxn
    rw [W.smul_smul_right, W.smul_vacuum_nonneg h le_rfl]
    simp
  · obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((2 : ℂ) * n) (by norm_num : 0 < 2)
    have hs0 : s ≠ 0 := by
      rintro rfl
      have : (2 : ℂ) * n ≠ 0 := by
        have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
        exact mul_ne_zero two_ne_zero this
      exact this (by rw [← hs]; ring)
    have hsq' : W.smul h 0 (W.smul h 0 x) = (s ^ 2) • x := by rw [hsq, hs]; push_cast; ring_nf
    refine ⟨s, hs, (1 / 2 : ℂ) • (x + s⁻¹ • W.smul h 0 x),
      (1 / 2 : ℂ) • (x - s⁻¹ • W.smul h 0 x), by module, ?_, ?_⟩
    · have hsub : W.smul h 0 (x - s⁻¹ • W.smul h 0 x)
          = W.smul h 0 x - s⁻¹ • W.smul h 0 (W.smul h 0 x) := by
        rw [PreVertexAlgebra.smul_def, map_sub, map_smul]; rfl
      have hadd : W.smul h 0 (x + s⁻¹ • W.smul h 0 x)
          = W.smul h 0 x + s⁻¹ • W.smul h 0 (W.smul h 0 x) := by
        rw [PreVertexAlgebra.smul_def, map_add, map_smul]; rfl
      rw [W.smul_smul_right, hadd, hsq', smul_smul]
      have e1 : s⁻¹ * s ^ 2 = s := by field_simp
      rw [e1]
      match_scalars <;> field_simp
    · have hsub : W.smul h 0 (x - s⁻¹ • W.smul h 0 x)
          = W.smul h 0 x - s⁻¹ • W.smul h 0 (W.smul h 0 x) := by
        rw [PreVertexAlgebra.smul_def, map_sub, map_smul]; rfl
      rw [W.smul_smul_right, hsub, hsq', smul_smul]
      have e1 : s⁻¹ * s ^ 2 = s := by field_simp
      rw [e1]
      match_scalars <;> field_simp

end DMCOne

/-! ## §5 Non-vacuity: `V_{2m}` and its boson satisfy every hypothesis -/

section V2mCheck

open VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet HeisenbergN MvPolynomial LatMod

variable (m : ℕ) (hm : 1 ≤ m)

theorem V2m_isHeisVector : DMCOne.IsHeisVector (V2m m hm) (hb m) :=
  ⟨hb_mem_grading m hm, by rw [hb_smul_hb m hm zero_le_one, if_pos rfl]⟩

/-- In `V_{2m}`, `ω = ½ h₍₋₁₎h`: the lattice conformal vector is the Heisenberg one. -/
theorem V2m_conformal_eq_omegaH : (V2m m hm).conformalVector = DMCOne.omegaH (V2m m hm) (hb m) := by
  have key := latVOA_smul_bosonState (latP m) (latP_even m) (latP_posDef m hm) (a0 m) 0 (X (0, a0 m)) 0
  rw [show (-((0:ℕ):ℤ)) - 1 = -1 by norm_num] at key
  have key' : (latticeVOAGen (latP m) (latP_even m) (latP_posDef m hm)).smul
      (bosonState (latP m) (a0 m)) (-1) (bosonState (latP m) (a0 m))
        = latStateGen (latP m) (X (0, a0 m) * X (0, a0 m)) 0 := key
  rw [DMCOne.omegaH, hb, V2m, key']
  change omegaLatGen (latP m) = _
  rw [omegaLatGen, ωN, Finset.sum_eq_single (a0 m)]
  · rw [ωNa, oscN_neg_one_sq_vacuumN, mkEα_apply]
    simp [latStateGen, sq, TensorProduct.smul_tmul']
  · intro b _ hb
    exfalso; apply hb
    have h1 : (b : ℕ) < 1 := lt_of_lt_of_eq b.2 (rank_latP m)
    ext; simp [a0]; omega
  · simp

/-- In `V_{2m}` the Heisenberg commutant of the boson is `ℂ𝟙`. -/
theorem V2m_commutant_le : DMCOne.commutant (V2m m hm) (hb m) ≤ ℂ ∙ (V2m m hm).vacuum :=
  DMCOne.commutant_le_of_conformal_eq (V2m_conformal_eq_omegaH m hm)

end V2mCheck

/-! ## §6 The two named Dong–Mason facts and the reduction of `IDongMason` -/

universe u

/-- **DM-1, the analytic Dong–Mason step at `c = 1`.** In a nice VOA of central charge `1`, the
Heisenberg commutant of a unit Heisenberg vector `h ∈ W₁` (`h₍₁₎h = 𝟙`) is `ℂ𝟙`. Equivalently
(`DMCOne.commutant_le_iff`, proved): `ω = ½ h₍₋₁₎h`.

*Source.* C. Dong and G. Mason, *Rational vertex operator algebras and the effective central
charge*, IMRN 2004 (arXiv:math/0201318), proof of Theorem 3: for a Heisenberg subVOA `M(1)` of rank
`l` generated by a Cartan subalgebra of `W₁`, the commutant `C` is a VOA of effective central
charge `c̃ − l`, and `c̃ − l = 0` forces `C = ℂ𝟙`; pseudo-unitarity gives `c̃ = c = 1`. At `c = 1`,
`W₁` is reductive (DM Thm 1) of rank `≤ 1` (DM Thm 3), so `W₁ ∈ {ℂ, sl₂}`, and every `h` with
`h₍₁₎h ≠ 0` spans a Cartan subalgebra (a non-isotropic element of `sl₂` is semisimple).

*Non-vacuous / consistent.* `V2m_commutant_le` checks the conclusion on every `V_{2m}`; the
hypothesis is satisfied there (`V2m_nice`, `V2m_centralCharge`, `V2m_isHeisVector`). -/
def HeisCommutantTrivial : Prop :=
  ∀ (𝒲 : Type u) [AddCommGroup 𝒲] [Module ℂ 𝒲] (W : VertexOperatorAlgebra 𝒲), Nice W →
    W.centralCharge = 1 → ∀ h : 𝒲, DMCOne.IsHeisVector W h →
      DMCOne.commutant W h ≤ ℂ ∙ W.vacuum

/-- **DM-2, the algebraic reconstruction.** A strongly rational VOA whose conformal vector is the
Heisenberg one, `ω = ½ h₍₋₁₎h` for a unit Heisenberg vector `h`, is isomorphic to some `V_{2m}`.

*Source.* The lattice step of the proof of Dong–Mason (IMRN 2004) Theorem 3: with trivial
commutant, `W = ⊕_{λ ∈ L} M(1, λ)` with multiplicity one and `L` an even lattice; then `W ≅ V_L`
by the uniqueness of the lattice VOA attached to `L` (Frenkel–Lepowsky–Meurman 1988; V. Kac,
*Vertex algebras for beginners*; Lepowsky–Li 2004, Ch. 6). Here `L ⊂ ℝ` has rank one, so `L = √(2m) ℤ`; `L ≠ 0` because
the rank-one Heisenberg VOA `M(1)` itself is not `C₂`-cofinite.

*What is already proved toward it in this file* (`§4`): the vacuum space `Ω` of `h` satisfies
`L₀ = ½ h₍₀₎²` on `Ω` (`L0_on_vac_of_conformal_eq`), `h₍₀₎` is semisimple on `Ω`
(`vac_split`), every charge `λ` satisfies `λ² = 2n` with the vacuum vector in `Wₙ`
(`vac_charge_sq`), and the commutant is `ℂ𝟙` (`commutant_le_of_conformal_eq`). What remains is
multiplicity one, closure of the charges under addition, and the construction of the VOA
isomorphism.

*Non-vacuous.* `V2m_conformal_eq_omegaH`: every `V_{2m}` satisfies the hypothesis. -/
def HeisLatticeReconstruction : Prop :=
  ∀ (𝒲 : Type u) [AddCommGroup 𝒲] [Module ℂ 𝒲] (W : VertexOperatorAlgebra 𝒲),
    StronglyRational W → ∀ h : 𝒲, DMCOne.IsHeisVector W h →
      W.conformalVector = DMCOne.omegaH W h → ∃ (m : ℕ) (hm : 1 ≤ m), VOAIsomorphic W (V2m m hm)

/-- **`IDongMason` from the two named Dong–Mason facts.** The Heisenberg vector
(`DMCOne.exists_heisVector`) and the identity `ω = ω_h` (`DMCOne.conformal_eq_omegaH_of_commutant`)
are proved here; DM-1 supplies the trivial commutant, DM-2 the lattice reconstruction. -/
theorem iDongMason_of_facts (hC : HeisCommutantTrivial.{u}) (hR : HeisLatticeReconstruction.{u}) :
    IDongMason.{u} := by
  intro 𝒲 _ _ W hW hc h1
  obtain ⟨h, hmem, hone⟩ := DMCOne.exists_heisVector hW.1 h1
  have hh : DMCOne.IsHeisVector W h := ⟨hmem, hone⟩
  exact hR 𝒲 W hW.1 h hh
    (DMCOne.conformal_eq_omegaH_of_commutant hW.1 hh (hC 𝒲 W hW hc h hh))

end VOA.Classification.COne
