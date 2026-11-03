/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.SuperReconstruction
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Symplectic fermions — the `c = -2` logarithmic free field

Two **odd weight-one** fields `χ⁺, χ⁻` with

`{χᵃ_m, χᵇ_n} = m · δ_{m+n,0} · ωᵃᵇ`,  `ω` the symplectic form,

the free-field theory whose even part is the triplet `W(2)` — the canonical logarithmic CFT at
`c = -2`.  This is the first genuinely *symplectic* fermion pair in the library, and the intended
first `SuperVertexAlgebra` instance.

## Why this is not just `FreeFermion` twice

Two structural differences, both visible in the relation above.

* The pairing carries a factor of `m`, so the `ε`-twisted commutator is a **`δ`-derivative**, not
  a bare `δ`.  Locality order is therefore `2`, not `1`, and `localε_of_car` — which handles only
  the `δ_{m+n+1,0}·S` shape — does not apply.  We go through `deltaDeriv 1` directly.
* The pairing is **antisymmetric in the species index** and antisymmetric in the mode (through
  `m` at `m + n = 0`), so the product is symmetric, as an anticommutator must be.  Getting either
  sign alone wrong would break `chi_anticomm`, so this is a real check.

## Indexing

`FormalDist` is indexed by the **`z`-exponent** throughout this library (`a(z) = ∑ⱼ aⱼ zʲ`, with
`mode a m = a (-m-1)`), which is what `mulBySub` acts on.  So `chi a j = χᵃ_{-j-1}`: creation for
`j ≥ 0`, annihilation for `j ≤ -1`.  With that convention lower truncation holds, which is what
`reconstructε` will need.

## The zero modes

`χᵃ_0` has coefficient `m = 0`, so it acts as **zero** on the vacuum module — consistent, since
`{χᵃ_0, χᵇ_n} = 0` for all `n` and `χᵃ_0` kills the vacuum.  The famous `c = -2` zero-mode
Grassmann algebra lives on other modules, not on this one.
-/

namespace VOA.SympFerm

open CliffordAlgebra

/-- Mode space: one generator per (level, species) pair. -/
noncomputable abbrev SFModes : Type := (ℕ × Fin 2) →₀ ℂ

/-- Zero quadratic form — the Clifford algebra is the exterior algebra. -/
noncomputable abbrev QSF : QuadraticForm ℂ SFModes := 0

/-- **The symplectic-fermion Fock space** `Λ((ℕ × Fin 2) →₀ ℂ)`. -/
noncomputable abbrev FockSF := CliffordAlgebra QSF

/-- The sign `σₐ` with `σ₀ = 1`, `σ₁ = -1`. -/
def sfSign (a : Fin 2) : ℂ := if a = 0 then 1 else -1

/-- The symplectic form `ωᵃᵇ`: nonzero only on the opposite species, with `ω⁰¹ = 1 = -ω¹⁰`. -/
def sfOmega (a b : Fin 2) : ℂ := if b = a + 1 then sfSign a else 0

@[simp] theorem sfOmega_same (a : Fin 2) : sfOmega a a = 0 := by
  fin_cases a <;>
    simp [sfOmega, sfSign, show ((0 : Fin 2) + 1 = 1) from rfl]

theorem sfOmega_antisymm (a b : Fin 2) : sfOmega b a = -sfOmega a b := by
  fin_cases a <;> fin_cases b <;>
    norm_num [sfOmega, sfSign, show ((1 : Fin 2) + 1 = 0) from rfl,
      show ((0 : Fin 2) + 1 = 1) from rfl]

/-! ## The base Clifford operators

Separating the scalar weights from the Clifford operators keeps the three CAR proofs identical
to the free-fermion ones; the symplectic weights are reattached afterwards by linearity. -/

/-- Contraction against the coordinate functional at `p`. -/
noncomputable def annBase (p : ℕ × Fin 2) : Module.End ℂ FockSF :=
  contractLeft (Finsupp.lapply p)

/-- Exterior multiplication by the generator at `p`. -/
noncomputable def creBase (p : ℕ × Fin 2) : Module.End ℂ FockSF :=
  LinearMap.mulLeft ℂ (ι QSF (Finsupp.single p (1 : ℂ)))

theorem creBase_anticomm (p q : ℕ × Fin 2) (x : FockSF) :
    creBase p (creBase q x) + creBase q (creBase p x) = 0 := by
  change ι QSF _ * (ι QSF _ * x) + ι QSF _ * (ι QSF _ * x) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ι_mul_ι_add_swap]
  simp [QuadraticMap.polar]

theorem annBase_anticomm (p q : ℕ × Fin 2) (x : FockSF) :
    annBase p (annBase q x) + annBase q (annBase p x) = 0 := by
  simp only [annBase]
  rw [contractLeft_comm]
  exact neg_add_cancel _

theorem annBase_creBase_anticomm (p q : ℕ × Fin 2) (x : FockSF) :
    annBase p (creBase q x) + creBase q (annBase p x)
      = (if p = q then (1 : ℂ) else 0) • x := by
  simp only [annBase, creBase, LinearMap.mulLeft_apply]
  rw [contractLeft_ι_mul]
  rw [show (Finsupp.lapply p : SFModes →ₗ[ℂ] ℂ) (Finsupp.single q (1 : ℂ))
      = (if p = q then (1 : ℂ) else 0) by
    simp [Finsupp.lapply_apply, Finsupp.single_apply, eq_comm]]
  abel

/-- The creation operator `χᵃ_{-k-1}`. -/
noncomputable def creSF (a : Fin 2) (k : ℕ) : Module.End ℂ FockSF := creBase (k, a)

/-- The annihilation operator `χᵃ_m` for `m ≥ 0`: contraction against the symplectic partner,
weighted by `m · σₐ`.  At `m = 0` the weight vanishes, so `χᵃ_0 = 0` here. -/
noncomputable def annSF (a : Fin 2) (m : ℕ) : Module.End ℂ FockSF :=
  ((m : ℂ) * sfSign a) • annBase (m - 1, a + 1)

@[simp] theorem annSF_zero (a : Fin 2) : annSF a 0 = 0 := by
  rw [annSF]; norm_num

/-! ## The three canonical anticommutation relations -/

theorem creSF_anticomm (a b : Fin 2) (j k : ℕ) (x : FockSF) :
    creSF a j (creSF b k x) + creSF b k (creSF a j x) = 0 :=
  creBase_anticomm _ _ x

theorem annSF_anticomm (a b : Fin 2) (m n : ℕ) (x : FockSF) :
    annSF a m (annSF b n x) + annSF b n (annSF a m x) = 0 := by
  change ((m : ℂ) * sfSign a) • annBase _ (((n : ℂ) * sfSign b) • annBase _ x)
      + ((n : ℂ) * sfSign b) • annBase _ (((m : ℂ) * sfSign a) • annBase _ x) = 0
  rw [map_smul, map_smul, smul_smul, smul_smul,
    mul_comm ((n : ℂ) * sfSign b) ((m : ℂ) * sfSign a), ← smul_add, annBase_anticomm, smul_zero]

/-- **The mixed relation** `{χᵃ_m, χᵇ_{-k-1}} = m · σₐ · δ_{(m-1,a+1),(k,b)}`, which is
`m · δ_{k,m-1} · ωᵃᵇ`. -/
theorem annSF_creSF_anticomm (a b : Fin 2) (m k : ℕ) (x : FockSF) :
    annSF a m (creSF b k x) + creSF b k (annSF a m x)
      = (((m : ℂ) * sfSign a)
          * (if ((m - 1, a + 1) : ℕ × Fin 2) = (k, b) then (1 : ℂ) else 0)) • x := by
  change ((m : ℂ) * sfSign a) • annBase _ (creBase _ x)
      + creBase _ (((m : ℂ) * sfSign a) • annBase _ x) = _
  rw [map_smul, ← smul_add, annBase_creBase_anticomm, smul_smul]

/-- **The mixed relation in `ω` form**: `{χᵃ_m, χᵇ_{-k-1}} = m · δ_{m,k+1} · ωᵃᵇ`. -/
theorem annSF_creSF_omega (a b : Fin 2) (m k : ℕ) (x : FockSF) :
    annSF a m (creSF b k x) + creSF b k (annSF a m x)
      = (if m = k + 1 then (m : ℂ) * sfOmega a b else 0) • x := by
  rw [annSF_creSF_anticomm]
  congr 1
  by_cases hm0 : m = 0
  · subst hm0
    rw [if_neg (show ¬((0 : ℕ) = k + 1) by omega)]
    norm_num
  · have hiff : (((m - 1, a + 1) : ℕ × Fin 2) = (k, b)) ↔ (m = k + 1 ∧ b = a + 1) := by
      rw [Prod.ext_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2.symm⟩
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2.symm⟩
    by_cases hm : m = k + 1
    · by_cases hab : b = a + 1
      · rw [if_pos (hiff.mpr ⟨hm, hab⟩), if_pos hm, sfOmega, if_pos hab]; ring
      · rw [if_neg (fun hc => hab (hiff.mp hc).2), if_pos hm, sfOmega, if_neg hab]; ring
    · rw [if_neg (fun hc => hm (hiff.mp hc).1), if_neg hm]; ring

/-! ## The fields

`chi a j = χᵃ_{-j-1}`: the `z`-exponent indexing, so creation sits at `j ≥ 0` and annihilation at
`j ≤ -1`, and lower truncation (`IsField`) is the true statement. -/

/-- **The symplectic fermion field** `χᵃ(z) = ∑ₙ χᵃ₍ₙ₎ z^{-n-1}`, as a formal distribution
indexed by the `z`-exponent. -/
noncomputable def chi (a : Fin 2) : FormalDist (Module.End ℂ FockSF) :=
  fun j => if 0 ≤ j then creSF a j.toNat else annSF a (-j - 1).toNat

/-- Opposite species have opposite sign: `σ_{a+1} = -σₐ`. -/
theorem sfSign_succ (a : Fin 2) : sfSign (a + 1) = -sfSign a := by
  fin_cases a <;> norm_num [sfSign, show ((0 : Fin 2) + 1 = 1) from rfl,
    show ((1 : Fin 2) + 1 = 0) from rfl]

/-- **The canonical anticommutation relations for `χ`**, in `z`-exponent indexing:
`{χᵃ(j), χᵇ(k)} = (-j-1)·δ_{j+k+2,0}·ωᵃᵇ`.  The factor `(-j-1)` is the mode, so this is a
`δ`-**derivative** — the source of the order-2 locality. -/
theorem chi_anticomm (a b : Fin 2) (j k : ℤ) :
    chi a j * chi b k + chi b k * chi a j
      = (if j + k + 2 = 0 then (((-j - 1 : ℤ) : ℂ) * sfOmega a b) else 0)
        • (1 : Module.End ℂ FockSF) := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, chi, LinearMap.smul_apply,
    Module.End.one_apply]
  by_cases hj : 0 ≤ j <;> by_cases hk : 0 ≤ k <;> simp only [hj, hk, if_true, if_false]
  · -- both creation: `j + k + 2 ≥ 2`
    rw [if_neg (by omega), zero_smul]
    simpa using creSF_anticomm a b j.toNat k.toNat x
  · -- `j` creation, `k` annihilation
    rw [add_comm, annSF_creSF_omega]
    by_cases h : j + k + 2 = 0
    · rw [if_pos h, if_pos (show (-k - 1).toNat = j.toNat + 1 by omega)]
      congr 1
      rw [sfOmega_antisymm a b]
      have hcast : (((-k - 1).toNat : ℕ) : ℂ) = -((-j - 1 : ℤ) : ℂ) := by
        have h1 : ((-k - 1).toNat : ℤ) = j + 1 := by omega
        have h2 : (((-k - 1).toNat : ℕ) : ℂ) = (((-k - 1).toNat : ℤ) : ℂ) := by push_cast; ring
        rw [h2, h1]; push_cast; ring
      rw [hcast]; ring
    · rw [if_neg h, if_neg (show ¬ ((-k - 1).toNat = j.toNat + 1) by omega), zero_smul]
  · -- `j` annihilation, `k` creation
    rw [annSF_creSF_omega]
    by_cases h : j + k + 2 = 0
    · rw [if_pos h, if_pos (show (-j - 1).toNat = k.toNat + 1 by omega)]
      congr 1
      have hcast : (((-j - 1).toNat : ℕ) : ℂ) = ((-j - 1 : ℤ) : ℂ) := by
        have h2 : (((-j - 1).toNat : ℕ) : ℂ) = (((-j - 1).toNat : ℤ) : ℂ) := by push_cast; ring
        rw [h2, show ((-j - 1).toNat : ℤ) = -j - 1 by omega]
      rw [hcast]
    · rw [if_neg h, if_neg (show ¬ ((-j - 1).toNat = k.toNat + 1) by omega), zero_smul]
  · -- both annihilation
    have hz : (if j + k + 2 = 0 then (((-j - 1 : ℤ) : ℂ) * sfOmega a b) else 0) = 0 := by
      by_cases h : j + k + 2 = 0
      · rw [if_pos h, show ((-j - 1 : ℤ) : ℂ) = 0 by
          rw [show j = -1 by omega]; norm_num, zero_mul]
      · rw [if_neg h]
    rw [hz, zero_smul]
    simpa using annSF_anticomm a b (-j - 1).toNat (-k - 1).toNat x

/-! ## Super-locality

The anticommutator is a `δ`-**derivative**, so the locality order is `2`.  `localε_of_car`, which
handles only the bare-`δ` shape `δ_{m+n+1,0}·S`, does not apply here — this is the first field
pair in the library needing `deltaDeriv` at positive order. -/

/-- **The symplectic fermions are `ε`-local at `ε = -1`, with order 2.**

`koszul 1 1 = -1` is the Koszul sign of two odd fields, so this is super-VA4 for a purely odd
generating pair.  Unlike the free fermion, the order is `2` — the `1/(z-w)²` OPE. -/
theorem chi_localε (a b : Fin 2) : Localε (-1) (chi a) (chi b) := by
  refine ⟨2, ?_⟩
  have h : bracketDistε (-1) (chi a) (chi b)
      = deltaDeriv 1 (fun t => if t = 0 then (sfOmega a b) • (1 : Module.End ℂ FockSF) else 0) := by
    apply FormalDist₂.ext; intro m n
    change chi a m * chi b n - (-1 : ℂ) • (chi b n * chi a m)
      = (∏ i ∈ Finset.range 1, (-m - 1 - (i : ℤ)))
        • (if m + n + 1 + 1 = 0 then (sfOmega a b) • (1 : Module.End ℂ FockSF) else 0)
    rw [neg_smul, one_smul, sub_neg_eq_add, chi_anticomm]
    rw [Finset.prod_range_one]
    by_cases hmn : m + n + 2 = 0
    · rw [if_pos hmn, if_pos (by omega : m + n + 1 + 1 = 0), Nat.cast_zero, sub_zero,
        ← Int.cast_smul_eq_zsmul ℂ (-m - 1), smul_smul]
    · rw [if_neg hmn, if_neg (by omega : ¬ (m + n + 1 + 1 = 0)), smul_zero, zero_smul]
  rw [h]
  exact mulBySubPow_succ_deltaDeriv 1 _

/-- Restated with the Koszul sign in place of the literal `-1`, matching super-VA4. -/
theorem chi_localε_koszul (a b : Fin 2) : Localε (koszul 1 1) (chi a) (chi b) := by
  rw [koszul_one_one]; exact chi_localε a b

/-! ## Lower truncation

`reconstructε` needs `IsField`, i.e. that `chi a j` kills any fixed vector for `j ≪ 0`.  Since
`chi a j` is a contraction at index `-j-2` there, this is the statement that a *fixed* element of
the exterior algebra involves only finitely many generators.

Proving it needs a Leibniz rule for `contractLeft` on general products.  Mathlib has only the
`ι a * b` case (`contractLeft_ι_mul`), so the graded derivation property is proved here. -/

/-- **Contraction is an odd derivation**: `d⌋(a·b) = (d⌋a)·b + (involute a)·(d⌋b)`.
Mathlib provides only the `a = ι v` case; this is the general one, by Clifford induction.
The `involute` is forced — contraction is odd, so it picks up a sign past each generator. -/
theorem contractLeft_mul' (d : SFModes →ₗ[ℂ] ℂ) (a : FockSF) : ∀ b : FockSF,
    contractLeft d (a * b) = contractLeft d a * b + involute a * contractLeft d b := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r =>
      intro b
      rw [contractLeft_algebraMap_mul, contractLeft_algebraMap, zero_mul, zero_add,
        AlgHom.commutes]
  | ι v =>
      intro b
      rw [contractLeft_ι_mul, contractLeft_ι, involute_ι, neg_mul, ← Algebra.smul_def,
        ← sub_eq_add_neg]
  | mul x y hx hy =>
      intro b
      rw [mul_assoc, hx (y * b), hy b, hx y, map_mul]
      noncomm_ring
  | add x y hx hy =>
      intro b
      rw [add_mul, map_add, hx b, hy b]
      simp only [map_add, add_mul]
      abel

/-- **A fixed vector involves only finitely many generators**: contraction at a high enough
index annihilates it. -/
theorem contractLeft_high_eq_zero (x : FockSF) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ c : Fin 2,
      contractLeft (Finsupp.lapply ((k, c) : ℕ × Fin 2)) x = 0 := by
  classical
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact ⟨0, fun k _ c => by rw [contractLeft_algebraMap]⟩
  | ι v =>
      refine ⟨(v.support.image Prod.fst).sup id + 1, fun k hk c => ?_⟩
      rw [contractLeft_ι]
      have hv : v ((k, c) : ℕ × Fin 2) = 0 := by
        by_contra hne
        have h1 : ((k, c) : ℕ × Fin 2) ∈ v.support := Finsupp.mem_support_iff.mpr hne
        have h2 : k ∈ v.support.image Prod.fst := Finset.mem_image.mpr ⟨(k, c), h1, rfl⟩
        have h3 := Finset.le_sup (f := (id : ℕ → ℕ)) h2
        simp only [id] at h3
        omega
      rw [show (Finsupp.lapply ((k, c) : ℕ × Fin 2) : SFModes →ₗ[ℂ] ℂ) v
            = v ((k, c) : ℕ × Fin 2) from rfl, hv, map_zero]
  | mul x y hx hy =>
      obtain ⟨Nx, hX⟩ := hx
      obtain ⟨Ny, hY⟩ := hy
      exact ⟨max Nx Ny, fun k hk c => by
        rw [contractLeft_mul', hX k (le_trans (le_max_left _ _) hk) c, zero_mul,
          hY k (le_trans (le_max_right _ _) hk) c, mul_zero, add_zero]⟩
  | add x y hx hy =>
      obtain ⟨Nx, hX⟩ := hx
      obtain ⟨Ny, hY⟩ := hy
      exact ⟨max Nx Ny, fun k hk c => by
        rw [map_add, hX k (le_trans (le_max_left _ _) hk) c,
          hY k (le_trans (le_max_right _ _) hk) c, add_zero]⟩

/-- **The symplectic fermion fields are fields** (lower truncation, VA5). -/
theorem chi_isField (a : Fin 2) : IsField (chi a) := by
  intro x
  obtain ⟨N, hN⟩ := contractLeft_high_eq_zero x
  refine ⟨-(N : ℤ) - 2, fun j hj => ?_⟩
  change chi a j x = 0
  rw [chi, if_neg (by omega : ¬ (0 ≤ j)), annSF, LinearMap.smul_apply]
  change ((((-j - 1).toNat : ℂ) * sfSign a) • annBase ((-j - 1).toNat - 1, a + 1) x) = 0
  rw [annBase, hN ((-j - 1).toNat - 1) (by omega) (a + 1), smul_zero]

/-! ## Creation from the vacuum

The vacuum is `1 : FockSF`.  These are `reconstructε`'s `hcre0` and `hcreneg` for the two
generators. -/

/-- The vacuum vector. -/
noncomputable abbrev vacSF : FockSF := 1

/-- **VA3 base**: `χᵃ(z)|0⟩` has constant term the generating state `χᵃ_{-1}|0⟩`. -/
@[simp] theorem chi_zero_vac (a : Fin 2) :
    chi a 0 vacSF = ι QSF (Finsupp.single ((0, a) : ℕ × Fin 2) (1 : ℂ)) := by
  rw [chi, if_pos le_rfl]
  change creBase (Int.toNat 0, a) vacSF = _
  rw [creBase]
  change ι QSF (Finsupp.single ((Int.toNat 0, a) : ℕ × Fin 2) (1 : ℂ)) * (1 : FockSF) = _
  rw [mul_one]
  norm_num

/-- **VA3 regularity**: `χᵃ(z)|0⟩` has no negative powers — the annihilation half kills the
vacuum, since contraction annihilates `1`. -/
@[simp] theorem chi_neg_vac (a : Fin 2) (q : ℤ) (hq : q < 0) : chi a q vacSF = 0 := by
  rw [chi, if_neg (by omega), annSF, LinearMap.smul_apply]
  change (((-q - 1).toNat : ℂ) * sfSign a) • annBase ((-q - 1).toNat - 1, a + 1) vacSF = 0
  rw [annBase]
  change (((-q - 1).toNat : ℂ) * sfSign a)
      • contractLeft (Finsupp.lapply (((-q - 1).toNat - 1, a + 1) : ℕ × Fin 2)) (1 : FockSF) = 0
  rw [contractLeft_one, smul_zero]

end VOA.SympFerm
