/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenVirasoro
import VOA.Examples.LatticeGenVOAInstance

/-!
# Background charge (Feigin–Fuchs / linear dilaton) on the general even-lattice VOA

The lattice analogue of `Examples.VirasoroFock`'s `Lld`/`Lld_virasoro`.  On the free-boson Fock
space the background-charge deformation `Lₙ ↦ Lₙ − (n+1)λ(n)` is easy because the zero mode
`λ(0)` acts as `0`.  On a **lattice** VOA `V_L = FockN(rank L) ⊗ ℂ{L}` the zero mode is *not* zero:
on the charge-`γ` sector `a₀` acts by `γ`, so `λ(0) = ⟨λ,γ⟩ ≠ 0`.  That single fact is what this
file handles.

## Sign convention  (pinned, do not flip)

`LBg λ n := Lₙ − (n+1)·λ(n)`, corresponding to the conformal vector `ω_L + λ(−2)|0⟩`.  It is fixed
by `LBg_weight_latChargeGen`: the charged vacuum `e^β` gets conformal weight

  `wt(e^β) = ½⟨β,β⟩ − ⟨λ,β⟩`.

For the triplet data (`⟨α,α⟩ = 2p`, `λ = ((p−1)/(2p))·α`) this gives `wt(e^{α}) = p − (p−1) = 1`
and `wt(e^{−α}) = p + (p−1) = 2p−1`, the required normalization
(`LBg_weight_charge_self` / `LBg_weight_charge_neg`).

## Main results

* `bg_virasoro_core` — the abstract algebraic core: given a Virasoro family `P` of central charge
  `c₀` and a weight-one current `β` (`[Pₘ,βₙ] = −n β_{m+n}`) with level `κ`
  (`[βₘ,βₙ] = δ_{m+n,0}·κ·m`), the deformed family `Pₙ − (n+1)βₙ` is Virasoro of central charge
  `c₀ − 12κ`.  This is `Lld_virasoro` with the level and the boson central charge made abstract.
* `bgCur` — the **full** background-charge current on `V_L`: `λ(n) = ∑ₐ λₐ·mode(α^a(z)) n`,
  *including the momentum zero mode* `zGradeOpGen`.  The key lemma is
  `OpSec_comm_BetaSec`: the zero mode is exactly what makes `[Lₘ, λ(n)] = −n λ(m+n)` hold on the
  nose (without it the identity fails by the `δ_{m+n,0}⟨γ,λ⟩` central residue of `[γ(m), λ(n)]`).
* `LBg_virasoro` — **the target**: `[LBgₘ, LBgₙ] = (m−n)LBg_{m+n} + δ_{m+n,0}(m³−m)/12·c` with
  `c = rank L − 12⟨λ,λ⟩`.
* `LBg_weight_latChargeGen` — the deformed weight formula, which pins the sign.
* `omegaBg` / `mode_YfullGen_omegaBg` — the **conformal vector** itself: `ω_λ = ω_L + λ(−2)|0⟩`
  is a genuine state of `V_L`, and the modes of its reconstructed vertex operator
  `Y(ω_λ, z)` are exactly `LBg`:  `mode (Y(ω_λ,z)) (n+1) = Lₙ^λ`.

The background charge `λ` is given by its **orthonormal-frame coordinate vector**
`lam : Fin (rank L) → ℂ`, not by a lattice element: in every application `λ ∉ L` (it lies in
`L ⊗ ℚ`).  `latBg c α` is the special case `λ = c·α`.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen.BgA

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN

/-! ## §0  The abstract background-charge Virasoro core. -/

section Core

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- **The background-charge deformation of an abstract Virasoro family.**

Given `P : ℤ → End ℂ W` satisfying the Virasoro relation with central charge `c₀`, and a
*weight-one current* `β : ℤ → End ℂ W` — i.e. `[Pₛ, βₜ] = −t·β_{s+t}` on the nose, with the level
`[βₛ, βₜ] = δ_{s+t,0}·κ·s` — the deformed family `Pₙ − (n+1)·βₙ` is again Virasoro, with central
charge `c₀ − 12κ`.

This is `VOA.Lld_virasoro` with the free-boson data (`c₀ = 1`, `κ = 1`) abstracted away;
on a lattice VOA `β` must be the current *including its momentum zero mode*, which is the only
way `hPb` can hold with no `δ_{s+t,0}` residue. -/
theorem bg_virasoro_core (P β : ℤ → End ℂ W) (c₀ κ : ℂ)
    (hPP : ∀ s t : ℤ, P s * P t - P t * P s
      = ((s : ℂ) - t) • P (s + t)
        + (if s + t = 0 then ((s : ℂ) ^ 3 - s) / 12 * c₀ else 0) • (1 : End ℂ W))
    (hPb : ∀ s t : ℤ, P s * β t - β t * P s = (-(t : ℂ)) • β (s + t))
    (hbb : ∀ s t : ℤ, β s * β t - β t * β s
      = (if s + t = 0 then κ * (s : ℂ) else 0) • (1 : End ℂ W))
    (m n : ℤ) :
    (P m - ((m : ℂ) + 1) • β m) * (P n - ((n : ℂ) + 1) • β n)
      - (P n - ((n : ℂ) + 1) • β n) * (P m - ((m : ℂ) + 1) • β m)
      = ((m : ℂ) - n) • (P (m + n) - (((m + n : ℤ) : ℂ) + 1) • β (m + n))
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * (c₀ - 12 * κ) else 0) • (1 : End ℂ W) := by
  classical
  have hbP : β m * P n - P n * β m = ((m : ℂ)) • β (m + n) := by
    have h := hPb n m
    rw [add_comm n m] at h
    rw [← neg_sub, h]
    module
  have hexpand : (P m - ((m : ℂ) + 1) • β m) * (P n - ((n : ℂ) + 1) • β n)
      - (P n - ((n : ℂ) + 1) • β n) * (P m - ((m : ℂ) + 1) • β m)
      = (P m * P n - P n * P m)
        - ((n : ℂ) + 1) • (P m * β n - β n * P m)
        - ((m : ℂ) + 1) • (β m * P n - P n * β m)
        + (((m : ℂ) + 1) * ((n : ℂ) + 1)) • (β m * β n - β n * β m) := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
    module
  rw [hexpand, hPP m n, hPb m n, hbP, hbb m n]
  by_cases hmn : m + n = 0
  · have hn : (n : ℂ) = -(m : ℂ) := by
      have h : n = -m := by omega
      rw [h]; push_cast; ring
    have hz : ((m + n : ℤ) : ℂ) = 0 := by rw [hmn]; norm_num
    simp only [if_pos hmn]
    rw [hz, hn]
    module
  · simp only [if_neg hmn]
    push_cast
    module

end Core

variable (L : IntegralLattice)

/-! ## §1  The background-charge oscillator on the boson factor. -/

/-- The **background-charge oscillator** `λ(m) = ∑ₐ λₐ·aᵃ(m)` on `FockN (rank L)`, for an arbitrary
complex frame-coordinate vector `lam`.  (`chargeOsc L α` is the special case `lam = chargeCoord α`,
the only one that lies in the lattice.) -/
noncomputable def bgOsc (lam : Fin (rank L) → ℂ) (m : ℤ) : End ℂ (FockN (rank L)) :=
  ∑ a : Fin (rank L), lam a • HeisenbergN.oscN (rank L) 1 a m

/-- The euclidean pairing of two frame-coordinate vectors, `⟨λ,μ⟩ = ∑ₐ λₐ μₐ`. -/
noncomputable def bgForm (lam mu : Fin (rank L) → ℂ) : ℂ := ∑ a : Fin (rank L), lam a * mu a

theorem bgForm_comm (lam mu : Fin (rank L) → ℂ) : bgForm L lam mu = bgForm L mu lam :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The charge oscillator is the background oscillator at the charge's frame coordinates. -/
theorem chargeOsc_eq_bgOsc (α : L.carrier) (m : ℤ) :
    chargeOsc L α m = bgOsc L (chargeCoord L α) m := rfl

/-- On a lattice pair the euclidean frame pairing is the lattice form. -/
theorem bgForm_chargeCoord (hPos : L.PosDef) (α β : L.carrier) :
    bgForm L (chargeCoord L α) (chargeCoord L β) = ((L.form α β : ℤ) : ℂ) :=
  sum_chargeCoord L hPos α β

theorem bgOsc_zero (lam : Fin (rank L) → ℂ) : bgOsc L lam 0 = 0 :=
  Finset.sum_eq_zero fun _ _ => by rw [HeisenbergN.oscN_zero, smul_zero]

theorem bgOsc_apply (lam : Fin (rank L) → ℂ) (m : ℤ) (y : FockN (rank L)) :
    bgOsc L lam m y = ∑ a : Fin (rank L), lam a • HeisenbergN.oscN (rank L) 1 a m y := by
  rw [bgOsc, LinearMap.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => rfl

/-- **The Heisenberg bracket of two background oscillators**:
`[λ(m), μ(n)] = ⟨λ,μ⟩·m·δ_{m+n,0}`.  Same proof as `chargeOsc_comm`, with the metric identity
replaced by the definition of `bgForm` (no positive-definiteness needed). -/
theorem bgOsc_comm (lam mu : Fin (rank L) → ℂ) (m n : ℤ) :
    bgOsc L lam m * bgOsc L mu n - bgOsc L mu n * bgOsc L lam m
      = (if m + n = 0 then bgForm L lam mu * (m : ℂ) else 0) • (1 : End ℂ (FockN (rank L))) := by
  classical
  rw [Module.End.one_eq_id]
  have e1 : bgOsc L lam m * bgOsc L mu n
      = ∑ a : Fin (rank L), ∑ b : Fin (rank L),
          (lam a * mu b) •
            (HeisenbergN.oscN (rank L) 1 a m * HeisenbergN.oscN (rank L) 1 b n) := by
    simp only [bgOsc]
    rw [Fintype.sum_mul_sum]
    simp only [smul_mul_smul_comm]
  have e2 : bgOsc L mu n * bgOsc L lam m
      = ∑ a : Fin (rank L), ∑ b : Fin (rank L),
          (lam a * mu b) •
            (HeisenbergN.oscN (rank L) 1 b n * HeisenbergN.oscN (rank L) 1 a m) := by
    simp only [bgOsc]
    rw [Fintype.sum_mul_sum]
    simp only [smul_mul_smul_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [mul_comm (mu b) (lam a)]
  have hexpand : bgOsc L lam m * bgOsc L mu n - bgOsc L mu n * bgOsc L lam m
      = ∑ a : Fin (rank L), ∑ b : Fin (rank L),
          (lam a * mu b) •
            (HeisenbergN.oscN (rank L) 1 a m * HeisenbergN.oscN (rank L) 1 b n
              - HeisenbergN.oscN (rank L) 1 b n * HeisenbergN.oscN (rank L) 1 a m) := by
    rw [e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [smul_sub]
  have hbr : ∀ a b : Fin (rank L),
      HeisenbergN.oscN (rank L) 1 a m * HeisenbergN.oscN (rank L) 1 b n
          - HeisenbergN.oscN (rank L) 1 b n * HeisenbergN.oscN (rank L) 1 a m
        = (if a = b ∧ m + n = 0 then (m : ℂ) else 0) • LinearMap.id := by
    intro a b
    rw [HeisenbergN.oscN_comm (rank L) 1 a b m n, mul_one]
  rw [hexpand]
  simp only [hbr, smul_smul]
  by_cases hP : m + n = 0
  · rw [if_pos hP]
    simp only [← Finset.sum_smul]
    congr 1
    have hb : ∀ a : Fin (rank L),
        (∑ b : Fin (rank L), (lam a * mu b) * (if a = b ∧ m + n = 0 then (m : ℂ) else 0))
          = (lam a * mu a) * (m : ℂ) := by
      intro a
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb])
          (fun h => absurd (Finset.mem_univ a) h)]
      simp [hP]
    simp only [hb]
    rw [← Finset.sum_mul]
    rfl
  · rw [if_neg hP, zero_smul]
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
    simp [hP]

/-- **`[Lₘ, λ(n)] = −n·λ(m+n)`** on the boson factor (vector form). -/
theorem LvirN_bgOsc (lam : Fin (rank L) → ℂ) (m n : ℤ) (y : FockN (rank L)) :
    HeisenbergN.LvirN (rank L) 1 m (bgOsc L lam n y)
      = (-(n : ℂ)) • bgOsc L lam (m + n) y
        + bgOsc L lam n (HeisenbergN.LvirN (rank L) 1 m y) := by
  rw [bgOsc_apply, map_sum,
    Finset.sum_congr rfl (fun a _ => by
      rw [map_smul, HeisenbergN.LvirN_oscN (rank L) 1 one_ne_zero a m n y, smul_add,
        smul_comm (lam a) (-(n : ℂ))]),
    Finset.sum_add_distrib, ← Finset.smul_sum, ← bgOsc_apply, ← bgOsc_apply]

/-- **`[Lₘ, λ(n)] = −n·λ(m+n)`** on the boson factor (operator form). -/
theorem LvirN_comm_bgOsc (lam : Fin (rank L) → ℂ) (m n : ℤ) :
    HeisenbergN.LvirN (rank L) 1 m * bgOsc L lam n
        - bgOsc L lam n * HeisenbergN.LvirN (rank L) 1 m
      = (-(n : ℂ)) • bgOsc L lam (m + n) := by
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LvirN_bgOsc,
    LinearMap.smul_apply]
  abel

/-! ## §2  The charge-sector operators: the Virasoro family and the full current. -/

/-- The pairing `⟨λ,γ⟩` of the background charge with a lattice charge — the value of the
**momentum zero mode** `λ(0)` on the charge-`γ` sector. -/
noncomputable def bgPair (lam : Fin (rank L) → ℂ) (γ : L.carrier) : ℂ :=
  bgForm L lam (chargeCoord L γ)

/-- The charge-`γ` conformal-weight shift `δ_{s,0}·½⟨γ,γ⟩` of the lattice Sugawara modes. -/
noncomputable def scWt (γ : L.carrier) (s : ℤ) : ℂ :=
  if s = 0 then (1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ) else 0

/-- The momentum zero mode `δ_{s,0}·⟨λ,γ⟩` of the background current on the charge-`γ` sector. -/
noncomputable def scMom (lam : Fin (rank L) → ℂ) (γ : L.carrier) (s : ℤ) : ℂ :=
  if s = 0 then bgPair L lam γ else 0

/-- The lattice Virasoro mode `Lₛ` restricted to the charge-`γ` sector, as an operator on the
boson factor: `Lₛ + γ(s) + δ_{s,0}·½⟨γ,γ⟩` (cf. `LLGen_tmul`). -/
noncomputable def OpSec (γ : L.carrier) (s : ℤ) : End ℂ (FockN (rank L)) :=
  HeisenbergN.LvirN (rank L) 1 s + chargeOsc L γ s + scWt L γ s • (1 : End ℂ (FockN (rank L)))

/-- The **full** background current `λ(s)` restricted to the charge-`γ` sector:
the oscillator plus the momentum zero mode `δ_{s,0}⟨λ,γ⟩`. -/
noncomputable def BetaSec (lam : Fin (rank L) → ℂ) (γ : L.carrier) (s : ℤ) :
    End ℂ (FockN (rank L)) :=
  bgOsc L lam s + scMom L lam γ s • (1 : End ℂ (FockN (rank L)))

theorem OpSec_apply (γ : L.carrier) (s : ℤ) (y : FockN (rank L)) :
    OpSec L γ s y = HeisenbergN.LvirN (rank L) 1 s y + chargeOsc L γ s y
      + (if s = 0 then ((1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ)) • y else 0) := by
  rw [OpSec, LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, scWt]
  by_cases h : s = 0 <;> simp [h]

theorem BetaSec_apply (lam : Fin (rank L) → ℂ) (γ : L.carrier) (s : ℤ) (y : FockN (rank L)) :
    BetaSec L lam γ s y = bgOsc L lam s y + scMom L lam γ s • y := by
  rw [BetaSec, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]

/-- The lattice Sugawara Virasoro relation inside one charge sector (vector form); repackaging of
`hbos_core_vec`. -/
theorem OpSec_virasoro_vec (hPos : L.PosDef) (γ : L.carrier) (m n : ℤ) (q : FockN (rank L)) :
    OpSec L γ m (OpSec L γ n q) - OpSec L γ n (OpSec L γ m q)
      = ((m : ℂ) - n) • OpSec L γ (m + n) q
        + (if m + n = 0 then ((rank L : ℂ) * ((m : ℂ) ^ 3 - m) / 12) • q else 0) := by
  classical
  have hLL : ∀ (s t : ℤ) (y : FockN (rank L)),
      HeisenbergN.LvirN (rank L) 1 s (HeisenbergN.LvirN (rank L) 1 t y)
          - HeisenbergN.LvirN (rank L) 1 t (HeisenbergN.LvirN (rank L) 1 s y)
        = ((s : ℂ) - t) • HeisenbergN.LvirN (rank L) 1 (s + t) y
          + (if s + t = 0 then (rank L : ℂ) * ((s : ℂ) ^ 3 - s) / 12 else 0) • y := by
    intro s t y
    have h := congrArg (fun (T : End ℂ (FockN (rank L))) => T y)
      (HeisenbergN.L_virasoroN (rank L) 1 one_ne_zero s t)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at h
    exact h
  have hLa : ∀ (s t : ℤ) (y : FockN (rank L)),
      HeisenbergN.LvirN (rank L) 1 s (chargeOsc L γ t y)
        = (-(t : ℂ)) • chargeOsc L γ (s + t) y
          + chargeOsc L γ t (HeisenbergN.LvirN (rank L) 1 s y) := fun s t y =>
    LvirN_chargeOsc L γ s t y
  have haa : ∀ (s t : ℤ) (y : FockN (rank L)),
      chargeOsc L γ s (chargeOsc L γ t y) - chargeOsc L γ t (chargeOsc L γ s y)
        = (if s + t = 0 then ((L.form γ γ : ℤ) : ℂ) * (s : ℂ) else 0) • y := by
    intro s t y
    have h := congrArg (fun (T : End ℂ (FockN (rank L))) => T y)
      (chargeOsc_comm L hPos γ γ s t)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at h
    exact h
  exact hbos_core_vec L m n q (rank L : ℂ) ((L.form γ γ : ℤ) : ℂ)
    (HeisenbergN.LvirN (rank L) 1) (chargeOsc L γ) hLL hLa haa
    (fun s y => OpSec L γ s y) (by funext s y; exact OpSec_apply L γ s y)

/-- The lattice Sugawara Virasoro relation inside one charge sector (operator form),
central charge `rank L`. -/
theorem OpSec_virasoro (hPos : L.PosDef) (γ : L.carrier) (m n : ℤ) :
    OpSec L γ m * OpSec L γ n - OpSec L γ n * OpSec L γ m
      = ((m : ℂ) - n) • OpSec L γ (m + n)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * (rank L : ℂ) else 0)
            • (1 : End ℂ (FockN (rank L))) := by
  refine LinearMap.ext fun q => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    OpSec_virasoro_vec L hPos γ m n q, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, Module.End.one_apply]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn]
    congr 1
    congr 1
    ring
  · rw [if_neg hmn, if_neg hmn, zero_smul]

/-- **The heart of the matter.**  `[Lₘ, λ(n)] = −n·λ(m+n)` on the charge-`γ` sector, *with no
central residue*: the `δ_{m+n,0}·⟨γ,λ⟩·m` produced by `[γ(m), λ(n)]` is exactly the transformation
of the momentum zero mode `δ_{n,0}⟨λ,γ⟩` inside `BetaSec`.  This is the one place where the lattice
differs from the free boson (`VirasoroFock`), and it is why `BetaSec` must carry the zero mode. -/
theorem OpSec_comm_BetaSec (lam : Fin (rank L) → ℂ) (γ : L.carrier) (m n : ℤ) :
    OpSec L γ m * BetaSec L lam γ n - BetaSec L lam γ n * OpSec L γ m
      = (-(n : ℂ)) • BetaSec L lam γ (m + n) := by
  classical
  have hsplit : OpSec L γ m * BetaSec L lam γ n - BetaSec L lam γ n * OpSec L γ m
      = (HeisenbergN.LvirN (rank L) 1 m * bgOsc L lam n
          - bgOsc L lam n * HeisenbergN.LvirN (rank L) 1 m)
        + (chargeOsc L γ m * bgOsc L lam n - bgOsc L lam n * chargeOsc L γ m) := by
    rw [OpSec, BetaSec]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  rw [hsplit, LvirN_comm_bgOsc, chargeOsc_eq_bgOsc, bgOsc_comm, BetaSec, smul_add, smul_smul]
  congr 1
  congr 1
  rw [scMom, bgPair]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn, bgForm_comm]
    have hn : (n : ℂ) = -(m : ℂ) := by
      have h : n = -m := by omega
      rw [h]; push_cast; ring
    rw [hn]; ring
  · rw [if_neg hmn, if_neg hmn, mul_zero]

/-- The level of the background current: `[λ(m), λ(n)] = ⟨λ,λ⟩·m·δ_{m+n,0}` (the zero modes are
central and drop out). -/
theorem BetaSec_comm (lam : Fin (rank L) → ℂ) (γ : L.carrier) (m n : ℤ) :
    BetaSec L lam γ m * BetaSec L lam γ n - BetaSec L lam γ n * BetaSec L lam γ m
      = (if m + n = 0 then bgForm L lam lam * (m : ℂ) else 0)
          • (1 : End ℂ (FockN (rank L))) := by
  have hsplit : BetaSec L lam γ m * BetaSec L lam γ n - BetaSec L lam γ n * BetaSec L lam γ m
      = bgOsc L lam m * bgOsc L lam n - bgOsc L lam n * bgOsc L lam m := by
    rw [BetaSec, BetaSec]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  rw [hsplit, bgOsc_comm]

/-- The **background-charge Virasoro mode on the charge-`γ` sector**: `Lₙ − (n+1)λ(n)`. -/
noncomputable def LSecBg (lam : Fin (rank L) → ℂ) (γ : L.carrier) (s : ℤ) :
    End ℂ (FockN (rank L)) :=
  OpSec L γ s - ((s : ℂ) + 1) • BetaSec L lam γ s

/-- **The Virasoro relation on one charge sector**, central charge `rank L − 12⟨λ,λ⟩`. -/
theorem LSecBg_virasoro (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (γ : L.carrier) (m n : ℤ) :
    LSecBg L lam γ m * LSecBg L lam γ n - LSecBg L lam γ n * LSecBg L lam γ m
      = ((m : ℂ) - n) • LSecBg L lam γ (m + n)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * ((rank L : ℂ) - 12 * bgForm L lam lam)
           else 0) • (1 : End ℂ (FockN (rank L))) :=
  bg_virasoro_core (OpSec L γ) (BetaSec L lam γ) (rank L : ℂ) (bgForm L lam lam)
    (fun s t => OpSec_virasoro L hPos γ s t)
    (fun s t => OpSec_comm_BetaSec L lam γ s t)
    (fun s t => BetaSec_comm L lam γ s t) m n

@[simp] theorem scWt_zero (γ : L.carrier) :
    scWt L γ 0 = (1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ) := if_pos rfl

@[simp] theorem scMom_zero (lam : Fin (rank L) → ℂ) (γ : L.carrier) :
    scMom L lam γ 0 = bgPair L lam γ := if_pos rfl

/-! ## §3  The global background-charge current and Virasoro modes on `V_L`. -/

/-- The **background-charge current** `λ(z) = ∑ₐ λₐ·α^a(z)` on `V_L`, mode `n`.  It is assembled
from the VOA boson currents `alphaLatGen`, hence automatically carries the lattice **momentum zero
mode** `zGradeOpGen` at `n = 0` — the ingredient that is absent on the free-boson Fock space. -/
noncomputable def bgCur (lam : Fin (rank L) → ℂ) (n : ℤ) : End ℂ (LatModuleGen L) :=
  ∑ a : Fin (rank L), lam a • mode (alphaLatGen L a) n

/-- The background current on a basis vector `q ⊗ e^γ` is the sector current `BetaSec`. -/
theorem bgCur_latStateGen (lam : Fin (rank L) → ℂ) (n : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    bgCur L lam n (latStateGen L q γ) = latStateGen L (BetaSec L lam γ n q) γ := by
  classical
  have hcur : ∀ a : Fin (rank L),
      currentN (rank L) 1 a (-n - 1) = HeisenbergN.oscN (rank L) 1 a n := by
    intro a; rw [HeisenbergN.currentN_apply]; congr 1; ring
  have hbase : ∀ a : Fin (rank L),
      (lam a • mode (alphaLatGen L a) n) (latStateGen L q γ)
        = latStateGen L (lam a • HeisenbergN.oscN (rank L) 1 a n q) γ
          + (if n = 0 then lam a * chargeCoord L γ a else 0) • latStateGen L q γ := by
    intro a
    have hA : (LinearMap.rTensor (L.carrier →₀ ℂ) (HeisenbergN.oscN (rank L) 1 a n))
          (latStateGen L q γ) = latStateGen L (HeisenbergN.oscN (rank L) 1 a n q) γ := by
      simp only [latStateGen]
      rw [LinearMap.rTensor_tmul]
    have hB : (if (-n - 1 : ℤ) = -1 then zGradeOpGen L a else 0) (latStateGen L q γ)
        = (if n = 0 then chargeCoord L γ a else 0) • latStateGen L q γ := by
      by_cases hn : n = 0
      · rw [if_pos hn, if_pos (by omega : (-n - 1 : ℤ) = -1), zGradeOpGen_latStateGen]
      · rw [if_neg hn, if_neg (by omega : ¬ (-n - 1 : ℤ) = -1), LinearMap.zero_apply, zero_smul]
    rw [LinearMap.smul_apply, mode_apply, alphaLatGen_apply, LinearMap.add_apply, hcur a, hA, hB,
      smul_add, latStateGen_smul_boson, smul_smul, mul_ite, mul_zero]
  rw [bgCur, LinearMap.coe_sum, Finset.sum_apply,
    Finset.sum_congr rfl (fun a _ => hbase a), Finset.sum_add_distrib, ← Finset.sum_smul,
    BetaSec_apply, latStateGen_add_boson, latStateGen_smul_boson]
  congr 1
  · rw [bgOsc_apply]
    exact (map_sum (mkEα L γ) _ _).symm
  · congr 1
    rw [scMom, bgPair, bgForm]
    by_cases hn : n = 0
    · simp only [if_pos hn]
    · simp only [if_neg hn, Finset.sum_const_zero]

/-- **The background-charge Virasoro modes on `V_L`**: `Lₙ^λ = Lₙ − (n+1)·λ(n)`.

The sign is the one for which the conformal vector is `ω_L + λ(−2)|0⟩`; it is pinned by
`LBg_weight_latChargeGen` below. -/
noncomputable def LBg (lam : Fin (rank L) → ℂ) (n : ℤ) : End ℂ (LatModuleGen L) :=
  LLGen L n - ((n : ℂ) + 1) • bgCur L lam n

/-- `LBg` acts inside each charge sector by `LSecBg`. -/
theorem LBg_mkEα (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (n : ℤ) (q : FockN (rank L))
    (γ : L.carrier) :
    LBg L lam n (mkEα L γ q) = mkEα L γ (LSecBg L lam γ n q) := by
  classical
  have h1 : LLGen L n (mkEα L γ q) = mkEα L γ (OpSec L γ n q) := by
    rw [show mkEα L γ q = latStateGen L q γ from rfl, LLGen_tmul L hPos, OpSec_apply]
    simp only [map_add, apply_ite (mkEα L γ), map_zero, map_smul]
    rfl
  have h2 : bgCur L lam n (mkEα L γ q) = mkEα L γ (BetaSec L lam γ n q) :=
    bgCur_latStateGen L lam n q γ
  rw [LBg, LinearMap.sub_apply, LinearMap.smul_apply, h1, h2, LSecBg, LinearMap.sub_apply,
    LinearMap.smul_apply, map_sub, map_smul]

/-! ## §4  The Virasoro relation with central charge `rank L − 12⟨λ,λ⟩`. -/

/-- The background-charge Virasoro relation on a basis vector `q ⊗ e^γ`. -/
theorem LBg_comm_latStateGen (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (m n : ℤ)
    (q : FockN (rank L)) (γ : L.carrier) :
    (LBg L lam m * LBg L lam n - LBg L lam n * LBg L lam m) (latStateGen L q γ)
      = (((m : ℂ) - n) • LBg L lam (m + n)
          + (if m + n = 0
             then (((m : ℂ) ^ 3 - m) / 12 * ((rank L : ℂ) - 12 * bgForm L lam lam))
                    • (1 : End ℂ (LatModuleGen L))
             else 0)) (latStateGen L q γ) := by
  classical
  have hv := congrArg (fun (T : End ℂ (FockN (rank L))) => T q) (LSecBg_virasoro L hPos lam γ m n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply] at hv
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    show latStateGen L q γ = mkEα L γ q from rfl]
  simp only [LBg_mkEα L hPos]
  rw [← map_sub, hv, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    LBg_mkEα L hPos]
  congr 1
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn, LinearMap.smul_apply, Module.End.one_apply, map_smul]
  · rw [if_neg hmn, if_neg hmn, zero_smul, map_zero, LinearMap.zero_apply]

/-- **THE TARGET.**  The background-charge (Feigin–Fuchs / linear-dilaton) Virasoro relation on the
general even positive-definite lattice VOA `V_L`:

`[Lₘ^λ, Lₙ^λ] = (m−n)L_{m+n}^λ + δ_{m+n,0}·(m³−m)/12·c`,  `c = rank L − 12⟨λ,λ⟩`.

The background charge `λ` is an arbitrary vector of the ambient orthonormal frame — in particular it
need **not** lie in `L`, which is essential: for the triplet/singlet series `λ ∈ L ⊗ ℚ ∖ L`. -/
theorem LBg_virasoro (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (m n : ℤ) :
    LBg L lam m * LBg L lam n - LBg L lam n * LBg L lam m
      = ((m : ℂ) - n) • LBg L lam (m + n)
        + (if m + n = 0
           then (((m : ℂ) ^ 3 - m) / 12 * ((rank L : ℂ) - 12 * bgForm L lam lam))
                  • (1 : End ℂ (LatModuleGen L))
           else 0) := by
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y1 y2 hy1 hy2 => rw [map_add, map_add, hy1, hy2]
  | tmul q g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero]; rw [map_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add]; rw [map_add, map_add, h1, h2]
      | single c b =>
          rw [(Finsupp.smul_single_one c b).symm,
            show (Finsupp.single c 1 : L.carrier →₀ ℂ) = eGen L c from rfl]
          erw [TensorProduct.tmul_smul]
          rw [map_smul, map_smul, show q ⊗ₜ[ℂ] eGen L c = latStateGen L q c from rfl,
            LBg_comm_latStateGen L hPos]

/-! ## §5  The deformed conformal weight — this is what pins the sign. -/

/-- **The deformed weight of the charged vacuum**: `L₀^λ e^β = (½⟨β,β⟩ − ⟨λ,β⟩) e^β`.

This is the theorem that fixes the sign convention in `LBg`.  With `⟨α,α⟩ = 2p` and
`λ = ((p−1)/(2p))·α` it gives `wt(e^α) = p − (p−1) = 1` and `wt(e^{−α}) = p + (p−1) = 2p−1`,
the triplet-algebra normalization (see `LBg_weight_charge_self` / `LBg_weight_charge_neg`). -/
theorem LBg_weight_latChargeGen (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (β : L.carrier) :
    LBg L lam 0 (latChargeGen L β)
      = ((1 / 2 : ℂ) * ((L.form β β : ℤ) : ℂ) - bgPair L lam β) • latChargeGen L β := by
  have hvac : LSecBg L lam β 0 (HeisenbergN.vacuumN (rank L))
      = ((1 / 2 : ℂ) * ((L.form β β : ℤ) : ℂ) - bgPair L lam β)
          • HeisenbergN.vacuumN (rank L) := by
    rw [LSecBg, LinearMap.sub_apply, LinearMap.smul_apply, OpSec, BetaSec, scWt_zero, scMom_zero,
      LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, Module.End.one_apply,
      HeisenbergN.LvirN_vacuum (rank L) 1 (by norm_num : (-1 : ℤ) ≤ 0),
      chargeOsc_eq_bgOsc, bgOsc_zero, bgOsc_zero, LinearMap.zero_apply]
    push_cast
    module
  rw [latChargeGen, show latStateGen L (HeisenbergN.vacuumN (rank L)) β
      = mkEα L β (HeisenbergN.vacuumN (rank L)) from rfl, LBg_mkEα L hPos, hvac, map_smul]

/-! ## §6  The lattice-direction background charge `λ = c·α`. -/

/-- The background charge `λ = c·α` in the direction of a lattice vector `α`, with `c ∈ ℂ`
arbitrary (in applications `c ∈ ℚ`, so `λ ∉ L`). -/
noncomputable def latBg (c : ℂ) (α : L.carrier) : Fin (rank L) → ℂ :=
  fun a => c * chargeCoord L α a

theorem bgForm_latBg (hPos : L.PosDef) (c d : ℂ) (α β : L.carrier) :
    bgForm L (latBg L c α) (latBg L d β) = c * d * ((L.form α β : ℤ) : ℂ) := by
  rw [← bgForm_chargeCoord L hPos α β, bgForm, bgForm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by simp only [latBg]; ring

theorem bgPair_latBg (hPos : L.PosDef) (c : ℂ) (α γ : L.carrier) :
    bgPair L (latBg L c α) γ = c * ((L.form α γ : ℤ) : ℂ) := by
  rw [bgPair, show chargeCoord L γ = latBg L 1 γ from by funext a; simp [latBg],
    bgForm_latBg L hPos]
  ring

/-- **Central charge `rank L − 12 c²⟨α,α⟩`** for the lattice-direction background charge `λ = cα`.
For rank `1` with `⟨α,α⟩ = 2p` and `c = (p−1)/(2p)` this is `1 − 6(p−1)²/p`, the `(1,p)` triplet
central charge (`p = 2` gives `c = −2`). -/
theorem LBg_virasoro_latBg (hPos : L.PosDef) (c : ℂ) (α : L.carrier) (m n : ℤ) :
    LBg L (latBg L c α) m * LBg L (latBg L c α) n
        - LBg L (latBg L c α) n * LBg L (latBg L c α) m
      = ((m : ℂ) - n) • LBg L (latBg L c α) (m + n)
        + (if m + n = 0
           then (((m : ℂ) ^ 3 - m) / 12 * ((rank L : ℂ) - 12 * (c ^ 2 * ((L.form α α : ℤ) : ℂ))))
                  • (1 : End ℂ (LatModuleGen L))
           else 0) := by
  have h : bgForm L (latBg L c α) (latBg L c α) = c ^ 2 * ((L.form α α : ℤ) : ℂ) := by
    rw [bgForm_latBg L hPos]; ring
  rw [← h]
  exact LBg_virasoro L hPos (latBg L c α) m n

/-- `wt(e^α) = (½ − c)⟨α,α⟩` for `λ = cα`.  With `⟨α,α⟩ = 2p`, `c = (p−1)/(2p)`: `wt = 1`. -/
theorem LBg_weight_charge_self (hPos : L.PosDef) (c : ℂ) (α : L.carrier) :
    LBg L (latBg L c α) 0 (latChargeGen L α)
      = (((1 / 2 : ℂ) - c) * ((L.form α α : ℤ) : ℂ)) • latChargeGen L α := by
  rw [LBg_weight_latChargeGen L hPos, bgPair_latBg L hPos]
  congr 1
  ring

/-- `wt(e^{−α}) = (½ + c)⟨α,α⟩` for `λ = cα`.  With `⟨α,α⟩ = 2p`, `c = (p−1)/(2p)`: `wt = 2p−1`. -/
theorem LBg_weight_charge_neg (hPos : L.PosDef) (c : ℂ) (α : L.carrier) :
    LBg L (latBg L c α) 0 (latChargeGen L (-α))
      = (((1 / 2 : ℂ) + c) * ((L.form α α : ℤ) : ℂ)) • latChargeGen L (-α) := by
  have h1 : L.form (-α) (-α) = L.form α α := by simp
  have h2 : L.form α (-α) = - L.form α α := by simp
  rw [LBg_weight_latChargeGen L hPos, bgPair_latBg L hPos, h1, h2]
  push_cast
  congr 1
  ring

/-! ## §7  The background-charge conformal vector `ω_λ = ω_L + λ(−2)|0⟩`. -/

/-- `:f(z)1(z): = f(z)` whenever the right factor *is* the identity field. -/
theorem nprod_eq_of_right_eq_idField {V : Type*} [AddCommGroup V] [Module ℂ V]
    {f g : FormalDist (End ℂ V)} (hf : IsField f) (hg : IsField g) (h : g = idField) :
    nprod hf hg = f := by
  subst h
  exact nprod_idField hf

/-- The neutral (charge-`0`) word field of length one is the boson generator field
`Y(α^a_{-i-1}|0⟩, z) = (i!)⁻¹ ∂ᶦ α^a(z)`; the charge-`0` seed `Yeαvec 0` is the identity field. -/
theorem YwordLatGen_singleton (i : ℕ) (a : Fin (rank L)) :
    YwordLatGen L [(i, a)] 0 = genFieldLatGen L a i := by
  have h0 : YwordLatGen L ([] : List (ℕ × Fin (rank L))) (0 : L.carrier)
      = (idField : FormalDist (End ℂ (LatModuleGen L))) := by
    rw [YwordLatGen_nil]
    funext t
    refine LinearMap.ext fun y => ?_
    rw [Yeαvec_zero_apply, idField_apply]
    split_ifs with ht
    · rw [LinearMap.id_apply]
    · rw [LinearMap.zero_apply]
  rw [YwordLatGen_cons]
  exact nprod_eq_of_right_eq_idField _ _ h0

/-- The modes of `∂α^a(z)`: `mode (∂α^a) (n+1) = −(n+1)·mode(α^a) n`.  This is the
`−(n+1)` that the background-charge deformation needs, produced by the derivative in `λ(−2)|0⟩`. -/
theorem mode_genFieldLatGen_one (a : Fin (rank L)) (n : ℤ) :
    mode (genFieldLatGen L a 1) (n + 1) = (-((n : ℂ) + 1)) • mode (alphaLatGen L a) n := by
  have h1 : genFieldLatGen L a 1 = VOA.deriv (alphaLatGen L a) := by
    rw [genFieldLatGen, Function.iterate_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
  have hd : VOA.deriv (alphaLatGen L a) (-(n + 1) - 1)
      = ((-(n + 1) - 1 + 1 : ℤ)) • alphaLatGen L a (-(n + 1) - 1 + 1) := rfl
  rw [h1, mode_apply, mode_apply, hd, show (-(n + 1) - 1 + 1 : ℤ) = -n - 1 from by ring,
    ← Int.cast_smul_eq_zsmul ℂ (-n - 1 : ℤ) (alphaLatGen L a (-n - 1))]
  congr 1
  push_cast
  ring

/-- `λ(−2)|0⟩` written out as a combination of boson word states. -/
theorem mkEα_osc_eq_wordState (a : Fin (rank L)) :
    mkEα L 0 (HeisenbergN.oscN (rank L) 1 a (-2) (HeisenbergN.vacuumN (rank L)))
      = wordStateLatGen L [(1, a)] 0 := by
  rw [wordStateLatGen_cons, wordStateLatGen_nil, latChargeGen]
  simp only [latStateGen, mkEα_apply]
  rw [show currentN (rank L) 1 a ((1 : ℕ) : ℤ) = HeisenbergN.oscN (rank L) 1 a (-2) from by
      rw [HeisenbergN.currentN_apply, Nat.cast_one]; norm_num, LinearMap.rTensor_tmul]

/-- **The background-charge conformal vector** `ω_λ = ω_L + λ(−2)|0⟩ ∈ V_L`.

`λ(−2)|0⟩ = ∑ₐ λₐ·α^a_{−2}|0⟩` always lies in `V_L` even though `λ ∉ L`: the background charge only
ever enters through the *neutral* (charge-`0`) Fock factor, which is a `ℂ`-vector space. -/
noncomputable def omegaBg (lam : Fin (rank L) → ℂ) : LatModuleGen L :=
  omegaLatGen L + mkEα L 0 (bgOsc L lam (-2) (HeisenbergN.vacuumN (rank L)))

/-- **`ω_λ` really is the conformal vector of `LBg`**:
`mode (Y(ω_λ, z)) (n+1) = Lₙ^λ`, with `Y` the reconstructed lattice vertex map.

Together with `LBg_virasoro` this exhibits `ω_λ` as a genuine conformal vector on `V_L` of central
charge `rank L − 12⟨λ,λ⟩` (the `L₀`-grading and the vacuum axioms are of course *not* claimed: for
`λ ≠ 0` the weights are shifted and in general not bounded below). -/
theorem mode_YfullGen_omegaBg (hEven : L.Even) (hPos : L.PosDef) (lam : Fin (rank L) → ℂ)
    (n : ℤ) :
    mode (YfullGen L hEven hPos (omegaBg L lam)) (n + 1) = LBg L lam n := by
  classical
  have hY : YfullGen L hEven hPos (omegaBg L lam)
      = YfullGen L hEven hPos (omegaLatGen L)
        + ∑ a : Fin (rank L), lam a • genFieldLatGen L a 1 := by
    rw [omegaBg, map_add]
    congr 1
    rw [bgOsc_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, map_smul, mkEα_osc_eq_wordState, YfullGen_word, YwordLatGen_singleton]
  have hsum : (∑ a : Fin (rank L), lam a • genFieldLatGen L a 1) (-(n + 1) - 1)
      = ∑ a : Fin (rank L), lam a • (genFieldLatGen L a 1) (-(n + 1) - 1) :=
    Finset.sum_apply (-(n + 1) - 1) Finset.univ (fun a => lam a • genFieldLatGen L a 1)
  have hmode : mode (YfullGen L hEven hPos (omegaBg L lam)) (n + 1)
      = LLGen L n + ∑ a : Fin (rank L), lam a • mode (genFieldLatGen L a 1) (n + 1) := by
    rw [hY]
    change (YfullGen L hEven hPos (omegaLatGen L)) (-(n + 1) - 1)
        + (∑ a : Fin (rank L), lam a • genFieldLatGen L a 1) (-(n + 1) - 1)
      = LLGen L n + ∑ a : Fin (rank L), lam a • mode (genFieldLatGen L a 1) (n + 1)
    rw [hsum]
    congr 1
    exact mode_YfullGen_omega_eq_LLGen L hEven hPos n
  rw [hmode,
    Finset.sum_congr rfl (fun a (_ : a ∈ (Finset.univ : Finset (Fin (rank L)))) => by
      rw [mode_genFieldLatGen_one L a n, smul_comm]),
    ← Finset.smul_sum, LBg, bgCur, neg_smul, ← sub_eq_add_neg]

end VOA.LatGen.BgA
