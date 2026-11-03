/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedLeading

/-!
# The twisted product formula at two exponentials  (Moonshine step M6)

The base case `PF (e^α) (e^β)` of the twisted product formula, and hence (`PF_of_base`) the
twisted product formula `PF u v` for **all** states `u, v` of `V_L`.

The defect `D(e,e',ℓ) = Def β (e^α) e e' ℓ` vanishes at large `ℓ` (`Def_eventually_zero`); we
descend in `ℓ`.  At a level `m` below which nothing is known yet but above which `D` vanishes,
the recursion `Def_ode` (with `Def_balance`) gives, for `x_c = D(0,c,m)` and `y_c = D(1,c−1,m)`,

  `−(m+1) x = n y`,  `−(m+1) y = n x`  (`n = ⟨α,β⟩`),

so `(m+1+n)(x+y) = 0` and `(m+1−n)(x−y) = 0`.  Away from the two degenerate levels both
combinations vanish.  At `m = −n−1` (resp. `m = n−1`) the combination `x+y` (resp. `x−y`)
satisfies the charge relation of charge `α+β` (resp. `β−α`) by `Def_charge`, so by the uniqueness
lemma `fld_eq_zero_of_charge` it vanishes once its vacuum expectations vanish.  These are
computed by `cfT_star_YTL` and the scalar identities `leading_plus` / `leading_minus`, against
`e^α₍ₘ₎e^β = ε(α,β) e^{α±β}` on the state side (`smul_echg_echg`).  The normalisation
`2^{−|α|²}` of the twisted exponential is exactly what makes the two sides agree.

* `vac_plus`, `vac_minus` — the two vacuum identities;
* `Def_level` — one step of the descent;
* `Def_echg_eq_zero` — the defect vanishes identically;
* `PF_echg` — the base case; `PF_all` — the twisted product formula for all states.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA.Moonshine.LatticeTwisted

open MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN IntegralLattice LatGen Extraspecial
open Module (End)
open scoped BigOperators TensorProduct

variable (L : IntegralLattice.{0}) (hEven : L.Even) (hU : IsUnit (gramMat L).det) (hPos : L.PosDef)

/-- The vacuum expectation of the zero mode, as a linear functional on fields. -/
noncomputable def vacL (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    Fld (MT L hEven hU) →ₗ[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU) :=
  (cfT 0) ∘ₗ (LinearMap.applyₗ (1 ⊗ₜ[ℂ] t)) ∘ₗ modeL 0

theorem vacL_apply (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) (X : Fld (MT L hEven hU)) :
    vacL L hEven hU t X = cfT 0 (mode X.1 0 (1 ⊗ₜ[ℂ] t)) := rfl

theorem cfT_YTL_one (γ : L.carrier) (k : ℤ) (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    cfT 0 (YTL L hEven hU γ k (1 ⊗ₜ[ℂ] t))
      = ((2 : ℂ) ^ (-(L.form γ γ)) * (if -k - 2 + L.form γ γ = 0 then 1 else 0))
        • eT L hEven hU γ t := by
  rw [YTL_tmul, map_smul, cfT_tmul, DD_one, smul_smul,
    show coeff 0 (sMz (chargeCoord L γ) (-k - 2 + L.form γ γ))
      = constantCoeff (sMz (chargeCoord L γ) (-k - 2 + L.form γ γ)) by
        rw [MvPolynomial.constantCoeff_eq], constantCoeff_sMz]

theorem eT_eT_apply (α β : L.carrier) (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    eT L hEven hU α (eT L hEven hU β t) = latticeCocycle L α β • eT L hEven hU (α + β) t := by
  rw [show eT L hEven hU α (eT L hEven hU β t) = (eT L hEven hU α * eT L hEven hU β) t from rfl,
    eT_mul, LinearMap.smul_apply]

theorem pow_two_combine (A B D : ℤ) (a b : ℕ) (h : (a : ℤ) - b = D) :
    (2 : ℂ) ^ (-A) * (2 : ℂ) ^ (-B) * ((1 / 2 : ℂ) ^ a * 2 ^ b) = (2 : ℂ) ^ (-(A + D + B)) := by
  rw [one_div, inv_pow, ← zpow_natCast, ← zpow_natCast (2 : ℂ) b, ← zpow_neg,
    ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0),
    ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]
  congr 1
  omega

theorem form_add_self (α β : L.carrier) :
    L.form (α + β) (α + β) = L.form α α + 2 * L.form α β + L.form β β := by
  simp only [map_add, LinearMap.add_apply]
  rw [form_symm L β α]
  ring

theorem form_neg_add_self (α β : L.carrier) :
    L.form (-α + β) (-α + β) = L.form α α + -(2 * L.form α β) + L.form β β := by
  rw [form_add_self]
  simp only [map_neg, LinearMap.neg_apply]
  ring

theorem piE_zero_add_one (u : LatModuleGen L) : piE L 0 u + piE L 1 u = u := by
  simp only [piE, zpow_zero, zpow_one, one_smul, neg_one_smul]
  module

theorem piE_zero_eq (u : LatModuleGen L) : piE L 0 u = piE L 1 u + thetaLat L u := by
  simp only [piE, zpow_zero, zpow_one, one_smul, neg_one_smul]
  module

theorem Def_mem (β : L.carrier) (u : LatModuleGen L) (e e' ℓ : ℤ) :
    Def L hEven hU hPos β u e e' ℓ ∈ TGenerated (latGenSet L hEven hU) :=
  sub_mem_tgenerated (star_mem (latGenSet_local L hEven hU hPos) (FL_mem L hEven hU hPos _ _)
    (FL_mem L hEven hU hPos _ _) _ _) (FL_mem L hEven hU hPos _ _)

/-- The vacuum identity at the level `m = −⟨α,β⟩ − 1`. -/
theorem vac_plus (α β : L.carrier) (m c : ℤ) (hm : m = -L.form α β - 1)
    (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    vacL L hEven hU t (Def L hEven hU hPos β (echg L α) 0 c m
      + Def L hEven hU hPos β (echg L α) 1 (c - 1) m) = 0 := by
  subst hm
  set n := L.form α β with hn
  set I : ℕ := (n.natAbs + n + 1).toNat
  rw [map_add, Def, Def, map_sub, map_sub, sub_add_sub_comm, sub_eq_zero,
    show (0 : ℤ) + c = c by ring, show (1 : ℤ) + (c - 1) = c by ring,
    ← map_add (vacL L hEven hU t) (FL L hEven hU c _) (FL L hEven hU c _),
    ← map_add (FL L hEven hU c), ← PreVertexAlgebra.smul_add_left, piE_zero_add_one]
  simp only [FL_echg L hEven hU hPos]
  rw [vacL_apply, vacL_apply, cfT_star_YTL L hEven hU hPos α β 0 c _ I (by omega),
    cfT_star_YTL L hEven hU hPos α β 1 (c - 1) _ I (by omega), smul_echg_echg, ← hn]
  rw [if_pos (show (0 : ℤ) ≤ -(-n - 1) - 1 - n by omega),
    show (-(-n - 1) - 1 - n).toNat = 0 by omega, vSchur_zero, ← echg_eq,
    map_smul, map_smul, FL_echg L hEven hU hPos, vacL_apply, mode_YTLFld, cfT_YTL_one,
    eT_eT_apply, form_add_self, ← hn, smul_smul, smul_smul, smul_smul, ← add_smul]
  by_cases hC : c + 2 = L.form α α + 2 * n + L.form β β
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), ← add_mul, ← mul_add,
      show L.form α α - 2 - 1 = L.form α α - 2 - 0 - 1 by ring,
      leading_plus n (L.form α α - 2 - 0) I (by omega)]
    congr 1
    rw [pow_two_combine _ _ (2 * n) _ _ (by omega)]
    ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp

/-- The vacuum identity at the level `m = ⟨α,β⟩ − 1`. -/
theorem vac_minus (α β : L.carrier) (m c : ℤ) (hm : m = L.form α β - 1)
    (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    vacL L hEven hU t (Def L hEven hU hPos β (echg L α) 0 c m
      + (-1 : ℂ) • Def L hEven hU hPos β (echg L α) 1 (c - 1) m) = 0 := by
  subst hm
  set n := L.form α β with hn
  set I : ℕ := (n.natAbs - n + 1).toNat
  rw [neg_one_smul, ← sub_eq_add_neg, map_sub, Def, Def, map_sub, map_sub, sub_sub_sub_comm,
    sub_eq_zero, show (0 : ℤ) + c = c by ring, show (1 : ℤ) + (c - 1) = c by ring,
    ← map_sub (vacL L hEven hU t) (FL L hEven hU c _) (FL L hEven hU c _),
    ← map_sub (FL L hEven hU c), piE_zero_eq, PreVertexAlgebra.smul_add_left, add_sub_cancel_left,
    thetaLat_latChargeGen]
  simp only [FL_echg L hEven hU hPos]
  rw [vacL_apply, vacL_apply, cfT_star_YTL L hEven hU hPos α β 0 c _ I (by omega),
    cfT_star_YTL L hEven hU hPos α β 1 (c - 1) _ I (by omega), smul_echg_echg,
    map_neg, LinearMap.neg_apply, ← hn, latticeCocycle_neg_left]
  rw [if_pos (show (0 : ℤ) ≤ -(n - 1) - 1 - -n by omega),
    show (-(n - 1) - 1 - -n).toNat = 0 by omega, vSchur_zero, ← echg_eq,
    map_smul, map_smul, FL_echg L hEven hU hPos, vacL_apply, mode_YTLFld, cfT_YTL_one,
    eT_eT_apply, form_neg_add_self, ← hn, smul_smul, smul_smul, smul_smul, ← sub_smul]
  have heT : eT L hEven hU (α + β) = eT L hEven hU (-α + β) := by
    rw [← eT_add_two_nsmul L hEven hU (-α + β) α]
    congr 1
    abel
  rw [heT]
  by_cases hC : c + 2 = L.form α α + -(2 * n) + L.form β β
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), ← sub_mul, ← mul_sub,
      show L.form α α - 2 - 1 = L.form α α - 2 - 0 - 1 by ring,
      leading_minus n (L.form α α - 2 - 0) (by have := hEven α; omega) I (by omega)]
    congr 1
    rw [pow_two_combine _ _ (-(2 * n)) _ _ (by omega)]
    ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp

/-- **One step of the descent**: if the defect vanishes above level `m`, it vanishes at `m`. -/
theorem Def_level (α β : L.carrier) (m : ℤ)
    (h : ∀ e e' m' : ℤ, m < m' → Def L hEven hU hPos β (echg L α) e e' m' = 0) :
    ∀ e e' : ℤ, Def L hEven hU hPos β (echg L α) e e' m = 0 := by
  set D := fun e e' : ℤ => Def L hEven hU hPos β (echg L α) e e' m with hD
  set n := L.form α β with hn
  have hode : ∀ e e' : ℤ, (-(((m + 1 : ℤ)) : ℂ)) • D e e' = (n : ℂ) • D (e - 1) (e' + 1) := by
    intro e e'
    have := Def_ode L hEven hU hPos α β e e' (m + 1) (fun m' hm' => h _ _ _ (by omega))
    rwa [show m + 1 - 1 = m by ring] at this
  have hx : ∀ c : ℤ, (-(((m + 1 : ℤ)) : ℂ)) • D 0 c = (n : ℂ) • D 1 (c - 1) := by
    intro c
    have h1 := hode 0 c
    have h2 := Def_balance L hEven hU hPos β (echg L α) (-1) (c + 1) m
    rw [show (-1 : ℤ) + 2 = 1 by norm_num, show c + 1 - 2 = c - 1 by ring] at h2
    rw [h1, show (0 : ℤ) - 1 = -1 by norm_num]
    exact congrArg _ h2.symm
  have hy : ∀ c : ℤ, (-(((m + 1 : ℤ)) : ℂ)) • D 1 (c - 1) = (n : ℂ) • D 0 c := by
    intro c
    have h1 := hode 1 (c - 1)
    rwa [show (1 : ℤ) - 1 = 0 by norm_num, show c - 1 + 1 = c by ring] at h1
  have hmem : ∀ e e' : ℤ, D e e' ∈ TGenerated (latGenSet L hEven hU) :=
    fun e e' => Def_mem L hEven hU hPos β _ e e' m
  have hl : ∀ (b : Fin (rank L)) {X : Fld (MT L hEven hU)},
      X ∈ TGenerated (latGenSet L hEven hU) →
      Local (FgT (Tm := Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) b).1 X.1 :=
    fun b X hX => tloc L hEven hU hPos (FgT_mem L hEven hU b) hX
  have hch := Def_charge L hEven hU hPos α β m h
  have hb2 : ∀ c : ℤ, D 2 (c - 1) = D 0 (c + 1) := by
    intro c
    have h2 := Def_balance L hEven hU hPos β (echg L α) 0 (c + 1) m
    rwa [show (0 : ℤ) + 2 = 2 by norm_num, show c + 1 - 2 = c - 1 by ring] at h2
  -- the combination `x + y`
  have hplus : ∀ c : ℤ, D 0 c + D 1 (c - 1) = 0 := by
    by_cases hdeg : m + 1 + n = 0
    · refine fld_eq_zero_of_charge (fun b => chargeCoord L α b + chargeCoord L β b)
        (fun c => D 0 c + D 1 (c - 1)) (fun c => ?_) (fun b c => ?_) (fun b c s => ?_)
        (fun c t => ?_)
      · show D 0 (c + 2) + D 1 (c + 2 - 1) = fzmul 1 (D 0 c + D 1 (c - 1))
        rw [show c + 2 - 1 = c - 1 + 2 by ring, hD]
        simp only
        rw [Def_shift_right, Def_shift_right, fzmul_add]
      · exact hl b (add_mem_tgenerated (hmem _ _) (hmem _ _))
      · show star (1 / 2) (FgT b) s (D 0 c + D 1 (c - 1))
          = if s = 0 then (chargeCoord L α b + chargeCoord L β b) • (D 0 (c + 1) + D 1 (c + 1 - 1))
            else 0
        rw [star_add_right (hl b (hmem _ _)) (hl b (hmem _ _)), hD]
        simp only
        rw [hch b 0 c s, hch b 1 (c - 1) s]
        split_ifs
        · have := hb2 c
          simp only [hD] at this
          rw [show (0 : ℤ) + 1 = 1 by norm_num, show c - 1 + 1 = c by ring,
            show (1 : ℤ) + 1 = 2 by norm_num, show c + 1 - 1 = c by ring, this]
          module
        · rw [add_zero]
      · exact vac_plus L hEven hU hPos α β m c (by omega) t
    · intro c
      have hz : (((m + 1 + n : ℤ)) : ℂ) • (D 0 c + D 1 (c - 1)) = 0 := by
        have h1 := hx c
        have h2 := hy c
        push_cast at h1 h2 ⊢
        linear_combination (norm := module) -h1 - h2
      rcases smul_eq_zero.mp hz with h0 | h0
      · exact absurd (by exact_mod_cast h0) hdeg
      · exact h0
  -- the combination `x − y`
  have hminus : ∀ c : ℤ, D 0 c + (-1 : ℂ) • D 1 (c - 1) = 0 := by
    by_cases hdeg : m + 1 - n = 0
    · refine fld_eq_zero_of_charge (fun b => chargeCoord L β b - chargeCoord L α b)
        (fun c => D 0 c + (-1 : ℂ) • D 1 (c - 1)) (fun c => ?_) (fun b c => ?_) (fun b c s => ?_)
        (fun c t => ?_)
      · show D 0 (c + 2) + (-1 : ℂ) • D 1 (c + 2 - 1) = fzmul 1 (D 0 c + (-1 : ℂ) • D 1 (c - 1))
        rw [show c + 2 - 1 = c - 1 + 2 by ring, hD]
        simp only
        rw [Def_shift_right, Def_shift_right, fzmul_add, fzmul_smul]
      · exact hl b (add_mem_tgenerated (hmem _ _) (smul_mem_tgenerated _ (hmem _ _)))
      · show star (1 / 2) (FgT b) s (D 0 c + (-1 : ℂ) • D 1 (c - 1))
          = if s = 0 then (chargeCoord L β b - chargeCoord L α b) •
              (D 0 (c + 1) + (-1 : ℂ) • D 1 (c + 1 - 1)) else 0
        rw [star_add_right (hl b (hmem _ _)) (hl b (smul_mem_tgenerated _ (hmem _ _))),
          star_smul_right (hl b (hmem _ _)), hD]
        simp only
        rw [hch b 0 c s, hch b 1 (c - 1) s]
        split_ifs
        · have := hb2 c
          simp only [hD] at this
          rw [show (0 : ℤ) + 1 = 1 by norm_num, show c - 1 + 1 = c by ring,
            show (1 : ℤ) + 1 = 2 by norm_num, show c + 1 - 1 = c by ring, this]
          module
        · rw [smul_zero, add_zero]
      · exact vac_minus L hEven hU hPos α β m c (by omega) t
    · intro c
      have hz : (((m + 1 - n : ℤ)) : ℂ) • (D 0 c + (-1 : ℂ) • D 1 (c - 1)) = 0 := by
        have h1 := hx c
        have h2 := hy c
        push_cast at h1 h2 ⊢
        linear_combination (norm := module) h2 - h1
      rcases smul_eq_zero.mp hz with h0 | h0
      · exact absurd (by exact_mod_cast h0) hdeg
      · exact h0
  -- both classes vanish
  have h0 : ∀ c : ℤ, D 0 c = 0 := by
    intro c
    have h1 := hplus c
    have h2 := hminus c
    linear_combination (norm := module) (1 / 2 : ℂ) • h1 + (1 / 2 : ℂ) • h2
  have h1 : ∀ c : ℤ, D 1 c = 0 := by
    intro c
    have h1 := hplus (c + 1)
    rw [h0, zero_add, show c + 1 - 1 = c by ring] at h1
    exact h1
  intro e e'
  have he : e = e % 2 + 2 * (e / 2) := by omega
  show D e e' = 0
  rw [hD]
  simp only
  rw [he, Def_shift_left']
  rcases Int.emod_two_eq_zero_or_one e with hr | hr
  · rw [hr]
    have := h0 e'
    simp only [hD] at this
    rw [this, fzmul_zero]
  · rw [hr]
    have := h1 e'
    simp only [hD] at this
    rw [this, fzmul_zero]

/-- **The defect vanishes identically.** -/
theorem Def_echg_eq_zero (α β : L.carrier) (e e' ℓ : ℤ) :
    Def L hEven hU hPos β (echg L α) e e' ℓ = 0 := by
  obtain ⟨L0, hL0⟩ := Def_eventually_zero L hEven hU hPos β (echg L α)
  have key : ∀ k : ℕ, ∀ e e' ℓ : ℤ, L0 - k ≤ ℓ → Def L hEven hU hPos β (echg L α) e e' ℓ = 0 := by
    intro k
    induction k with
    | zero => exact fun e e' ℓ hℓ => hL0 e e' ℓ (by simpa using hℓ)
    | succ k ih =>
      intro e e' ℓ hℓ
      rcases lt_or_ge ℓ (L0 - k) with hlt | hge
      · have hℓ' : ℓ = L0 - k - 1 := by push_cast at hℓ; omega
        exact Def_level L hEven hU hPos α β ℓ (fun e e' m' hm' => ih e e' m' (by omega)) e e'
      · exact ih e e' ℓ hge
  exact key (L0 - ℓ).toNat e e' ℓ (by omega)

/-- **The base case of the twisted product formula**: `PF (e^α) (e^β)`. -/
theorem PF_echg (α β : L.carrier) : PF L hEven hU hPos (echg L α) (echg L β) :=
  PF_echg_of_Def L hEven hU hPos α β (Def_echg_eq_zero L hEven hU hPos α β)

/-- **The twisted product formula for all states of `V_L`**:
`star (e/2) F_e(u) ℓ F_{e'}(v) = F_{e+e'}((piE e u)₍ℓ₎ v)`. -/
theorem PF_all (u v : LatModuleGen L) : PF L hEven hU hPos u v :=
  PF_of_base L hEven hU hPos (PF_echg L hEven hU hPos) u v

end VOA.Moonshine.LatticeTwisted
