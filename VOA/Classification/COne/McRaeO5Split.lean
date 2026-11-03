/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO5Twisted
import VOA.Classification.COne.McRaeO5Cyclic
import VOA.Classification.COne.ABDWeakAdmissibleSpectrum

/-! # O5, parts (b) and (d): twisted summands are modules for `V^{⟨g⟩}`, and surjections split

Setting: `W` a VOA, `G ≤ Aut W`, `C = LogModuleCat (W^G)` (`C₂`), `V = vObj G hfg` the O3 algebra.
Let `(X, a)` be a left `V`-module in `C`, `g ∈ G`, and `p : X ⟶ X` a module endomorphism whose image
is `g`-twisted (for instance McRae's projection `π_g` of O4c).

* **(b), the analytic bridge — isolated, not proved.** `TwistedJacobiBridge G hfg hC2` states the
  Jacobi identity for the integral log-free modes of `actY a` on `range p`, for `u, v` fixed by `g`.
  It is McRae's Thm 4.14 / Huang–Kirillov–Lepowsky / Creutzig–Kanade–McRae Thm 3.65 (a local
  module of the commutative algebra `V^{⟨g⟩}` in `C` is a `V^{⟨g⟩}`-module), restricted to
  `V^{⟨g⟩} ⊆ V`, where O5(a) (`twisted_modes`) already shows the modes are integral and log-free.
* `twistedWeakModule`: given the bridge, `range p` is a weak `V^{⟨g⟩}`-module, extending the
  `V^G`-action of `X` (`twistedWeakModule_mode_fixed`).
* `twisted_admissible`: it is admissible (generalized `L₀`-eigenspaces span, bounded below).
* `exists_twisted_section`: if `V^{⟨g⟩}` is admissibly rational, every surjective `V`-module
  map `f : X₁ ⟶ X₂` has a `C`-morphism `s : X₂ ⟶ X₁` with `s ≫ f = p₂`, `p₂ ≫ s = s`,
  `s ≫ p₁ = s`.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO5
open CategoryTheory MonoidalCategory BraidedCategory VOA.LogTensor VOA.LogTensor.LogModuleCat
open VOA.C2Rigid.LocalInjective VOA.Classification.COne.McRaeO4c VOA.Classification.COne.McRaeO3

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-! ## The weak `V^{⟨g⟩}`-module on the image of `p` -/

section Construction
variable {G : Subgroup (Aut W)} {hfg : FinGen (orbifold G).adjointRestrict}
  {hC2 : C2Cofinite (orbifoldVOA G)} {X : LogModuleCat (orbifoldVOA G)}
  (a : tensorObject hC2 (vObj G hfg) X ⟶ X) (p : X ⟶ X) (g : Aut W)

/-- The image of `p`. -/
abbrev Sp : Submodule ℂ X := LinearMap.range p.1

/-- Mode-level data extracted from the categorical hypotheses. -/
structure TwistData : Prop where
  /-- `p` is a module map: `p ∘ actY a = actY a ∘ (1 ⊗ p)`. -/
  stab : ∀ (n : ℂ) (k : ℕ) (v : V) (x : X),
    p.1 ((actY hC2 a).1 n k v x) = (actY hC2 a).1 n k v (p.1 x)
  /-- O5(a): on `range p`, `g`-fixed vectors act log-free (`k ≥ 1` modes vanish). -/
  logFree : ∀ v : V, g v = v → ∀ (x : X) (n : ℂ) (k : ℕ), 1 ≤ k →
    (actY hC2 a).1 n k v (p.1 x) = 0
  /-- O5(a): on `range p`, `g`-fixed vectors act with integral powers only. -/
  integral : ∀ v : V, g v = v → ∀ (x : X) (n : ℂ), (∀ j : ℤ, n ≠ j) →
    (actY hC2 a).1 n 0 v (p.1 x) = 0
  /-- Unit law: on `V^G`, the action is that of `X`. -/
  unit : ∀ (u : (orbifold G).carrier) (j : ℤ) (x : X),
    (actY hC2 a).1 (j : ℂ) 0 (u : V) x = mode (X.act.YM u) j x
  /-- **The bridge (b)**: the Jacobi identity on `range p` for `g`-fixed vectors. -/
  jacobi : ∀ u v : V, g u = u → g v = v → ∀ (x : X) (ℓ m n : ℤ),
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        ((actY hC2 a).1 ((ℓ + m - i : ℤ) : ℂ) 0 u ((actY hC2 a).1 ((n + i : ℤ) : ℂ) 0 v (p.1 x))
          - negOnePow ℓ • (actY hC2 a).1 ((ℓ + n - i : ℤ) : ℂ) 0 v
              ((actY hC2 a).1 ((m + i : ℤ) : ℂ) 0 u (p.1 x))))
      = ∑ᶠ i : ℤ, cbz m i • (actY hC2 a).1 ((m + n - i : ℤ) : ℂ) 0 (W.smul u (ℓ + i) v) (p.1 x)

variable {a p g}

theorem TwistData.mem (hD : TwistData a p g) (n : ℂ) (k : ℕ) (v : V) {y : X}
    (hy : y ∈ Sp p) : (actY hC2 a).1 n k v y ∈ Sp p := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨_, hD.stab n k v x⟩

/-- The integral log-free mode `v_{(j)}` restricted to `range p`. -/
def endo (hD : TwistData a p g) (v : V) (j : ℤ) : Module.End ℂ (Sp p) :=
  ((actY hC2 a).1 (j : ℂ) 0 v).restrict (fun _ hy => hD.mem (j : ℂ) 0 v hy)

theorem endo_coe (hD : TwistData a p g) (v : V) (j : ℤ) (y : Sp p) :
    ((endo hD v j y : Sp p) : X) = (actY hC2 a).1 (j : ℂ) 0 v y := rfl

/-- The fields of the weak module. -/
def twistedFields (hD : TwistData a p g) :
    (orbifold (Subgroup.zpowers g)).carrier →ₗ[ℂ] FormalDist (Module.End ℂ (Sp p)) where
  toFun v m := endo hD (v : V) (-m - 1)
  map_add' v w := by
    funext m
    refine LinearMap.ext fun y => Subtype.ext ?_
    change (actY hC2 a).1 _ 0 ((v : V) + (w : V)) y =
      (actY hC2 a).1 _ 0 (v : V) y + (actY hC2 a).1 _ 0 (w : V) y
    exact LinearMap.congr_fun (map_add ((actY hC2 a).1 _ 0) (v : V) (w : V)) _
  map_smul' c v := by
    funext m
    refine LinearMap.ext fun y => Subtype.ext ?_
    change (actY hC2 a).1 _ 0 (c • (v : V)) y = c • (actY hC2 a).1 _ 0 (v : V) y
    exact LinearMap.congr_fun (map_smul ((actY hC2 a).1 _ 0) c (v : V)) _

theorem mode_twistedFields (hD : TwistData a p g) (v : (orbifold (Subgroup.zpowers g)).carrier)
    (j : ℤ) (y : Sp p) :
    ((mode (twistedFields hD v) j y : Sp p) : X) = (actY hC2 a).1 (j : ℂ) 0 (v : V) y := by
  change (actY hC2 a).1 (((-(-j - 1) - 1 : ℤ)) : ℂ) 0 (v : V) y = _
  rw [show (-(-j - 1) - 1 : ℤ) = j by ring]

theorem fixed_of_mem {v : V} (hv : v ∈ (orbifold (Subgroup.zpowers g)).carrier) : g v = v :=
  (mem_orbifold_zpowers_iff g v).mp hv

/-- **The weak `V^{⟨g⟩}`-module structure on `range p`** (given the bridge). -/
def twistedWeakModule (hD : TwistData a p g) :
    WeakModule (orbifoldVOA (Subgroup.zpowers g)) (Sp p) where
  YM := twistedFields hD
  vacuum_YM := by
    funext m
    refine LinearMap.ext fun y => Subtype.ext ?_
    have hvac : (W.vacuum) ∈ (orbifold G).carrier := (orbifold G).vacuum_mem
    change (actY hC2 a).1 (((-m - 1 : ℤ)) : ℂ) 0 W.vacuum y = _
    rw [hD.unit ⟨W.vacuum, hvac⟩ (-m - 1) y]
    have h1 : X.act.YM ⟨W.vacuum, hvac⟩ = 1 := X.act.vacuum_YM
    have h2 : mode (1 : FormalDist (Module.End ℂ X)) (-m - 1) = if m = 0 then 1 else 0 := by
      unfold mode
      rw [FormalDist.one_apply, show (-(-m - 1) - 1 : ℤ) = m by ring]
    rw [h1, h2, FormalDist.one_apply]
    split_ifs <;> rfl
  truncation v y := by
    obtain ⟨N, hN⟩ := (actY hC2 a).2.truncation (v : V) (y : X) 0
    refine ⟨N, fun n hn => Subtype.ext ?_⟩
    rw [mode_twistedFields]
    have := hN n hn 0
    rwa [zero_add] at this
  jacobi v w y ℓ m n := by
    obtain ⟨x, hx⟩ := y.2
    have hJ := hD.jacobi (v : V) (w : V) (fixed_of_mem v.2) (fixed_of_mem w.2) x ℓ m n
    apply Subtype.val_injective
    change (Sp p).subtype _ = (Sp p).subtype _
    rw [LatMod.map_finsum_of_injective (Sp p).subtype Subtype.val_injective,
      LatMod.map_finsum_of_injective (Sp p).subtype Subtype.val_injective]
    have hy : (y : X) = p.1 x := hx.symm
    convert hJ using 2
    · funext i
      simp only [Submodule.subtype_apply, Submodule.coe_smul, Submodule.coe_sub,
        mode_twistedFields, hy]
    · funext i
      simp only [Submodule.subtype_apply, Submodule.coe_smul, mode_twistedFields, hy]
      push_cast
      rfl

theorem twistedWeakModule_mode (hD : TwistData a p g)
    (v : (orbifold (Subgroup.zpowers g)).carrier) (j : ℤ) (y : Sp p) :
    ((mode ((twistedWeakModule hD).YM v) j y : Sp p) : X) = (actY hC2 a).1 (j : ℂ) 0 (v : V) y :=
  mode_twistedFields hD v j y

/-! ## Admissibility -/

theorem twisted_L0_coe (hD : TwistData a p g) (y : Sp p) :
    ((LogTensor.L0 (twistedWeakModule hD) y : Sp p) : X) = X.act.L0op (y : X) := by
  change ((mode ((twistedWeakModule hD).YM
      ⟨W.conformalVector, (orbifold (Subgroup.zpowers g)).conformal_mem⟩) 1 y : Sp p) : X) = _
  rw [twistedWeakModule_mode]
  exact hD.unit ⟨W.conformalVector, (orbifold G).conformal_mem⟩ 1 y

theorem twisted_L0_pow_coe (hD : TwistData a p g) (α : ℂ) (k : ℕ) (y : Sp p) :
    ((((LogTensor.L0 (twistedWeakModule hD) - α • 1) ^ k) y : Sp p) : X) =
      ((X.act.L0op - α • 1) ^ k) (y : X) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    congr 1
    change ((LogTensor.L0 (twistedWeakModule hD) y - α • y : Sp p) : X) = _
    rw [Submodule.coe_sub, Submodule.coe_smul, twisted_L0_coe]
    rfl

theorem hom_L0_pow {Y Z : LogModuleCat (orbifoldVOA G)} (q : Y ⟶ Z) (α : ℂ) (k : ℕ) (x : Y) :
    q.1 (((Y.act.L0op - α • 1) ^ k) x) = ((Z.act.L0op - α • 1) ^ k) (q.1 x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    congr 1
    change q.1 (mode (Y.act.YM (orbifoldVOA G).conformalVector) 1 x - α • x) =
      mode (Z.act.YM (orbifoldVOA G).conformalVector) 1 (q.1 x) - α • q.1 x
    rw [map_sub, map_smul, q.2]

/-- **The twisted summand is an admissible `V^{⟨g⟩}`-module.** -/
theorem twisted_admissible (hD : TwistData a p g) :
    ∃ N : AdmissibleModule (orbifoldVOA (Subgroup.zpowers g)) (Sp p),
      N.toWeakModule = twistedWeakModule hD := by
  obtain ⟨B, hB⟩ := X.act.boundedBelow
  refine ABDWeakAdmissible.exists_admissible_of_spectral_bound _ ?_ B ?_
  · -- the generalized eigenspaces span
    set T := ⨆ α : ℂ, (LogTensor.L0 (twistedWeakModule hD)).maxGenEigenspace α
    have hx : ∀ x : X, (⟨p.1 x, x, rfl⟩ : Sp p) ∈ T := by
      intro x
      have hxtop : x ∈ ⨆ α, X.act.weight α := by
        rw [X.act.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
      refine Submodule.iSup_induction _ (motive := fun x => (⟨p.1 x, x, rfl⟩ : Sp p) ∈ T) hxtop
        ?_ ?_ ?_
      · intro α x hxα
        obtain ⟨k, hk⟩ := X.act.L0op_locNilpotent hxα
        refine Submodule.mem_iSup_of_mem α ?_
        rw [Module.End.mem_maxGenEigenspace]
        refine ⟨k, Subtype.ext ?_⟩
        rw [twisted_L0_pow_coe]
        change ((X.act.L0op - α • 1) ^ k) (p.1 x) = 0
        rw [← hom_L0_pow, hk, map_zero]
      · have : (⟨p.1 0, 0, rfl⟩ : Sp p) = 0 := Subtype.ext (map_zero p.1)
        simp only
        rw [this]; exact T.zero_mem
      · intro x y hx hy
        have : (⟨p.1 (x + y), x + y, rfl⟩ : Sp p) = ⟨p.1 x, x, rfl⟩ + ⟨p.1 y, y, rfl⟩ :=
          Subtype.ext (map_add p.1 x y)
        rw [this]; exact T.add_mem hx hy
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨x, hxy⟩ := y.2
    have : y = ⟨p.1 x, x, rfl⟩ := Subtype.ext hxy.symm
    rw [this]; exact hx x
  · -- bounded below
    intro α hα
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hy
    have hkX : ((X.act.L0op - α • 1) ^ k) (y : X) = 0 :=
      (twisted_L0_pow_coe hD α k y).symm.trans (congrArg Subtype.val hk)
    have hmem : (y : X) ∈ X.act.weight α :=
      X.act.maxGenEigenspace_le_weight α ((Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨k, hkX⟩)
    refine hB α fun hbot => hy0 (Subtype.ext ?_)
    rw [hbot] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem

end Construction

/-! ## Splitting surjections between twisted summands -/

section Split
variable {G : Subgroup (Aut W)} {hfg : FinGen (orbifold G).adjointRestrict}
  {hC2 : C2Cofinite (orbifoldVOA G)} {X₁ X₂ : LogModuleCat (orbifoldVOA G)}
  {a₁ : tensorObject hC2 (vObj G hfg) X₁ ⟶ X₁} {a₂ : tensorObject hC2 (vObj G hfg) X₂ ⟶ X₂}
  {p₁ : X₁ ⟶ X₁} {p₂ : X₂ ⟶ X₂} {g : Aut W}

/-- **O5 (d), mode-level form.** Given the twist data on both sides, a rational `V^{⟨g⟩}`,
and a surjective map `f` of action operators commuting with the projections, there is a
`C`-morphism `s` with `s ≫ f = p₂`, `p₂ ≫ s = s` and `s ≫ p₁ = s`. -/
theorem exists_section_of_twistData (hD₁ : TwistData a₁ p₁ g)
    (hrat : AdmissiblyRational (orbifoldVOA (Subgroup.zpowers g)))
    (hfix : ∀ u ∈ (orbifold G).carrier, g u = u) (f : X₁ ⟶ X₂)
    (hf : ∀ (n : ℂ) (k : ℕ) (v : V) (x : X₁),
      f.1 ((actY hC2 a₁).1 n k v x) = (actY hC2 a₂).1 n k v (f.1 x))
    (hfs : Function.Surjective f.1) (hnat : ∀ x, f.1 (p₁.1 x) = p₂.1 (f.1 x))
    (hp₁ : ∀ x, p₁.1 (p₁.1 x) = p₁.1 x) (hp₂ : ∀ x, p₂.1 (p₂.1 x) = p₂.1 x) :
    ∃ s : X₂ ⟶ X₁, s ≫ f = p₂ ∧ p₂ ≫ s = s ∧ s ≫ p₁ = s := by
  classical
  obtain ⟨N, hN⟩ := twisted_admissible hD₁
  let B := twistedWeakModule hD₁
  let fS : Sp p₁ →ₗ[ℂ] X₂ := f.1 ∘ₗ (Sp p₁).subtype
  have hBmode : ∀ (v : (orbifold (Subgroup.zpowers g)).carrier) (j : ℤ) (y : Sp p₁),
      ((mode (N.toWeakModule.YM v) j y : Sp p₁) : X₁) = (actY hC2 a₁).1 (j : ℂ) 0 (v : V) y := by
    intro v j y
    rw [hN]
    exact twistedWeakModule_mode hD₁ v j y
  let K : WeakModule.Submodule' N.toWeakModule :=
    ⟨LinearMap.ker fS, fun v n y hy => by
      rw [LinearMap.mem_ker] at hy ⊢
      change f.1 ((mode (N.toWeakModule.YM v) n y : Sp p₁) : X₁) = 0
      rw [hBmode, hf]
      change f.1 (y : X₁) = 0 at hy
      rw [hy, map_zero]⟩
  obtain ⟨Q, hQ⟩ := hrat N K
  have memS₂ : ∀ y : Sp p₁, fS y ∈ Sp p₂ := by
    rintro ⟨_, x, rfl⟩
    exact ⟨f.1 x, (hnat x).symm⟩
  let fQ : Q.carrier →ₗ[ℂ] Sp p₂ := (fS.codRestrict (Sp p₂) memS₂) ∘ₗ Q.carrier.subtype
  have hfQ : ∀ q : Q.carrier, ((fQ q : Sp p₂) : X₂) = f.1 ((q : Sp p₁) : X₁) := fun _ => rfl
  have inj : Function.Injective fQ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    have hqK : (q : Sp p₁) ∈ K.carrier := by
      change fS q = 0
      have := congrArg Subtype.val hq
      exact this
    have := (Submodule.disjoint_def.mp hQ.disjoint) (q : Sp p₁) hqK q.2
    exact Subtype.ext this
  have surj : Function.Surjective fQ := by
    rintro ⟨_, w, rfl⟩
    obtain ⟨x, rfl⟩ := hfs w
    have hmem : (⟨p₁.1 x, x, rfl⟩ : Sp p₁) ∈ K.carrier ⊔ Q.carrier := by
      rw [hQ.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨k, hk, q, hq, hkq⟩ := Submodule.mem_sup.mp hmem
    refine ⟨⟨q, hq⟩, Subtype.ext ?_⟩
    rw [hfQ]
    have hk0 : f.1 ((k : Sp p₁) : X₁) = 0 := hk
    have := congrArg (fun z : Sp p₁ => f.1 (z : X₁)) hkq
    simp only [Submodule.coe_add, map_add, hk0, zero_add] at this
    rw [this]
    exact hnat x
  let e : Q.carrier ≃ₗ[ℂ] Sp p₂ := LinearEquiv.ofBijective fQ ⟨inj, surj⟩
  have he : ∀ q, e q = fQ q := fun _ => rfl
  let sL : X₂ →ₗ[ℂ] X₁ :=
    (Sp p₁).subtype ∘ₗ Q.carrier.subtype ∘ₗ e.symm.toLinearMap ∘ₗ p₂.1.rangeRestrict
  have hsL : ∀ y, sL y = ((e.symm (p₂.1.rangeRestrict y) : Sp p₁) : X₁) := fun _ => rfl
  have hspec : ∀ y, f.1 (sL y) = p₂.1 y := by
    intro y
    rw [hsL, ← hfQ, ← he, LinearEquiv.apply_symm_apply]
    rfl
  have hact : ∀ (u : (orbifold G).carrier) (n : ℤ) (y : X₂),
      sL (mode (X₂.act.YM u) n y) = mode (X₁.act.YM u) n (sL y) := by
    intro u n y
    let ub : (orbifold (Subgroup.zpowers g)).carrier :=
      ⟨(u : V), (mem_orbifold_zpowers_iff g _).mpr (hfix _ u.2)⟩
    set q := e.symm (p₂.1.rangeRestrict y) with hq
    have hq'Q : mode (N.toWeakModule.YM ub) n (q : Sp p₁) ∈ Q.carrier := Q.act_mem ub n q.2
    have hq'coe : ((mode (N.toWeakModule.YM ub) n (q : Sp p₁) : Sp p₁) : X₁) =
        mode (X₁.act.YM u) n ((q : Sp p₁) : X₁) := by
      rw [hBmode]
      exact hD₁.unit u n _
    have hkey : e.symm (p₂.1.rangeRestrict (mode (X₂.act.YM u) n y)) =
        ⟨mode (N.toWeakModule.YM ub) n (q : Sp p₁), hq'Q⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [he, hfQ]
      change p₂.1 (mode (X₂.act.YM u) n y) = f.1 ((mode (N.toWeakModule.YM ub) n (q : Sp p₁) :
        Sp p₁) : X₁)
      rw [hq'coe, f.2, p₂.2]
      congr 1
      have := hspec y
      rw [hsL] at this
      exact this.symm
    rw [hsL, hkey]
    exact hq'coe
  let s : X₂ ⟶ X₁ := ⟨sL, hact⟩
  refine ⟨s, ?_, ?_, ?_⟩
  · apply hom_ext
    intro y
    exact hspec y
  · apply hom_ext
    intro y
    change sL (p₂.1 y) = sL y
    have h2 : p₂.1.rangeRestrict (p₂.1 y) = p₂.1.rangeRestrict y := Subtype.ext (hp₂ y)
    rw [hsL, hsL, h2]
  · apply hom_ext
    intro y
    change p₁.1 (sL y) = sL y
    obtain ⟨x, hx⟩ := (e.symm (p₂.1.rangeRestrict y) : Sp p₁).2
    rw [hsL, ← hx, hp₁]

end Split

end VOA.Classification.COne.McRaeO5
