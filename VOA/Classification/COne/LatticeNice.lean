/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.LatticeStronglyRational
import VOA.Classification.COne.Statement
import VOA.Modules.RationalityLattice

/-!
# `V_{2m}` is nice

For `L = √(2m)ℤ` (`m ≥ 1`):

* `existsUnique_latticeModule_equiv` — **classification of irreducibles** (Dong 1993): every
  irreducible ordinary `V_{2m}`-module `N` (carrier in `Type`) is isomorphic to
  `latticeModule m hm j` for exactly one `j ∈ {0, …, 2m-1}`.  Variants:
  `exists_latticeModule_equiv_int`, `exists_latticeModule_equiv_abs` (representative `|j| ≤ m`).
* `V2m_pseudoUnitary`, `V2m_centralCharge` (`c = 1`), `V2m_nice`.
* `nice_of_hasCOneLabel_lat` — the lattice clause of GR Prop. 3.2:
  `HasCOneLabel V (.lat m) → Nice V ∧ V.centralCharge = 1`, for `V` on a carrier in `Type`, via
  the transport lemmas `stronglyRational_of_iso`, `pseudoUnitary_of_iso`,
  `centralCharge_eq_of_iso` (and `isSimple_of_iso`, `selfDual_of_iso`, `c2Cofinite_of_iso`,
  `admissiblyRational_of_iso`), valid along any `VOAIsomorphic` between carriers in one universe.

## Route for the classification
`N` is admissible (`OrdVModule.toAdmissible`), so `LatticeRational2` applies: `N` has a nonzero
vacuum `h(0)`-eigenvector `w` of charge index `j` (`exists_vacEig`, from `vac_le_eigSpan`), and by
irreducibility its charge orbit `(w_k)_{k∈ℤ}` is a basis of the vacuum space `Ω_N`
(`vacBasis`: `orbitSpan_eq_top` + `vac_mem_span_wseq` + distinct `h(0)`-eigenvalues).  The same
holds in `V_{L+λ_j}` for `w = e^{λ_j}` (`latticeModule_vacEig`).  The comparison map
`orbitEquiv : M(1) ⊗ Ω ≅ M(1) ⊗ Ω'`, `p(h)·w_k ↦ p(h)·w'_k`, is a linear equivalence intertwining
the `h`-creation modes (`orbitEquiv_cr`).  It intertwines all modes of `e^{±α}`
(`orbitEquiv_charge`): on each `w_k` the top mode is `raiseOp`/`lowerOp`, with the same universal
constants on both sides (`raise_wseq'`, `lower_wseq'`), and the lower modes are forced by the
charge recursion (`charge_intertw_vac`); then the commutator `[h(n), e^β_(q)]` propagates through
`M(1) ⊗ Ω` (`eq_top_of_vac_le`).  Finally `moduleEquivOfPmCharge` upgrades this to a module
isomorphism (`e^{±α}` generate `V_L`).  The range `0 ≤ j < 2m` and uniqueness come from
`latticeModule_iso_iff`.

## Pseudo-unitarity
For `|j| ≤ m`, every weight of `V_{L+λ_j}` is real and `≥ j²/4m` (`latticeModule_lowestWeight`);
weights transfer along isomorphisms (`moduleEquiv_weight_ne_bot`).  `j = 0` is excluded since
`V_{L+λ_0} ≅ V_{2m}` (`latticeModuleZeroEquiv`).

## Status
No `sorry`, no new axioms.  Unconditional: the only hypothesis is `1 ≤ m` (and, for
`nice_of_hasCOneLabel_lat`, the label).  Not imported by the umbrella.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet HeisenbergN MvPolynomial LatMod
open Module (End)

section Explicit

variable {m : ℕ} {hm : 1 ≤ m} {M : Type*} [AddCommGroup M] [Module ℂ M]
  {N : AdmissibleModule (V2m m hm) M}

variable (m) in
/-- The raising constant along a charge orbit. -/
noncomputable def raiseC (k : ℤ) : ℂ := if 0 ≤ k then 1 else latticeCocycle (latP m) (1 : ℤ) (-1 : ℤ)

variable (m) in
/-- The lowering constant along a charge orbit. -/
noncomputable def lowerC (k : ℤ) : ℂ := if k ≤ 0 then 1 else latticeCocycle (latP m) (-1 : ℤ) (1 : ℤ)

/-- `raise_wseq` with its (universal) constant made explicit. -/
theorem raise_wseq' {j : ℤ} {w : M} (hw : VacEig N j w) (k : ℤ) :
    raiseOp N (j + 2 * m * k) (wseq N j w k) = raiseC m k • wseq N j w (k + 1) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [raiseC, if_pos (by positivity), one_smul, wseq_natCast,
      show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, wseq_natCast]
    rfl
  · rcases n with _ | n
    · rw [raiseC, if_pos (by simp), one_smul]
      simp only [Nat.cast_zero, neg_zero, zero_add]
      rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, wseq_natCast]
      rfl
    · rw [raiseC, if_neg (by push_cast; omega), wseq_neg_natCast,
        show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by push_cast; ring, wseq_neg_natCast]
      have hd := downSeq_spec hw n
      obtain ⟨-, -, -, h4⟩ := vac_lower N (j - 2 * m * n) _ hd.1 hd.2
      rw [← h4]
      change raiseOp N _ (lowerOp N (j - 2 * m * n) (downSeq N j w n)) = _
      rw [raiseOp, lowerOp]
      congr 2
      push_cast; ring

/-- `lower_wseq` with its (universal) constant made explicit. -/
theorem lower_wseq' {j : ℤ} {w : M} (hw : VacEig N j w) (k : ℤ) :
    lowerOp N (j + 2 * m * k) (wseq N j w k) = lowerC m k • wseq N j w (k - 1) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rcases n with _ | n
    · rw [lowerC, if_pos (by simp), one_smul]
      simp only [Nat.cast_zero, zero_sub]
      rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) from rfl, wseq_neg_natCast]
      change lowerOp N (j + 2 * m * 0) w = lowerOp N (j - 2 * m * 0) w
      simp
    · rw [lowerC, if_neg (by push_cast; omega), wseq_natCast,
        show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by push_cast; ring, wseq_natCast]
      have hu := upSeq_spec hw n
      obtain ⟨-, -, -, h4⟩ := vac_raise N (j + 2 * m * n) _ hu.1 hu.2
      rw [← h4]
      change lowerOp N _ (raiseOp N (j + 2 * m * n) (upSeq N j w n)) = _
      rw [lowerOp, raiseOp]
      congr 2
      push_cast; ring
  · rw [lowerC, if_pos (by omega), one_smul, wseq_neg_natCast,
      show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by push_cast; ring, wseq_neg_natCast]
    change lowerOp N _ _ = lowerOp N (j - 2 * m * n) (downSeq N j w n)
    congr 2
    ring

end Explicit

/-! ## The vacuum space of an irreducible module: a basis indexed by the charge orbit -/

section VacBasis

variable {m : ℕ} {hm : 1 ≤ m} {M : Type*} [AddCommGroup M] [Module ℂ M]
  {N : AdmissibleModule (V2m m hm) M}

/-- The zero weak submodule. -/
def botSub (A : WeakModule (V2m m hm) M) : WeakModule.Submodule' A where
  carrier := ⊥
  act_mem u n x hx := by
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, WeakModule.act_def, map_zero]

theorem wseq_ne_zero {j : ℤ} {w : M} (hw : VacEig N j w) (hw0 : w ≠ 0) (k : ℤ) :
    wseq N j w k ≠ 0 := by
  intro h
  have := (wseq_mem_iff hw (botSub N.toWeakModule) k).mp (by
    change wseq N j w k ∈ (⊥ : Submodule ℂ M); rw [h]; exact Submodule.zero_mem _)
  exact hw0 ((Submodule.mem_bot ℂ).mp this)

theorem wseq_linearIndependent {j : ℤ} {w : M} (hw : VacEig N j w) (hw0 : w ≠ 0) :
    LinearIndependent ℂ (wseq N j w) := by
  have hc1 : chargeCoord (latP m) (1 : ℤ) (a0 m) ≠ 0 := chargeCoord_one_ne_zero m hm
  set μ : ℤ → ℂ := fun k => ((j + 2 * m * k : ℤ) : ℂ) / chargeCoord (latP m) (1 : ℤ) (a0 m)
  have hμ : Function.Injective μ := by
    intro a b hab
    simp only [μ] at hab
    rw [div_left_inj' hc1] at hab
    have := Int.cast_injective hab
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    nlinarith
  refine Module.End.eigenvectors_linearIndependent' ((admissibleHeisRep N).a 0) μ hμ _
    fun k => ?_
  refine Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr ?_,
    wseq_ne_zero hw hw0 k⟩
  exact (wseq_spec hw k).2

theorem orbitSpan_eq_top {j : ℤ} {w : M} (hw : VacEig N j w) (hw0 : w ≠ 0)
    (hirr : ∀ P : WeakModule.Submodule' N.toWeakModule, P.carrier = ⊥ ∨ P.carrier = ⊤) :
    orbitSpan N j w = ⊤ := by
  rcases hirr (orbitSub N hw) with h | h
  · exact absurd ((Submodule.mem_bot ℂ).mp (h ▸ mem_orbitSub hw)) hw0
  · exact h

theorem vac_le_span_wseq {j : ℤ} {w : M} (hw : VacEig N j w) (hw0 : w ≠ 0)
    (hirr : ∀ P : WeakModule.Submodule' N.toWeakModule, P.carrier = ⊥ ∨ P.carrier = ⊤) :
    (admissibleHeisRep N).vac ≤ Submodule.span ℂ (Set.range (wseq N j w)) := fun v hv =>
  vac_mem_span_wseq hw hv (by rw [orbitSpan_eq_top hw hw0 hirr]; trivial)

/-- The orbit vectors as elements of the vacuum space. -/
noncomputable def wvac {j : ℤ} {w : M} (hw : VacEig N j w) (k : ℤ) : (admissibleHeisRep N).vac :=
  ⟨wseq N j w k, (wseq_spec hw k).1⟩

/-- **The vacuum space of an irreducible module has basis `(w_k)_{k ∈ ℤ}`.** -/
noncomputable def vacBasis {j : ℤ} {w : M} (hw : VacEig N j w) (hw0 : w ≠ 0)
    (hirr : ∀ P : WeakModule.Submodule' N.toWeakModule, P.carrier = ⊥ ∨ P.carrier = ⊤) :
    Module.Basis ℤ ℂ (admissibleHeisRep N).vac :=
  Module.Basis.mk (v := wvac hw)
    (LinearIndependent.of_comp (admissibleHeisRep N).vac.subtype
      (wseq_linearIndependent hw hw0))
    (by
      intro x _
      have hx := vac_le_span_wseq hw hw0 hirr x.2
      have hrange : Set.range (wseq N j w) = (admissibleHeisRep N).vac.subtype '' Set.range (wvac hw) := by
        rw [← Set.range_comp]; rfl
      rw [hrange, Submodule.span_image] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := Subtype.ext hyx
      rwa [← this])

theorem vacBasis_apply {j : ℤ} {w : M} (hw : VacEig N j w) (hw0 : w ≠ 0)
    (hirr : ∀ P : WeakModule.Submodule' N.toWeakModule, P.carrier = ⊥ ∨ P.carrier = ⊤) (k : ℤ) :
    vacBasis hw hw0 hirr k = wvac hw k := by
  simp [vacBasis]

end VacBasis

/-! ## The comparison map between two irreducible modules with the same vacuum eigenvalue -/

section OrbitEquiv

variable {m : ℕ} {hm : 1 ≤ m} {M M' : Type*} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup M'] [Module ℂ M']
  {N : AdmissibleModule (V2m m hm) M} {N' : AdmissibleModule (V2m m hm) M'}
  {j : ℤ} {w : M} {w' : M'} (hw : VacEig N j w) (hw0 : w ≠ 0) (hw' : VacEig N' j w')
  (hw0' : w' ≠ 0)
  (hirr : ∀ P : WeakModule.Submodule' N.toWeakModule, P.carrier = ⊥ ∨ P.carrier = ⊤)
  (hirr' : ∀ P : WeakModule.Submodule' N'.toWeakModule, P.carrier = ⊥ ∨ P.carrier = ⊤)

/-- The comparison map `M ≅ M(1) ⊗ Ω ≅ M(1) ⊗ Ω' ≅ M'`, `p(h)·w_k ↦ p(h)·w'_k`. -/
noncomputable def orbitEquiv : M ≃ₗ[ℂ] M' :=
  (admissibleHeisRep N).fockEquiv.symm.trans
    ((Finsupp.mapRange.linearEquiv
        ((vacBasis hw hw0 hirr).equiv (vacBasis hw' hw0' hirr') (Equiv.refl ℤ))).trans
      (admissibleHeisRep N').fockEquiv)

theorem orbitEquiv_wseq (k : ℤ) :
    orbitEquiv hw hw0 hw' hw0' hirr hirr' (wseq N j w k) = wseq N' j w' k := by
  have h1 : wseq N j w k = ((wvac hw k : (admissibleHeisRep N).vac) : M) := rfl
  have h2 : wseq N' j w' k = ((wvac hw' k : (admissibleHeisRep N').vac) : M') := rfl
  rw [orbitEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1,
    (admissibleHeisRep N).fockEquiv_symm_vac, Finsupp.mapRange.linearEquiv_apply,
    Finsupp.mapRange_single, ← vacBasis_apply hw hw0 hirr, Module.Basis.equiv_apply,
    Equiv.refl_apply, vacBasis_apply, HeisSvN.HeisRep.fockEquiv_apply,
    HeisSvN.HeisRep.fockMap_single_zero, h2]

theorem mapRange_mapDomain_comm {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (φ : A →+ B) (g : (ℕ →₀ ℕ) → (ℕ →₀ ℕ)) (f : (ℕ →₀ ℕ) →₀ A) :
    Finsupp.mapRange φ φ.map_zero (Finsupp.mapDomain g f)
      = Finsupp.mapDomain g (Finsupp.mapRange φ φ.map_zero f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g' hf hg =>
    rw [Finsupp.mapDomain_add, Finsupp.mapRange_add φ.map_add, Finsupp.mapRange_add φ.map_add,
      Finsupp.mapDomain_add, hf, hg]
  | single s a => simp [Finsupp.mapDomain_single, Finsupp.mapRange_single]

theorem orbitEquiv_cr (i : ℕ) (x : M) :
    orbitEquiv hw hw0 hw' hw0' hirr hirr' ((admissibleHeisRep N).cr i x)
      = (admissibleHeisRep N').cr i (orbitEquiv hw hw0 hw' hw0' hirr hirr' x) := by
  set φ := (vacBasis hw hw0 hirr).equiv (vacBasis hw' hw0' hirr') (Equiv.refl ℤ)
  have he : ∀ f, orbitEquiv hw hw0 hw' hw0' hirr hirr' ((admissibleHeisRep N).fockMap f)
      = (admissibleHeisRep N').fockMap (Finsupp.mapRange.linearEquiv φ f) := by
    intro f
    rw [orbitEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      ← HeisSvN.HeisRep.fockEquiv_apply, LinearEquiv.symm_apply_apply,
      HeisSvN.HeisRep.fockEquiv_apply]
  obtain ⟨f, rfl⟩ := (admissibleHeisRep N).fockMap_surjective x
  rw [HeisSvN.HeisRep.cr_fockMap, he, he, HeisSvN.HeisRep.cr_fockMap]
  congr 1
  exact mapRange_mapDomain_comm φ.toLinearMap.toAddMonoidHom _ f

theorem orbitEquiv_hneg {n : ℤ} (hn : n < 0) (x : M) :
    orbitEquiv hw hw0 hw' hw0' hirr hirr' (mode (N.YM (hb m)) n x)
      = mode (N'.YM (hb m)) n (orbitEquiv hw hw0 hw' hw0' hirr hirr' x) := by
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = -((i : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
  exact orbitEquiv_cr hw hw0 hw' hw0' hirr hirr' i x

end OrbitEquiv

/-! ## Uniqueness of the charge modes on a vacuum vector -/

section ChargeIntertw

variable {m : ℕ} {hm : 1 ≤ m} {M M' : Type*} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup M'] [Module ℂ M']

/-- **The charge modes on a vacuum eigenvector are determined by the top one.**  If an injective
linear map `e` intertwines the creation modes of `h`, sends the vacuum eigenvector `ω` to a vacuum
eigenvector with the same eigenvalue, and intertwines the top mode `e^β_(N₁-1)` on `ω`, then it
intertwines every `e^β_(n)` on `ω` (downward induction with `charge_recursion` on both sides). -/
theorem charge_intertw_vac (A : WeakModule (V2m m hm) M) (B : WeakModule (V2m m hm) M')
    (e : M →ₗ[ℂ] M') (he : Function.Injective e)
    (hcr : ∀ n : ℤ, n < 0 → ∀ y, e (mode (A.YM (hb m)) n y) = mode (B.YM (hb m)) n (e y))
    (β : ℤ) (ω : M) (hω : ∀ i : ℤ, 0 < i → mode (A.YM (hb m)) i ω = 0)
    (hω' : ∀ i : ℤ, 0 < i → mode (B.YM (hb m)) i (e ω) = 0)
    (lam : ℂ) (hlam : mode (A.YM (hb m)) 0 ω = lam • ω)
    (hlam' : mode (B.YM (hb m)) 0 (e ω) = lam • e ω)
    (N₁ : ℤ) (hN : chargeCoord (latP m) β (a0 m) * lam = -N₁)
    (htop : e (mode (A.YM (latChargeGen (latP m) β)) (N₁ - 1) ω)
      = mode (B.YM (latChargeGen (latP m) β)) (N₁ - 1) (e ω)) :
    ∀ n : ℤ, e (mode (A.YM (latChargeGen (latP m) β)) n ω)
      = mode (B.YM (latChargeGen (latP m) β)) n (e ω) := by
  have hv := charge_vanish A β ω hω lam hlam N₁ hN
  have hv' := charge_vanish B β (e ω) hω' lam hlam' N₁ hN
  have key : ∀ d : ℕ, e (mode (A.YM (latChargeGen (latP m) β)) (N₁ - 1 - d) ω)
      = mode (B.YM (latChargeGen (latP m) β)) (N₁ - 1 - d) (e ω) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
    rcases d with _ | d
    · simpa using htop
    · have hrec := charge_recursion A β ω hω lam hlam (N₁ - 1 - d)
      have hrec' := charge_recursion B β (e ω) hω' lam hlam' (N₁ - 1 - d)
      rw [hN, show N₁ - 1 - (d : ℤ) - 1 = N₁ - 1 - ((d + 1 : ℕ) : ℤ) by push_cast; ring] at hrec hrec'
      have hcoef : (-((N₁ - 1 - d : ℤ) : ℂ) - -(N₁ : ℂ)) = ((d + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [hcoef] at hrec hrec'
      have hne : ((d + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
      have h1 := congrArg e hrec
      rw [map_smul, map_smul, map_finsum_of_injective e he] at h1
      have hsum : (∑ᶠ i : ℤ, e (if 0 ≤ i then mode (A.YM (hb m)) (-1 - i)
            (mode (A.YM (latChargeGen (latP m) β)) (N₁ - 1 - d + i) ω) else 0))
          = ∑ᶠ i : ℤ, (if 0 ≤ i then mode (B.YM (hb m)) (-1 - i)
            (mode (B.YM (latChargeGen (latP m) β)) (N₁ - 1 - d + i) (e ω)) else 0) := by
        refine finsum_congr fun i => ?_
        split_ifs with hi
        · rw [hcr _ (by omega)]
          congr 1
          by_cases hid : i ≤ d
          · have := IH (d - i.toNat) (by omega)
            rwa [show N₁ - 1 - ((d - i.toNat : ℕ) : ℤ) = N₁ - 1 - d + i by omega] at this
          · rw [hv _ (by omega), hv' _ (by omega), map_zero]
        · exact map_zero e
      rw [hsum, ← hrec'] at h1
      exact smul_right_injective _ hne h1
  intro n
  by_cases hn : N₁ ≤ n
  · rw [hv n hn, hv' n hn, map_zero]
  · have := key (N₁ - 1 - n).toNat
    rwa [show N₁ - 1 - ((N₁ - 1 - n).toNat : ℤ) = n by omega] at this

end ChargeIntertw

/-! ## The comparison map intertwines `e^{±α}` -/

section OrbitEquivCharge

variable {m : ℕ} {hm : 1 ≤ m} {M M' : Type*} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup M'] [Module ℂ M']
  {N : AdmissibleModule (V2m m hm) M} {N' : AdmissibleModule (V2m m hm) M'}
  {j : ℤ} {w : M} {w' : M'} (hw : VacEig N j w) (hw0 : w ≠ 0) (hw' : VacEig N' j w')
  (hw0' : w' ≠ 0)
  (hirr : ∀ P : WeakModule.Submodule' N.toWeakModule, P.carrier = ⊥ ∨ P.carrier = ⊤)
  (hirr' : ∀ P : WeakModule.Submodule' N'.toWeakModule, P.carrier = ⊥ ∨ P.carrier = ⊤)

/-- On each orbit vector, the comparison map intertwines all modes of `e^{±α}`. -/
theorem orbitEquiv_charge_wseq (β : ℤ) (hβ : β = 1 ∨ β = -1) (k : ℤ) (t : ℤ) :
    orbitEquiv hw hw0 hw' hw0' hirr hirr' (mode (N.YM (latChargeGen (latP m) β)) t (wseq N j w k))
      = mode (N'.YM (latChargeGen (latP m) β)) t
          (orbitEquiv hw hw0 hw' hw0' hirr hirr' (wseq N j w k)) := by
  set e := orbitEquiv hw hw0 hw' hw0' hirr hirr'
  have hc1 : chargeCoord (latP m) (1 : ℤ) (a0 m) ≠ 0 := chargeCoord_one_ne_zero m hm
  have hcn : chargeCoord (latP m) (-1 : ℤ) (a0 m) = -chargeCoord (latP m) (1 : ℤ) (a0 m) :=
    chargeCoord_neg (latP m) (1 : ℤ) (a0 m)
  have hs := wseq_spec hw k
  have hs' := wseq_spec hw' k
  have hek : e (wseq N j w k) = wseq N' j w' k := orbitEquiv_wseq hw hw0 hw' hw0' hirr hirr' k
  set J : ℤ := j + 2 * m * k with hJ
  have hcr : ∀ n : ℤ, n < 0 → ∀ y, e (mode (N.YM (hb m)) n y) = mode (N'.YM (hb m)) n (e y) :=
    fun n hn y => orbitEquiv_hneg hw hw0 hw' hw0' hirr hirr' hn y
  have hω := admissible_vac_modes N hs.1
  have hω' : ∀ i : ℤ, 0 < i → mode (N'.YM (hb m)) i (e (wseq N j w k)) = 0 := by
    rw [hek]; exact admissible_vac_modes N' hs'.1
  have hlam' : mode (N'.YM (hb m)) 0 (e (wseq N j w k))
      = ((J : ℂ) / chargeCoord (latP m) (1 : ℤ) (a0 m)) • e (wseq N j w k) := by
    rw [hek]; exact hs'.2
  rcases hβ with rfl | rfl
  · refine charge_intertw_vac N.toWeakModule N'.toWeakModule e.toLinearMap e.injective hcr 1
      (wseq N j w k) hω hω' _ hs.2 hlam' (-J) (by field_simp; push_cast; ring) ?_ t
    change e (raiseOp N J (wseq N j w k)) = raiseOp N' J (e (wseq N j w k))
    rw [hek, raise_wseq' hw k, raise_wseq' hw' k, map_smul, orbitEquiv_wseq]
  · refine charge_intertw_vac N.toWeakModule N'.toWeakModule e.toLinearMap e.injective hcr (-1)
      (wseq N j w k) hω hω' _ hs.2 hlam' J (by rw [hcn]; field_simp) ?_ t
    change e (lowerOp N J (wseq N j w k)) = lowerOp N' J (e (wseq N j w k))
    rw [hek, lower_wseq' hw k, lower_wseq' hw' k, map_smul, orbitEquiv_wseq]

/-- The comparison map intertwines all modes of `e^{±α}` on all of `M`. -/
theorem orbitEquiv_charge (β : ℤ) (hβ : β = 1 ∨ β = -1) (t : ℤ) (x : M) :
    orbitEquiv hw hw0 hw' hw0' hirr hirr' (mode (N.YM (latChargeGen (latP m) β)) t x)
      = mode (N'.YM (latChargeGen (latP m) β)) t (orbitEquiv hw hw0 hw' hw0' hirr hirr' x) := by
  set e := orbitEquiv hw hw0 hw' hw0' hirr hirr'
  set H := admissibleHeisRep N
  let S : Submodule ℂ M :=
    { carrier := {x | ∀ t, e (mode (N.YM (latChargeGen (latP m) β)) t x)
        = mode (N'.YM (latChargeGen (latP m) β)) t (e x)}
      add_mem' := by
        intro a b ha hb t
        simp only [Set.mem_setOf_eq] at ha hb
        rw [map_add, map_add, ha, hb, map_add, map_add]
      zero_mem' := by intro t; simp
      smul_mem' := by
        intro c a ha t
        simp only [Set.mem_setOf_eq] at ha
        rw [map_smul, map_smul, ha, map_smul, map_smul] }
  have htop : S = ⊤ := by
    refine H.eq_top_of_vac_le S ?_ ?_
    · refine le_trans (vac_le_span_wseq hw hw0 hirr) (Submodule.span_le.mpr ?_)
      rintro _ ⟨k, rfl⟩ t
      exact orbitEquiv_charge_wseq hw hw0 hw' hw0' hirr hirr' β hβ k t
    · intro n hn y hy t
      change e (mode (N.YM (latChargeGen (latP m) β)) t (mode (N.YM (hb m)) n y))
        = mode (N'.YM (latChargeGen (latP m) β)) t (e (mode (N.YM (hb m)) n y))
      have hA := heis_charge_comm N.toWeakModule β n t y
      have hB := heis_charge_comm N'.toWeakModule β n t (e y)
      simp only [WeakModule.act_def] at hA hB
      rw [show mode (N.YM (latChargeGen (latP m) β)) t (mode (N.YM (hb m)) n y)
          = mode (N.YM (hb m)) n (mode (N.YM (latChargeGen (latP m) β)) t y)
            - chargeCoord (latP m) β (a0 m) • mode (N.YM (latChargeGen (latP m) β)) (n + t) y
          by rw [← hA]; abel,
        map_sub, map_smul, orbitEquiv_hneg hw hw0 hw' hw0' hirr hirr' hn, hy t, hy (n + t),
        orbitEquiv_hneg hw hw0 hw' hw0' hirr hirr' hn, ← hB]
      abel
  have hx : x ∈ S := by rw [htop]; trivial
  exact hx t

end OrbitEquivCharge

/-! ## From `e^{±α}` to a module isomorphism -/

section PmIso

variable {m : ℕ} {hm : 1 ≤ m} {M M' : Type} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup M'] [Module ℂ M']

/-- A linear equivalence intertwining every mode of `e^{α}` and `e^{-α}` is a module isomorphism:
the intertwined states form a subspace closed under all products, containing `e^{±α}`, hence every
`e^{kα}` (`V2m_smul_charge_charge_top`), hence everything (`latVOA_generated`). -/
noncomputable def moduleEquivOfPmCharge (A : OrdVModule (V2m m hm) M)
    (B : OrdVModule (V2m m hm) M') (e : M ≃ₗ[ℂ] M')
    (h : ∀ β : ℤ, (β = 1 ∨ β = -1) → ∀ t x, e (mode (A.YM (latChargeGen (latP m) β)) t x)
      = mode (B.YM (latChargeGen (latP m) β)) t (e x)) :
    ModuleEquiv (V2m m hm) A B where
  toLinearEquiv := e
  map_act u n x := by
    set S := intertwSub A.toWeakModule B.toWeakModule e.toLinearMap
    have hsm : ∀ u ∈ S, ∀ v ∈ S, ∀ n : ℤ, (V2m m hm).smul u n v ∈ S :=
      fun u hu v hv n => intertwSub_smul _ _ _ e.injective hu hv n
    have h1 : latChargeGen (latP m) (1 : ℤ) ∈ S := fun t x => h 1 (Or.inl rfl) t x
    have hm1 : latChargeGen (latP m) (-1 : ℤ) ∈ S := fun t x => h (-1) (Or.inr rfl) t x
    have step : ∀ a c : ℤ, latChargeGen (latP m) a ∈ S → latChargeGen (latP m) c ∈ S →
        latChargeGen (latP m) (a + c) ∈ S := by
      intro a c ha hc
      have := hsm _ ha _ hc (-1 - 2 * m * a * c)
      rw [V2m_smul_charge_charge_top] at this
      have h2 := S.smul_mem (latticeCocycle (latP m) a c)⁻¹ this
      rwa [smul_smul, inv_mul_cancel₀ (LatMod.latticeCocycle_ne_zero _ _ _), one_smul] at h2
    have hall : ∀ k : ℤ, latChargeGen (latP m) k ∈ S := by
      intro k
      induction k using Int.induction_on with
      | zero => simpa using step 1 (-1) h1 hm1
      | succ k ih => simpa [add_comm] using step 1 k h1 ih
      | pred k ih => simpa [add_comm, sub_eq_add_neg] using step (-1) (-k) hm1 ih
    have htop : S = ⊤ :=
      latVOA_generated (latP m) (latP_even m) (latP_posDef m hm) S hsm (fun β => hall β)
    have hu : u ∈ S := by rw [htop]; trivial
    exact hu n x

end PmIso

/-! ## The classification of irreducible `V_{2m}`-modules -/

section Classify

variable {m : ℕ} {hm : 1 ≤ m}

theorem hVec_eq_hb : hVec (latP m) (a0 m) = hb m := by
  simp [hVec, hb, bosonState, latVacuumGen, latStateGen, vacuumN]

theorem chi_zero_eq (hm : 1 ≤ m) (j : ℤ) :
    chi m j 0 = (j : ℂ) / chargeCoord (latP m) (1 : ℤ) (a0 m) := by
  have h := chi_mul m hm j 0
  rw [eq_div_iff (chargeCoord_one_ne_zero m hm), h]
  simp

/-- The state `e^{λ_j} = 𝟙 ⊗ e^0` of `V_{L+λ_j}` is a vacuum eigenvector with charge index `j`. -/
theorem latticeModule_vacEig (j : ℤ) :
    VacEig (latticeModule m hm j).toAdmissible j (latVacuumGen (latP m)) := by
  have hmode : ∀ n : ℤ, mode ((latticeModule m hm j).YM (hb m)) n (latVacuumGen (latP m))
      = latStateGen (latP m) (oscN (rank (latP m)) 1 (a0 m) n (vacuumN _)
          + (if n = 0 then chi m j 0 • vacuumN _ else 0)) 0 := by
    intro n
    rw [← hVec_eq_hb, latVacuumGen, latticeModule_hVec_mode]
    rfl
  refine ⟨(admissibleHeisRep _).mem_vac.mpr fun n hn => ?_, ?_⟩
  · change mode ((latticeModule m hm j).YM (hb m)) n (latVacuumGen (latP m)) = 0
    rw [hmode, if_neg (by omega), oscN_apply_pos _ _ _ hn]
    simp [vacuumN, latStateGen]
  · change mode ((latticeModule m hm j).YM (hb m)) 0 (latVacuumGen (latP m)) = _
    rw [hmode, if_pos rfl, oscN_zero, LinearMap.zero_apply, zero_add, latStateGen_csmul,
      chi_zero_eq hm]
    rfl

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- A nonzero admissible `V_{2m}`-module has a nonzero vacuum eigenvector. -/
theorem exists_vacEig (N : AdmissibleModule (V2m m hm) M) [Nontrivial M] :
    ∃ (j : ℤ) (w : M), VacEig N j w ∧ w ≠ 0 := by
  set H := admissibleHeisRep N
  by_contra hcon
  push Not at hcon
  have hvac : H.vac ≤ ⊥ := by
    refine le_trans (vac_le_eigSpan N) ?_
    rw [HeisSvN.HeisRep.eigSpan, Submodule.span_le]
    rintro v ⟨hv, μ, ⟨j, rfl⟩, hvμ⟩
    exact (Submodule.mem_bot ℂ).mpr (hcon j v ⟨hv, hvμ⟩)
  have htop := H.eq_top_of_vac_le ⊥ hvac (fun n _ x hx => by
    rw [(Submodule.mem_bot ℂ).mp hx, map_zero]; exact Submodule.zero_mem _)
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have : x ∈ (⊥ : Submodule ℂ M) := by rw [htop]; trivial
  exact hx ((Submodule.mem_bot ℂ).mp this)

end Classify

/-! ## Weights are an isomorphism invariant -/

section WeightTransfer

universe u

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- A nonzero `L₀`-eigenvector of eigenvalue `α` forces `M_α ≠ 0`. -/
theorem weight_ne_bot_of_eigen (A : OrdVModule W M) {α : ℂ} {y : M} (hy : y ≠ 0)
    (hL : mode (A.YM W.conformalVector) 1 y = α • y) : A.weight α ≠ ⊥ := by
  intro hα
  set L0 := mode (A.YM W.conformalVector) 1
  have hle : (⊤ : Submodule ℂ M) ≤ ⨆ β, ⨆ (_ : β ≠ α), L0.eigenspace β := by
    rw [← A.isInternal.submodule_iSup_eq_top, iSup_le_iff]
    intro β
    by_cases hβ : β = α
    · subst hβ; rw [hα]; exact bot_le
    · refine le_trans (fun x hx => ?_) (le_iSup₂_of_le β hβ le_rfl)
      exact Module.End.mem_eigenspace_iff.mpr (A.L0_weight β x hx)
  have hd := Module.End.eigenspaces_iSupIndep L0 α
  exact hy (Submodule.disjoint_def.mp hd y (Module.End.mem_eigenspace_iff.mpr hL)
    (hle Submodule.mem_top))

/-- Isomorphic modules have the same nonzero weight spaces. -/
theorem moduleEquiv_weight_ne_bot {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VertexOperatorAlgebra 𝒱} {M M' : Type u} [AddCommGroup M] [Module ℂ M] [AddCommGroup M']
    [Module ℂ M'] {A : OrdVModule W M} {B : OrdVModule W M'} (e : ModuleEquiv W A B) {α : ℂ}
    (h : B.weight α ≠ ⊥) : A.weight α ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine weight_ne_bot_of_eigen A (y := e.symm.toLinearEquiv x)
    (fun h0 => hx0 (e.symm.toLinearEquiv.injective (by rw [h0, map_zero]))) ?_
  have := e.symm.map_act W.conformalVector 1 x
  simp only [WeakModule.act_def] at this
  rw [← this, B.L0_weight α x hx, map_smul]

end WeightTransfer

/-! ## Main results -/

section Main

variable {m : ℕ} {hm : 1 ≤ m}

/-- Every irreducible ordinary `V_{2m}`-module is `V_{L+λ_j}` for some `j ∈ ℤ` (its vacuum
`h(0)`-charge index). -/
theorem exists_latticeModule_equiv_int {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (V2m m hm) M) (hN : N.IsIrreducible) :
    ∃ j : ℤ, Nonempty (ModuleEquiv (V2m m hm) (latticeModule m hm j) N) := by
  haveI := hN.1
  obtain ⟨j, w, hw, hw0⟩ := exists_vacEig N.toAdmissible
  have hL := latticeModule_isIrreducible m hm j
  exact ⟨j, ⟨moduleEquivOfPmCharge (latticeModule m hm j) N
    (orbitEquiv (latticeModule_vacEig (m := m) (hm := hm) j) (latVacuumGen_ne_zero _) hw hw0
      hL.2 hN.2)
    (fun β hβ t x => orbitEquiv_charge _ _ _ _ _ _ β hβ t x)⟩⟩

/-- **Classification of the irreducible `V_{2m}`-modules** (Dong 1993): every irreducible
ordinary `V_{2m}`-module is isomorphic to `V_{L+λ_j}` for exactly one `j ∈ {0, …, 2m-1}`. -/
theorem existsUnique_latticeModule_equiv {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (V2m m hm) M) (hN : N.IsIrreducible) :
    ∃! j : ℤ, (0 ≤ j ∧ j < 2 * m) ∧
      Nonempty (ModuleEquiv (V2m m hm) (latticeModule m hm j) N) := by
  obtain ⟨j, ⟨e⟩⟩ := exists_latticeModule_equiv_int N hN
  have h2m : (0 : ℤ) < 2 * m := by omega
  obtain ⟨f⟩ := (latticeModule_iso_iff m hm (j % (2 * m)) j).mpr
    ⟨-(j / (2 * m)), by rw [Int.emod_def]; ring⟩
  refine ⟨j % (2 * m), ⟨⟨Int.emod_nonneg _ h2m.ne', Int.emod_lt_of_pos _ h2m⟩, ⟨f.trans e⟩⟩, ?_⟩
  rintro j' ⟨⟨hj'0, hj'1⟩, ⟨e'⟩⟩
  obtain ⟨d, hd⟩ := (latticeModule_iso_iff m hm j' (j % (2 * m))).mp ⟨e'.trans (f.trans e).symm⟩
  have h0 := Int.emod_nonneg j h2m.ne'
  have h1 := Int.emod_lt_of_pos j h2m
  have : d = 0 := by
    by_contra hd0
    rcases lt_or_gt_of_ne hd0 with h | h
    · have : 2 * (m : ℤ) * d ≤ -(2 * m) := by nlinarith
      omega
    · have : 2 * (m : ℤ) * 1 ≤ 2 * m * d := by nlinarith
      omega
  subst this
  omega

/-- The representative with `|j| ≤ m`. -/
theorem exists_latticeModule_equiv_abs {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (V2m m hm) M) (hN : N.IsIrreducible) :
    ∃ j : ℤ, |j| ≤ m ∧ Nonempty (ModuleEquiv (V2m m hm) (latticeModule m hm j) N) := by
  obtain ⟨j, ⟨⟨hj0, hj1⟩, ⟨e⟩⟩, -⟩ := existsUnique_latticeModule_equiv N hN
  by_cases hjm : j ≤ m
  · exact ⟨j, abs_le.mpr ⟨by omega, hjm⟩, ⟨e⟩⟩
  · obtain ⟨f⟩ := (latticeModule_iso_iff m hm (j - 2 * m) j).mpr ⟨-1, by ring⟩
    exact ⟨j - 2 * m, abs_le.mpr ⟨by omega, by omega⟩, ⟨f.trans e⟩⟩

variable (m hm)

/-- **`V_{2m}` is pseudo-unitary**: an irreducible module not isomorphic to `V_{2m}` is
`V_{L+λ_j}` with `0 < |j| ≤ m`, whose weights are real and `≥ j²/(4m) > 0`. -/
theorem V2m_pseudoUnitary : PseudoUnitary (V2m m hm) := by
  intro M _ _ N hN hnot α hα
  obtain ⟨j, hj, ⟨e⟩⟩ := exists_latticeModule_equiv_abs N hN
  by_cases hj0 : j = 0
  · subst hj0
    exact (hnot.false (e.symm.trans (latticeModuleZeroEquiv m hm))).elim
  · obtain ⟨r, rfl, hr⟩ := latticeModule_lowestWeight m hm j hj (moduleEquiv_weight_ne_bot e hα)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hjr : (0 : ℝ) < (j : ℝ) ^ 2 := by positivity
    rw [Complex.ofReal_re]
    exact lt_of_lt_of_le (by positivity) hr

/-- `c(V_{2m}) = 1`. -/
theorem V2m_centralCharge : (V2m m hm).centralCharge = 1 := by
  rw [V2m, latticeVOAGen_centralCharge, rank_latP]
  simp

/-- **`V_{2m}` is nice** (strongly rational and pseudo-unitary). -/
theorem V2m_nice : Nice (V2m m hm) := ⟨V2m_stronglyRational m hm, V2m_pseudoUnitary m hm⟩

end Main

/-! ## Transport of niceness along a VOA isomorphism -/

section Transport

universe u

variable {𝒱 𝒲 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] [AddCommGroup 𝒲] [Module ℂ 𝒲]
  {V : VertexOperatorAlgebra 𝒱} {T : VertexOperatorAlgebra 𝒲}

theorem isVOAHom_symm' (e : 𝒱 ≃ₗ[ℂ] 𝒲) (he : IsVOAHom V T e.toLinearMap) :
    IsVOAHom T V e.symm.toLinearMap where
  map_vacuum := by
    apply e.injective
    simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
    exact he.map_vacuum.symm
  map_smul u n x := by
    apply e.injective
    simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
    have := he.map_smul (e.symm u) n (e.symm x)
    simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] at this
    exact this.symm

/-- A VOA homomorphism preserving the conformal vector intertwines every `L n`. -/
theorem voaHom_map_L {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) (n : ℤ) (v : 𝒱) :
    φ (V.L n v) = T.L n (φ v) := by
  have := hφ.map_smul V.conformalVector (n + 1) v
  rw [hω] at this
  exact this

theorem voaHom_map_L_pow {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) (n : ℤ) (j : ℕ) (v : 𝒱) :
    φ (((V.L n) ^ j) v) = ((T.L n) ^ j) (φ v) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', Module.End.mul_apply, voaHom_map_L hφ hω, ih, pow_succ',
      Module.End.mul_apply]

/-- In a VOA, an `L₀`-eigenvector of integer eigenvalue `n` lies in `𝒱_n`. -/
theorem mem_grading_of_L0 (W : VertexOperatorAlgebra 𝒲) {n : ℤ} {y : 𝒲}
    (hy : W.L 0 y = (n : ℂ) • y) : y ∈ W.grading n := by
  have htop : (⊤ : Submodule ℂ 𝒲) ≤ W.grading n ⊔ ⨆ (k : ℤ) (_ : k ≠ n), W.grading k := by
    rw [← W.isInternal.submodule_iSup_eq_top, iSup_split_single _ n]
  obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.mp (htop (Submodule.mem_top (x := y)))
  have hgr : ∀ k : ℤ, W.grading k ≤ (W.L 0).eigenspace (k : ℂ) := fun k x hx =>
    Module.End.mem_eigenspace_iff.mpr (W.L_zero_grading x hx)
  have hz1 : z ∈ (W.L 0).eigenspace (n : ℂ) := by
    have h1 : a + z ∈ (W.L 0).eigenspace (n : ℂ) := Module.End.mem_eigenspace_iff.mpr hy
    have h2 := hgr n ha
    simpa using Submodule.sub_mem _ h1 h2
  have hle : (⨆ (k : ℤ) (_ : k ≠ n), W.grading k)
      ≤ ⨆ (μ : ℂ) (_ : μ ≠ (n : ℂ)), (W.L 0).eigenspace μ :=
    iSup₂_le fun k hk =>
      le_trans (hgr k) (le_iSup₂_of_le (k : ℂ) (by exact_mod_cast hk) le_rfl)
  have hz2 := hle hz
  have := Submodule.disjoint_def.mp (Module.End.eigenspaces_iSupIndep (W.L 0) (n : ℂ)) z hz1 hz2
  rw [this, add_zero]; exact ha

theorem voaHom_map_grading {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) {n : ℤ} {v : 𝒱} (hv : v ∈ V.grading n) :
    φ v ∈ T.grading n := by
  refine mem_grading_of_L0 T ?_
  rw [← voaHom_map_L hφ hω, V.L_zero_grading v hv, map_smul]

/-- Pulling a weak module back along a VOA homomorphism. -/
def pullWeak {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ) {M : Type*} [AddCommGroup M] [Module ℂ M]
    (B : WeakModule T M) : WeakModule V M where
  YM := B.YM ∘ₗ φ
  vacuum_YM := by simp [hφ.map_vacuum, B.vacuum_YM]
  truncation u x := B.truncation (φ u) x
  jacobi u v x ℓ m n := by
    simp only [LinearMap.comp_apply, hφ.map_smul]
    exact B.jacobi (φ u) (φ v) x ℓ m n

@[simp] theorem pullWeak_act {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ) {M : Type*}
    [AddCommGroup M] [Module ℂ M] (B : WeakModule T M) (u : 𝒱) (n : ℤ) (x : M) :
    (pullWeak hφ B).act u n x = B.act (φ u) n x := rfl

variable (e : 𝒱 ≃ₗ[ℂ] 𝒲) (he : IsVOAHom V T e.toLinearMap)
  (hω : e V.conformalVector = T.conformalVector)

include hω in
theorem symm_conformal : e.symm T.conformalVector = V.conformalVector := by
  rw [← hω, LinearEquiv.symm_apply_apply]

include he hω in
/-- Central charge is an isomorphism invariant (for a nonzero vacuum). -/
theorem centralCharge_eq_of_iso (hT : T.vacuum ≠ 0) : V.centralCharge = T.centralCharge := by
  have key : ∀ {𝒰 : Type u} [AddCommGroup 𝒰] [Module ℂ 𝒰] (W : VertexOperatorAlgebra 𝒰),
      W.L 2 (W.L (-2) W.vacuum) = (W.centralCharge / 2) • W.vacuum := by
    intro 𝒰 _ _ W
    have h := LinearMap.congr_fun (W.L_virasoro 2 (-2)) W.vacuum
    have h2 : W.L 2 W.vacuum = 0 := (W.creation W.conformalVector).2 3 (by norm_num)
    have h0 : W.L 0 W.vacuum = 0 := by
      rw [W.L_zero_grading _ W.vacuum_mem]; simp
    simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.add_apply, LinearMap.smul_apply, h2, map_zero, sub_zero] at h
    rw [h, if_pos (by norm_num), show (2 : ℤ) + -2 = 0 by norm_num, h0]
    simp only [smul_zero, zero_add, LinearMap.smul_apply, Module.End.one_apply]
    congr 1
    push_cast; ring
  have hV := key V
  have hTk := key T
  have hL : ∀ (n : ℤ) (v : 𝒱), e (V.L n v) = T.L n (e v) := fun n v => by
    simpa using voaHom_map_L he hω n v
  have hvac : e V.vacuum = T.vacuum := by simpa using he.map_vacuum
  have h1 := congrArg e hV
  rw [hL, hL, hvac, map_smul, hvac, hTk] at h1
  have h3 : ((T.centralCharge / 2) - (V.centralCharge / 2)) • T.vacuum = 0 := by
    rw [sub_smul, h1, sub_self]
  have := (smul_eq_zero.mp h3).resolve_right hT
  linear_combination -2 * this

include he in
theorem isSimple_of_iso (hT : T.IsSimple) : V.IsSimple := by
  refine ⟨fun h => hT.1 ?_, fun I hI => ?_⟩
  · rw [eq_bot_iff]
    intro y _
    have : e.symm y ∈ (⊤ : Submodule ℂ 𝒱) := Submodule.mem_top
    rw [h, Submodule.mem_bot] at this
    rw [Submodule.mem_bot, ← e.apply_symm_apply y, this, map_zero]
  · have hJ : T.IsIdeal (I.map e.toLinearMap) := by
      intro u v n hv
      obtain ⟨v', hv', rfl⟩ := hv
      refine ⟨V.smul (e.symm u) n v', hI _ _ _ hv', ?_⟩
      have := he.map_smul (e.symm u) n v'
      simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] at this
      exact this
    have hc : I = (I.map e.toLinearMap).comap e.toLinearMap :=
      (Submodule.comap_map_eq_of_injective e.injective I).symm
    rcases hT.2 _ hJ with h | h
    · left; rw [hc, h, Submodule.comap_bot]; exact LinearMap.ker_eq_bot.mpr e.injective
    · right; rw [hc, h, Submodule.comap_top]

include he hω in
theorem selfDual_of_iso (hT : T.SelfDual) : V.SelfDual := by
  obtain ⟨B, hBf, hBr⟩ := hT
  let B' : VertexOperatorAlgebra.InvariantForm V :=
    { form := B.form.compl₁₂ e.toLinearMap e.toLinearMap
      virasoro_adj := by
        intro n a b
        simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_toLinearMap]
        have h1 := voaHom_map_L he hω n a
        have h2 := voaHom_map_L he hω (-n) b
        simp only [LinearEquiv.coe_toLinearMap] at h1 h2
        rw [h1, h2, B.virasoro_adj] }
  refine ⟨B', ?_, ?_⟩
  · intro wt u hu n a b
    have hu' := voaHom_map_grading he hω hu
    simp only [B', LinearMap.compl₁₂_apply, LinearEquiv.coe_toLinearMap]
    have hs := he.map_smul u n a
    simp only [LinearEquiv.coe_toLinearMap] at hs hu'
    rw [hs, hBf wt (e u) hu' n (e a) (e b)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have hp := voaHom_map_L_pow he hω 1 j u
    have hs2 := he.map_smul (((V.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b
    simp only [LinearEquiv.coe_toLinearMap] at hp hs2
    rw [hs2, hp]
  · rw [eq_bot_iff]
    intro a ha
    rw [VertexOperatorAlgebra.InvariantForm.mem_leftRadical] at ha
    have hea : e a ∈ VertexOperatorAlgebra.InvariantForm.leftRadical B := by
      rw [VertexOperatorAlgebra.InvariantForm.mem_leftRadical]
      refine LinearMap.ext fun y => ?_
      have := LinearMap.congr_fun ha (e.symm y)
      simpa [B'] using this
    rw [hBr, Submodule.mem_bot] at hea
    rw [Submodule.mem_bot]
    exact e.injective (by rw [hea, map_zero])

include he in
theorem c2Cofinite_of_iso (hT : C2Cofinite T) : C2Cofinite V := by
  have hmap : (O₂ V).map e.toLinearMap = O₂ T := by
    rw [O₂, O₂, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨u, v, rfl⟩, rfl⟩
      exact ⟨e u, e v, he.map_smul u (-2) v⟩
    · rintro ⟨u, v, rfl⟩
      refine ⟨V.smul (e.symm u) (-2) (e.symm v), ⟨_, _, rfl⟩, ?_⟩
      have := he.map_smul (e.symm u) (-2) (e.symm v)
      simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] at this
      exact this
  unfold C2Cofinite at hT ⊢
  exact LinearEquiv.finiteDimensional (Submodule.Quotient.equiv (O₂ V) (O₂ T) e hmap).symm

include he hω in
theorem admissiblyRational_of_iso (hT : AdmissiblyRational T) : AdmissiblyRational V := by
  intro M _ _ N P
  have hs := isVOAHom_symm' e he
  have hωs := symm_conformal e hω
  let N' : AdmissibleModule T M :=
    { toWeakModule := pullWeak hs N.toWeakModule
      lev := N.lev
      lev_eq_bot_of_neg := N.lev_eq_bot_of_neg
      isInternal := N.isInternal
      act_lev := fun w p k a ha x hx => N.act_lev (voaHom_map_grading hs hωs ha) hx }
  let P' : WeakModule.Submodule' N'.toWeakModule :=
    ⟨P.carrier, fun u n x hx => P.act_mem (e.symm u) n hx⟩
  obtain ⟨Q', hQ'⟩ := hT N' P'
  refine ⟨⟨Q'.carrier, fun u n x hx => ?_⟩, hQ'⟩
  have := Q'.act_mem (e u) n hx
  simpa [N', pullWeak] using this

include he hω in
theorem stronglyRational_of_iso (hT : StronglyRational T) : StronglyRational V :=
  { simple := isSimple_of_iso e he hT.simple
    selfDual := selfDual_of_iso e he hω hT.selfDual
    c2Cofinite := c2Cofinite_of_iso e he hT.c2Cofinite
    rational := admissiblyRational_of_iso e he hω hT.rational }

include he hω in
theorem pseudoUnitary_of_iso (hT : PseudoUnitary T) : PseudoUnitary V := by
  intro M _ _ N hN hnot α hα
  have hs := isVOAHom_symm' e he
  have hωs := symm_conformal e hω
  let N' : OrdVModule T M :=
    { toWeakModule := pullWeak hs N.toWeakModule
      weight := N.weight
      isInternal := N.isInternal
      L0_weight := fun α x hx => by
        have := N.L0_weight α x hx
        simpa [pullWeak, hωs] using this
      finrank := N.finrank
      boundedBelow := N.boundedBelow }
  refine hT M N' ⟨hN.1, fun P => ?_⟩ ⟨fun f => hnot.false ?_⟩ α hα
  · let P0 : WeakModule.Submodule' N.toWeakModule :=
      ⟨P.carrier, fun u n x hx => by
        have := P.act_mem (e u) n hx
        simpa [N', pullWeak] using this⟩
    exact hN.2 P0
  · refine
      { toLinearEquiv := f.toLinearEquiv.trans e.symm
        map_act := fun u n x => ?_ }
    have h1 := f.map_act (e u) n x
    simp only [N', pullWeak_act, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply] at h1
    simp only [LinearEquiv.trans_apply]
    rw [h1]
    change e.symm (T.smul (e u) n (f.toLinearEquiv x)) = V.smul u n (e.symm (f.toLinearEquiv x))
    have := hs.map_smul (e u) n (f.toLinearEquiv x)
    simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply] at this
    exact this

end Transport

/-! ## The lattice clause of the converse (GR Prop. 3.2) -/

/-- **The lattice clause of Gannon–Rayhaun Prop. 3.2**: a VOA isomorphic to `V_{2m}` is nice
and has `c = 1`.  Stated for carriers in `Type` (the universe of `V_{2m}`), because
`PseudoUnitary` and `AdmissiblyRational` quantify over modules in the VOA's own universe. -/
theorem nice_of_hasCOneLabel_lat {𝒱 : Type} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (V : VertexOperatorAlgebra 𝒱) (m : ℕ) (h : HasCOneLabel V (.lat m)) :
    Nice V ∧ V.centralCharge = 1 := by
  obtain ⟨hm, e, he, hω⟩ := h
  refine ⟨⟨stronglyRational_of_iso e he hω (V2m_stronglyRational m hm),
    pseudoUnitary_of_iso e he hω (V2m_pseudoUnitary m hm)⟩, ?_⟩
  rw [centralCharge_eq_of_iso e he hω
    (V2m_stronglyRational m hm).toStronglyFinite.vacuum_ne_zero, V2m_centralCharge]

end VOA.Classification.COne
