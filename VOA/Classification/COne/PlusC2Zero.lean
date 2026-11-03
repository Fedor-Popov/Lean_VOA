/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusC2Sector
import VOA.Classification.COne.LatticeModulesIrred

/-!
# `C₂(V_{2m}⁺)`: the `M(1)⁺` sector from a lattice-free residual

Notation of `PlusC2Sector.lean`.  `φ_w(q)` (`topCoeff`) is the coefficient of `α(−1)^w` in a Fock
state `q` of weight `w` — the unique monomial whose polynomial degree equals its weight.

## The two inputs

* **The charged relations** (proved here, `vSchur_mem_G`):
  `x_{sα}₍ₙ₎ e^{−sα} = ε·S_d(sα) ⊗ e⁰` for `−2ms² ≤ n ≤ −2`, `d = −n − 1 + 2ms²`: the
  charge-`−2sα` term `e^{−sα}₍ₙ₎e^{−sα}` vanishes in this range.  Hence
  `P(S_d(sα) ⊗ e⁰) ∈ C₂(V⁺)` for `2ms² < d < 4ms²`, and `φ_d(S_d(sα)) = (s·c)^d/d! ≠ 0`
  (`topCoeff_vSchur`).  For `s ≥ 3` these windows overlap, so every `d > 18m` is covered
  (`exists_window`).
* **The lattice-free residual** `M1PlusC2Line m hm` (TRUE, cited — see its docstring): for all
  large weights `w`, a state of `M(1)⁺_w` with vanishing `φ_w` (no condition for odd `w`) lies in
  the *internal* `C₂(M(1)⁺) = span{u₍₋₂₎v : u, v ∈ M(1)⁺}`.  Equivalently `R(M(1)⁺)_w` is spanned
  by the class of `α(−1)^w` (i.e. of `ω^{w/2}`) for even `w`, and vanishes for odd `w`.

## Main results

* `sectorZero_of_m1PlusC2Line : M1PlusC2Line m hm → PlusSectorFinite m hm 0` — the `M(1)⁺`
  sector is finite modulo `C₂(V_{2m}⁺)` (every `m ≥ 1`).
* `vSchur_mem_G`, `topCoeff_vSchur`, `exists_window`.

## Why the residual is the right one

`φ_w` vanishes on the internal `C₂(M(1)⁺)` for the trivial reason that `u₍₋₂₎v` has polynomial
degree `≤ deg u + deg v ≤ wt u + wt v < w`; so `M1PlusC2Line` says exactly that
`dim R(M(1)⁺)_w ≤ 1` eventually.  Exact computation (`scratchpad/q2/rm1plus.py`, mod-p ranks,
which can only *over*estimate the quotient) gives `dim R(M(1)⁺)_w = 1,0,2,0,2,0,2,0,1,0,1,0,1`
for `w = 2,…,14`, with `α(−1)^w ∉ C₂(M(1)⁺)`.  The statement for all `w ≥ 10` follows from the
Dong–Nagatomo strong generation of `M(1)⁺` by `ω` and `J` (J. Algebra 216 (1999), Thm 2.7) and the
two relations at weights 8 and 10 (Yamskulna 2004, Cor. 5.10, 5.14; confirmed above).
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN VOA.Moonshine LatMod

namespace PlusC2

variable (m : ℕ) (hm : 1 ≤ m)

/-! ## §1  The top coefficient `φ_w` -/

/-- `φ_w(q)`: the coefficient of `α(−1)^w = X(0,a₀)^w` in `q`. -/
noncomputable def topCoeff (w : ℕ) (q : FockN (rank (latP m))) : ℂ :=
  MvPolynomial.coeff (Finsupp.single ((0 : ℕ), a0 m) w) q

theorem topCoeff_X_mul (w k : ℕ) (q : FockN (rank (latP m))) :
    topCoeff m (w + 1) (MvPolynomial.X ((k, a0 m)) * q) = if k = 0 then topCoeff m w q else 0 := by
  rw [topCoeff, MvPolynomial.coeff_X_mul']
  by_cases hk : k = 0
  · subst hk
    rw [if_pos (by simp), if_pos rfl, topCoeff]
    congr 1
    rw [Finsupp.single_add (((0 : ℕ), a0 m)) w 1, add_tsub_cancel_right]
  · rw [if_neg, if_neg hk]
    rw [Finsupp.mem_support_iff, Finsupp.single_apply, if_neg]
    · simp
    · intro h; exact hk (congrArg Prod.fst h).symm

theorem vVar_rankOne (a : (latP m).carrier) (k : ℕ) :
    vVar (latP m) a k = chargeCoord (latP m) a (a0 m) • MvPolynomial.X ((k, a0 m)) := by
  rw [vVar]
  refine Finset.sum_eq_single (a0 m) (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)
  exfalso
  apply hb
  have hb1 : b.val < 1 := lt_of_lt_of_eq b.isLt (rank_latP m)
  exact Fin.ext (by simp only [a0]; omega)

/-- `φ_d(S_d(a)) = c_a^d / d!`, `c_a` the charge coordinate of `a`. -/
theorem topCoeff_vSchur (a : (latP m).carrier) (d : ℕ) :
    topCoeff m d (vSchur (latP m) a d) = chargeCoord (latP m) a (a0 m) ^ d / (d.factorial : ℂ) := by
  induction d with
  | zero => simp [topCoeff, vSchur_zero]
  | succ d ih =>
    rw [vSchur_succ, topCoeff, MvPolynomial.coeff_smul, MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single 0]
    · rw [vVar_rankOne, smul_mul_assoc, MvPolynomial.coeff_smul, ← topCoeff, topCoeff_X_mul,
        if_pos rfl, Nat.sub_zero, ih, smul_eq_mul, smul_eq_mul, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · intro k _ hk
      rw [vVar_rankOne, smul_mul_assoc, MvPolynomial.coeff_smul, ← topCoeff, topCoeff_X_mul,
        if_neg hk, smul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos d)) h

include hm in
theorem chargeCoord_nat_ne_zero (s : ℕ) (hs : 1 ≤ s) :
    chargeCoord (latP m) ((s : ℤ) : (latP m).carrier) (a0 m) ≠ 0 := by
  have h := sum_chargeCoord (latP m) (latP_posDef m hm) ((s : ℤ) : (latP m).carrier)
    ((1 : ℤ) : (latP m).carrier)
  rw [sum_rankOne, latP_form] at h
  intro h0
  rw [h0, zero_mul] at h
  have : (2 * (m : ℤ) * s * 1 : ℤ) ≠ 0 := by
    have : (1 : ℤ) ≤ m := by exact_mod_cast hm
    have : (1 : ℤ) ≤ s := by exact_mod_cast hs
    positivity
  exact this (by exact_mod_cast h.symm)

include hm in
theorem topCoeff_vSchur_ne_zero (s : ℕ) (hs : 1 ≤ s) (d : ℕ) :
    topCoeff m d (vSchur (latP m) ((s : ℤ) : (latP m).carrier) d) ≠ 0 := by
  rw [topCoeff_vSchur]
  exact div_ne_zero (pow_ne_zero _ (chargeCoord_nat_ne_zero m hm s hs))
    (by exact_mod_cast Nat.factorial_ne_zero d)

/-! ## §2  The charged relations `P(S_d(sα) ⊗ e⁰) ∈ C₂(V⁺)`, `2ms² < d < 4ms²` -/

/-- For `2ms² < d < 4ms²`: `S_d(sα) ⊗ e⁰ ∈ G = P⁻¹(C₂(V⁺))`. -/
theorem vSchur_mem_G (s : ℕ) (d : ℕ) (hd1 : 2 * m * s ^ 2 < d) (hd2 : d < 4 * m * s ^ 2) :
    latStateGen (latP m) (vSchur (latP m) ((s : ℤ) : (latP m).carrier) d) 0 ∈ G m hm := by
  set a : (latP m).carrier := ((s : ℤ) : (latP m).carrier) with ha
  have haa : (latP m).form a a = 2 * (m : ℤ) * s ^ 2 := by
    rw [ha, latP_form]; ring
  have hform1 : (latP m).form a (-a) = -(2 * (m : ℤ) * s ^ 2) := by
    rw [map_neg, haa]
  have hform2 : (latP m).form (-a) (-a) = 2 * (m : ℤ) * s ^ 2 := by
    rw [map_neg, map_neg, LinearMap.neg_apply, neg_neg, haa]
  set n : ℤ := -(d : ℤ) - 1 + 2 * (m : ℤ) * s ^ 2 with hn
  have hd1' : 2 * (m : ℤ) * s ^ 2 < d := by exact_mod_cast hd1
  have hd2' : (d : ℤ) < 4 * (m : ℤ) * s ^ 2 := by exact_mod_cast hd2
  have h1 := split_mem_G m hm a (n := n) (by rw [hn]; linarith) (latStateGen (latP m) (vacuumN _) (-a))
  rw [V2m, latVOA_smul_latChargeGen_state, latVOA_smul_latChargeGen_state,
    hform1, hform2, EEVec_vacuum, EEVec_vacuum,
    if_pos (show (0 : ℤ) ≤ -n - 1 - -(2 * (m : ℤ) * s ^ 2) by rw [hn]; linarith),
    if_neg (show ¬ (0 : ℤ) ≤ -n - 1 - 2 * (m : ℤ) * s ^ 2 by rw [hn]; linarith),
    show -n - 1 - -(2 * (m : ℤ) * s ^ 2) = (d : ℤ) by rw [hn]; ring, Int.toNat_natCast,
    add_neg_cancel] at h1
  simp only [latStateGen, TensorProduct.zero_tmul, smul_zero, add_zero] at h1
  have h2 := Submodule.smul_mem _ (latticeCocycle (latP m) a (-a)) h1
  rwa [smul_smul, latticeCocycle_sq, one_smul] at h2

include hm in
/-- For `d > 18m` there is `s ≥ 3` with `2ms² < d < 4ms²`. -/
theorem exists_window (d : ℕ) (hd : 18 * m < d) :
    ∃ s : ℕ, 1 ≤ s ∧ 2 * m * s ^ 2 < d ∧ d < 4 * m * s ^ 2 := by
  have hex : ∃ s : ℕ, d ≤ 2 * m * (s + 1) ^ 2 := ⟨d, by
    have h1 : d ≤ (d + 1) ^ 2 := by nlinarith
    have h2 : (d + 1) ^ 2 ≤ 2 * m * (d + 1) ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
    omega⟩
  classical
  set s := Nat.find hex with hs
  have hspec : d ≤ 2 * m * (s + 1) ^ 2 := Nat.find_spec hex
  have hm0 : 1 ≤ m := by omega
  have hs3 : 3 ≤ s := by
    by_contra h
    push Not at h
    have : (s + 1) ^ 2 ≤ 9 := by nlinarith
    have : 2 * m * (s + 1) ^ 2 ≤ 18 * m := by nlinarith
    omega
  have hlow : 2 * m * s ^ 2 < d := by
    have hmin := Nat.find_min hex (show s - 1 < s by omega)
    push Not at hmin
    rwa [show s - 1 + 1 = s by omega] at hmin
  refine ⟨s, by omega, hlow, ?_⟩
  have : (s + 1) ^ 2 < 2 * s ^ 2 := by nlinarith
  nlinarith

/-! ## §3  The residual and the reduction -/

/-- The **internal** `C₂(M(1)⁺)`: `span{u₍₋₂₎v : u, v ∈ M(1)⁺}` inside `V_{2m}⁺`. -/
noncomputable def c2M1Plus : Submodule ℂ (VP m hm) :=
  Submodule.span ℂ {x | ∃ a b : FockN (rank (latP m)),
    x = (V2mPlus m hm).smul (PP m hm (latStateGen (latP m) a 0)) (-2) (PP m hm (latStateGen (latP m) b 0))}

theorem c2M1Plus_le_O₂ : c2M1Plus m hm ≤ O₂ (V2mPlus m hm) := by
  rw [c2M1Plus, Submodule.span_le]
  rintro _ ⟨a, b, rfl⟩
  exact smul_le_neg_two_mem_O₂ _ _ _ le_rfl

/-- **The lattice-free residual for the `M(1)⁺` sector** (TRUE; cited):
for all large `w`, every `q` of Fock weight `w` whose `α(−1)^w`-coefficient vanishes (no condition
when `w` is odd) has `P(q ⊗ e⁰) ∈ C₂(M(1)⁺)`, the span of `u₍₋₂₎v` with `u, v ∈ M(1)⁺`.

It is a statement about the Heisenberg orbifold `M(1)⁺` only (the charged sectors of `V_{2m}` do
not enter, and the normalisation `⟨α,α⟩ = 2m` only rescales `α(−1)`): it says
`dim R(M(1)⁺)_w ≤ 1` for large `w`, the class being detected by `α(−1)^w`.
Sources: Dong–Nagatomo, J. Algebra 216 (1999) 384–404, Thm 2.7 (`M(1)⁺` is strongly generated by
`ω` and `J`), together with the relations `J₋₁J ≡ ρL(−2)²J + σL(−2)⁴𝟙` (weight 8) and
`L(−2)³J ≡ 4L(−2)⁵𝟙` (weight 10) of Yamskulna, Comm. Algebra 32 (2004), Cor. 5.10 and 5.14 (her
numerical constants are approximate; the existence of the relations is what is used, and it is
confirmed by the exact computation `scratchpad/q2/rm1plus.py`: `dim R(M(1)⁺)_w = 1` for even
`10 ≤ w ≤ 14`, `0` for odd `3 ≤ w ≤ 13`).  NOT proved here. -/
def M1PlusC2Line : Prop :=
  ∃ N : ℕ, ∀ w : ℕ, N ≤ w → ∀ q ∈ gradingWN (rank (latP m)) w,
    (Even w → topCoeff m w q = 0) → PP m hm (latStateGen (latP m) q 0) ∈ c2M1Plus m hm

/-- The linear map `q ↦ P(q ⊗ e⁰)`. -/
noncomputable def sec0 : FockN (rank (latP m)) →ₗ[ℂ] VP m hm :=
  (PP m hm).comp ((TensorProduct.mk ℂ (FockN (rank (latP m))) ((latP m).carrier →₀ ℂ)).flip
    (eGen (latP m) 0))

theorem sec0_apply (q : FockN (rank (latP m))) : sec0 m hm q = PP m hm (latStateGen (latP m) q 0) := rfl

/-- High weights of `M(1)⁺` lie in `C₂(V⁺)`, given the residual. -/
theorem sec0_mem_O₂_of_line {N : ℕ}
    (hN : ∀ w : ℕ, N ≤ w → ∀ q ∈ gradingWN (rank (latP m)) w,
      (Even w → topCoeff m w q = 0) → PP m hm (latStateGen (latP m) q 0) ∈ c2M1Plus m hm)
    (w : ℕ) (hw : N ≤ w) (hw' : 18 * m < w) (q : FockN (rank (latP m)))
    (hq : q ∈ gradingWN (rank (latP m)) w) : sec0 m hm q ∈ O₂ (V2mPlus m hm) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_window m hm w hw'
  set S := vSchur (latP m) ((s : ℤ) : (latP m).carrier) w with hS
  have hSmem : S ∈ gradingWN (rank (latP m)) w := vSchur_mem_gradingWN (latP m) _ w
  have hSne := topCoeff_vSchur_ne_zero m hm s hs1 w
  set c : ℂ := topCoeff m w q / topCoeff m w S with hc
  set q' := q - c • S with hq'
  have hq'mem : q' ∈ gradingWN (rank (latP m)) w :=
    Submodule.sub_mem _ hq (Submodule.smul_mem _ _ hSmem)
  have htop : topCoeff m w q' = 0 := by
    simp only [hq', topCoeff, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, smul_eq_mul]
    rw [← topCoeff, ← topCoeff, hc]
    have hSne' : topCoeff m w S ≠ 0 := hSne
    rw [div_mul_cancel₀ _ hSne', sub_self]
  have h1 : sec0 m hm q' ∈ O₂ (V2mPlus m hm) :=
    c2M1Plus_le_O₂ m hm (hN w hw q' hq'mem fun _ => htop)
  have h2 : sec0 m hm S ∈ O₂ (V2mPlus m hm) := vSchur_mem_G m hm s w hs2 hs3
  have : q = q' + c • S := by rw [hq']; abel
  rw [this, map_add, map_smul]
  exact Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2)

/-- **The `M(1)⁺` sector is finite modulo `C₂(V_{2m}⁺)`**, given the lattice-free residual. -/
theorem sectorZero_of_m1PlusC2Line (h : M1PlusC2Line m hm) : PlusSectorFinite m hm 0 := by
  classical
  obtain ⟨N, hN⟩ := h
  set N' := N + 18 * m + 1 with hN'
  -- the low weights span a finite-dimensional space
  set Low : Submodule ℂ (FockN (rank (latP m))) := ⨆ w : Fin N', gradingWN (rank (latP m)) w
    with hLow
  haveI : ∀ w, FiniteDimensional ℂ (gradingWN (rank (latP m)) w) :=
    fun w => gradingWN_finiteDimensional _ w
  haveI : FiniteDimensional ℂ Low := by
    rw [hLow]
    exact Submodule.finiteDimensional_iSup _
  haveI : FiniteDimensional ℂ (Low.map (sec0 m hm)) := Module.Finite.map _ _
  obtain ⟨S, hS⟩ := (Submodule.fg_iff_finiteDimensional _).mpr
    (inferInstance : FiniteDimensional ℂ (Low.map (sec0 m hm)))
  refine ⟨S, ?_⟩
  rw [sectorP, Submodule.span_le]
  rintro _ ⟨q, rfl⟩
  change sec0 m hm q ∈ _
  -- reduce to homogeneous `q`
  suffices hsub : (⊤ : Submodule ℂ (FockN (rank (latP m)))) ≤
      (Submodule.span ℂ (S : Set (VP m hm)) ⊔ O₂ (V2mPlus m hm)).comap (sec0 m hm) by
    exact hsub (Submodule.mem_top (x := q))
  refine (gradingWN_iSup_eq_top _).ge.trans (iSup_le fun w p hp => ?_)
  rw [Submodule.mem_comap]
  rcases Nat.lt_or_ge w N' with hw | hw
  · refine Submodule.mem_sup_left ?_
    rw [hS]
    refine ⟨p, ?_, rfl⟩
    rw [hLow]
    exact Submodule.mem_iSup_of_mem (⟨w, hw⟩ : Fin N') hp
  · refine Submodule.mem_sup_right ?_
    exact sec0_mem_O₂_of_line m hm hN w (by omega) (by omega) p hp

end PlusC2

end VOA.Classification.COne
