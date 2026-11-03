/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesSingTailDiag

/-!
# The slots of `T`-degree exactly `n`

The tail of `BoxInclusion n r` consists of the slots `(N, k = r - N)` with `k ≥ n`.  This file
proves **every slot with `k = n`** (any `N`, any weight), with no Witt-singularity hypothesis.

The test reads `F(J + x̃) · v₀^{2N} = y + Σ a_l · (jets of (J + x̃)ⁿ)` with `y` a combination of
products of `r = N + n` letters.  Apply the specialisation `chi` of `TwoSeriesInclLow`
(`u = α ξ √(1+st) + α² ε / √(1+st)`, `v = √(1+st)`): the Sugawara images are `α² (A + ε B)`, so
both `F(J + x̃)` and every jet of `(J + x̃)ⁿ` carry exactly `α^{2n}`.  Divide by `α^{2n}` and set
`α = 0` (`Pi0`).  Then `u ↦ 0`, so **every multiplier `chi(a_l)` collapses to a polynomial in `s`
with complex coefficients** (`Pi0_chi_mem`): the ideal contributes only `ℂ[s]`-combinations of
`θ0(jets of Tⁿ)`.  Two identities finish the argument:

* `shift_mem`, `shift_iter` — `s Θⁿ_j + Θⁿ_{j+1} ∈ W0 (n + 1)`, hence
  `s^w Θⁿ_j ≡ (-1)^w Θⁿ_{j+w}` modulo `W0 (n + w)`; this comes from `(1 + s t) B(t) = -s`.
  So for `w ≤ N` the term `s^w θ0(jet)` is absorbed into `θ0(jetSpanT)` (`decomp_of_mem_M0`);
* `high_eq_zero` — the terms `s^w θ0(jet)` with `w > N` would raise the `ε`-free `s`-degree
  beyond `n + N`; their leading coefficient is `sqMap` of a nonzero polynomial, so they vanish.

What remains is `θ0(F + G) ∈ W0 (N + n)` with `G` a combination of jets of `Tⁿ`, and the
letters-only sharpness at `α = 0` (`vars_lt_of_W0`) puts `F + G` in the box; projecting to the
weight of `F` (`pw`) gives `τ ∈ box`.

Main results:

* `LiftDegN.boxInclusion_degN` — **every slot of `BoxInclusion n r` with `r - N = n`**;
* `boxSingularTail_of_high`, `boxInclusionTail_of_high` — the tails reduce to the slots with
  `r - N > n`; `boxInclusion_succ_of_slot0` — `BoxInclusion n (n + 1)` reduces to the slot `N = 0`;
* `boxSingularTail_one` — everything at `n = 1` (`R_1 = ℂ`);
* `twoSeries_gradedUnitary_of_strictModel_singularLiftHigh` — the endpoint with the
  ideal-elimination input `SingularLiftHigh n r` (slots `r - N > n` only, `r > n`);
* `twoSeries_gradedUnitary_one_of_strictModel` — `n = 1`, conditional only on `hA`, `det`.

Numerically (exact linear algebra mod `1000003`, scripts not in the repository, not a proof): the same
`α^{2n}`-order argument is **not** sharp in the slots `r - N > n`: with `chi` kept to `α`-order
`D`, the slot `n = 2`, `N = 0`, `k = 3` is detected for `D = 2k + 2` but not `D = 2k + 1`, and the
slot `n = 2`, `N = 1`, `k = 3` for `D = 2k + 7` but not `D = 2k + 3`.  Those slots need a different
idea.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.InvariantSymbol VOA.SocleEval
open VOA.AdamovicSymbol Module
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete

noncomputable section

-- The dual numbers over `Cq[s]` make instance search and unification expensive (as in
-- `TwoSeriesInclLow`).
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace LiftDegN

open InclLow TailWitt SingTailLift SingTailDiag

/-! ### The dual numbers at `α = 0` -/

/-- The coefficient ring at `α = 0`: `ℂ[r₀, q₁, q₂, …]` with `r₀ = X 0`, `q_m = X m`. -/
abbrev K0 : Type := MvPolynomial ℕ ℂ

/-- `K0[s]`. -/
abbrev P0 : Type := Polynomial K0

/-- `K0[s][ε]`. -/
abbrev D0 : Type := DualNumber P0

/-- `W0 r`: the `a + ε b` with `deg a ≤ r` and `deg (s b) ≤ r`. -/
def W0 (r : ℕ) : Submodule ℂ D0 where
  carrier := {x | (TrivSqZeroExt.fst x).degree ≤ (r : WithBot ℕ) ∧
    (Polynomial.X * TrivSqZeroExt.snd x).degree ≤ (r : WithBot ℕ)}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · rw [TrivSqZeroExt.fst_add]
      exact (Polynomial.degree_add_le _ _).trans (max_le hx1 hy1)
    · rw [TrivSqZeroExt.snd_add, mul_add]
      exact (Polynomial.degree_add_le _ _).trans (max_le hx2 hy2)
  zero_mem' := by simp
  smul_mem' := by
    rintro c x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · rw [TrivSqZeroExt.fst_smul]
      exact (Polynomial.degree_smul_le _ _).trans hx1
    · rw [TrivSqZeroExt.snd_smul, mul_smul_comm]
      exact (Polynomial.degree_smul_le _ _).trans hx2

theorem mem_W0 {r : ℕ} {x : D0} :
    x ∈ W0 r ↔ (TrivSqZeroExt.fst x).degree ≤ (r : WithBot ℕ) ∧
      (Polynomial.X * TrivSqZeroExt.snd x).degree ≤ (r : WithBot ℕ) := Iff.rfl

theorem W0_mono {a b : ℕ} (h : a ≤ b) : W0 a ≤ W0 b := by
  rintro x ⟨h1, h2⟩
  have hab : (a : WithBot ℕ) ≤ b := by exact_mod_cast h
  exact ⟨h1.trans hab, h2.trans hab⟩

theorem mul_mem_W0 {a b : ℕ} {x y : D0} (hx : x ∈ W0 a) (hy : y ∈ W0 b) : x * y ∈ W0 (a + b) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, ?_⟩
  · rw [TrivSqZeroExt.fst_mul]
    exact Polynomial.degree_mul_le_of_le hx1 hy1 |>.trans (by push_cast; rfl)
  · rw [TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_mul, mul_add]
    refine (Polynomial.degree_add_le _ _).trans (max_le ?_ ?_)
    · rw [← mul_assoc, mul_comm Polynomial.X, mul_assoc]
      exact Polynomial.degree_mul_le_of_le hx1 hy2 |>.trans (by push_cast; rfl)
    · rw [← mul_assoc]
      exact Polynomial.degree_mul_le_of_le hx2 hy1 |>.trans (by push_cast; rfl)

theorem inl_mem_W0 {p : P0} {r : ℕ} (hp : p.degree ≤ r) : (TrivSqZeroExt.inl p : D0) ∈ W0 r :=
  ⟨by rwa [TrivSqZeroExt.fst_inl], by simp⟩

theorem eps_mem_W0 : (DualNumber.eps : D0) ∈ W0 1 := by
  refine ⟨by simp, ?_⟩
  rw [DualNumber.snd_eps, mul_one]
  exact Polynomial.degree_X_le

theorem inlX_mem_W0 : (TrivSqZeroExt.inl Polynomial.X : D0) ∈ W0 1 :=
  inl_mem_W0 Polynomial.degree_X_le

theorem one_mem_W0 : (1 : D0) ∈ W0 0 := by
  rw [← TrivSqZeroExt.inl_one]
  exact inl_mem_W0 (by simp)

/-! ### Setting `α = 0` -/

/-- `Polynomial.map piA` as an algebra map. -/
abbrev mapA : Pl →ₐ[ℂ] P0 := Polynomial.mapAlgHom piA

/-- `α ↦ 0` on the dual numbers: `piA` on both components. -/
def Pi0 : DP →ₐ[ℂ] D0 :=
  TrivSqZeroExt.lift ((TrivSqZeroExt.inlAlgHom ℂ P0 P0).comp mapA)
    ((TrivSqZeroExt.inrHom P0 P0).restrictScalars ℂ ∘ₗ mapA.toLinearMap)
    (fun x y => TrivSqZeroExt.inr_mul_inr _ _ _)
    (fun r x => by
      change TrivSqZeroExt.inr ((r * x).map (piA : Cq →+* K0)) =
        TrivSqZeroExt.inl (r.map (piA : Cq →+* K0)) * TrivSqZeroExt.inr (x.map (piA : Cq →+* K0))
      rw [Polynomial.map_mul, TrivSqZeroExt.inl_mul_inr, smul_eq_mul])
    (fun r x => by
      change TrivSqZeroExt.inr ((x * r).map (piA : Cq →+* K0)) =
        TrivSqZeroExt.inr (x.map (piA : Cq →+* K0)) * TrivSqZeroExt.inl (r.map (piA : Cq →+* K0))
      rw [Polynomial.map_mul, TrivSqZeroExt.inr_mul_inl, op_smul_eq_mul])

theorem Pi0_fst (x : DP) : (Pi0 x).fst = (x.fst).map piA := by
  simp [Pi0, TrivSqZeroExt.lift_def]

theorem Pi0_snd (x : DP) : (Pi0 x).snd = (x.snd).map piA := by
  simp [Pi0, TrivSqZeroExt.lift_def]

theorem Pi0_inl (p : Pl) : Pi0 (TrivSqZeroExt.inl p) = TrivSqZeroExt.inl (p.map piA) := by
  ext <;> simp [Pi0_fst, Pi0_snd]

theorem Pi0_eps : Pi0 DualNumber.eps = DualNumber.eps := by
  ext <;> simp [Pi0_fst, Pi0_snd]

theorem Pi0_W {r : ℕ} {x : DP} (hx : x ∈ W r) : Pi0 x ∈ W0 r := by
  obtain ⟨h1, h2⟩ := mem_W.mp hx
  refine ⟨?_, ?_⟩
  · rw [Pi0_fst]
    exact (Polynomial.degree_map_le).trans h1
  · rw [Pi0_snd, ← Polynomial.map_X (piA : Cq →+* K0), ← Polynomial.map_mul]
    exact (Polynomial.degree_map_le).trans h2


/-! ### The specialisation of `ℂ[T_j]` at `α = 0` -/

/-- `A_m` at `α = 0`: `q_{m+1} + s q_m` (`r₀²` in place of `q₀`). -/
def a0 (m : ℕ) : P0 := (Aco m).map (piA : Cq →+* K0)

/-- `B_m` at `α = 0`: `(-s)^{m+1}`. -/
def b0 (m : ℕ) : P0 := (Bco m).map (piA : Cq →+* K0)

/-- `T_m ↦ A_m + ε B_m` at `α = 0`. -/
abbrev th0 : TPoly →ₐ[ℂ] D0 := InclLead.theta a0 b0

theorem Pi0_theta (F : TPoly) : Pi0 (InclLead.theta Aco Bco F) = th0 F := by
  have h : Pi0.comp (InclLead.theta Aco Bco) = th0 := by
    refine MvPolynomial.algHom_ext fun m => ?_
    simp only [AlgHom.coe_comp, Function.comp_apply, InclLead.theta, aeval_X, map_add, map_mul,
      Pi0_inl, Pi0_eps, a0, b0]
  exact congrArg (fun f : TPoly →ₐ[ℂ] D0 => f F) h

theorem natDegree_a0 (m : ℕ) : (a0 m).natDegree ≤ 1 :=
  (Polynomial.natDegree_map_le).trans (natDegree_Aco m)

theorem b0_eq (m : ℕ) : b0 m = Polynomial.C ((-1) ^ (m + 1)) * Polynomial.X ^ (m + 1) := by
  rw [b0, Bco_eq]
  simp [piA_al]

theorem natDegree_b0 (m : ℕ) : (b0 m).natDegree ≤ m + 1 := by
  rw [b0_eq]; exact Polynomial.natDegree_C_mul_X_pow_le _ _

theorem coeff_b0 (m : ℕ) : (b0 m).coeff (m + 1) = (-1) ^ (m + 1) := by
  rw [b0_eq, Polynomial.coeff_C_mul_X_pow, if_pos rfl]

theorem sb_a0 : InclLead.sb a0 = fun m => if m = 0 then (X 0 : K0) ^ 2 else X m := by
  funext m
  rw [InclLead.sb, a0, Polynomial.coeff_map]
  exact piA_sb m

theorem aeval_sb_a0 (F : TPoly) : aeval (InclLead.sb a0) F = InclLead.sqMap F := by
  rw [sb_a0, InclLead.sqMap]

/-! ### `α = 0` on the jet variables -/

/-- The constants `ℂ[s] ⊂ K0[s][ε]`. -/
def Cs : Subalgebra ℂ D0 :=
  ((TrivSqZeroExt.inlAlgHom ℂ P0 P0).comp
    (Polynomial.mapAlgHom (Algebra.ofId ℂ K0))).range

theorem Pi0_chiV_zero (j : ℕ) : Pi0 (chiV (0, j)) = 0 := by
  have h1 : (PowerSeries.coeff j (PowerSeries.C a2 * cS sv)).map (piA : Cq →+* K0) = 0 := by
    rw [PowerSeries.coeff_C_mul, Polynomial.map_mul, a2, Polynomial.map_C]
    simp [piA_al]
  have hη : cst ηS = PowerSeries.C (Polynomial.C al) * cst ξS := by
    rw [ηS, RingHom.map_mul, PowerSeries.map_C]
  have h2 : (PowerSeries.coeff j (cst ηS * bS sv)).map (piA : Cq →+* K0) = 0 := by
    rw [hη, mul_assoc, PowerSeries.coeff_C_mul, Polynomial.map_mul, Polynomial.map_C]
    simp [piA_al]
  have h0 : chiV (0, j) = DualNumber.eps * TrivSqZeroExt.inl
      (PowerSeries.coeff j (PowerSeries.C a2 * cS sv)) +
      TrivSqZeroExt.inl (PowerSeries.coeff j (cst ηS * bS sv)) := by
    simp [chiV]
  rw [h0, map_add, map_mul, Pi0_inl, Pi0_inl, Pi0_eps, h1, h2, TrivSqZeroExt.inl_zero, mul_zero,
    add_zero]

theorem Pi0_chiV_one (j : ℕ) : Pi0 (chiV (1, j)) ∈ Cs := by
  have h : chiV (1, j) = TrivSqZeroExt.inl (PowerSeries.coeff j (bS sv)) := by
    simp [chiV]
  rw [h, Pi0_inl, bS, PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff]
  refine ⟨Polynomial.C (Ring.choose (1 / 2 : ℂ) j) * Polynomial.X ^ j, ?_⟩
  change TrivSqZeroExt.inl _ = _
  congr 1
  rw [mul_smul_comm, mul_one, ← algebraMap_smul Cq, Polynomial.smul_eq_C_mul, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, sv, Polynomial.map_X]
  simp

theorem Pi0_chi_mem (a : JetPoly) : Pi0 (chi a) ∈ Cs := by
  induction a using MvPolynomial.induction_on with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes]
    exact Cs.algebraMap_mem c
  | add p q hp hq => rw [map_add, map_add]; exact Cs.add_mem hp hq
  | mul_X p x hp =>
    rw [map_mul, map_mul]
    refine Cs.mul_mem hp ?_
    rw [chi, aeval_X]
    obtain ⟨b, j⟩ := x
    fin_cases b
    · change Pi0 (chiV (0, j)) ∈ Cs
      rw [Pi0_chiV_zero]; exact Cs.zero_mem
    · exact Pi0_chiV_one j

/-! ### The shift identity -/

/-- `Θ(t) = Σ_m (A_m + ε B_m) t^m` at `α = 0`. -/
def Th : PowerSeries D0 := PowerSeries.mk fun m => th0 (X m)

theorem th0_X (m : ℕ) :
    th0 (X m) = TrivSqZeroExt.inl (a0 m) + DualNumber.eps * TrivSqZeroExt.inl (b0 m) := by
  simp [InclLead.theta]

theorem map_th0_tSer : PowerSeries.map th0.toRingHom tSer = Th := by
  refine PowerSeries.ext fun m => ?_
  simp [Th, tSer]

theorem th0_coeff_pow (n j : ℕ) :
    th0 (PowerSeries.coeff j (tSer ^ n)) = PowerSeries.coeff j (Th ^ n) := by
  rw [← map_th0_tSer, ← map_pow, PowerSeries.coeff_map]
  rfl

/-- The `ε`-free part of `Θ`. -/
def Aser : PowerSeries D0 := PowerSeries.mk fun m => TrivSqZeroExt.inl (a0 m)

/-- The `ε`-part of `Θ`. -/
def Bser : PowerSeries D0 := PowerSeries.mk fun m => TrivSqZeroExt.inl (b0 m)

theorem Th_eq : Th = Aser + PowerSeries.C DualNumber.eps * Bser := by
  refine PowerSeries.ext fun m => ?_
  rw [Th, Aser, Bser, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk, th0_X]

theorem Ceps_sq : (PowerSeries.C DualNumber.eps : PowerSeries D0) * PowerSeries.C DualNumber.eps
    = 0 := by
  rw [← map_mul, DualNumber.eps_mul_eps, map_zero]

theorem Th_pow (n : ℕ) : Th ^ n =
    Aser ^ n + PowerSeries.C DualNumber.eps * ((n : PowerSeries D0) * Aser ^ (n - 1) * Bser) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hA : (n : PowerSeries D0) * Aser ^ (n - 1) * Aser = (n : PowerSeries D0) * Aser ^ n := by
      rcases n with _ | n
      · simp
      · rw [Nat.add_sub_cancel, mul_assoc, ← pow_succ]
    rw [pow_succ, ih, Th_eq, Nat.add_sub_cancel]
    push_cast
    linear_combination (PowerSeries.C DualNumber.eps * Bser) * hA +
      ((n : PowerSeries D0) * Aser ^ (n - 1) * Bser * Bser) * Ceps_sq

theorem one_add_mul_Bser :
    (1 + PowerSeries.C (TrivSqZeroExt.inl Polynomial.X) * PowerSeries.X) * Bser =
      -PowerSeries.C (TrivSqZeroExt.inl Polynomial.X : D0) := by
  refine PowerSeries.ext fun m => ?_
  rw [add_mul, one_mul, mul_assoc, map_add, PowerSeries.coeff_C_mul, map_neg,
    PowerSeries.coeff_C]
  rcases m with _ | m
  · rw [PowerSeries.coeff_zero_X_mul, mul_zero, add_zero, if_pos rfl, Bser, PowerSeries.coeff_mk,
      b0_eq]
    simp
  · rw [PowerSeries.coeff_succ_X_mul, if_neg (Nat.succ_ne_zero m), neg_zero, Bser,
      PowerSeries.coeff_mk, PowerSeries.coeff_mk, b0_eq, b0_eq, ← TrivSqZeroExt.inl_mul,
      ← TrivSqZeroExt.inl_add, ← TrivSqZeroExt.inl_zero]
    congr 1
    rw [pow_succ (-1 : K0) (m + 1), pow_succ (Polynomial.X : P0) (m + 1)]
    simp only [map_mul, map_neg, map_one]
    ring

/-- All coefficients lie in `W0 d`. -/
def InW0 (d : ℕ) (f : PowerSeries D0) : Prop := ∀ m, PowerSeries.coeff m f ∈ W0 d

theorem InW0.mono {a b : ℕ} {f : PowerSeries D0} (hf : InW0 a f) (h : a ≤ b) : InW0 b f :=
  fun m => W0_mono h (hf m)

theorem InW0.mul {a b : ℕ} {f g : PowerSeries D0} (hf : InW0 a f) (hg : InW0 b g) :
    InW0 (a + b) (f * g) := fun m => by
  rw [PowerSeries.coeff_mul]
  exact Submodule.sum_mem _ fun p _ => mul_mem_W0 (hf p.1) (hg p.2)

theorem InW0.add {a : ℕ} {f g : PowerSeries D0} (hf : InW0 a f) (hg : InW0 a g) :
    InW0 a (f + g) := fun m => by
  rw [map_add]; exact add_mem (hf m) (hg m)

theorem InW0.neg {a : ℕ} {f : PowerSeries D0} (hf : InW0 a f) : InW0 a (-f) := fun m => by
  rw [map_neg]; exact neg_mem (hf m)

theorem inW0_C {a : ℕ} {x : D0} (hx : x ∈ W0 a) : InW0 a (PowerSeries.C x) := fun m => by
  rw [PowerSeries.coeff_C]
  split_ifs
  · exact hx
  · exact Submodule.zero_mem _

theorem inW0_one : InW0 0 (1 : PowerSeries D0) := by
  rw [← map_one PowerSeries.C]; exact inW0_C one_mem_W0

theorem inW0_natCast (n : ℕ) : InW0 0 (n : PowerSeries D0) := by
  rw [← map_natCast PowerSeries.C]
  refine inW0_C ?_
  rw [← nsmul_one]
  exact Submodule.smul_of_tower_mem _ n one_mem_W0

theorem inW0_X : InW0 0 (PowerSeries.X : PowerSeries D0) := fun m => by
  rw [PowerSeries.coeff_X]
  split_ifs
  · exact one_mem_W0
  · exact Submodule.zero_mem _

theorem inW0_Aser : InW0 1 Aser := fun m => by
  rw [Aser, PowerSeries.coeff_mk]
  exact inl_mem_W0 ((Polynomial.degree_le_natDegree).trans (by exact_mod_cast natDegree_a0 m))

theorem inW0_Aser_pow : ∀ n : ℕ, InW0 n (Aser ^ n)
  | 0 => by rw [pow_zero]; exact inW0_one
  | n + 1 => by rw [pow_succ]; exact (inW0_Aser_pow n).mul inW0_Aser

/-- **The shift identity**: `s Θⁿ_j + Θⁿ_{j+1}` lies in `W0 (n + 1)`. -/
theorem shift_mem (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    TrivSqZeroExt.inl Polynomial.X * PowerSeries.coeff j (Th ^ n) +
      PowerSeries.coeff (j + 1) (Th ^ n) ∈ W0 (n + 1) := by
  have h1 : TrivSqZeroExt.inl Polynomial.X * PowerSeries.coeff j (Th ^ n) +
      PowerSeries.coeff (j + 1) (Th ^ n) = PowerSeries.coeff (j + 1)
        ((1 + PowerSeries.C (TrivSqZeroExt.inl Polynomial.X) * PowerSeries.X) * Th ^ n) := by
    rw [add_mul, one_mul, mul_assoc, map_add, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, add_comm]
  have h2 : (1 + PowerSeries.C (TrivSqZeroExt.inl Polynomial.X) * PowerSeries.X) * Th ^ n =
      (1 + PowerSeries.C (TrivSqZeroExt.inl Polynomial.X) * PowerSeries.X) * Aser ^ n -
        PowerSeries.C DualNumber.eps * ((n : PowerSeries D0) * Aser ^ (n - 1) *
          PowerSeries.C (TrivSqZeroExt.inl Polynomial.X)) := by
    rw [Th_pow]
    linear_combination (PowerSeries.C DualNumber.eps * ((n : PowerSeries D0) * Aser ^ (n - 1))) *
      one_add_mul_Bser
  rw [h1, h2]
  have hS : InW0 1 (1 + PowerSeries.C (TrivSqZeroExt.inl Polynomial.X : D0) * PowerSeries.X) :=
    (inW0_one.mono (Nat.zero_le 1)).add ((inW0_C inlX_mem_W0).mul inW0_X)
  have hT1 : InW0 (n + 1) ((1 + PowerSeries.C (TrivSqZeroExt.inl Polynomial.X) *
      PowerSeries.X) * Aser ^ n) := by
    have := hS.mul (inW0_Aser_pow n)
    rwa [add_comm] at this
  have hT2 : InW0 (n + 1) (PowerSeries.C DualNumber.eps * ((n : PowerSeries D0) *
      Aser ^ (n - 1) * PowerSeries.C (TrivSqZeroExt.inl Polynomial.X))) := by
    have := (inW0_C eps_mem_W0).mul (((inW0_natCast n).mul (inW0_Aser_pow (n - 1))).mul
      (inW0_C inlX_mem_W0))
    rwa [show 1 + (0 + (n - 1) + 1) = n + 1 by omega] at this
  exact (hT1.add hT2.neg) (j + 1) |> fun h => by rwa [sub_eq_add_neg]

/-- **Iterated shift**: `s^w Θⁿ_j ≡ (-1)^w Θⁿ_{j+w}` modulo `W0 (n + w)`. -/
theorem shift_iter (n : ℕ) (hn : 1 ≤ n) : ∀ w j : ℕ,
    TrivSqZeroExt.inl Polynomial.X ^ w * PowerSeries.coeff j (Th ^ n) -
      (-1) ^ w * PowerSeries.coeff (j + w) (Th ^ n) ∈ W0 (n + w)
  | 0, j => by simp
  | w + 1, j => by
    have h1 := mul_mem_W0 inlX_mem_W0 (shift_iter n hn w j)
    have h2 := W0_mono (show n + 1 ≤ n + (w + 1) by omega) (shift_mem n hn (j + w))
    have h3 : (-1 : D0) ^ w * (TrivSqZeroExt.inl Polynomial.X * PowerSeries.coeff (j + w)
        (Th ^ n) + PowerSeries.coeff (j + w + 1) (Th ^ n)) ∈ W0 (n + (w + 1)) := by
      rw [show ∀ y : D0, (-1 : D0) ^ w * y = ((-1 : ℂ) ^ w) • y from fun y => by
        rw [Algebra.smul_def]; simp]
      exact Submodule.smul_mem _ _ h2
    rw [show 1 + (n + w) = n + (w + 1) by ring] at h1
    convert add_mem h1 h3 using 1
    rw [show j + (w + 1) = j + w + 1 by ring]
    ring

/-! ### The test ideal through `chi`, keeping the multipliers -/

/-- The `ℂ`-span of `chi(a) · θ(jets of Tⁿ)`. -/
def Mchi (n : ℕ) : Submodule ℂ DP :=
  Submodule.span ℂ {z | ∃ (a : JetPoly) (j : ℕ),
    z = chi a * InclLead.theta Aco Bco (PowerSeries.coeff j (tSer ^ n))}

theorem chi_tco_eq : (fun m => chi (tco m)) = fun m =>
    TrivSqZeroExt.inl a2 * (TrivSqZeroExt.inl (Aco m) +
      DualNumber.eps * TrivSqZeroExt.inl (Bco m)) := funext chi_tSug

theorem chi_aeval_tco {k : ℕ} {F : TPoly} (hF : F ∈ tDeg k) :
    chi (aeval tco F) = TrivSqZeroExt.inl a2 ^ k * InclLead.theta Aco Bco F := by
  rw [MvPolynomial.comp_aeval_apply, chi_tco_eq, aeval_mul_tDeg _ _ hF]
  rfl

theorem chi_gen (n j : ℕ) : chi (PowerSeries.coeff j (testSer ^ n)) =
    TrivSqZeroExt.inl a2 ^ n * InclLead.theta Aco Bco (PowerSeries.coeff j (tSer ^ n)) := by
  rw [← aeval_tco_coeff_pow]
  exact chi_aeval_tco (coeff_tSer_pow_mem_tDeg n j)

theorem chi_mul_mem_Mchi {n : ℕ} (a : JetPoly) {z : DP} (hz : z ∈ Mchi n) :
    chi a * z ∈ Mchi n := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, j, rfl⟩ := hx
    exact Submodule.subset_span ⟨a * b, j, by rw [map_mul, mul_assoc]⟩
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

/-- **The test ideal through `chi`**: `chi(x) = α^{2n} Z` with `Z` a combination of
`chi(a) · θ(jets of Tⁿ)`. -/
theorem chi_testIdeal_Mchi {n : ℕ} {x : JetPoly} (hx : x ∈ testIdeal n) :
    ∃ Z ∈ Mchi n, chi x = TrivSqZeroExt.inl a2 ^ n * Z := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    refine ⟨InclLead.theta Aco Bco (PowerSeries.coeff j (tSer ^ n)),
      Submodule.subset_span ⟨1, j, by rw [map_one, one_mul]⟩, chi_gen n j⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by rw [map_zero, mul_zero]⟩
  | add y z _ _ hy hz =>
    obtain ⟨Y, hY, hy⟩ := hy
    obtain ⟨Z, hZ, hz⟩ := hz
    exact ⟨Y + Z, add_mem hY hZ, by rw [map_add, hy, hz, mul_add]⟩
  | smul a y _ hy =>
    obtain ⟨Y, hY, hy⟩ := hy
    refine ⟨chi a * Y, chi_mul_mem_Mchi a hY, ?_⟩
    rw [smul_eq_mul, map_mul, hy]
    ring

/-- The cancellation of `α^{2n}` in `W r`. -/
theorem mem_W_of_mul {n r : ℕ} {Y : DP} (h : TrivSqZeroExt.inl a2 ^ n * Y ∈ W r) : Y ∈ W r := by
  obtain ⟨h1, h2⟩ := mem_W.mp h
  have hc : (al ^ (2 * n) : Cq) ≠ 0 := pow_ne_zero _ (X_ne_zero _)
  have he : (TrivSqZeroExt.inl a2 ^ n : DP) = TrivSqZeroExt.inl (Polynomial.C (al ^ (2 * n))) := by
    rw [TrivSqZeroExt.inl_pow, a2, ← map_pow, ← pow_mul]
  rw [he, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, Polynomial.degree_C_mul hc] at h1
  rw [he, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inl, smul_zero, add_zero,
    TrivSqZeroExt.fst_inl, smul_eq_mul, mul_left_comm, Polynomial.degree_C_mul hc] at h2
  exact mem_W.mpr ⟨h1, h2⟩

/-- The `ℂ`-span of `p(s) · θ0(jets of Tⁿ)`, `p ∈ ℂ[s]`. -/
def M0 (n : ℕ) : Submodule ℂ D0 :=
  Submodule.span ℂ {z | ∃ (p : Polynomial ℂ) (j : ℕ),
    z = TrivSqZeroExt.inl (p.map (algebraMap ℂ K0)) * th0 (PowerSeries.coeff j (tSer ^ n))}

theorem Pi0_Mchi {n : ℕ} {Z : DP} (hZ : Z ∈ Mchi n) : Pi0 Z ∈ M0 n := by
  have h : (Mchi n).map Pi0.toLinearMap ≤ M0 n := by
    rw [Mchi, Submodule.map_span_le]
    rintro _ ⟨a, j, rfl⟩
    obtain ⟨p, hp⟩ := Pi0_chi_mem a
    refine Submodule.subset_span ⟨p, j, ?_⟩
    rw [AlgHom.toLinearMap_apply, map_mul, Pi0_theta, ← hp]
    rfl
  exact h (Submodule.mem_map_of_mem hZ)

/-! ### Normal form of `M0` modulo `W0 (n + N)` -/

/-- `s` in `K0[s][ε]`. -/
abbrev sD : D0 := TrivSqZeroExt.inl Polynomial.X

/-- The decomposition property: `z ≡ θ0(G) + s^{N+1} H(s)` modulo `W0 (n + N)`, with `G` and the
coefficients of `H` combinations of jets of `Tⁿ`. -/
def Decomp (n N : ℕ) (z : D0) : Prop :=
  ∃ G ∈ jetSpanT n, ∃ H : Polynomial TPoly, (∀ i, H.coeff i ∈ jetSpanT n) ∧
    z - th0 G - sD ^ (N + 1) * Polynomial.eval₂ th0.toRingHom sD H ∈ W0 (n + N)

theorem Decomp.add {n N : ℕ} {z z' : D0} (h : Decomp n N z) (h' : Decomp n N z') :
    Decomp n N (z + z') := by
  obtain ⟨G, hG, H, hH, hz⟩ := h
  obtain ⟨G', hG', H', hH', hz'⟩ := h'
  refine ⟨G + G', add_mem hG hG', H + H', fun i => ?_, ?_⟩
  · rw [Polynomial.coeff_add]; exact add_mem (hH i) (hH' i)
  · convert add_mem hz hz' using 1
    rw [map_add, Polynomial.eval₂_add]
    ring

theorem Decomp.smul {n N : ℕ} {z : D0} (c : ℂ) (h : Decomp n N z) : Decomp n N (c • z) := by
  obtain ⟨G, hG, H, hH, hz⟩ := h
  refine ⟨c • G, Submodule.smul_mem _ c hG, Polynomial.C (algebraMap ℂ TPoly c) * H, fun i => ?_,
    ?_⟩
  · rw [Polynomial.coeff_C_mul, ← Algebra.smul_def]; exact Submodule.smul_mem _ c (hH i)
  · convert Submodule.smul_mem _ c hz using 1
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, map_smul, smul_sub, smul_sub]
    congr 1
    change sD ^ (N + 1) * (th0 (algebraMap ℂ TPoly c) * _) = _
    rw [AlgHom.commutes, ← Algebra.smul_def, mul_smul_comm]

theorem Decomp.zero (n N : ℕ) : Decomp n N 0 :=
  ⟨0, Submodule.zero_mem _, 0, fun i => by simp, by simp⟩

theorem inl_monomial (i : ℕ) (c : ℂ) :
    (TrivSqZeroExt.inl ((Polynomial.monomial i c).map (algebraMap ℂ K0)) : D0) = c • sD ^ i := by
  rw [Polynomial.map_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, TrivSqZeroExt.inl_mul,
    TrivSqZeroExt.inl_pow, Algebra.smul_def]
  rfl

theorem decomp_monomial (n N : ℕ) (hn : 1 ≤ n) (i : ℕ) (c : ℂ) (j : ℕ) :
    Decomp n N (TrivSqZeroExt.inl ((Polynomial.monomial i c).map (algebraMap ℂ K0)) *
      th0 (PowerSeries.coeff j (tSer ^ n))) := by
  rw [inl_monomial, th0_coeff_pow]
  rcases Nat.lt_or_ge N i with hi | hi
  · refine ⟨0, Submodule.zero_mem _, Polynomial.monomial (i - (N + 1))
      (c • PowerSeries.coeff j (tSer ^ n)), fun l => ?_, ?_⟩
    · rw [Polynomial.coeff_monomial]
      split_ifs
      · exact Submodule.smul_mem _ c (Submodule.subset_span ⟨j, rfl⟩)
      · exact Submodule.zero_mem _
    · rw [Polynomial.eval₂_monomial, map_zero, sub_zero]
      change _ - sD ^ (N + 1) * (th0 (c • PowerSeries.coeff j (tSer ^ n)) * _) ∈ _
      rw [map_smul, th0_coeff_pow]
      convert Submodule.zero_mem (W0 (n + N)) using 1
      rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, ← mul_assoc]
      have hp : sD ^ i = sD ^ (N + 1) * sD ^ (i - (N + 1)) := by
        rw [← pow_add, show N + 1 + (i - (N + 1)) = i by omega]
      rw [hp, sub_eq_zero]
      congr 1
      ring
  · refine ⟨(c * (-1) ^ i) • PowerSeries.coeff (j + i) (tSer ^ n),
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j + i, rfl⟩), 0, fun l => by simp, ?_⟩
    rw [Polynomial.eval₂_zero, mul_zero, sub_zero, map_smul, th0_coeff_pow]
    have h := W0_mono (show n + i ≤ n + N by omega) (shift_iter n hn i j)
    convert Submodule.smul_mem _ c h using 1
    rw [smul_sub, mul_smul, smul_mul_assoc]
    congr 1
    rw [show ∀ y : D0, ((-1 : ℂ) ^ i) • y = (-1 : D0) ^ i * y from fun y => by
      rw [Algebra.smul_def]; simp]

/-- **Every element of `M0` has the normal form `θ0(G) + s^{N+1} H(s)` modulo `W0 (n + N)`.** -/
theorem decomp_of_mem_M0 (n N : ℕ) (hn : 1 ≤ n) {z : D0} (hz : z ∈ M0 n) : Decomp n N z := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, j, rfl⟩ := hx
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [Polynomial.map_add, TrivSqZeroExt.inl_add, add_mul]; exact hp.add hq
    | monomial i c => exact decomp_monomial n N hn i c j
  | zero => exact Decomp.zero n N
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

/-! ### Leading coefficients at `α = 0` -/

/-- The `ε`-free part of `θ0(F)` for `F` of `T`-degree `k`: degree `≤ k`, top coefficient
`F(r₀², q₁, q₂, …)`. -/
theorem lead_fst {k : ℕ} {F : TPoly} (hF : F ∈ tDeg k) :
    (th0 F).fst.natDegree ≤ k ∧ (th0 F).fst.coeff k = InclLead.sqMap F := by
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, rfl, rfl⟩ := hP
    obtain ⟨h1, h2, -, -⟩ := InclLead.lead_list a0 b0 natDegree_a0 natDegree_b0 coeff_b0 l.sum l
      (fun x hx => List.le_sum_of_mem hx)
    exact ⟨h1, by rw [h2, aeval_sb_a0]⟩
  | zero => simp
  | add P Q _ _ hP hQ =>
    refine ⟨?_, ?_⟩
    · rw [map_add, TrivSqZeroExt.fst_add]
      exact (Polynomial.natDegree_add_le _ _).trans (max_le hP.1 hQ.1)
    · rw [map_add, TrivSqZeroExt.fst_add, Polynomial.coeff_add, hP.2, hQ.2, map_add]
  | smul c P _ hP =>
    refine ⟨?_, ?_⟩
    · rw [map_smul, TrivSqZeroExt.fst_smul]
      exact (Polynomial.natDegree_smul_le _ _).trans hP.1
    · rw [map_smul, TrivSqZeroExt.fst_smul, Polynomial.coeff_smul, hP.2, map_smul]

theorem fst_eval₂ (H : Polynomial TPoly) :
    (Polynomial.eval₂ th0.toRingHom sD H).fst =
      Polynomial.eval₂ ((TrivSqZeroExt.fstHom ℂ P0 P0).toRingHom.comp th0.toRingHom)
        Polynomial.X H := by
  have := Polynomial.hom_eval₂ H th0.toRingHom (TrivSqZeroExt.fstHom ℂ P0 P0).toRingHom sD
  simpa using this

/-- **The high part vanishes**: if `θ0(F) + s^{N+1} H(s) ∈ W0 (n + N)` with `F` and all
coefficients of `H` of `T`-degree `n`, then `H = 0`. -/
theorem high_eq_zero {n N : ℕ} {F : TPoly} (hF : F ∈ tDeg n) {H : Polynomial TPoly}
    (hH : ∀ i, H.coeff i ∈ tDeg n)
    (h : th0 F + sD ^ (N + 1) * Polynomial.eval₂ th0.toRingHom sD H ∈ W0 (n + N)) : H = 0 := by
  by_contra hne
  set d := H.natDegree
  have hlead : H.coeff d ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  have hdeg := (mem_W0.mp h).1
  have hc : (TrivSqZeroExt.fst (th0 F + sD ^ (N + 1) *
      Polynomial.eval₂ th0.toRingHom sD H)).coeff (n + N + 1 + d) = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hdeg (by exact_mod_cast (by omega)))
  rw [TrivSqZeroExt.fst_add, Polynomial.coeff_add, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow,
    TrivSqZeroExt.fst_inl, fst_eval₂, Polynomial.eval₂_eq_sum_range,
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (lead_fst hF).1 (by omega)),
    zero_add, show n + N + 1 + d = (N + 1) + (n + d) by ring, Polynomial.coeff_X_pow_mul',
    if_pos (by omega), show N + 1 + (n + d) - (N + 1) = n + d by omega,
    Polynomial.finsetSum_coeff, Finset.sum_eq_single d] at hc
  · rw [RingHom.comp_apply, Polynomial.coeff_mul_X_pow] at hc
    change (th0 (H.coeff d)).fst.coeff n = 0 at hc
    rw [(lead_fst (hH d)).2] at hc
    exact hlead (InclLead.aeval_sq_injective (hc.trans (map_zero _).symm))
  · intro i hi hid
    have hid' : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hid
    rw [RingHom.comp_apply, Polynomial.coeff_mul_X_pow', if_pos (by omega)]
    change (th0 (H.coeff i)).fst.coeff (n + d - i) = 0
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (lead_fst (hH i)).1 (by omega))
  · intro hd
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self d)) hd

/-- **Letters-only sharpness at `α = 0`**: `θ0(F) ∈ W0 (N + k)` for `F` of `T`-degree `k` forces
every jet of `F` to be `< N`. -/
theorem vars_lt_of_W0 {N k : ℕ} {F : TPoly} (hF : F ∈ tDeg k) (h : th0 F ∈ W0 (N + k)) :
    ∀ m ∈ F.vars, m < N := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m0, hm0, hm0N⟩ := hcon
  have hne : F.vars.Nonempty := ⟨m0, hm0⟩
  have hMmem : F.vars.max' hne ∈ F.vars := Finset.max'_mem _ _
  have hMle : ∀ m ∈ F.vars, m ≤ F.vars.max' hne := fun m hm => Finset.le_max' _ _ hm
  have hNM : N ≤ F.vars.max' hne := le_trans hm0N (hMle m0 hm0)
  have hFV : F ∈ InclLead.V (F.vars.max' hne) k := by
    have := cut_tDeg_le_V (F.vars.max' hne) k (Submodule.mem_map.mpr ⟨F, hF, rfl⟩)
    rwa [AlgHom.toLinearMap_apply, cut_eq_self (fun m hm => hMle m hm)] at this
  obtain ⟨-, hlead⟩ := InclLead.lead_span a0 b0 natDegree_a0 natDegree_b0 coeff_b0 hFV
  have h0 : (th0 F).snd.coeff (k + F.vars.max' hne) = 0 := by
    have h2 := (mem_W0.mp h).2
    rw [← Polynomial.coeff_X_mul]
    exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_le_of_lt h2 (by exact_mod_cast (by omega)))
  rw [hlead, aeval_sb_a0] at h0
  have hpd : InclLead.sqMap (pderiv (F.vars.max' hne) F) = 0 :=
    (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  exact InclLead.not_mem_vars_of_pderiv_eq_zero
    (InclLead.aeval_sq_injective (hpd.trans (map_zero _).symm)) hMmem

/-! ### The weight grading of `ℂ[T_j]` -/

/-- The weight `T_m ↦ m + 1`. -/
abbrev wT : ℕ → ℕ := fun m => m + 1

/-- The weight-`E` component. -/
abbrev pw (E : ℕ) : TPoly →ₗ[ℂ] TPoly := weightedHomogeneousComponent wT E

theorem isWH_listProd : ∀ l : List ℕ,
    IsWeightedHomogeneous wT ((l.map X).prod : TPoly) (l.map fun m => m + 1).sum
  | [] => by simpa using isWeightedHomogeneous_one (R := ℂ) wT
  | x :: l => by
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons]
    exact (isWeightedHomogeneous_X ℂ wT x).mul (isWH_listProd l)

theorem pw_tMonW {k E : ℕ} {F : TPoly} (hF : F ∈ tMonW TPoly X k (E : ℤ)) : pw E F = F := by
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, -, he, rfl⟩ := hP
    have he' : (l.map fun m => m + 1).sum = E := by exact_mod_cast he
    exact (he' ▸ isWH_listProd l).weightedHomogeneousComponent_same
  | zero => exact map_zero _
  | add P Q _ _ hP hQ => rw [map_add, hP, hQ]
  | smul c P _ hP => rw [map_smul, hP]

theorem pw_tDeg {k : ℕ} (E : ℕ) {F : TPoly} (hF : F ∈ tDeg k) :
    pw E F ∈ tMonW TPoly X k (E : ℤ) := by
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    by_cases he : (l.map fun m => m + 1).sum = E
    · have h := isWH_listProd l
      rw [he] at h
      rw [h.weightedHomogeneousComponent_same]
      exact Submodule.subset_span ⟨l, hl, by exact_mod_cast he, rfl⟩
    · rw [(isWH_listProd l).weightedHomogeneousComponent_ne E (fun h => he h.symm)]
      exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add P Q _ _ hP hQ => rw [map_add]; exact add_mem hP hQ
  | smul c P _ hP => rw [map_smul]; exact Submodule.smul_mem _ c hP

theorem coeff_tSer_pow_isWH : ∀ n j : ℕ,
    IsWeightedHomogeneous wT (PowerSeries.coeff j (tSer ^ n)) (j + n)
  | 0, j => by
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs with h
    · subst h; exact isWeightedHomogeneous_one ℂ wT
    · exact isWeightedHomogeneous_zero ℂ wT _
  | n + 1, j => by
    rw [pow_succ, PowerSeries.coeff_mul]
    refine IsWeightedHomogeneous.sum _ _ _ fun p hp => ?_
    have hpj := Finset.mem_antidiagonal.mp hp
    rw [tSer, PowerSeries.coeff_mk]
    have := (coeff_tSer_pow_isWH n p.1).mul (isWeightedHomogeneous_X ℂ wT p.2)
    convert this using 1
    simp only [wT]
    omega

theorem pw_jetSpanT {n : ℕ} (E : ℕ) {G : TPoly} (hG : G ∈ jetSpanT n) : pw E G ∈ jetSpanT n := by
  induction hG using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨j, rfl⟩ := hP
    by_cases he : E = j + n
    · rw [he, (coeff_tSer_pow_isWH n j).weightedHomogeneousComponent_same]
      exact Submodule.subset_span ⟨j, rfl⟩
    · rw [(coeff_tSer_pow_isWH n j).weightedHomogeneousComponent_ne E he]
      exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add P Q _ _ hP hQ => rw [map_add]; exact add_mem hP hQ
  | smul c P _ hP => rw [map_smul]; exact Submodule.smul_mem _ c hP

theorem vars_pw_subset (E : ℕ) (F : TPoly) {m : ℕ} (hm : m ∈ (pw E F).vars) : m ∈ F.vars := by
  rw [mem_vars_iff_mem_support] at hm ⊢
  obtain ⟨d, hd, hmd⟩ := hm
  rw [support_weightedHomogeneousComponent, Finset.mem_filter] at hd
  exact ⟨d, hd.1, hmd⟩

/-! ### The slots of `T`-degree `n` -/

/-- **Every slot of `BoxInclusion n r` with `T`-degree exactly `n`** (any `N`): a test-passing
`τ ∈ R_n` of `T`-degree `n` lies in the box. -/
theorem boxInclusion_degN {n r : ℕ} (hn : 1 ≤ n) (d : ℤ) (N : ℕ) (hk : r - N = n) (hNr : N < r) :
    tMonW (Rn n) (tn n) (r - N) (d - r) ⊓ testSp n r N ≤ boxW (tn n) N (r - N) (d - r) := by
  rintro τ ⟨hτ, hT⟩
  rcases lt_or_ge (d - r) 0 with hneg | hpos
  · rw [tMonW_neg _ _ hneg] at hτ
    have h0 : τ = 0 := by simpa using hτ
    rw [h0]; exact Submodule.zero_mem _
  obtain ⟨E, hE⟩ : ∃ E : ℕ, d - r = (E : ℤ) := ⟨(d - r).toNat, (Int.toNat_of_nonneg hpos).symm⟩
  rw [hE] at hτ ⊢
  rw [hk] at hτ ⊢
  have hr : r = N + n := by omega
  rw [tMonW_Rn_eq] at hτ
  obtain ⟨F, hF, rfl⟩ := Submodule.mem_map.mp hτ
  rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk] at hT ⊢
  rw [SetLike.mem_coe, mem_testSp, ψn_mk, ← map_pow, ← map_mul, testLetters_eq,
    ← Submodule.map_pow] at hT
  obtain ⟨y, hy, hyP⟩ := hT
  rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hyP
  obtain ⟨Z, hZM, hZ⟩ := chi_testIdeal_Mchi hyP
  have hFd : F ∈ tDeg n := tMonW_le_tDeg _ _ hF
  rw [map_sub, map_mul, map_pow, chi_v0, one_pow, mul_one, chi_aeval_tco hFd] at hZ
  have hW : InclLead.theta Aco Bco F + Z ∈ W r := by
    refine mem_W_of_mul (n := n) ?_
    rw [mul_add, ← hZ, add_sub_cancel]
    exact chi_Lpoly_pow r hy
  have hW0 := Pi0_W hW
  rw [map_add, Pi0_theta] at hW0
  obtain ⟨G, hG, H, hH, hdec⟩ := decomp_of_mem_M0 n N hn (Pi0_Mchi hZM)
  have hsum : th0 (F + G) + sD ^ (N + 1) * Polynomial.eval₂ th0.toRingHom sD H ∈ W0 (n + N) := by
    have := sub_mem (W0_mono (show r ≤ n + N by omega) hW0) hdec
    convert this using 1
    rw [map_add]
    ring
  have hFG : F + G ∈ tDeg n := add_mem hFd (jetSpanT_le_tDeg n hG)
  have hH0 := high_eq_zero hFG (fun i => jetSpanT_le_tDeg n (hH i)) hsum
  rw [hH0, Polynomial.eval₂_zero, mul_zero, add_zero, add_comm n N] at hsum
  have hvars := vars_lt_of_W0 hFG hsum
  -- project to weight `E`
  have hpF : pw E (F + G) = F + pw E G := by rw [map_add, pw_tMonW hF]
  have hbox : F + pw E G ∈ boxW X N n (E : ℤ) := by
    rw [← hpF]
    have := cut_tMonW_le_boxW N n (E : ℤ) (Submodule.mem_map.mpr ⟨_, pw_tDeg E hFG, rfl⟩)
    rwa [AlgHom.toLinearMap_apply,
      cut_eq_self (fun m hm => hvars m (vars_pw_subset E _ hm))] at this
  have hmk : Ideal.Quotient.mk (jetIdealT n) F =
      Ideal.Quotient.mk (jetIdealT n) (F + pw E G) := by
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr
      (jetSpanT_le_jetIdealT n (pw_jetSpanT E hG)), add_zero]
  rw [hmk]
  exact boxW_map n N n (E : ℤ) (Submodule.mem_map.mpr ⟨_, hbox, rfl⟩)

/-- `BoxSingularTail` in the slots of `T`-degree exactly `n`. -/
theorem boxSingularTail_degN {n r : ℕ} (hn : 1 ≤ n) (d : ℤ) (N : ℕ) (hNr : N < r)
    (hk : r - N = n) (τ : Rn n) (hτ : τ ∈ tMonW (Rn n) (tn n) (r - N) (d - r) ⊓ testSp n r N) :
    τ ∈ boxW (tn n) N (r - N) (d - r) :=
  boxInclusion_degN hn d N hk hNr hτ

/-! ### `n = 1`: `R_1 = ℂ` -/

theorem tn_one (m : ℕ) : tn 1 m = 0 := by
  rw [tn, Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.subset_span ⟨m, ?_⟩
  simp [tSer]

theorem tMonW_one_eq_bot {k : ℕ} (hk : 1 ≤ k) (e : ℤ) : tMonW (Rn 1) (tn 1) k e = ⊥ := by
  rw [tMonW, Submodule.span_eq_bot]
  rintro _ ⟨l, hl, -, rfl⟩
  obtain ⟨x, l', rfl⟩ : ∃ x l', l = x :: l' := by
    rcases l with _ | ⟨x, l'⟩
    · simp at hl; omega
    · exact ⟨x, l', rfl⟩
  rw [List.map_cons, List.prod_cons, tn_one, zero_mul]

end LiftDegN

open LiftDegN SingTailLift TailWitt

/-- **The ideal-elimination input in the slots of `T`-degree `> n`**: `SingularLift` restricted to
the slots with `r - N > n` (the slots with `r - N = n` are proved, `boxInclusion_degN`). -/
def SingularLiftHigh (n r : ℕ) : Prop :=
  ∀ (d : ℤ) (N : ℕ), N < r → n < r - N → ∀ τ : Rn n,
    τ ∈ tMonW (Rn n) (tn n) (r - N) (d - r) ⊓ testSp n r N →
    (∀ j : ℕ, 1 ≤ j → dR n j τ ∈ boxW (tn n) N (r - N) (d - r - j)) →
    ∃ F ∈ tMonW TPoly X (r - N) (d - r), Ideal.Quotient.mk (jetIdealT n) F = τ ∧
      aeval tco F * X (1, 0) ^ (2 * N) ∈ InclLow.Lpoly ^ r

/-- **The Witt-singular tail in the slots of `T`-degree `> n`.** -/
def BoxSingularTailHigh (n r : ℕ) : Prop :=
  ∀ (d : ℤ) (N : ℕ), N < r → n < r - N → ∀ τ : Rn n,
    τ ∈ tMonW (Rn n) (tn n) (r - N) (d - r) ⊓ testSp n r N →
    (∀ j : ℕ, 1 ≤ j → dR n j τ ∈ boxW (tn n) N (r - N) (d - r - j)) →
    τ ∈ boxW (tn n) N (r - N) (d - r)

/-- `SingularLift` implies its high part. -/
theorem singularLiftHigh_of_singularLift {n r : ℕ} (h : SingularLift n r) : SingularLiftHigh n r :=
  fun d N hN hk => h d N hN hk.le

/-- **`BoxSingularTailHigh` from ideal elimination in the high slots.** -/
theorem boxSingularTailHigh_of_singularLiftHigh {n r : ℕ} (h : SingularLiftHigh n r) :
    BoxSingularTailHigh n r := by
  intro d N hN hk τ hτ hsing
  obtain ⟨F, hF, rfl, hL⟩ := h d N hN hk τ hτ hsing
  have hL' : aeval tco F * X (1, 0) ^ (2 * N) ∈ InclLow.Lpoly ^ (N + (r - N)) := by
    rwa [show N + (r - N) = r by omega]
  exact InclLow.boxW_map n N (r - N) (d - r)
    (Submodule.mem_map.mpr ⟨F, mem_boxW_of_mem_Lpoly_pow hF hL', rfl⟩)

/-- **`BoxSingularTail` from its high slots** (the `T`-degree-`n` slots are proved). -/
theorem boxSingularTail_of_high {n r : ℕ} (hn : 1 ≤ n) (h : BoxSingularTailHigh n r) :
    BoxSingularTail n r := by
  intro d N hN hk τ hτ hsing
  rcases Nat.lt_or_ge n (r - N) with hlt | hge
  · exact h d N hN hlt τ hτ hsing
  · exact boxSingularTail_degN hn d N hN (le_antisymm hge hk) τ hτ

/-- **`BoxSingularTail 1 r` for every `r`**: `R_1 = ℂ`. -/
theorem boxSingularTail_one (r : ℕ) : BoxSingularTail 1 r := by
  intro d N hN hk τ hτ _
  have h0 : τ = 0 := by
    have := hτ.1
    rw [tMonW_one_eq_bot (by omega)] at this
    simpa using this
  rw [h0]; exact Submodule.zero_mem _

/-- **The tail of `BoxInclusion` in the slots of `T`-degree `> n`.** -/
def BoxInclusionTailHigh (n r : ℕ) : Prop :=
  ∀ (d : ℤ) (N : ℕ), N < r → n < r - N →
    tMonW (Rn n) (tn n) (r - N) (d - r) ⊓ testSp n r N ≤ boxW (tn n) N (r - N) (d - r)

/-- **`BoxInclusionTail` from its slots of `T`-degree `> n`.** -/
theorem boxInclusionTail_of_high {n r : ℕ} (hn : 1 ≤ n) (h : BoxInclusionTailHigh n r) :
    BoxInclusionTail n r := by
  intro d N hN hk
  rcases Nat.lt_or_ge n (r - N) with hlt | hge
  · exact h d N hN hlt
  · exact boxInclusion_degN hn d N (le_antisymm hge hk) hN

/-- **`BoxInclusion n (n + 1)` reduces to the single slot `N = 0`** (`T`-degree `n + 1`). -/
theorem boxInclusion_succ_of_slot0 {n : ℕ} (hn : 1 ≤ n)
    (h0 : ∀ d : ℤ, tMonW (Rn n) (tn n) (n + 1) (d - (n + 1 : ℕ)) ⊓ testSp n (n + 1) 0 ≤
      boxW (tn n) 0 (n + 1) (d - (n + 1 : ℕ))) :
    BoxInclusion n (n + 1) := by
  refine boxInclusion_of_tail (boxInclusionTail_of_high hn fun d N hN hk => ?_)
  obtain rfl : N = 0 := by omega
  simpa using h0 d

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, `#print axioms`-clean, conditional only on `hA`,
detection `det` and the ideal-elimination input in the slots of `T`-degree `> n` with `r > n`
(for `r = n + 1` only the slot `N = 0` remains). -/
theorem twoSeries_gradedUnitary_of_strictModel_singularLiftHigh (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (lift : ∀ r, n < r → SingularLiftHigh n r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_strictModel_singular n hn hA det fun r =>
    if h : n < r then
      boxSingularTail_of_high hn (boxSingularTailHigh_of_singularLiftHigh (lift r h))
    else SingTailDiag.boxSingularTail_of_le hn (by omega)

/-- **Affine GU ⇒ GU of `M(2, 5)`** (`n = 1`), `#print axioms`-clean, conditional only on
`hA` and detection `det`: no ideal-elimination input is needed since `R_1 = ℂ`. -/
theorem twoSeries_gradedUnitary_one_of_strictModel
    (hA : GradedUnitary (affineForm (twoSeriesLevels 1)) (affineRealStructure (twoSeriesLevels 1))
      (affineFlag (twoSeriesLevels 1)))
    (det : TwoSeriesModelDetects 1) :
    VirGradedUnitary (twoSeriesLevels 1).c (targetRealStructure (twoSeriesLevels 1)) :=
  twoSeries_gradedUnitary_of_strictModel_singular 1 le_rfl hA det boxSingularTail_one

end

end VOA.TwoSeries.StrictModel
