/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Poisson summation in several variables

**Ebeling, *Lattices and Codes*, Theorem 2.3.**  Mathlib provides Poisson summation only in one
variable (`Real.tsum_eq_tsum_fourier`), and that proof rests on one-dimensional interval-integral
API with no multivariate analogue.  This file builds the `d`-variable statement on top of the
multivariate Fourier series of `Mathlib.Analysis.Fourier.AddCircleMulti`, and then transports it
to an arbitrary lattice in a finite-dimensional real inner product space.

## Outline

1. `UnitAddTorus.proj` is the covering projection `ℝ^ι → (ℝ/ℤ)^ι`; it is an open quotient map
   (a finite product of the open quotient maps `ℝ → ℝ/ℤ`), which is what lets a `ℤ^ι`-periodic
   continuous function on `ℝ^ι` be read as a continuous function on the torus.
2. `UnitAddTorus.periodisation` is `x ↦ ∑' n : ℤ^ι, g (x + n)`, continuous as soon as the
   sup-norms of the translates are summable on every compact set
   (`UnitAddTorus.LocallySummable`, Ebeling's hypothesis (V2)).
3. `UnitAddTorus.mFourierCoeff_torusPeriodisation` is the key lemma: the `m`-th Fourier
   coefficient of the periodisation is the Fourier transform of `g` at `m`.  The proof runs the
   integral over the half-open unit box `(0,1]^ι`, which
   `UnitAddTorus.isAddFundamentalDomain_unitBox` exhibits as a fundamental domain for `ℤ^ι`;
   the sum-integral exchange is dominated convergence and the reassembly is
   `MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum''`, both dimension-agnostic.
4. `UnitAddTorus.tsum_intVec_eq_tsum_twist_integral` is Poisson summation over `ℤ^ι`.
5. `ZSpan.integral_comp_basis` is the linear change of variables `x ↦ ∑ᵢ xᵢ bᵢ`, obtained by
   identifying `Measure.map` of the Lebesgue measure with `Basis.addHaar`; together with the
   dual basis of the inner product this turns step 4 into `ZSpan.poissonSummation` and
   `ZLattice.poissonSummation`.

## Main results

* `UnitAddTorus.tsum_intVec_eq_tsum_twist_integral` — Poisson summation over `ℤ^ι`.
* `ZSpan.poissonSummation` — Poisson summation over `⊕ᵢ ℤ bᵢ`, indexed by `ℤ^ι`.
* `ZLattice.poissonSummation` — the same, indexed by the lattice and its dual `ZLattice.dual`.

## References

Ebeling, *Lattices and Codes*, Theorem 2.3.
-/

noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped Real FourierTransform BigOperators NNReal ENNReal

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι]

/-- The covering projection `ℝ^ι → (ℝ/ℤ)^ι`, coordinatewise reduction mod `ℤ`. -/
def proj (x : ι → ℝ) : UnitAddTorus ι := fun i => (x i : UnitAddCircle)

@[continuity, fun_prop]
theorem continuous_proj : Continuous (proj : (ι → ℝ) → UnitAddTorus ι) := by
  unfold proj
  fun_prop

theorem isOpenQuotientMap_proj : IsOpenQuotientMap (proj : (ι → ℝ) → UnitAddTorus ι) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

/-- The real vector attached to an integer vector. -/
def intVec (n : ι → ℤ) : ι → ℝ := fun i => (n i : ℝ)

@[simp] theorem intVec_apply (n : ι → ℤ) (i : ι) : intVec n i = (n i : ℝ) := rfl

@[simp] theorem intVec_zero : intVec (0 : ι → ℤ) = (0 : ι → ℝ) := by ext i; simp [intVec]

theorem intVec_add (m n : ι → ℤ) : intVec (m + n) = intVec m + intVec n := by
  ext i; simp [intVec]

theorem _root_.AddCircle.coe_intCast_eq_zero (n : ℤ) : ((n : ℝ) : UnitAddCircle) = 0 := by
  rw [show ((n : ℝ)) = n • (1 : ℝ) by simp, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]

@[simp] theorem proj_add_intVec (x : ι → ℝ) (n : ι → ℤ) : proj (x + intVec n) = proj x := by
  ext i
  simp only [proj, Pi.add_apply, intVec_apply]
  rw [AddCircle.coe_add, AddCircle.coe_intCast_eq_zero, add_zero]

theorem proj_eq_proj_iff {x y : ι → ℝ} : proj x = proj y ↔ ∃ n : ι → ℤ, y = x + intVec n := by
  constructor
  · intro h
    have h' : ∀ i, ∃ k : ℤ, (k : ℝ) = y i - x i := by
      intro i
      have : ((x i : ℝ) : UnitAddCircle) = ((y i : ℝ) : UnitAddCircle) := congrFun h i
      rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff] at this
      obtain ⟨k, hk⟩ := this
      rw [zsmul_eq_mul, mul_one] at hk
      exact ⟨-k, by push_cast; linarith⟩
    choose n hn using h'
    exact ⟨n, funext fun i => by rw [Pi.add_apply, intVec_apply, hn i]; ring⟩
  · rintro ⟨n, rfl⟩
    exact (proj_add_intVec x n).symm

theorem mFourier_proj (m : ι → ℤ) (x : ι → ℝ) :
    mFourier m (proj x) = (Real.fourierChar (∑ i, (m i : ℝ) * x i) : ℂ) := by
  simp only [mFourier, ContinuousMap.coe_mk, proj, fourier_coe_apply]
  rw [← Complex.exp_sum, Real.fourierChar_apply]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

end UnitAddTorus

/-! ## Periodisation -/

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι]

/-- The `ℤ^ι`-translates of a continuous function on `ℝ^ι`. -/
def translates (g : C(ι → ℝ, ℂ)) (n : ι → ℤ) : C(ι → ℝ, ℂ) :=
  g.comp (ContinuousMap.addRight (intVec n))

@[simp] theorem translates_apply (g : C(ι → ℝ, ℂ)) (n : ι → ℤ) (x : ι → ℝ) :
    translates g n x = g (x + intVec n) := rfl

/-- Local normal convergence of the `ℤ^ι`-periodisation of `g`: on every compact set the
sup-norms of the translates are summable. This is Ebeling's hypothesis (V2). -/
def LocallySummable (g : C(ι → ℝ, ℂ)) : Prop :=
  ∀ K : Compacts (ι → ℝ), Summable fun n : ι → ℤ => ‖(translates g n).restrict K‖

theorem LocallySummable.summable {g : C(ι → ℝ, ℂ)} (hg : LocallySummable g) :
    Summable (translates g) :=
  ContinuousMap.summable_of_locally_summable_norm hg

/-- The periodisation `x ↦ ∑' n : ℤ^ι, g (x + n)`, as a continuous function on `ℝ^ι`. -/
def periodisation (g : C(ι → ℝ, ℂ)) : C(ι → ℝ, ℂ) := ∑' n : ι → ℤ, translates g n

theorem periodisation_apply {g : C(ι → ℝ, ℂ)} (hg : LocallySummable g) (x : ι → ℝ) :
    periodisation g x = ∑' n : ι → ℤ, g (x + intVec n) :=
  (ContinuousMap.tsum_apply hg.summable x).symm

theorem periodisation_add_intVec {g : C(ι → ℝ, ℂ)} (hg : LocallySummable g)
    (x : ι → ℝ) (k : ι → ℤ) : periodisation g (x + intVec k) = periodisation g x := by
  rw [periodisation_apply hg, periodisation_apply hg]
  rw [← (Equiv.addLeft k).tsum_eq (fun n : ι → ℤ => g (x + intVec n))]
  refine tsum_congr fun n => ?_
  congr 1
  rw [Equiv.coe_addLeft, intVec_add]
  ring

/-! ### Descent to the torus -/

/-- A `ℤ^ι`-periodic function on `ℝ^ι`, read as a function on the torus. -/
def liftTorus (G : (ι → ℝ) → ℂ) : UnitAddTorus ι → ℂ :=
  fun t => G (Function.surjInv isOpenQuotientMap_proj.surjective t)

theorem liftTorus_proj {G : (ι → ℝ) → ℂ} (hG : ∀ (x : ι → ℝ) (k : ι → ℤ), G (x + intVec k) = G x)
    (x : ι → ℝ) : liftTorus G (proj x) = G x := by
  have h : proj (Function.surjInv isOpenQuotientMap_proj.surjective (proj x)) = proj x :=
    Function.surjInv_eq _ _
  obtain ⟨n, hn⟩ := proj_eq_proj_iff.1 h
  nth_rewrite 2 [hn]
  rw [hG]
  rfl

theorem continuous_liftTorus {G : (ι → ℝ) → ℂ} (hGc : Continuous G)
    (hG : ∀ (x : ι → ℝ) (k : ι → ℤ), G (x + intVec k) = G x) : Continuous (liftTorus G) := by
  rw [isOpenQuotientMap_proj.isQuotientMap.continuous_iff]
  exact hGc.congr fun x => (liftTorus_proj hG x).symm

/-- The periodisation of `g` as a continuous function on the torus `(ℝ/ℤ)^ι`. -/
def torusPeriodisation (g : C(ι → ℝ, ℂ)) (hg : LocallySummable g) : C(UnitAddTorus ι, ℂ) :=
  ⟨liftTorus (periodisation g),
    continuous_liftTorus (periodisation g).continuous (periodisation_add_intVec hg)⟩

@[simp] theorem torusPeriodisation_proj {g : C(ι → ℝ, ℂ)} (hg : LocallySummable g) (x : ι → ℝ) :
    torusPeriodisation g hg (proj x) = periodisation g x :=
  liftTorus_proj (periodisation_add_intVec hg) x

end UnitAddTorus

/-! ## The integer lattice `ℤ^ι` and its unit box -/

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι]

theorem intVec_injective : Function.Injective (intVec (ι := ι)) := fun _ _ h =>
  funext fun i => Int.cast_injective (α := ℝ) (congrFun h i)

variable (ι) in
/-- `ℤ^ι` as an additive subgroup of `ℝ^ι`. -/
def intLattice : AddSubgroup (ι → ℝ) where
  carrier := Set.range (intVec (ι := ι))
  add_mem' := by rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩; exact ⟨m + n, intVec_add m n⟩
  zero_mem' := ⟨0, by ext i; simp [intVec]⟩
  neg_mem' := by rintro _ ⟨n, rfl⟩; exact ⟨-n, by ext i; simp [intVec]⟩

theorem mem_intLattice {v : ι → ℝ} : v ∈ intLattice ι ↔ ∃ n : ι → ℤ, intVec n = v := Iff.rfl

/-- The parametrisation of `ℤ^ι ⊆ ℝ^ι` by `ι → ℤ`. -/
noncomputable def intLatticeEquiv : (ι → ℤ) ≃ (intLattice ι) :=
  Equiv.ofBijective (fun n => (⟨intVec n, ⟨n, rfl⟩⟩ : intLattice ι))
    ⟨fun _ _ h => intVec_injective (congrArg Subtype.val h),
      fun v => by obtain ⟨n, hn⟩ := mem_intLattice.1 v.2; exact ⟨n, Subtype.ext hn⟩⟩

@[simp] theorem coe_intLatticeEquiv (n : ι → ℤ) :
    ((intLatticeEquiv n : intLattice ι) : ι → ℝ) = intVec n := rfl

instance : Countable (intLattice ι) := Countable.of_equiv _ (intLatticeEquiv (ι := ι))

variable (ι) in
/-- The half-open unit box `(0,1]^ι`, the fundamental domain of `ℤ^ι` used by
`UnitAddTorus.mFourierCoeff_eq_integral`. -/
def unitBox : Set (ι → ℝ) := {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1}

theorem measurableSet_unitBox : MeasurableSet (unitBox ι) := by
  have : unitBox ι = Set.pi Set.univ fun _ : ι => Ioc (0 : ℝ) 1 := by
    ext x; simp [unitBox]
  rw [this]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem mem_unitBox_iff {x : ι → ℝ} : x ∈ unitBox ι ↔ ∀ i, ⌈x i⌉ = 1 := by
  refine forall_congr' fun i => ?_
  rw [Int.ceil_eq_iff]
  norm_num

theorem isAddFundamentalDomain_unitBox :
    IsAddFundamentalDomain (intLattice ι) (unitBox ι) volume := by
  refine IsAddFundamentalDomain.mk' measurableSet_unitBox.nullMeasurableSet fun x => ?_
  have key : ∀ n : ι → ℤ, (intVec n + x ∈ unitBox ι) ↔ n = fun i => 1 - ⌈x i⌉ := by
    intro n
    rw [mem_unitBox_iff, funext_iff]
    refine forall_congr' fun i => ?_
    rw [Pi.add_apply, intVec_apply, add_comm, Int.ceil_add_intCast]
    omega
  refine ⟨intLatticeEquiv (fun i => 1 - ⌈x i⌉), ?_, ?_⟩
  · show intVec _ + x ∈ unitBox ι
    exact (key _).2 rfl
  · rintro ⟨v, hv⟩ h
    obtain ⟨n, rfl⟩ := mem_intLattice.1 hv
    have hn : n = fun i => 1 - ⌈x i⌉ := (key n).1 h
    exact Subtype.ext (congrArg intVec hn)

end UnitAddTorus

/-! ## The twisting character -/

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι]

theorem _root_.Real.fourierChar_intCast (k : ℤ) : Real.fourierChar ((k : ℝ)) = 1 := by
  apply Subtype.ext
  rw [Real.fourierChar_apply]
  push_cast
  rw [show ((2 * (π : ℂ) * (k : ℂ))) * Complex.I = (k : ℂ) * (2 * π * Complex.I) by ring,
    Complex.exp_int_mul_two_pi_mul_I]

/-- The character `x ↦ 𝐞 (-∑ i, mᵢ xᵢ)` on `ℝ^ι`. -/
def twist (m : ι → ℤ) : C(ι → ℝ, ℂ) where
  toFun x := (Real.fourierChar (-∑ i, (m i : ℝ) * x i) : ℂ)
  continuous_toFun := by
    exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))

@[simp] theorem twist_apply (m : ι → ℤ) (x : ι → ℝ) :
    twist m x = (Real.fourierChar (-∑ i, (m i : ℝ) * x i) : ℂ) := rfl

@[simp] theorem norm_twist (m : ι → ℤ) (x : ι → ℝ) : ‖twist m x‖ = 1 := Circle.norm_coe _

theorem twist_add_intVec (m : ι → ℤ) (n : ι → ℤ) (x : ι → ℝ) :
    twist m (x + intVec n) = twist m x := by
  have h : (-∑ i, (m i : ℝ) * (x + intVec n) i)
      = (-∑ i, (m i : ℝ) * x i) + ((-∑ i, m i * n i : ℤ) : ℝ) := by
    simp only [Pi.add_apply, intVec_apply, mul_add, Finset.sum_add_distrib]
    push_cast
    ring
  simp only [twist_apply, h, AddChar.map_add_eq_mul, Real.fourierChar_intCast, mul_one]

theorem mFourier_proj_eq_twist (m : ι → ℤ) (x : ι → ℝ) :
    mFourier (-m) (proj x) = twist m x := by
  rw [mFourier_proj, twist_apply]
  congr 2
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

end UnitAddTorus

/-! ## Integrability from local normal convergence -/

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι]

variable (ι) in
/-- The closed unit box `[0,1]^ι`; a compact set containing `unitBox ι`. -/
def closedUnitBox : Compacts (ι → ℝ) :=
  ⟨Set.pi Set.univ fun _ => Icc (0 : ℝ) 1, isCompact_univ_pi fun _ => isCompact_Icc⟩

theorem unitBox_subset_closedUnitBox : unitBox ι ⊆ (closedUnitBox ι : Set (ι → ℝ)) :=
  fun _ hx _ _ => ⟨(hx _).1.le, (hx _).2⟩

@[simp] theorem volume_unitBox : volume (unitBox ι) = 1 := by
  have h : unitBox ι = Set.pi Set.univ fun _ : ι => Ioc (0 : ℝ) 1 := by ext x; simp [unitBox]
  rw [h, volume_pi_pi]
  simp

theorem norm_le_of_mem_unitBox {g : C(ι → ℝ, ℂ)} (n : ι → ℤ) {x : ι → ℝ} (hx : x ∈ unitBox ι) :
    ‖g (x + intVec n)‖ ≤ ‖(translates g n).restrict (closedUnitBox ι : Set (ι → ℝ))‖ :=
  ((translates g n).restrict (closedUnitBox ι : Set (ι → ℝ))).norm_coe_le_norm
    ⟨x, unitBox_subset_closedUnitBox hx⟩

theorem norm_restrict_twist_mul (m : ι → ℤ) (g : C(ι → ℝ, ℂ)) (n : ι → ℤ)
    (K : Compacts (ι → ℝ)) :
    ‖(translates (twist m * g) n).restrict (K : Set (ι → ℝ))‖
      = ‖(translates g n).restrict (K : Set (ι → ℝ))‖ := by
  simp_rw [ContinuousMap.norm_eq_iSup_norm]
  refine iSup_congr fun x => ?_
  simp only [translates, ContinuousMap.restrict_apply, ContinuousMap.mul_comp,
    ContinuousMap.mul_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addRight,
    norm_mul, norm_twist, one_mul]

theorem LocallySummable.twist_mul {g : C(ι → ℝ, ℂ)} (hg : LocallySummable g) (m : ι → ℤ) :
    LocallySummable (twist m * g) := by
  intro K
  simpa only [norm_restrict_twist_mul] using hg K

theorem LocallySummable.integrable {g : C(ι → ℝ, ℂ)} (hg : LocallySummable g) :
    Integrable g volume := by
  refine ⟨g.continuous.aestronglyMeasurable, ?_⟩
  set a : (ι → ℤ) → ℝ := fun n => ‖(translates g n).restrict (closedUnitBox ι : Set (ι → ℝ))‖
    with ha
  have hsum : Summable a := hg (closedUnitBox ι)
  have key : ∫⁻ x, ‖g x‖ₑ ≤ ∑' n : ι → ℤ, ENNReal.ofReal (a n) := by
    rw [isAddFundamentalDomain_unitBox.lintegral_eq_tsum'' (fun x => ‖g x‖ₑ)]
    rw [← (intLatticeEquiv (ι := ι)).tsum_eq
      (fun h : intLattice ι => ∫⁻ x in unitBox ι, ‖g (h +ᵥ x)‖ₑ)]
    refine ENNReal.tsum_le_tsum fun n => ?_
    calc ∫⁻ x in unitBox ι, ‖g ((intLatticeEquiv n) +ᵥ x)‖ₑ
        ≤ ∫⁻ _ in unitBox ι, ENNReal.ofReal (a n) := by
          refine setLIntegral_mono' measurableSet_unitBox fun x hx => ?_
          rw [← ofReal_norm]
          refine ENNReal.ofReal_le_ofReal ?_
          have : (intLatticeEquiv n : ι → ℝ) +ᵥ x = x + intVec n := by
            simp [coe_intLatticeEquiv, add_comm]
          rw [show ((intLatticeEquiv n) +ᵥ x : ι → ℝ) = x + intVec n from this]
          exact norm_le_of_mem_unitBox n hx
      _ = ENNReal.ofReal (a n) := by rw [setLIntegral_const, volume_unitBox, mul_one]
  refine lt_of_le_of_lt key ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) hsum]
  exact ENNReal.ofReal_lt_top

end UnitAddTorus

/-! ## The Fourier coefficients of the periodisation -/

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι]

theorem integrableOn_unitBox (f : C(ι → ℝ, ℂ)) : IntegrableOn f (unitBox ι) volume :=
  (f.continuous.locallyIntegrable.integrableOn_isCompact
    (closedUnitBox ι).isCompact).mono_set unitBox_subset_closedUnitBox

@[simp] theorem volume_real_unitBox : (volume : Measure (ι → ℝ)).real (unitBox ι) = 1 := by
  simp [measureReal_def]

/-- **The key lemma for Poisson summation.** The `m`-th Fourier coefficient of the
`ℤ^ι`-periodisation of `g` is the value at `m` of the Fourier transform of `g`. -/
theorem mFourierCoeff_torusPeriodisation {g : C(ι → ℝ, ℂ)} (hg : LocallySummable g) (m : ι → ℤ) :
    mFourierCoeff (torusPeriodisation g hg) m = ∫ x : ι → ℝ, twist m x * g x := by
  have hset : {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} = unitBox ι := by
    ext x; simp [unitBox]
  have hint : ∀ x : ι → ℝ,
      mFourier (-m) (fun i => ((x i : ℝ) : UnitAddCircle)) •
        (torusPeriodisation g hg) (fun i => ((x i : ℝ) : UnitAddCircle))
        = ∑' n : ι → ℤ, (twist m * g) (x + intVec n) := by
    intro x
    show mFourier (-m) (proj x) • (torusPeriodisation g hg) (proj x) = _
    rw [mFourier_proj_eq_twist, torusPeriodisation_proj, periodisation_apply hg, smul_eq_mul,
      ← tsum_mul_left]
    exact tsum_congr fun n => by
      rw [ContinuousMap.mul_apply, twist_add_intVec]
  -- the twisted function, and its integrability
  set Ψ : C(ι → ℝ, ℂ) := twist m * g with hΨ
  have hΨloc : LocallySummable Ψ := hg.twist_mul m
  have hΨint : Integrable Ψ volume := hΨloc.integrable
  -- Step 1: the coefficient is an integral over the unit box
  rw [mFourierCoeff_eq_integral _ m 0, hset,
    setIntegral_congr_fun measurableSet_unitBox (fun x _ => hint x)]
  -- Step 2: exchange the sum and the integral
  have hswap : ∫ x in unitBox ι, ∑' n : ι → ℤ, Ψ (x + intVec n)
      = ∑' n : ι → ℤ, ∫ x in unitBox ι, Ψ (x + intVec n) := by
    refine (HasSum.tsum_eq ?_).symm
    refine hasSum_integral_of_summable_integral_norm
      (F := fun (n : ι → ℤ) (x : ι → ℝ) => Ψ (x + intVec n)) (fun n => ?_) ?_
    · exact integrableOn_unitBox (translates Ψ n)
    · refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
        (fun n => ?_) (hΨloc (closedUnitBox ι))
      have hb : ∫ x in unitBox ι, ‖Ψ (x + intVec n)‖
          ≤ ∫ _ in unitBox ι, ‖(translates Ψ n).restrict (closedUnitBox ι : Set (ι → ℝ))‖ := by
        refine setIntegral_mono_on ((integrableOn_unitBox (translates Ψ n)).norm)
          (integrableOn_const (by simp) (by simp)) measurableSet_unitBox fun x hx => ?_
        exact norm_le_of_mem_unitBox n hx
      simpa using hb
  rw [hswap]
  -- Step 3: the unit box is a fundamental domain for `ℤ^ι`
  have hfd : ∫ x : ι → ℝ, Ψ x = ∑' n : ι → ℤ, ∫ x in unitBox ι, Ψ (x + intVec n) := by
    rw [isAddFundamentalDomain_unitBox.integral_eq_tsum'' (Ψ : (ι → ℝ) → ℂ) hΨint,
      ← (intLatticeEquiv (ι := ι)).tsum_eq
        (fun h : intLattice ι => ∫ x in unitBox ι, Ψ (h +ᵥ x))]
    exact tsum_congr fun n =>
      setIntegral_congr_fun measurableSet_unitBox fun x _ => by
        show Ψ ((intLatticeEquiv n : ι → ℝ) + x) = Ψ (x + intVec n)
        rw [coe_intLatticeEquiv, add_comm]
  rw [← hfd]
  rfl

end UnitAddTorus

/-! ## Poisson summation over `ℤ^ι` -/

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι]

@[simp] theorem proj_zero : proj (0 : ι → ℝ) = 0 := by
  ext i; simp [proj]

@[simp] theorem mFourier_eval_zero (m : ι → ℤ) : mFourier m (0 : UnitAddTorus ι) = 1 := by
  simp [mFourier]

/-- **Poisson summation in `ι` variables**, general form: the periodisation of `g` at `y` is
the sum of its Fourier series. -/
theorem tsum_add_intVec_eq {g : C(ι → ℝ, ℂ)} (hg : LocallySummable g)
    (h_sum : Summable fun m : ι → ℤ => ∫ x : ι → ℝ, twist m x * g x) (y : ι → ℝ) :
    ∑' n : ι → ℤ, g (y + intVec n)
      = ∑' m : ι → ℤ, (∫ x : ι → ℝ, twist m x * g x) * mFourier m (proj y) := by
  have hc : Summable (mFourierCoeff (torusPeriodisation g hg)) := by
    have h : (mFourierCoeff (torusPeriodisation g hg))
        = fun m : ι → ℤ => ∫ x : ι → ℝ, twist m x * g x :=
      funext fun m => mFourierCoeff_torusPeriodisation hg m
    rw [h]; exact h_sum
  have hs := hasSum_mFourier_series_apply_of_summable hc (proj y)
  rw [torusPeriodisation_proj, periodisation_apply hg] at hs
  rw [← hs.tsum_eq]
  exact tsum_congr fun m => by
    rw [smul_eq_mul, mFourierCoeff_torusPeriodisation hg]

/-- **Poisson summation in `ι` variables**: `∑_{n ∈ ℤ^ι} g n = ∑_{m ∈ ℤ^ι} ĝ m`, where the
Fourier transform is taken with respect to the standard pairing `⟨m, x⟩ = ∑ᵢ mᵢ xᵢ`.

Ebeling, *Lattices and Codes*, Theorem 2.3, for the standard lattice `ℤ^ι`. -/
theorem tsum_intVec_eq_tsum_twist_integral {g : C(ι → ℝ, ℂ)} (hg : LocallySummable g)
    (h_sum : Summable fun m : ι → ℤ => ∫ x : ι → ℝ, twist m x * g x) :
    ∑' n : ι → ℤ, g (intVec n) = ∑' m : ι → ℤ, ∫ x : ι → ℝ, twist m x * g x := by
  have := tsum_add_intVec_eq hg h_sum 0
  simpa using this

end UnitAddTorus

/-! ## Linear change of variables along a basis -/

namespace ZSpan

open Module MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem addHaar_pi_basisFun : (Pi.basisFun ℝ ι).addHaar = (volume : Measure (ι → ℝ)) := by
  rw [Basis.addHaar_def, Basis.parallelepiped_basisFun, addHaarMeasure_eq_volume_pi]

theorem map_basisFun_map (b : Basis ι ℝ V) :
    (Pi.basisFun ℝ ι).map (b.equivFunL.symm.toLinearEquiv) = b := by
  classical
  refine DFunLike.ext _ _ fun i => ?_
  simp only [Basis.map_apply, Pi.basisFun_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
  show b.equivFun.symm (Pi.single i 1) = b i
  simp

theorem map_equivFunL_symm_volume (b : Basis ι ℝ V) :
    Measure.map (b.equivFunL.symm : (ι → ℝ) → V) volume = b.addHaar := by
  rw [← addHaar_pi_basisFun, Basis.map_addHaar, map_basisFun_map]

end ZSpan

namespace ZSpan

open Module MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem volume_parallelepiped_ne_zero (b : Basis ι ℝ V) :
    (volume : Measure V) (Basis.parallelepiped b) ≠ 0 :=
  (Measure.measure_pos_of_nonempty_interior _ (Basis.parallelepiped b).interior_nonempty).ne'

theorem volume_parallelepiped_ne_top (b : Basis ι ℝ V) :
    (volume : Measure V) (Basis.parallelepiped b) ≠ ⊤ :=
  (Basis.parallelepiped b).isCompact.measure_lt_top.ne

theorem addHaar_eq_smul_volume (b : Basis ι ℝ V) :
    b.addHaar
      = (((volume : Measure V) (Basis.parallelepiped b))⁻¹.toNNReal) • (volume : Measure V) := by
  have h0 := volume_parallelepiped_ne_zero b
  have ht := volume_parallelepiped_ne_top b
  have hcoe : ((((volume : Measure V) (Basis.parallelepiped b))⁻¹.toNNReal : ℝ≥0) : ℝ≥0∞)
      = ((volume : Measure V) (Basis.parallelepiped b))⁻¹ :=
    ENNReal.coe_toNNReal (ENNReal.inv_ne_top.2 h0)
  rw [Basis.addHaar_eq_iff, Measure.coe_nnreal_smul_apply, hcoe]
  exact ENNReal.inv_mul_cancel h0 ht

theorem addHaar_eq_inv_smul_volume (b : Basis ι ℝ V) :
    b.addHaar
      = (((volume : Measure V) (Basis.parallelepiped b))⁻¹ : ℝ≥0∞) • (volume : Measure V) := by
  have h0 := volume_parallelepiped_ne_zero b
  have hcoe : ((((volume : Measure V) (Basis.parallelepiped b))⁻¹.toNNReal : ℝ≥0) : ℝ≥0∞)
      = ((volume : Measure V) (Basis.parallelepiped b))⁻¹ :=
    ENNReal.coe_toNNReal (ENNReal.inv_ne_top.2 h0)
  rw [addHaar_eq_smul_volume b]
  ext s
  rw [Measure.coe_nnreal_smul_apply, Measure.smul_apply, smul_eq_mul, hcoe]

theorem volume_eq_smul_addHaar (b : Basis ι ℝ V) :
    (volume : Measure V) = ((volume : Measure V) (Basis.parallelepiped b)) • b.addHaar := by
  have h0 := volume_parallelepiped_ne_zero b
  have ht := volume_parallelepiped_ne_top b
  rw [addHaar_eq_inv_smul_volume b, smul_smul, ENNReal.mul_inv_cancel h0 ht, one_smul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Linear change of variables.** Integrating along the parametrisation `x ↦ ∑ᵢ xᵢ bᵢ`
of `V` by `ℝ^ι` divides the integral by the volume of the parallelepiped of `b`. -/
theorem integral_comp_basis (b : Basis ι ℝ V) (h : V → E) :
    ∫ x : ι → ℝ, h (b.equivFunL.symm x)
      = (((volume : Measure V) (Basis.parallelepiped b)).toReal)⁻¹ • ∫ v : V, h v := by
  have h0 := volume_parallelepiped_ne_zero b
  have ht := volume_parallelepiped_ne_top b
  have h1 : ∫ v : V, h v ∂(b.addHaar) = ∫ x : ι → ℝ, h (b.equivFunL.symm x) := by
    rw [← map_equivFunL_symm_volume b]
    exact integral_map_equiv (b.equivFunL.symm.toHomeomorph.toMeasurableEquiv) h
  have h2 : ∫ v : V, h v = ((volume : Measure V) (Basis.parallelepiped b)).toReal
      • ∫ v : V, h v ∂(b.addHaar) := by
    conv_lhs => rw [volume_eq_smul_addHaar b]
    rw [integral_smul_measure]
  have h3 : ((volume : Measure V) (Basis.parallelepiped b)).toReal ≠ 0 := by
    simp only [ne_eq, ENNReal.toReal_eq_zero_iff, not_or]
    exact ⟨h0, ht⟩
  rw [← h1, h2, smul_smul, inv_mul_cancel₀ h3, one_smul]

end ZSpan

/-! ## The dual basis and the covolume -/

namespace ZSpan

open Module MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

open scoped RealInnerProductSpace

theorem volume_parallelepiped_eq_covolume (b : Basis ι ℝ V) :
    (volume : Measure V) (Basis.parallelepiped b)
      = ENNReal.ofReal (ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume) := by
  have hfd : (volume : Measure V) (ZSpan.fundamentalDomain b)
      = (volume : Measure V) (Basis.parallelepiped b) := by
    rw [Basis.coe_parallelepiped]
    exact measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b volume)
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain b volume),
    measureReal_def, hfd, ENNReal.ofReal_toReal (volume_parallelepiped_ne_top b)]

theorem covolume_pos_of_basis (b : Basis ι ℝ V) :
    0 < ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume :=
  ZLattice.covolume_pos _ _

theorem toReal_volume_parallelepiped (b : Basis ι ℝ V) :
    ((volume : Measure V) (Basis.parallelepiped b)).toReal
      = ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume := by
  rw [volume_parallelepiped_eq_covolume b,
    ENNReal.toReal_ofReal (covolume_pos_of_basis b).le]

theorem innerₗ_nondegenerate : LinearMap.BilinForm.Nondegenerate (innerₗ V) :=
  ⟨fun x hx => inner_self_eq_zero.1 (hx x), fun y hy => inner_self_eq_zero.1 (hy y)⟩

theorem innerₗ_isSymm : LinearMap.BilinForm.IsSymm (innerₗ V) :=
  ⟨fun x y => real_inner_comm y x⟩

variable [DecidableEq ι]

/-- The basis of `V` dual to `b` with respect to the inner product:
`⟪dualBasis b i, b j⟫ = δᵢⱼ`. -/
noncomputable def dualBasis (b : Basis ι ℝ V) : Basis ι ℝ V :=
  LinearMap.BilinForm.dualBasis (innerₗ V) innerₗ_nondegenerate b

@[simp] theorem inner_dualBasis (b : Basis ι ℝ V) (i j : ι) :
    ⟪dualBasis b i, b j⟫ = if j = i then 1 else 0 :=
  LinearMap.BilinForm.apply_dualBasis_left (B := innerₗ V) innerₗ_nondegenerate b i j

@[simp] theorem inner_basis_dualBasis (b : Basis ι ℝ V) (i j : ι) :
    ⟪b i, dualBasis b j⟫ = if i = j then 1 else 0 :=
  LinearMap.BilinForm.apply_dualBasis_right (B := innerₗ V) innerₗ_nondegenerate innerₗ_isSymm b i j

variable (ι) in
/-- The lattice vector `∑ᵢ nᵢ bᵢ` attached to `n : ℤ^ι`. -/
noncomputable def latticeVec (b : Basis ι ℝ V) (n : ι → ℤ) : V := ∑ i, (n i : ℝ) • b i

theorem latticeVec_eq_equivFunL_symm (b : Basis ι ℝ V) (n : ι → ℤ) :
    latticeVec ι b n = b.equivFunL.symm (UnitAddTorus.intVec n) := by
  rw [latticeVec]
  show _ = b.equivFun.symm (UnitAddTorus.intVec n)
  rw [Basis.equivFun_symm_apply]
  rfl

theorem inner_equivFunL_symm_latticeVec (b : Basis ι ℝ V) (m : ι → ℤ) (x : ι → ℝ) :
    ⟪b.equivFunL.symm x, latticeVec ι (dualBasis b) m⟫ = ∑ i, (m i : ℝ) * x i := by
  have hx : b.equivFunL.symm x = ∑ j, x j • b j := by
    show b.equivFun.symm x = _
    rw [Basis.equivFun_symm_apply]
  rw [hx, latticeVec, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, inner_sum]
  simp [real_inner_smul_right, mul_comm]

end ZSpan

/-! ## Poisson summation over a lattice in an inner product space -/

namespace ZSpan

open Module MeasureTheory UnitAddTorus
open scoped RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The parametrisation `ℝ^ι → V`, `x ↦ ∑ᵢ xᵢ bᵢ`, as a continuous map. -/
noncomputable def coordMap (b : Basis ι ℝ V) : C(ι → ℝ, V) :=
  ⟨b.equivFunL.symm, b.equivFunL.symm.continuous⟩

@[simp] theorem coordMap_apply (b : Basis ι ℝ V) (x : ι → ℝ) :
    coordMap b x = b.equivFunL.symm x := rfl

theorem coordMap_intVec (b : Basis ι ℝ V) (n : ι → ℤ) :
    coordMap b (intVec n) = latticeVec ι b n := (latticeVec_eq_equivFunL_symm b n).symm

/-- Ebeling's hypothesis (V2): the periodisation of `f` over the lattice spanned by `b`
converges uniformly on compact sets. -/
def LocallySummableOn (b : Basis ι ℝ V) (f : C(V, ℂ)) : Prop :=
  ∀ K : Compacts V, Summable fun n : ι → ℤ =>
    ‖(f.comp (ContinuousMap.addRight (latticeVec ι b n))).restrict (K : Set V)‖

theorem LocallySummableOn.comp {b : Basis ι ℝ V} {f : C(V, ℂ)} (hf : LocallySummableOn b f) :
    LocallySummable (f.comp (coordMap b)) := by
  intro K'
  set K : Compacts V := ⟨coordMap b '' (K' : Set (ι → ℝ)),
    K'.isCompact.image (coordMap b).continuous⟩ with hK
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hf K)
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
  have hx : coordMap b (x : ι → ℝ) ∈ (K : Set V) := ⟨x, x.2, rfl⟩
  have hval : (translates (f.comp (coordMap b)) n).restrict (K' : Set (ι → ℝ)) x
      = (f.comp (ContinuousMap.addRight (latticeVec ι b n))).restrict (K : Set V)
        ⟨coordMap b (x : ι → ℝ), hx⟩ := by
    show f (coordMap b ((x : ι → ℝ) + intVec n)) = f (coordMap b (x : ι → ℝ) + latticeVec ι b n)
    rw [← coordMap_intVec b n]
    congr 1
    exact map_add b.equivFunL.symm _ _
  rw [hval]
  exact ContinuousMap.norm_coe_le_norm _ _

/-- The Fourier coefficient computation, transported to `V`: the twisted integral over `ℝ^ι`
is the Fourier transform of `f` at the dual lattice point, divided by the covolume. -/
theorem integral_twist_comp (b : Basis ι ℝ V) (f : V → ℂ) (m : ι → ℤ) :
    ∫ x : ι → ℝ, twist m x * f (b.equivFunL.symm x)
      = (ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume)⁻¹
        • 𝓕 f (latticeVec ι (dualBasis b) m) := by
  set h : V → ℂ :=
    fun v => ((Real.fourierChar (-⟪v, latticeVec ι (dualBasis b) m⟫) : Circle) : ℂ) * f v with hh
  have h1 : (fun x : ι → ℝ => twist m x * f (b.equivFunL.symm x))
      = fun x : ι → ℝ => h (b.equivFunL.symm x) := by
    funext x
    simp only [hh, twist_apply]
    rw [inner_equivFunL_symm_latticeVec]
  rw [h1, integral_comp_basis b h, toReal_volume_parallelepiped b]
  refine congrArg
    (fun z : ℂ => (ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume)⁻¹ • z) ?_
  exact (Real.fourier_eq f (latticeVec ι (dualBasis b) m)).symm

/-- **Poisson summation over a lattice** (Ebeling, *Lattices and Codes*, Theorem 2.3).

For a continuous `f : V → ℂ` whose periodisation over the lattice `Γ = ⊕ᵢ ℤ bᵢ` converges
uniformly on compact sets, and whose Fourier transform is summable over the dual lattice,

`∑_{x ∈ Γ} f x = (1 / covol Γ) ∑_{y ∈ Γ*} 𝓕 f y`.

Here both sides are indexed by `ℤ^ι` through `b` and its dual basis. -/
theorem poissonSummation (b : Basis ι ℝ V) {f : C(V, ℂ)} (hf : LocallySummableOn b f)
    (hsum : Summable fun m : ι → ℤ => 𝓕 (f : V → ℂ) (latticeVec ι (dualBasis b) m)) :
    ∑' n : ι → ℤ, f (latticeVec ι b n)
      = (ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume)⁻¹
        • ∑' m : ι → ℤ, 𝓕 (f : V → ℂ) (latticeVec ι (dualBasis b) m) := by
  set c := (ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume)⁻¹ with hc
  have hkey : (fun m : ι → ℤ => ∫ x : ι → ℝ, twist m x * (f.comp (coordMap b)) x)
      = fun m : ι → ℤ => c • 𝓕 (f : V → ℂ) (latticeVec ι (dualBasis b) m) :=
    funext fun m => integral_twist_comp b (f : V → ℂ) m
  have hsum' : Summable fun m : ι → ℤ => ∫ x : ι → ℝ, twist m x * (f.comp (coordMap b)) x := by
    rw [hkey]; exact hsum.const_smul c
  calc ∑' n : ι → ℤ, f (latticeVec ι b n)
      = ∑' n : ι → ℤ, (f.comp (coordMap b)) (intVec n) :=
        tsum_congr fun n => by rw [ContinuousMap.comp_apply, coordMap_intVec]
    _ = ∑' m : ι → ℤ, c • 𝓕 (f : V → ℂ) (latticeVec ι (dualBasis b) m) := by
        rw [← hkey]; exact tsum_intVec_eq_tsum_twist_integral hf.comp hsum'
    _ = c • ∑' m : ι → ℤ, 𝓕 (f : V → ℂ) (latticeVec ι (dualBasis b) m) := by
        simp_rw [Complex.real_smul, tsum_mul_left]

end ZSpan

/-! ## Poisson summation, indexed by the lattice and its dual -/

namespace ZLattice

open Module MeasureTheory UnitAddTorus ZSpan
open scoped RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- `ℤ^ι` parametrises the lattice spanned by `b`. -/
noncomputable def latticeEquiv (b : Basis ι ℝ V) :
    (ι → ℤ) ≃ (Submodule.span ℤ (Set.range b)) :=
  (b.restrictScalars ℤ).equivFun.toEquiv.symm

@[simp] theorem coe_latticeEquiv (b : Basis ι ℝ V) (n : ι → ℤ) :
    ((latticeEquiv b n : Submodule.span ℤ (Set.range b)) : V) = latticeVec ι b n := by
  have h : (latticeEquiv b n : Submodule.span ℤ (Set.range b))
      = ∑ i, n i • (b.restrictScalars ℤ i) := by
    simp [latticeEquiv, Basis.equivFun_symm_apply]
  rw [h, latticeVec]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by
    simp [Basis.restrictScalars_apply, ← Int.cast_smul_eq_zsmul ℝ]

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [T2Space M]

theorem tsum_lattice (b : Basis ι ℝ V) (F : V → M) :
    ∑' x : Submodule.span ℤ (Set.range b), F x = ∑' n : ι → ℤ, F (latticeVec ι b n) := by
  rw [← (latticeEquiv b).tsum_eq (fun x : Submodule.span ℤ (Set.range b) => F x)]
  exact tsum_congr fun n => by rw [coe_latticeEquiv]

theorem summable_lattice_iff (b : Basis ι ℝ V) (F : V → M) :
    (Summable fun x : Submodule.span ℤ (Set.range b) => F x)
      ↔ Summable fun n : ι → ℤ => F (latticeVec ι b n) := by
  rw [← (latticeEquiv b).summable_iff (f := fun x : Submodule.span ℤ (Set.range b) => F x)]
  exact summable_congr fun n => by rw [Function.comp_apply, coe_latticeEquiv]

theorem latticeVec_eq_zero_iff (b : Basis ι ℝ V) {n : ι → ℤ} :
    latticeVec ι b n = 0 ↔ n = 0 := by
  rw [latticeVec_eq_equivFunL_symm]
  constructor
  · intro h
    have : intVec n = (0 : ι → ℝ) := by
      have := congrArg b.equivFunL h
      simpa using this
    exact intVec_injective (by rw [this, intVec_zero])
  · rintro rfl
    simp

theorem summable_norm_rpow_latticeVec (b : Basis ι ℝ V) {r : ℝ}
    (hr : r < -(Fintype.card ι : ℝ)) :
    Summable fun n : ι → ℤ => ‖latticeVec ι b n‖ ^ r := by
  have hrank : Module.finrank ℤ (Submodule.span ℤ (Set.range b)) = Fintype.card ι :=
    Module.finrank_eq_card_basis (b.restrictScalars ℤ)
  have hs : Summable fun z : Submodule.span ℤ (Set.range b) => ‖(z : V)‖ ^ r :=
    _root_.ZLattice.summable_norm_rpow (Submodule.span ℤ (Set.range ⇑b)) r (by rwa [hrank])
  exact (summable_lattice_iff b (fun v : V => ‖v‖ ^ r)).1 hs

/-- The dual lattice of `⊕ᵢ ℤ bᵢ` is spanned by the dual basis. -/
theorem dualSubmodule_span (b : Basis ι ℝ V) :
    LinearMap.BilinForm.dualSubmodule (R := ℤ) (innerₗ V) (Submodule.span ℤ (Set.range b))
      = Submodule.span ℤ (Set.range (dualBasis b)) :=
  LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ) _ innerₗ_nondegenerate b

variable (V) in
/-- The dual lattice `L* = {y | ⟪y, x⟫ ∈ ℤ for all x ∈ L}` of a lattice in an inner product
space. -/
noncomputable def dual (L : Submodule ℤ V) : Submodule ℤ V :=
  LinearMap.BilinForm.dualSubmodule (R := ℤ) (innerₗ V) L

theorem mem_dual {L : Submodule ℤ V} {y : V} :
    y ∈ dual V L ↔ ∀ x ∈ L, ∃ n : ℤ, (n : ℝ) = ⟪y, x⟫ := by
  simp only [dual, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one, innerₗ_apply_apply]
  exact forall₂_congr fun x _ => by simp [eq_comm]

/-- The dual of the lattice spanned by `b` is spanned by the dual basis of `b`. -/
theorem dual_span (b : Basis ι ℝ V) :
    dual V (Submodule.span ℤ (Set.range b)) = Submodule.span ℤ (Set.range (dualBasis b)) :=
  dualSubmodule_span b

/-- **Poisson summation over a lattice in a Euclidean space.**
Ebeling, *Lattices and Codes*, Theorem 2.3.

If the periodisation of `f` over `Γ = ⊕ᵢ ℤ bᵢ` converges uniformly on compact sets and the
Fourier transform of `f` is summable over the dual lattice `Γ*`, then

`∑_{x ∈ Γ} f x = (covol Γ)⁻¹ ∑_{y ∈ Γ*} 𝓕 f y`. -/
theorem poissonSummation (b : Basis ι ℝ V) {f : C(V, ℂ)} (hf : ZSpan.LocallySummableOn b f)
    (hsum : Summable fun y : dual V (Submodule.span ℤ (Set.range b)) => 𝓕 (f : V → ℂ) y) :
    ∑' x : Submodule.span ℤ (Set.range b), f x
      = (covolume (Submodule.span ℤ (Set.range b)) volume)⁻¹
        • ∑' y : dual V (Submodule.span ℤ (Set.range b)), 𝓕 (f : V → ℂ) y := by
  rw [dual_span b] at hsum ⊢
  rw [tsum_lattice b (fun v => f v), tsum_lattice (dualBasis b) (fun v => 𝓕 (f : V → ℂ) v)]
  exact ZSpan.poissonSummation b hf ((summable_lattice_iff _ _).1 hsum)

/-- A practical sufficient condition for Ebeling's hypothesis (V2): polynomial decay of order
strictly larger than the rank. -/
theorem locallySummableOn_of_norm_le (b : Basis ι ℝ V) (f : C(V, ℂ)) {C p : ℝ}
    (hp : (Fintype.card ι : ℝ) < p)
    (hb : ∀ v : V, ‖f v‖ ≤ C * (1 + ‖v‖) ^ (-p)) :
    ZSpan.LocallySummableOn b f := by
  have hp0 : (0 : ℝ) ≤ p := le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg _) hp)
  have hC : 0 ≤ C := le_trans (norm_nonneg (f 0)) (by simpa using hb 0)
  intro K
  obtain ⟨r, hr⟩ := K.isCompact.isBounded.subset_closedBall (0 : V)
  set R : ℝ := max r 0 with hRdef
  have hR0 : (0 : ℝ) ≤ R := le_max_right _ _
  have hRK : (K : Set V) ⊆ Metric.closedBall 0 R :=
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  set D : ℝ := C * (1 + R) ^ p with hD
  have hD0 : (0 : ℝ) ≤ D := mul_nonneg hC (Real.rpow_nonneg (by linarith) _)
  have hbound : ∀ n : ι → ℤ,
      ‖(f.comp (ContinuousMap.addRight (ZSpan.latticeVec ι b n))).restrict (K : Set V)‖
        ≤ D * (1 + ‖ZSpan.latticeVec ι b n‖) ^ (-p) := by
    intro n
    set l := ZSpan.latticeVec ι b n with hl
    have hDnn : (0 : ℝ) ≤ D * (1 + ‖l‖) ^ (-p) :=
      mul_nonneg hD0 (Real.rpow_nonneg (by positivity) _)
    refine (ContinuousMap.norm_le _ hDnn).2 fun x => ?_
    have hx : ‖(x : V)‖ ≤ R := by simpa using hRK x.2
    have hlx : ‖l‖ ≤ ‖(x : V) + l‖ + ‖(x : V)‖ := by
      have h := norm_sub_le ((x : V) + l) (x : V)
      rwa [add_sub_cancel_left] at h
    have hprod : 1 + ‖l‖ ≤ (1 + R) * (1 + ‖(x : V) + l‖) := by
      nlinarith [norm_nonneg ((x : V) + l), hR0]
    have hmono : ((1 + R) * (1 + ‖(x : V) + l‖)) ^ (-p) ≤ (1 + ‖l‖) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hprod (by linarith)
    have hsplit : ((1 + R) * (1 + ‖(x : V) + l‖)) ^ (-p)
        = (1 + R) ^ (-p) * (1 + ‖(x : V) + l‖) ^ (-p) :=
      Real.mul_rpow (by linarith) (by positivity)
    have hcancel : (1 + R) ^ p * (1 + R) ^ (-p) = 1 := by
      rw [← Real.rpow_add (by linarith)]; simp
    show ‖f ((x : V) + l)‖ ≤ D * (1 + ‖l‖) ^ (-p)
    calc ‖f ((x : V) + l)‖
        ≤ C * (1 + ‖(x : V) + l‖) ^ (-p) := hb _
      _ = D * ((1 + R) ^ (-p) * (1 + ‖(x : V) + l‖) ^ (-p)) := by
          rw [hD, show C * (1 + R) ^ p * ((1 + R) ^ (-p) * (1 + ‖(x : V) + l‖) ^ (-p))
            = C * ((1 + R) ^ p * (1 + R) ^ (-p)) * (1 + ‖(x : V) + l‖) ^ (-p) from by ring,
            hcancel, mul_one]
      _ = D * ((1 + R) * (1 + ‖(x : V) + l‖)) ^ (-p) := by rw [hsplit]
      _ ≤ D * (1 + ‖l‖) ^ (-p) := mul_le_mul_of_nonneg_left hmono hD0
  have hmaj : Summable fun n : ι → ℤ => (1 + ‖ZSpan.latticeVec ι b n‖) ^ (-p) := by
    refine Summable.of_norm_bounded_eventually
      (summable_norm_rpow_latticeVec b (r := -p) (by linarith)) ?_
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (Set.finite_singleton (0 : ι → ℤ)) fun n hn => ?_
    by_contra hne
    refine hn ?_
    have hne' : ZSpan.latticeVec ι b n ≠ 0 := fun h =>
      hne (Set.mem_singleton_iff.2 ((latticeVec_eq_zero_iff b).1 h))
    have hpos : 0 < ‖ZSpan.latticeVec ι b n‖ := norm_pos_iff.2 hne'
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound (hmaj.mul_left D)

end ZLattice
