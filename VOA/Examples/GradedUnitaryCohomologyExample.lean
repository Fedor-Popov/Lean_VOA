/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.GradedUnitaryCohomologyTransfer
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Non-vacuity witness for `KahlerComplex`

A five-dimensional complex `ℂ⁵` realizing Beem–Garner's quartet (Figure 3.1) together with
one harmonic singlet. Basis and bidegrees `(2R, gh)`:

* `e₀ = x̃` in `(0,0)`, `e₁ = Q⁻x̃` in `(1,1)`, `e₂ = Q⁺x̃` in `(1,-1)`,
  `e₃ = Q⁻Q⁺x̃` in `(2,0)`, and the singlet `e₄` in `(0,0)`.

The four pieces are `Q⁻ : e₀ ↦ e₁, e₂ ↦ e₃`; `S⁺ = (Q⁻)†`; `Q⁺ : e₀ ↦ e₂, e₁ ↦ -e₃`;
`S⁻ = -(Q⁺)†`, with the standard Hermitian form and `c = 1`. Every `KahlerComplex` hypothesis
is verified, the differentials are nonzero, and the harmonic space is nonzero (`e₄`) while
`x̃` is not harmonic. So the hypotheses are consistent and not degenerate.
-/

namespace VOA.GradedUnitaryCohomology.Example

open VOA.LeeYangCosetTransfer

/-- The bidegrees `(2R, gh)` of the basis vectors. -/
def bideg : Fin 5 → ℤ × ℤ := ![(0, 0), (1, 1), (1, -1), (2, 0), (0, 0)]

/-- Vectors supported on basis vectors of bidegree `a`. -/
def deg (a : ℤ × ℤ) : Submodule ℂ (Fin 5 → ℂ) where
  carrier := {x | ∀ i, bideg i ≠ a → x i = 0}
  add_mem' hx hy i hi := by simp [hx i hi, hy i hi]
  zero_mem' _ _ := rfl
  smul_mem' c x hx i hi := by simp [hx i hi]

/-- The standard Hermitian form. -/
noncomputable def P : SesqForm (Fin 5 → ℂ) where
  toFun x y := ∑ i, (starRingEnd ℂ) (x i) * y i
  add_left a a' b := by simp [add_mul, Finset.sum_add_distrib]
  smul_left z a b := by simp [Finset.mul_sum, mul_assoc]
  add_right a b b' := by simp [mul_add, Finset.sum_add_distrib]
  smul_right z a b := by simp [Finset.mul_sum, mul_left_comm]

theorem P_apply (x y : Fin 5 → ℂ) :
    P x y = ∑ i, (starRingEnd ℂ) (x i) * y i := rfl

/-- Build a linear endomorphism of `ℂ⁵` from a coordinate formula. -/
def mkLin (f : (Fin 5 → ℂ) → (Fin 5 → ℂ))
    (hadd : ∀ x y, f (x + y) = f x + f y) (hsmul : ∀ (c : ℂ) x, f (c • x) = c • f x) :
    (Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun := f
  map_add' := hadd
  map_smul' := hsmul

/-- `Q⁻`. -/
def Qm : (Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) :=
  mkLin (fun x => ![0, x 0, 0, x 2, 0])
    (fun x y => by ext i; fin_cases i <;> simp)
    (fun c x => by ext i; fin_cases i <;> simp)
/-- `S⁺ = (Q⁻)†`. -/
def Sp : (Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) :=
  mkLin (fun x => ![x 1, 0, x 3, 0, 0])
    (fun x y => by ext i; fin_cases i <;> simp)
    (fun c x => by ext i; fin_cases i <;> simp)
/-- `Q⁺`. -/
def Qp : (Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) :=
  mkLin (fun x => ![0, 0, x 0, -x 1, 0])
    (fun x y => by ext i; fin_cases i <;> simp; ring)
    (fun c x => by ext i; fin_cases i <;> simp)
/-- `S⁻ = -(Q⁺)†`. -/
def Sm : (Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) :=
  mkLin (fun x => ![-x 2, x 3, 0, 0, 0])
    (fun x y => by ext i; fin_cases i <;> simp; ring)
    (fun c x => by ext i; fin_cases i <;> simp)

@[simp] theorem Qm_apply (x : Fin 5 → ℂ) : Qm x = ![0, x 0, 0, x 2, 0] := rfl
@[simp] theorem Sp_apply (x : Fin 5 → ℂ) : Sp x = ![x 1, 0, x 3, 0, 0] := rfl
@[simp] theorem Qp_apply (x : Fin 5 → ℂ) : Qp x = ![0, 0, x 0, -x 1, 0] := rfl
@[simp] theorem Sm_apply (x : Fin 5 → ℂ) : Sm x = ![-x 2, x 3, 0, 0, 0] := rfl

theorem single_mem (i : Fin 5) (z : ℂ) : Pi.single i z ∈ deg (bideg i) := by
  intro k hk
  have : k ≠ i := fun h => hk (h ▸ rfl)
  simp [this]

theorem span : iSup deg = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ i, Pi.single i (x i) := (Finset.univ_sum_single x).symm
  rw [hx]
  exact Submodule.sum_mem _ fun i _ => (le_iSup deg (bideg i)) (single_mem i (x i))

theorem orth (a b : ℤ × ℤ) (hab : a ≠ b) (x : Fin 5 → ℂ) (hx : x ∈ deg a)
    (y : Fin 5 → ℂ) (hy : y ∈ deg b) : P x y = 0 := by
  rw [P_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : bideg i = a
  · rw [hy i (fun h => hab (hi.symm.trans h)), mul_zero]
  · rw [hx i hi, map_zero, zero_mul]

theorem pos : IsPosOn P ⊤ := by
  intro x _ hx
  refine ⟨∑ i, Complex.normSq (x i), ?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      exact hx (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
    exact lt_of_lt_of_le (Complex.normSq_pos.mpr hi)
      (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (x j)) (Finset.mem_univ i))
  · rw [P_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]

/-- Shift bookkeeping: membership of a coordinate formula in a shifted piece. -/
theorem homog {f : (Fin 5 → ℂ) → (Fin 5 → ℂ)} {s : ℤ × ℤ}
    (hf : ∀ x i, f x i ≠ 0 → ∃ j, bideg j + s = bideg i ∧ x j ≠ 0) (a : ℤ × ℤ)
    (x : Fin 5 → ℂ) (hx : x ∈ deg a) : f x ∈ deg (a + s) := by
  intro i hi
  by_contra hne
  obtain ⟨j, hj, hxj⟩ := hf x i hne
  apply hxj
  apply hx j
  intro h
  apply hi
  rw [← hj, h]

set_option linter.flexible false in
/-- The witness `KahlerComplex`. -/
noncomputable def quartet : KahlerComplex (Fin 5 → ℂ) where
  P := P
  pos := pos
  deg := deg
  span := span
  orth := orth
  Qm := Qm
  Sm := Sm
  Qp := Qp
  Sp := Sp
  Qm_deg := homog (fun x i h => by
    fin_cases i <;> simp at h
    · exact ⟨0, rfl, h⟩
    · exact ⟨2, rfl, h⟩)
  Sm_deg := homog (fun x i h => by
    fin_cases i <;> simp at h
    · exact ⟨2, rfl, h⟩
    · exact ⟨3, rfl, h⟩)
  Qp_deg := homog (fun x i h => by
    fin_cases i <;> simp at h
    · exact ⟨0, rfl, h⟩
    · exact ⟨1, rfl, h⟩)
  Sp_deg := homog (fun x i h => by
    fin_cases i <;> simp at h
    · exact ⟨1, rfl, h⟩
    · exact ⟨3, rfl, h⟩)
  c := 1
  c_sq := by norm_num
  adj_Qm x y := by
    simp [P_apply, Fin.sum_univ_five]
  adj_Sm x y := by
    simp [P_apply, Fin.sum_univ_five]; ring
  sq_zero := by
    ext x i; fin_cases i <;> simp
  anticomm := by
    ext x i; fin_cases i <;> simp

/-- The differentials are not zero: `𝐐⁻ x̃ = Q⁻ x̃ ≠ 0`. -/
theorem D_ne_zero : quartet.D ≠ 0 := by
  intro h
  have := congrFun (LinearMap.congr_fun h (Pi.single 0 1)) 1
  simp [KahlerComplex.D, quartet] at this

/-- The singlet is a nonzero harmonic vector, so the harmonic space (= cohomology) is nonzero. -/
theorem singlet_mem_harm : (Pi.single 4 1 : Fin 5 → ℂ) ∈ quartet.harm := by
  rw [KahlerComplex.mem_harm_iff]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> simp [quartet]

theorem singlet_ne_zero : (Pi.single 4 1 : Fin 5 → ℂ) ≠ 0 := by
  intro h; have := congrFun h 4; simp at this

/-- The quartet top `x̃` is not harmonic. -/
theorem xtilde_not_mem_harm : (Pi.single 0 1 : Fin 5 → ℂ) ∉ quartet.harm := by
  rw [KahlerComplex.mem_harm_iff]
  rintro ⟨h, -⟩
  have := congrFun h 1
  simp [quartet] at this

/-! ### The form/conjugation datum on the witness -/

/-- `i^{-2R}` on each basis vector. -/
noncomputable def wt (i : Fin 5) : ℂ := (Complex.I ^ (bideg i).1)⁻¹

/-- The invariant bilinear form `B x y = Σ i^{-2R_i} x_i y_i`. -/
noncomputable def B : LinearMap.BilinForm ℂ (Fin 5 → ℂ) :=
  LinearMap.mk₂ ℂ (fun x y => ∑ i, wt i * x i * y i)
    (fun x x' y => by simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

/-- The conjugation: componentwise complex conjugation. -/
def ρ : (Fin 5 → ℂ) →ₗ⋆[ℂ] (Fin 5 → ℂ) where
  toFun x i := (starRingEnd ℂ) (x i)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

@[simp] theorem ρ_apply (x : Fin 5 → ℂ) (i : Fin 5) : ρ x i = (starRingEnd ℂ) (x i) := rfl

/-- `h x y = B (ρ x) y`. -/
noncomputable def h : SesqForm (Fin 5 → ℂ) where
  toFun x y := B (ρ x) y
  add_left a a' b := by simp
  smul_left z a b := by simp
  add_right a b b' := by simp
  smul_right z a b := by simp

theorem ρ_comm (T : (Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ))
    (hT : T = Qm ∨ T = Sm ∨ T = Qp ∨ T = Sp) (x : Fin 5 → ℂ) : T (ρ x) = ρ (T x) := by
  rcases hT with rfl | rfl | rfl | rfl <;> ext i <;> fin_cases i <;> simp

theorem ρ_ρ (x : Fin 5 → ℂ) : ρ (ρ x) = x := by ext i; simp

theorem ρ_harmDeg (j : ℤ) (x : Fin 5 → ℂ) (hx : x ∈ quartet.harmDeg (j, 0)) :
    ρ x ∈ quartet.harmDeg (j, 0) := by
  obtain ⟨hh, hd⟩ := hx
  obtain ⟨h1, h2, h3, h4⟩ := (KahlerComplex.mem_harm_iff _ x).mp hh
  refine ⟨(KahlerComplex.mem_harm_iff _ _).mpr ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · change Qm (ρ x) = 0; rw [ρ_comm Qm (by simp), show Qm x = 0 from h1, map_zero]
  · change Sm (ρ x) = 0; rw [ρ_comm Sm (by simp), show Sm x = 0 from h2, map_zero]
  · change Qp (ρ x) = 0; rw [ρ_comm Qp (by simp), show Qp x = 0 from h3, map_zero]
  · change Sp (ρ x) = 0; rw [ρ_comm Sp (by simp), show Sp x = 0 from h4, map_zero]
  · intro i hi; simp [show x i = 0 from hd i hi]

/-- The witness `GUData`: every hypothesis verified. -/
noncomputable def guData : GUData quartet where
  B := B
  ρ := ρ
  h := h
  h_eq _ _ := rfl
  P_eq j g x hx y := by
    change ∑ i, (starRingEnd ℂ) (x i) * y i = Complex.I ^ j * ∑ i, wt i * ρ x i * y i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : bideg i = (j, g)
    · rw [wt, hi, ρ_apply]
      field_simp [zpow_ne_zero j Complex.I_ne_zero]
    · simp [show x i = 0 from hx i hi]
  ρ_maps := ρ_harmDeg
  ρ_onto j y hy := ⟨ρ y, ρ_harmDeg j y hy, ρ_ρ y⟩

/-- The positivity theorem applies to a nonzero vector: the singlet lies in the layer `p = 0`
of the induced flag, and `signedForm h 0` is positive on that layer. -/
theorem singlet_mem_layer : (Pi.single 4 1 : Fin 5 → ℂ) ∈ guData.layer 0 0 := by
  rw [guData.layer_eq le_rfl]
  refine ⟨singlet_mem_harm, ?_⟩
  exact single_mem 4 1

theorem singlet_signed_pos :
    ∃ r : ℝ, 0 < r ∧ signedForm guData.h 0 (Pi.single 4 1) (Pi.single 4 1) = (r : ℂ) :=
  guData.layer_signed_pos 0 le_rfl _ singlet_mem_layer singlet_ne_zero

end VOA.GradedUnitaryCohomology.Example
