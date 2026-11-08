import VOA.Foundations.LatticeAlgebraTwisted
import Mathlib.Tactic.FinCases

/-!
# The even unimodular hyperbolic plane

The underlying lattice of `II_{1,1}` has Gram matrix `[[0,1],[1,0]]`.
Its norm is `2xy`; its charged ground-state weight is `xy`.
No positivity assumption occurs in these constructions.
-/

namespace VOA.Moonshine.ConwayNorton

open scoped TensorProduct
open IntegralLattice

/-- Gram matrix of the hyperbolic plane in its isotropic integral basis. -/
def hyperbolicGram : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- The integral hyperbolic plane `II_{1,1}`, with norm `2xy`. -/
noncomputable def lorentzianLattice : IntegralLattice where
  carrier := Fin 2 → ℤ
  form := Matrix.toBilin' hyperbolicGram
  isSymm := by
    rw [LinearMap.BilinForm.isSymm_def]
    intro x y
    simp [hyperbolicGram, Matrix.toBilin'_apply, Fin.sum_univ_two]
    ring

theorem lorentzian_form_apply (x y : lorentzianLattice.carrier) :
    lorentzianLattice.form x y = x 0 * y 1 + x 1 * y 0 := by
  change Matrix.toBilin' hyperbolicGram x y = _
  simp [hyperbolicGram, Matrix.toBilin'_apply, Fin.sum_univ_two]

theorem lorentzian_even : lorentzianLattice.Even := by
  intro x
  refine ⟨x 0 * x 1, ?_⟩
  rw [lorentzian_form_apply]
  ring

theorem lorentzian_rank : rank lorentzianLattice = 2 := by
  exact Module.finrank_eq_card_basis (Pi.basisFun ℤ (Fin 2))

theorem lorentzian_gram_det : hyperbolicGram.det = -1 := by
  norm_num [hyperbolicGram, Matrix.det_fin_two]

theorem lorentzian_form_nondegenerate : lorentzianLattice.form.Nondegenerate := by
  have hleft : lorentzianLattice.form.SeparatingLeft := by
    intro x hx
    have hx0 := hx ![0, 1]
    have hx1 := hx ![1, 0]
    simp only [lorentzian_form_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, mul_one, mul_zero, zero_add, add_zero] at hx0 hx1
    apply funext
    intro i
    fin_cases i
    · exact hx0
    · exact hx1
  exact ⟨hleft, fun x hx => hleft x (fun y => by
    rw [IntegralLattice.form_symm lorentzianLattice]; exact hx y)⟩

theorem lorentzian_not_posDef : ¬ lorentzianLattice.PosDef := by
  intro h
  have hx : (![1, -1] : Fin 2 → ℤ) ≠ 0 := by
    intro heq
    have := congrFun heq 0
    norm_num at this
  have hp := h ![1, -1] hx
  norm_num [lorentzian_form_apply] at hp

/-- The base-changed isotropic basis; shared carrier with the standard lattice. -/
noncomputable def lorentzianRealBasis :
    Module.Basis (Fin 2) ℝ (ℝ ⊗[ℤ] lorentzianLattice.carrier) := stdLatticeBasis 2

theorem lorentzianRealBasis_apply (j : Fin 2) :
    lorentzianRealBasis j =
      (1 : ℝ) ⊗ₜ[ℤ] (Pi.single j (1 : ℤ) : lorentzianLattice.carrier) :=
  stdLatticeBasis_apply 2 j

theorem lorentzian_real_form_basis (i j : Fin 2) :
    lorentzianLattice.formℝ (lorentzianRealBasis i) (lorentzianRealBasis j) =
      if i = j then 0 else 1 := by
  rw [lorentzianRealBasis_apply, lorentzianRealBasis_apply]
  have h := formℝ_tmul lorentzianLattice (Pi.single i (1 : ℤ)) (Pi.single j (1 : ℤ))
  trans (lorentzianLattice.form (Pi.single i (1 : ℤ)) (Pi.single j (1 : ℤ)) : ℝ)
  · exact h
  rw [lorentzian_form_apply]
  fin_cases i <;> fin_cases j <;> norm_num [Pi.single_apply]

theorem lorentzian_real_pairing_coordinate
    (x : ℝ ⊗[ℤ] lorentzianLattice.carrier) (j : Fin 2) :
    lorentzianLattice.formℝ x (lorentzianRealBasis j) =
      lorentzianRealBasis.repr x j.rev := by
  conv_lhs => rw [← lorentzianRealBasis.sum_repr x]
  simp only [Fin.sum_univ_two]
  fin_cases j <;> simp [Fin.rev, lorentzian_real_form_basis]

/-- Unimodularity in the repository's actual real dual-lattice sense. -/
theorem lorentzian_selfDual : lorentzianLattice.SelfDual := by
  intro x
  constructor
  · intro hx
    choose k hk using fun j : Fin 2 => hx (Pi.single j.rev (1 : ℤ))
    refine ⟨k, lorentzianRealBasis.repr.injective ?_⟩
    ext j
    have hc : lorentzianRealBasis.repr (lorentzianLattice.toReal k) j = (k j : ℝ) :=
      stdLattice_toReal_repr 2 k j
    rw [hc]
    have hb : lorentzianLattice.toReal (Pi.single j.rev (1 : ℤ)) =
        lorentzianRealBasis j.rev := by
      rw [lorentzianRealBasis_apply]
      rfl
    have hj := hk j
    rw [hb, lorentzian_real_pairing_coordinate, Fin.rev_rev] at hj
    exact hj.symm
  · rintro ⟨v, rfl⟩
    exact lorentzianLattice.le_dual v

/-- Half the norm, the integral ground-state conformal weight. -/
def lorentzianEnergy (x : lorentzianLattice.carrier) : ℤ := x 0 * x 1

theorem lorentzianEnergy_half_norm (x : lorentzianLattice.carrier) :
    2 * lorentzianEnergy x = lorentzianLattice.form x x := by
  rw [lorentzianEnergy, lorentzian_form_apply]
  ring

theorem lorentzianEnergy_add (x y : lorentzianLattice.carrier) :
    lorentzianEnergy (x + y) = lorentzianEnergy x + lorentzianEnergy y +
      lorentzianLattice.form x y := by
  simp only [lorentzianEnergy, lorentzian_form_apply]
  change (x 0 + y 0) * (x 1 + y 1) = _
  ring

/-- Charged ground states have no uniform lower energy bound. -/
theorem lorentzianEnergy_unbounded_below (N : ℤ) :
    ∃ x : lorentzianLattice.carrier, lorentzianEnergy x < N := by
  exact ⟨![1, N - 1], by simp [lorentzianEnergy]⟩

/-- The existing FLM cocycle works without positive definiteness. -/
noncomputable def lorentzianCocycle :
    lorentzianLattice.carrier → lorentzianLattice.carrier → ℂ :=
  latticeCocycle lorentzianLattice

theorem lorentzianCocycle_law (x y z : lorentzianLattice.carrier) :
    lorentzianCocycle x y * lorentzianCocycle (x + y) z =
      lorentzianCocycle y z * lorentzianCocycle x (y + z) :=
  latticeCocycle_cocycleLaw lorentzianLattice x y z

theorem lorentzianCocycle_commutator (x y : lorentzianLattice.carrier) :
    lorentzianCocycle x y * lorentzianCocycle y x =
      (-1 : ℂ) ^ (lorentzianLattice.form x y) :=
  latticeCocycle_comm lorentzianLattice lorentzian_even x y

theorem lorentzianCocycle_normalized (x : lorentzianLattice.carrier) :
    lorentzianCocycle 0 x = 1 ∧ lorentzianCocycle x 0 = 1 :=
  ⟨latticeCocycle_zero_left lorentzianLattice x,
    latticeCocycle_zero_right lorentzianLattice x⟩

theorem lorentzianTwistedProduct_assoc (f g h : lorentzianLattice.carrier →₀ ℂ) :
    twMul lorentzianLattice (twMul lorentzianLattice f g) h =
      twMul lorentzianLattice f (twMul lorentzianLattice g h) :=
  twMul_assoc lorentzianLattice f g h

end VOA.Moonshine.ConwayNorton
