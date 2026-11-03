/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.QExpKatzSpanning
import VOA.Classification.COne.QExpKatzLevelOne

/-!
# The remaining Cramer-frame input, with its algebra proved

`LevelOneMultiplier24` asks for a common denominator `q^v t`, with `t(0)` a unit
in a finite extension of `ℤ[1/M]`, `p ∤ M`, such that the multiplied expansions
are finite sums of integral series times level-one modular forms. The latter
forms may have arbitrary complex coefficients; their finite coefficient lattices
are proved in `QExpKatzLevelOne`, not assumed.

This is a TRUE sufficient arithmetic input for positive weights, not an
unconditional theorem here. Its source is the same classical arithmetic
spanning-family theorem as `CyclotomicSpanning24` (Katz §§1.6–1.7, Diamond–Im
§12.3, with analytic comparison): `levelOneMultiplier24_of_cyclotomicSpanning`
proves this implication using denominator 1 and constant level-one forms.

For the proposed geometric route, `cramer_levelOne_coeff_lattice` proves that
an actual matrix with integral entries, the stated determinant factorization,
and level-one cofactor products suffices. Constructing such matrices from slash
transforms, checking integrality at all cusps, and proving the leading-unit
property are not done here. Neither mere nonvanishing of the determinant nor
algebraicity of coefficients is substituted for those conditions.
-/

open UpperHalfPlane
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne.SSHecke

/-- Local algebraic conclusion of a level-one multiplier identity. -/
theorem exists_lattice_of_levelOne_multiplier {M : ℕ} (hM : M ≠ 0)
    (A : Subalgebra (zInv M) ℂ) (hA : A.toSubmodule.FG)
    (a : PowerSeries ℂ) (v : ℕ) (t : PowerSeries A)
    (ht : IsUnit (PowerSeries.constantCoeff t)) {d : ℕ}
    (g : Fin d → PowerSeries A) (w : Fin d → ℤ)
    (G : (i : Fin d) → ModularForm 𝒮ℒ (w i))
    (heq : (PowerSeries.X ^ v * PowerSeries.map (algebraMap A ℂ) t) * a =
      ∑ i, PowerSeries.map (algebraMap A ℂ) (g i) * qExpansion 1 (G i)) :
    ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, PowerSeries.coeff n a ∈ awaySat M L := by
  choose K hK hcoeff using fun i => levelOne_hasFiniteCoeffLattice (w i) (G i)
  let L : Submodule A ℂ := ⨆ i, Submodule.span A (K i : Set ℂ)
  have hL : L.FG := Submodule.fg_iSup _ fun i => (hK i).span
  have hG : ∀ i n, PowerSeries.coeff n (qExpansion 1 (G i)) ∈ L :=
    fun i n => Submodule.mem_iSup_of_mem i (Submodule.subset_span (hcoeff i n))
  obtain ⟨J, hJ, hJL⟩ := fg_extension_exists_lattice hM A hA hL
  refine ⟨J, hJ, fun n => hJL _ (coeff_mem_of_mul_shift_unit v t ht ?_ n)⟩
  intro j
  rw [heq, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [mul_comm]
  exact coeff_mul_map_mem (g i) (hG i) j

/-- The arithmetic input in the normal form delivered by a Cramer frame.
It is implied by the classical cyclotomic spanning theorem, as proved below. -/
def LevelOneMultiplier24 (k : ℤ) : Prop :=
  ∀ (N : ℕ), 0 < N → 24 ∣ N → ∀ (p : ℕ), p.Prime → p.Coprime N →
    ∃ (M : ℕ), ¬ p ∣ M ∧ ∃ A : Subalgebra (zInv M) ℂ, A.toSubmodule.FG ∧
      ∃ (v : ℕ) (t : PowerSeries A), IsUnit (PowerSeries.constantCoeff t) ∧
        ∃ (d : ℕ) (g : Fin d → PowerSeries A),
          ∀ F : ModularForm
            (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k,
            ∃ (w : Fin d → ℤ) (G : (i : Fin d) → ModularForm 𝒮ℒ (w i)),
              (PowerSeries.X ^ v * PowerSeries.map (algebraMap A ℂ) t) * qExpansion 1 F =
                ∑ i, PowerSeries.map (algebraMap A ℂ) (g i) * qExpansion 1 (G i)

/-- The multiplier criterion implies precisely the requested away-from-prime bound. -/
theorem qExpPrinciple24Away_of_levelOneMultiplier {k : ℤ}
    (h : LevelOneMultiplier24 k) : QExpPrinciple24Away k := by
  intro N hN h24 F p hp hpN
  obtain ⟨M, hpM, A, hA, v, t, ht, d, g, hF⟩ := h N hN h24 p hp hpN
  obtain ⟨w, G, heq⟩ := hF F
  have hM : M ≠ 0 := fun h0 => hpM (h0 ▸ dvd_zero p)
  exact ⟨M, hpM, exists_lattice_of_levelOne_multiplier hM A hA _ v t ht g w G heq⟩

/-- Weight-two headline: all post-frame coefficient arguments are discharged. -/
theorem qExpPrinciple24Away_two_of_levelOneMultiplier
    (h : LevelOneMultiplier24 2) : QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_of_levelOneMultiplier h

/-- The residual has a classical certificate: cyclotomic spanning gives it with denominator 1.
This also documents its truth without claiming an unproved geometric frame construction. -/
theorem levelOneMultiplier24_of_cyclotomicSpanning {k : ℤ}
    (h : CyclotomicSpanning24 k) : LevelOneMultiplier24 k := by
  intro N hN h24 p hp hpN
  obtain ⟨ζ, hζ, d, f, hf, hspan⟩ := h N hN h24
  let A := cyclotomicAway N ζ
  let g : Fin d → PowerSeries A := fun i =>
    PowerSeries.mk fun n => ⟨PowerSeries.coeff n (qExpansion 1 (f i)), hf i n⟩
  have hg : ∀ i, PowerSeries.map (algebraMap A ℂ) (g i) = qExpansion 1 (f i) := by
    intro i
    ext n
    simp only [PowerSeries.coeff_map, g, PowerSeries.coeff_mk]
    rfl
  refine ⟨N, (Nat.Prime.coprime_iff_not_dvd hp).mp hpN, A,
    cyclotomicAway_fg hN hζ, 0, 1, by simp, d, g, ?_⟩
  intro F
  obtain ⟨c, hc⟩ := hspan F
  refine ⟨fun _ => 0, fun i => c i • (1 : ModularForm 𝒮ℒ 0), ?_⟩
  simp only [pow_zero, map_one, one_mul, hg, VOA.Huang.AndersonMoore.qExpansion_smul_one]
  rw [hc, qExpansion_sum_Gamma1]
  apply Finset.sum_congr rfl
  intro i _
  rw [PowerSeries.smul_eq_C_mul, mul_comm]

/-- An actual Cramer frame with integral entries and level-one cofactor products suffices.
The equality `det(H)^2 = q^v t` includes the crucial unit-leading-coefficient condition.
There is no assertion in this theorem that such a frame exists. -/
theorem cramer_levelOne_coeff_lattice {M : ℕ} (hM : M ≠ 0)
    (A : Subalgebra (zInv M) ℂ) (hA : A.toSubmodule.FG) {d : ℕ}
    (H : Matrix (Fin d) (Fin d) (PowerSeries A)) (b : Fin d → PowerSeries ℂ)
    (j : Fin d) (v : ℕ) (t : PowerSeries A)
    (ht : IsUnit (PowerSeries.constantCoeff t))
    (hdet : Matrix.det (fun i j => PowerSeries.map (algebraMap A ℂ) (H i j)) ^ 2 =
      PowerSeries.X ^ v * PowerSeries.map (algebraMap A ℂ) t)
    (w : Fin d → ℤ) (G : (i : Fin d) → ModularForm 𝒮ℒ (w i))
    (hnum : ∀ i,
      Matrix.det (fun i j => PowerSeries.map (algebraMap A ℂ) (H i j)) *
        Matrix.cramer (fun i j => PowerSeries.map (algebraMap A ℂ) (H i j)) b i =
          qExpansion 1 (G i)) :
    ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, PowerSeries.coeff n (b j) ∈ awaySat M L := by
  apply exists_lattice_of_levelOne_multiplier hM A hA (b j) v t ht (H j) w G
  rw [← hdet, cramer_det_sq]
  simp_rw [hnum]

end VOA.Classification.COne.SSHecke
