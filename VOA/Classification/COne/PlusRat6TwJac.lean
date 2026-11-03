import VOA.Classification.COne.PlusRat6Main
import VOA.Classification.COne.PlusTwistCharacters

/-! # Three consequences of the twisted Jacobi identity (order two, any VOA)

For a `g`-twisted module `T` of order `2` (`T.YM u k = u₍k/2₎`):

* `tw_deriv`: `Y(L(-1)u, k-2) = (1 - k/2) Y(u, k-4)` on the support coset of `u`;
* `tw_comm`: for `g`-fixed `u`, `[u₍ₙ₎, v₍ₘ/₂₎] = Σ_{i ≤ n} C(n,i) (u₍ᵢ₎v)₍(2n+m-2i)/2₎`;
* `tw_iter_vac`: for `u` in the `-1`-eigenspace and a vector `x` killed by the relevant
  non-negative modes of `u` and `v`, `Σ_i C(1/2,i) (u₍₋ₙ₊ᵢ₎v)₍(1+m-2i)/2₎ x = 0`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat6
open VOA
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {g : Aut W} (T : TwistedModule g 2 M)

theorem L_neg_one_eq_smul_vac (u : V) : W.L (-1) u = W.smul u (-2) W.vacuum := by
  have hc := VertexOperatorAlgebra.creation_pow W u 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul] at hc
  rw [VertexOperatorAlgebra.T_eq_Lneg1, show (-(1 : ℤ) - 1) = -2 from by norm_num] at hc
  exact hc.symm

theorem smul_vac_neg_one (u : V) : W.smul u (-1) W.vacuum = u := (W.creation u).1

theorem smul_vac_nonneg (u : V) {n : ℤ} (hn : 0 ≤ n) : W.smul u n W.vacuum = 0 :=
  (W.creation u).2 n hn

theorem tw_vac (k : ℤ) (x : M) : T.YM W.vacuum k x = if k = -2 then x else 0 := by
  rw [T.vacuum_YM]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (by exact_mod_cast h1) h2
  · exact absurd (by exact_mod_cast h2) h1
  · rfl

/-- **Derivative property** of a twisted module. -/
theorem tw_deriv (j : ℕ) (u : V) (hu : u ∈ g.twistedEigenspace 2 j) (k : ℤ)
    (hk : (k + j) % 2 = 0) (x : M) :
    T.YM (W.L (-1) u) (k - 2) x = (1 - (k : ℂ) / 2) • T.YM u (k - 4) x := by
  have J := T.jacobi j u hu W.vacuum x (-2) k (-2) (by exact_mod_cast hk)
  rw [finsum_eq_single _ (0 : ℤ) (by
      intro i hi
      rcases lt_or_gt_of_ne hi with hneg | hpos
      · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
      · rw [tw_vac, tw_vac, if_neg (by push_cast; omega), if_neg (by push_cast; omega),
          map_zero, smul_zero, sub_zero, smul_zero])] at J
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 2) _ (by
      intro i hi
      rw [Function.mem_support] at hi
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      apply hi
      rw [smul_vac_nonneg u (by omega), map_zero, Pi.zero_apply, LinearMap.zero_apply,
        smul_zero])] at J
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at J
  have e1 : (-2 : ℤ) + ((0 : ℕ) : ℤ) = -2 := by norm_num
  have e2 : (-2 : ℤ) + ((1 : ℕ) : ℤ) = -1 := by norm_num
  have e3 : k + -2 - ((0 : ℕ) : ℤ) * ((2 : ℕ) : ℤ) = k - 2 := by push_cast; ring
  have e4 : k + -2 - ((1 : ℕ) : ℤ) * ((2 : ℕ) : ℤ) = k - 4 := by push_cast; ring
  have e5 : (-2 : ℤ) * ((2 : ℕ) : ℤ) + k - 0 * ((2 : ℕ) : ℤ) = k - 4 := by push_cast; ring
  have e6 : (-2 : ℤ) + 0 * ((2 : ℕ) : ℤ) = -2 := by norm_num
  have e7 : (-2 : ℤ) * ((2 : ℕ) : ℤ) + -2 - 0 * ((2 : ℕ) : ℤ) = -6 := by norm_num
  rw [e1, e2, smul_vac_neg_one, ← L_neg_one_eq_smul_vac, e3, e4, e5, e6, e7, tw_vac, tw_vac,
    if_pos rfl, if_neg (by norm_num)] at J
  simp only [cbz_zero, mul_one, one_smul, cbinom_zero, smul_zero, sub_zero] at J
  have hc1 : cbinom ((k : ℂ) / ((2 : ℕ) : ℂ)) 1 = (k : ℂ) / 2 := by
    simp [cbinom]
  rw [hc1, negOnePow, if_pos (by decide)] at J
  simp only [one_smul] at J
  rw [sub_smul, one_smul, eq_sub_iff_add_eq]
  exact J.symm

/-- **Commutator formula** for a `g`-fixed state. -/
theorem tw_comm (u : V) (hu : g u = u) (n : ℕ) (v : V) (x : M) (m : ℤ) :
    T.YM u (2 * n) (T.YM v m x) - T.YM v m (T.YM u (2 * n) x) =
      ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : ℂ) •
        T.YM (W.smul u i v) (2 * n + m - 2 * i) x := by
  have J := T.jacobi 0 u (TwistedPlus.mem_twistedEigenspace_zero hu) v x 0 (2 * n) m
    (by push_cast; omega)
  rw [finsum_eq_single _ (0 : ℤ) (by
      intro i hi
      rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])] at J
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + 1)) _ (by
      intro i hi
      rw [Function.mem_support] at hi
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      apply hi
      rw [show (((2 * (n : ℤ) : ℤ) : ℂ) / ((2 : ℕ) : ℂ)) = ((n : ℕ) : ℂ) by push_cast; ring,
        TwistedReduction.cbinom_natCast_of_lt (by omega), zero_smul])] at J
  simp only [cbz_zero, mul_one, negOnePow, if_pos (show Even (0 : ℤ) by decide), one_smul,
    zero_mul, sub_zero, zero_add] at J
  push_cast at J
  rw [add_zero, add_zero] at J
  rw [J]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show ((2 : ℂ) * (n : ℂ) / 2) = ((n : ℕ) : ℂ) by ring, TwistedReduction.cbinom_natCast]
  congr 2
  ring

/-- **Iterates on a vacuum-like vector.** -/
theorem tw_iter_vac (u : V) (hu : u ∈ g.twistedEigenspace 2 1) (v : V) (x : M) (n m : ℤ)
    (hux : ∀ i : ℕ, T.YM u (1 + 2 * i) x = 0) (hvx : ∀ i : ℕ, T.YM v (m + 2 * i) x = 0) :
    ∑ᶠ i : ℕ, cbinom ((1 : ℂ) / 2) i • T.YM (W.smul u (-n + i) v) (1 + m - 2 * i) x = 0 := by
  have J := T.jacobi 1 u hu v x (-n) 1 m (by norm_num)
  rw [finsum_eq_zero_of_forall_eq_zero (by
      intro i
      rcases lt_or_ge i 0 with hneg | hnn
      · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
      · obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' := ⟨i.toNat, by omega⟩
        have h1 := hvx i'
        have h2 := hux i'
        rw [show m + (i' : ℤ) * ((2 : ℕ) : ℤ) = m + 2 * i' by push_cast; ring, h1,
          show (1 : ℤ) + (i' : ℤ) * ((2 : ℕ) : ℤ) = 1 + 2 * i' by push_cast; ring, h2,
          map_zero, map_zero, smul_zero, sub_zero, smul_zero])] at J
  rw [J]
  refine finsum_congr (fun i => ?_)
  congr 2
  · push_cast; ring
  · push_cast; ring

end VOA.Classification.COne.PlusRat6
