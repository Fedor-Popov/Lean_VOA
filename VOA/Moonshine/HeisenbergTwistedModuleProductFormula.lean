/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.HeisenbergTwistedModuleWords
import VOA.Core.Borcherds
import VOA.Core.Automorphism

/-!
# The twisted product formula for the twisted Heisenberg module  (Moonshine step M6a)

With `F_e(u) = resc (Y^T u) 2 e` (`Moonshine.FT`), the twisted product formula of the reduction
`TwistedReduction.twistedJacobi_of_local_pf`, inverted, says that `u ↦ F(u)` is a homomorphism
for the twisted products of `HeisenbergTwistedModuleTwistedComm`:

  `star (e/2) (F_e u) ℓ (F_{e'} v) = F_{e+e'}(u₍ℓ₎v)`     (`starPF`).

It is proved here for every `σ`-eigenvector `u ∈ 𝒱ʲ` with `e ≡ j (mod 2)`, every state `v` and
every class `e'`, by induction on `v`:

* **generators** (`genPF`): `star ½ (Fgen b) ℓ F_e(w) = F_{e+1}(b₍ℓ₎w)` for all `ℓ`, `w` — the
  creation modes are `FT_gen_creation`; the annihilation modes follow by induction on `w` from the
  twisted commutator formula `star_comm`, the generator products `star_gen_gen` and the
  Heisenberg commutator in `heisVOA1 r`;
* **translation** (`FT_translation`): `∂F_e(u) − (e/2) z⁻¹ F_e(u) = F_e(L₋₁u)`, by induction on
  `u` from `deriv_star`; hence the vacuum case `star (e/2) (F_e u) ℓ 1 = F_e(u₍ℓ₎𝟙)`
  (`starPF_vacuum`, via `star_deriv_one`);
* **the induction step**: `v = b₍₋ₙ₋₁₎v'`, using `star_comm` with the generator outside, `genPF`
  for `b₍ₛ₎u`, and the commutator formula of `heisVOA1 r`.

Binomial inversion (`TwistedReduction.pf_of_inverse`) turns `starPF` into the product formula
`hpf` of `twistedJacobi_YT_of_productFormula`, giving `twistedJacobi_YT`:
**`TwistedJacobi (sigma1 r) 2 (YT r)`**, the corrected DLM twisted Jacobi identity for the
concrete twisted vertex operator, for all pairs of states.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

namespace Moonshine

open MvPolynomial TwistedHeisenberg HeisenbergN TwistedReduction
open Module (End)
open scoped BigOperators

variable (r : ℕ)

/-! ## Facts in `heisVOA1 r` -/

/-- The commutator formula of a VOA, as a `range` sum with any bound past the products. -/
theorem voa_comm {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)
    (u v x : 𝒱) (a b : ℤ) (L : ℕ) (hL : ∀ k : ℕ, L ≤ k → W.smul u k v = 0) :
    W.smul u a (W.smul v b x) - W.smul v b (W.smul u a x)
      = ∑ j ∈ Finset.range L, gBinom a j • W.smul (W.smul u j v) (a + b - j) x := by
  obtain ⟨N, hzero, hcomm⟩ := VertexOperatorAlgebra.commBound W u v a b
  have h1 : W.smul u a (W.smul v b x) - W.smul v b (W.smul u a x)
      = ⁅mode (W.Y u) a, mode (W.Y v) b⁆ x := by
    rw [Ring.lie_def]; rfl
  rw [h1, hcomm, LinearMap.sum_apply,
    Fin.sum_univ_eq_sum_range (fun j => (gBinom a j • mode (W.Y (W.smul u j v)) (a + b - j)) x) N]
  have hv : ∀ K : ℕ, (∀ k : ℕ, K ≤ k → W.smul u k v = 0) → ∀ j : ℕ, K ≤ j →
      gBinom a j • W.smul (W.smul u j v) (a + b - j) x = 0 := by
    intro K hK j hj
    rw [hK j hj, PreVertexAlgebra.smul_zero_left, smul_zero]
  simp only [LinearMap.smul_apply]
  change ∑ j ∈ Finset.range N, gBinom a j • W.smul (W.smul u j v) (a + b - j) x = _
  rw [← sum_range_eq_of_vanish _ (le_max_left N L) (hv N hzero),
    ← sum_range_eq_of_vanish _ (le_max_right N L) (hv L hL)]

/-- Products of `σ`-eigenvectors are `σ`-eigenvectors. -/
theorem smul_mem_eigen {j j' : ℕ} {u v : FockN r}
    (hu : u ∈ (sigma1 r).twistedEigenspace 2 j) (hv : v ∈ (sigma1 r).twistedEigenspace 2 j')
    (n : ℤ) : (heisVOA1 r).smul u n v ∈ (sigma1 r).twistedEigenspace 2 (j + j') := by
  rw [mem_twistedEigenspace_two_iff] at hu hv ⊢
  have h := (sigma1 r).map_smul' u n v
  simp only [sigmaHeisAut_apply] at h
  change LatGen.sigmaN r ((heisVOA1 r).smul u n v) = _
  rw [show (heisVOA1 r).smul u n v = (heisVOA1 r).toPreVertexAlgebra.smul u n v from rfl, h, hu, hv,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right, smul_smul, pow_add, mul_comm]

theorem X_mem_eigen (b : Fin r) : (X (0, b) : FockN r) ∈ (sigma1 r).twistedEigenspace 2 1 :=
  X_mem_twistedEigenspace_one r 1 one_ne_zero (0, b)

theorem vacuum_mem_eigen : vacuumN r ∈ (sigma1 r).twistedEigenspace 2 0 :=
  vacuumN_mem_twistedEigenspace_zero r 1 one_ne_zero

theorem omega_mem_eigen : (heisVOA1 r).conformalVector ∈ (sigma1 r).twistedEigenspace 2 0 := by
  rw [mem_twistedEigenspace_two_iff, pow_zero, one_smul]
  exact sigmaN_ωN r 1

/-- The products of two generators, `b₍ⱼ₎c = δ_{j,1} δ_{bc} 𝟙` for `j ≥ 0`, in `range 2` form. -/
theorem smul_X_X_two_le (b c : Fin r) (k : ℕ) (hk : 2 ≤ k) :
    (heisVOA1 r).smul (X (0, b)) k (X (0, c)) = 0 := by
  rw [smul_X_X_nonneg r b c (by omega), if_neg (by omega)]

/-! ## The vacuum fields -/

theorem FT_zero_vacuum : FT r 0 (vacuumN r) = Fld.one := by
  rw [vacuumN, show (1 : FockN r) = monomial 0 1 by rw [monomial_zero', map_one], FT_monomial]
  simp

theorem FT_vacuum_even (k : ℤ) : FT r (2 * k) (vacuumN r) = fzmul k Fld.one := by
  rw [show 2 * k = 0 + 2 * k by ring, FT_shift, FT_zero_vacuum]

theorem FT_vacuum_odd {e : ℤ} (he : e % 2 = 1) : FT r e (vacuumN r) = 0 :=
  FT_eq_zero_of_parity r (vacuum_mem_eigen r) (by push_cast; omega)

theorem smul_vacuumN (n : ℤ) (w : FockN r) :
    (heisVOA1 r).smul (vacuumN r) n w = if n = -1 then w else 0 :=
  PreVertexAlgebra.smul_vacuum_left _ n w

theorem FT_one_X (b : Fin r) : FT r 1 (X (0, b)) = FgenFld r b := by
  rw [X_zero_eq_monomialN, FT_monomial, Finsupp.degree_single, monoWordN_single, Ywt_single]
  simp

/-! ## The generators against every state -/

theorem FT_gen_creation' (e : ℤ) (b : Fin r) {ℓ : ℤ} (hℓ : ℓ < 0) (w : FockN r) :
    star (1 / 2) (FgenFld r b) ℓ (FT r e w) = FT r (e + 1) ((heisVOA1 r).smul (X (0, b)) ℓ w) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, ℓ = -(n : ℤ) - 1 := ⟨(-ℓ - 1).toNat, by omega⟩
  exact (FT_gen_creation r e b n w).symm

/-- The twisted product formula for the generators, on word states. -/
theorem genPF_word (l : List (ℕ × Fin r)) : ∀ (b : Fin r) (e' ℓ : ℤ),
    star (1 / 2) (FgenFld r b) ℓ (FT r e' (wordStateN l))
      = FT r (e' + 1) ((heisVOA1 r).smul (X (0, b)) ℓ (wordStateN l)) := by
  induction l with
  | nil =>
      intro b e' ℓ
      rcases lt_or_ge ℓ 0 with hℓ | hℓ
      · exact FT_gen_creation' r e' b hℓ _
      rw [wordStateN_nil, show (1 : FockN r) = vacuumN r from rfl,
        show (heisVOA1 r).smul (X (0, b)) ℓ (vacuumN r) = 0 from
          PreVertexAlgebra.smul_vacuum_nonneg _ _ hℓ, FT_zero]
      rcases Int.emod_two_eq_zero_or_one e' with he | he
      · rw [show e' = 2 * (e' / 2) by omega, FT_vacuum_even, star_fzmul_right,
          star_one_right_nonneg _ _ hℓ, fzmul_zero]
      · rw [FT_vacuum_odd r he, star_zero_right]
  | cons c l ih =>
      intro b e' ℓ
      rcases lt_or_ge ℓ 0 with hℓ | hℓ
      · exact FT_gen_creation' r e' b hℓ _
      set w := wordStateN l with hw
      rw [wordStateN_cons]
      have hFX : FT r e' (X c * w)
          = star (1 / 2) (FgenFld r c.2) (-(c.1 : ℤ) - 1) (FT r (e' - 1) w) := by
        have := FT_mul_X r (e' - 1) c w
        rwa [sub_add_cancel] at this
      rw [hFX]
      have hT := star_comm (genSet_local r) (FgenFld_mem r b) (FgenFld_mem r c.2)
        (FT_mem r (e' - 1) w) (1 / 2) (1 / 2) ℓ (-(c.1 : ℤ) - 1) 2
        (fun s hs => prod_Fgen_two_le_fld r b c.2 (by omega))
      rw [Finset.sum_range_succ, Finset.sum_range_one, star_gen_gen, star_gen_gen,
        if_neg (by norm_num), if_pos rfl, star_zero_left, smul_zero, zero_add,
        star_smul_left (local_fzmul_one_left 1 _),
        show (1 / 2 : ℂ) + 1 / 2 = ((1 : ℤ) : ℂ) by norm_num, star_fzmul_one,
        ih b (e' - 1) ℓ, sub_add_cancel,
        FT_gen_creation' r e' c.2 (show -(c.1 : ℤ) - 1 < 0 by omega)] at hT
      rw [eq_add_of_sub_eq hT]
      -- the right side, through the commutator of `heisVOA1 r`
      have hXc : (X c : FockN r) * w = (heisVOA1 r).smul (X (0, c.2)) (-(c.1 : ℤ) - 1) w := by
        rw [smul_X_neg]
      have hV := voa_comm (heisVOA1 r) (X (0, b)) (X (0, c.2)) w ℓ (-(c.1 : ℤ) - 1) 2
        (smul_X_X_two_le r b c.2)
      rw [Finset.sum_range_succ, Finset.sum_range_one,
        smul_X_X_nonneg r b c.2 (by norm_num), smul_X_X_nonneg r b c.2 (by norm_num),
        if_neg (by norm_num)] at hV
      rw [hXc, eq_add_of_sub_eq hV, FT_add, FT_add, FT_smul, FT_smul]
      simp only [PreVertexAlgebra.smul_zero_left, FT_zero, smul_zero, zero_add]
      congr 1
      have hz : fzmul 1 (FT r (e' - 1) w) = FT r (e' + 1) w := by
        rw [← FT_add_two, show e' - 1 + 2 = e' + 1 by ring]
      by_cases hbc : b = c.2 <;> by_cases hn : ℓ + (-(c.1 : ℤ) - 1) - 1 = -1 <;>
        simp only [hbc, hn, Nat.cast_one, and_self, and_false, if_true, if_false,
          one_smul, zero_smul, smul_vacuumN, FT_zero, smul_zero, PreVertexAlgebra.smul_zero_left, hz]

theorem monomial_eq_smul_wordState (m : (ℕ × Fin r) →₀ ℕ) (a : ℂ) :
    (monomial m a : FockN r) = a • wordStateN (monoWordN m) := by
  rw [wordStateN_monoWordN, smul_monomial, smul_eq_mul, mul_one]

/-- **The twisted product formula for the generators**, for every state `w` and every mode:
`star ½ (Fgen b) ℓ F_e(w) = F_{e+1}(b₍ℓ₎w)`. -/
theorem genPF (b : Fin r) (e' ℓ : ℤ) (w : FockN r) :
    star (1 / 2) (FgenFld r b) ℓ (FT r e' w)
      = FT r (e' + 1) ((heisVOA1 r).smul (X (0, b)) ℓ w) := by
  induction w using MvPolynomial.induction_on' with
  | monomial m a =>
      rw [monomial_eq_smul_wordState, FT_smul, star_smul_right (gen_FT_local r _ _ _), genPF_word,
        PreVertexAlgebra.smul_smul_right, FT_smul]
  | add p q hp hq =>
      rw [FT_add, star_add_right (gen_FT_local r _ _ _) (gen_FT_local r _ _ _), hp, hq,
        PreVertexAlgebra.smul_add_right, FT_add]

/-! ## Translation covariance -/

theorem T_eq_smul_omega (u : FockN r) :
    (heisVOA1 r).toPreVertexAlgebra.T u = (heisVOA1 r).smul (heisVOA1 r).conformalVector 0 u := by
  rw [VertexOperatorAlgebra.T_eq_Lneg1, VertexOperatorAlgebra.L_def]
  rfl

theorem T_mem_eigen {j : ℕ} {u : FockN r} (hu : u ∈ (sigma1 r).twistedEigenspace 2 j) :
    (heisVOA1 r).toPreVertexAlgebra.T u ∈ (sigma1 r).twistedEigenspace 2 j := by
  rw [T_eq_smul_omega]
  have := smul_mem_eigen r (omega_mem_eigen r) hu 0
  rwa [zero_add] at this

/-- `(Tu)₍ₙ₎ = −n u₍ₙ₋₁₎`, with a complex scalar. -/
theorem smul_T_left (u : FockN r) (n : ℤ) (w : FockN r) :
    (heisVOA1 r).smul ((heisVOA1 r).toPreVertexAlgebra.T u) n w
      = (-(n : ℂ)) • (heisVOA1 r).smul u (n - 1) w := by
  rw [PreVertexAlgebra.smul_def, PreVertexAlgebra.smul_def, VertexOperatorAlgebra.mode_Y_T,
    ← Int.cast_smul_eq_zsmul ℂ (-n), LinearMap.smul_apply, Int.cast_neg]

/-- `T` is a derivation of the products: `T(b₍q₎w) = b₍q₎(Tw) − q b₍q₋₁₎w`. -/
theorem T_smul (u : FockN r) (q : ℤ) (w : FockN r) :
    (heisVOA1 r).toPreVertexAlgebra.T ((heisVOA1 r).smul u q w)
      = (heisVOA1 r).smul u q ((heisVOA1 r).toPreVertexAlgebra.T w)
        - (q : ℂ) • (heisVOA1 r).smul u (q - 1) w := by
  rw [T_eq_smul_omega, VertexOperatorAlgebra.zeroMode_leibniz, ← T_eq_smul_omega,
    ← T_eq_smul_omega, smul_T_left, neg_smul, add_comm, ← sub_eq_add_neg]

theorem T_vacuumN : (heisVOA1 r).toPreVertexAlgebra.T (vacuumN r) = 0 :=
  PreVertexAlgebra.T_vacuum _

theorem deriv_mem {Y : Fld (FockT r)} (hY : Y ∈ TGenerated (genSet r)) :
    Fld.deriv Y ∈ TGenerated (genSet r) := by
  have h : Fld.deriv Y = Fld.prod (-2) Y Fld.one := by
    apply Subtype.ext
    rw [Fld.deriv_val, show (-2 : ℤ) = -((1 : ℕ) : ℤ) - 1 by norm_num, Fld.prod_one_right_negsucc]
    simp
  rw [h]
  exact prod_mem_tgenerated _ hY (one_mem_tgenerated _)

/-- **Translation covariance of the twisted vertex operator**, on word states. -/
theorem FT_translation_word (l : List (ℕ × Fin r)) : ∀ e : ℤ,
    Fld.deriv (FT r e (wordStateN l)) - ((e : ℂ) / 2) • fzmul (-1) (FT r e (wordStateN l))
      = FT r e ((heisVOA1 r).toPreVertexAlgebra.T (wordStateN l)) := by
  induction l with
  | nil =>
      intro e
      rw [wordStateN_nil, show (1 : FockN r) = vacuumN r from rfl, T_vacuumN, FT_zero]
      rcases Int.emod_two_eq_zero_or_one e with he | he
      · obtain ⟨k, rfl⟩ : ∃ k : ℤ, e = 2 * k := ⟨e / 2, by omega⟩
        rw [FT_vacuum_even, deriv_fzmul, fld_deriv_one, fzmul_zero, add_zero, fzmul_fzmul,
          show (-1 : ℤ) + k = k - 1 by ring]
        push_cast
        rw [show (2 * (k : ℂ)) / 2 = k by ring, sub_self]
      · rw [FT_vacuum_odd r he, fld_deriv_zero, fzmul_zero, smul_zero, sub_zero]
  | cons c l ih =>
      intro e
      set w := wordStateN l with hw
      rw [wordStateN_cons]
      have hXc : (X c : FockN r) * w = (heisVOA1 r).smul (X (0, c.2)) (-(c.1 : ℤ) - 1) w := by
        rw [smul_X_neg]
      have hFX : FT r e (X c * w)
          = star (1 / 2) (FgenFld r c.2) (-(c.1 : ℤ) - 1) (FT r (e - 1) w) := by
        have := FT_mul_X r (e - 1) c w
        rwa [sub_add_cancel] at this
      have hIH := ih (e - 1)
      have hdY : Fld.deriv (FT r (e - 1) w) = FT r (e - 1) ((heisVOA1 r).toPreVertexAlgebra.T w)
          + (((e - 1 : ℤ) : ℂ) / 2) • fzmul (-1) (FT r (e - 1) w) := by
        rw [← hIH]; abel
      rw [hFX, deriv_star (gen_FT_local r _ _ _), hdY,
        star_add_right (gen_FT_local r _ _ _) (tlocal r (FgenFld_mem r _)
          (smul_mem_tgenerated _ (fzmul_mem_tgenerated _ (FT_mem r _ _)))),
        star_smul_right (tlocal r (FgenFld_mem r _) (fzmul_mem_tgenerated _ (FT_mem r _ _))),
        star_fzmul_right, hXc, T_smul, FT_sub, FT_smul,
        FT_gen_creation' r (e - 1) c.2 (show -(c.1 : ℤ) - 1 < 0 by omega),
        FT_gen_creation' r (e - 1) c.2 (show -(c.1 : ℤ) - 1 - 1 < 0 by omega), sub_add_cancel]
      push_cast
      module

/-- **Translation covariance**: `∂F_e(u) − (e/2) z⁻¹ F_e(u) = F_e(L₋₁u)` for every state. -/
theorem FT_translation (e : ℤ) (u : FockN r) :
    Fld.deriv (FT r e u) - ((e : ℂ) / 2) • fzmul (-1) (FT r e u)
      = FT r e ((heisVOA1 r).toPreVertexAlgebra.T u) := by
  induction u using MvPolynomial.induction_on' with
  | monomial m a =>
      rw [monomial_eq_smul_wordState, FT_smul, fld_deriv_smul, fzmul_smul, smul_comm, ← smul_sub,
        FT_translation_word, map_smul, FT_smul]
  | add p q hp hq =>
      rw [FT_add, fld_deriv_add, fzmul_add, smul_add, map_add, FT_add, ← hp, ← hq]
      abel

/-- **The vacuum case of the twisted product formula**:
`star (e/2) F_e(u) ℓ 1 = F_e(u₍ℓ₎𝟙)`. -/
theorem starPF_one (e : ℤ) (u : FockN r) (ℓ : ℤ) :
    star ((e : ℂ) / 2) (FT r e u) ℓ Fld.one = FT r e ((heisVOA1 r).smul u ℓ (vacuumN r)) := by
  rcases le_or_gt 0 ℓ with hℓ | hℓ
  · rw [star_one_right_nonneg _ _ hℓ, show (heisVOA1 r).smul u ℓ (vacuumN r) = 0 from
      PreVertexAlgebra.smul_vacuum_nonneg _ _ hℓ, FT_zero]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = -(k : ℤ) - 1 := ⟨(-ℓ - 1).toNat, by omega⟩
  induction k generalizing u with
  | zero =>
      rw [show -((0 : ℕ) : ℤ) - 1 = -1 by norm_num, star_one_right_neg_one,
        show (heisVOA1 r).smul u (-1) (vacuumN r) = u from PreVertexAlgebra.smul_vacuum_neg_one _ u]
  | succ k ih =>
      have h := star_deriv_one ((e : ℂ) / 2) (FT r e u) (-(k : ℤ) - 1)
      rw [FT_translation, ih _ (by omega), smul_T_left,
        show -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 by push_cast; ring, FT_smul] at h
      have hk : (-((-(k : ℤ) - 1 : ℤ) : ℂ)) ≠ 0 := by
        have : (-((-(k : ℤ) - 1 : ℤ) : ℂ)) = (k : ℂ) + 1 := by push_cast; ring
        rw [this]
        exact_mod_cast Nat.succ_ne_zero k
      exact (smul_right_injective _ hk h).symm

/-! ## The twisted product formula for all pairs -/

/-- A common bound past which both the field products `Fgen₍ₛ₎F_e(u)` and the VOA products
`b₍ₛ₎u` vanish. -/
theorem exists_gen_bound (b : Fin r) (e : ℤ) (u : FockN r) :
    ∃ L : ℕ, (∀ s : ℕ, L ≤ s → Fld.prod s (FgenFld r b) (FT r e u) = 0)
      ∧ ∀ s : ℕ, L ≤ s → (heisVOA1 r).smul (X (0, b)) s u = 0 := by
  obtain ⟨K₁, hK₁⟩ := exists_prod_offset_zero (gen_FT_local r b e u) 0
  obtain ⟨K₂, hK₂⟩ := PreVertexAlgebra.smul_eventually_zero (heisVOA1 r).toPreVertexAlgebra (X (0, b)) u
  refine ⟨K₁ + K₂.toNat, fun s hs => ?_, fun s hs => hK₂ s (by omega)⟩
  have := hK₁ s (by omega)
  rwa [zero_add] at this

/-- The twisted product formula, on word states `v`. -/
theorem starPF_word (l : List (ℕ × Fin r)) : ∀ (j : ℕ) (u : FockN r),
    u ∈ (sigma1 r).twistedEigenspace 2 j → ∀ (e : ℤ), (e + j) % 2 = 0 → ∀ (e' ℓ : ℤ),
      star ((e : ℂ) / 2) (FT r e u) ℓ (FT r e' (wordStateN l))
        = FT r (e + e') ((heisVOA1 r).smul u ℓ (wordStateN l)) := by
  induction l with
  | nil =>
      intro j u hu e he e' ℓ
      rw [wordStateN_nil, show (1 : FockN r) = vacuumN r from rfl]
      rcases Int.emod_two_eq_zero_or_one e' with he' | he'
      · obtain ⟨k, rfl⟩ : ∃ k : ℤ, e' = 2 * k := ⟨e' / 2, by omega⟩
        rw [FT_vacuum_even, star_fzmul_right, starPF_one, FT_shift]
      · rw [FT_vacuum_odd r he', star_zero_right, FT_eq_zero_of_parity r
          (smul_mem_eigen r hu (vacuum_mem_eigen r) ℓ) (by push_cast; omega)]
  | cons c l ih =>
      intro j u hu e he e' ℓ
      set v := wordStateN l with hv
      rw [wordStateN_cons]
      have hXc : (X c : FockN r) * v = (heisVOA1 r).smul (X (0, c.2)) (-(c.1 : ℤ) - 1) v := by
        rw [smul_X_neg]
      have hFX : FT r e' (X c * v)
          = star (1 / 2) (FgenFld r c.2) (-(c.1 : ℤ) - 1) (FT r (e' - 1) v) := by
        have := FT_mul_X r (e' - 1) c v
        rwa [sub_add_cancel] at this
      obtain ⟨L, hLF, hLV⟩ := exists_gen_bound r c.2 e u
      have hT := star_comm (genSet_local r) (FgenFld_mem r c.2) (FT_mem r e u)
        (FT_mem r (e' - 1) v) (1 / 2) ((e : ℂ) / 2) (-(c.1 : ℤ) - 1) ℓ L hLF
      rw [ih j u hu e he (e' - 1) ℓ,
        FT_gen_creation' r (e + (e' - 1)) c.2 (show -(c.1 : ℤ) - 1 < 0 by omega)] at hT
      have hterm : ∀ s ∈ Finset.range L, gBinom (-(c.1 : ℤ) - 1) s •
          star (1 / 2 + (e : ℂ) / 2) (star (1 / 2) (FgenFld r c.2) s (FT r e u))
            (-(c.1 : ℤ) - 1 + ℓ - s) (FT r (e' - 1) v)
          = gBinom (-(c.1 : ℤ) - 1) s • FT r (e + e')
              ((heisVOA1 r).smul ((heisVOA1 r).smul (X (0, c.2)) s u)
                (-(c.1 : ℤ) - 1 + ℓ - s) v) := by
        intro s _
        rw [genPF, show (1 / 2 : ℂ) + (e : ℂ) / 2 = ((e + 1 : ℤ) : ℂ) / 2 by push_cast; ring,
          ih (1 + j) _ (smul_mem_eigen r (X_mem_eigen r c.2) hu s) (e + 1) (by omega) (e' - 1),
          show e + 1 + (e' - 1) = e + e' by ring]
      rw [Finset.sum_congr rfl hterm] at hT
      have hV := voa_comm (heisVOA1 r) (X (0, c.2)) u v (-(c.1 : ℤ) - 1) ℓ L hLV
      rw [hFX, hXc, show (heisVOA1 r).smul u ℓ ((heisVOA1 r).smul (X (0, c.2)) (-(c.1 : ℤ) - 1) v)
          = (heisVOA1 r).smul (X (0, c.2)) (-(c.1 : ℤ) - 1) ((heisVOA1 r).smul u ℓ v)
            - ∑ s ∈ Finset.range L, gBinom (-(c.1 : ℤ) - 1) s • (heisVOA1 r).smul
                ((heisVOA1 r).smul (X (0, c.2)) s u) (-(c.1 : ℤ) - 1 + ℓ - s) v by
          rw [← hV]; abel, FT_sub, FT_sum]
      simp only [FT_smul]
      rw [← hT, show e + (e' - 1) + 1 = e + e' by ring]
      abel

/-- **The twisted product formula, star form**: for `u ∈ 𝒱ʲ`, `e ≡ j (mod 2)`, every state
`v`, every class `e'` and every `ℓ`, `star (e/2) F_e(u) ℓ F_{e'}(v) = F_{e+e'}(u₍ℓ₎v)`. -/
theorem starPF {j : ℕ} {u : FockN r} (hu : u ∈ (sigma1 r).twistedEigenspace 2 j) {e : ℤ}
    (he : (e + j) % 2 = 0) (v : FockN r) (e' ℓ : ℤ) :
    star ((e : ℂ) / 2) (FT r e u) ℓ (FT r e' v) = FT r (e + e') ((heisVOA1 r).smul u ℓ v) := by
  induction v using MvPolynomial.induction_on' with
  | monomial m a =>
      rw [monomial_eq_smul_wordState, FT_smul, star_smul_right (FT_local r _ _ _ _),
        starPF_word r _ j u hu e he, PreVertexAlgebra.smul_smul_right, FT_smul]
  | add p q hp hq =>
      rw [FT_add, star_add_right (FT_local r _ _ _ _) (FT_local r _ _ _ _), hp, hq,
        PreVertexAlgebra.smul_add_right, FT_add]

/-! ## The product formula and the twisted Jacobi identity -/

/-- **The twisted product formula** (product form), exactly the hypothesis `hpf` of
`twistedJacobi_YT_of_productFormula`, obtained from `starPF` by binomial inversion. -/
theorem productFormula_YT (j : ℕ) (u : FockN r) (hu : u ∈ (sigma1 r).twistedEigenspace 2 j)
    (v : FockN r) (e' : ℤ) (ℓ s : ℤ) (x : FockT r) :
    mode (Fld.prod ℓ (rescFld (by norm_num : 0 < 2) (YT_truncation r u) (j : ℤ))
        (rescFld (by norm_num : 0 < 2) (YT_truncation r v) e')).1 s x
      = ∑ᶠ t : ℕ, cbinom ((((j : ℤ) : ℤ) : ℂ) / (2 : ℕ)) t •
          YT r ((heisVOA1 r).smul u (ℓ + t) v) ((2 : ℕ) * (s - t) + (j : ℤ) + e') x := by
  change mode (Fld.prod ℓ (FT r j u) (FT r e' v)).1 s x = _
  have hc : ((((j : ℤ) : ℤ) : ℂ) / (2 : ℕ)) = ((j : ℤ) : ℂ) / 2 := by push_cast; ring
  rw [hc]
  obtain ⟨N₁, hN₁⟩ := Fld.prod_eventually_zero_of_local (FT_local r j e' u v)
  obtain ⟨N₂, hN₂⟩ := PreVertexAlgebra.smul_eventually_zero (heisVOA1 r).toPreVertexAlgebra u v
  have hpf := pf_of_inverse (((j : ℤ) : ℂ) / 2)
    (fun ℓ s => mode (Fld.prod ℓ (FT r j u) (FT r e' v)).1 s x)
    (fun ℓ s => mode (FT r (j + e') ((heisVOA1 r).smul u ℓ v)).1 s x) (max N₁ N₂)
    (fun ℓ s hℓ => by
      beta_reduce
      rw [hN₁ ℓ (le_of_max_le_left hℓ), mode_fld_zero])
    (fun ℓ s hℓ => by
      beta_reduce
      rw [show (heisVOA1 r).smul u ℓ v = 0 from hN₂ ℓ (le_of_max_le_right hℓ), FT_zero,
        mode_fld_zero])
    (fun ℓ s => by
      beta_reduce
      obtain ⟨K, hK⟩ := exists_prod_offset_zero (FT_local r j e' u v) ℓ
      rw [← starPF r hu (e := j) (by omega) v e' ℓ, star_eq_sum_range _ _ _ _ K hK,
        mode_fld_sum, finsum_nat_eq_sum_range K _ (fun i hi => by
          rw [hK i hi, mode_fld_zero, smul_zero])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mode_fld_smul, mode_fzmul, ← sub_eq_add_neg])
    ℓ s
  rw [hpf]
  refine finsum_congr fun t => ?_
  beta_reduce
  rw [FT_val, mode_resc]
  congr 2
  push_cast
  ring_nf

/-- **The corrected DLM twisted Jacobi identity for the concrete twisted vertex operator**,
for all pairs of states: `TwistedJacobi (sigma1 r) 2 (YT r)`. -/
theorem twistedJacobi_YT : TwistedJacobi (sigma1 r) 2 (YT r) :=
  twistedJacobi_YT_of_productFormula r
    (fun j u hu v e' _ _ ℓ s x => productFormula_YT r j u hu v e' ℓ s x)

end Moonshine

end VOA
