/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperBlockRelations
import VOA.Modularity.SuperSymmetricFunctionals
import VOA.Modules.ZhuVermaAnArchResSkew

/-!
# The signed Zhu commutator and the square-bracket zero mode

For an integral-weight super VOA, the square-bracket zero mode is the supercommutator in the
super Zhu algebra.  The sign is the single Koszul scalar attached to the two parity-homogeneous
inputs.

The proof does not use the conditional super-skew API.  Instead it first derives the exact
mode-form super skew identity from the audited super Jacobi identity by specializing its
`m = -1`, `n = 0` slice to the vacuum.  The resulting translation tower is then collapsed modulo
`superO`; the remaining coefficient calculation is Zhu's alternating Vandermonde convolution.
-/

namespace VOA

open scoped BigOperators

set_option autoImplicit false

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

variable (V : SuperNearVOA 𝒱)

/-! ## Unconditional super skew from the audited super Jacobi identity -/

/-- The exact super skew identity in the project's mode and translation calculus.  This is
derived from `superJacobi`, not from the conditional `Core.SuperSkew` gate. -/
theorem superSmul_eq_skew_Lpow {p q : ZMod 2} {a b : 𝒱}
    (ha : a ∈ V.parity p) (hb : b ∈ V.parity q) (t : ℤ) :
    V.smul b t a
      = koszul p q • ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) •
          (sgn (-t - 1 - (j : ℤ))) •
            ((V.L (-1) ^ j) (V.smul a (t + (j : ℤ)) b)) := by
  have hJ := V.superJacobi ha hb V.vacuum t (-1) 0
  have hleft :
      (∑ᶠ i : ℤ, (negOnePow i * cbz t i) •
          (V.smul a (t - 1 - i) (V.smul b i V.vacuum)
            - (koszul p q * negOnePow t) •
                V.smul b (t - i) (V.smul a (-1 + i) V.vacuum)))
        = -(koszul p q * negOnePow t) • V.smul b t a := by
    rw [finsum_eq_single _ 0]
    · simp only [negOnePow, cbz_zero, one_mul, one_smul, if_pos (by norm_num : Even (0 : ℤ))]
      rw [V.smul_vacuum_eq_zero b (by norm_num : (0 : ℤ) ≤ 0),
        SuperVertexAlgebra.smul_zero_right,
        show (-1 : ℤ) + 0 = -1 from by norm_num, V.smul_neg_one_vacuum]
      simp
    · intro i hi
      rcases lt_or_gt_of_ne hi with hi | hi
      · rw [cbz_apply_neg t hi, mul_zero, zero_smul]
      · have hbi : V.smul b i V.vacuum = 0 := V.smul_vacuum_eq_zero b (by omega)
        have hai : V.smul a (-1 + i) V.vacuum = 0 := V.smul_vacuum_eq_zero a (by omega)
        rw [hbi, hai, SuperVertexAlgebra.smul_zero_right, SuperVertexAlgebra.smul_zero_right,
          smul_zero, sub_zero, smul_zero]
  have hright :
      (∑ᶠ i : ℤ, cbz (-1) i • V.smul (V.smul a (t + i) b) (-1 - i) V.vacuum)
        = ∑ᶠ j : ℕ, ((-1 : ℂ) ^ j) •
            (((j.factorial : ℂ)⁻¹) • ((V.L (-1) ^ j) (V.smul a (t + (j : ℤ)) b))) := by
    symm
    apply VertexOperatorAlgebra.finsum_nat_to_int
    · intro i hi
      rw [cbz_apply_neg (-1) hi, zero_smul]
    · intro j
      rw [ZhuRes.cbz_neg_one j,
        show (-1 : ℤ) - (j : ℤ) = -(j : ℤ) - 1 from by ring,
        V.creation_powε, smul_smul]
  simp only [add_zero, zero_add, sub_eq_add_neg] at hJ hleft hright
  rw [hleft, hright] at hJ
  have hε : koszul p q ≠ 0 := by
    intro h
    have := koszul_mul_self p q
    rw [h, zero_mul] at this
    exact zero_ne_one this
  have ht : negOnePow t ≠ 0 := by
    intro ht
    have ht2 := negOnePow_mul_self t
    rw [ht, zero_mul] at ht2
    exact zero_ne_one ht2
  have hsolve : V.smul b t a
      = -(koszul p q * negOnePow t) •
          ∑ᶠ j : ℕ, ((-1 : ℂ) ^ j) •
            (((j.factorial : ℂ)⁻¹) • ((V.L (-1) ^ j) (V.smul a (t + (j : ℤ)) b))) := by
    have hs : -(koszul p q * negOnePow t) * -(koszul p q * negOnePow t) = 1 := by
      rw [mul_neg, neg_mul, neg_neg, mul_assoc, mul_left_comm (negOnePow t),
        ← mul_assoc (koszul p q), koszul_mul_self, one_mul, negOnePow_mul_self]
    rw [← hJ, smul_smul, hs, one_smul]
  rw [hsolve]
  have hfin : (Function.support fun j : ℕ =>
      ((-1 : ℂ) ^ j) • (((j.factorial : ℂ)⁻¹) •
        ((V.L (-1) ^ j) (V.smul a (t + (j : ℤ)) b)))).Finite := by
    obtain ⟨N, hN⟩ := V.regularity a b
    refine Set.Finite.subset (Set.finite_Iio (N - t).toNat) ?_
    intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Set.mem_Iio]
    by_contra hc
    rw [not_lt] at hc
    exact hj (by
      have hz := hN (t + (j : ℤ)) (by omega)
      change V.smul a (t + (j : ℤ)) b = 0 at hz
      rw [hz, map_zero, smul_zero, smul_zero])
  have hfin' : (Function.support fun j : ℕ =>
      ((j.factorial : ℂ)⁻¹) • (sgn (-t - 1 - (j : ℤ))) •
        ((V.L (-1) ^ j) (V.smul a (t + (j : ℤ)) b))).Finite := by
    obtain ⟨N, hN⟩ := V.regularity a b
    refine Set.Finite.subset (Set.finite_Iio (N - t).toNat) ?_
    intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Set.mem_Iio]
    by_contra hc
    rw [not_lt] at hc
    exact hj (by
      have hz := hN (t + (j : ℤ)) (by omega)
      change V.smul a (t + (j : ℤ)) b = 0 at hz
      rw [hz, map_zero, smul_zero, smul_zero])
  rw [smul_finsum' _ hfin, smul_finsum' _ hfin']
  refine finsum_congr fun j => ?_
  simp only [smul_smul]
  congr 1
  rw [show -t - 1 - (j : ℤ) = -(t + (j : ℤ) + 1) from by ring,
    sgn_neg', show t + (j : ℤ) + 1 = (t + 1) + (j : ℤ) from by ring,
    sgn_add_natCast, sgn_succ]
  have hsgn : sgn t = negOnePow t := rfl
  rw [hsgn]
  ring

/-! ## The translation tower modulo the super Zhu ideal -/

/-- On a homogeneous vector, the defining super Zhu generator identifies `L₋₁` with minus the
weight modulo `superO`. -/
theorem Lneg1_grading_mem_superO (hV : V.IntegralWeights) {d : ℤ} {w : 𝒱}
    (hw : w ∈ V.gradingZ d) :
    V.L (-1) w + (d : ℂ) • w ∈ V.superO hV := by
  have hL0 : V.L 0 w = (d : ℂ) • w :=
    V.L0_eigenvalue (by simpa [SuperNearVOA.gradingZ_apply] using hw)
  have h := V.superO_mem_of_L hV w V.vacuum
  rw [V.superZhuMul_vacuum_right hV, hL0] at h
  exact h

/-- The `L₋₁` tower on a homogeneous vector collapses to Zhu's rising-factorial scalar modulo
`superO`. -/
theorem Lneg1_pow_mod_superO (hV : V.IntegralWeights) :
    ∀ (j : ℕ) {d : ℤ} {w : 𝒱}, w ∈ V.gradingZ d →
      (V.L (-1) ^ j) w - djTowerScalar d j • w ∈ V.superO hV := by
  intro j
  induction j with
  | zero =>
      intro d w _
      simp [djTowerScalar_zero]
  | succ j ih =>
      intro d w hw
      have hLw : V.L (-1) w ∈ V.gradingZ (d + 1) := V.L_neg_one_mem_gradingZ_succ hw
      have h₁ := ih hLw
      have h₂ : djTowerScalar (d + 1) j • (V.L (-1) w + (d : ℂ) • w)
          ∈ V.superO hV :=
        Submodule.smul_mem _ _ (V.Lneg1_grading_mem_superO hV hw)
      have hsum := (V.superO hV).add_mem h₁ h₂
      have hpow : (V.L (-1) ^ (j + 1)) w = (V.L (-1) ^ j) (V.L (-1) w) := by
        rw [pow_succ]
        rfl
      have hscal : djTowerScalar d (j + 1) = -(d : ℂ) * djTowerScalar (d + 1) j := by
        rw [djTowerScalar_succ]
      have hrw :
          (V.L (-1) ^ j) (V.L (-1) w) - djTowerScalar (d + 1) j • V.L (-1) w
              + djTowerScalar (d + 1) j • (V.L (-1) w + (d : ℂ) • w)
            = (V.L (-1) ^ (j + 1)) w - djTowerScalar d (j + 1) • w := by
        rw [hpow, hscal, smul_add, smul_smul]
        module
      rwa [hrw] at hsum

/-! ## Full residues and super skew modulo `superO` -/

/-- The honest all-integer residue
`Res_z (1+z)^E z^(-P) Y(a,z)b`, in super-VOA mode notation. -/
noncomputable def superResFull (E P : ℤ) (a b : 𝒱) : 𝒱 :=
  ∑ᶠ ell : ℤ, cbz E (ell + P) • V.smul a ell b

theorem superResFull_support_finite (E P : ℤ) (a b : 𝒱) :
    (Function.support fun ell : ℤ => cbz E (ell + P) • V.smul a ell b).Finite := by
  obtain ⟨N, hN⟩ := V.regularity a b
  refine Set.Finite.subset (Set.finite_Icc (-P) N) ?_
  intro ell hell
  simp only [Function.mem_support, ne_eq] at hell
  rw [Set.mem_Icc]
  constructor
  · by_contra hc
    push Not at hc
    exact hell (by rw [cbz_apply_neg E (by omega), zero_smul])
  · by_contra hc
    push Not at hc
    have hz := hN ell (by omega)
    change V.smul a ell b = 0 at hz
    exact hell (by rw [hz, smul_zero])

/-- A scalar family applied to the eventually-zero products `a_(t+j)b` has finite support. -/
theorem superSkewFamily_support_finite (a b : 𝒱) (t : ℤ)
    (c : ℕ → ℂ) (F : ℕ → 𝒱 → 𝒱) (hF : ∀ j, F j 0 = 0) :
    (Function.support fun j : ℕ => c j • F j (V.smul a (t + (j : ℤ)) b)).Finite := by
  obtain ⟨N, hN⟩ := V.regularity a b
  refine Set.Finite.subset (Set.finite_Iio (N - t).toNat) ?_
  intro j hj
  simp only [Function.mem_support, ne_eq] at hj
  rw [Set.mem_Iio]
  by_contra hc
  rw [not_lt] at hc
  have hz := hN (t + (j : ℤ)) (by omega)
  change V.smul a (t + (j : ℤ)) b = 0 at hz
  exact hj (by rw [hz, hF, smul_zero])

/-- Mode-form super skew symmetry after the translation tower is collapsed modulo `superO`.
The only new factor relative to Zhu's bosonic formula is `koszul p q`. -/
theorem superSkew_mod_superO (hV : V.IntegralWeights) {K M : ℕ} {p q : ZMod 2}
    {a b : 𝒱} (haK : a ∈ V.gradingZ (K : ℤ)) (hap : a ∈ V.parity p)
    (hbM : b ∈ V.gradingZ (M : ℤ)) (hbq : b ∈ V.parity q) (t : ℤ) :
    V.smul b t a
      - (koszul p q * sgn (t + 1)) •
          V.superResFull ((K : ℤ) + (M : ℤ) - 2 - t) (-t) a b
      ∈ V.superO hV := by
  set E : ℤ := (K : ℤ) + (M : ℤ) - 2 - t with hE
  have hterm : ∀ j : ℕ,
      (koszul p q * ((j.factorial : ℂ)⁻¹) * sgn (-t - 1 - (j : ℤ))) •
          ((V.L (-1) ^ j) (V.smul a (t + (j : ℤ)) b))
        - (koszul p q * sgn (t + 1) * cbz E (j : ℤ)) •
            V.smul a (t + (j : ℤ)) b ∈ V.superO hV := by
    intro j
    have hgr : V.smul a (t + (j : ℤ)) b
        ∈ V.gradingZ ((K : ℤ) + (M : ℤ) - (t + (j : ℤ)) - 1) :=
      V.smul_mem_gradingZ haK hbM (t + (j : ℤ))
    have htow := V.Lneg1_pow_mod_superO hV j hgr
    have hscaled := Submodule.smul_mem (V.superO hV)
      (koszul p q * ((j.factorial : ℂ)⁻¹) * sgn (-t - 1 - (j : ℤ))) htow
    have hidx : ((K : ℤ) + (M : ℤ) - (t + (j : ℤ)) - 1)
        = E - (j : ℤ) + 1 := by rw [hE]; ring
    have hsgn : sgn (-t - 1 - (j : ℤ)) = sgn (t + 1) * (-1 : ℂ) ^ j := by
      rw [show -t - 1 - (j : ℤ) = -((t + 1) + (j : ℤ)) from by ring,
        sgn_neg', sgn_add_natCast]
    have hfac : (j.factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hscal :
        (koszul p q * (j.factorial : ℂ)⁻¹ * sgn (-t - 1 - (j : ℤ)))
            * djTowerScalar ((K : ℤ) + (M : ℤ) - (t + (j : ℤ)) - 1) j
          = koszul p q * sgn (t + 1) * cbz E (j : ℤ) := by
      have h2 : (((-1 : ℂ) ^ j) ^ 2) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [hidx, djTowerScalar_shift_eq, hsgn]
      field_simp
      rw [h2]
      ring
    rw [smul_sub, smul_smul, hscal] at hscaled
    exact hscaled
  have hF1 : (Function.support fun j : ℕ =>
      (koszul p q * ((j.factorial : ℂ)⁻¹) * sgn (-t - 1 - (j : ℤ))) •
        ((V.L (-1) ^ j) (V.smul a (t + (j : ℤ)) b))).Finite :=
    V.superSkewFamily_support_finite a b t _ (fun j x => (V.L (-1) ^ j) x)
      (fun j => map_zero _)
  have hF2 : (Function.support fun j : ℕ =>
      (koszul p q * sgn (t + 1) * cbz E (j : ℤ)) •
        V.smul a (t + (j : ℤ)) b).Finite :=
    V.superSkewFamily_support_finite a b t _ (fun _ x => x) (fun _ => rfl)
  have hLHS : V.smul b t a = ∑ᶠ j : ℕ,
      (koszul p q * ((j.factorial : ℂ)⁻¹) * sgn (-t - 1 - (j : ℤ))) •
        ((V.L (-1) ^ j) (V.smul a (t + (j : ℤ)) b)) := by
    rw [V.superSmul_eq_skew_Lpow hap hbq t]
    have hinner0 : (Function.support fun j : ℕ =>
        (((j.factorial : ℂ)⁻¹) * sgn (-t - 1 - (j : ℤ))) •
          ((V.L (-1) ^ j) (V.smul a (t + (j : ℤ)) b))).Finite :=
      V.superSkewFamily_support_finite a b t _ (fun j x => (V.L (-1) ^ j) x)
        (fun j => map_zero _)
    have hinner : (Function.support fun j : ℕ =>
        ((j.factorial : ℂ)⁻¹) • sgn (-t - 1 - (j : ℤ)) •
          ((V.L (-1) ^ j) (V.smul a (t + (j : ℤ)) b))).Finite := by
      simpa only [smul_smul] using hinner0
    rw [smul_finsum' _ hinner]
    exact finsum_congr fun j => by simp only [smul_smul]; congr 1; ring
  have hF0 : (Function.support fun j : ℕ =>
      cbz E (j : ℤ) • V.smul a (t + (j : ℤ)) b).Finite :=
    V.superSkewFamily_support_finite a b t _ (fun _ x => x) (fun _ => rfl)
  have hRHS : (koszul p q * sgn (t + 1)) •
      V.superResFull E (-t) a b
      = ∑ᶠ j : ℕ, (koszul p q * sgn (t + 1) * cbz E (j : ℤ)) •
          V.smul a (t + (j : ℤ)) b := by
    rw [superResFull]
    have hZ : (∑ᶠ ell : ℤ, cbz E (ell + -t) • V.smul a ell b)
        = ∑ᶠ j : ℕ, cbz E (j : ℤ) • V.smul a (t + (j : ℤ)) b := by
      symm
      calc
        (∑ᶠ j : ℕ, cbz E (j : ℤ) • V.smul a (t + (j : ℤ)) b)
            = ∑ᶠ z : ℤ, cbz E z • V.smul a (t + z) b :=
              VertexOperatorAlgebra.finsum_nat_to_int _ _
                (fun z hz => by rw [cbz_apply_neg E hz, zero_smul]) (fun _ => rfl)
        _ = ∑ᶠ z : ℤ,
              (fun r : ℤ => cbz E (r + -t) • V.smul a r b) (Equiv.addLeft t z) := by
              refine finsum_congr fun z => ?_
              simp only [Equiv.coe_addLeft]
              rw [show (t + z) + -t = z from by ring]
        _ = ∑ᶠ ell : ℤ, cbz E (ell + -t) • V.smul a ell b :=
              finsum_comp_equiv (Equiv.addLeft t)
                (f := fun ell : ℤ => cbz E (ell + -t) • V.smul a ell b)
    rw [hZ, smul_finsum' _ hF0]
    exact finsum_congr fun j => by rw [smul_smul]
  rw [hE] at hRHS
  rw [hLHS, hRHS, ← finsum_sub_distrib hF1 hF2]
  exact finsum_mem_submodule_dj _ hterm

/-! ## Zhu residues and the signed commutator -/

/-- On a nonnegative homogeneous weight, the super Zhu product is the honest exponent-`K`,
pole-one residue. -/
theorem superZhuMul_eq_superResFull (hV : V.IntegralWeights) {K : ℕ} {a : 𝒱}
    (ha : a ∈ V.gradingZ (K : ℤ)) (b : 𝒱) :
    V.superZhuMul hV a b = V.superResFull (K : ℤ) 1 a b := by
  rw [V.superZhuMul_homogeneous hV ha b]
  have hsub : (Function.support fun i : ℕ =>
      cbz (K : ℤ) (i : ℤ) • V.smul a ((i : ℤ) - 1) b)
      ⊆ ↑(Finset.range (K + 1)) := by
    intro i hi
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    push Not at hc
    exact hi (by rw [cbz_lt (by positivity) (by omega), zero_smul])
  calc
    (∑ i ∈ Finset.range (K + 1),
        cbz (K : ℤ) (i : ℤ) • V.smul a ((i : ℤ) - 1) b)
        = ∑ᶠ i : ℕ, cbz (K : ℤ) (i : ℤ) • V.smul a ((i : ℤ) - 1) b :=
          (finsum_eq_sum_of_support_subset _ hsub).symm
    _ = ∑ᶠ z : ℤ, cbz (K : ℤ) z • V.smul a (z - 1) b :=
          VertexOperatorAlgebra.finsum_nat_to_int _ _
            (fun z hz => by rw [cbz_apply_neg _ hz, zero_smul]) (fun _ => rfl)
    _ = ∑ᶠ z : ℤ,
          (fun r : ℤ => cbz (K : ℤ) (r + 1) • V.smul a r b) (Equiv.subRight 1 z) := by
          refine finsum_congr fun z => ?_
          change cbz (K : ℤ) z • V.smul a (z - 1) b =
            cbz (K : ℤ) ((z - 1) + 1) • V.smul a (z - 1) b
          rw [show z - 1 + 1 = z from by ring]
    _ = ∑ᶠ ell : ℤ, cbz (K : ℤ) (ell + 1) • V.smul a ell b :=
          finsum_comp_equiv (Equiv.subRight 1)
            (f := fun ell : ℤ => cbz (K : ℤ) (ell + 1) • V.smul a ell b)
    _ = V.superResFull (K : ℤ) 1 a b := rfl

/-- Reversing the two homogeneous inputs in the Zhu product costs one Koszul sign and changes
the residue exponent from `K` to `K-1`, modulo `superO`. -/
theorem superZhuMul_skew_mod_superO (hV : V.IntegralWeights) {K M : ℕ} {p q : ZMod 2}
    {a b : 𝒱} (haK : a ∈ V.gradingZ (K : ℤ)) (hap : a ∈ V.parity p)
    (hbM : b ∈ V.gradingZ (M : ℤ)) (hbq : b ∈ V.parity q) :
    V.superZhuMul hV b a
      - koszul p q • V.superResFull ((K : ℤ) - 1) 1 a b ∈ V.superO hV := by
  let S : Finset ℕ := Finset.range (M + 1)
  have hmem : ∀ s ∈ S,
      cbz (M : ℤ) (s : ℤ) • V.smul b ((s : ℤ) - 1) a
        - (cbz (M : ℤ) (s : ℤ) * koszul p q * sgn (s : ℤ)) •
            V.superResFull ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1)
              (1 - (s : ℤ)) a b ∈ V.superO hV := by
    intro s _
    have h := Submodule.smul_mem (V.superO hV) (cbz (M : ℤ) (s : ℤ))
      (V.superSkew_mod_superO hV haK hap hbM hbq ((s : ℤ) - 1))
    rw [smul_sub, smul_smul,
      show (s : ℤ) - 1 + 1 = (s : ℤ) from by ring,
      show (K : ℤ) + (M : ℤ) - 2 - ((s : ℤ) - 1)
          = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1 from by ring,
      show -((s : ℤ) - 1) = 1 - (s : ℤ) from by ring] at h
    simpa [mul_assoc] using h
  have hsum : V.superZhuMul hV b a
      - ∑ s ∈ S, (cbz (M : ℤ) (s : ℤ) * koszul p q * sgn (s : ℤ)) •
          V.superResFull ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1)
            (1 - (s : ℤ)) a b ∈ V.superO hV := by
    rw [V.superZhuMul_homogeneous hV hbM a, Int.toNat_natCast]
    change (∑ s ∈ S, cbz (M : ℤ) (s : ℤ) • V.smul b ((s : ℤ) - 1) a)
        - ∑ s ∈ S, (cbz (M : ℤ) (s : ℤ) * koszul p q * sgn (s : ℤ)) •
          V.superResFull ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1)
            (1 - (s : ℤ)) a b ∈ V.superO hV
    rw [← Finset.sum_sub_distrib]
    exact Submodule.sum_mem _ hmem
  have hid0 : (∑ s ∈ S, (cbz (M : ℤ) (s : ℤ) * sgn (s : ℤ)) •
        V.superResFull ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1)
          (1 - (s : ℤ)) a b)
      = V.superResFull ((K : ℤ) - 1) 1 a b := by
    have hexp : ∀ s : ℕ,
        (cbz (M : ℤ) (s : ℤ) * sgn (s : ℤ)) •
          V.superResFull ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1)
            (1 - (s : ℤ)) a b
        = ∑ᶠ ell : ℤ, (cbz (M : ℤ) (s : ℤ) * sgn (s : ℤ) *
            cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1)
              (ell + (1 - (s : ℤ)))) • V.smul a ell b := by
      intro s
      rw [superResFull, smul_finsum' _ (V.superResFull_support_finite _ _ a b)]
      exact finsum_congr fun ell => by rw [smul_smul]
    have hfin : ∀ s ∈ S, (Function.support fun ell : ℤ =>
        (cbz (M : ℤ) (s : ℤ) * sgn (s : ℤ) *
          cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1)
            (ell + (1 - (s : ℤ)))) • V.smul a ell b).Finite := by
      intro s _
      refine Set.Finite.subset
        (V.superResFull_support_finite
          ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) (1 - (s : ℤ)) a b) ?_
      intro ell hell
      simp only [Function.mem_support, ne_eq] at hell ⊢
      intro hz
      exact hell (by rw [← smul_smul, hz, smul_zero])
    rw [Finset.sum_congr rfl (fun s _ => hexp s),
      ← finsum_finsetSum_comm' S _ hfin]
    rw [superResFull]
    refine finsum_congr fun ell => ?_
    rw [← Finset.sum_smul]
    congr 1
    have hsub : (Function.support fun s : ℕ =>
        sgn (s : ℤ) * cbz (M : ℤ) (s : ℤ) *
          cbz (((K : ℤ) + (M : ℤ) - 1) - (s : ℤ))
            ((ell + 1) - (s : ℤ))) ⊆ ↑S := by
      intro s hs
      simp only [Function.mem_support, ne_eq] at hs
      simp only [S, Finset.coe_range, Set.mem_Iio]
      by_contra hc
      push Not at hc
      exact hs (by rw [cbz_lt (by positivity) (by omega), mul_zero, zero_mul])
    have hstep : (∑ s ∈ S, cbz (M : ℤ) (s : ℤ) * sgn (s : ℤ) *
          cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1)
            (ell + (1 - (s : ℤ))))
        = ∑ᶠ sigma : ℤ, sgn sigma * cbz (M : ℤ) sigma *
            cbz (((K : ℤ) + (M : ℤ) - 1) - sigma) ((ell + 1) - sigma) := by
      have hrange : (∑ s ∈ S, sgn (s : ℤ) * cbz (M : ℤ) (s : ℤ) *
            cbz (((K : ℤ) + (M : ℤ) - 1) - (s : ℤ)) ((ell + 1) - (s : ℤ)))
          = ∑ᶠ sigma : ℤ, sgn sigma * cbz (M : ℤ) sigma *
              cbz (((K : ℤ) + (M : ℤ) - 1) - sigma) ((ell + 1) - sigma) := by
        rw [← finsum_eq_sum_of_support_subset _ hsub]
        exact VertexOperatorAlgebra.finsum_nat_to_int _ _
          (fun z hz => by rw [cbz_apply_neg _ hz, mul_zero, zero_mul]) (fun _ => rfl)
      rw [← hrange]
      exact Finset.sum_congr rfl fun s _ => by
        rw [show (K : ℤ) + (M : ℤ) - (s : ℤ) - 1
              = ((K : ℤ) + (M : ℤ) - 1) - (s : ℤ) from by ring,
          show ell + (1 - (s : ℤ)) = (ell + 1) - (s : ℤ) from by ring]
        ring
    rw [hstep, cbz_alt_vandermonde M ((K : ℤ) + (M : ℤ) - 1) (ell + 1)]
    rw [show ((K : ℤ) + (M : ℤ) - 1) - (M : ℤ) = (K : ℤ) - 1 from by ring]
  have hid : (∑ s ∈ S,
      (cbz (M : ℤ) (s : ℤ) * koszul p q * sgn (s : ℤ)) •
        V.superResFull ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1)
          (1 - (s : ℤ)) a b)
      = koszul p q • V.superResFull ((K : ℤ) - 1) 1 a b := by
    rw [← hid0, Finset.smul_sum]
    exact Finset.sum_congr rfl fun s _ => by simp only [smul_smul]; congr 1; ring
  rwa [hid] at hsum

/-- The signed super Zhu commutator is the exponent-`K-1` residue modulo `superO`. -/
theorem superZhu_comm_residue_mod_superO (hV : V.IntegralWeights) {K M : ℕ}
    {p q : ZMod 2} {a b : 𝒱} (haK : a ∈ V.gradingZ (K : ℤ))
    (hap : a ∈ V.parity p) (hbM : b ∈ V.gradingZ (M : ℤ))
    (hbq : b ∈ V.parity q) :
    V.superZhuMul hV a b - koszul p q • V.superZhuMul hV b a
      - V.superResFull ((K : ℤ) - 1) 0 a b ∈ V.superO hV := by
  have hskew := V.superZhuMul_skew_mod_superO hV haK hap hbM hbq
  have hskew' : koszul p q • V.superZhuMul hV b a
      - V.superResFull ((K : ℤ) - 1) 1 a b ∈ V.superO hV := by
    have hs := Submodule.smul_mem (V.superO hV) (koszul p q) hskew
    rw [smul_sub, smul_smul, koszul_mul_self, one_smul] at hs
    exact hs
  have huv := V.superZhuMul_eq_superResFull hV haK b
  have hpas : V.superResFull (K : ℤ) 1 a b
      = V.superResFull ((K : ℤ) - 1) 1 a b
        + V.superResFull ((K : ℤ) - 1) 0 a b := by
    rw [superResFull, superResFull, superResFull,
      ← finsum_add_distrib
        (V.superResFull_support_finite ((K : ℤ) - 1) 1 a b)
        (V.superResFull_support_finite ((K : ℤ) - 1) 0 a b)]
    refine finsum_congr fun ell => ?_
    rw [← add_smul, cbz_pascal (K : ℤ) (ell + 1),
      show ell + 1 - 1 = ell + 0 from by ring]
  have hrw : V.superZhuMul hV a b - koszul p q • V.superZhuMul hV b a
        - V.superResFull ((K : ℤ) - 1) 0 a b
      = -(koszul p q • V.superZhuMul hV b a
          - V.superResFull ((K : ℤ) - 1) 1 a b) := by
    rw [huv, hpas]
    abel
  rw [hrw]
  exact (V.superO hV).neg_mem hskew'

/-! ## Square-bracket zero modes and the cusp relation -/

/-- For positive integral weight, the square-bracket zero mode is the exponent-`K-1` residue. -/
theorem superVSqZ_zero_eq_superResFull {K : ℕ} (hK : 1 ≤ K) (a b : 𝒱) :
    V.superVSqZ a K 0 b = V.superResFull ((K : ℤ) - 1) 0 a b := by
  rw [V.superVSqZ_apply, superResFull]
  exact finsum_congr fun ell => by
    rw [add_zero, cbz_eq_sqBracketCoeffZ_zero K hK ell]

/-- **Signed Zhu commutator congruence.**  For weight- and parity-homogeneous inputs of positive
left weight, the square-bracket zero mode represents their supercommutator in the super Zhu
algebra. -/
theorem superZhu_comm_mod_superO (hV : V.IntegralWeights) {K M : ℕ}
    (hK : 1 ≤ K) {p q : ZMod 2} {a b : 𝒱}
    (haK : a ∈ V.gradingZ (K : ℤ)) (hap : a ∈ V.parity p)
    (hbM : b ∈ V.gradingZ (M : ℤ)) (hbq : b ∈ V.parity q) :
    V.superZhuMul hV a b - koszul p q • V.superZhuMul hV b a
      - V.superVSqZ a K 0 b ∈ V.superO hV := by
  rw [V.superVSqZ_zero_eq_superResFull hK]
  exact V.superZhu_comm_residue_mod_superO hV haK hap hbM hbq

/-- Every positive-weight bi-homogeneous supercommutator representative belongs to the intrinsic
cusp relation space. -/
theorem superZhu_supercommutator_mem_superCuspRelSpan (hV : V.IntegralWeights)
    {K M : ℕ} (hK : 1 ≤ K) {p q : ZMod 2} {a b : 𝒱}
    (haK : a ∈ V.gradingZ (K : ℤ)) (hap : a ∈ V.parity p)
    (hbM : b ∈ V.gradingZ (M : ℤ)) (hbq : b ∈ V.parity q) :
    V.superZhuMul hV a b - koszul p q • V.superZhuMul hV b a
      ∈ V.superCuspRelSpan hV := by
  have hO := V.superZhu_comm_mod_superO hV hK haK hap hbM hbq
  have hzero := superVSqZ_zero_mem_superCuspRelSpan (hV := hV) hK haK b
  have hadd := (V.superCuspRelSpan hV).add_mem
    (superO_le_superCuspRelSpan hO) hzero
  have heq :
      (V.superZhuMul hV a b - koszul p q • V.superZhuMul hV b a
          - V.superVSqZ a K 0 b) + V.superVSqZ a K 0 b
        = V.superZhuMul hV a b - koszul p q • V.superZhuMul hV b a := by
    abel
  rwa [heq] at hadd

/-- On a genuine super VOA, the same representative belongs to the specialized analytic block
relation span at the cusp. -/
theorem superZhu_supercommutator_mem_superBlockRelSpanAtCusp
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights)
    {K M : ℕ} (hK : 1 ≤ K) {p q : ZMod 2} {a b : 𝒱}
    (haK : a ∈ W.toSuperNearVOA.gradingZ (K : ℤ))
    (hap : a ∈ W.parity p) (hbM : b ∈ W.toSuperNearVOA.gradingZ (M : ℤ))
    (hbq : b ∈ W.parity q) :
    W.toSuperNearVOA.superZhuMul hV a b
        - koszul p q • W.toSuperNearVOA.superZhuMul hV b a
      ∈ W.toSuperNearVOA.superBlockRelSpanAtCusp := by
  rw [superBlockRelSpanAtCusp_eq_superCuspRelSpan W hV]
  exact W.toSuperNearVOA.superZhu_supercommutator_mem_superCuspRelSpan
    hV hK haK hap hbM hbq

/-- The bi-homogeneous statement extends to arbitrary parity-homogeneous representatives.  The
weight-zero slice is central because it is the vacuum line; negative slices vanish by positivity.
This is the reduction needed for generators of the supercommutator span of the Zhu quotient. -/
theorem superZhu_supercommutator_mem_superCuspRelSpan_of_parity
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights)
    {p q : ZMod 2} {a b : 𝒱} (hap : a ∈ W.parity p) (hbq : b ∈ W.parity q) :
    W.toSuperNearVOA.superZhuMul hV a b
        - koszul p q • W.toSuperNearVOA.superZhuMul hV b a
      ∈ W.toSuperNearVOA.superCuspRelSpan hV := by
  let V := W.toSuperNearVOA
  have ha' : a ∈ ⨆ k : ℤ, V.gradingZ k ⊓ V.parity p :=
    V.parity_le_iSup_gradingZ_inf hV p hap
  refine Submodule.iSup_induction (fun k : ℤ => V.gradingZ k ⊓ V.parity p)
    (motive := fun u => ∀ v ∈ V.parity q,
      V.superZhuMul hV u v - koszul p q • V.superZhuMul hV v u
        ∈ V.superCuspRelSpan hV) ha' ?_ ?_ ?_ b hbq
  · intro k u hu v hv
    rw [Submodule.mem_inf] at hu
    rcases lt_trichotomy k 0 with hk | hk | hk
    · have hu0 : u = 0 := by
        have hbot := W.gradingZ_neg_eq_bot k hk
        rw [hbot, Submodule.mem_bot] at hu
        exact hu.1
      subst hu0
      simp only [V.superZhuMul_zero_left, V.superZhuMul_zero_right, smul_zero, sub_zero]
      exact (V.superCuspRelSpan hV).zero_mem
    · subst hk
      have hugrade : u ∈ W.grading 0 := by
        simpa [V, SuperNearVOA.gradingZ_apply] using hu.1
      rw [W.vacuum_grade, Submodule.mem_span_singleton] at hugrade
      obtain ⟨c, rfl⟩ := hugrade
      rw [show W.vacuum = V.vacuum from rfl] at hu ⊢
      rcases zmod2_cases p with hp | hp <;> subst hp
      · rw [V.superZhuMul_smul_left hV, V.superZhuMul_vacuum_left hV,
          V.superZhuMul_smul_right hV, V.superZhuMul_vacuum_right hV,
          koszul_zero_left, one_smul, sub_self]
        exact (V.superCuspRelSpan hV).zero_mem
      · have heven : c • V.vacuum ∈ V.parity 0 :=
          Submodule.smul_mem _ c V.vacuum_parity
        have hproj0 := V.parProj_of_mem_ne (p := 1) (q := 0)
          (by decide : (0 : ZMod 2) ≠ 1) heven
        have hproj1 := V.parProj_of_mem hu.2
        have hz : c • V.vacuum = 0 := by rwa [hproj1] at hproj0
        rw [hz, V.superZhuMul_zero_left, V.superZhuMul_zero_right, smul_zero, sub_zero]
        exact (V.superCuspRelSpan hV).zero_mem
    · have hk1 : 1 ≤ k.toNat := by omega
      have huK : u ∈ V.gradingZ ((k.toNat : ℕ) : ℤ) := by
        simpa [show ((k.toNat : ℕ) : ℤ) = k from by omega] using hu.1
      have hv' : v ∈ ⨆ m : ℤ, V.gradingZ m ⊓ V.parity q :=
        V.parity_le_iSup_gradingZ_inf hV q hv
      refine Submodule.iSup_induction (fun m : ℤ => V.gradingZ m ⊓ V.parity q)
        (motive := fun w =>
          V.superZhuMul hV u w - koszul p q • V.superZhuMul hV w u
            ∈ V.superCuspRelSpan hV) hv' ?_ ?_ ?_
      · intro m w hw
        rw [Submodule.mem_inf] at hw
        rcases lt_or_ge m 0 with hm | hm
        · have hw0 : w = 0 := by
            have hbot := W.gradingZ_neg_eq_bot m hm
            rw [hbot, Submodule.mem_bot] at hw
            exact hw.1
          subst hw0
          simp only [V.superZhuMul_zero_left, V.superZhuMul_zero_right, smul_zero, sub_zero]
          exact (V.superCuspRelSpan hV).zero_mem
        · have hwM : w ∈ V.gradingZ ((m.toNat : ℕ) : ℤ) := by
            simpa [show ((m.toNat : ℕ) : ℤ) = m from by omega] using hw.1
          exact V.superZhu_supercommutator_mem_superCuspRelSpan hV hk1
            huK hu.2 hwM hw.2
      · simp only [V.superZhuMul_zero_left, V.superZhuMul_zero_right, smul_zero, sub_zero]
        exact (V.superCuspRelSpan hV).zero_mem
      · intro x y hx hy
        have heq :
            V.superZhuMul hV u (x + y) - koszul p q • V.superZhuMul hV (x + y) u
              = (V.superZhuMul hV u x - koszul p q • V.superZhuMul hV x u)
                + (V.superZhuMul hV u y - koszul p q • V.superZhuMul hV y u) := by
          rw [V.superZhuMul_add_right hV, V.superZhuMul_add_left hV, smul_add]
          abel
        rw [heq]
        exact (V.superCuspRelSpan hV).add_mem hx hy
  · intro v _
    simp only [V.superZhuMul_zero_left, V.superZhuMul_zero_right, smul_zero, sub_zero]
    exact (V.superCuspRelSpan hV).zero_mem
  · intro x y hx hy v hv
    have heq :
        V.superZhuMul hV (x + y) v - koszul p q • V.superZhuMul hV v (x + y)
          = (V.superZhuMul hV x v - koszul p q • V.superZhuMul hV v x)
            + (V.superZhuMul hV y v - koszul p q • V.superZhuMul hV v y) := by
      rw [V.superZhuMul_add_left hV, V.superZhuMul_add_right hV, smul_add]
      abel
    rw [heq]
    exact (V.superCuspRelSpan hV).add_mem (hx v hv) (hy v hv)

/-- Every homogeneous supercommutator generator in the super Zhu algebra has a representative in
the intrinsic cusp relation space. -/
theorem superZhuComm_generator_has_superCusp_lift
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights)
    (hZ : SuperZhuRingData W.toSuperNearVOA hV) {p q : ZMod 2}
    {x y : W.toSuperNearVOA.superA hV}
    (hx : x ∈ W.toSuperNearVOA.superAParity hV p)
    (hy : y ∈ W.toSuperNearVOA.superAParity hV q) :
    letI := hZ.AsRing
    ∃ g : 𝒱, g ∈ W.toSuperNearVOA.superCuspRelSpan hV ∧
      W.toSuperNearVOA.superMk hV g = x * y - koszul p q • (y * x) := by
  letI := hZ.AsRing
  obtain ⟨a, hap, hax⟩ := Submodule.mem_map.mp hx
  obtain ⟨b, hbq, hby⟩ := Submodule.mem_map.mp hy
  subst x
  subst y
  refine ⟨W.toSuperNearVOA.superZhuMul hV a b
      - koszul p q • W.toSuperNearVOA.superZhuMul hV b a, ?_, ?_⟩
  · exact superZhu_supercommutator_mem_superCuspRelSpan_of_parity W hV hap hbq
  · rw [map_sub, map_smul, hZ.AsRing_mul_eq, hZ.AsRing_mul_eq,
      hZ.superAmul_mk, hZ.superAmul_mk]

/-- Consequently the full supercommutator span of the super Zhu algebra is contained in the image
of the cusp relation space. -/
theorem superZhuCommSpan_le_map_superCuspRelSpan
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights)
    (hZ : SuperZhuRingData W.toSuperNearVOA hV) :
    letI := hZ.AsRing
    letI := hZ.AsAlgebra
    hZ.superZhuCommSpan ≤
      Submodule.map (W.toSuperNearVOA.superMk hV)
        (W.toSuperNearVOA.superCuspRelSpan hV) := by
  letI := hZ.AsRing
  letI := hZ.AsAlgebra
  rw [SuperZhuRingData.superZhuCommSpan, superCommSpan, Submodule.span_le]
  rintro z ⟨p, q, x, y, hx, hy, rfl⟩
  obtain ⟨g, hg, heq⟩ := superZhuComm_generator_has_superCusp_lift W hV hZ hx hy
  exact ⟨g, hg, heq⟩

end SuperNearVOA

end VOA
