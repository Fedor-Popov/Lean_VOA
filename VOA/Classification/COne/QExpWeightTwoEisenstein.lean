import VOA.Classification.COne.QExpWeightTwoProducts

/-!
# Explicit integral coefficients for the full-level weight-one route

The positive coefficients below rewrite Mascot's signed divisor sum as two
sums over positive divisors; the second uses zeta^(N-b) in place of zeta^(-b).
Source: Mascot, *Moduli-friendly Eisenstein series over the p-adics and the
computation of modular Galois representations*, Theorem 4.2.2,
https://doi.org/10.1007/s40993-022-00329-6 .

We multiply each normalized generator by 2N, and additionally by (1-zeta^b)
when a=0 and b is nonzero. All resulting coefficients are manifestly in
Z[zeta], hence in `cyclotomicAway N zeta`. The scaling is nonzero for a
primitive root and valid indices. The (0,0) generator is set to zero.

`FullLevelEisensteinRealization24` is the remaining classical input: these
specific series are expansions of weight-one forms whose products span the
Gamma1 weight-two forms. This is a consequence of Khuri-Makdisi, Theorems 3.5
and 5.1, https://arxiv.org/abs/0903.1439, and the Fourier formula above. It is
not proved here. Unlike the more abstract product input, it has no separate
coefficient-integrality hypothesis; that part is proved below.
-/

open UpperHalfPlane
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne.SSHecke

/-- Scalar clearing the constant coefficient of one normalized weight-one generator. -/
def weightOneScale (N : ℕ) (ζ : ℂ) (a b : Fin N) : ℂ :=
  if a.val = 0 ∧ b.val ≠ 0 then 2 * N * (1 - ζ ^ b.val) else 2 * N

/-- Positive Fourier coefficients, written without negative powers. -/
def weightOneDivisorCoeff (N : ℕ) (ζ : ℂ) (a b : Fin N) (n : ℕ) : ℂ :=
  ∑ t ∈ n.divisors,
    ((if t % N = a.val then ζ ^ ((n / t) * b.val) else 0) -
    (if (t + a.val) % N = 0 then ζ ^ ((n / t) * (N - b.val)) else 0))

/-- The rescaled constant and positive coefficients; the zero index denotes the zero form. -/
def weightOneIntegralCoeff (N : ℕ) (ζ : ℂ) (a b : Fin N) (n : ℕ) : ℂ :=
  if a.val = 0 ∧ b.val = 0 then 0 else
    if n = 0 then
      if a.val = 0 then N * (1 + ζ ^ b.val) else N - 2 * a.val
    else weightOneScale N ζ a b * weightOneDivisorCoeff N ζ a b n

theorem weightOneScale_ne_zero {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (a b : Fin N) : weightOneScale N ζ a b ≠ 0 := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold weightOneScale
  split_ifs with h
  · exact mul_ne_zero (mul_ne_zero (by norm_num) hNC)
      (sub_ne_zero.mpr (hζ.pow_ne_one_of_pos_of_lt h.2 b.isLt).symm)
  · exact mul_ne_zero (by norm_num) hNC

theorem weightOneScale_mem_subalgebra {R : Type*} [CommRing R] [Algebra R ℂ]
    (A : Subalgebra R ℂ) (N : ℕ) {ζ : ℂ} (hz : ζ ∈ A) (a b : Fin N) :
    weightOneScale N ζ a b ∈ A := by
  have hbase : (2 : ℂ) * N ∈ A := A.mul_mem (A.natCast_mem 2) (A.natCast_mem N)
  unfold weightOneScale
  split_ifs
  · exact A.mul_mem hbase (A.sub_mem A.one_mem (A.pow_mem hz _))
  · exact hbase

theorem weightOneDivisorCoeff_mem_subalgebra {R : Type*} [CommRing R] [Algebra R ℂ]
    (A : Subalgebra R ℂ) (N : ℕ) {ζ : ℂ} (hz : ζ ∈ A) (a b : Fin N) (n : ℕ) :
    weightOneDivisorCoeff N ζ a b n ∈ A := by
  unfold weightOneDivisorCoeff
  apply A.sum_mem
  intro t _
  apply A.sub_mem
  all_goals split_ifs
  all_goals first
    | exact A.pow_mem hz _
    | exact A.zero_mem

/-- Integrality of every coefficient is proved without any modular-form existence input. -/
theorem weightOneIntegralCoeff_mem_subalgebra {R : Type*} [CommRing R] [Algebra R ℂ]
    (A : Subalgebra R ℂ) (N : ℕ) {ζ : ℂ} (hz : ζ ∈ A) (a b : Fin N) (n : ℕ) :
    weightOneIntegralCoeff N ζ a b n ∈ A := by
  unfold weightOneIntegralCoeff
  split_ifs with hzero hn ha
  · exact A.zero_mem
  · exact A.mul_mem (A.natCast_mem N) (A.add_mem A.one_mem (A.pow_mem hz _))
  · exact A.sub_mem (A.natCast_mem N) (A.mul_mem (A.natCast_mem 2) (A.natCast_mem a.val))
  · exact A.mul_mem (weightOneScale_mem_subalgebra A N hz a b)
      (weightOneDivisorCoeff_mem_subalgebra A N hz a b n)

theorem weightOneIntegralCoeff_mem (N : ℕ) (ζ : ℂ) (a b : Fin N) (n : ℕ) :
    weightOneIntegralCoeff N ζ a b n ∈ cyclotomicAway N ζ :=
  weightOneIntegralCoeff_mem_subalgebra _ N (Algebra.subset_adjoin (Set.mem_singleton ζ)) a b n

/-- The rescaled coefficients actually lie in Z[zeta], without inverting the level. -/
theorem weightOneIntegralCoeff_mem_int (N : ℕ) (ζ : ℂ) (a b : Fin N) (n : ℕ) :
    weightOneIntegralCoeff N ζ a b n ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) :=
  weightOneIntegralCoeff_mem_subalgebra _ N (Algebra.subset_adjoin (Set.mem_singleton ζ)) a b n

/-- Precise remaining analytic input for the explicitly normalized Fourier family.
TRUE by full-level Eisenstein generation and its Fourier formula; not an axiom or theorem.
Only the weight-two Gamma1 restriction of the published generation theorem is requested. -/
def FullLevelEisensteinRealization24 : Prop :=
  ∀ N : ℕ, 0 < N → 24 ∣ N →
    ∃ ζ : ℂ, IsPrimitiveRoot ζ N ∧
      ∃ E : Fin N → Fin N → ModularForm
        (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 1,
        (∀ a b n, (qExpansion (N : ℝ) (E a b)).coeff n =
          weightOneIntegralCoeff N ζ a b n) ∧
        ∀ F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 2,
          ∃ (d : ℕ) (a b a' b' : Fin d → Fin N) (c : Fin d → ℂ),
            ∀ τ : ℍ, F τ = ∑ i, c i * (E (a i) (b i) τ * E (a' i) (b' i) τ)

/-- The explicit Fourier realization supplies all arithmetic hypotheses of the product route. -/
theorem fullLevelIntegralProducts24_of_eisensteinRealization
    (h : FullLevelEisensteinRealization24) : FullLevelIntegralProducts24 := by
  intro N hN h24
  obtain ⟨ζ, hζ, E, hE, hspan⟩ := h N hN h24
  refine ⟨ζ, hζ, fun F => ?_⟩
  obtain ⟨d, a, b, a', b', c, hc⟩ := hspan F
  refine ⟨d, (fun i => E (a i) (b i)), (fun i => E (a' i) (b' i)), c, ?_, ?_, hc⟩
  · intro i n
    rw [hE]
    exact weightOneIntegralCoeff_mem N ζ _ _ n
  · intro i n
    rw [hE]
    exact weightOneIntegralCoeff_mem N ζ _ _ n

/-- The explicitly rescaled realization gives an ordinary finite integer coefficient lattice.
This is stronger than the away-from-level target. The analytic input remains explicit. -/
theorem qExpPrinciple24_two_of_eisensteinRealization
    (h : FullLevelEisensteinRealization24) : QExpPrinciple24 2 := by
  intro N hN h24 F
  obtain ⟨ζ, hζ, E, hE, hspan⟩ := h N hN h24
  obtain ⟨d, a, b, a', b', c, hc⟩ := hspan F
  have hzInt : IsIntegral ℤ ζ :=
    IsIntegral.of_pow hN (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  refine exists_int_lattice_of_fullLevel_products hN (Algebra.adjoin ℤ {ζ})
    hzInt.fg_adjoin_singleton F (fun i => E (a i) (b i))
    (fun i => E (a' i) (b' i)) c ?_ ?_ hc
  · intro i n
    rw [hE]
    exact weightOneIntegralCoeff_mem_int N ζ _ _ n
  · intro i n
    rw [hE]
    exact weightOneIntegralCoeff_mem_int N ζ _ _ n

/-- Explicit full-level Eisenstein realization implies bounded denominators with M=N. -/
theorem qExpPrinciple24OverZInvN_two_of_eisensteinRealization
    (h : FullLevelEisensteinRealization24) : QExpPrinciple24OverZInvN 2 :=
  qExpPrinciple24OverZInvN_two_of_fullLevelIntegralProducts
    (fullLevelIntegralProducts24_of_eisensteinRealization h)

/-- Weight-two headline with a concrete, cited, and still unproved analytic input. -/
theorem qExpPrinciple24Away_two_of_eisensteinRealization
    (h : FullLevelEisensteinRealization24) : QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_of_overZInvN
    (qExpPrinciple24OverZInvN_two_of_eisensteinRealization h)

end VOA.Classification.COne.SSHecke
