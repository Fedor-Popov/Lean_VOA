import VOA.Classification.COne.QExpWeightTwoWidth

/-!
# A full-level weight-one product route to bounded denominators

The missing input `FullLevelIntegralProducts24` is a precise consequence of
Khuri-Makdisi, *Moduli interpretation of Eisenstein series*, Theorems 3.5 and
5.1 (https://arxiv.org/abs/0903.1439), together with the Fourier formula in
Mascot, *Moduli-friendly Eisenstein series over the p-adics and the computation
of modular Galois representations*, Theorem 4.2.2:
https://doi.org/10.1007/s40993-022-00329-6 .

This is full level Gamma(N), not the weight-one toric family on Gamma1(N).
We only ask for products spanning the restrictions of Gamma1 weight-two forms.
The input does not encode the Eisenstein property: it retains exactly the
modularity, coefficient arithmetic, and product identities used below.
The classical existence theorem is NOT proved in this file.

The arithmetic normalization is legitimate: the nonconstant Fourier
coefficients in Mascot's formula are sums of signed powers of a root of unity.
For each generator its constant term can be cleared by a nonzero factor
2N or 2N(1-zeta^d), and this rescaling does not change the complex product span.
In particular the requested localized coefficient ring is sufficient.
-/

open UpperHalfPlane
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne.SSHecke

/-- Finite combinations commute with q-expansion at full-level width N. -/
theorem qExpansion_sum_Gamma {N : ℕ} (hN : 0 < N) {k : ℤ} {d : ℕ}
    (c : Fin d → ℂ)
    (f : Fin d → ModularForm
      (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) k) :
    qExpansion (N : ℝ) (∑ i, c i • f i : ModularForm
      (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) k) =
      ∑ i, c i • qExpansion (N : ℝ) (f i) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let Q := ModularForm.qExpansionAddHom hNR (nat_mem_strictPeriods_Gamma N) k
  change Q (∑ i, c i • f i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact ModularForm.qExpansion_smul hNR (nat_mem_strictPeriods_Gamma N) (c i) (f i)

/-- Products of series with coefficients in a subalgebra still have coefficients there. -/
theorem coeff_mul_mem_subalgebra {R : Type*} [CommRing R] [Algebra R ℂ]
    (A : Subalgebra R ℂ) {a b : PowerSeries ℂ}
    (ha : ∀ n, a.coeff n ∈ A) (hb : ∀ n, b.coeff n ∈ A) (n : ℕ) :
    (a * b).coeff n ∈ A := by
  rw [PowerSeries.coeff_mul]
  exact A.sum_mem fun x _ => A.mul_mem (ha x.1) (hb x.2)

/-- A pointwise identity with full-level products gives an identity of width-N series. -/
theorem qExpansion_eq_sum_products {N : ℕ} (hN : 0 < N) {d : ℕ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (f g : Fin d → ModularForm
      (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 1)
    (c : Fin d → ℂ)
    (heq : ∀ τ : ℍ, F τ = ∑ i, c i * (f i τ * g i τ)) :
    qExpansion (N : ℝ) F =
      ∑ i, c i • (qExpansion (N : ℝ) (f i) * qExpansion (N : ℝ) (g i)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let H : ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 2 :=
    ∑ i, c i • (f i).mul (g i)
  have hFH : (F : ℍ → ℂ) = H := by
    funext τ
    change F τ = (ModularForm.coeHom (∑ i, c i • (f i).mul (g i))) τ
    rw [map_sum]
    simpa [ModularForm.coeHom, ModularForm.coe_smul, ModularForm.coe_mul,
      Finset.sum_apply, smul_eq_mul] using heq τ
  change qExpansion (N : ℝ) (F : ℍ → ℂ) = _
  rw [hFH]
  change qExpansion (N : ℝ) (∑ i, c i • (f i).mul (g i) : ModularForm
    (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 2) = _
  exact (qExpansion_sum_Gamma hN c (fun i => (f i).mul (g i))).trans
    (by simp_rw [ModularForm.qExpansion_mul hNR (nat_mem_strictPeriods_Gamma N)])

/-- All arithmetic after an integral full-level product identity is unconditional.
In particular the lattice can use M=N, uniformly for all primes away from N. -/
theorem exists_lattice_of_fullLevel_products {N : ℕ} (hN : 0 < N)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {d : ℕ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (f g : Fin d → ModularForm
      (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 1)
    (c : Fin d → ℂ)
    (hf : ∀ i n, (qExpansion (N : ℝ) (f i)).coeff n ∈ cyclotomicAway N ζ)
    (hg : ∀ i n, (qExpansion (N : ℝ) (g i)).coeff n ∈ cyclotomicAway N ζ)
    (heq : ∀ τ : ℍ, F τ = ∑ i, c i * (f i τ * g i τ)) :
    ∃ L : Submodule ℤ ℂ, L.FG ∧
      ∀ n, (qExpansion 1 F).coeff n ∈ awaySat N L := by
  letI : NeZero N := ⟨hN.ne'⟩
  let A := cyclotomicAway N ζ
  let L := Submodule.span A (Set.range c)
  have hL : L.FG := Submodule.fg_span (Set.finite_range c)
  obtain ⟨K, hK, hmem⟩ := fg_extension_exists_lattice hN.ne' A
    (cyclotomicAway_fg hN hζ) hL
  refine ⟨K, hK, fun n => hmem _ ?_⟩
  rw [← qExpansion_coeff_nat_mul hN F n, qExpansion_eq_sum_products hN F f g c heq]
  exact finite_combination_coeff_mem c _ (fun i j =>
    ⟨⟨_, coeff_mul_mem_subalgebra A (hf i) (hg i) j⟩, rfl⟩) (N * n)

/-- Integral products over a finite integer algebra give an ordinary finite lattice.
No localization, and no condition on a prime, is needed in this version. -/
theorem exists_int_lattice_of_fullLevel_products {N : ℕ} (hN : 0 < N)
    (A : Subalgebra ℤ ℂ) (hA : A.toSubmodule.FG) {d : ℕ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (f g : Fin d → ModularForm
      (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 1)
    (c : Fin d → ℂ)
    (hf : ∀ i n, (qExpansion (N : ℝ) (f i)).coeff n ∈ A)
    (hg : ∀ i n, (qExpansion (N : ℝ) (g i)).coeff n ∈ A)
    (heq : ∀ τ : ℍ, F τ = ∑ i, c i * (f i τ * g i τ)) :
    ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, (qExpansion 1 F).coeff n ∈ L := by
  letI : NeZero N := ⟨hN.ne'⟩
  letI : Module.Finite ℤ A := Module.Finite.of_fg hA
  let L := Submodule.span A (Set.range c)
  have hL : L.FG := Submodule.fg_span (Set.finite_range c)
  refine ⟨L.restrictScalars ℤ, hL.restrictScalars (R := ℤ), fun n => ?_⟩
  change (qExpansion 1 F).coeff n ∈ L
  rw [← qExpansion_coeff_nat_mul hN F n, qExpansion_eq_sum_products hN F f g c heq]
  exact finite_combination_coeff_mem c _ (fun i j =>
    ⟨⟨_, coeff_mul_mem_subalgebra A (hf i) (hg i) j⟩, rfl⟩) (N * n)

/-- Missing classical input, restricted to exactly the product identities needed.
TRUE by the cited full-level generation and Fourier formulas, but unproved here.
The factors need not be Gamma1 forms, and the finite list may depend on F. -/
def FullLevelIntegralProducts24 : Prop :=
  ∀ N : ℕ, 0 < N → 24 ∣ N →
    ∃ ζ : ℂ, IsPrimitiveRoot ζ N ∧
      ∀ F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 2,
        ∃ (d : ℕ)
          (f g : Fin d → ModularForm
            (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 1)
          (c : Fin d → ℂ),
          (∀ i n, (qExpansion (N : ℝ) (f i)).coeff n ∈ cyclotomicAway N ζ) ∧
          (∀ i n, (qExpansion (N : ℝ) (g i)).coeff n ∈ cyclotomicAway N ζ) ∧
          ∀ τ : ℍ, F τ = ∑ i, c i * (f i τ * g i τ)

/-- Full-level integral weight-one products imply the stronger M=N conclusion. -/
theorem qExpPrinciple24OverZInvN_two_of_fullLevelIntegralProducts
    (h : FullLevelIntegralProducts24) : QExpPrinciple24OverZInvN 2 := by
  intro N hN h24 F
  obtain ⟨ζ, hζ, hs⟩ := h N hN h24
  obtain ⟨d, f, g, c, hf, hg, heq⟩ := hs F
  exact exists_lattice_of_fullLevel_products hN hζ F f g c hf hg heq

/-- Weight-two target, conditional only on the explicitly named full-level input. -/
theorem qExpPrinciple24Away_two_of_fullLevelIntegralProducts
    (h : FullLevelIntegralProducts24) : QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_of_overZInvN
    (qExpPrinciple24OverZInvN_two_of_fullLevelIntegralProducts h)

end VOA.Classification.COne.SSHecke
