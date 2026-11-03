/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.Inputs
import Mathlib.NumberTheory.ModularForms.Discriminant
import VOA.Classification.COne.ModularDataLemmas

/-!
# Gannon–Rayhaun Theorem 3.1, conditionally (A4)

`gannonRayhaun_of_inputs` derives `GannonRayhaunStatement` from

* the seven external inputs of `Inputs.lean` (`IModData`, `ICongruenceGalois`, `ISerreStark`,
  `IVirasoro`, `ITannakian`, `IDongMason`, `IEnumeration`), and
* four **named gaps** — steps of GR §3 (or classical analysis) that are *true* but not yet
  formalized: `GapQExpansion`, `GapLemma37`, `GapThetaReduction`, `GapGaloisBound`.

The gaps are *not* inputs: each is a TODO with a proof plan in its docstring. Two are pure
classical analysis/combinatorics with no VOA content (`GapQExpansion`, `GapThetaReduction`);
two are GR-internal arguments (`GapLemma37` = GR Lemma 3.7; `GapGaloisBound` = GR (3.31)–(3.35)
with Prop. 3.8).

## What is proved here (consuming B1–B4)

1. `VOAIsomorphic.symm/.trans`, `autConj`, **`orbifold_transport`** (`W ≅ W'`, `G ≤ Aut W` ⟹
   `W^G ≅ W'^{G'}`, `G ≃* G'`), `inCOneList_of_iso`.
2. `projZ`: GR's `Proj_ℤ` realized as an average over `T^k` (`rootSum_eq`, `projZ_ch`), and its
   action on theta quotients (`avg_theta`, `projZ_theta_div_eta`, for square-free `t`).
3. `theta_div_eta_S`, `theta01_div_eta_S`: **B1** (`rankOneTheta_S_residues`,
   `rankOneTheta_zero_one_S`) combined with Mathlib's `η(-1/τ) = (√i)⁻¹ √τ η(τ)`.
4. **GR Lemma 3.10** (`IsModularData.lemma_3_10`): `S₀₀ P_V = η⁻¹ Σ_t w_t θ_{0,1,t}`.
5. **GR (3.40) ⟹ (2.33)** (`IsModularData.vacuum_identity`) from B1.
6. **GR Theorem 2.18, forward** (`IsModularData.factorized_of_vacuum_identity`): **B3**
   (`tannakian_squeeze`) fed with positivity `chR_pos` and the leading asymptotics
   `tendsto_chR` (dominated convergence) of the actual characters.
7. **GR Lemma 3.11** via **B4** (`theta_weight_nonneg`), with `hθ` produced by
   `IsModularData.formal_theta` (analytic ⟹ formal) and `hVir` from `IVirasoro`.
8. `Σ_t w_t = S₀₀` (`sum_weights`), **GR Prop 3.12** via **B2**
   (`existsUnique_weight_ne_zero`), `P_V = θ_{0,1,t⋆}/η`, and `dim W₁ ≥ 1`
   (`one_le_pCoeff_one`).
9. `inCOneList_of_extension` (Dong–Mason + transport + enumeration) and the assembly
   `gannonRayhaun_of_inputs`.

`#print axioms gannonRayhaun_of_inputs`: Lean's three only. It is **conditional** on the eleven
hypotheses above; it is not an unconditional theorem.

## TODO plan for the gaps

* `GapQExpansion.unique`: power-series uniqueness on the punctured disc
  (`HasFPowerSeriesAt.eq_formalMultilinearSeries` after `q = e^{2πiτ}`).
  `.theta`: regroup `rankOneTheta` by `N = t m²` (`HasSum.sigma`).
  `.eta_mul`: `∏(1 - qⁿ⁺¹)` as a power series (`Nat.Partition.hasProd_genFun` in the formal
  topology, then analytic convergence) and the Cauchy product
  (`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`).
* `GapThetaReduction`: `θ_{n₀,r,tℓ²} = θ_{n₀ℓ,rℓ,t}` and refinement of the modulus; both are
  `Equiv.tsum_eq` reindexings of `rankOneThetaTerm`.
* `GapLemma37`: `η`'s multiplier on `Γ(24)` (or `θ/η` invariance), `F(τ+1) = F(τ)` from
  `ch_add_nat` and `eta_add_one`, generation `Γ₁(N) = ⟨Γ(N), T⟩`, cusp bounds from
  `S_transform` and `h_a ≥ 0`.
* `GapGaloisBound`: GR Prop 3.8 (theta Galois law, classical), then the leading `q^{-1/24}`
  coefficient of `ch_V(γ_ℓ(-1/τ))` computed both ways with `theta_div_eta_S` and the
  `tendsto_chR`-style asymptotics; `d ≥ 1` (`d_ge_one`) gives `|Σ (2t/ℓ) w_t| ≥ S₀₀`.
-/

open Complex Finset Module Filter Topology

noncomputable section

namespace VOA.Classification.COne

open VOA

universe u v w

/-! ## 1. Isomorphism and orbifold transport -/

section Transport

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {𝒲 : Type v} [AddCommGroup 𝒲] [Module ℂ 𝒲]
variable {𝒰 : Type w} [AddCommGroup 𝒰] [Module ℂ 𝒰]

theorem VOAIsomorphic.refl (V : VertexOperatorAlgebra 𝒱) : VOAIsomorphic V V :=
  ⟨LinearEquiv.refl ℂ 𝒱, IsVOAHom.id V, rfl⟩

theorem isVOAHom_symm {V : VertexOperatorAlgebra 𝒱} {T : VertexOperatorAlgebra 𝒲}
    (e : 𝒱 ≃ₗ[ℂ] 𝒲) (he : IsVOAHom V T e.toLinearMap) :
    IsVOAHom T V e.symm.toLinearMap where
  map_vacuum := by
    apply e.injective
    simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
    exact he.map_vacuum.symm
  map_smul u n x := by
    apply e.injective
    simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
    have := he.map_smul (e.symm u) n (e.symm x)
    simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] at this
    exact this.symm

theorem VOAIsomorphic.symm {V : VertexOperatorAlgebra 𝒱} {T : VertexOperatorAlgebra 𝒲}
    (h : VOAIsomorphic V T) : VOAIsomorphic T V := by
  obtain ⟨e, he, hω⟩ := h
  refine ⟨e.symm, isVOAHom_symm e he, ?_⟩
  apply e.injective
  simp [hω]

theorem VOAIsomorphic.trans {V : VertexOperatorAlgebra 𝒱} {T : VertexOperatorAlgebra 𝒲}
    {U : VertexOperatorAlgebra 𝒰} (h₁ : VOAIsomorphic V T) (h₂ : VOAIsomorphic T U) :
    VOAIsomorphic V U := by
  obtain ⟨e, he, hω⟩ := h₁
  obtain ⟨f, hf, hω'⟩ := h₂
  refine ⟨e.trans f, ?_, ?_⟩
  · have := hf.comp he
    exact this
  · simp [hω, hω']

/-- Conjugating an automorphism by a VOA isomorphism. -/
def autConj {W : VertexOperatorAlgebra 𝒱} {W' : VertexOperatorAlgebra 𝒲} (e : 𝒱 ≃ₗ[ℂ] 𝒲)
    (he : IsVOAHom W W' e.toLinearMap) (hω : e W.conformalVector = W'.conformalVector)
    (g : Aut W) : Aut W' where
  toLinearEquiv := (e.symm.trans g.toLinearEquiv).trans e
  map_smul' u n x := by
    have hs := isVOAHom_symm e he
    simp only [LinearEquiv.trans_apply]
    have h1 := hs.map_smul u n x
    simp only [LinearEquiv.coe_toLinearMap] at h1
    rw [h1, g.map_smul']
    have h2 := he.map_smul (g.toLinearEquiv (e.symm u)) n (g.toLinearEquiv (e.symm x))
    simpa only [LinearEquiv.coe_toLinearMap] using h2
  map_vacuum := by
    have hs := isVOAHom_symm e he
    simp only [LinearEquiv.trans_apply]
    have h1 := hs.map_vacuum
    simp only [LinearEquiv.coe_toLinearMap] at h1
    rw [h1, g.map_vacuum]
    simpa only [LinearEquiv.coe_toLinearMap] using he.map_vacuum
  map_omega := by
    simp only [LinearEquiv.trans_apply]
    have h1 : e.symm W'.conformalVector = W.conformalVector := by
      rw [← hω]; simp
    rw [h1, g.map_omega, hω]

@[simp] theorem autConj_apply {W : VertexOperatorAlgebra 𝒱} {W' : VertexOperatorAlgebra 𝒲}
    (e : 𝒱 ≃ₗ[ℂ] 𝒲) (he : IsVOAHom W W' e.toLinearMap)
    (hω : e W.conformalVector = W'.conformalVector) (g : Aut W) (x : 𝒲) :
    autConj e he hω g x = e (g (e.symm x)) := rfl

/-- Conjugation by a VOA isomorphism, as a group homomorphism `Aut W →* Aut W'`. -/
def autConjHom {W : VertexOperatorAlgebra 𝒱} {W' : VertexOperatorAlgebra 𝒲} (e : 𝒱 ≃ₗ[ℂ] 𝒲)
    (he : IsVOAHom W W' e.toLinearMap) (hω : e W.conformalVector = W'.conformalVector) :
    Aut W →* Aut W' where
  toFun := autConj e he hω
  map_one' := Aut.ext (LinearEquiv.ext fun x => by simp)
  map_mul' g g' := Aut.ext (LinearEquiv.ext fun x => by simp)

theorem autConjHom_injective {W : VertexOperatorAlgebra 𝒱} {W' : VertexOperatorAlgebra 𝒲}
    (e : 𝒱 ≃ₗ[ℂ] 𝒲) (he : IsVOAHom W W' e.toLinearMap)
    (hω : e W.conformalVector = W'.conformalVector) :
    Function.Injective (autConjHom e he hω) := by
  intro g g' hgg
  apply Aut.ext
  apply LinearEquiv.ext
  intro x
  have := congrArg (fun k : Aut W' => k (e x)) hgg
  simpa [autConjHom] using this

/-- **Orbifold transport.** If `W ≅ W'` (as VOAs) and `G ≤ Aut W`, then the conjugate subgroup
`G' ≤ Aut W'` is isomorphic to `G` and `W^G ≅ W'^{G'}`. -/
theorem orbifold_transport {W : VertexOperatorAlgebra 𝒱} {W' : VertexOperatorAlgebra 𝒲}
    (h : VOAIsomorphic W W') (G : Subgroup (Aut W)) :
    ∃ G' : Subgroup (Aut W'), Nonempty (G ≃* G') ∧
      VOAIsomorphic (orbifoldVOA G) (orbifoldVOA G') := by
  obtain ⟨e, he, hω⟩ := h
  set φ := autConjHom e he hω
  refine ⟨G.map φ, ⟨G.equivMapOfInjective φ (autConjHom_injective e he hω)⟩, ?_⟩
  have hcar : (orbifold (G.map φ)).carrier = (orbifold G).carrier.map e.toLinearMap := by
    ext y
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      intro g hg
      have := hy (φ g) ⟨g, hg, rfl⟩
      change e (g (e.symm y)) = y at this
      apply e.injective
      simpa using this
    · rintro ⟨x, hx, rfl⟩
      rintro _ ⟨g, hg, rfl⟩
      change e (g (e.symm (e x))) = e x
      simp only [LinearEquiv.symm_apply_apply]
      rw [hx g hg]
  let f : (orbifold G).carrier ≃ₗ[ℂ] (orbifold (G.map φ)).carrier :=
    (e.submoduleMap (orbifold G).carrier).trans (LinearEquiv.ofEq _ _ hcar.symm)
  have hf : ∀ x, ((f x : (orbifold (G.map φ)).carrier) : 𝒲) = e x := fun x => rfl
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · apply Subtype.ext
    rw [LinearEquiv.coe_toLinearMap, hf]
    exact he.map_vacuum
  · intro u n x
    apply Subtype.ext
    rw [LinearEquiv.coe_toLinearMap, hf]
    exact he.map_smul u n x
  · apply Subtype.ext
    rw [hf]
    exact hω

/-- Membership in the list is invariant under isomorphism. -/
theorem inCOneList_of_iso {V : VertexOperatorAlgebra 𝒱} {T : VertexOperatorAlgebra 𝒲}
    (h : VOAIsomorphic V T) (hT : InCOneList T) : InCOneList V := by
  rcases hT with ⟨m, hm, h'⟩ | ⟨m, hm, h2, h'⟩ | ⟨G, hG, h'⟩ | ⟨G, hG, h'⟩ | ⟨G, hG, h'⟩
  · exact Or.inl ⟨m, hm, h.trans h'⟩
  · exact Or.inr (Or.inl ⟨m, hm, h2, h.trans h'⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨G, hG, h.trans h'⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨G, hG, h.trans h'⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨G, hG, h.trans h'⟩)))

end Transport

/-! ## 2. Projection onto integer weights, and `θ/η` -/

/-- Projection onto integer conformal weights, by averaging over `T^k`. -/
def projZ (N : ℕ) (c : ℂ) (f : ℂ → ℂ) (τ : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k ∈ range N, cexp (2 * Real.pi * I * (c / 24) * k) * f (τ + k)

open Classical in
theorem rootSum_eq {N : ℕ} (hN : 0 < N) (x : ℂ) (hx : ∃ m : ℤ, (N : ℂ) * x = m) :
    (N : ℂ)⁻¹ * ∑ k ∈ range N, cexp (2 * Real.pi * I * x * k) =
      if ∃ m : ℤ, x = m then 1 else 0 := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set ζ := cexp (2 * Real.pi * I * x) with hζ
  have hpow : ∀ k : ℕ, cexp (2 * Real.pi * I * x * k) = ζ ^ k := by
    intro k; rw [hζ, ← Complex.exp_nat_mul]; ring_nf
  simp_rw [hpow]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    have : ζ = 1 := by
      rw [hζ, show 2 * ↑Real.pi * I * (m : ℂ) = m * (2 * Real.pi * I) by ring,
        Complex.exp_int_mul_two_pi_mul_I]
    simp [this, hN0]
  · have hζ1 : ζ ≠ 1 := by
      intro h1
      rw [hζ, Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      apply h; refine ⟨n, ?_⟩
      have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, I_ne_zero]
      have := hn
      field_simp at this
      linear_combination this
    obtain ⟨m, hm⟩ := hx
    have hζN : ζ ^ N = 1 := by
      rw [hζ, ← Complex.exp_nat_mul,
        show (N : ℂ) * (2 * ↑Real.pi * I * x) = m * (2 * Real.pi * I) by rw [← hm]; ring,
        Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hζ1, hζN, sub_self, zero_div, mul_zero]

/-- The root-of-unity sum for a rational `A/B`, `B ∣ N`. -/
theorem rootSum_div {N : ℕ} (hN : 0 < N) (A : ℤ) {B : ℕ} (hB : 0 < B) (hBN : B ∣ N) :
    (N : ℂ)⁻¹ * ∑ k ∈ range N, cexp (2 * Real.pi * I * ((A : ℂ) / B) * k) =
      if (B : ℤ) ∣ A then 1 else 0 := by
  have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hiff : (∃ m : ℤ, (A : ℂ) / B = m) ↔ (B : ℤ) ∣ A := by
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      have : (A : ℂ) = B * m := by rw [← hm]; field_simp
      exact_mod_cast this
    · rintro ⟨m, rfl⟩
      exact ⟨m, by push_cast; field_simp⟩
  rw [rootSum_eq hN]
  · by_cases hd : (B : ℤ) ∣ A
    · rw [if_pos (hiff.2 hd), if_pos hd]
    · rw [if_neg (fun h => hd (hiff.1 h)), if_neg hd]
  · obtain ⟨q, rfl⟩ := hBN
    exact ⟨q * A, by push_cast; field_simp⟩

theorem projZ_congr {N : ℕ} {c : ℂ} {f g : ℂ → ℂ} (hfg : ∀ τ : ℂ, 0 < τ.im → f τ = g τ)
    {τ : ℂ} (hτ : 0 < τ.im) : projZ N c f τ = projZ N c g τ := by
  unfold projZ
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hfg (τ + k) (by simpa using hτ)]

theorem projZ_sum {ι : Type*} (s : Finset ι) (N : ℕ) (c : ℂ) (f : ι → ℂ → ℂ) (τ : ℂ) :
    projZ N c (fun τ => ∑ i ∈ s, f i τ) τ = ∑ i ∈ s, projZ N c (f i) τ := by
  unfold projZ
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem projZ_const_mul (N : ℕ) (c z : ℂ) (f : ℂ → ℂ) (τ : ℂ) :
    projZ N c (fun τ => z * f τ) τ = z * projZ N c f τ := by
  unfold projZ
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### η -/

theorem eta_add_one (τ : ℂ) :
    ModularForm.eta (τ + 1) = cexp (2 * Real.pi * I / 24) * ModularForm.eta τ := by
  unfold ModularForm.eta
  have hq : ∀ n, ModularForm.eta_q n (τ + 1) = ModularForm.eta_q n τ := by
    intro n
    rw [ModularForm.eta_q_eq_cexp, ModularForm.eta_q_eq_cexp,
      show 2 * ↑Real.pi * I * (↑n + 1) * (τ + 1) =
        2 * ↑Real.pi * I * (↑n + 1) * τ + ((n + 1 : ℕ) : ℤ) * (2 * Real.pi * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp_rw [hq]
  rw [← mul_assoc]
  congr 1
  simp only [Function.Periodic.qParam]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eta_add_nat (τ : ℂ) (k : ℕ) :
    ModularForm.eta (τ + k) = cexp (2 * Real.pi * I * (1 / 24) * k) * ModularForm.eta τ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, eta_add_one, ih, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring

/-! ### Projection of theta quotients -/

theorem dvd_sq_iff_of_squarefree {t : ℕ} (ht : Squarefree t) {r : ℕ} (hr : 0 < r) (n : ℤ) :
    ((4 * t * r ^ 2 : ℕ) : ℤ) ∣ n ^ 2 ↔ ((2 * t * r : ℕ) : ℤ) ∣ n := by
  constructor
  · intro h
    have h2r : ((2 * r : ℕ) : ℤ) ^ 2 ∣ n ^ 2 :=
      (Dvd.intro (t : ℤ) (by push_cast; ring)).trans h
    obtain ⟨m, rfl⟩ := (Int.pow_dvd_pow_iff two_ne_zero).1 h2r
    have hr0 : ((4 * r ^ 2 : ℕ) : ℤ) ≠ 0 := by positivity
    have htm : (t : ℤ) ∣ m ^ 2 := by
      obtain ⟨k, hk⟩ := h
      refine ⟨k, ?_⟩
      have : ((4 * r ^ 2 : ℕ) : ℤ) * m ^ 2 = ((4 * r ^ 2 : ℕ) : ℤ) * (t * k) := by
        push_cast at hk ⊢; linear_combination hk
      exact mul_left_cancel₀ hr0 this
    have hts : Squarefree (t : ℤ) := Int.squarefree_natCast.2 ht
    obtain ⟨k, rfl⟩ := (hts.dvd_pow_iff_dvd two_ne_zero).1 htm
    exact ⟨k, by push_cast; ring⟩
  · rintro ⟨k, rfl⟩
    exact ⟨t * k ^ 2, by push_cast; ring⟩

theorem hasSum_theta_proj {t r : ℕ} (ht : Squarefree t) (hr : 0 < r) {j : ℕ} (hj : j < r)
    {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun m : ℤ => if ((4 * t * r ^ 2 : ℕ) : ℤ) ∣ ((j : ℤ) + r * m) ^ 2 then
        rankOneThetaTerm j r (1 / (4 * (t : ℝ) * (r : ℝ) ^ 2)) τ m else 0)
      (if j = 0 then rankOneTheta 0 1 t τ else 0) := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne_zero
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  by_cases hj0 : j = 0
  · subst hj0
    rw [if_pos rfl]
    have htpos : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht.ne_zero
    set f : ℤ → ℂ := fun m => if ((4 * t * r ^ 2 : ℕ) : ℤ) ∣ (((0 : ℕ) : ℤ) + r * m) ^ 2 then
        rankOneThetaTerm ((0 : ℕ) : ℤ) r (1 / (4 * (t : ℝ) * (r : ℝ) ^ 2)) τ m else 0 with hf
    have hcond : ∀ m : ℤ, ((4 * t * r ^ 2 : ℕ) : ℤ) ∣ (((0 : ℕ) : ℤ) + r * m) ^ 2 ↔
        ((2 * t : ℕ) : ℤ) ∣ m := by
      intro m
      rw [dvd_sq_iff_of_squarefree ht hr]
      simp only [Nat.cast_zero, zero_add]
      push_cast
      rw [show (2 * (t : ℤ) * r) = r * (2 * t) by ring]
      exact mul_dvd_mul_iff_left (by exact_mod_cast hr.ne')
    set g : ℤ → ℤ := fun k => (2 * t : ℕ) * k with hg
    have hginj : Function.Injective g := by
      intro a b hab
      have h2t : ((2 * t : ℕ) : ℤ) ≠ 0 := by
        have := ht.ne_zero; positivity
      exact mul_left_cancel₀ h2t hab
    have hsupp : ∀ x, x ∉ Set.range g → f x = 0 := by
      intro x hx
      rw [hf]; simp only
      rw [if_neg]
      intro h
      obtain ⟨k, hk⟩ := (hcond x).1 h
      exact hx ⟨k, hk.symm⟩
    rw [← hginj.hasSum_iff hsupp]
    have hθ := (summable_rankOneThetaTerm 0 one_ne_zero htpos hτ).hasSum
    rw [rankOneTheta]
    refine hθ.congr_fun ?_
    intro k
    simp only [Function.comp, hf, hg]
    rw [if_pos ((hcond _).2 ⟨k, rfl⟩)]
    simp only [rankOneThetaTerm]
    congr 1
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne_zero
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast
    field_simp
    ring
  · rw [if_neg hj0]
    convert hasSum_zero with m
    rw [if_neg]
    intro h
    have h1 := (dvd_sq_iff_of_squarefree ht hr _).1 h
    have h2 : (r : ℤ) ∣ (j : ℤ) + r * m :=
      (Dvd.intro ((2 * t : ℕ) : ℤ) (by push_cast; ring)).trans h1
    have h3 : (r : ℤ) ∣ (j : ℤ) := by
      have := (Int.dvd_add_left (Dvd.intro m rfl)).1 h2
      exact this
    have h4 : r ∣ j := by exact_mod_cast h3
    exact hj0 (Nat.eq_zero_of_dvd_of_lt h4 hj)

/-- Averaging a theta series over `T^k`: `N⁻¹ Σ_k θ_{j,r,1/(4tr²)}(τ + k) = [j = 0] θ_{0,1,t}(τ)`
for square-free `t` and `4 t r² ∣ N`. -/
theorem avg_theta {N t r : ℕ} (hN : 0 < N) (ht : Squarefree t) (hr : 0 < r)
    (hdiv : 4 * t * r ^ 2 ∣ N) {j : ℕ} (hj : j < r) {τ : ℂ} (hτ : 0 < τ.im) :
    (N : ℂ)⁻¹ * ∑ k ∈ range N, rankOneTheta j r (1 / (4 * (t : ℝ) * (r : ℝ) ^ 2)) (τ + k) =
      if j = 0 then rankOneTheta 0 1 t τ else 0 := by
  have htpos : (0 : ℝ) < 1 / (4 * (t : ℝ) * (r : ℝ) ^ 2) := by
    have : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht.ne_zero
    have : (0 : ℝ) < r := by exact_mod_cast hr
    positivity
  have hr0 : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  have hB : 0 < 4 * t * r ^ 2 := by
    have := Nat.pos_of_ne_zero ht.ne_zero; positivity
  have hsum : HasSum (fun m : ℤ => (N : ℂ)⁻¹ * ∑ k ∈ range N,
      rankOneThetaTerm j r (1 / (4 * (t : ℝ) * (r : ℝ) ^ 2)) (τ + k) m)
      ((N : ℂ)⁻¹ * ∑ k ∈ range N, rankOneTheta j r (1 / (4 * (t : ℝ) * (r : ℝ) ^ 2)) (τ + k)) := by
    refine HasSum.mul_left _ (hasSum_sum fun k _ => ?_)
    exact (summable_rankOneThetaTerm _ hr0 htpos (by simpa using hτ)).hasSum
  refine hsum.unique ((hasSum_theta_proj ht hr hj hτ).congr_fun fun m => ?_)
  have hterm : ∀ k : ℕ, rankOneThetaTerm j r (1 / (4 * (t : ℝ) * (r : ℝ) ^ 2)) (τ + k) m =
      rankOneThetaTerm j r (1 / (4 * (t : ℝ) * (r : ℝ) ^ 2)) τ m *
        cexp (2 * Real.pi * I * ((((((j : ℤ) + r * m) ^ 2 : ℤ)) : ℂ) /
          ((4 * t * r ^ 2 : ℕ) : ℂ)) * k) := by
    intro k
    simp only [rankOneThetaTerm, ← Complex.exp_add]
    congr 1
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne_zero
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast
    field_simp
  simp_rw [hterm]
  rw [← Finset.mul_sum, mul_left_comm, rootSum_div hN _ hB hdiv]
  split_ifs <;> simp

theorem projZ_theta_div_eta {N t r : ℕ} (hN : 0 < N) (ht : Squarefree t) (hr : 0 < r)
    (hdiv : 4 * t * r ^ 2 ∣ N) {j : ℕ} (hj : j < r) {τ : ℂ} (hτ : 0 < τ.im) :
    projZ N 1 (fun τ => rankOneTheta j r (1 / (4 * (t : ℝ) * (r : ℝ) ^ 2)) τ /
        ModularForm.eta τ) τ =
      (if j = 0 then rankOneTheta 0 1 t τ else 0) / ModularForm.eta τ := by
  have hη : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero hτ
  unfold projZ
  have hk : ∀ k : ℕ, cexp (2 * Real.pi * I * (1 / 24) * k) *
      (rankOneTheta j r (1 / (4 * (t : ℝ) * (r : ℝ) ^ 2)) (τ + k) / ModularForm.eta (τ + k)) =
      rankOneTheta j r (1 / (4 * (t : ℝ) * (r : ℝ) ^ 2)) (τ + k) / ModularForm.eta τ := by
    intro k
    rw [eta_add_nat]
    have : cexp (2 * Real.pi * I * (1 / 24) * k) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  simp only [hk]
  rw [← Finset.sum_div, ← mul_div_assoc, avg_theta hN ht hr hdiv hj hτ]

/-! ### The `S`-transformation of `θ/η` -/

theorem cpow_half_neg_I_mul {τ : ℂ} (hτ : 0 < τ.im) {a : ℝ} (ha : 0 < a) :
    (-I * (τ / a)) ^ (1 / 2 : ℂ) =
      ((Real.sqrt a)⁻¹ : ℝ) * ((Complex.sqrt I)⁻¹ * Complex.sqrt τ) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hIτ : -I * τ ≠ 0 := mul_ne_zero (neg_ne_zero.2 I_ne_zero) hτ0
  have heq : -I * (τ / a) = ((a⁻¹ : ℝ) : ℂ) * (-I * τ) := by push_cast; ring
  have hlog1 : Complex.log (((a⁻¹ : ℝ) : ℂ) * (-I * τ)) =
      Real.log a⁻¹ + Complex.log (-I * τ) := Complex.log_ofReal_mul (inv_pos.2 ha) hIτ
  have hlog2 : Complex.log (-I * τ) = Complex.log (-I) + Complex.log τ := by
    rw [Complex.log_mul_eq_add_log_iff (neg_ne_zero.2 I_ne_zero) hτ0, Complex.arg_neg_I]
    have h0 : 0 ≤ Complex.arg τ := Complex.arg_nonneg_iff.2 hτ.le
    have h1 := Complex.arg_le_pi τ
    constructor <;> linarith [Real.pi_pos]
  rw [heq, Complex.cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast (inv_pos.2 ha).ne') hIτ),
    hlog1, hlog2, Complex.log_neg_I, sqrt_eq_exp I_ne_zero, sqrt_eq_exp hτ0,
    Complex.log_I, ← Complex.exp_neg, ← Complex.exp_add]
  have hreal : cexp ((Real.log a⁻¹ : ℂ) * (1 / 2)) = ((Real.sqrt a)⁻¹ : ℝ) := by
    rw [show ((Real.log a⁻¹ : ℝ) : ℂ) * (1 / 2) = ((Real.log a⁻¹ * (1 / 2) : ℝ) : ℂ) by
        push_cast; ring,
      ← Complex.ofReal_exp, ← Real.rpow_def_of_pos (inv_pos.2 ha), ← Real.sqrt_eq_rpow,
      Real.sqrt_inv]
  rw [← hreal, ← Complex.exp_add]
  congr 1
  ring

theorem eta_S {τ : ℂ} (hτ : 0 < τ.im) :
    ModularForm.eta (-1 / τ) = (Complex.sqrt I)⁻¹ * (Complex.sqrt τ * ModularForm.eta τ) := by
  have := ModularForm.eta_comp_eq_csqrt_I_inv hτ
  simpa using this

/-- **`S`-transformation of `θ_{n₀,r,t}/η`** (B1 + Mathlib's `η(-1/τ)`), GR (3.15):
`θ_{n₀,r,t}(-1/τ)/η(-1/τ) = (r√(2t))⁻¹ Σ_{j mod r} e^{2πi j n₀/r} θ_{j,r,1/(4tr²)}(τ)/η(τ)`. -/
theorem theta_div_eta_S (n₀ : ℤ) (r : ℕ) [NeZero r] {t : ℝ} (ht : 0 < t) {τ : ℂ}
    (hτ : 0 < τ.im) :
    rankOneTheta n₀ r t (-1 / τ) / ModularForm.eta (-1 / τ) =
      ((Real.sqrt (2 * t * (r : ℝ) ^ 2))⁻¹ : ℝ) *
        ∑ j : Fin r, cexp (2 * Real.pi * I * (j : ℕ) * n₀ / r) *
          (rankOneTheta (j : ℕ) r (1 / (4 * t * (r : ℝ) ^ 2)) τ / ModularForm.eta τ) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hr : (0 : ℝ) < r := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne r))
  have ha : (0 : ℝ) < 2 * t * (r : ℝ) ^ 2 := by positivity
  have hη : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero hτ
  have hsI : Complex.sqrt I ≠ 0 := by
    rw [sqrt_eq_exp I_ne_zero]; exact Complex.exp_ne_zero _
  have hsτ : Complex.sqrt τ ≠ 0 := by
    rw [sqrt_eq_exp hτ0]; exact Complex.exp_ne_zero _
  rw [rankOneTheta_S_residues n₀ r ht hτ, eta_S hτ]
  rw [show (2 * (t : ℂ) * (((r : ℤ) : ℂ)) ^ 2) = ((2 * t * (r : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring,
    cpow_half_neg_I_mul hτ ha]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  field_simp
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  ring_nf


/-! ## 3. Elementary facts about modular data -/

namespace ModularData

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
  {D : ModularData V}

theorem IsModularData.d_vac (hD : D.IsModularData) : D.d D.vac = 1 := by
  have h1 := hD.S_vac_left D.vac
  rw [hD.S_vac_vac] at h1
  have h2 : D.S00 = D.S00 * D.d D.vac := by exact_mod_cast h1
  have := hD.S00_pos
  field_simp at h2
  linarith

/-- Pseudo-unitarity: a non-vacuum simple module has positive lowest weight. -/
theorem IsModularData.h_pos (hD : D.IsModularData) (hV : Nice V) {a : D.ι} (ha : a ≠ D.vac) :
    0 < D.h a := by
  have hempty : IsEmpty (ModuleEquiv V (D.module a) (adjointModule V)) := by
    refine ⟨fun e => ha ?_⟩
    obtain ⟨f⟩ := hD.vac_iso
    exact hD.distinct a D.vac ⟨e.trans f.symm⟩
  have := hV.2 (D.carrier a) (D.module a) (hD.irred a) hempty (D.h a) (hD.weight_lowest a)
  simpa using this

theorem IsModularData.h_nonneg (hD : D.IsModularData) (hV : Nice V) (a : D.ι) : 0 ≤ D.h a := by
  by_cases ha : a = D.vac
  · rw [ha, hD.h_vac]
  · exact (hD.h_pos hV ha).le

theorem isIntWeight_iff (a : D.ι) : D.IsIntWeight a ↔ ∃ m : ℤ, (D.h a : ℂ) = m := by
  unfold IsIntWeight
  constructor
  · intro h
    refine ⟨(D.h a).num, ?_⟩
    have := Rat.coe_int_num_of_den_eq_one h
    rw [← this]; push_cast; rfl
  · rintro ⟨m, hm⟩
    have : D.h a = m := by exact_mod_cast hm
    rw [this]; rfl

theorem mem_intLabels (a : D.ι) : a ∈ D.intLabels ↔ D.IsIntWeight a := by
  simp [intLabels]

theorem IsModularData.vac_mem_intLabels (hD : D.IsModularData) : D.vac ∈ D.intLabels := by
  rw [mem_intLabels, isIntWeight_iff]; exact ⟨0, by simp [hD.h_vac]⟩

/-- **T-transformation** of a character, from its `q`-expansion:
`ch_a(τ + k) = e^{2πi k (h_a - c/24)} ch_a(τ)`. -/
theorem IsModularData.ch_add_nat (hD : D.IsModularData) (a : D.ι) (k : ℕ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    D.ch a (τ + k) =
      cexp (2 * Real.pi * I * ((D.h a : ℂ) - V.centralCharge / 24) * k) * D.ch a τ := by
  have h1 := hD.char a (τ + k) (by simpa using hτ)
  have h2 := (hD.char a τ hτ).mul_left
    (cexp (2 * Real.pi * I * ((D.h a : ℂ) - V.centralCharge / 24) * k))
  refine h1.unique (h2.congr_fun ?_)
  intro n
  rw [mul_left_comm, ← Complex.exp_add]
  congr 1
  have : 2 * ↑Real.pi * I * (↑(D.h a) + ↑n - V.centralCharge / 24) * (τ + ↑k) =
      2 * ↑Real.pi * I * (↑(D.h a) - V.centralCharge / 24) * ↑k +
        2 * ↑Real.pi * I * (↑(D.h a) + ↑n - V.centralCharge / 24) * τ +
        ((n * k : ℕ) : ℤ) * (2 * ↑Real.pi * I) := by push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end ModularData

/-! ## 4. GR Lemma 3.10 (`P_V`) -/


theorem im_neg_one_div_pos {τ : ℂ} (hτ : 0 < τ.im) : 0 < (-1 / τ).im := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  rw [neg_div, Complex.neg_im, Complex.div_im]
  simp only [Complex.one_re, Complex.one_im, zero_mul, one_mul, zero_div, zero_sub,
    neg_neg]
  exact div_pos hτ (Complex.normSq_pos.2 hτ0)

/-- `(√(2 t r²))⁻¹ = 1/(r √(2t))`. -/
theorem inv_sqrt_two_mul_sq (t : ℝ) (ht : 0 ≤ t) (r : ℕ) :
    (((Real.sqrt (2 * t * (r : ℝ) ^ 2))⁻¹ : ℝ) : ℂ) = 1 / ((r : ℂ) * (Real.sqrt (2 * t) : ℂ)) := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  push_cast
  ring

namespace ModularData

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
  {D : ModularData V}

theorem IsModularData.level_mul_h (hD : D.IsModularData) {N : ℕ} (hN : D.IsLevel N) (a : D.ι) :
    ∃ m : ℤ, (N : ℂ) * (D.h a : ℂ) = m := by
  obtain ⟨k₁, h₁⟩ := hN.2 a
  obtain ⟨k₀, h₀⟩ := hN.2 D.vac
  rw [hD.h_vac] at h₀
  refine ⟨k₁ - k₀, ?_⟩
  push_cast
  rw [← h₁, ← h₀]
  ring

/-- **`Proj_ℤ` on characters**: averaging over `T^k` keeps exactly the integer-weight
characters. -/
theorem IsModularData.projZ_ch (hD : D.IsModularData) {N : ℕ} (hN : D.IsLevel N) (a : D.ι)
    {τ : ℂ} (hτ : 0 < τ.im) :
    projZ N V.centralCharge (D.ch a) τ = if D.IsIntWeight a then D.ch a τ else 0 := by
  unfold projZ
  have hk : ∀ k : ℕ, cexp (2 * Real.pi * I * (V.centralCharge / 24) * k) * D.ch a (τ + k) =
      cexp (2 * Real.pi * I * (D.h a : ℂ) * k) * D.ch a τ := by
    intro k
    rw [hD.ch_add_nat a k hτ, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp only [hk]
  rw [← Finset.sum_mul, ← mul_assoc, rootSum_eq hN.1 _ (hD.level_mul_h hN a)]
  by_cases hi : D.IsIntWeight a
  · rw [if_pos ((isIntWeight_iff a).1 hi), if_pos hi, one_mul]
  · rw [if_neg (fun h => hi ((isIntWeight_iff a).2 h)), if_neg hi, zero_mul]

/-- The module side of `P_V`: `Proj_ℤ[ch_V(-1/τ)] = Σ_{h_b ∈ ℤ} S_{0b} ch_b(τ) = S₀₀ P_V(τ)`
(GR (2.28)–(2.30)). -/
theorem IsModularData.projZ_vac_S (hD : D.IsModularData) {N : ℕ} (hN : D.IsLevel N) {τ : ℂ}
    (hτ : 0 < τ.im) :
    projZ N V.centralCharge (fun τ => D.ch D.vac (-1 / τ)) τ =
      D.S00 * ∑ b ∈ D.intLabels, D.d b * D.ch b τ := by
  rw [projZ_congr (g := fun τ => ∑ b, D.S D.vac b * D.ch b τ)
    (fun τ hτ => hD.S_transform D.vac τ hτ) hτ, projZ_sum]
  simp only [projZ_const_mul, hD.projZ_ch hN _ hτ, intLabels, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · rw [hD.S_vac_left]; ring
  · simp

/-- **GR Lemma 3.10** (`P_V`, eq. (3.24)–(3.27)), consuming B1. Suppose `c = 1`, `N` is a level,
and the vacuum character has the canonical theta decomposition of GR Lemma 3.9,
`η(τ) ch_V(τ) = Σ_{t∈T} Σ_{j mod r_t} a_t(j) θ_{j,r_t,t}(τ)` with square-free `t` and
`4 t r_t² ∣ N`. Then
`S₀₀ Σ_{h_b ∈ ℤ} d_b ch_b(τ) = η(τ)⁻¹ Σ_t w_t θ_{0,1,t}(τ)`, `w_t = (r_t √(2t))⁻¹ Σ_j a_t(j)`. -/
theorem IsModularData.lemma_3_10 (hD : D.IsModularData) (hc : V.centralCharge = 1) {N : ℕ}
    (hN : D.IsLevel N) (T : Finset ℕ) (hT : ∀ t ∈ T, Squarefree t) (r : ℕ → ℕ)
    [∀ t, NeZero (r t)] (hrN : ∀ t ∈ T, 4 * t * r t ^ 2 ∣ N) (a : (t : ℕ) → ZMod (r t) → ℂ)
    (hdec : ∀ τ : ℂ, 0 < τ.im → ModularForm.eta τ * D.ch D.vac τ =
      ∑ t ∈ T, ∑ j : ZMod (r t), a t j * rankOneTheta (j.val : ℕ) (r t) t τ)
    {τ : ℂ} (hτ : 0 < τ.im) :
    D.S00 * ∑ b ∈ D.intLabels, D.d b * D.ch b τ =
      (∑ t ∈ T, (1 / ((r t : ℂ) * (Real.sqrt (2 * t) : ℂ)) * ∑ j : ZMod (r t), a t j) *
        rankOneTheta 0 1 t τ) / ModularForm.eta τ := by
  rw [← hD.projZ_vac_S hN hτ, hc]
  -- the theta side of `ch_V(-1/τ)`
  have hS : ∀ τ' : ℂ, 0 < τ'.im → D.ch D.vac (-1 / τ') =
      ∑ t ∈ T, ∑ j : ZMod (r t), a t j *
        ((((Real.sqrt (2 * (t : ℝ) * ((r t : ℕ) : ℝ) ^ 2))⁻¹ : ℝ) : ℂ) *
          ∑ i : Fin (r t), cexp (2 * Real.pi * I * (i : ℕ) * ((j.val : ℕ) : ℤ) / (r t : ℕ)) *
            (rankOneTheta (i : ℕ) (r t) (1 / (4 * (t : ℝ) * ((r t : ℕ) : ℝ) ^ 2)) τ' /
              ModularForm.eta τ')) := by
    intro τ' hτ'
    have hm := im_neg_one_div_pos hτ'
    have hη := ModularForm.eta_ne_zero hm
    have h := hdec _ hm
    rw [mul_comm, ← eq_div_iff hη, Finset.sum_div] at h
    rw [h]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have htpos : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero (hT t ht).ne_zero
    rw [mul_div_assoc, theta_div_eta_S _ (r t) htpos hτ']
  rw [projZ_congr (f := fun τ => D.ch D.vac (-1 / τ)) hS hτ, projZ_sum T, Finset.sum_div]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [projZ_sum, projZ_const_mul]
  have hrpos : 0 < r t := Nat.pos_of_ne_zero (NeZero.ne _)
  have hproj : ∀ i : Fin (r t), projZ N 1 (fun τ => rankOneTheta (i : ℕ) (r t)
      (1 / (4 * (t : ℝ) * ((r t : ℕ) : ℝ) ^ 2)) τ / ModularForm.eta τ) τ =
      (if (i : ℕ) = 0 then rankOneTheta 0 1 t τ else 0) / ModularForm.eta τ :=
    fun i => projZ_theta_div_eta hN.1 (hT t ht) hrpos (hrN t ht) i.2 hτ
  simp only [hproj]
  have hi : ∀ j : ZMod (r t), ∑ i : Fin (r t),
      cexp (2 * Real.pi * I * (i : ℕ) * ((j.val : ℕ) : ℤ) / (r t : ℕ)) *
        ((if (i : ℕ) = 0 then rankOneTheta 0 1 t τ else 0) / ModularForm.eta τ) =
      rankOneTheta 0 1 t τ / ModularForm.eta τ := by
    intro j
    rw [Fintype.sum_eq_single ⟨0, hrpos⟩]
    · simp
    · intro i hi0
      have : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
      simp [this]
  simp only [hi]
  rw [inv_sqrt_two_mul_sq _ (Nat.cast_nonneg _), Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end ModularData


/-! ## 5. GR Theorem 2.18 via B3 -/

/-- Leading behaviour of a positive `q`-series at `τ = iy`, `y → ∞`. -/
theorem tendsto_lead (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (x : ℝ) (hx : 0 ≤ x) (F : ℝ → ℝ)
    (hF : ∀ y, 0 < y → HasSum (fun n : ℕ => c n * Real.exp (-(2 * Real.pi * (x + n - 1 / 24) * y)))
      (F y)) :
    Tendsto (fun y => Real.exp (-(2 * Real.pi * y * 1 / 24)) * F y) atTop
      (𝓝 (∑' n : ℕ, if x + n = 0 then c n else 0)) := by
  have hrw : ∀ y, 0 < y → Real.exp (-(2 * Real.pi * y * 1 / 24)) * F y =
      ∑' n : ℕ, c n * Real.exp (-(2 * Real.pi * (x + n) * y)) := by
    intro y hy
    refine (((hF y hy).mul_left (Real.exp (-(2 * Real.pi * y * 1 / 24)))).tsum_eq.symm.trans
      (tsum_congr fun n => ?_)).symm.symm
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  refine Tendsto.congr' (EventuallyEq.symm ((eventually_gt_atTop 0).mono fun y hy => hrw y hy)) ?_
  refine tendsto_tsum_of_dominated_convergence (bound := fun n => c n *
    Real.exp (-(2 * Real.pi * (x + n)))) ?_ ?_ ?_
  · have h1 := (hF 1 one_pos).summable.mul_left (Real.exp (-(2 * Real.pi * (1 / 24))))
    refine h1.congr fun n => ?_
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  · intro n
    by_cases h0 : x + n = 0
    · simp only [h0, if_true, mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one]
      exact tendsto_const_nhds
    · simp only [h0, if_false]
      have hpos : 0 < x + n := lt_of_le_of_ne (by positivity) (Ne.symm h0)
      have : Tendsto (fun y : ℝ => -(2 * Real.pi * (x + n) * y)) atTop atBot := by
        have h2 : 0 < 2 * Real.pi * (x + n) := by positivity
        exact tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop h2)
      simpa using (Real.tendsto_exp_atBot.comp this).const_mul (c n)
  · filter_upwards [eventually_ge_atTop 1] with y hy n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc n), abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hc n)
    have : 0 ≤ 2 * Real.pi * (x + n) := by positivity
    nlinarith

theorem cexp_at_imag (x y : ℝ) :
    cexp (2 * Real.pi * I * (x : ℂ) * ((y : ℂ) * I)) =
      ((Real.exp (-(2 * Real.pi * x * y)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- A `q`-series with real coefficients, evaluated at `τ = iy`, is real. -/
theorem hasSum_re_of_imag (c : ℕ → ℝ) (x y : ℝ) (z : ℂ)
    (h : HasSum (fun n : ℕ => (c n : ℂ) * cexp (2 * Real.pi * I * ((x : ℂ) + n - 1 / 24) *
      ((y : ℂ) * I))) z) :
    HasSum (fun n : ℕ => c n * Real.exp (-(2 * Real.pi * (x + n - 1 / 24) * y))) z.re ∧
      z = (z.re : ℂ) := by
  have hterm : ∀ n : ℕ, (c n : ℂ) * cexp (2 * Real.pi * I * ((x : ℂ) + n - 1 / 24) *
      ((y : ℂ) * I)) = ((c n * Real.exp (-(2 * Real.pi * (x + n - 1 / 24) * y)) : ℝ) : ℂ) := by
    intro n
    rw [show ((x : ℂ) + n - 1 / 24) = ((x + n - 1 / 24 : ℝ) : ℂ) by push_cast; ring,
      cexp_at_imag]
    push_cast; ring
  simp_rw [hterm] at h
  have hre : HasSum (fun n : ℕ => c n * Real.exp (-(2 * Real.pi * (x + n - 1 / 24) * y))) z.re := by
    have := h.mapL Complex.reCLM
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at this
    exact this
  refine ⟨hre, ?_⟩
  exact h.unique (Complex.hasSum_ofReal.2 hre)

namespace ModularData

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
  {D : ModularData V}

/-- `ch_a(iy)` as a real number. -/
def chR (D : ModularData V) (a : D.ι) (y : ℝ) : ℝ := (D.ch a ((y : ℂ) * I)).re

theorem IsModularData.char_imag (hD : D.IsModularData) (hc : V.centralCharge = 1) (a : D.ι)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => (finrank ℂ ((D.module a).weight ((D.h a : ℂ) + n)) : ℝ) *
      Real.exp (-(2 * Real.pi * ((D.h a : ℝ) + n - 1 / 24) * y))) (D.chR a y) ∧
      D.ch a ((y : ℂ) * I) = (D.chR a y : ℂ) := by
  have h := hD.char a ((y : ℂ) * I) (by simpa using hy)
  rw [hc] at h
  have := hasSum_re_of_imag (fun n => (finrank ℂ ((D.module a).weight ((D.h a : ℂ) + n)) : ℝ))
    (D.h a) y _ (by simpa using h)
  exact this

theorem IsModularData.char_vac_imag (hD : D.IsModularData) (hc : V.centralCharge = 1)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => (finrank ℂ (V.grading n) : ℝ) *
      Real.exp (-(2 * Real.pi * ((0 : ℝ) + n - 1 / 24) * y))) (D.chR D.vac y) := by
  have h := hD.char_vac ((y : ℂ) * I) (by simpa using hy)
  rw [hc] at h
  exact (hasSum_re_of_imag (fun n => (finrank ℂ (V.grading n) : ℝ)) 0 y _
    (by simpa using h)).1

theorem IsModularData.chR_pos (hD : D.IsModularData) (hc : V.centralCharge = 1) (a : D.ι)
    {y : ℝ} (hy : 0 < y) : 0 < D.chR a y := by
  have h := (hD.char_imag hc a hy).1
  refine lt_of_lt_of_le ?_ (le_hasSum h 0 fun n _ => by positivity)
  have hfd := (D.module a).finrank ((D.h a : ℂ) + (0 : ℕ))
  have hne : (D.module a).weight ((D.h a : ℂ) + (0 : ℕ)) ≠ ⊥ := by
    simpa using hD.weight_lowest a
  have : 0 < finrank ℂ ((D.module a).weight ((D.h a : ℂ) + (0 : ℕ))) :=
    Nat.pos_of_ne_zero fun h0 => hne (Submodule.finrank_eq_zero.1 h0)
  have : (0 : ℝ) < finrank ℂ ((D.module a).weight ((D.h a : ℂ) + (0 : ℕ))) := by
    exact_mod_cast this
  positivity

theorem IsModularData.tendsto_chR (hD : D.IsModularData) (hV : Nice V)
    (hc : V.centralCharge = 1) (a : D.ι) :
    Tendsto (fun y => Real.exp (-(2 * Real.pi * y * 1 / 24)) * D.chR a y) atTop
      (𝓝 (if a = D.vac then 1 else 0)) := by
  by_cases ha : a = D.vac
  · subst ha
    rw [if_pos rfl]
    have h := tendsto_lead (fun n => (finrank ℂ (V.grading n) : ℝ)) (fun n => by positivity)
      0 le_rfl (D.chR D.vac) fun y hy => hD.char_vac_imag hc hy
    convert h using 2
    rw [tsum_eq_single 0]
    · simp [hV.1.stronglyFinite.finrank_grading_zero_eq_one]
    · intro n hn
      simp [hn]
  · rw [if_neg ha]
    have hpos : (0 : ℝ) < D.h a := by exact_mod_cast hD.h_pos hV ha
    have h := tendsto_lead (fun n => (finrank ℂ ((D.module a).weight ((D.h a : ℂ) + n)) : ℝ))
      (fun n => by positivity) (D.h a) hpos.le (D.chR a) fun y hy => (hD.char_imag hc a hy).1
    convert h using 2
    have : ∀ n : ℕ, (D.h a : ℝ) + n ≠ 0 := fun n => by positivity
    simp [this]

/-- **GR Theorem 2.18, forward direction, consuming B3 (`tannakian_squeeze`).** If the vacuum
identity (2.33) `Σ_{h_b∈ℤ} (κ d_b - Σ_{h_a∈ℤ} d_a S_ab) ch_b = 0` holds on `ℍ` (here
`κ = D S₀₀`), then `S_ab = S₀₀ d_a d_b` on the integer-weight modules. -/
theorem IsModularData.factorized_of_vacuum_identity (hD : D.IsModularData) (hV : Nice V)
    (hc : V.centralCharge = 1) (κ : ℝ)
    (hid : ∀ τ : ℂ, 0 < τ.im → ∑ b ∈ D.intLabels,
      ((κ : ℂ) * D.d b - ∑ a ∈ D.intLabels, (D.d a : ℂ) * D.S a b) * D.ch b τ = 0) :
    ∀ a b, D.IsIntWeight a → D.IsIntWeight b → D.S a b = D.S00 * D.d a * D.d b := by
  set Z := D.intLabels
  have hvZ : D.vac ∈ Z := hD.vac_mem_intLabels
  set i₀ : Z := ⟨D.vac, hvZ⟩
  have hsq := tannakian_squeeze (ι := Z) i₀ (fun a b => D.S a b) (fun a => D.d a) D.S00 1
    (((κ / D.S00 : ℝ)) : ℂ) (fun b y => D.chR b y)
    (fun a => lt_of_lt_of_le one_pos (hD.d_ge_one a)) (hD.d_vac) hD.S00_pos
    (fun a => hD.S_vac_right a) (fun a b => hD.S_bound a b)
    (fun b y hy => hD.chR_pos hc b hy)
    (by simpa [i₀] using hD.tendsto_chR hV hc D.vac)
    (fun b hb => by
      have hne : (b : D.ι) ≠ D.vac := fun h => hb (Subtype.ext h)
      simpa [hne] using hD.tendsto_chR hV hc b)
    (fun y hy => by
      have h := hid ((y : ℂ) * I) (by simpa using hy)
      have hS0 : (D.S00 : ℂ) ≠ 0 := by exact_mod_cast hD.S00_pos.ne'
      rw [← Finset.sum_coe_sort Z] at h
      refine Eq.trans ?_ h
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [(hD.char_imag hc b (by exact hy)).2, ← Finset.sum_coe_sort Z]
      congr 2
      push_cast
      field_simp)
  intro a b ha hb
  exact hsq.2 ⟨a, (mem_intLabels a).2 ha⟩ ⟨b, (mem_intLabels b).2 hb⟩

end ModularData


/-! ## 6. GR (3.40): the vacuum identity (2.33) from B1 -/


/-- `θ_{0,1,t}(-1/τ)/η(-1/τ) = (2t)^{-1/2} θ_{0,1,1/(4t)}(τ)/η(τ)` (B1 + `η(-1/τ)`). -/
theorem theta01_div_eta_S {t : ℝ} (ht : 0 < t) {τ : ℂ} (hτ : 0 < τ.im) :
    rankOneTheta 0 1 t (-1 / τ) / ModularForm.eta (-1 / τ) =
      ((Real.sqrt (2 * t))⁻¹ : ℝ) * (rankOneTheta 0 1 (1 / (4 * t)) τ / ModularForm.eta τ) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hη : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero hτ
  have hsI : Complex.sqrt I ≠ 0 := by
    rw [sqrt_eq_exp I_ne_zero]; exact Complex.exp_ne_zero _
  have hsτ : Complex.sqrt τ ≠ 0 := by
    rw [sqrt_eq_exp hτ0]; exact Complex.exp_ne_zero _
  rw [rankOneTheta_zero_one_S ht hτ, eta_S hτ,
    show (2 * (t : ℂ)) = ((2 * t : ℝ) : ℂ) by push_cast; ring,
    cpow_half_neg_I_mul hτ (by positivity : (0 : ℝ) < 2 * t)]
  field_simp

theorem projZ_theta01_div_eta {N t : ℕ} (hN : 0 < N) (ht : Squarefree t) (htN : 4 * t ∣ N)
    {τ : ℂ} (hτ : 0 < τ.im) :
    projZ N 1 (fun τ => rankOneTheta 0 1 (1 / (4 * (t : ℝ))) τ / ModularForm.eta τ) τ =
      rankOneTheta 0 1 t τ / ModularForm.eta τ := by
  have h := projZ_theta_div_eta (r := 1) (j := 0) hN ht one_pos (by simpa using htN) one_pos hτ
  simpa using h

namespace ModularData

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
  {D : ModularData V}

/-- **GR (3.40) ⟹ (2.33)**, consuming B1. If `P_V = Σ_{h_a∈ℤ} d_a ch_a = θ_{0,1,t}/η` with `t`
square-free and `4t ∣ N` for a level `N`, then
`Σ_{h_b∈ℤ} ((2t)^{-1/2} d_b - Σ_{h_a∈ℤ} d_a S_ab) ch_b = 0` on `ℍ`. -/
theorem IsModularData.vacuum_identity (hD : D.IsModularData) (hc : V.centralCharge = 1)
    {N : ℕ} (hN : D.IsLevel N) {t : ℕ} (ht : Squarefree t) (htN : 4 * t ∣ N)
    (hP : ∀ τ : ℂ, 0 < τ.im →
      ∑ a ∈ D.intLabels, (D.d a : ℂ) * D.ch a τ = rankOneTheta 0 1 t τ / ModularForm.eta τ)
    {τ : ℂ} (hτ : 0 < τ.im) :
    ∑ b ∈ D.intLabels, ((((Real.sqrt (2 * t))⁻¹ : ℝ) : ℂ) * D.d b -
      ∑ a ∈ D.intLabels, (D.d a : ℂ) * D.S a b) * D.ch b τ = 0 := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht.ne_zero
  -- (A) the module side
  have hA : projZ N 1 (fun τ => ∑ a ∈ D.intLabels, (D.d a : ℂ) * D.ch a (-1 / τ)) τ =
      ∑ b ∈ D.intLabels, (∑ a ∈ D.intLabels, (D.d a : ℂ) * D.S a b) * D.ch b τ := by
    rw [projZ_congr (g := fun τ => ∑ a ∈ D.intLabels, (D.d a : ℂ) *
        ∑ b, D.S a b * D.ch b τ)
      (fun τ hτ => by simp only [hD.S_transform _ τ hτ]) hτ, projZ_sum]
    simp only [projZ_const_mul, projZ_sum, ← hc, hD.projZ_ch hN _ hτ]
    simp only [mul_ite, mul_zero, ← Finset.sum_filter]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  -- (B) the theta side
  have hB : projZ N 1 (fun τ => ∑ a ∈ D.intLabels, (D.d a : ℂ) * D.ch a (-1 / τ)) τ =
      (((Real.sqrt (2 * t))⁻¹ : ℝ) : ℂ) * ∑ b ∈ D.intLabels, (D.d b : ℂ) * D.ch b τ := by
    rw [projZ_congr (g := fun τ => (((Real.sqrt (2 * t))⁻¹ : ℝ) : ℂ) *
        (rankOneTheta 0 1 (1 / (4 * (t : ℝ))) τ / ModularForm.eta τ))
      (fun τ hτ => by
        simp only
        rw [hP _ (im_neg_one_div_pos hτ), theta01_div_eta_S htpos hτ]) hτ,
      projZ_const_mul, projZ_theta01_div_eta hN.1 ht htN hτ, hP τ hτ]
  have h := hA.symm.trans hB
  rw [Finset.mul_sum] at h
  rw [← sub_eq_zero.2 h.symm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

end ModularData


/-! ## 7. The `q`-expansion gap, B4/B2 consumption, and the conditional theorem -/


/-- **Gap: the `q`-expansion principle** (classical analysis; *not* VOA-specific).
1. `unique`: a function on `ℍ` has at most one `q`-expansion `Σ_{n≥0} c_n qⁿ`;
2. `eta_mul`: if `g(τ) = Σ c_n q^{n - 1/24}` on `ℍ`, then `η g = Σ_N [(∏(1-qᵏ)) · Σ c_n qⁿ]_N q^N`
   (Euler's product expanded as `eulerSeries`, and the Cauchy product of absolutely convergent
   series);
3. `theta`: `θ_{j,r,t}(τ) = Σ_N #{m ≡ j (r) : t m² = N} q^N` (`thetaSeries`, B4).
TODO: all three are provable from Mathlib (`HasFPowerSeriesAt` uniqueness; `tprod` of
`1 - qⁿ⁺¹` against `Nat.Partition` / `eulerSeries`; regrouping `rankOneTheta` by `N = t m²`). -/
structure GapQExpansion : Prop where
  unique : ∀ (c c' : ℕ → ℂ) (f : ℂ → ℂ),
    (∀ τ : ℂ, 0 < τ.im → HasSum (fun n : ℕ => c n * cexp (2 * Real.pi * I * n * τ)) (f τ)) →
    (∀ τ : ℂ, 0 < τ.im → HasSum (fun n : ℕ => c' n * cexp (2 * Real.pi * I * n * τ)) (f τ)) →
    c = c'
  eta_mul : ∀ (c : ℕ → ℂ) (g : ℂ → ℂ),
    (∀ τ : ℂ, 0 < τ.im →
      HasSum (fun n : ℕ => c n * cexp (2 * Real.pi * I * ((n : ℂ) - 1 / 24) * τ)) (g τ)) →
    ∀ τ : ℂ, 0 < τ.im →
      HasSum (fun n : ℕ => PowerSeries.coeff n
        (PowerSeries.map (Int.castRingHom ℂ) eulerSeries * PowerSeries.mk c) *
          cexp (2 * Real.pi * I * n * τ)) (ModularForm.eta τ * g τ)
  theta : ∀ (r : ℕ) [NeZero r] (j : ZMod r) (t : ℕ), 0 < t → ∀ τ : ℂ, 0 < τ.im →
    HasSum (fun n : ℕ => (thetaCoeff r j t n : ℂ) * cexp (2 * Real.pi * I * n * τ))
      (rankOneTheta (j.val : ℕ) r t τ)

namespace ModularData

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
  {D : ModularData V}

/-- An integer-weight label has `h_a ∈ ℕ`. -/
theorem IsModularData.exists_nat_h (hD : D.IsModularData) (hV : Nice V) {a : D.ι}
    (ha : D.IsIntWeight a) : ∃ k : ℕ, (D.h a : ℂ) = k := by
  obtain ⟨m, hm⟩ := (isIntWeight_iff a).1 ha
  have h0 : (0 : ℚ) ≤ D.h a := hD.h_nonneg hV a
  have hq : D.h a = m := by exact_mod_cast hm
  have hm0 : 0 ≤ m := by exact_mod_cast hq ▸ h0
  refine ⟨m.toNat, ?_⟩
  rw [hm]
  have : ((m.toNat : ℤ)) = m := Int.toNat_of_nonneg hm0
  rw [← this]; push_cast; rfl

/-- The `q`-expansion of an integer-weight character in absolute weights:
`ch_a(τ) = Σ_n dim (V_a)_n q^{n - 1/24}`. -/
theorem IsModularData.char_int (hD : D.IsModularData) (hV : Nice V) (hc : V.centralCharge = 1)
    {a : D.ι} (ha : D.IsIntWeight a) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => (finrank ℂ ((D.module a).weight (n : ℂ)) : ℂ) *
      cexp (2 * Real.pi * I * ((n : ℂ) - 1 / 24) * τ)) (D.ch a τ) := by
  obtain ⟨k, hk⟩ := hD.exists_nat_h hV ha
  have h := hD.char a τ hτ
  rw [hc, hk] at h
  have hz : ∑ i ∈ Finset.range k, (finrank ℂ ((D.module a).weight (i : ℂ)) : ℂ) *
      cexp (2 * Real.pi * I * ((i : ℂ) - 1 / 24) * τ) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hik : i < k := Finset.mem_range.1 hi
    have hbot : (D.module a).weight (i : ℂ) = ⊥ := by
      by_contra hne
      obtain ⟨m, hm⟩ := hD.weight_support a _ hne
      rw [hk] at hm
      have : (i : ℂ) = ((k + m : ℕ) : ℂ) := by push_cast; exact hm
      have := Nat.cast_injective this
      omega
    rw [hbot, finrank_bot]; simp
  rw [← add_zero (D.ch a τ), ← hz, ← hasSum_nat_add_iff k]
  refine h.congr_fun fun n => ?_
  rw [show ((n + k : ℕ) : ℂ) = (k : ℂ) + n by push_cast; ring]

/-- The coefficients `p_n = Σ_{h_a∈ℤ} d_a dim (V_a)_n` of `P_V = Σ_{h_a∈ℤ} d_a ch_a`. -/
def pCoeff (D : ModularData V) (n : ℕ) : ℝ :=
  ∑ a ∈ D.intLabels, D.d a * (finrank ℂ ((D.module a).weight (n : ℂ)) : ℝ)

theorem IsModularData.hasSum_PV (hD : D.IsModularData) (hV : Nice V) (hc : V.centralCharge = 1)
    {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => (D.pCoeff n : ℂ) * cexp (2 * Real.pi * I * ((n : ℂ) - 1 / 24) * τ))
      (∑ a ∈ D.intLabels, (D.d a : ℂ) * D.ch a τ) := by
  have h := hasSum_sum (s := D.intLabels) fun a ha =>
    (hD.char_int hV hc ((mem_intLabels a).1 ha) hτ).mul_left (D.d a : ℂ)
  refine h.congr_fun fun n => ?_
  simp only [pCoeff]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- `dim (V_vac)_n = dim V_n`, by uniqueness of `q`-expansions. -/
theorem IsModularData.vac_dims (hQ : GapQExpansion) (hD : D.IsModularData) (hV : Nice V)
    (hc : V.centralCharge = 1) (n : ℕ) :
    finrank ℂ ((D.module D.vac).weight (n : ℂ)) = finrank ℂ (V.grading n) := by
  have hvac : D.IsIntWeight D.vac := (mem_intLabels _).1 hD.vac_mem_intLabels
  have key := hQ.unique (fun n => (finrank ℂ ((D.module D.vac).weight (n : ℂ)) : ℂ))
    (fun n => (finrank ℂ (V.grading n) : ℂ))
    (fun τ => cexp (2 * Real.pi * I * τ / 24) * D.ch D.vac τ)
    (fun τ hτ => ((hD.char_int hV hc hvac hτ).mul_left _).congr_fun fun n => by
      rw [mul_left_comm, ← Complex.exp_add]; congr 2; ring)
    (fun τ hτ => by
      have h := hD.char_vac τ hτ
      rw [hc] at h
      exact (h.mul_left _).congr_fun fun n => by
        rw [mul_left_comm, ← Complex.exp_add]; congr 2; ring)
  exact_mod_cast congrFun key n

theorem IsModularData.pCoeff_zero (hQ : GapQExpansion) (hD : D.IsModularData) (hV : Nice V)
    (hc : V.centralCharge = 1) : D.pCoeff 0 = 1 := by
  unfold pCoeff
  rw [Finset.sum_eq_single D.vac]
  · rw [hD.d_vac, one_mul]
    have := hD.vac_dims hQ hV hc 0
    rw [this]
    exact_mod_cast hV.1.stronglyFinite.finrank_grading_zero_eq_one
  · intro a _ ha
    have hpos := hD.h_pos hV ha
    have hbot : (D.module a).weight ((0 : ℕ) : ℂ) = ⊥ := by
      by_contra hne
      obtain ⟨m, hm⟩ := hD.weight_support a _ hne
      have : (0 : ℝ) = (D.h a : ℝ) + m := by
        have := congrArg Complex.re hm
        simpa using this
      have : (0 : ℝ) < D.h a := by exact_mod_cast hpos
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    rw [hbot, finrank_bot]; simp
  · intro h; exact absurd hD.vac_mem_intLabels h

end ModularData

theorem coeff_zero_eulerSeries : PowerSeries.coeff 0 eulerSeries = 1 := by
  simp [eulerSeries]

theorem coeff_one_eulerSeries : PowerSeries.coeff 1 eulerSeries = -1 := by
  simp [eulerSeries, PowerSeries.coeff_X]

theorem thetaCoeff_one_zero (t : ℕ) : thetaCoeff 1 0 t 0 = 1 := by
  simp [thetaCoeff, Finset.filter_singleton]

theorem coeff_zero_mul' (φ ψ : PowerSeries ℂ) :
    PowerSeries.coeff 0 (φ * ψ) = PowerSeries.coeff 0 φ * PowerSeries.coeff 0 ψ := by
  simp [PowerSeries.coeff_mul]

theorem coeff_one_mul' (φ ψ : PowerSeries ℂ) :
    PowerSeries.coeff 1 (φ * ψ) = PowerSeries.coeff 0 φ * PowerSeries.coeff 1 ψ +
      PowerSeries.coeff 1 φ * PowerSeries.coeff 0 ψ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
  simp

theorem hasSum_theta01 (hQ : GapQExpansion) {t : ℕ} (ht : 0 < t) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => (thetaCoeff 1 0 t n : ℂ) * cexp (2 * Real.pi * I * n * τ))
      (rankOneTheta 0 1 t τ) := by
  simpa using hQ.theta 1 0 t ht τ hτ

namespace ModularData

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
  {D : ModularData V}

/-- **Analytic ⟹ formal**: the canonical theta decomposition of `η ch_V` on `ℍ` gives the
formal identity B4 consumes as `hθ`. -/
theorem IsModularData.formal_theta (hQ : GapQExpansion) (hD : D.IsModularData)
    (hc : V.centralCharge = 1) (T : Finset ℕ) (hT : ∀ t ∈ T, 0 < t) (R : ℕ → ℕ+)
    (a : (t : ℕ) → ZMod (R t) → ℂ)
    (hdec : ∀ τ : ℂ, 0 < τ.im → ModularForm.eta τ * D.ch D.vac τ =
      ∑ t ∈ T, ∑ j : ZMod (R t), a t j * rankOneTheta (j.val : ℕ) (R t : ℕ) t τ) :
    PowerSeries.map (Int.castRingHom ℂ) (eulerSeries * vacuumSeries V) =
      ∑ t ∈ T, ∑ j : ZMod (R t),
        a t j • PowerSeries.map (Int.castRingHom ℂ) (thetaSeries (R t) j t) := by
  set c : ℕ → ℂ := fun n => (finrank ℂ (V.grading n) : ℂ) with hcdef
  have hL := hQ.eta_mul c (D.ch D.vac) fun τ hτ => by
    have h := hD.char_vac τ hτ
    rw [hc] at h
    exact h
  have hR : ∀ τ : ℂ, 0 < τ.im → HasSum (fun n : ℕ =>
      (∑ t ∈ T, ∑ j : ZMod (R t), a t j * (thetaCoeff (R t) j t n : ℂ)) *
        cexp (2 * Real.pi * I * n * τ)) (ModularForm.eta τ * D.ch D.vac τ) := by
    intro τ hτ
    rw [hdec τ hτ]
    have := hasSum_sum (s := T) fun t ht => hasSum_sum (s := Finset.univ) fun j _ =>
      (hQ.theta (R t) j t (hT t ht) τ hτ).mul_left (a t j)
    refine this.congr_fun fun n => ?_
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have key := hQ.unique _ _ _ (fun τ hτ => hL τ hτ) hR
  ext n
  rw [coeff_theta_sum, ← congrFun key n, map_mul]
  congr 2

/-- **`Σ_t w_t = S₀₀`** (end of the proof of GR Lemma 3.10): the `q⁰` coefficient. -/
theorem IsModularData.sum_weights (hQ : GapQExpansion) (hD : D.IsModularData) (hV : Nice V)
    (hc : V.centralCharge = 1) (T : Finset ℕ) (hT : ∀ t ∈ T, 0 < t) (wC : ℕ → ℂ)
    (h310 : ∀ τ : ℂ, 0 < τ.im → (D.S00 : ℂ) * ∑ b ∈ D.intLabels, (D.d b : ℂ) * D.ch b τ =
      (∑ t ∈ T, wC t * rankOneTheta 0 1 t τ) / ModularForm.eta τ) :
    (D.S00 : ℂ) = ∑ t ∈ T, wC t := by
  have hL := hQ.eta_mul (fun n => (D.S00 : ℂ) * D.pCoeff n)
    (fun τ => (D.S00 : ℂ) * ∑ b ∈ D.intLabels, (D.d b : ℂ) * D.ch b τ) fun τ hτ =>
      ((hD.hasSum_PV hV hc hτ).mul_left (D.S00 : ℂ)).congr_fun fun n => by ring
  have hR : ∀ τ : ℂ, 0 < τ.im → HasSum (fun n : ℕ =>
      (∑ t ∈ T, wC t * (thetaCoeff 1 0 t n : ℂ)) * cexp (2 * Real.pi * I * n * τ))
      (ModularForm.eta τ * ((D.S00 : ℂ) * ∑ b ∈ D.intLabels, (D.d b : ℂ) * D.ch b τ)) := by
    intro τ hτ
    rw [h310 τ hτ, mul_div_cancel₀ _ (ModularForm.eta_ne_zero hτ)]
    have := hasSum_sum (s := T) fun t ht => (hasSum_theta01 hQ (hT t ht) hτ).mul_left (wC t)
    refine this.congr_fun fun n => ?_
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have key := congrFun (hQ.unique _ _ _ (fun τ hτ => hL τ hτ) hR) 0
  rw [coeff_zero_mul'] at key
  simp only [PowerSeries.coeff_map, coeff_zero_eulerSeries, PowerSeries.coeff_mk,
    hD.pCoeff_zero hQ hV hc, thetaCoeff_one_zero] at key
  simpa using key

/-- **`dim W₁ ≥ 1`**: if `P_V = θ_{0,1,t}/η`, then `p₁ = 1 + #{m : t m² = 1} ≥ 1`
(the `q^{1-1/24}` coefficient, GR proof of Prop 3.6). -/
theorem IsModularData.one_le_pCoeff_one (hQ : GapQExpansion) (hD : D.IsModularData)
    (hV : Nice V) (hc : V.centralCharge = 1) {t : ℕ} (ht : 0 < t)
    (hP : ∀ τ : ℂ, 0 < τ.im →
      ∑ a ∈ D.intLabels, (D.d a : ℂ) * D.ch a τ = rankOneTheta 0 1 t τ / ModularForm.eta τ) :
    1 ≤ D.pCoeff 1 := by
  have hL := hQ.eta_mul (fun n => (D.pCoeff n : ℂ))
    (fun τ => ∑ b ∈ D.intLabels, (D.d b : ℂ) * D.ch b τ) fun τ hτ => hD.hasSum_PV hV hc hτ
  have hR : ∀ τ : ℂ, 0 < τ.im → HasSum (fun n : ℕ =>
      (thetaCoeff 1 0 t n : ℂ) * cexp (2 * Real.pi * I * n * τ))
      (ModularForm.eta τ * ∑ b ∈ D.intLabels, (D.d b : ℂ) * D.ch b τ) := by
    intro τ hτ
    rw [hP τ hτ, mul_div_cancel₀ _ (ModularForm.eta_ne_zero hτ)]
    exact hasSum_theta01 hQ ht hτ
  have key := congrFun (hQ.unique _ _ _ (fun τ hτ => hL τ hτ) hR) 1
  rw [coeff_one_mul'] at key
  simp only [PowerSeries.coeff_map, coeff_zero_eulerSeries, coeff_one_eulerSeries,
    PowerSeries.coeff_mk, hD.pCoeff_zero hQ hV hc, map_one, map_neg] at key
  have key' : (D.pCoeff 1 : ℂ) = 1 + (thetaCoeff 1 0 t 1 : ℂ) := by
    push_cast at key
    linear_combination key
  have : D.pCoeff 1 = 1 + (thetaCoeff 1 0 t 1 : ℝ) := by exact_mod_cast key'
  rw [this]
  have : (0 : ℝ) ≤ thetaCoeff 1 0 t 1 := Nat.cast_nonneg _
  linarith

/-- A level exists: `N = 24 ∏_a den(h_a)` (for `c = 1`). -/
theorem exists_level (hc : V.centralCharge = 1) :
    ∃ N : ℕ, D.IsLevel N ∧ 24 ∣ N := by
  set P := ∏ a, (D.h a).den with hP
  refine ⟨24 * P, ⟨by positivity, fun a => ?_⟩, dvd_mul_right _ _⟩
  obtain ⟨Q, hQ⟩ : (D.h a).den ∣ P := Finset.dvd_prod_of_mem _ (Finset.mem_univ a)
  refine ⟨24 * Q * (D.h a).num - P, ?_⟩
  rw [hc]
  have hmul : D.h a * (D.h a).den = (D.h a).num := Rat.mul_den_eq_num _
  have : ((24 * P : ℕ) : ℚ) * (D.h a - 1 / 24) = ((24 * Q * (D.h a).num - P : ℤ) : ℚ) := by
    rw [hQ]
    push_cast
    linear_combination (24 * (Q : ℚ)) * hmul
  have := congrArg (fun x : ℚ => (x : ℂ)) this
  push_cast at this ⊢
  rw [← this]

end ModularData

/-! ## Gaps: GR-internal steps not yet formalized -/

/-- **Gap: GR Lemma 3.7.** For a nice `c = 1` VOA and any level `N`, if the characters are
`Γ(N)`-invariant (`ICongruenceGalois`), then `F_V = η · ch_V` is a holomorphic θ-type weight-½
form for `Γ₁(N)`. TODO: `η(γτ)/η(τ) = θ(γτ)/θ(τ)` on `Γ(24)` (GR (3.11)), `F_V(τ+1) = F_V(τ)`,
`⟨Γ(N), T⟩ ⊇ Γ₁(N)`, and holomorphy at the cusps from `S_transform` + pseudo-unitarity. -/
def GapLemma37 : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    V.centralCharge = 1 → ∀ D : ModularData V, D.IsModularData → ∀ N : ℕ, D.IsLevel N →
      (∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ a (τ : ℂ), 0 < τ.im →
        D.ch a (mobius γ τ) = D.ch a τ) →
      IsThetaTypeForm N (fun τ => ModularForm.eta τ * D.ch D.vac τ)

/-- **Gap: the theta relations (3.13)** (pure theta-function combinatorics). A finite
combination of `θ_{n₀,r,t}` with `4 t r² ∣ N` can be rewritten with square-free `t` and one
modulus `R_t` per `t`, `4 t R_t² ∣ N`. TODO: `θ_{n₀,r,tℓ²} = θ_{n₀ℓ,rℓ,t}` and
`θ_{n₀,r,t} = Σ_{n₀' ≡ n₀ (r)} θ_{n₀',rℓ,t}`, both termwise reindexings of `rankOneTheta`. -/
def GapThetaReduction : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (s : Finset (ℤ × ℕ × ℕ)) (coef : ℤ × ℕ × ℕ → ℂ),
    (∀ p ∈ s, 1 ≤ p.2.1 ∧ 1 ≤ p.2.2 ∧ 4 * p.2.2 * p.2.1 ^ 2 ∣ N) →
    ∃ (T : Finset ℕ) (R : ℕ → ℕ+) (a : (t : ℕ) → ZMod (R t) → ℂ),
      (∀ t ∈ T, Squarefree t ∧ 4 * t * (R t : ℕ) ^ 2 ∣ N) ∧
      ∀ τ : ℂ, 0 < τ.im → ∑ p ∈ s, coef p * rankOneTheta p.1 p.2.1 p.2.2 τ =
        ∑ t ∈ T, ∑ j : ZMod (R t), a t j * rankOneTheta (j.val : ℕ) (R t : ℕ) t τ

/-- **Gap: the Galois bound, GR (3.31)–(3.35)** with Prop. 3.8. For a nice `c = 1` VOA whose
modular data are Galois-symmetric at level `N` and whose `η ch_V` has the canonical theta
decomposition, `|Σ_t (2t/ℓ) w_t| ≥ S₀₀` for every `ℓ` coprime to `N`. TODO: the theta Galois
law (3.18) `θ_{n₀,r,t}(γ_ℓτ)/η(γ_ℓτ) = (2t/ℓ) θ_{ℓn₀,r,t}(τ)/η(τ)` (classical, Shimura), then
compare the `q^{-1/24}` coefficients of the `S`-transforms of (3.31) and (3.32) using
`theta_div_eta_S` and `tendsto_chR`; `d ≥ 1` gives (3.35). -/
def GapGaloisBound : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    V.centralCharge = 1 → ∀ D : ModularData V, D.IsModularData → ∀ N : ℕ, D.IsLevel N →
      D.GaloisSymmetric N →
      ∀ (T : Finset ℕ) (R : ℕ → ℕ+) (a : (t : ℕ) → ZMod (R t) → ℂ),
        (∀ t ∈ T, Squarefree t ∧ 4 * t * (R t : ℕ) ^ 2 ∣ N) →
        (∀ τ : ℂ, 0 < τ.im → ModularForm.eta τ * D.ch D.vac τ =
          ∑ t ∈ T, ∑ j : ZMod (R t), a t j * rankOneTheta (j.val : ℕ) (R t : ℕ) t τ) →
        ∀ ℓ : ℕ, ℓ.Coprime N →
          D.S00 ≤ ‖∑ t ∈ T, (jacobiSym (2 * (t : ℤ)) ℓ : ℂ) *
            ((1 / ((R t : ℂ) * (Real.sqrt (2 * t) : ℂ))) * ∑ j : ZMod (R t), a t j)‖


/-! ## The conditional theorem -/

/-- **The last step** (GR proof of Thm 3.1 from Prop 3.6): if `V ≅ W^G` with `W` nice, `c = 1`,
`W₁ ≠ 0` and `G` finite, then `V` is in the list. Consumes `IDongMason`, the orbifold transport
lemma, and `IEnumeration`. -/
theorem inCOneList_of_extension (hDM : IDongMason.{w}) (hEn : IEnumeration)
    {𝒱 : Type v} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
    {𝒲 : Type w} [AddCommGroup 𝒲] [Module ℂ 𝒲] {W : VertexOperatorAlgebra 𝒲}
    (G : Subgroup (Aut W)) (hG : Finite G) (hW : Nice W) (hc : W.centralCharge = 1)
    (h1 : finrank ℂ (W.grading 1) ≠ 0) (hV : VOAIsomorphic V (orbifoldVOA G)) :
    InCOneList V := by
  obtain ⟨m, hm, hWm⟩ := hDM 𝒲 W hW hc h1
  obtain ⟨G', ⟨e⟩, hGG'⟩ := orbifold_transport hWm G
  have hG' : Finite G' := Finite.of_equiv _ e.toEquiv
  exact inCOneList_of_iso (hV.trans hGG') (hEn m hm G' hG')

/-- **Gannon–Rayhaun Theorem 3.1 (forward), conditionally.** `#print axioms`-clean,
**conditional on** the seven external inputs of `Inputs.lean` *and* the four named gaps
`GapLemma37`, `GapThetaReduction`, `GapQExpansion`, `GapGaloisBound` (GR-internal or classical
steps not yet formalized; see the module docstring). B1–B4 are all consumed on the way. -/
theorem gannonRayhaun_of_inputs
    (hMod : IModData.{u}) (hCG : ICongruenceGalois.{u}) (hSS : ISerreStark24)
    (hVir : IVirasoro.{u}) (hTan : ITannakian.{u}) (hDM : IDongMason.{u})
    (hEn : IEnumeration)
    (g37 : GapLemma37.{u}) (gRed : GapThetaReduction) (gQ : GapQExpansion)
    (gGal : GapGaloisBound.{u}) :
    GannonRayhaunStatement.{u} := by
  intro 𝒱 _ _ V hV hc
  obtain ⟨D, hD⟩ := hMod 𝒱 V hV
  obtain ⟨N, hN, h24⟩ := ModularData.exists_level (D := D) hc
  have hN0 : N ≠ 0 := hN.1.ne'
  have h8 : 8 ∣ N := (show 8 ∣ 24 by norm_num).trans h24
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  obtain ⟨hΓ, hGal⟩ := hCG 𝒱 V hV D hD N hN
  -- Lemma 3.7 + Serre–Stark + (3.13): the canonical theta decomposition (GR Lemma 3.9)
  have hF := g37 𝒱 V hV hc D hD N hN hΓ
  obtain ⟨s, coef, hs, hfs⟩ := hSS N _ hN.1 h24 hF
  obtain ⟨T, R, a, hT, hred⟩ := gRed N hN.1 s coef hs
  have hdec : ∀ τ : ℂ, 0 < τ.im → ModularForm.eta τ * D.ch D.vac τ =
      ∑ t ∈ T, ∑ j : ZMod (R t), a t j * rankOneTheta (j.val : ℕ) (R t : ℕ) t τ :=
    fun τ hτ => (hfs τ hτ).trans (hred τ hτ)
  have hTsq : ∀ t ∈ T, Squarefree t := fun t ht => (hT t ht).1
  have hTpos : ∀ t ∈ T, 0 < t := fun t ht => Nat.pos_of_ne_zero (hT t ht).1.ne_zero
  have hT4 : ∀ t ∈ T, 4 * t ∣ N := fun t ht =>
    (Dvd.intro ((R t : ℕ) ^ 2) (by ring)).trans (hT t ht).2
  -- Lemma 3.10 (B1)
  have h310 := fun (τ : ℂ) (hτ : 0 < τ.im) => hD.lemma_3_10 hc hN T hTsq (fun t => (R t : ℕ))
    (fun t ht => (hT t ht).2) a hdec hτ
  -- Lemma 3.11 (B4)
  obtain ⟨A, hA0, hAeq⟩ := hVir 𝒱 V hV.1.stronglyFinite.vacuum_ne_zero hc
  have hθ := hD.formal_theta gQ hc T hTpos R a hdec
  have hVirF : PowerSeries.map (Int.castRingHom ℂ) (eulerSeries * vacuumSeries V) =
      PowerSeries.map (Int.castRingHom ℂ) (etaVirasoroSum A) := by rw [hAeq]
  have hw : ∀ t ∈ T, ∃ x : ℝ, 0 ≤ x ∧
      (1 / (((R t : ℕ) : ℂ) * (Real.sqrt (2 * t) : ℂ))) * ∑ j : ZMod (R t), a t j = x :=
    fun t ht => theta_weight_nonneg _ A hA0 hVirF T hTsq (fun t => (R t : ℕ)) a hθ ht
  choose! w hw0 hwC using hw
  -- `Σ_t w_t = S₀₀`
  have hsumC := hD.sum_weights gQ hV hc T hTpos _ h310
  have hsum : ∑ t ∈ T, w t = D.S00 := by
    have : ∑ t ∈ T, (1 / (((R t : ℕ) : ℂ) * (Real.sqrt (2 * t) : ℂ))) *
        ∑ j : ZMod (R t), a t j = ∑ t ∈ T, (w t : ℂ) :=
      Finset.sum_congr rfl fun t ht => hwC t ht
    rw [this] at hsumC
    exact_mod_cast hsumC.symm
  -- Prop 3.12 (B2)
  have hbound : ∀ ℓ : ℕ, ℓ.Coprime N →
      D.S00 ≤ |∑ t ∈ T, (jacobiSym (2 * (t : ℤ)) ℓ : ℝ) * w t| := by
    intro ℓ hℓ
    have h := gGal 𝒱 V hV hc D hD N hN hGal T R a hT hdec ℓ hℓ
    have : ∑ t ∈ T, (jacobiSym (2 * (t : ℤ)) ℓ : ℂ) *
        ((1 / ((R t : ℂ) * (Real.sqrt (2 * t) : ℂ))) * ∑ j : ZMod (R t), a t j) =
        ((∑ t ∈ T, (jacobiSym (2 * (t : ℤ)) ℓ : ℝ) * w t : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun t ht => by rw [hwC t ht]
    rw [this, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  obtain ⟨ts, ⟨htsT, hwts⟩, huniq⟩ := existsUnique_weight_ne_zero hN0 h8 T
    (fun t ht => ⟨hTsq t ht, hT4 t ht⟩) w hw0 hD.S00_pos hsum hbound
  have hother : ∀ t ∈ T, t ≠ ts → w t = 0 := fun t ht hne => by
    by_contra h; exact hne (huniq t ⟨ht, h⟩)
  have hwts' : w ts = D.S00 := by
    rw [← hsum, Finset.sum_eq_single ts (fun t ht hne => hother t ht hne)
      (fun h => absurd htsT h)]
  -- `P_V = θ_{0,1,t⋆}/η` (GR (3.30))
  have hP : ∀ τ : ℂ, 0 < τ.im → ∑ b ∈ D.intLabels, (D.d b : ℂ) * D.ch b τ =
      rankOneTheta 0 1 ts τ / ModularForm.eta τ := by
    intro τ hτ
    have h := h310 τ hτ
    have hs : ∑ t ∈ T, (1 / (((R t : ℕ) : ℂ) * (Real.sqrt (2 * t) : ℂ)) *
        ∑ j : ZMod (R t), a t j) * rankOneTheta 0 1 t τ = (D.S00 : ℂ) * rankOneTheta 0 1 ts τ := by
      rw [Finset.sum_eq_single ts]
      · rw [hwC ts htsT, hwts']
      · intro t ht hne; rw [hwC t ht, hother t ht hne]; simp
      · intro h; exact absurd htsT h
    rw [hs, mul_div_assoc] at h
    have hS0 : (D.S00 : ℂ) ≠ 0 := by exact_mod_cast hD.S00_pos.ne'
    exact mul_left_cancel₀ hS0 h
  -- (3.40) (B1) and Theorem 2.18 (B3)
  have hfact := hD.factorized_of_vacuum_identity hV hc _ fun τ hτ =>
    hD.vacuum_identity hc hN (hTsq ts htsT) (hT4 ts htsT) hP hτ
  -- Proposition 2.13 + 2.17
  obtain ⟨𝒲, _, _, W, G, hWnice, hGfin, hWc, hVW, hdims⟩ := hTan 𝒱 V hV D hD hfact
  -- `W₁ ≠ 0`
  have hp1 := hD.one_le_pCoeff_one gQ hV hc (hTpos ts htsT) hP
  have hW1 : finrank ℂ (W.grading 1) ≠ 0 := by
    have h := hdims 1
    have : (finrank ℂ (W.grading 1) : ℝ) = D.pCoeff 1 := by exact_mod_cast h
    intro h0
    rw [h0, Nat.cast_zero] at this
    linarith
  exact inCOneList_of_extension hDM hEn G hGfin hWnice (hWc.trans hc) hW1 hVW


end VOA.Classification.COne
