/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesModelCharBlocksG

/-!
# Feigin–Stoyanovsky generating functions at coloured points

For a symmetric `F(x_1, …, x_s)` and a map `ρ : Fin s → Fin K` whose fibres have sizes `c_b`,

  `ψ_F ( Π_b [t_b^{a_b}] T(t_b)^{c_b} ) = [t^a] F(t_{ρ(1)}, …, t_{ρ(s)})`        (`ψF_tpow`)

— the generating function of `ψ_F` on a product of powers of `T` at `K` points is `F` with its
variables collided according to `ρ`.  The proof runs through multivariate power series:
`Π_v T(x_v)` renamed along `ρ` is `Π_b T(t_b)^{c_b}`, and coefficientwise application of `ψ_F`
commutes with renaming.

Consequently (`ψF_jet_eq_zero`): **if every collision of `n` variables kills `F`, then `ψ_F`
kills the jet ideal of `Tⁿ`**, and `ψ_F` descends to `R_n` (`ψbarG`).

Everything is proved outright.
-/

namespace VOA.TwoSeries.ModelChar

open MvPolynomial VOA.SymbolModel VOA.TwoSeries.StrictModel VOA.JetProduct
open scoped BigOperators

noncomputable section

/-! ### Univariate series placed in one variable -/

variable {A : Type} [CommRing A]

/-- A univariate series in the variable `b`. -/
def embS {K : ℕ} (b : Fin K) (φ : PowerSeries A) : MvPowerSeries (Fin K) A :=
  MvPowerSeries.rename (fun _ : Unit => b) (φ : MvPowerSeries Unit A)

theorem coeff_embS_single {K : ℕ} (b : Fin K) (φ : PowerSeries A) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single b n) (embS b φ) = PowerSeries.coeff n φ := by
  have h := MvPowerSeries.coeff_embDomain_rename (R := A) ⟨fun _ : Unit => b, fun _ _ _ => rfl⟩
    (φ : MvPowerSeries Unit A) (Finsupp.single () n)
  rw [Finsupp.embDomain_single] at h
  exact h

theorem coeff_embS_eq_zero {K : ℕ} (b : Fin K) (φ : PowerSeries A) (x : Fin K →₀ ℕ)
    (hx : x ≠ Finsupp.single b (x b)) : MvPowerSeries.coeff x (embS b φ) = 0 := by
  apply MvPowerSeries.coeff_rename_eq_zero
  rintro ⟨y, rfl⟩
  apply hx
  rw [Finsupp.unique_single y, Finsupp.mapDomain_single]
  simp

theorem embS_pow {K : ℕ} (b : Fin K) (φ : PowerSeries A) (c : ℕ) :
    embS b φ ^ c = embS b (φ ^ c) := by
  rw [embS, embS, ← map_pow]

/-- The coefficient of a product of series in separate variables. -/
theorem coeff_prod_sep {K : ℕ} (f : Fin K → MvPowerSeries (Fin K) A)
    (hf : ∀ v (x : Fin K →₀ ℕ), x ≠ Finsupp.single v (x v) → MvPowerSeries.coeff x (f v) = 0)
    (e : Fin K →₀ ℕ) :
    MvPowerSeries.coeff e (∏ v, f v) = ∏ v, MvPowerSeries.coeff (Finsupp.single v (e v)) (f v) := by
  classical
  rw [MvPowerSeries.coeff_prod]
  let l0 : Fin K →₀ (Fin K →₀ ℕ) := Finsupp.equivFunOnFinite.symm fun v => Finsupp.single v (e v)
  rw [Finset.sum_eq_single l0]
  · rfl
  · intro l hl hne
    rw [Finset.mem_finsuppAntidiag] at hl
    by_contra hprod
    apply hne
    have hall : ∀ v, l v = Finsupp.single v (l v v) := by
      intro v
      by_contra hv
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ v) (hf v _ hv))
    have hsum : ∀ w, e w = l w w := by
      intro w
      rw [← hl.1, Finset.sum_apply']
      rw [Finset.sum_eq_single w]
      · intro v _ hvw
        rw [hall v, Finsupp.single_apply, if_neg hvw]
      · intro h; exact absurd (Finset.mem_univ w) h
    ext v : 1
    rw [hall v, ← hsum v]
    rfl
  · intro h
    exfalso; apply h
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    exact Finsupp.univ_sum_single e

/-! ### The generating function at coloured points -/

/-- `Π_v T(x_v)` as a power series in `x_1, …, x_s`. -/
def tProd (s : ℕ) : MvPowerSeries (Fin s) TPoly := ∏ v, embS v tSer

theorem coeff_tProd (s : ℕ) (x : Fin s →₀ ℕ) :
    MvPowerSeries.coeff x (tProd s) = ∏ v, (X (x v) : TPoly) := by
  rw [tProd, coeff_prod_sep _ (fun v x hx => coeff_embS_eq_zero v _ x hx)]
  apply Finset.prod_congr rfl
  intro v _
  rw [coeff_embS_single, tSer, PowerSeries.coeff_mk]

theorem rename_embS {K K' : ℕ} (ρ : Fin K → Fin K') (b : Fin K) (φ : PowerSeries A) :
    MvPowerSeries.rename ρ (embS b φ) = embS (ρ b) φ := by
  rw [embS, embS, MvPowerSeries.rename_rename]
  rfl

theorem rename_tProd {s K : ℕ} (ρ : Fin s → Fin K) (c : Fin K → ℕ)
    (hρ : ∀ b, (Finset.univ.filter fun v => ρ v = b).card = c b) :
    MvPowerSeries.rename ρ (tProd s) = ∏ b, embS b (tSer ^ c b) := by
  rw [tProd, map_prod]
  simp_rw [rename_embS]
  rw [← Finset.prod_fiberwise' Finset.univ ρ (fun b => embS b tSer)]
  apply Finset.prod_congr rfl
  intro b _
  rw [Finset.prod_const, hρ, embS_pow]

theorem coeff_prod_embS_pow {K : ℕ} (c a : Fin K → ℕ) :
    MvPowerSeries.coeff (toF a) (∏ b, embS b (tSer ^ c b) : MvPowerSeries (Fin K) TPoly) =
      ∏ b, PowerSeries.coeff (a b) (tSer ^ c b) := by
  rw [coeff_prod_sep _ (fun v x hx => coeff_embS_eq_zero v _ x hx)]
  apply Finset.prod_congr rfl
  intro b _
  rw [toF_apply, coeff_embS_single]

theorem ψF_coeff_rename {s K : ℕ} {F : MvPolynomial (Fin s) ℂ} (hF : Symm F)
    (ρ : Fin s → Fin K) (e : Fin K →₀ ℕ) :
    ψF F (MvPowerSeries.coeff e (MvPowerSeries.rename ρ (tProd s))) =
      MvPolynomial.coeff e (rename ρ F) := by
  rw [← MvPolynomial.coeff_coe, ← MvPowerSeries.rename_coe, MvPowerSeries.coeff_rename,
    MvPowerSeries.coeff_rename, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [coeff_tProd, ψF_prod_X hF, toF_coe, MvPolynomial.coeff_coe]

/-- **The FS generating function at coloured points**:
`ψ_F (Π_b [t_b^{a_b}] T(t_b)^{c_b}) = [t^a] F(t_ρ)` when the fibres of `ρ` have sizes `c`. -/
theorem ψF_tpow {s K : ℕ} {F : MvPolynomial (Fin s) ℂ} (hF : Symm F) (ρ : Fin s → Fin K)
    (c : Fin K → ℕ) (hρ : ∀ b, (Finset.univ.filter fun v => ρ v = b).card = c b)
    (a : Fin K → ℕ) :
    ψF F (∏ b, PowerSeries.coeff (a b) (tSer ^ c b)) = coeff (toF a) (rename ρ F) := by
  rw [← coeff_prod_embS_pow, ← rename_tProd ρ c hρ, ψF_coeff_rename hF]

/-! ### The jet ideal of `Tⁿ` -/

theorem tSer_pow_isHomogeneous : ∀ (c b : ℕ),
    (PowerSeries.coeff b (tSer ^ c) : TPoly).IsHomogeneous c
  | 0, b => by
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact isHomogeneous_one _ _
    · exact isHomogeneous_zero _ _ _
  | c + 1, b => by
    rw [pow_succ, PowerSeries.coeff_mul]
    refine IsHomogeneous.sum _ _ _ fun p _ => (tSer_pow_isHomogeneous c p.1).mul ?_
    simp only [tSer, PowerSeries.coeff_mk]
    exact isHomogeneous_X _ _

theorem ψF_eq_zero_of_isHomogeneous {s : ℕ} (F : MvPolynomial (Fin s) ℂ) {p : TPoly} {d : ℕ}
    (hp : p.IsHomogeneous d) (hd : d ≠ s) : ψF F p = 0 := by
  rw [ψF_apply]
  refine Finset.sum_eq_zero fun e he => ?_
  have h := hp (mem_support_iff.mp he)
  rw [cF_eq_zero, mul_zero]
  rw [Finsupp.degree_eq_weight_one]
  simpa using fun h' => hd (h.symm.trans (by simpa using h'))

/-- The collision map: the first `n` variables to `0`, the rest to `1, …, s'`. -/
def collide (n s' : ℕ) : Fin (n + s') → Fin (s' + 1) :=
  Fin.append (fun _ : Fin n => (0 : Fin (s' + 1))) Fin.succ

theorem card_collide (n s' : ℕ) (b : Fin (s' + 1)) :
    (Finset.univ.filter fun v => collide n s' v = b).card =
      (Fin.cons n (fun _ : Fin s' => 1) : Fin (s' + 1) → ℕ) b := by
  classical
  refine Fin.cases ?_ (fun w => ?_) b
  · simp only [Fin.cons_zero]
    rw [show (Finset.univ.filter fun v => collide n s' v = 0) =
        (Finset.univ : Finset (Fin n)).map (Fin.castAddEmb s') from ?_]
    · simp
    · ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      refine Fin.addCases (fun i => ?_) (fun j => ?_) v
      · simp [collide, Fin.append_left]
      · simp [collide, Fin.append_right, Fin.succ_ne_zero]
        intro i h
        exact absurd (congrArg Fin.val h) (by simp; omega)
  · simp only [Fin.cons_succ]
    rw [Finset.card_eq_one]
    refine ⟨Fin.natAdd n w, ?_⟩
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine Fin.addCases (fun i => ?_) (fun j => ?_) v
    · simp [collide, Fin.append_left, (Fin.succ_ne_zero w).symm]
      intro h
      exact absurd (congrArg Fin.val h) (by simp; omega)
    · simp [collide, Fin.append_right, Fin.succ_inj]

/-- **The kernel property for `Tⁿ`**: if every collision of `n` variables kills `F`, then
`ψ_F` kills `coeff_m(T(z)ⁿ) · p`. -/
theorem ψF_jet_mul_eq_zero' {n s : ℕ} {F : MvPolynomial (Fin s) ℂ} (hF : Symm F)
    (hcoll : ∀ (K : ℕ) (ρ : Fin s → Fin K) (b : Fin K),
      n ≤ (Finset.univ.filter fun v => ρ v = b).card → rename ρ F = 0)
    (m : ℕ) (p : TPoly) : ψF F (PowerSeries.coeff m (tSer ^ n) * p) = 0 := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  by_cases he : e.degree + n = s
  · set d := e.degree with hd
    obtain ⟨j, hj⟩ := exists_monoOf d e hd.symm
    have hs : s = n + d := by omega
    let ρ : Fin s → Fin (d + 1) := collide n d ∘ finCongr hs
    have hρ : ∀ b, (Finset.univ.filter fun v => ρ v = b).card =
        (Fin.cons n (fun _ : Fin d => 1) : Fin (d + 1) → ℕ) b := by
      intro b
      rw [← card_collide n d b]
      apply Finset.card_bij (fun v _ => finCongr hs v)
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        exact hv
      · intro v _ w _ h; exact (finCongr hs).injective h
      · intro w hw
        refine ⟨(finCongr hs).symm w, ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        simpa [ρ] using hw
    have hprod : PowerSeries.coeff m (tSer ^ n) * monomial e (coeff e p) = coeff e p •
        ∏ b, PowerSeries.coeff ((Fin.cons m j : Fin (d + 1) → ℕ) b)
          (tSer ^ (Fin.cons n (fun _ : Fin d => 1) : Fin (d + 1) → ℕ) b) := by
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, pow_one]
      have hX : ∏ w : Fin d, PowerSeries.coeff (j w) (tSer : PowerSeries TPoly) =
          monomial e 1 := by
        rw [← hj, ← prod_X_eq_monomial]
        apply Finset.prod_congr rfl
        intro w _
        rw [tSer, PowerSeries.coeff_mk]
      rw [hX, smul_eq_C_mul, ← mul_assoc, mul_comm (MvPolynomial.C _), mul_assoc,
        C_mul_monomial, mul_one]
    rw [hprod, map_smul, ψF_tpow hF ρ _ hρ, hcoll (d + 1) ρ 0 (by rw [hρ 0]; simp), coeff_zero,
      smul_zero]
  · apply ψF_eq_zero_of_isHomogeneous F _ (d := n + e.degree) (by omega)
    exact (tSer_pow_isHomogeneous n m).mul (isHomogeneous_monomial _ rfl)

/-- Collisions of `n` variables kill `F`. -/
def CollKill (n : ℕ) {s : ℕ} (F : MvPolynomial (Fin s) ℂ) : Prop :=
  ∀ (K : ℕ) (ρ : Fin s → Fin K) (b : Fin K),
    n ≤ (Finset.univ.filter fun v => ρ v = b).card → rename ρ F = 0

theorem ψF_jetIdeal_n {n s : ℕ} {F : MvPolynomial (Fin s) ℂ} (hF : Symm F) (hk : CollKill n F)
    {x : TPoly} (hx : x ∈ jetIdealT n) : ψF F x = 0 := by
  have key : ∀ y, ψF F (y * x) = 0 := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨m, rfl⟩ y
      rw [mul_comm]
      exact ψF_jet_mul_eq_zero' hF hk m y
    · intro y; rw [mul_zero, map_zero]
    · intro a b _ _ ha hb y; rw [mul_add, map_add, ha, hb, add_zero]
    · intro a b _ hb y; rw [smul_eq_mul, ← mul_assoc]; exact hb _
  simpa using key 1

/-- The descended functional `ψ_F : R_n → ℂ` for `F` killed by `n`-collisions. -/
def ψbarG (n : ℕ) {s : ℕ} (F : MvPolynomial (Fin s) ℂ) (hF : Symm F) (hk : CollKill n F) :
    Rn n →ₗ[ℂ] ℂ :=
  (Submodule.liftQ ((jetIdealT n).restrictScalars ℂ) (ψF F) (fun _ hx =>
    LinearMap.mem_ker.mpr (ψF_jetIdeal_n hF hk hx))) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv ℂ (jetIdealT n)).symm.toLinearMap

theorem ψbarG_comp_mk (n : ℕ) {s : ℕ} (F : MvPolynomial (Fin s) ℂ) (hF : Symm F)
    (hk : CollKill n F) :
    ψbarG n F hF hk ∘ₗ (Ideal.Quotient.mkₐ ℂ (jetIdealT n)).toLinearMap = ψF F :=
  LinearMap.ext fun _ => rfl

end

end VOA.TwoSeries.ModelChar
