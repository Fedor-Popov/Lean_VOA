/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.Periodic
import Mathlib.GroupTheory.Commensurable
import VOA.Moonshine.MoonshineCNTraceBounds
import VOA.Moonshine.JAnalyticQExpansion

/-!
# The Conway–Norton conjecture (statement)

For every automorphism `g` of the moonshine module `V♮` (the Monster, node M1), the McKay–Thompson series
`T_g(τ) = q⁻¹ + Σ_{n ≥ 1} tr(g | V♮_{n+1}) qⁿ` is the normalised Hauptmodul of a group `Γ_g ≤ SL(2,ℝ)`
which contains `Γ₀(N)` for some `N` and is commensurable with `SL(2,ℤ)`.

"Normalised Hauptmodul" is stated without Riemann surfaces: `f` is holomorphic on `ℍ`, `Γ`-invariant,
`f = q⁻¹ + O(q)` at `∞`, finite at every other cusp, and the induced map
`X(Γ) = Γ\ℍ ⊔ Γ\{cusps} → ℙ¹(ℂ)` (the class of `∞` going to `∞`) is a bijection. That bijection is
holomorphic, so `X(Γ) ≅ ℙ¹`: this is the genus-zero property.

The full statement and its identity specialization; no genus-zero conclusion is assumed.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology CongruenceSubgroup AutMonster
open scoped MatrixGroups Manifold

/-- The cusp `∞ ∈ ℙ¹(ℝ)`. -/
abbrev cuspInfty : OnePoint ℝ := OnePoint.infty

/-- `q = e^{2πiτ}`. -/
noncomputable def qPar (τ : ℍ) : ℂ := Function.Periodic.qParam 1 (τ : ℂ)

/-- The McKay–Thompson series as a function on `ℍ`:
`T_g(τ) = q⁻¹ + Σ_{n ≥ 0} tr(g | V♮_{n+1}) qⁿ` (the `n = 0` coefficient is `tr(g | V♮₁) = 0`). -/
noncomputable def mckayThompsonFun (g : AutVnat) (τ : ℍ) : ℂ :=
  (qPar τ)⁻¹ + ∑' n : ℕ, PowerSeries.coeff n (mckayThompson g) * qPar τ ^ n

/-- `γ` has positive determinant and sends `∞` to `c`. -/
def SendsInftyTo (γ : GL (Fin 2) ℝ) (c : OnePoint ℝ) : Prop :=
  0 < (γ.det : ℝ) ∧ γ • cuspInfty = c

/-- `f` tends to `w` at the cusp `c`, uniformly on horoball neighbourhoods of `c`. -/
def HasCuspValue (f : ℍ → ℂ) (c : OnePoint ℝ) (w : ℂ) : Prop :=
  ∀ γ : GL (Fin 2) ℝ, SendsInftyTo γ c → Tendsto (fun τ : ℍ => f (γ • τ)) atImInfty (𝓝 w)

/-- `c` is a cusp of `Γ` that is not `Γ`-equivalent to `∞`. -/
def IsOtherCusp (Γ : Subgroup (GL (Fin 2) ℝ)) (c : OnePoint ℝ) : Prop :=
  IsCusp c Γ ∧ ∀ γ ∈ Γ, γ • cuspInfty ≠ c

/-- **Normalised Hauptmodul of a genus-zero group.**
`holomorphic`–`cuspFinite`: `f` is a modular function for `Γ` with a simple pole at `∞`, normalised as
`q⁻¹ + 0 + O(q)`, and finite at every other cusp.
`injective`–`surjective`: the induced map `X(Γ) → ℙ¹(ℂ)` is a bijection. -/
structure IsNormalizedHauptmodul (Γ : Subgroup (GL (Fin 2) ℝ)) (f : ℍ → ℂ) : Prop where
  holomorphic : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f
  invariant : ∀ γ ∈ Γ, ∀ τ : ℍ, f (γ • τ) = f τ
  normalized : Tendsto (fun τ : ℍ => f τ - (qPar τ)⁻¹) atImInfty (𝓝 0)
  cuspFinite : ∀ c, IsOtherCusp Γ c → ∃ w, HasCuspValue f c w
  injective : ∀ τ σ : ℍ, f τ = f σ → ∃ γ ∈ Γ, γ • τ = σ
  cuspValue_not_attained :
    ∀ c w, IsOtherCusp Γ c → HasCuspValue f c w → ∀ τ : ℍ, f τ ≠ w
  cuspValue_injective : ∀ c c' w, IsOtherCusp Γ c → IsOtherCusp Γ c' →
    HasCuspValue f c w → HasCuspValue f c' w → ∃ γ ∈ Γ, γ • c = c'
  surjective : ∀ w : ℂ, (∃ τ : ℍ, f τ = w) ∨ ∃ c, IsOtherCusp Γ c ∧ HasCuspValue f c w

/-- A genus-zero group (with a width-one cusp at `∞`): one that carries a normalised Hauptmodul. -/
def IsGenusZero (Γ : Subgroup (GL (Fin 2) ℝ)) : Prop :=
  ∃ f : ℍ → ℂ, IsNormalizedHauptmodul Γ f

/-- `Γ₀(N)` and `Γ₁(N)` inside `GL(2,ℝ)`. -/
abbrev gamma0GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) := ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
abbrev gamma1GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) := ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

/-- A moonshine-type group: in `SL(2,ℝ)`, containing `Γ₀(N)`, commensurable with `SL(2,ℤ)`. -/
def IsMoonshineGroup (Γ : Subgroup (GL (Fin 2) ℝ)) (N : ℕ) : Prop :=
  0 < N ∧ Γ.HasDetOne ∧ gamma0GL N ≤ Γ ∧ Subgroup.Commensurable Γ 𝒮ℒ

/-- The Conway–Norton property of one automorphism. -/
def ConwayNortonFor (g : AutVnat) : Prop :=
  ∃ (Γ : Subgroup (GL (Fin 2) ℝ)) (N : ℕ), IsMoonshineGroup Γ N ∧
    IsNormalizedHauptmodul Γ (mckayThompsonFun g)

/-- **The Conway–Norton (Monstrous Moonshine) conjecture**, for `Aut V♮`. With M1
(`AutVnat ≃* 𝕄`) this is the conjecture for every element of the Monster. -/
def ConwayNortonConjecture : Prop :=
  ∀ g : AutVnat, ConwayNortonFor g

/-- The same statement for any group mapped into `Aut V♮` (e.g. the Monster via M1). -/
def ConwayNortonVia {𝕄 : Type*} [Group 𝕄] (ι : 𝕄 →* AutVnat) : Prop :=
  ∀ g : 𝕄, ConwayNortonFor (ι g)

/-- The variant with `Γ₁(N)`; the case-free route proves it without rationality of traces. -/
def ConwayNortonGammaOne : Prop :=
  ∀ g : AutVnat, IsOfFinOrder g → ∃ (Γ : Subgroup (GL (Fin 2) ℝ)) (N : ℕ),
    0 < N ∧ Γ.HasDetOne ∧ gamma1GL N ≤ Γ ∧ Subgroup.Commensurable Γ 𝒮ℒ ∧
      IsNormalizedHauptmodul Γ (mckayThompsonFun g)


/-- `Im((aτ+b)/d) = a·Im τ/d > 0`. -/
theorem heckePoint_im_pos (a d b : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    0 < ((a * (τ : ℂ) + b) / d).im := by
  have hτ := τ.im_pos
  have h : ((a * (τ : ℂ) + b) / d).im = a * τ.im / d := by
    simp [Complex.div_natCast_im, Complex.mul_im]
  rw [h]
  positivity

/-- The Hecke point `(aτ+b)/d`. -/
noncomputable def heckePoint (a d : ℕ) (b : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) : ℍ :=
  ⟨(a * (τ : ℂ) + b) / d, heckePoint_im_pos a d b ha hd τ⟩

/-- **Complete replicability** (output of M7, input of M8): for every `g` and `m ≥ 1` some monic
polynomial of degree `m` evaluated at `T_g` equals the replicate Hecke sum. (That polynomial is then the
Faber polynomial.) -/
def CompletelyReplicable : Prop :=
  ∀ (g : AutVnat) (m : ℕ) (hm : 0 < m), ∃ P : Polynomial ℂ, P.Monic ∧ P.natDegree = m ∧
    ∀ τ : ℍ, P.eval (mckayThompsonFun g τ) =
      ∑ a ∈ m.divisors.attach, ∑ b ∈ Finset.range (m / a),
        mckayThompsonFun (g ^ (a : ℕ)) (heckePoint a (m / a) b (Nat.pos_of_mem_divisors a.2)
          (Nat.div_pos (Nat.divisor_le a.2) (Nat.pos_of_mem_divisors a.2)) τ)

/-- Rationality of all traces (the M1-side input that upgrades `Γ₁` to `Γ₀`). -/
def RationalTraces : Prop :=
  ∀ (g : AutVnat) (n : ℕ), ∃ r : ℚ, PowerSeries.coeff n (mckayThompson g) = r

/-- The function `q⁻¹ + Σ_{n ≥ 1} c n · qⁿ` on `ℍ` (the value `c 0` is ignored). -/
noncomputable def qSeriesFun (c : ℕ → ℂ) (τ : ℍ) : ℂ :=
  (qPar τ)⁻¹ + ∑' n : ℕ, c (n + 1) * qPar τ ^ (n + 1)

/-- A completely replicable family of period `N`: coefficient sequences `c k n` (`n ≥ 1`) for `k : ℕ`
(the replicate `g^k`), periodic in `k`, dominated by `J`, with `c 0 = J`, and satisfying the replication
formula with replicate `k * a` in the `a`-th Hecke block. -/
structure ReplicableFamily (N : ℕ) where
  c : ℕ → ℕ → ℂ
  periodic : ∀ k n, c (k + N) n = c k n
  dominated : ∀ k n, ‖c k n‖ ≤ ‖c 0 n‖
  zero_eq_J : ∀ n, c 0 n = PowerSeries.coeff (n + 1) JShift
  replicable : ∀ (k m : ℕ) (hm : 0 < m), ∃ P : Polynomial ℂ, P.Monic ∧ P.natDegree = m ∧
    ∀ τ : ℍ, P.eval (qSeriesFun (c k) τ) =
      ∑ a ∈ m.divisors.attach, ∑ b ∈ Finset.range (m / a),
        qSeriesFun (c (k * a)) (heckePoint a (m / a) b (Nat.pos_of_mem_divisors a.2)
          (Nat.div_pos (Nat.divisor_le a.2) (Nat.pos_of_mem_divisors a.2)) τ)

/-- The identity McKay–Thompson function is the analytic normalized `j`-invariant. -/
theorem mckayThompsonFun_one :
    mckayThompsonFun 1 = fun τ => jInvariant τ - 744 := by
  funext τ
  simp only [mckayThompsonFun, mckayThompson_one, PowerSeries.coeff_mk]
  rw [show (∑' n : ℕ, PowerSeries.coeff (n + 1) JShift * qPar τ ^ n) =
    jInvariant τ - 744 - (qPar τ)⁻¹ from (hasSum_JShift_laurent τ).tsum_eq]
  ring

/-- Removing the vanishing constant coefficient gives the abstract family convention. -/
theorem mckayThompsonFun_eq_qSeriesFun (g : AutVnat) :
    mckayThompsonFun g = qSeriesFun (fun n => PowerSeries.coeff n (mckayThompson g)) := by
  funext τ
  unfold mckayThompsonFun qSeriesFun
  congr 1
  by_cases hs : Summable (fun n : ℕ => PowerSeries.coeff n (mckayThompson g) * qPar τ ^ n)
  · simpa only [mckayThompson_coeff_zero, zero_mul, zero_add] using hs.tsum_eq_zero_add
  · have ht : ¬ Summable (fun n : ℕ =>
        PowerSeries.coeff (n + 1) (mckayThompson g) * qPar τ ^ (n + 1)) :=
      mt (summable_nat_add_iff (f := fun n : ℕ =>
        PowerSeries.coeff n (mckayThompson g) * qPar τ ^ n) 1).mp hs
    rw [tsum_eq_zero_of_not_summable hs, tsum_eq_zero_of_not_summable ht]

/-- The power family of a finite-order automorphism supplies the abstract M8 interface,
conditional only on complete replicability and finite order of this automorphism. -/
noncomputable def mckayThompsonReplicableFamily (hrep : CompletelyReplicable)
    (g : AutVnat) (hg : IsOfFinOrder g) : ReplicableFamily (orderOf g) where
  c k n := PowerSeries.coeff n (mckayThompson (g ^ k))
  periodic k n := by rw [pow_add, pow_orderOf_eq_one, mul_one]
  dominated k n := by
    simpa only [pow_zero] using mckayThompson_coeff_norm_le (g ^ k) hg.pow n
  zero_eq_J n := by simp only [pow_zero, mckayThompson_one, PowerSeries.coeff_mk]
  replicable k m hm := by
    simpa only [← mckayThompsonFun_eq_qSeriesFun, ← pow_mul] using hrep (g ^ k) m hm

/-- Existence with the positive period and the actual coefficient family made explicit. -/
theorem mckayThompson_replicableFamily_exists (hrep : CompletelyReplicable)
    (g : AutVnat) (hg : IsOfFinOrder g) :
    0 < orderOf g ∧ ∃ F : ReplicableFamily (orderOf g),
      ∀ k n, F.c k n = PowerSeries.coeff n (mckayThompson (g ^ k)) :=
  ⟨hg.orderOf_pos, mckayThompsonReplicableFamily hrep g hg, fun _ _ => rfl⟩

end VOA.Moonshine.ConwayNorton
