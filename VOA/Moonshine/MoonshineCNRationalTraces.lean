/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGammaZeroGalois
import VOA.Moonshine.MoonshineCNGenusZeroMain
import VOA.Moonshine.MoonshineCNTwistedDenominator
import VOA.Moonshine.MoonshineLRGenerationMonster
import VOA.Moonshine.MoonshineLRFinOrderRigid
import VOA.Moonshine.MoonshineLRHecke
import VOA.Moonshine.MoonshineLRNontrivial
import VOA.Moonshine.MoonshineLRCoeffBound
import VOA.Moonshine.MoonshineCNReplicationAnalytic
import VOA.Moonshine.MoonshineCNRationalRamanujan

/-!
# Every graded trace of every automorphism of `V♮` is rational

`RationalTraces` (the statement of `MoonshineCNStatement`): for every `g ∈ Aut V♮` and every `n`,
the coefficient `tr(g | V♮_{n+1})` of the McKay–Thompson series is a rational number. With no
hypotheses.

The proof (`Notes/monster_aut/RATIONALITY.md`, §2.4):
1. **Galois invariance** `T_{g^u} = T_g` for `u` coprime to the order of `g`
   (`mckayThompsonFun_pow_eq_of_coprime_holds`): the existing
   `mckayThompsonFun_pow_eq_of_coprime_of_completelyReplicable`, with its inputs discharged
   unconditionally: finite order (`M8.autVnat_isOfFinOrder`), complete replicability
   (`completelyReplicable_of_simpleRootGeneration M8.monsterLieSimpleRootGeneration`) and the `Γ₁`
   theorem (`conwayNortonGammaOne_of_completelyReplicable` with the prime Hecke identity and
   non-injectivity modulo translations of the replicable families).
2. **Coefficients** (`mckayThompson_eq_of_mckayThompsonFun_eq`): two finite-order McKay–Thompson
   functions that agree on `ℍ` have the same `q`-coefficients. The difference of the regular parts
   is a `J`-dominated power series in `q` vanishing on the punctured disc; Cauchy's estimate
   `M8.norm_coeff_le_of_hasSum_qPar` with bound `0` kills every coefficient.
3. **Ramanujan sums** (`Rationality.exists_rat_trace_of_trace_pow_coprime`): `A = g|_{V♮_{n+1}}`
   has `A^N = 1` and `tr(A^u) = tr(A)` for `u` coprime to `N`, hence `tr A ∈ ℚ`.

## Main results
* `completelyReplicable_holds`, `conwayNortonGammaOne_holds`,
  ⭐ `mckayThompsonFun_pow_eq_of_coprime_holds`.
* ⭐ `mckayThompson_eq_of_mckayThompsonFun_eq`, `mckayThompson_pow_eq_of_coprime`.
* ⭐ `exists_rat_gradedAutTrace`, `exists_rat_gradedAutTrace_two`, ⭐ `rationalTraces`.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane AutMonster

/-! ## Galois invariance, unconditionally -/

/-- **Complete replicability** of every McKay–Thompson series of `V♮`, with no hypotheses. -/
theorem completelyReplicable_holds : CompletelyReplicable :=
  completelyReplicable_of_simpleRootGeneration M8.monsterLieSimpleRootGeneration
    M8.autVnat_isOfFinOrder

/-- **The `Γ₁` form of Conway–Norton**, with no hypotheses. -/
theorem conwayNortonGammaOne_holds : ConwayNortonGammaOne :=
  conwayNortonGammaOne_of_completelyReplicable completelyReplicable_holds
    (fun _ _ k => M8.ReplicableFamily_primeHeckeIdentity _ k)
    (fun _ hg => M8.ReplicableFamily_notInjectiveModTranslations hg.orderOf_pos _)

/-- ⭐ **Galois invariance of McKay–Thompson series**, with no hypotheses: `T_{g^u} = T_g` for every
`g ∈ Aut V♮` and every `u` coprime to the order of `g`. -/
theorem mckayThompsonFun_pow_eq_of_coprime_holds (g : AutVnat) {u : ℕ}
    (hu : Nat.Coprime u (orderOf g)) : mckayThompsonFun (g ^ u) = mckayThompsonFun g :=
  mckayThompsonFun_pow_eq_of_coprime_of_completelyReplicable M8.autVnat_isOfFinOrder
    conwayNortonGammaOne_holds completelyReplicable_holds g hu

/-! ## From functions to coefficients -/

/-- ⭐ **`q`-coefficients are determined by the function**: if two finite-order automorphisms of
`V♮` have the same McKay–Thompson function on `ℍ`, they have the same McKay–Thompson series. -/
theorem mckayThompson_eq_of_mckayThompsonFun_eq {g h : AutVnat} (hg : IsOfFinOrder g)
    (hh : IsOfFinOrder h) (hfun : mckayThompsonFun g = mckayThompsonFun h) :
    mckayThompson g = mckayThompson h := by
  ext n
  have hc : ∀ τ : ℍ, Summable fun r => PowerSeries.coeff r (mckayThompson g) * qPar τ ^ r :=
    fun τ => (summable_norm_coeff_mul_qPar (isJDominated_mckayThompson g hg) τ).of_norm
  have hd : ∀ τ : ℍ, Summable fun r => PowerSeries.coeff r (mckayThompson h) * qPar τ ^ r :=
    fun τ => (summable_norm_coeff_mul_qPar (isJDominated_mckayThompson h hh) τ).of_norm
  have hsum : ∀ τ : ℍ, HasSum (fun r => (PowerSeries.coeff r (mckayThompson g)
      - PowerSeries.coeff r (mckayThompson h)) * qPar τ ^ r) 0 := by
    intro τ
    have h1 := (hc τ).hasSum.sub (hd τ).hasSum
    have h2 : ∑' r, PowerSeries.coeff r (mckayThompson g) * qPar τ ^ r
        = ∑' r, PowerSeries.coeff r (mckayThompson h) * qPar τ ^ r := by
      have := congrFun hfun τ
      simp only [mckayThompsonFun] at this
      exact add_left_cancel this
    rw [h2, sub_self] at h1
    simpa only [sub_mul] using h1
  have hle := M8.norm_coeff_le_of_hasSum_qPar
    (fun r => PowerSeries.coeff r (mckayThompson g) - PowerSeries.coeff r (mckayThompson h))
    (fun _ => 0) 0 hsum (fun _ => by simp) n
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

/-- `T_{g^u} = T_g` as power series, for `u` coprime to the order of `g`. -/
theorem mckayThompson_pow_eq_of_coprime (g : AutVnat) {u : ℕ}
    (hu : Nat.Coprime u (orderOf g)) : mckayThompson (g ^ u) = mckayThompson g :=
  mckayThompson_eq_of_mckayThompsonFun_eq (M8.autVnat_isOfFinOrder g).pow
    (M8.autVnat_isOfFinOrder g) (mckayThompsonFun_pow_eq_of_coprime_holds g hu)

/-! ## Rationality of the traces -/

/-- ⭐ **Every graded trace of every automorphism of `V♮` is rational**:
`tr(g | V♮_{n+1}) ∈ ℚ`. -/
theorem exists_rat_gradedAutTrace (g : AutVnat) (n : ℕ) :
    ∃ r : ℚ, gradedAutTrace VnatVOA g ((n : ℤ) + 1) = r := by
  letI := VnatVOA.finrank ((n : ℤ) + 1)
  have hN : 0 < orderOf g := (M8.autVnat_isOfFinOrder g).orderOf_pos
  have hA : gradedAutAction VnatVOA ((n : ℤ) + 1) g ^ orderOf g = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hgal : ∀ u : ℕ, (orderOf g).Coprime u →
      LinearMap.trace ℂ _ (gradedAutAction VnatVOA ((n : ℤ) + 1) g ^ u)
        = LinearMap.trace ℂ _ (gradedAutAction VnatVOA ((n : ℤ) + 1) g) := by
    intro u hu
    have h := congrArg (PowerSeries.coeff n) (mckayThompson_pow_eq_of_coprime g hu.symm)
    rw [mckayThompson_coeff, mckayThompson_coeff] at h
    rw [← map_pow]
    exact h
  exact Rationality.exists_rat_trace_of_trace_pow_coprime _ hN hA hgal

/-- **Weight-two traces are rational**: `tr(g | V♮₂) ∈ ℚ` for every `g ∈ Aut V♮`. -/
theorem exists_rat_gradedAutTrace_two (g : AutVnat) :
    ∃ r : ℚ, gradedAutTrace VnatVOA g 2 = r := by
  obtain ⟨r, hr⟩ := exists_rat_gradedAutTrace g 1
  have h2 : ((1 : ℕ) : ℤ) + 1 = 2 := by norm_num
  rw [h2] at hr
  exact ⟨r, hr⟩

/-- ⭐ **`RationalTraces`**, with no hypotheses: every coefficient of every McKay–Thompson series
of `V♮` is a rational number. -/
theorem rationalTraces : RationalTraces := fun g n => by
  obtain ⟨r, hr⟩ := exists_rat_gradedAutTrace g n
  exact ⟨r, by rw [mckayThompson_coeff, hr]⟩

end VOA.Moonshine.ConwayNorton
