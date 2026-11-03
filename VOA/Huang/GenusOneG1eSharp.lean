import VOA.Huang.GenusOneG1eLaurent
import VOA.Huang.GenusOneG1eVacuum
import VOA.Huang.GenusOneIntCoordTransport

/-!
# `InnerBracketSharp` from the algebraic substitution identity alone

Step (5f) of the proof of (G1).

The sharp bracket expansion `InnerBracketSharp D Q Y_in` (which gives (N1) and (N3)) follows from
the proved Laurent expansion `pair_laurent` and the purely ALGEBRAIC, formal identity
`IntCoord.NormalizedIntertwinerSubstitution Y_in` (Huang, math/0303049, Prop. 1.2: the explicit
formal bracket modes equal the exponentially transported modes), through `transportedModes_weight`
(`L[0]`-weight of a transported mode). No convergence estimate is
assumed: the absolute convergence is proved here (no square-trace-mass bound).

* `sum_laurent` — the expansion for a finite family of homogeneous components;
* `innerBracketSharp_of_substitution`;
* `IntertwinerSubstitutionInput` — the substitution identity for intertwiners among irreducible
  lowest-weight modules of a nice VOA (TRUE: Huang 2005; formal algebra, no analysis);
* `channelBracketSharpInput_of_substitution`,
  `fusionEigenInput_of_substitution : IntertwinerSubstitutionInput → ConjugationInputAll →
  ChannelIndependenceInput → FusionEigenInput`.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1e

open VOA VOA.Huang Complex VOA.Huang.GenusOneG1d VOA.Huang.VerlindeFusion
  VOA.Classification.COne VOA.Huang.ZhuModData
open VOA.Huang.GenusOne (sqL traceFunction)
open VOA.Huang.GenusOne.IntCoord (bracketModes NormalizedIntertwinerSubstitution
  transportedModes_weight)
open VOA.Huang.GenusOneG1c (iterF)
open scoped BigOperators

universe u w

section Sum

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- The expansion of a finite family of homogeneous components, aligned on the nonzero ones. -/
theorem sum_laurent (hV : StronglyRational W) (i₁ : P₁.IsIrreducibleLW)
    (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) {m n : ℕ}
    (wa : Fin m → P₁.carrier) (αa : Fin m → ℂ) (hwa : ∀ i, wa i ∈ P₁.isMod.weight (αa i))
    (wb : Fin n → P₂.carrier) (αb : Fin n → ℂ) (hwb : ∀ j, wb j ∈ P₂.isMod.weight (αb j))
    (κ' : ℂ) (N0 : ℕ)
    (hal : ∀ i j, wa i ≠ 0 → wb j ≠ 0 → ∃ D : ℕ, κ' - αa i - αb j + N0 = D)
    (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re →
      HasSum (fun s : ℕ => exp ((Q.h - κ' - N0) * log u) * u ^ s *
          traceFunction Y₃ N.h (bracketModes Y₄ (κ' - 1 - Q.h - ((s : ℂ) - N0))
            (∑ i, wa i) (∑ j, wb j)) τ)
        (∑ i, ∑ j, exp (αa i * u) * iterF Y₃ Y₄ (wa i) (wb j) (αa i) (αb j) τ (exp u - 1)) := by
  have hpair : ∀ p : Fin m × Fin n, ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re →
      HasSum (fun s : ℕ => exp ((Q.h - κ' - N0) * log u) * u ^ s *
          traceFunction Y₃ N.h (bracketModes Y₄ (κ' - 1 - Q.h - ((s : ℂ) - N0))
            (wa p.1) (wb p.2)) τ)
        (exp (αa p.1 * u) * iterF Y₃ Y₄ (wa p.1) (wb p.2) (αa p.1) (αb p.2) τ (exp u - 1)) := by
    rintro ⟨i, j⟩
    by_cases h0 : wa i = 0 ∨ wb j = 0
    · refine ⟨1, one_pos, fun u _ _ => ?_⟩
      have hl : exp (αa i * u) * iterF Y₃ Y₄ (wa i) (wb j) (αa i) (αb j) τ (exp u - 1) = 0 := by
        rcases h0 with h | h
        · rw [h, iterF_zero_left Y₃ Y₄ (hwb j), mul_zero]
        · rw [h, iterF_zero_right Y₃ Y₄ (hwa i), mul_zero]
      have hr : ∀ s : ℕ, exp ((Q.h - κ' - N0) * log u) * u ^ s *
          traceFunction Y₃ N.h (bracketModes Y₄ (κ' - 1 - Q.h - ((s : ℂ) - N0))
            (wa i) (wb j)) τ = 0 := by
        intro s
        rcases h0 with h | h
        · rw [h, map_zero, LinearMap.zero_apply, traceFunction_zero, mul_zero]
        · rw [h, map_zero, traceFunction_zero, mul_zero]
      simp only [hl, hr]
      exact hasSum_zero
    · push Not at h0
      obtain ⟨D, hD⟩ := hal i j h0.1 h0.2
      obtain ⟨δ, hδ, h⟩ := pair_laurent hV i₁ i₂ iN iQ Y₃ Y₄ (hwa i) (hwb j) κ' N0 D hD τ
      exact ⟨δ, hδ, fun u hu hre => (h u hu hre).1⟩
  choose δp hδp hp using hpair
  obtain ⟨δ, hδ, hle⟩ := exists_pos_le_fintype δp hδp
  refine ⟨δ, hδ, fun u hu hre => ?_⟩
  have hall : ∀ p : Fin m × Fin n, HasSum _ _ := fun p =>
    hp p u (lt_of_lt_of_le hu (hle p)) hre
  have hs := hasSum_sum (s := Finset.univ) (fun p _ => hall p)
  rw [← Finset.univ_product_univ, Finset.sum_product] at hs
  refine hs.congr_fun fun s => ?_
  rw [Finset.sum_product]
  have hlin : traceFunction Y₃ N.h (bracketModes Y₄ (κ' - 1 - Q.h - ((s : ℂ) - N0))
      (∑ i, wa i) (∑ j, wb j)) τ = ∑ i, ∑ j, traceFunction Y₃ N.h
        (bracketModes Y₄ (κ' - 1 - Q.h - ((s : ℂ) - N0)) (wa i) (wb j)) τ := by
    rw [← tfLin_apply hV.c2Cofinite iQ Y₃ (LWModule.hasConformalWeight N) τ]
    simp only [map_sum, LinearMap.coe_sum, Finset.sum_apply, tfLin_apply]
    exact Finset.sum_comm
  rw [hlin, Finset.mul_sum]
  simp only [Finset.mul_sum]

end Sum

section Main

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- **The sharp bracket expansion from the algebraic substitution identity.** -/
theorem innerBracketSharp_of_substitution (hV : StronglyRational W) (D : VOA.ModularData W ι)
    {a b : ι} (Q : LWModule W) (iQ : Q.IsIrreducibleLW)
    (Yin : IntertwiningOperator (lwOf D a).isMod (lwOf D b).isMod Q.isMod)
    (hsub : NormalizedIntertwinerSubstitution Yin) : InnerBracketSharp D Q Yin := by
  classical
  intro ins
  have hpa : ∀ i, ∃ p : ℕ, ins.wa i ≠ 0 → ins.αa i = D.h a + p := by
    intro i
    by_cases h : ins.wa i = 0
    · exact ⟨0, fun h' => absurd h h'⟩
    · have hb : (lwOf D a).isMod.weight (ins.αa i) ≠ ⊥ := fun hb => h (by
        have := ins.hwa i
        rw [hb, Submodule.mem_bot] at this
        exact this)
      obtain ⟨p, hp⟩ := (lwOf D a).isLow _ hb
      exact ⟨p, fun _ => hp⟩
  have hqb : ∀ j, ∃ q : ℕ, ins.wb j ≠ 0 → ins.αb j = D.h b + q := fun j => by
    obtain ⟨k, hk⟩ := ins.hlev j
    exact ⟨k, fun _ => hk⟩
  choose p hp using hpa
  choose q hq using hqb
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, N0 = ∑ i, p i + ∑ j, q j := ⟨_, rfl⟩
  have hpq : ∀ i j, p i + q j ≤ N0 := by
    intro i j
    have h1 : p i ≤ ∑ i, p i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : q j ≤ ∑ j, q j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  by_cases hnd : (∑ i, ins.wa i) ≠ 0 ∧ (∑ j, ins.wb j) ≠ 0
  · obtain ⟨na, hna⟩ := eigen_sqL_nat (lwOf D a).isMod (lwOf D a).isLow ins.hsqa hnd.1
    obtain ⟨nb, hnb⟩ := eigen_sqL_nat (lwOf D b).isMod (lwOf D b).isLow ins.hsqb hnd.2
    have hal : ∀ i j, ins.wa i ≠ 0 → ins.wb j ≠ 0 →
        ∃ Dn : ℕ, ins.κ - ins.αa i - ins.αb j + N0 = Dn := by
      intro i j hi hj
      have h1 := hpq i j
      refine ⟨na + nb + N0 - p i - q j, ?_⟩
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      rw [Insertion.κ, hna, hnb, hp i hi, hq j hj]
      change D.h a + (na : ℂ) + (D.h b + nb) - (D.h a + p i) - (D.h b + q j) + N0 = _
      ring
    let Vv : ℕ → Q.carrier := fun s =>
      bracketModes Yin (ins.κ - 1 - Q.h - ((s : ℂ) - N0)) (∑ i, ins.wa i) (∑ j, ins.wb j)
    have hVw : ∀ s, sqL Q.isMod 0 (Vv s) = (Q.h + s - N0) • Vv s := by
      intro s
      simp only [Vv]
      rw [hsub, transportedModes_weight Yin ins.hsqa ins.hsqb]
      congr 1
      unfold Insertion.κ
      ring
    refine ⟨fun _ => 1, Vv, fun s => if Vv s = 0 then Q.h else Q.h + s - N0, ?_, ?_, ?_⟩
    · intro s
      beta_reduce
      split_ifs with h
      · rw [h, map_zero, smul_zero]
      · exact hVw s
    · intro s
      beta_reduce
      split_ifs with h
      · exact ⟨0, by simp⟩
      · obtain ⟨n, hn⟩ := eigen_sqL_nat Q.isMod Q.isLow (hVw s) h
        exact ⟨n, hn⟩
    · intro y Yout τ
      obtain ⟨δ, hδ, hE⟩ := sum_laurent hV (lwOf_irreducible D a) (lwOf_irreducible D b)
        (lwOf_irreducible D y) iQ Yout Yin ins.wa ins.αa ins.hwa ins.wb ins.αb ins.hwb ins.κ N0
        hal τ
      refine ⟨δ, hδ, fun u hu hre => ?_⟩
      have h := hE u hu hre
      have hu0 : u ≠ 0 := fun h0 => by
        have := re_pos_of_exp_sub_one hre
        rw [h0, Complex.zero_re] at this
        exact lt_irrefl _ this
      have hterm : ∀ s : ℕ, (1 : ℂ) * exp (((if Vv s = 0 then Q.h else Q.h + s - N0) - ins.κ) *
          log u) * traceFunction Yout (D.h y) (Vv s) τ =
          exp ((Q.h - ins.κ - N0) * log u) * u ^ s *
            traceFunction Yout (lwOf D y).h (bracketModes Yin
              (ins.κ - 1 - Q.h - ((s : ℂ) - N0)) (∑ i, ins.wa i) (∑ j, ins.wb j)) τ := by
        intro s
        change _ = _ * _ * traceFunction Yout (D.h y) (Vv s) τ
        by_cases hv : Vv s = 0
        · rw [hv, traceFunction_zero, mul_zero, mul_zero]
        · rw [if_neg hv]
          have he : (Q.h + s - N0 - ins.κ) * log u = (Q.h - ins.κ - N0) * log u + s * log u := by
            ring
          rw [he, exp_add, Complex.exp_nat_mul, Complex.exp_log hu0]
          ring
      have h' := h.congr_fun hterm
      exact ⟨h'.summable, h'.tsum_eq.symm⟩
  · have hal : ∀ i j, ins.wa i ≠ 0 → ins.wb j ≠ 0 →
        ∃ Dn : ℕ, (D.h a + D.h b) - ins.αa i - ins.αb j + N0 = Dn := by
      intro i j hi hj
      have h1 := hpq i j
      refine ⟨N0 - p i - q j, ?_⟩
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hp i hi, hq j hj]
      ring
    refine ⟨fun _ => 0, fun _ => 0, fun _ => Q.h, fun _ => by simp, fun _ => ⟨0, by simp⟩, ?_⟩
    intro y Yout τ
    obtain ⟨δ, hδ, hE⟩ := sum_laurent hV (lwOf_irreducible D a) (lwOf_irreducible D b)
      (lwOf_irreducible D y) iQ Yout Yin ins.wa ins.αa ins.hwa ins.wb ins.αb ins.hwb
      (D.h a + D.h b) N0 hal τ
    refine ⟨δ, hδ, fun u hu hre => ⟨by simp, ?_⟩⟩
    have h := hE u hu hre
    have hz : ∀ s : ℕ, bracketModes Yin (D.h a + D.h b - 1 - Q.h - ((s : ℂ) - N0))
        (∑ i, ins.wa i) (∑ j, ins.wb j) = 0 := by
      intro s
      rw [not_and_or, not_not, not_not] at hnd
      rcases hnd with h0 | h0
      · rw [h0, map_zero, LinearMap.zero_apply]
      · rw [h0, map_zero]
    simp only [hz, traceFunction_zero, mul_zero] at h
    simp only [zero_mul, tsum_zero]
    exact h.unique hasSum_zero

/-- **Huang's coordinate-change identity for intertwining operators** (math/0303049, Prop. 1.2,
normalised; `IntCoord.NormalizedIntertwinerSubstitution`) for intertwiners among irreducible
lowest-weight modules of a nice VOA. A purely formal, algebraic statement (TRUE). -/
def IntertwinerSubstitutionInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (P₁ P₂ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW → Q.IsIrreducibleLW →
      ∀ Y : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod, NormalizedIntertwinerSubstitution Y

/-- **The coordinate-change input from the algebraic substitution identity.** -/
theorem channelBracketSharpInput_of_substitution (h : IntertwinerSubstitutionInput.{u}) :
    ChannelBracketSharpInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D _ _ _ a b Q iQ Yin
  exact innerBracketSharp_of_substitution hNice.1 D Q iQ Yin
    (h 𝒱 W hNice _ _ Q (lwOf_irreducible D a) (lwOf_irreducible D b) iQ Yin)

/-- **Huang's Theorem 5.2 from the algebraic substitution identity, (N2) and (N4).**
(N1) and (N3), including ALL convergence, are discharged. -/
theorem fusionEigenInput_of_substitution (h : IntertwinerSubstitutionInput.{u})
    (h2 : ConjugationInputAll.{u, w}) (h4 : ChannelIndependenceInput.{u, w}) :
    VerlindeEigen.FusionEigenInput.{u, w} :=
  fusionEigenInput_of_channelBracket (channelBracketSharpInput_of_substitution h) h2 h4

end Main

end VOA.Huang.GenusOneG1e
