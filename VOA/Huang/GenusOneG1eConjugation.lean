import VOA.Huang.GenusOneG1eSharp

/-!
# (N2) `ConjugationInput` from bracket skew-symmetry seen through Zhu's traces

Step (5g) of the proof of (G1).

With the proved Laurent expansions (`sum_laurent`) both the vacuum channel `vacF x` and the
reversed-pair channel `revF z` are explicit absolutely convergent series
`Σ_s e^{(−κ−N₀) log u} u^s Z(v_s)` of Zhu one-point functions of the explicit formal bracket modes
`v_s = bracketModes Y n_s (Σ w_a) (Σ w_b)` (`n_s = κ − 1 − (s − N₀)`). (N2) then reduces to
an identity between Zhu traces of explicit vectors:

* `TraceSkew F hv c π` (named, TRUE): `Z_x(Y^π[w_b]_n w_a) = μ e^{iπ(−n−1)} Z_x(Y^ε[w_a]_n w_b)`,
  `μ ≠ 0`. *Why true:* `π ∘ (skew) ∝ ε` (`Hom(M_b ⊠ M_a, V)` is one-dimensional since `ε ≠ 0`,
  and `π ≠ 0` as `η ≫ π = 𝟙`), so as intertwiners `Y^π = μ Ω₀(Y^ε)` (FHL skew-symmetry, phase
  `e^{iπ}`); transported to bracket coordinates (Huang Prop. 1.2) this is
  `Y^π[w_b, u] w_a = μ e^{u L[−1]} Y^ε[w_a, e^{iπ} u] w_b`; Zhu's `Z(L[−1] v) = 0` kills every
  `j ≥ 1` term of `e^{u L[−1]}`.
* the parity `Z_{σx}(v) = (−1)^k Z_x(v)` for `v ∈ V_[k]` is proved from Zhu's theorem at
  `−1 ∈ SL₂(ℤ)` and `ρ(−1) = P_σ` (`traceParity_of_rep`), the `L[0]`-weight `k = s − N₀ ∈ ℕ` of
  `v_s` from the substitution identity (`transportedModes_weight`) and `eigen_sqL_nat`.

* `conjugationInput_of_skew` (per instance), `conjugationInputAll_of_skew`;
* `fusionEigenInput_of_substitution_skew : IntertwinerSubstitutionInput → TraceSkewInput →
  ChannelIndependenceInput → FusionEigenInput`.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1e

open VOA VOA.Huang Complex VOA.Huang.GenusOneG1d VOA.Huang.VerlindeFusion
  VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.TensorCat
  VOA.Huang.VerlindeTransport VOA.Huang.GenusOneG1c CategoryTheory
open VOA.Huang.GenusOne (sqL traceFunction)
open VOA.Huang.GenusOne.IntCoord (bracketModes NormalizedIntertwinerSubstitution
  transportedModes_weight vacuum_traceFunction_eq)
open VOA.Huang.GenusTwoPoint (vacuumLW)
open scoped BigOperators MatrixGroups

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- The trace-level bracket skew-symmetry of the two vacuum pairings (TRUE; see the module doc). -/
def TraceSkew (F : FusionChoice W) {D : VOA.ModularData W ι} {a b : ι} (hv : W.vacuum ≠ 0)
    (c : TransferChoice F D a b) (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject) :
    Prop :=
  ∃ μ : ℂ, μ ≠ 0 ∧ ∀ (n : ℂ) (wa : (lwOf D a).carrier) (wb : (lwOf D b).carrier) (x : ι)
    (τ : UpperHalfPlane),
      traceFun D.Mfam D.h x
          (bracketModes (P := lwOf D b) (Q := lwOf D a) (N := vacuumLW W hv) (piInt F π) n wb wa)
          τ =
        μ * exp ((Real.pi : ℂ) * I * (-n - 1)) * traceFun D.Mfam D.h x
          (bracketModes (P := lwOf D a) (Q := lwOf D b) (N := vacuumLW W hv) (epsInt F c) n wa wb)
          τ

/-- `TraceSkew` for every instance (with `π` a retraction of the vacuum summand). -/
def TraceSkewInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ (F : FusionChoice W) (a b : ι) (c : TransferChoice F D a b) (hv : W.vacuum ≠ 0)
        (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject), c.η ≫ π = 𝟙 _ →
        TraceSkew F hv c π

/-- Trace parity from Zhu's theorem at `−1` and `ρ(−1) = P_σ`. -/
theorem traceParity_of_rep (D : VOA.ModularData W ι) (hZ : ZhuModularityAnalytic D)
    {σ : ι → ι} (hP : ∀ x y, D.rep (-1) x y = if y = σ x then 1 else 0) (k : ℕ) (v : 𝒱)
    (hv : v ∈ sqWeightSpace W (k : ℂ)) (x : ι) (τ : UpperHalfPlane) :
    traceFun D.Mfam D.h (σ x) v τ = (-1 : ℂ) ^ k * traceFun D.Mfam D.h x v τ := by
  have hz := hZ (-1) k v hv x τ
  rw [ModularGroup.SL_neg_smul, one_smul, autFactor_neg_one] at hz
  simp only [hP, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at hz
  rw [hz, ← mul_assoc, ← mul_pow]
  simp

theorem traceFun_zero (D : VOA.ModularData W ι) (x : ι) (τ : UpperHalfPlane) :
    traceFun D.Mfam D.h x 0 τ = 0 := by
  rw [← vacuum_traceFunction_eq D x 0 τ]
  exact traceFunction_zero _ _ τ

/-- Alignment of the components of an insertion (offsets from the lowest weights). -/
theorem ins_align (D : VOA.ModularData W ι) {a b : ι} (ins : Insertion D a b) :
    ∃ N0 : ℕ, (∀ i j, ins.wa i ≠ 0 → ins.wb j ≠ 0 →
        ∃ Dn : ℕ, (D.h a + D.h b) - ins.αa i - ins.αb j + N0 = Dn) ∧
      ((∑ i, ins.wa i) ≠ 0 → (∑ j, ins.wb j) ≠ 0 → ∀ i j, ins.wa i ≠ 0 → ins.wb j ≠ 0 →
        ∃ Dn : ℕ, ins.κ - ins.αa i - ins.αb j + N0 = Dn) := by
  classical
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
  refine ⟨∑ i, p i + ∑ j, q j, ?_, ?_⟩
  · intro i j hi hj
    have h1 : p i ≤ ∑ i, p i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : q j ≤ ∑ j, q j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    refine ⟨∑ i, p i + ∑ j, q j - p i - q j, ?_⟩
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hp i hi, hq j hj]
    push_cast; ring
  · intro hA hB i j hi hj
    obtain ⟨na, hna⟩ := eigen_sqL_nat (lwOf D a).isMod (lwOf D a).isLow ins.hsqa hA
    obtain ⟨nb, hnb⟩ := eigen_sqL_nat (lwOf D b).isMod (lwOf D b).isLow ins.hsqb hB
    have h1 : p i ≤ ∑ i, p i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : q j ≤ ∑ j, q j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    refine ⟨na + nb + (∑ i, p i + ∑ j, q j) - p i - q j, ?_⟩
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    rw [Insertion.κ, hna, hnb, hp i hi, hq j hj]
    change D.h a + (na : ℂ) + (D.h b + nb) - (D.h a + p i) - (D.h b + q j) + _ = _
    ring

/-- The parity step: `e^{iπ(−n−1)} Z_x(v) = e^{−iπκ} Z_{σx}(v)` for `v` of `L[0]`-weight
`s − N₀`, `n = κ − 1 − (s − N₀)`. -/
theorem parity_step (D : VOA.ModularData W ι) (hZ : ZhuModularityAnalytic D) (hv : W.vacuum ≠ 0)
    {σ : ι → ι} (hP : ∀ x y, D.rep (-1) x y = if y = σ x then 1 else 0) (κ : ℂ) (N0 s : ℕ)
    (v : 𝒱) (hw : sqL (adjointModule W) 0 v = ((s : ℂ) - N0) • v) (x : ι)
    (τ : UpperHalfPlane) :
    exp ((Real.pi : ℂ) * I * (-(κ - 1 - 0 - ((s : ℂ) - N0)) - 1)) *
        traceFun D.Mfam D.h x v τ =
      exp (-((Real.pi : ℂ) * I * κ)) * traceFun D.Mfam D.h (σ x) v τ := by
  by_cases h0 : v = 0
  · rw [h0, traceFun_zero, traceFun_zero, mul_zero, mul_zero]
  obtain ⟨k, hk⟩ := eigen_sqL_nat (adjointModule W) (vacuumLW W hv).isLow hw h0
  change ((s : ℂ) - N0) = 0 + k at hk
  rw [zero_add] at hk
  have hmem : v ∈ sqWeightSpace W (k : ℂ) := by
    rw [mem_sqWeightSpace_iff, ← sqL_adjoint_zero, hw, hk]
  rw [traceParity_of_rep D hZ hP k v hmem x τ]
  have he : (Real.pi : ℂ) * I * (-(κ - 1 - 0 - ((s : ℂ) - N0)) - 1) =
      -((Real.pi : ℂ) * I * κ) + k * ((Real.pi : ℂ) * I) := by
    rw [hk]; ring
  rw [he, exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  ring

/-- **(N2) for one instance**, from `TraceSkew`, the substitution identity for `Y^ε`, Zhu's
theorem at `−1` and `ρ(−1) = P_σ`. -/
theorem conjugationInput_of_skew (F : FusionChoice W) (hV : StronglyRational W)
    (D : VOA.ModularData W ι) (hZ : ZhuModularityAnalytic D) {a b : ι} (hv : W.vacuum ≠ 0)
    (c : TransferChoice F D a b) (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject)
    {σ : ι → ι} (hP : ∀ x y, D.rep (-1) x y = if y = σ x then 1 else 0)
    (hsk : TraceSkew F hv c π)
    (hsub : NormalizedIntertwinerSubstitution (P := lwOf D a) (Q := lwOf D b)
      (N := vacuumLW W hv) (epsInt F c)) :
    ConjugationInput F hv c π σ := by
  obtain ⟨μ, hμ, hsk⟩ := hsk
  refine ⟨μ, hμ, fun ins τ => ?_⟩
  have iQ : (vacuumLW W hv).IsIrreducibleLW :=
    (isSimple_iff_adjointModule_isIrreducible W).mp hV.simple
  obtain ⟨N0, hal0, hal1⟩ := ins_align D ins
  by_cases hnd : (∑ i, ins.wa i) ≠ 0 ∧ (∑ j, ins.wb j) ≠ 0
  · have hal := hal1 hnd.1 hnd.2
    have halr : ∀ j i, ins.wb j ≠ 0 → ins.wa i ≠ 0 →
        ∃ Dn : ℕ, ins.κ - ins.αb j - ins.αa i + N0 = Dn := by
      intro j i hj hi
      obtain ⟨Dn, h⟩ := hal i j hi hj
      exact ⟨Dn, by rw [← h]; ring⟩
    have hvac := fun x : ι => sum_laurent hV (lwOf_irreducible D a) (lwOf_irreducible D b)
      (lwOf_irreducible D x) iQ (moduleIntertwiner (lwOf D x).isMod) (epsInt F c)
      ins.wa ins.αa ins.hwa ins.wb ins.αb ins.hwb ins.κ N0 hal τ
    have hrev := fun x : ι => sum_laurent hV (lwOf_irreducible D b) (lwOf_irreducible D a)
      (lwOf_irreducible D x) iQ (moduleIntertwiner (lwOf D x).isMod) (piInt F π)
      ins.wb ins.αb ins.hwb ins.wa ins.αa ins.hwa ins.κ N0 halr τ
    choose δ1 hδ1 h1 using hvac
    choose δ2 hδ2 h2 using hrev
    obtain ⟨δa, hδa, hlea⟩ := exists_pos_le_fintype δ1 hδ1
    obtain ⟨δb, hδb, hleb⟩ := exists_pos_le_fintype δ2 hδ2
    refine ⟨min δa δb, lt_min hδa hδb, fun u hu hre z => ?_⟩
    have hA := h1 (σ z) u (lt_of_lt_of_le hu ((min_le_left _ _).trans (hlea _))) hre
    have hB := h2 z u (lt_of_lt_of_le hu ((min_le_right _ _).trans (hleb _))) hre
    unfold revF vacF
    rw [Finset.sum_comm, ← hB.tsum_eq, ← hA.tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun s => ?_
    have hw : sqL (adjointModule W) 0 (bracketModes (P := lwOf D a) (Q := lwOf D b)
        (N := vacuumLW W hv) (epsInt F c) (ins.κ - 1 - 0 - ((s : ℂ) - N0))
          (∑ i, ins.wa i) (∑ j, ins.wb j)) = ((s : ℂ) - N0) • bracketModes
          (P := lwOf D a) (Q := lwOf D b) (N := vacuumLW W hv) (epsInt F c)
          (ins.κ - 1 - 0 - ((s : ℂ) - N0)) (∑ i, ins.wa i) (∑ j, ins.wb j) := by
      rw [hsub]
      erw [transportedModes_weight (N := vacuumLW W hv) (epsInt F c) ins.hsqa ins.hsqb]
      congr 1
      unfold Insertion.κ
      ring
    have hps := parity_step D hZ hv hP ins.κ N0 s _ hw z τ
    have hsk' := hsk (ins.κ - 1 - 0 - ((s : ℂ) - N0)) (∑ i, ins.wa i) (∑ j, ins.wb j) z τ
    change exp (((0 : ℂ) - ins.κ - N0) * log u) * u ^ s * traceFunction
        (moduleIntertwiner (lwOf D z).isMod) (lwOf D z).h (bracketModes (P := lwOf D b)
          (Q := lwOf D a) (N := vacuumLW W hv) (piInt F π) (ins.κ - 1 - 0 - ((s : ℂ) - N0))
          (∑ j, ins.wb j) (∑ i, ins.wa i)) τ =
      μ * exp (-((Real.pi : ℂ) * I * ins.κ)) * (exp (((0 : ℂ) - ins.κ - N0) * log u) * u ^ s *
        traceFunction (moduleIntertwiner (lwOf D (σ z)).isMod) (lwOf D (σ z)).h
          (bracketModes (P := lwOf D a) (Q := lwOf D b) (N := vacuumLW W hv) (epsInt F c)
            (ins.κ - 1 - 0 - ((s : ℂ) - N0)) (∑ i, ins.wa i) (∑ j, ins.wb j)) τ)
    rw [vacuum_traceFunction_eq, vacuum_traceFunction_eq, hsk', mul_assoc μ, hps]
    ring
  · have halr : ∀ j i, ins.wb j ≠ 0 → ins.wa i ≠ 0 →
        ∃ Dn : ℕ, (D.h a + D.h b) - ins.αb j - ins.αa i + N0 = Dn := by
      intro j i hj hi
      obtain ⟨Dn, h⟩ := hal0 i j hi hj
      exact ⟨Dn, by rw [← h]; ring⟩
    have hvac := fun x : ι => sum_laurent hV (lwOf_irreducible D a) (lwOf_irreducible D b)
      (lwOf_irreducible D x) iQ (moduleIntertwiner (lwOf D x).isMod) (epsInt F c)
      ins.wa ins.αa ins.hwa ins.wb ins.αb ins.hwb (D.h a + D.h b) N0 hal0 τ
    have hrev := fun x : ι => sum_laurent hV (lwOf_irreducible D b) (lwOf_irreducible D a)
      (lwOf_irreducible D x) iQ (moduleIntertwiner (lwOf D x).isMod) (piInt F π)
      ins.wb ins.αb ins.hwb ins.wa ins.αa ins.hwa (D.h a + D.h b) N0 halr τ
    choose δ1 hδ1 h1 using hvac
    choose δ2 hδ2 h2 using hrev
    obtain ⟨δa, hδa, hlea⟩ := exists_pos_le_fintype δ1 hδ1
    obtain ⟨δb, hδb, hleb⟩ := exists_pos_le_fintype δ2 hδ2
    refine ⟨min δa δb, lt_min hδa hδb, fun u hu hre z => ?_⟩
    have hA := h1 (σ z) u (lt_of_lt_of_le hu ((min_le_left _ _).trans (hlea _))) hre
    have hB := h2 z u (lt_of_lt_of_le hu ((min_le_right _ _).trans (hleb _))) hre
    rw [not_and_or, not_not, not_not] at hnd
    have hz1 : ∀ n : ℂ, bracketModes (P := lwOf D a) (Q := lwOf D b) (N := vacuumLW W hv)
        (epsInt F c) n (∑ i, ins.wa i) (∑ j, ins.wb j) = 0 := by
      intro n
      rcases hnd with h0 | h0
      · rw [h0, map_zero, LinearMap.zero_apply]
      · rw [h0, map_zero]
    have hz2 : ∀ n : ℂ, bracketModes (P := lwOf D b) (Q := lwOf D a) (N := vacuumLW W hv)
        (piInt F π) n (∑ j, ins.wb j) (∑ i, ins.wa i) = 0 := by
      intro n
      rcases hnd with h0 | h0
      · rw [h0, map_zero]
      · rw [h0, map_zero, LinearMap.zero_apply]
    simp only [hz1, hz2, traceFunction_zero, mul_zero] at hA hB
    have hvacF : vacF F hv c ins (σ z) τ u = 0 := hA.unique hasSum_zero
    have hrevF : revF F hv π ins z τ u = 0 := by
      unfold revF
      rw [Finset.sum_comm]
      exact hB.unique hasSum_zero
    rw [hvacF, hrevF, mul_zero]

/-- **(N2) for every instance**, from `TraceSkewInput` and the substitution identity. -/
theorem conjugationInputAll_of_skew (hS : TraceSkewInput.{u, w})
    (hsub : IntertwinerSubstitutionInput.{u}) : ConjugationInputAll.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp F a b c hv π hπ σ hP
  have iQ : (vacuumLW W hv).IsIrreducibleLW :=
    (isSimple_iff_adjointModule_isIrreducible W).mp hNice.1.simple
  exact conjugationInput_of_skew F hNice.1 D hZ hv c π hP
    (hS 𝒱 W hNice ι D hZ hirr hcomp F a b c hv π hπ)
    (hsub 𝒱 W hNice (lwOf D a) (lwOf D b) (vacuumLW W hv) (lwOf_irreducible D a)
      (lwOf_irreducible D b) iQ (epsInt F c))

/-- **Huang's Theorem 5.2 from the substitution identity, trace skew-symmetry and (N4).**
(N1), (N2), (N3) and all convergence are discharged. -/
theorem fusionEigenInput_of_substitution_skew (hsub : IntertwinerSubstitutionInput.{u})
    (hS : TraceSkewInput.{u, w}) (h4 : ChannelIndependenceInput.{u, w}) :
    VerlindeEigen.FusionEigenInput.{u, w} :=
  fusionEigenInput_of_substitution hsub (conjugationInputAll_of_skew hS hsub) h4

end VOA.Huang.GenusOneG1e
