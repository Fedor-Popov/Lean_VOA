import VOA.Moonshine.MoonshineCNTwistedCharacters
import VOA.Moonshine.MoonshineCNReplicationAnalytic
import VOA.Moonshine.MoonshineCNMonsterBorcherdsData
import VOA.Moonshine.MoonshineLRConwayNorton

/-!
# The twisted denominator identities of the Monster Lie algebra, and complete replicability

For Borcherds data with a symmetry `σ` of finite order, every root space has an eigenbasis of `σ`,
so the twisted denominator identity holds as soon as the traces of the powers `σ^k` on the positive
root spaces are given by a coefficient family
(`BorcherdsData.twistedDenominatorIdentity_of_finOrder`).

For the Monster Lie algebra the root space `(m, n)` is `V♮` in weight `1 + mn`, compatibly with
`Aut V♮` (`monsterLie_weightAction_trace`), so the traces are the McKay–Thompson coefficients
`tr(σ^k | V♮_{1+mn})`.  Hence, given generation of the Monster Lie algebra by its simple root
spaces (the only Borcherds-data field not yet in Lean):

* `twistedDenominatorIdentity_of_simpleRootGeneration`: the twisted denominator identity of every
  finite-order automorphism of `V♮`;
* `completelyReplicableOfFinOrder_of_simpleRootGeneration`: complete replicability of every
  finite-order McKay–Thompson series, with the Faber polynomials;
* `completelyReplicable_of_simpleRootGeneration`: `CompletelyReplicable`, given that every
  automorphism has finite order;
* `conwayNorton_of_simpleRootGeneration`: the Conway–Norton conjecture, given generation and finite
  order (through the genus-zero theorem `M8.conwayNorton_of_finOrder_of_completelyReplicable`).
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open Module AutMonster

namespace BorcherdsData

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g)
  {G : Type*} [Group G] (A : D.GAction G)

theorem weightAction_one (γ : ℤ × ℤ) : D.weightAction A 1 γ = 1 := by
  ext x
  simp [weightAction]

/-- **The twisted denominator identity for a symmetry of finite order**, given the traces of its
powers on the positive root spaces. -/
theorem twistedDenominatorIdentity_of_finOrder (σ : G) (hσ : IsOfFinOrder σ) (c : ℕ → ℕ → ℂ)
    (htr : ∀ k : ℕ, 1 ≤ k → ∀ γ : ℤ × ℤ, borcherdsPositiveCone γ →
      LinearMap.trace ℂ (D.weightSpace γ) (D.weightAction A (σ ^ k) γ) =
        c k (γ.1 * γ.2).toNat) :
    TwistedDenominatorIdentity c := by
  classical
  obtain ⟨e, f, he, hf, hef⟩ := D.exists_normalized_real_pair
  obtain ⟨N, hN, hσN⟩ := isOfFinOrder_iff_pow_eq_one.mp hσ
  have hex : ∀ γ : ℤ × ℤ, ∃ (ι : Type _) (_ : Fintype ι) (b : Basis ι ℂ (D.weightSpace γ))
      (μ : ι → ℂ), ∀ i, D.weightAction A σ γ (b i) = μ i • b i := by
    intro γ
    haveI := D.weight_finite γ
    exact exists_eigenbasis_of_pow_eq_one _ hN (by
      rw [← D.weightAction_pow, hσN, D.weightAction_one])
  choose ι hι b μ hb using hex
  haveI : ∀ γ, Fintype (ι γ) := hι
  refine D.twistedDenominatorIdentity_of_eigenbasis ι e he f hf hef b μ A σ hb c ?_
  intro k hk γ hγ
  rw [← htr k hk γ hγ, D.weightAction_pow,
    trace_pow_eq_sum_of_eigenbasis (b γ) _ (μ γ) (hb γ)]

end BorcherdsData

/-! ### The Monster Lie algebra -/

/-- The trace of an automorphism of `V♮` on a positive root space `(m, n)` of the Monster Lie
algebra is its trace on `V♮` in weight `1 + mn`. -/
theorem monsterLie_weightAction_trace (hgen : MonsterLieSimpleRootGeneration) (τ : AutVnat)
    (γ : ℤ × ℤ) (hγ : borcherdsPositiveCone γ) :
    LinearMap.trace ℂ ((monsterLieBorcherdsData hgen).weightSpace γ)
        ((monsterLieBorcherdsData hgen).weightAction (monsterLieBorcherdsAction hgen) τ γ) =
      PowerSeries.coeff (γ.1 * γ.2).toNat (mckayThompson τ) := by
  have hne : γ.1 ≠ 0 ∨ -γ.2 ≠ 0 := Or.inl (by have := hγ.1; omega)
  let E := monsterLieRootSpaceEquiv γ.1 (-γ.2) hne
  let W : Module.End ℂ (monsterLieMomentum ![γ.1, -γ.2]) :=
    (monsterLieBorcherdsData hgen).weightAction (monsterLieBorcherdsAction hgen) τ γ
  have hconj : E.conj W = gradedAutAction VnatVOA (1 - γ.1 * -γ.2) τ := by
    apply LinearMap.ext
    intro v
    have h := monsterLieRootSpaceEquiv_equivariant γ.1 (-γ.2) hne τ (E.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  change LinearMap.trace ℂ _ W = _
  rw [← LinearMap.trace_conj' W E, hconj]
  change gradedAutTrace VnatVOA τ (1 - γ.1 * -γ.2) = _
  rw [mckayThompson_coeff]
  congr 1
  have hp : 0 < γ.1 * γ.2 := mul_pos (by have := hγ.1; omega) (by have := hγ.2; omega)
  rw [Int.toNat_of_nonneg hp.le]
  ring

/-- **The twisted denominator identities** of the Monster Lie algebra: for every automorphism
`σ` of `V♮` of finite order, `D ũ_σ = (1 − ũ_σ) P̃_σ`, given generation by simple root spaces. -/
theorem twistedDenominatorIdentity_of_simpleRootGeneration (hgen : MonsterLieSimpleRootGeneration)
    (σ : AutVnat) (hσ : IsOfFinOrder σ) : TwistedDenominatorIdentity (mckayThompsonFamily σ) :=
  (monsterLieBorcherdsData hgen).twistedDenominatorIdentity_of_finOrder
    (monsterLieBorcherdsAction hgen) σ hσ _
    fun k _ γ hγ => monsterLie_weightAction_trace hgen (σ ^ k) γ hγ

/-- **Complete replicability of every finite-order McKay–Thompson series**, given generation of
the Monster Lie algebra by its simple root spaces. -/
theorem completelyReplicableOfFinOrder_of_simpleRootGeneration
    (hgen : MonsterLieSimpleRootGeneration) : CompletelyReplicableOfFinOrder :=
  completelyReplicableOfFinOrder_of_twistedDenominator fun g hg =>
    twistedDenominatorIdentity_of_simpleRootGeneration hgen g hg

/-- **Complete replicability**, given generation and finite order of every automorphism. -/
theorem completelyReplicable_of_simpleRootGeneration (hgen : MonsterLieSimpleRootGeneration)
    (hfin : ∀ g : AutVnat, IsOfFinOrder g) : CompletelyReplicable :=
  completelyReplicable_of_twistedDenominator hfin fun g =>
    twistedDenominatorIdentity_of_simpleRootGeneration hgen g (hfin g)

/-- **The Conway–Norton conjecture**, given generation of the Monster Lie algebra by its simple
root spaces and finite order of every automorphism of `V♮`. -/
theorem conwayNorton_of_simpleRootGeneration (hgen : MonsterLieSimpleRootGeneration)
    (hfin : ∀ g : AutVnat, IsOfFinOrder g) : ConwayNortonConjecture :=
  M8.conwayNorton_of_finOrder_of_completelyReplicable hfin
    (completelyReplicable_of_simpleRootGeneration hgen hfin)

end VOA.Moonshine.ConwayNorton
