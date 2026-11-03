import VOA.DeligneAudit.SL4TAdjointSiteLevelRelations
import VOA.DeligneAudit.SL4TMultiDoubledAssembly

/-!
# Assembly of Law B at one adjoint site from joint relation flags

The level theorem is stated for coefficient flags whose level relations lie in
`(P, t^M)`. At one adjoint site the killed relation ideal is the joint ideal

    E = (P_y(t), t^(h+1), s t^h) ⊆ A[t],     A = R / I_J(h),

with the joint symbol `s` of `SL4TAdjointSiteResiduals`. This file proves:

* `pi_subspaceFlag_bound_of_relationIdeal`: the power-sum-stable flag bound for an arbitrary
  ideal of relations killed by `Φ̄`, generalising `pi_subspaceFlag_bound_of_characteristic`;
  its mixed form `mixedQuotientRingImage_bound_of_relationFlag`, for the structure
  `MixedQuotientRelationFlag`;
* `piCurrentMap_jointIdeal_eq_zero`: `Φ̄` kills `(P, t^(N+1), σ t^N)` once it kills `P` (the
  Garland relation), all modes above `N`, and `σ t^N A[t]`;
* `adjointSite_jointSymbol_lowering_zero`: on every block `F(h) π(s φ) = 0`, by type: Σ₁(h) on
  `(0, ·, 1)` (`s = 1`), the hypothesis L₂(h) on `(0, ·, 0)` (`s = b₀`), Theorem L₃(h) on
  `(1, ·, 1)` (`s = a₀`), and nothing on `(1, ·, 0)` (`s = 0`);
* `adjointSiteSecondLeviOrbit_bound_of_jointFlag`: a joint relation flag in `A` bounds the actual
  second Levi orbit of the block (Corollary K supplies `A → N̄`);
* `adjointSiteWordWeight_block_sum_le`: the block costs (the weights `3^T 2^D` of the words of the
  block) sum to at most `15 · 20^k · 6^(B-2k)` (`adjointSiteWord_weight_sum`);
* **`adjointSiteLawB_of_jointFlags`**: joint relation flags of these costs on every valid block,
  together with L₂(B - k), imply Law B at one adjoint site;
* `adjointSiteLawB_of_residuals_of_jointFlagConstruction`: hence `AdjointSiteLawBFromResiduals`
  follows from the single remaining ring statement `AdjointSiteJointFlagConstruction` (the
  joint Theorem U/L of §4: S_A(B, k) produces those flags).
-/

namespace VOA.DeligneAudit.SL4T

open Polynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.CVsl2 (SL2 bal)

noncomputable section

/-! ### The flag bound for an arbitrary killed relation ideal -/

section Abstract

variable {R V : Type*} [CommRing R] [Algebra ℂ R]
variable [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V}

/-- A correction with coefficients in an earlier subspace and a relation in a killed ideal gives
every later mode relation. -/
theorem piCurrentMap_subspace_cell_of_relationIdeal (π : R →ₗ[ℂ] V) (F : ℕ → Module.End ℂ V)
    (I : Submodule ℂ R) (N : Submodule ℂ V) (Rel : Ideal R[X])
    (hπ : ∀ a ∈ I, π a ∈ N) (hF : ∀ s, N ≤ N.comap (F s))
    (hkill : ∀ f ∈ Rel, piCurrentMap F π f = 0)
    (a : R) (n : ℕ) (p : R[X]) (hp : ∀ l, p.coeff l ∈ I)
    (hrel : Polynomial.C a * X ^ n + p ∈ Rel) (s : ℕ) (hs : n ≤ s) : F s (π a) ∈ N := by
  have hr := Rel.mul_mem_right (X ^ (s - n)) hrel
  rw [add_mul, mul_assoc, ← pow_add, Nat.add_sub_of_le hs] at hr
  have hz := hkill _ hr
  rw [map_add, piCurrentMap_C_mul_X_pow] at hz
  rw [eq_neg_of_add_eq_zero_left hz]
  apply N.neg_mem
  apply piCurrentMap_subspace π F I N hπ hF
  intro l
  rw [coeff_mul_X_pow']
  split_ifs
  · exact hp _
  · exact I.zero_mem

/-- **The cell bound for a power-sum-stable flag against an arbitrary killed relation ideal.** -/
theorem pi_subspaceFlag_bound_of_relationIdeal (hS : SL2 E H F)
    (π : R →ₗ[ℂ] V) (p : ℕ → R) (r n : ℕ)
    (v : ℕ → R) (I : ℕ → Submodule ℂ R) (ν : ℕ → ℕ) (Rel : Ideal R[X])
    (h0 : I 0 = ⊥) (htop : I n = ⊤)
    (hstep : ∀ i < n, I (i + 1) = I i ⊔ ℂ ∙ v i)
    (hstable : ∀ i ≤ n, ∀ s, 1 ≤ s → ∀ a ∈ I i, p s * a ∈ I i)
    (hrel : ∀ i < n, ∃ q : R[X], (∀ l, q.coeff l ∈ I i) ∧
      Polynomial.C (v i) * X ^ (ν i) + q ∈ Rel)
    (hp : ∀ s, 1 ≤ s → IsNilpotent (p s))
    (hE : ∀ s a, E s (π a) = 0)
    (hH0 : ∀ a, H 0 (π a) = (r : ℂ) • π a)
    (hH : ∀ s, 1 ≤ s → ∀ a, H s (π a) = π (p s * a))
    (hF0 : ∀ a, (F 0 ^ (r + 1)) (π a) = 0)
    (hkill : ∀ f ∈ Rel, piCurrentMap F π f = 0) :
    FiniteDimensional ℂ (currentSpan E H F (Set.range π)) ∧
      Module.finrank ℂ (currentSpan E H F (Set.range π)) ≤
        ∑ i ∈ Finset.range n, ((bal r (ν i)).map (· + 1)).prod := by
  have hprefix := subspaceFlag_eq_prefix v I n h0 hstep
  have himage (i : ℕ) (hi : i ≤ n) (a : R) (ha : a ∈ I i) :
      π a ∈ cellFlag E H F (fun j => π (v j)) i := by
    apply pi_prefix_le_cellFlag π v i
    rw [← hprefix i hi]
    exact ha
  have hspan : generatorPrefix v n = ⊤ := by rw [← hprefix n le_rfl, htop]
  rw [pi_currentSpan_eq_cellFlag π v n hspan]
  apply cellFlag_bound_any hS _ r ν n
  intro i hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [hE]
    exact Submodule.zero_mem _
  · rw [hH0, sub_self]
    exact Submodule.zero_mem _
  · intro s hs
    rw [hH s hs]
    exact himage i (by omega) _ (subspace_cell_nilpotent_mul (I i) (I (i + 1))
      (v i) (p s) (hstep i hi) (hstable i (by omega) s hs)
      (hstable (i + 1) (by omega) s hs) (hp s hs))
  · rw [hF0]
    exact Submodule.zero_mem _
  · obtain ⟨q, hq, hqr⟩ := hrel i hi
    exact piCurrentMap_subspace_cell_of_relationIdeal π F (I i) _ Rel
      (himage i (by omega)) (cellFlag_stable _ i).2.2 hkill (v i) (ν i) q hq hqr

/-- `Φ̄` kills the joint ideal `(P, t^(N+1), σ t^N)` once it kills `P`, all modes above `N`, and
`σ t^N A[t]`. -/
theorem piCurrentMap_jointIdeal_eq_zero (F : ℕ → Module.End ℂ V) (π : R →ₗ[ℂ] V)
    (P : R[X]) (σ : R) (N : ℕ) (hP : PiCharacteristic F π P)
    (hM : ∀ s, N + 1 ≤ s → ∀ a, F s (π a) = 0) (hσ : ∀ a, F N (π (σ * a)) = 0)
    (f : R[X])
    (hf : f ∈ Ideal.span {P} ⊔ Ideal.span {X ^ (N + 1)} ⊔ Ideal.span {Polynomial.C σ * X ^ N}) :
    piCurrentMap F π f = 0 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add, piCurrentMap_relationIdeal F π P (N + 1) hP hM hu, zero_add]
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hv
  clear hv hf hu
  induction g using Polynomial.induction_on' with
  | add g g' hg hg' => rw [mul_add, map_add, hg, hg', add_zero]
  | monomial l a =>
    rw [← C_mul_X_pow_eq_monomial, show Polynomial.C σ * X ^ N * (Polynomial.C a * X ^ l) =
      Polynomial.C (σ * a) * X ^ (l + N) by rw [C_mul, pow_add]; ring,
      piCurrentMap_C_mul_X_pow]
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · rw [zero_add]
      exact hσ a
    · exact hM _ (by omega) _

end Abstract

/-! ### Mixed relation flags -/

/-- A power-sum-stable coefficient flag whose level relations lie in a prescribed ideal. -/
structure MixedQuotientRelationFlag (q : MixedParams) (J : Ideal (MixedRing q))
    (Rel : Ideal (MixedRing q ⧸ J)[X]) (cost : ℕ) where
  length : ℕ
  vector : ℕ → MixedRing q ⧸ J
  space : ℕ → Submodule ℂ (MixedRing q ⧸ J)
  level : ℕ → ℕ
  zero : space 0 = ⊥
  top : space length = ⊤
  step : ∀ i < length, space (i + 1) = space i ⊔ ℂ ∙ vector i
  stable : ∀ i ≤ length, ∀ s, 1 ≤ s → ∀ a ∈ space i,
    Ideal.Quotient.mk J (mixedPowerSum q s) * a ∈ space i
  relation : ∀ i < length, ∃ p : (MixedRing q ⧸ J)[X],
    (∀ l, p.coeff l ∈ space i) ∧ Polynomial.C (vector i) * X ^ (level i) + p ∈ Rel
  bound : (∑ i ∈ Finset.range length,
    ((bal (mixedWeight q).toNat (level i)).map (· + 1)).prod) ≤ cost

section Mixed

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V}

/-- A relation flag in a killed coefficient quotient bounds the whole current image, provided
`Φ̄` kills `σ t^N` and all modes above `N`; the Garland relation is supplied automatically. -/
theorem mixedQuotientRingImage_bound_of_jointFlag
    (q : MixedParams) (hq : MixedValid q) (hS : SL2 E H F)
    (π : MixedRing q →ₗ[ℂ] V) (J : Ideal (MixedRing q))
    (hJ : J.restrictScalars ℂ ≤ LinearMap.ker π) (σ : MixedRing q) (N cost : ℕ)
    (flag : MixedQuotientRelationFlag q J
      (Ideal.span {(mixedCharacteristic q).map (Ideal.Quotient.mk J)} ⊔
        Ideal.span {X ^ (N + 1)} ⊔ Ideal.span {Polynomial.C (Ideal.Quotient.mk J σ) * X ^ N})
      cost)
    (hE : ∀ s φ, E s (π φ) = 0)
    (hH0 : ∀ φ, H 0 (π φ) = ((mixedWeight q).toNat : ℂ) • π φ)
    (hH : ∀ s, 1 ≤ s → ∀ φ, H s (π φ) = π (mixedPowerSum q s * φ))
    (hF0 : ∀ φ, (F 0 ^ ((mixedWeight q).toNat + 1)) (π φ) = 0)
    (hM : ∀ s, N + 1 ≤ s → ∀ φ, F s (π φ) = 0)
    (hσ : ∀ φ, F N (π (σ * φ)) = 0) :
    FiniteDimensional ℂ (currentSpan E H F (Set.range π)) ∧
      Module.finrank ℂ (currentSpan E H F (Set.range π)) ≤ cost := by
  let f := Ideal.Quotient.mkₐ ℂ J
  let ψ := multiplicityQuotientEvaluation π J hJ
  let p := fun s => f (mixedPowerSum q s)
  have heval (x : MixedRing q) : ψ (f x) = π x := rfl
  have hEq (s : ℕ) (x : MixedRing q ⧸ J) : E s (ψ x) = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J x
    exact hE s x
  have hHq (s : ℕ) (hs : 1 ≤ s) (x : MixedRing q ⧸ J) :
      H s (ψ x) = ψ (p s * x) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J x
    simpa only [p, ← map_mul, heval] using hH s hs x
  have hFq (x : MixedRing q ⧸ J) :
      (F 0 ^ ((mixedWeight q).toNat + 1)) (ψ x) = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J x
    exact hF0 x
  have htail (j : ℕ) (hj : (mixedWeight q).toNat < j) : newtonCoeff p j = 0 := by
    rw [newtonCoeff_map f, mixedPowerSum_newton_tail q hq j hj, map_zero]
  have hP := piCharacteristic_of_highest hS ψ p hEq hHq _ hFq htail
  have hpoly : descendingPoly (newtonCoeff p) (mixedWeight q).toNat =
      (mixedCharacteristic q).map f.toRingHom := by
    rw [← mixedPowerSum_descending q hq, descendingPoly_map]
    congr 1
    exact funext (newtonCoeff_map f (mixedPowerSum q))
  rw [hpoly] at hP
  have hkill : ∀ g ∈ Ideal.span {(mixedCharacteristic q).map (Ideal.Quotient.mk J)} ⊔
      Ideal.span {X ^ (N + 1)} ⊔ Ideal.span {Polynomial.C (Ideal.Quotient.mk J σ) * X ^ N},
      piCurrentMap F ψ g = 0 := by
    intro g hg
    apply piCurrentMap_jointIdeal_eq_zero F ψ _ (Ideal.Quotient.mk J σ) N hP
    · intro s hs x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J x
      exact hM s hs x
    · intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J x
      exact hσ x
    · exact hg
  obtain ⟨hf, hb⟩ := pi_subspaceFlag_bound_of_relationIdeal hS ψ p
    (mixedWeight q).toNat flag.length flag.vector flag.space flag.level _ flag.zero flag.top
    flag.step flag.stable flag.relation
    (fun s hs => (mixedPowerSum_nilpotent q hq s hs).map f) hEq
    (fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J x
      exact hH0 x) hHq hFq hkill
  have hr : Set.range ψ = Set.range π := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J x
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨f x, rfl⟩
  rw [hr] at hf hb
  exact ⟨hf, hb.trans flag.bound⟩

end Mixed

/-! ### The joint relation ideal at one adjoint site -/

/-- The joint relation ideal `(P_y, t^(h+1), s t^h)` of a one-adjoint-site block. -/
def adjointSiteJointRelationIdeal (q : MixedParams) (h : ℕ) :
    Ideal (AdjointSiteCoefficientRing q h)[X] :=
  Ideal.span {adjointSiteCharacteristic q h} ⊔ Ideal.span {X ^ (h + 1)} ⊔
    Ideal.span {Polynomial.C (Ideal.Quotient.mk _ (adjointSiteJointSymbol q)) * X ^ h}

/-- The cost of a block: the total weight `3^T 2^D` of its site words. -/
def adjointSiteBlockBound (B k : ℕ) (q : MixedParams) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u : AdjointSiteWord B k => adjointSiteWordBlock u = q),
    adjointSiteWordWeight u

/-- A joint relation flag in the coefficient ring of a block, of the block cost. -/
def AdjointSiteJointFlag (B k : ℕ) (q : MixedParams) : Prop :=
  Nonempty (MixedQuotientRelationFlag q (adjointSiteKernelIdeal q (B - k))
    (adjointSiteJointRelationIdeal q (B - k)) (adjointSiteBlockBound B k q))

/-- The block costs over any set of blocks sum to at most the total word weight. -/
theorem adjointSiteBlockBound_sum_le (B k : ℕ) (S : Finset MixedParams) :
    (∑ q ∈ S, adjointSiteBlockBound B k q) ≤ 15 * 20 ^ k * 6 ^ (B - 2 * k) := by
  classical
  rw [← adjointSiteWord_weight_sum B k]
  unfold adjointSiteBlockBound
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro u _
  rw [Finset.sum_ite_eq]
  split_ifs <;> omega

/-- The nested Levi indices inject into the valid blocks; their costs sum to the word total. -/
theorem adjointSiteNestedBlockBound_sum_le (B k : ℕ) :
    (∑ d ∈ radicalSupportedCounts 1 B 1,
      ∑ e ∈ mixedSecondSupportedCounts 1 B d,
        adjointSiteBlockBound B k (mixedLabelBlockParams 1 B d e.1 e.2)) ≤
          15 * 20 ^ k * 6 ^ (B - 2 * k) := by
  classical
  let t := (radicalSupportedCounts 1 B 1).sigma (mixedSecondSupportedCounts 1 B)
  have hs : (∑ x ∈ t, adjointSiteBlockBound B k (mixedCountIndexParams 1 B x)) =
      ∑ q ∈ t.image (mixedCountIndexParams 1 B), adjointSiteBlockBound B k q := by
    rw [Finset.sum_image (mixedCountIndexParams_injective 1 B).injOn]
  have he : (∑ d ∈ radicalSupportedCounts 1 B 1,
      ∑ e ∈ mixedSecondSupportedCounts 1 B d,
        adjointSiteBlockBound B k (mixedLabelBlockParams 1 B d e.1 e.2)) =
      ∑ x ∈ t, adjointSiteBlockBound B k (mixedCountIndexParams 1 B x) := by
    rw [Finset.sum_sigma]
    rfl
  rw [he, hs]
  exact adjointSiteBlockBound_sum_le B k _

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

set_option maxHeartbeats 400000 in
-- The case analysis unfolds the joint symbol over a nested quotient ring.
set_option synthInstance.maxHeartbeats 100000 in
/-- **The joint level relation.** On every block of `M(B, h)`, `F(h) π(s φ) = 0`: Σ₁(h) on
`(0, ·, 1)`, the flat relation L₂(h) on `(0, ·, 0)`, Theorem L₃(h) on `(1, ·, 1)`, and `s = 0` on
`(1, ·, 0)`. -/
theorem adjointSite_jointSymbol_lowering_zero (B h : ℕ) (hh : 0 < h)
    (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (ht : ∀ i s v, h + 1 ≤ s → ρ.op i s v = 0)
    (hg : ρ.op 9 h w = 0)
    (hflat : ∀ (d₂ e₁ e₂ : ℕ) (hv : MixedValid (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂))
      (φ : MixedRing (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂)),
      secondLeviQuotientLowering (radicalCountQuotCurrent ρ w ![0, d₂, 0])
          (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0]) e₁ e₂ h
        (mixedSecondLeviEvaluation ρ w 1 B hW ![0, d₂, 0] e₁ e₂ hv
          (adjointSiteFlatSymbol (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂) * φ)).val = 0)
    (d : Fin 3 → ℕ) (e₁ e₂ : ℕ) (hv : MixedValid (mixedLabelBlockParams 1 B d e₁ e₂))
    (φ : MixedRing (mixedLabelBlockParams 1 B d e₁ e₂)) :
    secondLeviQuotientLowering (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW d) e₁ e₂ h
      (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv
        (adjointSiteJointSymbol (mixedLabelBlockParams 1 B d e₁ e₂) * φ)).val = 0 := by
  obtain ⟨a₀, n, c₀, rfl⟩ : ∃ a₀ n c₀, d = ![a₀, n, c₀] :=
    ⟨d 0, d 1, d 2, by funext i; fin_cases i <;> rfl⟩
  have hd : a₀ ≤ 1 ∧ c₀ ≤ 1 := by
    simp [MixedValid, mixedLabelBlockParams] at hv
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd.1 with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd.2 with rfl | rfl
  · have hs : adjointSiteJointSymbol (mixedLabelBlockParams 1 B ![0, n, 0] e₁ e₂) =
        adjointSiteFlatSymbol (mixedLabelBlockParams 1 B ![0, n, 0] e₁ e₂) := by
      simp [adjointSiteJointSymbol, mixedLabelBlockParams]
    rw [hs]
    exact hflat n e₁ e₂ hv φ
  · have hs : adjointSiteJointSymbol (mixedLabelBlockParams 1 B ![0, n, 1] e₁ e₂) = 1 := by
      simp [adjointSiteJointSymbol, mixedLabelBlockParams]
    rw [hs, one_mul]
    exact adjointSite_unmarked_lowering_zero ρ w B hW h hh ht hg n e₁ e₂ hv φ
  · have hs : adjointSiteJointSymbol (mixedLabelBlockParams 1 B ![1, n, 0] e₁ e₂) = 0 := by
      simp [adjointSiteJointSymbol, mixedLabelBlockParams]
    rw [hs, zero_mul, map_zero, ZeroMemClass.coe_zero, map_zero]
  · have hs : adjointSiteJointSymbol (mixedLabelBlockParams 1 B ![1, n, 1] e₁ e₂) =
        adjointSiteMarkedSymbol (mixedLabelBlockParams 1 B ![1, n, 1] e₁ e₂) := by
      simp [adjointSiteJointSymbol, mixedLabelBlockParams]
    rw [hs]
    exact adjointSite_markedSymbol_lowering_zero ρ w B hW h hh ht hg n e₁ e₂ hv φ

set_option maxHeartbeats 400000 in
-- Both actual Levi quotients involve nested Grassmannian coefficient algebras.
set_option synthInstance.maxHeartbeats 100000 in
/-- A joint relation flag bounds the actual second Levi orbit of a one-adjoint-site block. -/
theorem adjointSiteSecondLeviOrbit_bound_of_jointFlag (B k : ℕ) (hk : 1 ≤ k)
    (hkB : 2 * k ≤ B) (hW : LocalWeylRel ρ w (weightABC 1 B 1))
    (ht : ∀ i s v, B - k + 1 ≤ s → ρ.op i s v = 0) (hg : ρ.op 9 (B - k) w = 0)
    (hflat : ∀ (d₂ e₁ e₂ : ℕ) (hv : MixedValid (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂))
      (φ : MixedRing (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂)),
      secondLeviQuotientLowering (radicalCountQuotCurrent ρ w ![0, d₂, 0])
          (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0]) e₁ e₂ (B - k)
        (mixedSecondLeviEvaluation ρ w 1 B hW ![0, d₂, 0] e₁ e₂ hv
          (adjointSiteFlatSymbol (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂) * φ)).val = 0)
    (d : Fin 3 → ℕ) (e₁ e₂ : ℕ) (hv : MixedValid (mixedLabelBlockParams 1 B d e₁ e₂))
    (hflag : AdjointSiteJointFlag B k (mixedLabelBlockParams 1 B d e₁ e₂)) :
    Module.finrank ℂ (secondLeviOrbit (radicalCountQuotCurrent ρ w d)
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW d) e₁ e₂) ≤
        adjointSiteBlockBound B k (mixedLabelBlockParams 1 B d e₁ e₂) := by
  have hh : 0 < B - k := by omega
  let Q := radicalCountQuotCurrent ρ w d
  let β := radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW d
  let q := mixedLabelBlockParams 1 B d e₁ e₂
  let π := (secondLeviMultiplicity Q β e₁ e₂).subtype.comp
    (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv)
  let q₀ := (a3KeyLabelInt B 1 1 ⟨d 0, d 1, d 2, 0⟩).toNat
  have hm := mixedLabelBlockParams_dominant 1 B d e₁ e₂ hv 1
  have hw : mixedWeight q = (q₀ : ℤ) + e₁ - e₂ := by
    dsimp only [q₀]
    rw [Int.toNat_of_nonneg hm]
    simp [q, mixedWeight, mixedQ, mixedLabelBlockParams, a3KeyLabelInt]
    ring
  have hwpos : 0 ≤ mixedWeight q := by
    have : MixedValid q := hv
    simp only [MixedValid] at this
    unfold mixedWeight
    omega
  have he : ∀ s φ, Q.op 1 s (β φ) = 0 :=
    fun s φ => radicalGrassmannianAmbientEvaluation_raising ρ w 1 B 1 hW d 1 s φ
  have hhw : ∀ φ, Q.op 7 0 (β φ) = (q₀ : ℂ) • β φ :=
    radicalGrassmannianAmbientEvaluation_weight ρ w 1 B 1 hW d 1 hm
  have hf : ∀ φ, (Q.op 4 0 ^ (q₀ + 1)) (β φ) = 0 :=
    radicalGrassmannianAmbientEvaluation_lowering ρ w 1 B 1 hW d 1 hm
  have hI : (adjointSiteKernelIdeal q (B - k)).restrictScalars ℂ ≤ LinearMap.ker π := by
    intro x hx
    have hz := adjointSite_kernelIdeal_le_kernel ρ w B hW (B - k) hh ht hg d e₁ e₂ hv hx
    change (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv x).val = 0
    rw [LinearMap.mem_ker.mp hz]
    rfl
  obtain ⟨flag⟩ := hflag
  have hb := mixedQuotientRingImage_bound_of_jointFlag q hv
    (secondLeviQuotient_currentRelations Q β e₁ e₂) π
    (adjointSiteKernelIdeal q (B - k)) hI (adjointSiteJointSymbol q) (B - k)
    (adjointSiteBlockBound B k q) flag
    (fun s φ => secondLeviMultiplicity_raising Q β he e₁ e₂ s
      (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv φ))
    (fun φ => by
      have hz := secondLeviMultiplicity_weight Q β q₀ hhw e₁ e₂
        (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv φ)
      rw [← hw] at hz
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hwpos]
      exact hz)
    (fun s hs φ => mixedSecondLeviEvaluation_cartan ρ w 1 B hW d e₁ e₂ hv s hs φ)
    (fun φ => by
      have hz := (secondLeviMultiplicity_lowering_sharp Q β q₀ he hhw hf e₁ e₂
        (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv φ)).2
      rw [← hw] at hz
      exact hz hwpos)
    (fun s hs φ => by
      obtain ⟨x, hx⟩ := (higherSecondLeviCountClosure Q β e₁ e₂).mkQ_surjective (π φ)
      rw [← hx]
      change (higherSecondLeviCountClosure Q β e₁ e₂).mkQ (Q.op 4 s x) = 0
      rw [radicalCountQuot_truncated ρ w (B - k + 1) ht d 4 s hs x, map_zero])
    (fun φ => adjointSite_jointSymbol_lowering_zero ρ w B (B - k) hh hW ht hg hflat d e₁ e₂ hv φ)
  have hr : Set.range π = (secondLeviMultiplicity Q β e₁ e₂ : Set _) := by
    ext x
    constructor
    · rintro ⟨φ, rfl⟩
      exact (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv φ).property
    · intro hx
      obtain ⟨φ, hφ⟩ := mixedSecondLeviEvaluation_surjective ρ w 1 B hW d e₁ e₂ hv ⟨x, hx⟩
      exact ⟨φ, congrArg Subtype.val hφ⟩
  rw [hr] at hb
  exact hb.2

set_option synthInstance.maxHeartbeats 100000 in
-- Both actual Levi filtrations use nested quotient coefficient algebras.
/-- Joint relation flags on every valid block bound every finite cyclic module with the relations
of `M(B, B - k)`. -/
theorem adjointSiteCyclic_rank_le_of_jointFlags [FiniteDimensional ℂ V] (B k : ℕ)
    (hk : 1 ≤ k) (hkB : 2 * k ≤ B) (hW : LocalWeylRel ρ w (weightABC 1 B 1))
    (ht : ∀ i s v, B - k + 1 ≤ s → ρ.op i s v = 0) (hg : ρ.op 9 (B - k) w = 0)
    (hflat : ∀ (d₂ e₁ e₂ : ℕ) (hv : MixedValid (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂))
      (φ : MixedRing (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂)),
      secondLeviQuotientLowering (radicalCountQuotCurrent ρ w ![0, d₂, 0])
          (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0]) e₁ e₂ (B - k)
        (mixedSecondLeviEvaluation ρ w 1 B hW ![0, d₂, 0] e₁ e₂ hv
          (adjointSiteFlatSymbol (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂) * φ)).val = 0)
    (hflags : ∀ q ∈ mixedValidBlocks 1 B, AdjointSiteJointFlag B k q) :
    Module.finrank ℂ (cycSubG ρ w) ≤ 15 * 20 ^ k * 6 ^ (B - 2 * k) := by
  apply le_trans (radicalCountFiltration_rank_le ρ w 1 B 1 hW
    (fun d => ∑ e ∈ mixedSecondSupportedCounts 1 B d,
      adjointSiteBlockBound B k (mixedLabelBlockParams 1 B d e.1 e.2)) ?_)
    (adjointSiteNestedBlockBound_sum_le B k)
  intro d hd
  rw [radicalCountClosure_map_eq_secondCounts ρ w 1 B 1 hW d]
  apply secondLeviFiltration_rank_le_of_orbit_bounds ρ w 1 B hW d
    ((mem_radicalSupportedCounts 1 B 1 d).mp hd) (adjointSiteBlockBound B k)
  intro e₁ e₂ hv
  exact adjointSiteSecondLeviOrbit_bound_of_jointFlag ρ w B k hk hkB hW ht hg hflat d e₁ e₂ hv
    (hflags _ ((mem_mixedValidBlocks 1 B _).mpr ⟨hv, rfl, rfl⟩))

/-- **Law B at one adjoint site from joint relation flags.** If every valid block carries a joint
relation flag of its word cost, then L₂(B - k) implies Law B. -/
theorem adjointSiteLawB_of_jointFlags (B k : ℕ) (hk : 1 ≤ k) (hkB : 2 * k ≤ B)
    (hflags : ∀ q ∈ mixedValidBlocks 1 B, AdjointSiteJointFlag B k q)
    (hL₂ : ZeroAdjointFlatRelation B k) : AdjointSiteLawB B k := by
  haveI := (adjointSiteModule_finite_and_local_bound B (B - k)).1
  obtain ⟨hW, -, hg⟩ := adjointSite_relations B (B - k)
  have ht : ∀ i s v, B - k + 1 ≤ s → (adjointSiteRep B (B - k)).op i s v = 0 :=
    fun i s v hs => adjointSiteModule_current_zero B (B - k) i s hs v
  have hb := adjointSiteCyclic_rank_le_of_jointFlags (adjointSiteRep B (B - k))
    (adjointSiteGenerator B (B - k)) B k hk hkB hW ht hg hL₂ hflags
  rw [presentedCurrent_cyclic, finrank_top] at hb
  exact ⟨inferInstance, hb⟩

/-- The remaining ring statement of §4–§5: the one-adjoint-site stratum count produces a joint
relation flag of the word cost on every valid block (the joint Theorem U/L with the stratum
filtration by the `G_j`). -/
def AdjointSiteJointFlagConstruction (B k : ℕ) : Prop :=
  OneAdjointStratumCount B k → ∀ q ∈ mixedValidBlocks 1 B, AdjointSiteJointFlag B k q

/-- **The conditional assembly of §6.** The target `AdjointSiteLawBFromResiduals` holds as soon
as the stratum count produces the joint relation flags. -/
theorem adjointSiteLawB_of_residuals_of_jointFlagConstruction (B k : ℕ) (hk : 1 ≤ k)
    (hkB : 2 * k ≤ B) (hU : AdjointSiteJointFlagConstruction B k) :
    AdjointSiteLawBFromResiduals B k :=
  fun hS hL₂ => adjointSiteLawB_of_jointFlags B k hk hkB (hU hS) hL₂

end

end VOA.DeligneAudit.SL4T
