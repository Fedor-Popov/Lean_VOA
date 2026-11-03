import VOA.Classification.COne.OrbPos2Restriction
import VOA.Classification.COne.OrbPos2Weights
import VOA.Classification.COne.OrbPosUntwisted
import VOA.Classification.COne.DistinctResiduals

/-!
# The precise representation-theoretic obligations for the inner-twist route

`ExceptionalDRXEmbedding` is the specialization of Dong--Ren--Xu Theorem 3.3
and Remark 3.4 (arXiv:1507.03306v2) to strongly rational exceptional orbifolds.
Its untwisted alternative uses an actual ordinary V₂-module. Its other
alternative uses an actual irreducible twisted module and an intertwining
injection into its constructed restriction. It contains no positivity claim.

`V2InnerTwistedSpectrum` is only the spectral consequence of Li's construction
and its inverse (q-alg/9504022, Proposition 5.4), with the two level-one charge
cosets. It contains neither an orbifold-completeness claim nor vacuum uniqueness.
Both propositions remain unproved. Their consequences below are proved.
-/

namespace VOA.Classification.COne.OrbPos2
open VOA VertexOperatorAlgebra OrbPos VOA.Huang.FusionUnit VOA.LatGen.Triplet LatMod

private theorem orderOf_le_five_of_cases {H : Type*} [Group H] (g : H)
    (h : g = 1 ∨ g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 4 = 1 ∨ g ^ 5 = 1) :
    orderOf g ≤ 5 := by
  rcases h with h | h | h | h | h
  · simp [h]
  all_goals
    have := orderOf_le_of_pow_eq_one (by decide) h
    omega

/-- Actual element orders in every exceptional subgroup are between one and five. -/
theorem exceptional_element_order_bounds
    {G : Subgroup (Aut (V2m 1 le_rfl))} (hG : IsExceptionalV2Group G) (g : G) :
    0 < orderOf g.1 ∧ orderOf g.1 ≤ 5 := by
  letI := exceptionalV2Group_finite hG
  rw [show orderOf g.1 = orderOf g from orderOf_injective G.subtype Subtype.val_injective g]
  refine ⟨orderOf_pos g, ?_⟩
  rcases hG with h | h | h
  · obtain ⟨e⟩ := h
    rw [← e.orderOf_eq g]
    exact orderOf_le_five_of_cases _ (A4_all (e g))
  · obtain ⟨e⟩ := h
    rw [← e.orderOf_eq g]
    exact orderOf_le_five_of_cases _ (S4_all (e g))
  · obtain ⟨e⟩ := h
    rw [← e.orderOf_eq g]
    exact orderOf_le_five_of_cases _ (A5_all (e g))

/-- The library's torus-conjugacy theorem applies to each actual exceptional element. -/
theorem exceptional_element_conjugate_torus
    {G : Subgroup (Aut (V2m 1 le_rfl))} (hG : IsExceptionalV2Group G) (g : G) :
    ∃ (φ : Aut (V2m 1 le_rfl)) (u : ℂˣ),
      φ * g.1 * φ⁻¹ = charU 1 le_rfl u :=
  exists_conj_charU g.1
    (orderOf_pos_iff.mp (exceptional_element_order_bounds hG g).1)

/-- Open Li spectral consequence for nonidentity finite-order inner twists of V₂.
Only realized weights of actual irreducible twisted modules are quantified.
The angle numerator and charge-coset label can be chosen uniformly for the module.
The sign of the angle can be absorbed by replacing `a` with `n-a` and relabeling.
-/
def V2InnerTwistedSpectrum : Prop :=
  ∀ (g : Aut (V2m 1 le_rfl)) (n : ℕ), 0 < n → orderOf g = n → g ≠ 1 →
    ∀ (T : Type) [AddCommGroup T] [Module ℂ T] (P : TwistedModule g n T),
      TwistedIrreducible P →
      ∃ (a ε : ℤ), 0 < a ∧ a < n ∧ (ε = 0 ∨ ε = 1) ∧
        ∀ α : ℂ, P.weight α ≠ ⊥ →
          ∃ (k : ℤ) (r : ℕ), α = (innerEnergy n a ε k r : ℂ)

/-- Open DRX completeness, split at the identity twist. The second alternative
keeps the automorphism, its exact order, all fractional modes, and the module map.
Strong rationality of the fixed algebra is retained explicitly. -/
def ExceptionalDRXEmbedding : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))), IsExceptionalV2Group G →
    StronglyRational (orbifoldVOA G) →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (N : OrdVModule (orbifoldVOA G) M),
      N.IsIrreducible →
      (∃ (T : Type) (_ : AddCommGroup T) (_ : Module ℂ T)
          (P : OrdVModule (V2m 1 le_rfl) T), P.IsIrreducible ∧
        ∃ f : M →ₗ[ℂ] T,
          f ∈ homSpace N ((orbifold G).restrictOrdVModule P) ∧ Function.Injective f) ∨
      (∃ (g : G) (n : ℕ) (hn : 0 < n), orderOf g.1 = n ∧ g.1 ≠ 1 ∧
        ∃ (T : Type) (_ : AddCommGroup T) (_ : Module ℂ T)
          (P : TwistedModule g.1 n T), TwistedIrreducible P ∧
          ∃ f : M →ₗ[ℂ] T,
            f ∈ homSpace N (orbifoldRestriction G g P hn) ∧ Function.Injective f)

universe u

/-- Realized weights transfer along injective ordinary-module maps. -/
theorem weight_ne_bot_of_embedding
    {V M T : Type u} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T]
    {W : VertexOperatorAlgebra V} (N : OrdVModule W M) (P : OrdVModule W T)
    (f : M →ₗ[ℂ] T) (hf : f ∈ homSpace N P) (hfi : Function.Injective f)
    {α : ℂ} (hα : N.weight α ≠ ⊥) : P.weight α ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα
  intro he
  have hfx := hom_mem_weight hf hx
  rw [he, Submodule.mem_bot] at hfx
  exact hx0 (hfi (hfx.trans (map_zero f).symm))

/-- The untwisted part of the required spectrum theorem is unconditional. -/
theorem v2_ordinary_weight_spectrum
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (V2m 1 le_rfl) M) (hi : N.IsIrreducible)
    {α : ℂ} (hα : N.weight α ≠ ⊥) :
    ∃ (j : ℤ) (r : ℕ), α = CyclicWeight 1 j r := by
  obtain ⟨j, ⟨e⟩⟩ := exists_latticeModule_equiv_int N hi
  obtain ⟨r, k, he⟩ := latticeModule_weight_ne_bot 1 le_rfl j
    (moduleEquiv_weight_ne_bot e hα)
  refine ⟨2 * k + j, r, he.trans ?_⟩
  unfold CyclicWeight
  apply congrArg (fun x : ℝ => (x : ℂ))
  push_cast
  ring

/-- Li's spectral consequence rules out weight zero in every nonidentity sector. -/
theorem nonidentity_twisted_weight_gap (hLi : V2InnerTwistedSpectrum)
    (g : Aut (V2m 1 le_rfl)) (n : ℕ) (hn : 0 < n) (ho : orderOf g = n)
    (hg : g ≠ 1) (hn5 : n ≤ 5)
    {T : Type} [AddCommGroup T] [Module ℂ T] (P : TwistedModule g n T)
    (hi : TwistedIrreducible P) {α : ℂ} (hα : P.weight α ≠ ⊥) :
    (1 : ℝ) / 100 ≤ α.re := by
  obtain ⟨a, ε, ha, han, _, hs⟩ := hLi g n hn ho hg T P hi
  obtain ⟨k, r, rfl⟩ := hs α hα
  exact innerEnergy_gap hn5 ha han ε k r

/-- DRX plus the Li spectral calculation proves the spectrum residual
`ExceptionalLowestWeightSpectrum`. -/
theorem exceptionalLowestWeightSpectrum_of_drx_li
    (hDRX : ExceptionalDRXEmbedding) (hLi : V2InnerTwistedSpectrum) :
    ExceptionalLowestWeightSpectrum := by
  intro G hG hSR M _ _ N hi α _ hα
  rcases hDRX G hG hSR M N hi with h | h
  · obtain ⟨T, _, _, P, hP, f, hf, hfi⟩ := h
    have hw := weight_ne_bot_of_embedding N _ f hf hfi hα
    obtain ⟨j, r, he⟩ := v2_ordinary_weight_spectrum P hP hw
    exact ⟨1, j, r, by omega, by omega, he⟩
  · obtain ⟨g, n, hn, ho, hg, T, _, _, P, hP, f, hf, hfi⟩ := h
    have hw := weight_ne_bot_of_embedding N _ f hf hfi hα
    obtain ⟨a, ε, _, _, _, hs⟩ := hLi g.1 n hn ho hg T P hP
    obtain ⟨k, r, he⟩ := hs α hw
    exact ⟨n, (n : ℤ) * (2 * k + ε) - a, r, hn,
      ho ▸ (exceptional_element_order_bounds hG g).2,
      he.trans (innerEnergy_eq_cyclicWeight hn a ε k r)⟩

/-- No separate vacuum-uniqueness input is needed: zero forces an untwisted
ambient vacuum sector, where the existing adjoint-embedding theorem applies. -/
theorem exceptionalZeroWeightEmbedding_of_drx_li
    (hDRX : ExceptionalDRXEmbedding) (hLi : V2InnerTwistedSpectrum) :
    ExceptionalZeroWeightEmbedding := by
  intro G hG hSR M _ _ N hi h0
  rcases hDRX G hG hSR M N hi with h | h
  · obtain ⟨T, _, _, P, hP, f, hf, hfi⟩ := h
    have hw := weight_ne_bot_of_embedding N _ f hf hfi h0
    have he : Nonempty (ModuleEquiv (V2m 1 le_rfl) P (adjointModule (V2m 1 le_rfl))) := by
      by_contra he
      have hp := V2m_pseudoUnitary 1 le_rfl T P hP ⟨fun e => he ⟨e⟩⟩ 0 hw
      simp at hp
    obtain ⟨e⟩ := he
    refine ⟨e.toLinearEquiv.toLinearMap.comp f, ?_, e.toLinearEquiv.injective.comp hfi⟩
    intro v k x
    exact (congrArg e.toLinearEquiv (hf v k x)).trans (e.map_act v.1 k (f x))
  · obtain ⟨g, n, hn, ho, hg, T, _, _, P, hP, f, hf, hfi⟩ := h
    have hw := weight_ne_bot_of_embedding N _ f hf hfi h0
    have hp := nonidentity_twisted_weight_gap hLi g.1 n hn ho hg
      (ho ▸ (exceptional_element_order_bounds hG g).2) P hP hw
    norm_num at hp

/-- Both original B5 residuals follow from the two explicit representation-theoretic inputs. -/
theorem exceptional_residuals_of_drx_li
    (hDRX : ExceptionalDRXEmbedding) (hLi : V2InnerTwistedSpectrum) :
    ExceptionalLowestWeightSpectrum ∧ ExceptionalZeroWeightVacuum :=
  ⟨exceptionalLowestWeightSpectrum_of_drx_li hDRX hLi,
    exceptionalZeroWeightVacuum_of_embedding (exceptionalZeroWeightEmbedding_of_drx_li hDRX hLi)⟩

/-- Conditional B5 endpoint. Neither input is asserted as a theorem. -/
theorem exceptionalOrbifoldPositiveWeightsFact_of_drx_li
    (hDRX : ExceptionalDRXEmbedding) (hLi : V2InnerTwistedSpectrum) :
    ExceptionalOrbifoldPositiveWeightsFact :=
  exceptionalOrbifoldPositiveWeightsFact_of_spectrum_embedding
    (exceptionalLowestWeightSpectrum_of_drx_li hDRX hLi)
    (exceptionalZeroWeightEmbedding_of_drx_li hDRX hLi)

/-- The quantitative B5 endpoint for every realized non-vacuum weight. -/
theorem exceptional_weights_gap_of_drx_li
    (hDRX : ExceptionalDRXEmbedding) (hLi : V2InnerTwistedSpectrum)
    (G : Subgroup (Aut (V2m 1 le_rfl))) (hG : IsExceptionalV2Group G)
    (hSR : StronglyRational (orbifoldVOA G))
    (M : Type) [AddCommGroup M] [Module ℂ M] (N : OrdVModule (orbifoldVOA G) M)
    (hi : N.IsIrreducible)
    (hn : IsEmpty (ModuleEquiv (orbifoldVOA G) N (adjointModule (orbifoldVOA G))))
    (α : ℂ) (hα : N.weight α ≠ ⊥) : (1 : ℝ) / 100 ≤ α.re :=
  exceptional_weights_gap_of_residuals (exceptional_residuals_of_drx_li hDRX hLi).1
    (exceptional_residuals_of_drx_li hDRX hLi).2 G hG hSR M N hi hn α hα

end VOA.Classification.COne.OrbPos2
