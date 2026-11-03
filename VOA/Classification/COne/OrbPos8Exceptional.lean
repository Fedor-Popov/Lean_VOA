import VOA.Classification.COne.OrbPos8Spectrum

/-! # Exceptional positivity from DRX alone

The spectral inclusion proved for arbitrary twisted modules is weaker than
full lattice-module classification, but is sufficient for the unchanged B5.
DRX completeness remains an explicit hypothesis.
-/

namespace VOA.Classification.COne.OrbPos8
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet HeisenbergN
open OrbPos OrbPos2 OrbPos3 OrbPos5 LatMod

/-- Every nonidentity finite-period torus element has a normalized shift angle. -/
theorem torus_eq_shiftAut (u : ℂˣ) {n : ℕ} (hn : 0 < n)
    (hp : (charU 1 le_rfl u) ^ n = 1) (hu : charU 1 le_rfl u ≠ 1) :
    ∃ a : ℤ, 0 < a ∧ a < n ∧ charU 1 le_rfl u = shiftAut n a := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hpow : u ^ n = 1 := charU_injective 1 le_rfl (by simpa using hp)
  have hc : (u : ℂ) ^ n = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hpow
  obtain ⟨i, hin, hi⟩ := (Complex.isPrimitiveRoot_exp n hn.ne').eq_pow_of_pow_eq_one hc
  have hei : phase n (i : ℤ) = (u : ℂ) := by
    rw [← hi, phase, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hue : u = torusUnit n i := by
    apply Units.ext
    exact hei.symm
  have hip : 0 < i := by
    by_contra h
    have hi0 : i = 0 := by omega
    subst i
    have h1 : u = 1 := by apply Units.ext; simpa [phase] using hei.symm
    exact hu (by rw [h1, map_one])
  exact ⟨i, by omega, by omega, by rw [hue]; rfl⟩

/-- Changing an equal automorphism index preserves the carried weight spaces. -/
noncomputable def castTwisted {g g' : Aut (V2m 1 le_rfl)} {n : ℕ}
    {M : Type} [AddCommGroup M] [Module ℂ M] (he : g = g')
    (P : TwistedModule g n M) : TwistedModule g' n M := he ▸ P

theorem castTwisted_weight {g g' : Aut (V2m 1 le_rfl)} {n : ℕ}
    {M : Type} [AddCommGroup M] [Module ℂ M] (he : g = g')
    (P : TwistedModule g n M) (α : ℂ) :
    (castTwisted he P).weight α = P.weight α := by
  subst g'
  rfl

/-- Spectral inclusion for every nonidentity finite-order V₂ sector.
The angle is uniform, while the integral label may depend on the weight. -/
theorem inner_twisted_weight_spectrum {g : Aut (V2m 1 le_rfl)} {n : ℕ}
    (hn : 0 < n) (ho : orderOf g = n) (hg : g ≠ 1)
    {M : Type} [AddCommGroup M] [Module ℂ M] (P : TwistedModule g n M)
    (hi : TwistedIrreducible P) :
    ∃ a : ℤ, 0 < a ∧ a < n ∧ ∀ α : ℂ, P.weight α ≠ ⊥ →
      ∃ (b : ℤ) (r : ℕ), α = (innerEnergy n a b 0 r : ℂ) := by
  obtain ⟨u, Q, hQord, _, hQweight⟩ := v2_twisted_torus_reduction hn ho P hi
  have hu : charU 1 le_rfl u ≠ 1 := by
    intro h
    have hn1 : n = 1 := by simpa [h] using hQord.symm
    exact hg (orderOf_eq_one_iff.mp (ho.trans hn1))
  obtain ⟨a, ha, han, he⟩ := torus_eq_shiftAut u hn
    (by rw [← hQord]; exact pow_orderOf_eq_one _) hu
  refine ⟨a, ha, han, fun α hα => ?_⟩
  have hw : Q.weight α ≠ ⊥ := by rwa [hQweight]
  have hw' : (castTwisted he Q).weight α ≠ ⊥ := by
    rw [castTwisted_weight he Q α]
    exact hw
  exact shifted_weight_spectrum (a := a) (castTwisted he Q) hn hw'

/-- Unconditional positive gap for every irreducible nonidentity sector
of order at most five. -/
theorem inner_twisted_weight_gap {g : Aut (V2m 1 le_rfl)} {n : ℕ}
    (hn : 0 < n) (ho : orderOf g = n) (hg : g ≠ 1) (hn5 : n ≤ 5)
    {M : Type} [AddCommGroup M] [Module ℂ M] (P : TwistedModule g n M)
    (hi : TwistedIrreducible P) {α : ℂ} (hα : P.weight α ≠ ⊥) :
    (1 : ℝ) / 100 ≤ α.re := by
  obtain ⟨a, ha, han, hs⟩ := inner_twisted_weight_spectrum hn ho hg P hi
  obtain ⟨b, r, rfl⟩ := hs α hα
  exact innerEnergy_gap hn5 ha han b 0 r

/-- DRX alone supplies the original exceptional lowest-weight spectrum residual. -/
theorem exceptionalLowestWeightSpectrum_of_drx (hDRX : ExceptionalDRXEmbedding) :
    ExceptionalLowestWeightSpectrum := by
  intro G hG hSR M _ _ N hi α _ hα
  rcases hDRX G hG hSR M N hi with h | h
  · obtain ⟨T, _, _, P, hP, f, hf, hfi⟩ := h
    have hw := weight_ne_bot_of_embedding N _ f hf hfi hα
    obtain ⟨j, r, he⟩ := v2_ordinary_weight_spectrum P hP hw
    exact ⟨1, j, r, by omega, by omega, he⟩
  · obtain ⟨g, n, hn, ho, hg, T, _, _, P, hP, f, hf, hfi⟩ := h
    have hw := weight_ne_bot_of_embedding N _ f hf hfi hα
    obtain ⟨a, _, _, hs⟩ := inner_twisted_weight_spectrum hn ho hg P hP
    obtain ⟨b, r, he⟩ := hs α hw
    refine ⟨n, (n : ℤ) * (2 * 0 + b) - a, r, hn,
      ho ▸ (exceptional_element_order_bounds hG g).2, ?_⟩
    exact he.trans (innerEnergy_eq_cyclicWeight hn a b 0 r)

/-- Zero energy forces an untwisted ambient vacuum embedding; the twisted
alternative is excluded by the newly proved gap. -/
theorem exceptionalZeroWeightEmbedding_of_drx (hDRX : ExceptionalDRXEmbedding) :
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
    have hp := inner_twisted_weight_gap hn ho hg
      (ho ▸ (exceptional_element_order_bounds hG g).2) P hP hw
    norm_num at hp

/-- The B5 target from the DRX completeness input alone. -/
theorem exceptionalOrbifoldPositiveWeightsFact_of_drx
    (hDRX : ExceptionalDRXEmbedding) : ExceptionalOrbifoldPositiveWeightsFact :=
  exceptionalOrbifoldPositiveWeightsFact_of_spectrum_embedding
    (exceptionalLowestWeightSpectrum_of_drx hDRX) (exceptionalZeroWeightEmbedding_of_drx hDRX)

end VOA.Classification.COne.OrbPos8
