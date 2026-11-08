import VOA.Moonshine.MoonshineLRGenerationTensor

/-!
# Cone-graded spaces: homogeneous bases and the character identity in dimension form

For a space graded by `ℕ × ℕ` with finite-dimensional pieces supported in the open cone, a
homogeneous basis with the counting data of `MoonshineLRGenerationCount` exists (`coneBasis`,
`coneLow`). It counts each degree `γ` exactly `dim wt γ` times (`basisDegCount_cone`).

**`coneProd_finrank_mul_one_sub_finrankSeries`**: if `L` is a cone-graded Lie algebra and
`S ⊆ L` is a cone-graded subspace with `T(S) ≃ U(L)` canonically, then
`Π_{m,n ≥ 1} (1 − pᵐ qⁿ)^{−dim L_(m,n)} · (1 − Σ_{a,b} dim S_(a,b) pᵃ q^b) = 1`.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open Module

section ConeBasis

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (wt : ℕ × ℕ → Submodule ℂ M) [DirectSum.Decomposition wt]
  [∀ γ, FiniteDimensional ℂ (wt γ)]

/-- Basis indices: a degree `γ` and a basis index of `wt γ`. -/
abbrev coneIndex : Type _ := Σ γ : ℕ × ℕ, Basis.ofVectorSpaceIndex ℂ (wt γ)

omit [∀ γ, FiniteDimensional ℂ (wt γ)] in
/-- The homogeneous basis collected from bases of the pieces. -/
def coneBasis : Basis (coneIndex wt) ℂ M :=
  (DirectSum.Decomposition.isInternal wt).collectedBasis fun γ => Basis.ofVectorSpace ℂ (wt γ)

omit [∀ γ, FiniteDimensional ℂ (wt γ)] in
theorem coneBasis_mem (k : coneIndex wt) : coneBasis wt k ∈ wt k.1 :=
  (DirectSum.Decomposition.isInternal wt).collectedBasis_mem _ k

omit [DirectSum.Decomposition wt] in
/-- The basis indices of degree `≤ Γ`. -/
def coneLow (Γ : ℕ × ℕ) : Finset (coneIndex wt) :=
  (Finset.Icc 0 Γ).sigma fun _ => Finset.univ

omit [DirectSum.Decomposition wt] in
theorem mem_coneLow (Γ : ℕ × ℕ) (k : coneIndex wt) : k ∈ coneLow wt Γ ↔ k.1 ≤ Γ := by
  simp only [coneLow, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_univ, and_true]
  exact and_iff_right (Prod.le_def.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩)

omit [DirectSum.Decomposition wt] [∀ γ, FiniteDimensional ℂ (wt γ)] in
/-- Degrees of basis vectors lie in the open cone when the pieces do. -/
theorem coneIndex_pos (hcone : ∀ γ : ℕ × ℕ, wt γ ≠ ⊥ → 1 ≤ γ.1 ∧ 1 ≤ γ.2)
    (k : coneIndex wt) : 1 ≤ k.1.1 ∧ 1 ≤ k.1.2 := by
  apply hcone
  intro h
  apply (Basis.ofVectorSpace ℂ (wt k.1)).ne_zero k.2
  exact Subtype.ext ((Submodule.eq_bot_iff _).mp h _ (Basis.ofVectorSpace ℂ (wt k.1) k.2).2)

omit [DirectSum.Decomposition wt] in
/-- The basis has `dim wt γ` vectors of degree `γ`. -/
theorem basisDegCount_cone (γ : ℕ × ℕ) :
    basisDegCount (fun k : coneIndex wt => k.1) (coneLow wt) γ = finrank ℂ (wt γ) := by
  classical
  rw [basisDegCount_eq_card_filter (fun k : coneIndex wt => k.1) (coneLow wt) (mem_coneLow wt)
    le_rfl]
  have h : (coneLow wt γ).filter (fun k => k.1 = γ) =
      ({γ} : Finset (ℕ × ℕ)).sigma fun _ => Finset.univ := by
    ext k
    simp only [Finset.mem_filter, mem_coneLow, Finset.mem_sigma, Finset.mem_singleton,
      Finset.mem_univ, and_true]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ le_rfl, h⟩⟩
  rw [h, Finset.card_sigma, Finset.sum_singleton, Finset.card_univ,
    ← finrank_eq_card_basis (Basis.ofVectorSpace ℂ (wt γ))]

omit [DirectSum.Decomposition wt] in
/-- `Σ_{a,b} dim wt (a,b) pᵃ q^b`. -/
def finrankSeries : PowerSeries (LaurentSeries ℂ) :=
  PowerSeries.mk fun a => HahnSeries.ofPowerSeries ℤ ℂ
    (PowerSeries.mk fun b => (finrank ℂ (wt (a, b)) : ℂ))

omit [DirectSum.Decomposition wt] in
theorem basisDegSeries_cone :
    basisDegSeries (fun k : coneIndex wt => k.1) (coneLow wt) = finrankSeries wt := by
  simp only [basisDegSeries, finrankSeries, basisDegCount_cone]

end ConeBasis

/-! ### Comparing exponents -/

theorem coneProd_zero : coneProd (fun _ _ => 0) = 1 := by
  have hL : coneLog (fun _ _ => (0 : ℂ)) = 0 := by
    refine PowerSeries.ext fun a => ?_
    rw [coneLog, PowerSeries.coeff_mk, coneLogCoeff, map_zero]
    simp [ofPowerSeries_mk_zero]
  refine (eq_of_ode (constantCoeff_coneLog _) (coneProd_spec _) ?_ ?_)
  · rw [hL, mul_zero, Derivation.map_one_eq_zero, mul_zero]
  · rw [constantCoeff_coneProd, map_one]

/-- **The sandwich step on series:** if `Π (1 − pᵐ qⁿ)^{−d} · (1 − X) = 1` and
`Π (1 − pᵐ qⁿ)^{c} = 1 − X`, then `c = d` on `m, n ≥ 1`. -/
theorem eq_of_coneProd_neg_mul_eq_one {c d : ℕ → ℕ → ℂ} {X : PowerSeries (LaurentSeries ℂ)}
    (h₁ : coneProd (fun m n => -d m n) * (1 - X) = 1) (h₂ : coneProd c = 1 - X) :
    ∀ m n : ℕ, 0 < m → 0 < n → c m n = d m n := by
  have h : coneProd (c + fun m n => -d m n) = coneProd (fun _ _ => 0) := by
    rw [coneProd_add, h₂, mul_comm, h₁, coneProd_zero]
  intro m n hm hn
  have := coneProd_exponent_unique h m n hm hn
  simp only [Pi.add_apply] at this
  exact (add_neg_eq_zero.mp this)

/-! ### Homogeneous submodules inherit the grading -/

section Homogeneous

variable {ι M : Type*} [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

/-- If `p` is the span of its homogeneous pieces `p ⊓ A i` for an independent family `A`, the
pieces `(A i).comap p.subtype` form an internal direct sum decomposition of `p`. -/
theorem isInternal_comap_of_le_iSup_inf {A : ι → Submodule ℂ M} (hA : iSupIndep A)
    (p : Submodule ℂ M) (hp : p ≤ ⨆ i, p ⊓ A i) :
    DirectSum.IsInternal fun i => (A i).comap p.subtype := by
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨?_, ?_⟩
  · let e : Submodule ℂ p ≃o Set.Iic p := p.mapIic
    have he : (e ∘ fun i => (A i).comap p.subtype) =
        fun i => ⟨p ⊓ A i, Set.mem_Iic.mpr inf_le_left⟩ := by
      ext i m
      change m ∈ ((A i).comap p.subtype).map p.subtype ↔ _
      rw [Submodule.map_comap_subtype]
    rw [← iSupIndep_map_orderIso_iff e, he]
    exact iSupIndep.of_coe_Iic_comp (hA.mono fun i => inf_le_right)
  · apply Submodule.map_injective_of_injective p.injective_subtype
    rw [Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype]
    refine le_antisymm (iSup_le fun i => ?_) ?_
    · rw [Submodule.map_comap_subtype]
      exact inf_le_left
    · refine hp.trans (iSup_mono fun i => ?_)
      rw [Submodule.map_comap_subtype]

end Homogeneous

/-! ### The character identity in dimension form -/

section Character

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

theorem ne_bot_of_ne_bot_of_mem {S : Submodule ℂ L} (wtS : ℕ × ℕ → Submodule ℂ S)
    (wt : ℕ × ℕ → Submodule ℂ L) (hS : ∀ γ (x : S), x ∈ wtS γ → (x : L) ∈ wt γ) (γ : ℕ × ℕ)
    (h : wtS γ ≠ ⊥) : wt γ ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp h
  rw [Submodule.ne_bot_iff]
  exact ⟨x, hS γ x hx, fun h0 => hx0 (Subtype.ext h0)⟩

/-- **The PBW character in dimension form (blueprint: the character identity in `MOON_BKM`):**
`Π_{m,n ≥ 1} (1 − pᵐ qⁿ)^{−dim L_(m,n)} · (1 − Σ dim S_(a,b) pᵃ q^b) = 1`. -/
theorem coneProd_finrank_mul_one_sub_finrankSeries
    (wt : ℕ × ℕ → Submodule ℂ L) [DirectSum.Decomposition wt] [∀ γ, FiniteDimensional ℂ (wt γ)]
    (hcone : ∀ γ : ℕ × ℕ, wt γ ≠ ⊥ → 1 ≤ γ.1 ∧ 1 ≤ γ.2)
    (hbr : ∀ {γ δ : ℕ × ℕ} {x y : L}, x ∈ wt γ → y ∈ wt δ → ⁅x, y⁆ ∈ wt (γ + δ))
    {S : Submodule ℂ L} (hτ : Function.Bijective (tensorGeneratorToEnveloping S))
    (wtS : ℕ × ℕ → Submodule ℂ S) [DirectSum.Decomposition wtS]
    [∀ γ, FiniteDimensional ℂ (wtS γ)]
    (hS : ∀ γ (x : S), x ∈ wtS γ → (x : L) ∈ wt γ) :
    coneProd (fun m n => -(finrank ℂ (wt (m, n)) : ℂ)) * (1 - finrankSeries wtS) = 1 := by
  classical
  letI : LinearOrder (coneIndex wt) := WellOrderingRel.isWellOrder.linearOrder
  have h := coneProd_mul_one_sub_basisDegSeries wt hbr hτ (coneBasis wtS) (fun k => k.1)
    (fun k => hS k.1 _ (coneBasis_mem wtS k))
    (coneIndex_pos wtS (fun γ h => hcone γ (ne_bot_of_ne_bot_of_mem wtS wt hS γ h)))
    (coneLow wtS) (mem_coneLow wtS) (coneBasis wt) (fun k => k.1) (coneBasis_mem wt)
    (coneIndex_pos wt hcone) (coneLow wt) (mem_coneLow wt)
  rw [basisDegSeries_cone] at h
  simpa only [basisDegCount_cone] using h

end Character

end VOA.Moonshine.ConwayNorton.M8
