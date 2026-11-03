import VOA.DeligneAudit.D4FusionToroidalFusionUZero

/-!
# Rank of the coadjoint part of the fusion associated graded

The graded image of a filtered subspace has rank no greater than the
source subspace. Applied to the pure coadjoint tensor, this gives `n^N`.
-/

namespace VOA.DeligneAudit.Toroidal.FusionGr

open VOA.DeligneAudit.Toroidal VOA.DeligneAudit.D1TensorG
open VOA.DeligneAudit.DeligneSector

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (A : ToroidalAction f V) (w : V) (U : Submodule ℂ V)

def subFbelow (d : ℕ) : Submodule ℂ V := evalFbelow A w d ⊓ U

/-- The image of the induced filtration on `U` in the ambient associated graded. -/
def subGr : Submodule ℂ (Gr A w) :=
  Submodule.span ℂ {v | ∃ d x, ∃ hx : x ∈ evalFbelow A w (d + 1),
    x ∈ U ∧ v = (kernel A w).mkQ (single A w d x hx)}

def subSymbol (d : ℕ) : subFbelow A w U (d + 1) →ₗ[ℂ] Gr A w :=
  symbol A w d ∘ₗ (subFbelow A w U (d + 1)).inclusion inf_le_left

theorem subSymbol_apply (d : ℕ) (x : subFbelow A w U (d + 1)) :
    subSymbol A w U d x = (kernel A w).mkQ
      (single A w d x.1 x.2.1) := rfl

def subPieceSum (B : ℕ) :
    (Π d : Fin B, subFbelow A w U (d.val + 1)) →ₗ[ℂ] Gr A w where
  toFun v := ∑ d : Fin B, subSymbol A w U d.val (v d)
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.smul_sum]

theorem subPieceSum_single (B : ℕ) (d : Fin B)
    (x : subFbelow A w U (d.val + 1)) :
    subPieceSum A w U B (Pi.single d x) = subSymbol A w U d.val x := by
  change (∑ e : Fin B,
    subSymbol A w U e.val ((Pi.single d x : Π j : Fin B,
      subFbelow A w U (j.val + 1)) e)) = _
  rw [Finset.sum_eq_single d]
  · simp
  · intro e _ hed
    have he : (Pi.single d x : Π j : Fin B,
      subFbelow A w U (j.val + 1)) e = 0 := by simp [hed]
    rw [he, map_zero]
  · simp

theorem subPieceSum_range (B : ℕ) (hB : evalFbelow A w B = ⊤) :
    LinearMap.range (subPieceSum A w U B) = subGr A w U := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    change (∑ d : Fin B, subSymbol A w U d.val (v d)) ∈ subGr A w U
    apply Submodule.sum_mem
    intro d _
    apply Submodule.subset_span
    exact ⟨d.val, (v d).1, (v d).2.1, (v d).2.2,
      subSymbol_apply A w U d (v d)⟩
  · rw [subGr, Submodule.span_le]
    rintro _ ⟨d, x, hx, hU, rfl⟩
    by_cases hd : d < B
    · let j : Fin B := ⟨d, hd⟩
      let y : subFbelow A w U (j.val + 1) := ⟨x, ⟨hx, hU⟩⟩
      exact ⟨Pi.single j y, by rw [subPieceSum_single]; rfl⟩
    · have hBd : evalFbelow A w d = ⊤ := by
        apply top_unique
        rw [← hB]
        exact evalFbelow_mono A w (Nat.le_of_not_lt hd)
      have hlow : x ∈ evalFbelow A w d := by rw [hBd]; trivial
      have hker : single A w d x hx ∈ kernel A w :=
        Submodule.subset_span ⟨d, x, hlow, rfl⟩
      have hz : (kernel A w).mkQ (single A w d x hx) = 0 :=
        (Submodule.Quotient.mk_eq_zero (kernel A w)).mpr hker
      rw [hz]
      exact Submodule.zero_mem _

def subLowerEmbed (B : ℕ) :
    (Π d : Fin B, subFbelow A w U d.val) →ₗ[ℂ]
      (Π d : Fin B, subFbelow A w U (d.val + 1)) where
  toFun v d := ⟨(v d).1, ⟨evalFbelow_mono A w (Nat.le_succ _) (v d).2.1,
    (v d).2.2⟩⟩
  map_add' _ _ := by funext d; apply Subtype.ext; rfl
  map_smul' _ _ := by funext d; apply Subtype.ext; rfl

theorem subLowerEmbed_injective (B : ℕ) :
    Function.Injective (subLowerEmbed A w U B) := by
  intro v u h
  funext d
  apply Subtype.ext
  exact congrArg (fun x => (x d : V)) h

theorem subPieceSum_lower_zero (B : ℕ)
    (v : Π d : Fin B, subFbelow A w U d.val) :
    subPieceSum A w U B (subLowerEmbed A w U B v) = 0 := by
  change (∑ d : Fin B, subSymbol A w U d.val (subLowerEmbed A w U B v d)) = 0
  apply Finset.sum_eq_zero
  intro d _
  rw [subSymbol_apply]
  apply (Submodule.Quotient.mk_eq_zero (kernel A w)).mpr
  exact Submodule.subset_span ⟨d.val, (v d).1, (v d).2.1, rfl⟩

theorem subRank_tel [FiniteDimensional ℂ V] (B : ℕ) :
    (∑ d ∈ Finset.range B, Module.finrank ℂ (subFbelow A w U (d + 1))) =
      (∑ d ∈ Finset.range B, Module.finrank ℂ (subFbelow A w U d)) +
        Module.finrank ℂ (subFbelow A w U B) := by
  induction B with
  | zero => rw [show subFbelow A w U 0 = ⊥ by
      simp [subFbelow, evalFbelow_zero A w]]; simp
  | succ B ih =>
      simp only [Finset.sum_range_succ]
      omega

theorem finrank_subGr_le [FiniteDimensional ℂ V] (B : ℕ)
    (hB : evalFbelow A w B = ⊤) :
    FiniteDimensional ℂ (subGr A w U) ∧
      Module.finrank ℂ (subGr A w U) ≤ Module.finrank ℂ U := by
  have hrange := subPieceSum_range A w U B hB
  letI : FiniteDimensional ℂ (subGr A w U) := by rw [← hrange]; infer_instance
  have hker : LinearMap.range (subLowerEmbed A w U B) ≤
      LinearMap.ker (subPieceSum A w U B) := by
    rintro _ ⟨v, rfl⟩
    exact subPieceSum_lower_zero A w U B v
  have hle := Submodule.finrank_mono hker
  rw [LinearMap.finrank_range_of_inj (subLowerEmbed_injective A w U B)] at hle
  rw [Module.finrank_pi_fintype] at hle
  have hrank := (subPieceSum A w U B).finrank_range_add_finrank_ker
  rw [hrange, Module.finrank_pi_fintype] at hrank
  have hsum : (∑ d : Fin B, Module.finrank ℂ (subFbelow A w U (d.val + 1))) =
      (∑ d : Fin B, Module.finrank ℂ (subFbelow A w U d.val)) +
        Module.finrank ℂ U := by
    calc
      _ = ∑ d ∈ Finset.range B,
          Module.finrank ℂ (subFbelow A w U (d + 1)) :=
        Fin.sum_univ_eq_sum_range _ B
      _ = (∑ d ∈ Finset.range B, Module.finrank ℂ (subFbelow A w U d)) +
          Module.finrank ℂ (subFbelow A w U B) := subRank_tel A w U B
      _ = (∑ d : Fin B, Module.finrank ℂ (subFbelow A w U d.val)) +
          Module.finrank ℂ U := by
        have hUB : subFbelow A w U B = U := by simp [subFbelow, hB]
        rw [hUB]
        exact congrArg (fun q => q + Module.finrank ℂ U)
          (Fin.sum_univ_eq_sum_range
            (fun d => Module.finrank ℂ (subFbelow A w U d)) B).symm
  exact ⟨inferInstance, by omega⟩

end

end VOA.DeligneAudit.Toroidal.FusionGr

namespace VOA.DeligneAudit.Toroidal.FusionGr

open VOA.DeligneAudit.Toroidal VOA.DeligneAudit.D1TensorG
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable (S : DeligneSectorData)
variable (hskew : ∀ a b c, S.f a b c = -S.f b a c)
variable {N : ℕ} (z : Fin N → ℂ)

/-- The associated graded image of the pure coadjoint tensor. -/
def evalUZeroGr : Submodule ℂ
    (Gr (d1EvalAction S.f S.jacobi hskew z) (D1TensorG.generator S.c₀)) :=
  subGr (d1EvalAction S.f S.jacobi hskew z) (D1TensorG.generator S.c₀)
    (LinearMap.range (FusionUZero.embedCo S.n N))

theorem evalUZeroGr_rank_le (hz : Function.Injective z) :
    FiniteDimensional ℂ (evalUZeroGr S hskew z) ∧
      Module.finrank ℂ (evalUZeroGr S hskew z) ≤ S.n ^ N := by
  obtain ⟨B, hB⟩ := exists_evalFbelow_top S hskew z hz
  have h := finrank_subGr_le (d1EvalAction S.f S.jacobi hskew z)
    (D1TensorG.generator S.c₀) (LinearMap.range (FusionUZero.embedCo S.n N)) B hB
  exact ⟨h.1, by simpa only [FusionUZero.finrank_zero_source] using h.2⟩

theorem d4_evalUZeroGr_rank_le (N : ℕ) :
    FiniteDimensional ℂ
      (evalUZeroGr D4sector D1SiteG.D4Check.table_skewC (D1TensorG.points N)) ∧
    Module.finrank ℂ
      (evalUZeroGr D4sector D1SiteG.D4Check.table_skewC (D1TensorG.points N)) ≤
        28 ^ N := by
  simpa only [D4sector] using
    (evalUZeroGr_rank_le D4sector D1SiteG.D4Check.table_skewC
      (D1TensorG.points N) (D1TensorG.points_injective N))

end

end VOA.DeligneAudit.Toroidal.FusionGr

#print axioms VOA.DeligneAudit.Toroidal.FusionGr.subPieceSum_range
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.finrank_subGr_le
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.evalUZeroGr_rank_le
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.d4_evalUZeroGr_rank_le
