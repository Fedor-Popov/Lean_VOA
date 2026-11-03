import VOA.DeligneAudit.SL4TLineFlagRefinement
import VOA.DeligneAudit.SL4TAdjointSiteAssembly

/-!
# Power-sum-stable line flags against an arbitrary relation ideal

The line flags of `SL4TLineFlagRefinement` record level relations in the fixed ideal `(P, t^M)`.
Here the relation ideal is an arbitrary ideal `Rel` of `R[t]`, as needed for the joint relation
ideal `(P_y, t^(h+1), s t^h)` of one adjoint site. The constructions are the same: lines are
prepended from the top down; a layer whose power sums map it into a smaller subspace contributes
one line per missing dimension; and a chain of ideals refined by homogeneous degree gives a flag
whose cost is the sum over strata of the stratum dimension times the cost of its level. In a
mixed coefficient quotient such a flag is exactly a `MixedQuotientRelationFlag`.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- Lines with relative levels in a relation ideal, completing a subspace to the whole
coefficient algebra. -/
def RelationLineFlagFrom (p : ℕ → R) (Rel : Ideal R[X]) (r : ℕ) (F : Submodule ℂ R)
    (cost : ℕ) : Prop :=
  ∃ (n : ℕ) (v : ℕ → R) (ν : ℕ → ℕ),
    F ⊔ generatorPrefix v n = ⊤ ∧
    (∀ i ≤ n, ∀ s, 1 ≤ s → ∀ a ∈ F ⊔ generatorPrefix v i,
      p s * a ∈ F ⊔ generatorPrefix v i) ∧
    (∀ i < n, ∃ c : R[X], (∀ l, c.coeff l ∈ F ⊔ generatorPrefix v i) ∧
      Polynomial.C (v i) * X ^ ν i + c ∈ Rel) ∧
    (∑ i ∈ Finset.range n, lineLevelCost r (ν i)) ≤ cost

variable {p : ℕ → R} {Rel : Ideal R[X]} {r : ℕ}

/-- The whole algebra needs no further lines. -/
theorem relationLineFlagFrom_top : RelationLineFlagFrom p Rel r ⊤ 0 := by
  refine ⟨0, fun _ => 0, fun _ => 0, top_sup_eq _, ?_, ?_, by simp⟩
  · intro i _ s _ a _
    rw [top_sup_eq]
    exact Submodule.mem_top
  · intro i hi
    omega

/-- Any larger cost bound is still attained. -/
theorem relationLineFlagFrom_mono {F : Submodule ℂ R} {c c' : ℕ}
    (h : RelationLineFlagFrom p Rel r F c) (hc : c ≤ c') : RelationLineFlagFrom p Rel r F c' := by
  obtain ⟨n, v, ν, h₁, h₂, h₃, h₄⟩ := h
  exact ⟨n, v, ν, h₁, h₂, h₃, h₄.trans hc⟩

/-- A line whose relation is relative to a stable subspace can be placed first. -/
theorem relationLineFlagFrom_prepend {F : Submodule ℂ R} {cost : ℕ} (σ : R) (L : ℕ)
    (hF : ∀ s, 1 ≤ s → ∀ a ∈ F, p s * a ∈ F)
    (hσ : ∃ c : R[X], (∀ l, c.coeff l ∈ F) ∧ Polynomial.C σ * X ^ L + c ∈ Rel)
    (h : RelationLineFlagFrom p Rel r (F ⊔ ℂ ∙ σ) cost) :
    RelationLineFlagFrom p Rel r F (lineLevelCost r L + cost) := by
  obtain ⟨n, v, ν, htop, hstab, hrel, hcost⟩ := h
  have hpre (i : ℕ) : F ⊔ generatorPrefix (consSequence σ v) (i + 1) =
      (F ⊔ ℂ ∙ σ) ⊔ generatorPrefix v i := by
    rw [generatorPrefix_consSequence, sup_assoc]
  refine ⟨n + 1, consSequence σ v, consSequence L ν, ?_, ?_, ?_, ?_⟩
  · rw [hpre]
    exact htop
  · intro i hi s hs a ha
    cases i with
    | zero =>
        rw [generatorPrefix_zero, sup_bot_eq] at ha ⊢
        exact hF s hs a ha
    | succ i =>
        rw [hpre] at ha ⊢
        exact hstab i (by omega) s hs a ha
  · intro i hi
    cases i with
    | zero =>
        obtain ⟨c, hc, hcr⟩ := hσ
        exact ⟨c, fun l => by rw [generatorPrefix_zero, sup_bot_eq]; exact hc l, hcr⟩
    | succ i =>
        obtain ⟨c, hc, hcr⟩ := hrel i (by omega)
        exact ⟨c, fun l => by rw [hpre]; exact hc l, hcr⟩
  · rw [Finset.sum_range_succ']
    simp only [consSequence]
    omega

/-- One layer of a refinement: every intermediate subspace is completed with one line per
missing dimension, all of the layer's level. -/
theorem relationLineFlagFrom_layer [FiniteDimensional ℂ R]
    (U U' : Submodule ℂ R) (S : Set R) (L : ℕ) (hS : S ⊆ U')
    (hspan : U' ≤ U ⊔ Submodule.span ℂ S)
    (hp : ∀ s, 1 ≤ s → ∀ a ∈ U', p s * a ∈ U)
    (hcert : ∀ σ ∈ S, ∃ c : R[X], (∀ l, c.coeff l ∈ U) ∧ Polynomial.C σ * X ^ L + c ∈ Rel)
    (cost : ℕ) (h : RelationLineFlagFrom p Rel r U' cost) (F : Submodule ℂ R)
    (hUF : U ≤ F) (hFU : F ≤ U') :
    RelationLineFlagFrom p Rel r F
      (cost + (Module.finrank ℂ U' - Module.finrank ℂ F) * lineLevelCost r L) := by
  suffices hm : ∀ m, ∀ F : Submodule ℂ R, U ≤ F → F ≤ U' →
      Module.finrank ℂ U' - Module.finrank ℂ F = m →
      RelationLineFlagFrom p Rel r F (cost + m * lineLevelCost r L) from
    hm _ F hUF hFU rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro F hUF hFU hm
      by_cases hFe : F = U'
      · subst F
        apply relationLineFlagFrom_mono h
        omega
      have hσ : ∃ σ ∈ S, σ ∉ F := by
        by_contra hno
        apply hFe
        apply le_antisymm hFU
        apply hspan.trans
        apply sup_le hUF
        apply Submodule.span_le.mpr
        intro σ hσS
        by_contra hσF
        exact hno ⟨σ, hσS, hσF⟩
      obtain ⟨σ, hσS, hσF⟩ := hσ
      let F' := F ⊔ ℂ ∙ σ
      have hFF' : F < F' := by
        apply lt_of_le_of_ne le_sup_left
        intro he
        apply hσF
        rw [he]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self σ)
      have hF'U : F' ≤ U' := sup_le hFU ((Submodule.span_singleton_le_iff_mem σ U').mpr
        (hS hσS))
      have hr₁ : Module.finrank ℂ F < Module.finrank ℂ F' :=
        Submodule.finrank_lt_finrank_of_lt hFF'
      have hr₂ : Module.finrank ℂ F' ≤ Module.finrank ℂ U' := Submodule.finrank_mono hF'U
      have hih := ih (Module.finrank ℂ U' - Module.finrank ℂ F') (by omega) F'
        (hUF.trans le_sup_left) hF'U rfl
      have hpre := relationLineFlagFrom_prepend σ L
        (fun s hs a ha => hUF (hp s hs a (hFU ha)))
        (by
          obtain ⟨c, hc, hcr⟩ := hcert σ hσS
          exact ⟨c, fun l => hUF (hc l), hcr⟩) hih
      apply relationLineFlagFrom_mono hpre
      have hmm : Module.finrank ℂ U' - Module.finrank ℂ F' + 1 ≤ m := by omega
      calc lineLevelCost r L +
            (cost + (Module.finrank ℂ U' - Module.finrank ℂ F') * lineLevelCost r L)
          = cost + (Module.finrank ℂ U' - Module.finrank ℂ F' + 1) * lineLevelCost r L := by
            ring
        _ ≤ cost + m * lineLevelCost r L :=
            Nat.add_le_add_left (Nat.mul_le_mul_right _ hmm) _

/-- A descending chain of layers of one level telescopes to the total dimension drop. -/
theorem relationLineFlagFrom_layers [FiniteDimensional ℂ R]
    (U : ℕ → Submodule ℂ R) (S : ℕ → Set R) (L : ℕ) (n : ℕ)
    (hmono : ∀ e < n, U (e + 1) ≤ U e) (hS : ∀ e < n, S e ⊆ U e)
    (hspan : ∀ e < n, U e ≤ U (e + 1) ⊔ Submodule.span ℂ (S e))
    (hp : ∀ e < n, ∀ s, 1 ≤ s → ∀ a ∈ U e, p s * a ∈ U (e + 1))
    (hcert : ∀ e < n, ∀ σ ∈ S e, ∃ c : R[X], (∀ l, c.coeff l ∈ U (e + 1)) ∧
      Polynomial.C σ * X ^ L + c ∈ Rel)
    (cost : ℕ) (h : RelationLineFlagFrom p Rel r (U 0) cost) :
    RelationLineFlagFrom p Rel r (U n)
      (cost + (Module.finrank ℂ (U 0) - Module.finrank ℂ (U n)) * lineLevelCost r L) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      have hchain : ∀ e ≤ n, U e ≤ U 0 := by
        intro e he
        induction e with
        | zero => exact le_rfl
        | succ e ihe => exact (hmono e (by omega)).trans (ihe (by omega))
      have hprev := ih (fun e he => hmono e (by omega)) (fun e he => hS e (by omega))
        (fun e he => hspan e (by omega)) (fun e he => hp e (by omega))
        (fun e he => hcert e (by omega))
      have hstep := relationLineFlagFrom_layer (U (n + 1)) (U n) (S n) L (hS n (by omega))
        (hspan n (by omega)) (hp n (by omega)) (hcert n (by omega)) _ hprev (U (n + 1)) le_rfl
        (hmono n (by omega))
      apply relationLineFlagFrom_mono hstep (le_of_eq _)
      have h₁ : Module.finrank ℂ (U (n + 1)) ≤ Module.finrank ℂ (U n) :=
        Submodule.finrank_mono (hmono n (by omega))
      have h₂ : Module.finrank ℂ (U n) ≤ Module.finrank ℂ (U 0) :=
        Submodule.finrank_mono (hchain n le_rfl)
      rw [add_assoc, ← add_mul, Nat.sub_add_sub_cancel h₂ h₁]

/-- A graded stratification refines into a line flag against an arbitrary relation ideal,
whose cost is the sum over strata of the stratum dimension times the cost of its level. -/
theorem relationLineFlagFrom_gradedStrata [FiniteDimensional ℂ R]
    (G : ℕ → Submodule ℂ R) (m : ℕ) (hG0 : G 0 = ⊤) (hGm : G m = ⊥)
    (hanti : ∀ j < m, G (j + 1) ≤ G j)
    (hideal : ∀ j s, 1 ≤ s → ∀ a ∈ G j, p s * a ∈ G j)
    (degree : ℤ → Submodule ℂ R) (D : ℕ)
    (hmul : ∀ s : ℕ, 1 ≤ s → ∀ d : ℤ, ∀ a ∈ degree d, p s * a ∈ degree (d + (s : ℤ)))
    (hhigh : ∀ d : ℤ, (D : ℤ) < d → degree d = ⊥)
    (hhom : ∀ j < m, G j ≤ ⨆ (d : ℕ) (_ : d ≤ D), G j ⊓ degree d)
    (L : ℕ → ℕ)
    (hcert : ∀ j < m, ∀ d : ℕ, ∀ a ∈ G j ⊓ degree d, ∃ c : R[X],
      (∀ l, c.coeff l ∈ G j) ∧
      (∀ l, c.coeff l ≠ 0 → ∃ e : ℤ, (d : ℤ) < e ∧ c.coeff l ∈ degree e) ∧
      Polynomial.C a * X ^ L j + c ∈ Rel) :
    RelationLineFlagFrom p Rel r ⊥ (∑ j ∈ Finset.range m,
      (Module.finrank ℂ (G j) - Module.finrank ℂ (G (j + 1))) * lineLevelCost r (L j)) := by
  let V := gradedStratumLayer G degree D
  have hpiece (j e d : ℕ) (hed : e ≤ d) (hdD : d ≤ D) : G j ⊓ degree d ≤ V j e :=
    le_sup_of_le_right (le_iSup₂_of_le d ⟨hed, hdD⟩ le_rfl)
  have hzero_mem (j e : ℕ) (d : ℤ) (hd : (D : ℤ) < d) (a : R) (ha : a ∈ degree d) :
      a ∈ V j e := by
    rw [hhigh d hd] at ha
    rw [(Submodule.mem_bot ℂ).mp ha]
    exact Submodule.zero_mem _
  have hmemV (j e : ℕ) (d : ℤ) (hed : (e : ℤ) ≤ d) (a : R) (haG : a ∈ G j)
      (had : a ∈ degree d) : a ∈ V j e := by
    by_cases hdD : (D : ℤ) < d
    · exact hzero_mem j e d hdD a had
    · have hd0 : 0 ≤ d := le_trans (Int.natCast_nonneg e) hed
      have hdn : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg hd0
      apply hpiece j e d.toNat (by omega) (by omega)
      rw [hdn]
      exact ⟨haG, had⟩
  have hV0 (j : ℕ) (hj : j < m) : V j 0 = G j := by
    apply le_antisymm
    · apply sup_le (hanti j hj)
      exact iSup₂_le fun d _ => inf_le_left
    · apply (hhom j hj).trans
      exact iSup₂_le fun d hd => hpiece j 0 d (Nat.zero_le d) hd
  have hVD (j : ℕ) : V j (D + 1) = G (j + 1) := by
    apply le_antisymm
    · apply sup_le le_rfl
      exact iSup₂_le fun d hd => by omega
    · exact le_sup_left
  have hstrata : ∀ j ≤ m, RelationLineFlagFrom p Rel r (G j) (∑ i ∈ Finset.range j,
      (Module.finrank ℂ (G i) - Module.finrank ℂ (G (i + 1))) * lineLevelCost r (L i)) := by
    intro j
    induction j with
    | zero =>
        intro _
        rw [hG0, Finset.sum_range_zero]
        exact relationLineFlagFrom_top
    | succ j ih =>
        intro hj
        have hprev := ih (by omega)
        rw [← hV0 j (by omega)] at hprev
        have hlayers := relationLineFlagFrom_layers (V j)
          (fun e => ((G j ⊓ degree e : Submodule ℂ R) : Set R))
          (L j) (D + 1)
          (fun e _ => by
            apply sup_le_sup_left
            exact iSup₂_le fun d hd => le_iSup₂_of_le d ⟨by omega, hd.2⟩ le_rfl)
          (fun e he => by
            intro a ha
            exact hpiece j e e le_rfl (by omega) ha)
          (fun e he => by
            apply sup_le (le_sup_of_le_left le_sup_left)
            apply iSup₂_le
            intro d hd
            by_cases hde : d = e
            · subst d
              apply le_sup_of_le_right
              rw [Submodule.span_eq]
            · exact le_sup_of_le_left (hpiece j (e + 1) d (by omega) hd.2))
          (fun e he s hs a ha => by
            have hle : V j e ≤ (V j (e + 1)).comap (LinearMap.mulLeft ℂ (p s)) := by
              apply sup_le
              · intro a ha
                change p s * a ∈ V j (e + 1)
                exact Submodule.mem_sup_left (hideal (j + 1) s hs a ha)
              · apply iSup₂_le
                intro d hd a ha
                change p s * a ∈ V j (e + 1)
                apply hmemV j (e + 1) ((d : ℤ) + s) (by omega)
                · exact hideal j s hs a ha.1
                · exact hmul s hs d a ha.2
            exact hle ha)
          (fun e he σ hσ => by
            obtain ⟨c, hcG, hcdeg, hcr⟩ := hcert j (by omega) e σ hσ
            refine ⟨c, fun l => ?_, hcr⟩
            by_cases hc : c.coeff l = 0
            · rw [hc]
              exact Submodule.zero_mem _
            · obtain ⟨e', he', hce'⟩ := hcdeg l hc
              exact hmemV j (e + 1) e' (by omega) _ (hcG l) hce')
          _ hprev
        rw [hVD, hV0 j (by omega)] at hlayers
        rw [Finset.sum_range_succ]
        exact hlayers
  simpa only [hGm] using hstrata m le_rfl

/-- In a mixed coefficient quotient a relation line flag from zero is a power-sum-stable
relation flag with the same cost. -/
theorem mixedQuotientRelationFlag_of_relationLineFlag (q : MixedParams)
    (J : Ideal (MixedRing q)) (Rel : Ideal (MixedRing q ⧸ J)[X]) (cost : ℕ)
    (h : RelationLineFlagFrom (fun s => Ideal.Quotient.mk J (mixedPowerSum q s)) Rel
      (mixedWeight q).toNat ⊥ cost) :
    Nonempty (MixedQuotientRelationFlag q J Rel cost) := by
  obtain ⟨n, v, ν, htop, hstab, hrel, hcost⟩ := h
  simp only [bot_sup_eq] at htop hstab hrel
  exact ⟨{
    length := n
    vector := v
    space := generatorPrefix v
    level := ν
    zero := generatorPrefix_zero v
    top := htop
    step := fun i _ => generatorPrefix_succ v i
    stable := hstab
    relation := hrel
    bound := hcost }⟩

end

end VOA.DeligneAudit.SL4T
