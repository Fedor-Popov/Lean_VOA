import VOA.Moonshine.MoonshineLRGenerationGraded
import VOA.Moonshine.MoonshineCNBorcherdsResolutionRange
import Mathlib.LinearAlgebra.TensorAlgebra.Basis

/-!
# The tensor-algebra side of the PBW character

Let `S ⊆ L` be a subspace with homogeneous basis `bS` such that the canonical map
`T(S) → U(L)` (`tensorGeneratorToEnveloping`) is bijective.
* `envWordBasis`: the words `ι(bS k₁) ⋯ ι(bS kₙ)` form a homogeneous basis of `U(L)`.
* `finrank_envGraded_eq_wordCount`: for degrees in the open cone, `dim U(L)_Γ` is the number
  `W(Γ)` of words of weight `Γ`.
* `wordSeries_mul_one_sub`: `(Σ_Γ W(Γ) e^Γ) · (1 − ch S) = 1`.
* **`coneProd_mul_one_sub_basisDegSeries`**: with graded PBW (`finrank_envGraded_eq_expCount`),
  `Π_{m,n ≥ 1} (1 − pᵐ qⁿ)^{−dim L_(m,n)} · (1 − ch S) = 1`. This is the PBW character identity in
  `MOON_BKM`.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open UniversalEnvelopingAlgebra Module

/-! ### Words in the free algebra -/

theorem basisFreeMonoid_eq_prod {κ : Type*} (w : FreeMonoid κ) :
    FreeAlgebra.basisFreeMonoid ℂ κ w = (w.toList.map (FreeAlgebra.ι ℂ)).prod := by
  rw [FreeAlgebra.basisFreeMonoid, Basis.map_apply, Finsupp.coe_basisSingleOne]
  change (MonoidAlgebra.lift ℂ (FreeAlgebra ℂ κ) (FreeMonoid κ) (FreeMonoid.lift (FreeAlgebra.ι ℂ)))
    (MonoidAlgebra.single w 1) = _
  rw [MonoidAlgebra.lift_single, one_smul, FreeMonoid.lift_apply]

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

section Words

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]
variable (wt : G → Submodule ℂ L) [DirectSum.Decomposition wt]
variable (hbr : ∀ {γ δ : G} {x y : L}, x ∈ wt γ → y ∈ wt δ → ⁅x, y⁆ ∈ wt (γ + δ))
variable {S : Submodule ℂ L} (hτ : Function.Bijective (tensorGeneratorToEnveloping S))
variable {κ : Type*} (bS : Basis κ ℂ S) (degS : κ → G) (hbS : ∀ k, (bS k : L) ∈ wt (degS k))

/-- The word `ι(bS k₁) ⋯ ι(bS kₙ)` in `U(L)`. -/
def envWord (l : List κ) : UniversalEnvelopingAlgebra ℂ L :=
  (l.map fun k => ι ℂ (bS k : L)).prod

include hbS in
theorem envWord_mem (l : List κ) : envWord bS l ∈ envGraded wt hbr (l.map degS).sum := by
  induction l with
  | nil => simpa [envWord] using one_mem_envGraded wt hbr
  | cons k l ih =>
      have h := mul_mem_envGraded wt hbr (ι_mem_envGraded wt hbr (hbS k)) ih
      simpa [envWord] using h

/-- The word basis of `U(L)`: the basis of `T(S)` by words, transported along `T(S) ≃ U(L)`. -/
def envWordBasis : Basis (FreeMonoid κ) ℂ (UniversalEnvelopingAlgebra ℂ L) :=
  bS.tensorAlgebra.map (AlgEquiv.ofBijective _ hτ).toLinearEquiv

theorem envWordBasis_apply (w : FreeMonoid κ) : envWordBasis hτ bS w = envWord bS w.toList := by
  rw [envWordBasis, Basis.map_apply, Basis.tensorAlgebra, Basis.map_apply, basisFreeMonoid_eq_prod]
  simp only [AlgEquiv.toLinearEquiv_apply, map_list_prod,
    List.map_map, envWord]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp

include hbS in
theorem envWordBasis_mem (w : FreeMonoid κ) :
    envWordBasis hτ bS w ∈ envGraded wt hbr (w.toList.map degS).sum := by
  rw [envWordBasis_apply]
  exact envWord_mem wt hbr bS degS hbS w.toList

end Words

/-! ### Counting words of a given weight in the cone -/

section Count

variable {κ : Type*} [DecidableEq κ] (degS : κ → ℕ × ℕ)
variable (hdegS : ∀ k, 1 ≤ (degS k).1 ∧ 1 ≤ (degS k).2)
variable (lowS : (ℕ × ℕ) → Finset κ) (hlowS : ∀ Γ k, k ∈ lowS Γ ↔ degS k ≤ Γ)

/-- Words of weight `Γ`, built by recursion on a bound `n ≥ Γ.1` for the length. -/
def wordsAux : ℕ → (ℕ × ℕ) → Finset (List κ)
  | 0, Γ => if Γ = 0 then {[]} else ∅
  | n + 1, Γ => (if Γ = 0 then {[]} else ∅) ∪
      (lowS Γ).biUnion fun k => (wordsAux n (Γ - degS k)).map ⟨List.cons k, List.cons_injective⟩

omit [DecidableEq κ] in
theorem fst_le_fst_sum_map (k : κ) (l : List κ) :
    (degS k).1 ≤ ((k :: l).map degS).sum.1 := by
  rw [List.map_cons, List.sum_cons, Prod.fst_add]
  exact Nat.le_add_right _ _

include hdegS hlowS in
theorem mem_wordsAux (n : ℕ) (Γ : ℕ × ℕ) (hΓ : Γ.1 ≤ n) (l : List κ) :
    l ∈ wordsAux degS lowS n Γ ↔ (l.map degS).sum = Γ := by
  induction n generalizing Γ l with
  | zero =>
      cases l with
      | nil =>
          simp only [wordsAux, List.map_nil, List.sum_nil]
          split_ifs with h <;> simp [h, eq_comm]
      | cons k l =>
          simp only [wordsAux]
          have h1 := (hdegS k).1
          have h2 := fst_le_fst_sum_map degS k l
          constructor
          · split_ifs <;> simp
          · intro h
            rw [h] at h2
            omega
  | succ n ih =>
      cases l with
      | nil =>
          simp only [wordsAux, List.map_nil, List.sum_nil]
          constructor
          · intro hm
            rcases Finset.mem_union.mp hm with h | h
            · split_ifs at h with h0
              · exact h0.symm
              · simp at h
            · obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp h
              obtain ⟨l', _, hl'⟩ := Finset.mem_map.mp hk
              simp at hl'
          · intro h
            apply Finset.mem_union_left
            rw [if_pos h.symm]
            exact Finset.mem_singleton_self _
      | cons k l =>
          simp only [wordsAux, Finset.mem_union, Finset.mem_biUnion, Finset.mem_map,
            Function.Embedding.coeFn_mk, List.cons.injEq]
          have hl : (k :: l) ∉ (if Γ = 0 then ({[]} : Finset (List κ)) else ∅) := by
            split_ifs <;> simp
          rw [List.map_cons, List.sum_cons]
          constructor
          · rintro (h | ⟨k', hk', l', hl', h1, h2⟩)
            · exact absurd h hl
            · rw [h1] at hk'
              rw [h2, h1] at hl'
              have hle := (hlowS Γ k).mp hk'
              have h1 := (hdegS k).1
              rw [ih (Γ - degS k) (by simp only [Prod.fst_sub]; omega) l] at hl'
              rw [hl', add_tsub_cancel_of_le hle]
          · intro h
            have hle : degS k ≤ Γ := h ▸ le_self_add
            refine Or.inr ⟨k, (hlowS Γ k).mpr hle, l, ?_, rfl, rfl⟩
            have h1 := (hdegS k).1
            rw [ih (Γ - degS k) (by simp only [Prod.fst_sub]; omega) l, ← h,
              add_tsub_cancel_left]

/-- `W(Γ)`: the number of words of weight `Γ`. -/
def wordCount (Γ : ℕ × ℕ) : ℕ := (wordsAux degS lowS Γ.1 Γ).card

include hdegS hlowS in
theorem wordsAux_eq (n : ℕ) (Γ : ℕ × ℕ) (hΓ : Γ.1 ≤ n) :
    wordsAux degS lowS n Γ = wordsAux degS lowS Γ.1 Γ := by
  ext l
  rw [mem_wordsAux degS hdegS lowS hlowS n Γ hΓ, mem_wordsAux degS hdegS lowS hlowS Γ.1 Γ le_rfl]

theorem wordCount_zero : wordCount degS lowS 0 = 1 := by
  simp [wordCount, wordsAux]

include hdegS hlowS in
/-- **The word recursion:** `W(Γ) = Σ_{k, deg k ≤ Γ} W(Γ − deg k)` for `Γ ≠ 0`. -/
theorem wordCount_rec {Γ : ℕ × ℕ} (hΓ : Γ ≠ 0) :
    wordCount degS lowS Γ = ∑ k ∈ lowS Γ, wordCount degS lowS (Γ - degS k) := by
  rw [wordCount, ← wordsAux_eq degS hdegS lowS hlowS (Γ.1 + 1) Γ (Nat.le_succ _), wordsAux,
    if_neg hΓ, Finset.empty_union, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hle := (hlowS Γ k).mp hk
    rw [Finset.card_map, wordCount, wordsAux_eq degS hdegS lowS hlowS Γ.1 (Γ - degS k)
      (by simp only [Prod.fst_sub]; omega)]
  · intro k _ k' _ hkk'
    rw [Function.onFun, Finset.disjoint_left]
    intro l hl hl'
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hl hl'
    obtain ⟨l₁, _, rfl⟩ := hl
    obtain ⟨l₂, _, h⟩ := hl'
    exact hkk' (List.cons.inj h).1.symm

/-! ### The word series -/

/-- `Σ_Γ W(Γ) pᵃ q^b`. -/
def wordSeries : PowerSeries (LaurentSeries ℂ) :=
  PowerSeries.mk fun a => HahnSeries.ofPowerSeries ℤ ℂ
    (PowerSeries.mk fun b => (wordCount degS lowS (a, b) : ℂ))

/-- `ch S = Σ_γ dim S_γ pᵃ q^b`. -/
def basisDegSeries : PowerSeries (LaurentSeries ℂ) :=
  PowerSeries.mk fun a => HahnSeries.ofPowerSeries ℤ ℂ
    (PowerSeries.mk fun b => (basisDegCount degS lowS (a, b) : ℂ))

/-- An indicator on the first components of the two antidiagonals picks one term. -/
theorem sum_antidiagonal_ite_fst_two (a b s₀ u₀ : ℕ) (F : ℕ → ℕ → ℂ) :
    ∑ x ∈ Finset.antidiagonal a, ∑ y ∈ Finset.antidiagonal b,
        (if (x.1, y.1) = (s₀, u₀) then F x.2 y.2 else 0) =
      if s₀ ≤ a ∧ u₀ ≤ b then F (a - s₀) (b - u₀) else 0 := by
  rw [← sum_antidiagonal_ite_two a b s₀ u₀ F, ← Finset.Nat.sum_antidiagonal_swap]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.Nat.sum_antidiagonal_swap]
  rfl

omit [DecidableEq κ] in
include hdegS in
theorem basisDegCount_zero : basisDegCount degS lowS 0 = 0 := by
  classical
  rw [basisDegCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _ h
  have := (hdegS k).1
  rw [h] at this
  simp at this

include hdegS hlowS in
/-- `W(a,b) = [a = b = 0] + Σ_{s+j=a} Σ_{u+v=b} d(s,u) W(j,v)`. -/
theorem wordCount_coeff_identity (a b : ℕ) :
    (wordCount degS lowS (a, b) : ℂ) = (if a = 0 ∧ b = 0 then 1 else 0) +
      ∑ x ∈ Finset.antidiagonal a, ∑ y ∈ Finset.antidiagonal b,
        (basisDegCount degS lowS (x.1, y.1) : ℂ) * wordCount degS lowS (x.2, y.2) := by
  by_cases h0 : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp [Finset.antidiagonal_zero, show ((0 : ℕ), (0 : ℕ)) = 0 from rfl,
      basisDegCount_zero degS hdegS lowS, wordCount_zero]
  rw [if_neg h0, zero_add]
  have hΓ : ((a, b) : ℕ × ℕ) ≠ 0 := fun h => h0 ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  rw [wordCount_rec degS hdegS lowS hlowS hΓ, Nat.cast_sum]
  have hterm : ∀ k ∈ lowS (a, b), (wordCount degS lowS ((a, b) - degS k) : ℂ) =
      ∑ x ∈ Finset.antidiagonal a, ∑ y ∈ Finset.antidiagonal b,
        (if (x.1, y.1) = degS k then (wordCount degS lowS (x.2, y.2) : ℂ) else 0) := by
    intro k hk
    have hle := (hlowS (a, b) k).mp hk
    have h := sum_antidiagonal_ite_fst_two a b (degS k).1 (degS k).2
      (fun j v => (wordCount degS lowS (j, v) : ℂ))
    rw [if_pos ⟨hle.1, hle.2⟩] at h
    exact h.symm
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finset.mem_antidiagonal] at hx hy
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    basisDegCount_eq_card_filter degS lowS hlowS (Γ := (a, b))
      (Prod.le_def.mpr ⟨by omega, by omega⟩),
    Finset.filter_congr fun k _ => (eq_comm : (x.1, y.1) = degS k ↔ _)]

include hdegS hlowS in
/-- `Σ W(Γ) e^Γ = 1 + ch S · Σ W(Γ) e^Γ`. -/
theorem wordSeries_eq :
    wordSeries degS lowS = 1 + basisDegSeries degS lowS * wordSeries degS lowS := by
  refine PowerSeries.ext fun a => ?_
  rw [map_add, PowerSeries.coeff_mul, PowerSeries.coeff_one]
  simp only [wordSeries, basisDegSeries, PowerSeries.coeff_mk]
  simp_rw [← map_mul, ← map_sum]
  rw [show (if a = 0 then (1 : LaurentSeries ℂ) else 0) = HahnSeries.ofPowerSeries ℤ ℂ
      (if a = 0 then 1 else 0) by split_ifs <;> simp, ← map_add]
  congr 1
  refine PowerSeries.ext fun b => ?_
  rw [PowerSeries.coeff_mk, map_add, map_sum, wordCount_coeff_identity degS hdegS lowS hlowS a b]
  congr 1
  · by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb, PowerSeries.coeff_one]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [PowerSeries.coeff_mul]
    simp only [PowerSeries.coeff_mk]

include hdegS hlowS in
/-- **The tensor-algebra character:** `(Σ W(Γ) e^Γ) · (1 − ch S) = 1`. -/
theorem wordSeries_mul_one_sub :
    wordSeries degS lowS * (1 - basisDegSeries degS lowS) = 1 := by
  have h := wordSeries_eq degS hdegS lowS hlowS
  rw [mul_sub, mul_one]
  nth_rw 1 [h]
  ring

end Count

/-! ### The character identity for `U(L)` -/

section Character

variable (wt : ℕ × ℕ → Submodule ℂ L) [DirectSum.Decomposition wt]
variable (hbr : ∀ {γ δ : ℕ × ℕ} {x y : L}, x ∈ wt γ → y ∈ wt δ → ⁅x, y⁆ ∈ wt (γ + δ))
variable {S : Submodule ℂ L} (hτ : Function.Bijective (tensorGeneratorToEnveloping S))
variable {κ : Type*} [DecidableEq κ] (bS : Basis κ ℂ S) (degS : κ → ℕ × ℕ)
  (hbS : ∀ k, (bS k : L) ∈ wt (degS k))
  (hdegS : ∀ k, 1 ≤ (degS k).1 ∧ 1 ≤ (degS k).2)
  (lowS : (ℕ × ℕ) → Finset κ) (hlowS : ∀ Γ k, k ∈ lowS Γ ↔ degS k ≤ Γ)

include hτ hbS hdegS hlowS in
/-- `dim U(L)_Γ = W(Γ)`. -/
theorem finrank_envGraded_eq_wordCount (Γ : ℕ × ℕ) :
    finrank ℂ (envGraded wt hbr Γ) = wordCount degS lowS Γ := by
  rw [finrank_envGraded_of_basis wt hbr (envWordBasis hτ bS) (fun w => (w.toList.map degS).sum)
    (envWordBasis_mem wt hbr hτ bS degS hbS) Γ
    ((wordsAux degS lowS Γ.1 Γ).map FreeMonoid.toList.symm.toEmbedding), Finset.card_map,
    wordCount]
  intro w
  rw [Finset.mem_map_equiv, mem_wordsAux degS hdegS lowS hlowS Γ.1 Γ le_rfl]
  rfl

variable {A : Type*} [LinearOrder A] (b : Basis A ℂ L) (deg : A → ℕ × ℕ)
  (hb : ∀ a, b a ∈ wt (deg a))
  (hdeg : ∀ a, 1 ≤ (deg a).1 ∧ 1 ≤ (deg a).2)
  (low : (ℕ × ℕ) → Finset A) (hlow : ∀ Γ a, a ∈ low Γ ↔ deg a ≤ Γ)

omit [DecidableEq κ] in
include wt hbr hτ hbS hdegS hlowS hb hdeg hlow in
/-- **The PBW character (blueprint: the character identity in `MOON_BKM`), generic form:** if
`T(S) ≃ U(L)` canonically,
`Π_{m,n ≥ 1} (1 − pᵐ qⁿ)^{−dim L_(m,n)} · (1 − ch S) = 1`. -/
theorem coneProd_mul_one_sub_basisDegSeries :
    coneProd (fun m n => -(basisDegCount deg low (m, n) : ℂ)) *
      (1 - basisDegSeries degS lowS) = 1 := by
  classical
  rw [← expSeries_eq_coneProd deg hdeg low hlow]
  have h : expSeries deg low = wordSeries degS lowS := by
    refine PowerSeries.ext fun a => ?_
    simp only [expSeries, wordSeries, PowerSeries.coeff_mk]
    congr 1
    refine PowerSeries.ext fun c => ?_
    simp only [PowerSeries.coeff_mk]
    rw [← finrank_envGraded_eq_expCount wt hbr b deg hb hdeg low hlow,
      finrank_envGraded_eq_wordCount wt hbr hτ bS degS hbS hdegS lowS hlowS]
  rw [h, wordSeries_mul_one_sub degS hdegS lowS hlowS]

end Character

end VOA.Moonshine.ConwayNorton.M8
