/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.LatticesAndCodes.Leech.Defs

/-!
# Golay-code facts for the ground-state lattice residual

The combinatorial facts about the extended binary Golay code `𝒢` (`Code.golay`) used by
`VOA.Moonshine.GroundLatticeCoord`.  Subsets of the 24 coordinates are `Finset (Fin 24)`;
`ind A` is the indicator word.

* `golay_weight_cases`: every codeword has weight `0, 8, 12, 16` or `24`.
* `card_symmDiff_cases`: for codewords `A, B`, `|A Δ B| + 2|A ∩ B| = |A| + |B|` with `|A Δ B|`
  again a codeword weight.
* `steiner`: **every 5-subset of the coordinates lies in an octad** (`S(5,8,24)`, existence
  half).  Proof by counting, with no enumeration: two distinct octads meet in `≤ 4` points, so
  the `759 · C(8,5) = 42504` five-subsets of octads are distinct, and `C(24,5) = 42504`.
* `exists_octad_dot_ne_zero`: a word of even weight outside `𝒢` has odd intersection with
  some octad (self-duality, plus the splitting of dodecads into two octads).
* `exists_octad_inter_six`: a codeword of weight `12` or `16` meets some octad in exactly `6`
  points.
* `exists_octad_inter_three`: every `4`-set meets some octad in exactly `3` points.

## Status
`sorry`-free, no `decide` over the code, no project axiom.
-/

namespace VOA.Moonshine.GroundLat

open Code Finset

/-! ## §1  Indicator words -/

/-- The indicator word of a coordinate set. -/
def ind (A : Finset (Fin 24)) : Fin 24 → ZMod 2 := fun j => if j ∈ A then 1 else 0

theorem support_ind (A : Finset (Fin 24)) : support (ind A) = A := by
  ext j
  by_cases h : j ∈ A <;> simp [support, ind, h]

theorem weight_ind (A : Finset (Fin 24)) : weight (ind A) = A.card := by
  rw [weight_eq_card_support, support_ind]

theorem ind_support (c : Fin 24 → ZMod 2) : ind (support c) = c := by
  funext j
  simp only [ind, mem_support]
  generalize c j = x
  revert x
  decide

theorem ind_injective : Function.Injective ind := fun A B h => by
  rw [← support_ind A, h, support_ind]

theorem ind_dot (A B : Finset (Fin 24)) : ind A ⬝ᵥ ind B = ((A ∩ B).card : ZMod 2) := by
  rw [dotProduct_eq_card_inter, support_ind, support_ind]

theorem ind_add (A B : Finset (Fin 24)) : ind A + ind B = ind (symmDiff A B) := by
  funext j
  simp only [Pi.add_apply, ind, Finset.mem_symmDiff]
  by_cases ha : j ∈ A <;> by_cases hb : j ∈ B <;> simp [ha, hb]; decide

theorem ind_univ : ind univ = 1 := by
  funext j; simp [ind]

/-- An **octad**: a codeword of weight `8`. -/
def IsOct (O : Finset (Fin 24)) : Prop := ind O ∈ golay ∧ O.card = 8

/-! ## §2  Weights -/

theorem golay_weight_cases {c : Fin 24 → ZMod 2} (hc : c ∈ golay) :
    weight c = 0 ∨ weight c = 8 ∨ weight c = 12 ∨ weight c = 16 ∨ weight c = 24 := by
  have h4 := golay_isDoublyEven c hc
  have hle := weight_le c
  by_cases h0 : c = 0
  · left; rw [h0, weight_zero]
  have h8 := golay_eight_le_weight hc h0
  have h1 : c + 1 ∈ golay := golay.add_mem hc golay_one_mem
  have hw1 := weight_add_one c
  by_cases h24 : weight c = 24
  · simp [h24]
  have hne : c + 1 ≠ 0 := by
    intro h
    apply h24
    rw [h, weight_zero] at hw1
    omega
  have := golay_eight_le_weight h1 hne
  omega

theorem card_cases {A : Finset (Fin 24)} (hA : ind A ∈ golay) :
    A.card = 0 ∨ A.card = 8 ∨ A.card = 12 ∨ A.card = 16 ∨ A.card = 24 := by
  have := golay_weight_cases hA
  rwa [weight_ind] at this

/-- Two codewords: the symmetric difference is a codeword and the sizes are related. -/
theorem card_symmDiff_cases {A B : Finset (Fin 24)} (hA : ind A ∈ golay) (hB : ind B ∈ golay) :
    ind (symmDiff A B) ∈ golay ∧ (symmDiff A B).card + 2 * (A ∩ B).card = A.card + B.card ∧
      ((symmDiff A B).card = 0 ∨ (symmDiff A B).card = 8 ∨ (symmDiff A B).card = 12 ∨
        (symmDiff A B).card = 16 ∨ (symmDiff A B).card = 24) := by
  have hm : ind (symmDiff A B) ∈ golay := by rw [← ind_add]; exact golay.add_mem hA hB
  refine ⟨hm, ?_, card_cases hm⟩
  have := weight_add_two_mul_card_inter (ind A) (ind B)
  rwa [ind_add, weight_ind, support_ind, support_ind, weight_ind, weight_ind] at this

theorem eq_of_card_symmDiff_zero {A B : Finset (Fin 24)} (h : (symmDiff A B).card = 0) : A = B := by
  rw [card_eq_zero] at h
  exact symmDiff_eq_bot.1 h

/-- Two distinct octads meet in at most `4` points. -/
theorem octad_inter_le {O₁ O₂ : Finset (Fin 24)} (h₁ : IsOct O₁) (h₂ : IsOct O₂) (hne : O₁ ≠ O₂) :
    (O₁ ∩ O₂).card ≤ 4 := by
  obtain ⟨-, he, hc⟩ := card_symmDiff_cases h₁.1 h₂.1
  have h0 : (symmDiff O₁ O₂).card ≠ 0 := fun h => hne (eq_of_card_symmDiff_zero h)
  rw [h₁.2, h₂.2] at he
  omega

/-! ## §3  `S(5,8,24)` by counting -/

/-- The octads, as a `Finset`. -/
noncomputable def octads : Finset (Finset (Fin 24)) :=
  (golay.toFinset.filter fun c => weight c = 8).image support

theorem mem_octads {O : Finset (Fin 24)} : O ∈ octads ↔ IsOct O := by
  classical
  simp only [octads, Finset.mem_image, Finset.mem_filter, mem_toFinset]
  constructor
  · rintro ⟨c, ⟨hc, hw⟩, rfl⟩
    exact ⟨by rwa [ind_support], by rwa [← weight_eq_card_support]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨ind O, ⟨h1, by rw [weight_ind, h2]⟩, support_ind O⟩

theorem support_injective : Function.Injective (support : (Fin 24 → ZMod 2) → Finset (Fin 24)) :=
  fun c d h => by rw [← ind_support c, h, ind_support]

theorem card_octads : octads.card = 759 := by
  rw [octads, Finset.card_image_of_injective _ support_injective]
  exact golay_weightCount_eight

/-- **`S(5,8,24)` (existence).** Every `5`-subset of the coordinates lies in an octad. -/
theorem steiner {T : Finset (Fin 24)} (hT : T.card = 5) : ∃ O, IsOct O ∧ T ⊆ O := by
  classical
  set U := octads.biUnion (fun O => O.powersetCard 5) with hU
  have hsub : U ⊆ (univ : Finset (Fin 24)).powersetCard 5 := by
    intro S hS
    rw [hU, mem_biUnion] at hS
    obtain ⟨O, -, hSO⟩ := hS
    rw [mem_powersetCard] at hSO ⊢
    exact ⟨subset_univ _, hSO.2⟩
  have hcard : U.card = 42504 := by
    rw [hU, card_biUnion]
    · rw [sum_congr rfl (fun O hO => by rw [card_powersetCard, (mem_octads.1 hO).2]), sum_const,
        card_octads]
      rfl
    · intro O₁ h₁ O₂ h₂ hne
      rw [Function.onFun, disjoint_left]
      intro S hS1 hS2
      rw [mem_powersetCard] at hS1 hS2
      have h5 := card_le_card (subset_inter hS1.1 hS2.1)
      have := octad_inter_le (mem_octads.1 h₁) (mem_octads.1 h₂) hne
      omega
  have hall : ((univ : Finset (Fin 24)).powersetCard 5).card ≤ U.card := by
    rw [card_powersetCard, card_univ, Fintype.card_fin, hcard]
    decide
  have heq := eq_of_subset_of_card_le hsub hall
  have hTU : T ∈ U := by rw [heq, mem_powersetCard]; exact ⟨subset_univ _, hT⟩
  rw [hU, mem_biUnion] at hTU
  obtain ⟨O, hO, hTO⟩ := hTU
  exact ⟨O, mem_octads.1 hO, (mem_powersetCard.1 hTO).1⟩

/-- Five points of a set `S` lie in an octad meeting `S` in at least five points. -/
theorem exists_octad_inter_ge_five {S : Finset (Fin 24)} (hS : 5 ≤ S.card) :
    ∃ O, IsOct O ∧ 5 ≤ (O ∩ S).card := by
  obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq hS
  obtain ⟨O, hO, hTO⟩ := steiner hT
  exact ⟨O, hO, hT ▸ card_le_card (subset_inter hTO hTS)⟩

theorem exists_not_mem {s : Finset (Fin 24)} (h : s.card < 24) : ∃ j, j ∉ s := by
  by_contra hc
  push Not at hc
  rw [eq_univ_of_forall hc, card_univ, Fintype.card_fin] at h
  omega

/-! ## §4  Octads meeting given sets -/

/-- A dodecad is the sum of two octads. -/
theorem dodecad_split {C : Finset (Fin 24)} (hC : ind C ∈ golay) (h12 : C.card = 12) :
    ∃ O O', IsOct O ∧ IsOct O' ∧ ind C = ind O + ind O' := by
  obtain ⟨O, hO, h5⟩ := exists_octad_inter_ge_five (S := C) (by omega)
  obtain ⟨hm, he, hc⟩ := card_symmDiff_cases hO.1 hC
  have hle : (O ∩ C).card ≤ 8 := hO.2 ▸ card_le_card inter_subset_left
  rw [hO.2, h12] at he
  refine ⟨O, symmDiff O C, hO, ⟨hm, by omega⟩, ?_⟩
  rw [← ind_add, ← add_assoc]
  have key : ∀ x y : ZMod 2, y = x + x + y := by decide
  funext j
  exact key (ind O j) (ind C j)

/-- A word of even weight outside `𝒢` has odd intersection with some octad. -/
theorem exists_octad_dot_ne_zero {x : Fin 24 → ZMod 2} (hx : x ∉ golay) (hw : Even (weight x)) :
    ∃ O, IsOct O ∧ ind O ⬝ᵥ x ≠ 0 := by
  have hx' : x ∉ golay.dual := by rwa [golay_isSelfDual]
  rw [mem_dual] at hx'
  push Not at hx'
  obtain ⟨y, hy, hyx⟩ := hx'
  have h1x : (1 : Fin 24 → ZMod 2) ⬝ᵥ x = 0 := by
    rw [show (1 : Fin 24 → ZMod 2) ⬝ᵥ x = ∑ i, x i by simp [dotProduct], sum_eq_weight,
      ZMod.natCast_eq_zero_iff_even]
    exact hw
  rcases golay_weight_cases hy with h | h | h | h | h
  · rw [weight_eq_zero.1 h, zero_dotProduct] at hyx
    exact absurd rfl hyx
  · refine ⟨support y, ⟨by rwa [ind_support], by rwa [← weight_eq_card_support]⟩, ?_⟩
    rwa [ind_support]
  · obtain ⟨O, O', hO, hO', hsplit⟩ := dodecad_split (C := support y) (by rwa [ind_support])
      (by rwa [← weight_eq_card_support])
    rw [ind_support] at hsplit
    rw [hsplit, add_dotProduct] at hyx
    by_cases hz : ind O ⬝ᵥ x = 0
    · rw [hz, zero_add] at hyx
      exact ⟨O', hO', hyx⟩
    · exact ⟨O, hO, hz⟩
  · have hm : y + 1 ∈ golay := golay.add_mem hy golay_one_mem
    have hw1 : weight (y + 1) = 8 := by rw [weight_add_one, h]
    refine ⟨support (y + 1), ⟨by rwa [ind_support], by rwa [← weight_eq_card_support]⟩, ?_⟩
    rwa [ind_support, add_dotProduct, h1x, add_zero]
  · have hw1 : weight (y + 1) = 0 := by rw [weight_add_one, h]
    have hy1 : y = 1 := by
      have h0 := weight_eq_zero.1 hw1
      rw [← add_one_add_one y, h0, zero_add]
    rw [hy1, h1x] at hyx
    exact absurd rfl hyx

/-- The meeting sizes of an octad and a codeword of weight `w`. -/
theorem octad_inter_cases {O C : Finset (Fin 24)} (hO : IsOct O) (hC : ind C ∈ golay) :
    ind (symmDiff O C) ∈ golay ∧ (symmDiff O C).card + 2 * (O ∩ C).card = 8 + C.card ∧
      ((symmDiff O C).card = 0 ∨ (symmDiff O C).card = 8 ∨ (symmDiff O C).card = 12 ∨
        (symmDiff O C).card = 16 ∨ (symmDiff O C).card = 24) := by
  have := card_symmDiff_cases hO.1 hC
  rwa [hO.2] at this

/-- A codeword of weight `12` or `16` meets some octad in exactly `6` points. -/
theorem exists_octad_inter_six {C : Finset (Fin 24)} (hC : ind C ∈ golay)
    (h : C.card = 12 ∨ C.card = 16) : ∃ O, IsOct O ∧ (O ∩ C).card = 6 := by
  obtain ⟨O, hO, h5⟩ := exists_octad_inter_ge_five (S := C) (by omega)
  obtain ⟨-, he, hc⟩ := octad_inter_cases hO hC
  have hle : (O ∩ C).card ≤ 8 := hO.2 ▸ card_le_card inter_subset_left
  by_cases h6 : (O ∩ C).card = 6
  · exact ⟨O, hO, h6⟩
  -- only `|C| = 16`, `O ⊆ C` remains
  have h16 : C.card = 16 := by omega
  have h8 : (O ∩ C).card = 8 := by omega
  have hOC : O ⊆ C := by
    have := eq_of_subset_of_card_le (inter_subset_left (s₁ := O) (s₂ := C)) (by rw [h8, hO.2])
    rw [← this]; exact inter_subset_right
  obtain ⟨T, hTO, hT3⟩ := exists_subset_card_eq (s := O) (n := 3) (by rw [hO.2]; omega)
  obtain ⟨c5, hc5⟩ : ∃ c5, c5 ∈ C ∧ c5 ∉ O := by
    by_contra hc
    push Not at hc
    have := card_le_card (show C ⊆ O from hc)
    have := hO.2
    omega
  obtain ⟨d, hd⟩ := exists_not_mem (s := C) (by omega)
  have hc5T : c5 ∉ T := fun h => hc5.2 (hTO h)
  have hdT : d ∉ insert c5 T := by
    rw [mem_insert]
    rintro (rfl | h)
    · exact hd hc5.1
    · exact hd (hOC (hTO h))
  have hT5 : (insert d (insert c5 T)).card = 5 := by
    rw [card_insert_of_notMem hdT, card_insert_of_notMem hc5T, hT3]
  obtain ⟨O', hO', hsub⟩ := steiner hT5
  obtain ⟨-, he', hc'⟩ := octad_inter_cases hO' hC
  have hsub4 : insert c5 T ⊆ O' ∩ C := by
    intro j hj
    refine mem_inter.2 ⟨hsub (mem_insert_of_mem hj), ?_⟩
    rcases mem_insert.1 hj with rfl | h
    · exact hc5.1
    · exact hOC (hTO h)
  have hge4 : 4 ≤ (O' ∩ C).card := by
    have := card_le_card hsub4
    rwa [card_insert_of_notMem hc5T, hT3] at this
  have hle7 : (O' ∩ C).card ≤ 7 := by
    have hss : O' ∩ C ⊆ O'.erase d := by
      intro j hj
      rw [mem_inter] at hj
      exact mem_erase.2 ⟨fun h => hd (h ▸ hj.2), hj.1⟩
    have := card_le_card hss
    rw [card_erase_of_mem (hsub (mem_insert_self _ _)), hO'.2] at this
    exact this
  rw [h16] at he'
  by_cases h6' : (O' ∩ C).card = 6
  · exact ⟨O', hO', h6'⟩
  exfalso
  have h4 : (O' ∩ C).card = 4 := by omega
  have heq4 : insert c5 T = O' ∩ C :=
    eq_of_subset_of_card_le hsub4 (by rw [h4, card_insert_of_notMem hc5T, hT3])
  have hOO' : O ∩ O' = T := by
    apply Subset.antisymm
    · intro j hj
      rw [mem_inter] at hj
      have : j ∈ insert c5 T := by rw [heq4]; exact mem_inter.2 ⟨hj.2, hOC hj.1⟩
      rcases mem_insert.1 this with rfl | h
      · exact absurd hj.1 hc5.2
      · exact h
    · intro j hj
      exact mem_inter.2 ⟨hTO hj, hsub (mem_insert_of_mem (mem_insert_of_mem hj))⟩
  obtain ⟨-, he'', hc''⟩ := octad_inter_cases hO hO'.1
  rw [hOO', hT3, hO'.2] at he''
  omega

/-- Every `4`-set meets some octad in exactly `3` points. -/
theorem exists_octad_inter_three {S : Finset (Fin 24)} (hS : S.card = 4) :
    ∃ O, IsOct O ∧ (O ∩ S).card = 3 := by
  obtain ⟨s4, hs4⟩ : S.Nonempty := by rw [← card_pos]; omega
  obtain ⟨p, hp⟩ := exists_not_mem (s := S) (by omega)
  have h5 : (insert p S).card = 5 := by rw [card_insert_of_notMem hp, hS]
  obtain ⟨O₁, hO₁, hsub₁⟩ := steiner h5
  obtain ⟨q, hq⟩ := exists_not_mem (s := O₁) (by rw [hO₁.2]; omega)
  set S' := S.erase s4 with hS'
  have hS'3 : S'.card = 3 := by rw [card_erase_of_mem hs4, hS]
  have hpS' : p ∉ S' := fun h => hp (mem_of_mem_erase h)
  have hqS' : q ∉ insert p S' := by
    rw [mem_insert]
    rintro (rfl | h)
    · exact hq (hsub₁ (mem_insert_self _ _))
    · exact hq (hsub₁ (mem_insert_of_mem (mem_of_mem_erase h)))
  have h5' : (insert q (insert p S')).card = 5 := by
    rw [card_insert_of_notMem hqS', card_insert_of_notMem hpS', hS'3]
  obtain ⟨O₂, hO₂, hsub₂⟩ := steiner h5'
  have hs4O₂ : s4 ∉ O₂ := by
    intro hs
    have hne : O₁ ≠ O₂ := fun h => hq (h ▸ hsub₂ (mem_insert_self _ _))
    have hle := octad_inter_le hO₁ hO₂ hne
    have hss : insert p S ⊆ O₁ ∩ O₂ := by
      intro j hj
      refine mem_inter.2 ⟨hsub₁ hj, ?_⟩
      rcases mem_insert.1 hj with rfl | h
      · exact hsub₂ (mem_insert_of_mem (mem_insert_self _ _))
      · by_cases hjs : j = s4
        · exact hjs ▸ hs
        · exact hsub₂ (mem_insert_of_mem (mem_insert_of_mem (mem_erase.2 ⟨hjs, h⟩)))
    have := card_le_card hss
    omega
  refine ⟨O₂, hO₂, ?_⟩
  have : O₂ ∩ S = S' := by
    ext j
    simp only [mem_inter, hS', mem_erase]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => hs4O₂ (h ▸ h1), h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hsub₂ (mem_insert_of_mem (mem_insert_of_mem (mem_erase.2 ⟨h1, h2⟩))), h2⟩
  rw [this, hS'3]

end VOA.Moonshine.GroundLat
