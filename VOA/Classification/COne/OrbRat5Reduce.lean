import VOA.Classification.COne.OrbRat5Char

/-! # `CubicZhuCharacterTable` is equivalent to eight doubled pairs

The five non-doubled table weights `0, 1, 1/4, 1/16, 9/16` are realised by proved characters
(`OrbRat5Char`).  Every other table weight occurs exactly twice:
`4, 9/4` (untwisted) and `1/36, 25/36, 49/36, 1/9, 4/9, 16/9` (the two `ℤ/3`-twisted sectors).
`cubicZhuCharacterTable_iff` proves

  `CubicZhuCharacterTable ↔ ∀ k : Fin 8, CubicDoubledPair (cubicPairWeight k)`,

where `CubicDoubledPair w` asks for two DISTINCT characters of `A(W)` with `[ω] ↦ w`.  So the
residual is exactly as strong as the target (no hidden weakening), and it does not mention
the five non-doubled rows.
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.OrbRat5

open VOA VertexOperatorAlgebra OrbRat2

@[reducible] local instance zhuRingCubicR : Ring (VOA.A cubicModel) := instRingA _
@[reducible] local instance zhuAlgebraCubicR : Algebra ℂ (VOA.A cubicModel) := instAlgebraA _

/-- Two distinct characters of `A(W)` with `[ω]`-value `w`. -/
def CubicDoubledPair (w : ℚ) : Prop :=
  letI := instRingA cubicModel; letI := instAlgebraA cubicModel
  ∃ χ₁ χ₂ : VOA.A cubicModel →ₐ[ℂ] ℂ, χ₁ ≠ χ₂ ∧
    χ₁ (VOA.mk cubicModel cubicModel.conformalVector) = (w : ℂ) ∧
    χ₂ (VOA.mk cubicModel cubicModel.conformalVector) = (w : ℂ)

/-- The eight doubled weights of the Dong–Jiang table. -/
def cubicPairWeight : Fin 8 → ℚ := ![4, 9/4, 1/36, 25/36, 49/36, 1/9, 4/9, 16/9]

/-- OPEN: the two untwisted doubled pairs (`ℤ/3`-eigenspaces of `V₈⁺` and of `V_{L+λ₂}`). -/
def CubicUntwistedDoubledPairs : Prop := CubicDoubledPair 4 ∧ CubicDoubledPair (9/4)

/-- OPEN: the six doubled pairs of the two `ℤ/3`-twisted sectors
(weights `1/36, 25/36, 49/36, 1/9, 4/9, 16/9`). -/
def CubicTwistedDoubledPairs : Prop :=
  ∀ k : Fin 8, 2 ≤ k.val → CubicDoubledPair (cubicPairWeight k)

/-- The row of the table holding the first (`e = false`) or second member of pair `k`. -/
def pairRow (k : Fin 8) (e : Bool) : Fin 21 :=
  ![if e then 3 else 2, if e then 6 else 5, if e then 15 else 9, if e then 16 else 10,
    if e then 17 else 11, if e then 18 else 12, if e then 19 else 13, if e then 20 else 14] k

theorem pairRow_weight :
    ∀ (k : Fin 8) (e : Bool), tetraWeightQ (pairRow k e) = cubicPairWeight k := by
  decide +kernel

theorem pairRow_ne : ∀ k : Fin 8, pairRow k false ≠ pairRow k true := by decide +kernel

/-- Equal table weights at different rows form one of the eight doubled pairs. -/
theorem tetraWeight_eq_cases : ∀ i j : Fin 21, i ≠ j → tetraWeightQ i = tetraWeightQ j →
    ∃ k : Fin 8, (i = pairRow k false ∧ j = pairRow k true) ∨
      (i = pairRow k true ∧ j = pairRow k false) := by
  decide +kernel

/-- The non-doubled rows. -/
theorem single_rows : ∀ i : Fin 21, (∀ k : Fin 8, ∀ e : Bool, i ≠ pairRow k e) →
    tetraWeightQ i ∈ ({0, 1, 1/4, 1/16, 9/16} : Finset ℚ) := by
  decide +kernel

theorem tetraWeight_inj_rat {i j : Fin 21} (h : tetraWeight i = tetraWeight j) :
    tetraWeightQ i = tetraWeightQ j := by
  unfold tetraWeight at h
  exact_mod_cast h

/-- The table is equivalent to the eight doubled pairs. -/
theorem cubicZhuCharacterTable_iff :
    CubicZhuCharacterTable ↔ ∀ k : Fin 8, CubicDoubledPair (cubicPairWeight k) := by
  constructor
  · rintro ⟨χ, hχ, hω⟩ k
    refine ⟨χ (pairRow k false), χ (pairRow k true), fun h => pairRow_ne k (hχ h), ?_, ?_⟩
    · rw [hω, tetraWeight, pairRow_weight]
    · rw [hω, tetraWeight, pairRow_weight]
  · intro hp
    classical
    choose χ₁ χ₂ hne h₁ h₂ using hp
    have hsingle : ∀ i : Fin 21, ∃ ψ : VOA.A cubicModel →ₐ[ℂ] ℂ,
        ψ (VOA.mk cubicModel cubicModel.conformalVector) = tetraWeight i ∧
        ∀ k e, i = pairRow k e → ψ = (if e then χ₂ k else χ₁ k) := by
      intro i
      by_cases hi : ∃ k e, i = pairRow k e
      · obtain ⟨k, e, rfl⟩ := hi
        refine ⟨if e then χ₂ k else χ₁ k, ?_, ?_⟩
        · cases e
          · simp only [Bool.false_eq_true, if_false]
            rw [h₁, tetraWeight, pairRow_weight]
          · simp only [if_true]
            rw [h₂, tetraWeight, pairRow_weight]
        · intro k' e' he
          have hk : k = k' ∧ e = e' := by
            revert he; revert k k' e e'; decide +kernel
          obtain ⟨rfl, rfl⟩ := hk
          rfl
      · push Not at hi
        obtain ⟨ψ, hψ⟩ := cubic_five_characters _ (single_rows i hi)
        refine ⟨ψ, by rw [hψ]; rfl, fun k e he => absurd he (hi k e)⟩
    choose ψ hψω hψp using hsingle
    refine ⟨ψ, ?_, hψω⟩
    intro i j hij
    by_contra hne'
    have hw : tetraWeightQ i = tetraWeightQ j := by
      apply tetraWeight_inj_rat
      rw [← hψω i, ← hψω j, hij]
    obtain ⟨k, ⟨hi, hj⟩ | ⟨hi, hj⟩⟩ := tetraWeight_eq_cases i j hne' hw
    · have e1 := hψp i k false hi
      have e2 := hψp j k true hj
      simp only [Bool.false_eq_true, if_false, if_true] at e1 e2
      exact hne k (e1.symm.trans (hij.trans e2))
    · have e1 := hψp i k true hi
      have e2 := hψp j k false hj
      simp only [Bool.false_eq_true, if_false, if_true] at e1 e2
      exact hne k (e2.symm.trans (hij.symm.trans e1))

/-- The table from the two untwisted and the six twisted doubled pairs. -/
theorem cubicZhuCharacterTable_of_pairs (hu : CubicUntwistedDoubledPairs)
    (ht : CubicTwistedDoubledPairs) : CubicZhuCharacterTable := by
  apply cubicZhuCharacterTable_iff.mpr
  intro k
  by_cases hk : 2 ≤ k.val
  · exact ht k hk
  · have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · exact hu.1
    · simpa [cubicPairWeight] using hu.2

/-- And conversely: the residual pairs are consequences of the table. -/
theorem pairs_of_cubicZhuCharacterTable (h : CubicZhuCharacterTable) :
    CubicUntwistedDoubledPairs ∧ CubicTwistedDoubledPairs := by
  have hp := cubicZhuCharacterTable_iff.mp h
  refine ⟨⟨hp 0, by simpa [cubicPairWeight] using hp 1⟩, fun k _ => hp k⟩

end VOA.Classification.COne.OrbRat5
