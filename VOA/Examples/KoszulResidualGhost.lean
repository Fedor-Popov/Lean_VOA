/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.KoszulResidualNative
import VOA.Examples.KoszulConcreteEndpoint

/-!
# The antighost number operator on the actual ghost space

* `blockB_eq_bot_of_c0_neg` — joint pieces with a negative number of `c₀`'s vanish.
* `sN N` — the letters `(a, j)` with `j < N` (all colours).
* `Nb_W3` — on a word, `Nb (sN N)` counts the antighost letters of index `< N`.
* `Nb_ghostB` — on a joint ghost piece of antighost number `q` and weight `≤ N`,
  `Nb (sN N)` acts as `q`; `NbB_blockB` — the same for joint BRST pieces of weight `n ≤ N`.

Everything is proved outright.
-/

namespace VOA.KoszulResidual

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.LeeYangTransferAssembly VOA.KoszulConcrete VOA.SympFerm VOA.Ghost
open scoped TensorProduct

noncomputable section

/-! ### No negative `c₀` counts -/

theorem fockDegF_eq_bot_of_c0 {k : KF} (hk : ¬ 0 ≤ k.2) : fockDegF k = ⊥ := by
  rw [fockDegF, Submodule.span_eq_bot]
  rintro _ ⟨l, hl, rfl⟩
  exfalso
  apply hk
  have hl' : wordIdxF l = k := hl
  rw [← hl', wordIdxF]
  exact Int.natCast_nonneg _

theorem ghostDegF_eq_bot_of_c0 {k : KF} (hk : ¬ 0 ≤ k.2) : ghostDegF k = ⊥ :=
  tensorDeg_eq_bot_of (fun k : KF => 0 ≤ k.2) (fun a b ha hb => by
      simp only [Prod.snd_add]; omega) _ _
    (fun _ h => tensorDeg_eq_bot_of (fun k : KF => 0 ≤ k.2) (fun a b ha hb => by
      simp only [Prod.snd_add]; omega) _ _
      (fun _ h => fockDegF_eq_bot_of_c0 h) (fun _ h => fockDegF_eq_bot_of_c0 h) h)
    (fun _ h => fockDegF_eq_bot_of_c0 h) hk

theorem blockB_eq_bot_of_c0 {j : KF × ℤ} (hj : ¬ 0 ≤ j.1.2) : KoszulConcrete.blockB j = ⊥ :=
  tensorDeg_eq_bot_of (fun j : KF × ℤ => 0 ≤ j.1.2) (fun a b ha hb => by
      simp only [Prod.fst_add, Prod.snd_add]; omega) _ _
    (fun i h => by
      unfold KoszulConcrete.matterB matterF
      split_ifs with h1 h2
      · exact absurd (show (fun j : KF × ℤ => 0 ≤ j.1.2) i by simp [h2]) h
      · rfl
      · rfl)
    (fun i h => by
      unfold KoszulConcrete.ghostB
      split_ifs
      · exact ghostDegF_eq_bot_of_c0 h
      · rfl) hj

/-! ### The letters of index `< N` -/

/-- All letters `(a, j)` with `j < N`. -/
def sN (N : ℕ) : Finset LexLetter :=
  (Finset.univ ×ˢ Finset.range N).map toLex.toEmbedding

theorem mem_sN {N : ℕ} {q : LexLetter} : q ∈ sN N ↔ (ofLex q).2 < N := by
  simp only [sN, Finset.mem_map, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_range, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h; exact ⟨ofLex q, h, rfl⟩

theorem toLex_mem_sN {N : ℕ} (a : Fin 3) (j : ℕ) : toLex (a, j) ∈ sN N ↔ j < N := by
  rw [mem_sN]; rfl

/-! ### `Nb` on creation operators and words -/

/-- `[Nb s, Cr a p] = [p is an antighost letter in s] Cr a p`. -/
theorem Nb_Cr (s : Finset LexLetter) (a : Fin 3) (j : ℕ) (e : Fin 2) (y : Sl2GhostSpace) :
    Nb s (ConcreteHodge.Cr a (j, e) y) = ConcreteHodge.Cr a (j, e) (Nb s y) +
      if e = 0 ∧ toLex (a, j) ∈ s then ConcreteHodge.Cr a (j, e) y else 0 := by
  rw [Nb_apply, Nb_apply, map_sum]
  have hterm : ∀ q, gCr q (gAn q (ConcreteHodge.Cr a (j, e) y)) =
      ConcreteHodge.Cr a (j, e) (gCr q (gAn q y)) +
        if (ofLex q).1 = a ∧ ((ofLex q).2, (0 : Fin 2)) = (j, e) then gCr q y else 0 := by
    intro q
    have h := An_Cr_anticomm (ofLex q).1 a ((ofLex q).2, 0) (j, e) y
    rw [← eq_sub_iff_add_eq] at h
    change gAn q (ConcreteHodge.Cr a (j, e) y) = _ at h
    rw [h, map_sub, Cr_Cr_anticomm (ofLex q).1 a ((ofLex q).2, 0) (j, e)]
    split_ifs
    · rw [sub_neg_eq_add, add_comm]
    · rw [map_zero, zero_sub, neg_neg, add_zero]
  simp only [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  by_cases hp : e = 0 ∧ toLex (a, j) ∈ s
  · obtain ⟨rfl, hs⟩ := hp
    rw [if_pos ⟨rfl, hs⟩, Finset.sum_eq_single (toLex (a, j))]
    · rw [if_pos ⟨rfl, rfl⟩]; rfl
    · intro q _ hq
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply hq
      apply ofLex.injective
      rw [ofLex_toLex]
      exact Prod.ext h1 (congrArg Prod.fst h2)
    · intro h; exact absurd hs h
  · rw [if_neg hp]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hp
    refine ⟨(congrArg Prod.snd h2).symm, ?_⟩
    have : toLex (a, j) = q := by
      apply ofLex.injective
      rw [ofLex_toLex, ← h1]
      exact Prod.ext rfl (congrArg Prod.fst h2).symm
    rw [this]; exact hq

theorem Nb_gvac (s : Finset LexLetter) : Nb s gvac = 0 := by
  rw [Nb_apply]
  exact Finset.sum_eq_zero fun q _ => by rw [An_gvac, map_zero]

/-- The number of antighost letters of index `< N` in a word. -/
def bcount (N : ℕ) (l : SFWord) : ℕ := (l.filter fun p => p.2 = 0 ∧ p.1 < N).length

theorem bcount_cons (N : ℕ) (p : ℕ × Fin 2) (l : SFWord) :
    bcount N (p :: l) = bcount N l + if p.2 = 0 ∧ p.1 < N then 1 else 0 := by
  by_cases h : p.2 = 0 ∧ p.1 < N
  · simp [bcount, h]
  · rw [if_neg h]
    simp only [bcount, List.filter_cons]
    rw [if_neg (by simpa using h)]
    simp

theorem Nb_Cr_eigen (N : ℕ) (a : Fin 3) (p : ℕ × Fin 2) {y : Sl2GhostSpace} {c : ℕ}
    (hy : Nb (sN N) y = (c : ℂ) • y) :
    Nb (sN N) (ConcreteHodge.Cr a p y) =
      ((c + if p.2 = 0 ∧ p.1 < N then 1 else 0 : ℕ) : ℂ) • ConcreteHodge.Cr a p y := by
  obtain ⟨j, e⟩ := p
  rw [Nb_Cr, hy, map_smul]
  simp only [toLex_mem_sN]
  split_ifs <;> push_cast <;> simp [add_smul]

theorem Nb_W3 (N : ℕ) (l0 l1 l2 : SFWord) :
    Nb (sN N) (W3 l0 l1 l2) = ((bcount N l0 + bcount N l1 + bcount N l2 : ℕ) : ℂ) •
      W3 l0 l1 l2 := by
  induction l0 with
  | cons p l0 ih =>
      rw [← Cr0_W, Nb_Cr_eigen N 0 p ih, bcount_cons]
      congr 2
      ring
  | nil =>
    induction l1 with
    | cons p l1 ih =>
        have hk : (koszul 1 (len2 ([] : SFWord)) : ℂ) ≠ 0 := by
          simp [koszul, parSign, len2]
        have h1 := Cr1_W p [] l1 l2
        have hW : W3 [] (p :: l1) l2 = (koszul 1 (len2 ([] : SFWord)))⁻¹ •
            ConcreteHodge.Cr 1 p (W3 [] l1 l2) := by
          rw [h1, smul_smul, inv_mul_cancel₀ hk, one_smul]
        rw [hW, map_smul, Nb_Cr_eigen N 1 p ih, smul_comm, bcount_cons]
        congr 2
        ring
    | nil =>
      induction l2 with
      | cons p l2 ih =>
          have hk : (koszul 1 (len2 ([] : SFWord) + len2 ([] : SFWord)) : ℂ) ≠ 0 := by
            simp [koszul, parSign, len2]
          have h2 := Cr2_W p [] [] l2
          have hW : W3 [] [] (p :: l2) = (koszul 1 (len2 ([] : SFWord) +
              len2 ([] : SFWord)))⁻¹ • ConcreteHodge.Cr 2 p (W3 [] [] l2) := by
            rw [h2, smul_smul, inv_mul_cancel₀ hk, one_smul]
          rw [hW, map_smul, Nb_Cr_eigen N 2 p ih, smul_comm, bcount_cons]
          congr 2
          ring
      | nil =>
          rw [show W3 [] [] [] = gvac from rfl, Nb_gvac]
          simp [bcount]

/-! ### `Nb` on the fine ghost pieces -/

/-- The number of antighost letters of a word. -/
def nb (l : SFWord) : ℕ := (l.filter fun p => p.2 = 0).length

theorem nb_cons (p : ℕ × Fin 2) (l : SFWord) : nb (p :: l) = nb l + if p.2 = 0 then 1 else 0 := by
  by_cases h : p.2 = 0
  · simp [nb, h]
  · rw [if_neg h]
    simp only [nb, List.filter_cons]
    rw [if_neg (by simpa using h)]
    simp

theorem b2_modeIdxF (p : ℕ × Fin 2) : b2 (modeIdxF p) = if p.2 = 0 then 2 else 0 := by
  obtain ⟨j, e⟩ := p
  fin_cases e
  · simp [modeIdxF, modeIdx, modeR, ghCharge]
  · by_cases hj : j = 0
    · subst hj; simp [modeIdxF, modeIdx, modeR, ghCharge]
    · simp [modeIdxF, modeIdx, modeR, ghCharge, hj]

theorem b2_wordIdxF (l : SFWord) : b2 (wordIdxF l) = 2 * (nb l : ℤ) := by
  induction l with
  | nil => simp [wordIdxF, nb]
  | cons p l ih =>
      rw [wordIdxF_cons, map_add, ih, b2_modeIdxF, nb_cons]
      split_ifs <;> push_cast <;> ring

theorem bcount_eq_nb {N : ℕ} {l : SFWord} (hl : ghWeight l ≤ N) : bcount N l = nb l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      rw [ghWeight_cons] at hl
      rw [bcount_cons, nb_cons, ih (by omega)]
      congr 1
      by_cases h : p.2 = 0
      · have : ghModeWt p = p.1 + 1 := by simp [ghModeWt, ghWt, h]
        rw [if_pos h, if_pos ⟨h, by omega⟩]
      · rw [if_neg h, if_neg (fun h' => h h'.1)]

theorem wordIdxF_weight (l : SFWord) : (wordIdxF l).1.2 = ((ghWeight l : ℕ) : ℂ) := rfl

/-- `Nb` on a word of weight `≤ N` counts all its antighost letters. -/
theorem Nb_W3_of_weight (N : ℕ) (l0 l1 l2 : SFWord)
    (hw : ghWeight l0 + ghWeight l1 + ghWeight l2 ≤ N) :
    Nb (sN N) (W3 l0 l1 l2) = ((nb l0 + nb l1 + nb l2 : ℕ) : ℂ) • W3 l0 l1 l2 := by
  rw [Nb_W3, bcount_eq_nb (by omega), bcount_eq_nb (by omega), bcount_eq_nb (by omega)]

theorem fockDegF_induction (k : KF) (Φ : FockSF → Prop) (h0 : Φ 0)
    (hadd : ∀ x y, Φ x → Φ y → Φ (x + y)) (hsmul : ∀ (c : ℂ) x, Φ x → Φ (c • x))
    (hw : ∀ l : SFWord, wordIdxF l = k → Φ (stWordSF l)) : ∀ x ∈ fockDegF k, Φ x := by
  intro x hx
  rw [fockDegF] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨l, hl, rfl⟩ := hx; exact hw l hl
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

/-- **`Nb` acts as the antighost number on fine ghost pieces of weight `≤ N`.** -/
theorem Nb_ghostDegF (N : ℕ) {k : KF} {q : ℤ} (hq : b2 k = 2 * q)
    (hw : ∀ w : ℕ, (w : ℂ) = k.1.2 → w ≤ N) :
    ∀ y ∈ ghostDegF k, Nb (sN N) y = (q : ℂ) • y := by
  refine tensorDeg_induction pairDegF fockDegF k _ (by simp)
    (fun x y hx hy => by rw [map_add, hx, hy, smul_add])
    (fun c x hx => by rw [map_smul, hx, smul_comm]) ?_
  intro b x hx z hz
  revert hx
  refine (fun hx => tensorDeg_induction fockDegF fockDegF b
    (fun x => Nb (sN N) (x ⊗ₜ[ℂ] z) = (q : ℂ) • (x ⊗ₜ[ℂ] z)) (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [TensorProduct.add_tmul, map_add, hx, hy, smul_add])
    (fun c x hx => by beta_reduce at hx ⊢; rw [← TensorProduct.smul_tmul', map_smul, hx, smul_comm]) ?_ x hx)
  intro b' u hu v hv
  refine fockDegF_induction _ (fun u => Nb (sN N) ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] z) =
      (q : ℂ) • ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] z)) (by simp)
    (fun x y hx hy => by
      beta_reduce at hx hy ⊢
      rw [TensorProduct.add_tmul, TensorProduct.add_tmul, map_add, hx, hy, smul_add])
    (fun c x hx => by
      beta_reduce at hx ⊢
      rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', map_smul, hx, smul_comm])
    ?_ u hu
  intro l0 hl0
  refine fockDegF_induction _ (fun v => Nb (sN N) ((stWordSF l0 ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] z) =
      (q : ℂ) • ((stWordSF l0 ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] z)) (by simp)
    (fun x y hx hy => by
      beta_reduce at hx hy ⊢
      rw [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, hx, hy, smul_add])
    (fun c x hx => by
      beta_reduce at hx ⊢
      rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_smul, hx, smul_comm])
    ?_ v hv
  intro l1 hl1
  refine fockDegF_induction _ (fun z => Nb (sN N) ((stWordSF l0 ⊗ₜ[ℂ] stWordSF l1) ⊗ₜ[ℂ] z) =
      (q : ℂ) • ((stWordSF l0 ⊗ₜ[ℂ] stWordSF l1) ⊗ₜ[ℂ] z)) (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [TensorProduct.tmul_add, map_add, hx, hy, smul_add])
    (fun c x hx => by beta_reduce at hx ⊢; rw [TensorProduct.tmul_smul, map_smul, hx, smul_comm])
    ?_ z hz
  intro l2 hl2
  have hsum : wordIdxF l0 + wordIdxF l1 + wordIdxF l2 = k := by
    rw [hl0, hl1, hl2]; abel
  have hwt : ghWeight l0 + ghWeight l1 + ghWeight l2 ≤ N := by
    apply hw
    rw [← hsum]
    simp only [Prod.fst_add, Prod.snd_add, wordIdxF_weight]
    push_cast; ring
  have hnb : ((nb l0 + nb l1 + nb l2 : ℕ) : ℤ) = q := by
    have h := hq
    rw [← hsum, map_add, map_add, b2_wordIdxF, b2_wordIdxF, b2_wordIdxF] at h
    push_cast; omega
  have := Nb_W3_of_weight N l0 l1 l2 hwt
  rw [show (stWordSF l0 ⊗ₜ[ℂ] stWordSF l1) ⊗ₜ[ℂ] stWordSF l2 = W3 l0 l1 l2 from rfl, this,
    ← hnb]
  push_cast; rfl

end

end VOA.KoszulResidual
