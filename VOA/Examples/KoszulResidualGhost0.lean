/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.KoszulResidualGr

/-!
# The ghost content of the antighost-free blocks

* `NT T` — the number operator of a finite set `T` of ghost modes; on a word it counts the
  letters in `T` (`NT_W3`).
* `ghostDegF_le_vac` — a fine ghost piece with no `b` and no `c` letters is the vacuum line.
* `Nc N` (all `c`-modes of index `≤ N`) acts as the identity on fine ghost pieces with one `c`
  letter, no `b` letters and weight `≤ N` (`Nc_ghostDegF`).
* `vacφ` — a functional with `vacφ gvac = 1`; `Pvac = vacφ(·) gvac`.

Everything is proved outright.
-/

set_option linter.deprecated false

namespace VOA.KoszulResidual

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.LeeYangTransferAssembly VOA.KoszulConcrete VOA.SympFerm VOA.Ghost
open scoped TensorProduct

noncomputable section

/-! ### The number operator of a set of modes -/

/-- The number operator of a finite set of ghost modes `(colour, mode)`. -/
def NT (T : Finset (Fin 3 × (ℕ × Fin 2))) : Module.End ℂ Sl2GhostSpace :=
  ∑ t ∈ T, ConcreteHodge.Cr t.1 t.2 ∘ₗ ConcreteHodge.An t.1 t.2

theorem NT_apply (T : Finset (Fin 3 × (ℕ × Fin 2))) (y : Sl2GhostSpace) :
    NT T y = ∑ t ∈ T, ConcreteHodge.Cr t.1 t.2 (ConcreteHodge.An t.1 t.2 y) := by
  simp [NT, LinearMap.coe_sum]

theorem NT_Cr (T : Finset (Fin 3 × (ℕ × Fin 2))) (a : Fin 3) (p : ℕ × Fin 2)
    (y : Sl2GhostSpace) :
    NT T (ConcreteHodge.Cr a p y) = ConcreteHodge.Cr a p (NT T y) +
      if (a, p) ∈ T then ConcreteHodge.Cr a p y else 0 := by
  rw [NT_apply, NT_apply, map_sum]
  have hterm : ∀ t : Fin 3 × (ℕ × Fin 2),
      ConcreteHodge.Cr t.1 t.2 (ConcreteHodge.An t.1 t.2 (ConcreteHodge.Cr a p y)) =
      ConcreteHodge.Cr a p (ConcreteHodge.Cr t.1 t.2 (ConcreteHodge.An t.1 t.2 y)) +
        if t = (a, p) then ConcreteHodge.Cr a p y else 0 := by
    intro t
    have h := An_Cr_anticomm t.1 a t.2 p y
    rw [← eq_sub_iff_add_eq] at h
    rw [h, map_sub, Cr_Cr_anticomm t.1 a t.2 p]
    by_cases ht : t = (a, p)
    · subst ht
      rw [if_pos ⟨rfl, rfl⟩, if_pos rfl, sub_neg_eq_add, add_comm]
    · rw [if_neg (fun h => ht (Prod.ext h.1 h.2)), if_neg ht, map_zero, zero_sub, neg_neg,
        add_zero]
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']

theorem NT_gvac (T : Finset (Fin 3 × (ℕ × Fin 2))) : NT T gvac = 0 := by
  rw [NT_apply]
  exact Finset.sum_eq_zero fun t _ => by rw [An_gvac, map_zero]

/-- The number of letters of colour `a` of a word lying in `T`. -/
def tcount (T : Finset (Fin 3 × (ℕ × Fin 2))) (a : Fin 3) (l : SFWord) : ℕ :=
  (l.filter fun p => (a, p) ∈ T).length

theorem tcount_cons (T : Finset (Fin 3 × (ℕ × Fin 2))) (a : Fin 3) (p : ℕ × Fin 2)
    (l : SFWord) :
    tcount T a (p :: l) = tcount T a l + if (a, p) ∈ T then 1 else 0 := by
  by_cases h : (a, p) ∈ T
  · simp [tcount, h]
  · rw [if_neg h]
    simp only [tcount, List.filter_cons]
    rw [if_neg (by simpa using h)]
    simp

theorem NT_Cr_eigen (T : Finset (Fin 3 × (ℕ × Fin 2))) (a : Fin 3) (p : ℕ × Fin 2)
    {y : Sl2GhostSpace} {c : ℕ} (hy : NT T y = (c : ℂ) • y) :
    NT T (ConcreteHodge.Cr a p y) =
      ((c + if (a, p) ∈ T then 1 else 0 : ℕ) : ℂ) • ConcreteHodge.Cr a p y := by
  rw [NT_Cr, hy, map_smul]
  split_ifs <;> push_cast <;> simp [add_smul]

/-- **`NT T` counts the letters in `T`.** -/
theorem NT_W3 (T : Finset (Fin 3 × (ℕ × Fin 2))) (l0 l1 l2 : SFWord) :
    NT T (W3 l0 l1 l2) =
      ((tcount T 0 l0 + tcount T 1 l1 + tcount T 2 l2 : ℕ) : ℂ) • W3 l0 l1 l2 := by
  induction l0 with
  | cons p l0 ih =>
      rw [← Cr0_W, NT_Cr_eigen T 0 p ih, tcount_cons]
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
        rw [hW, map_smul, NT_Cr_eigen T 1 p ih, smul_comm, tcount_cons]
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
          rw [hW, map_smul, NT_Cr_eigen T 2 p ih, smul_comm, tcount_cons]
          congr 2
          ring
      | nil =>
          rw [show W3 [] [] [] = gvac from rfl, NT_gvac]
          simp [tcount]

/-! ### Induction over the words of a fine ghost piece -/

theorem ghostDegF_induction (k : KF) (Φ : Sl2GhostSpace → Prop) (h0 : Φ 0)
    (hadd : ∀ x y, Φ x → Φ y → Φ (x + y)) (hsmul : ∀ (c : ℂ) x, Φ x → Φ (c • x))
    (hw : ∀ l0 l1 l2 : SFWord, wordIdxF l0 + wordIdxF l1 + wordIdxF l2 = k → Φ (W3 l0 l1 l2)) :
    ∀ y ∈ ghostDegF k, Φ y := by
  refine tensorDeg_induction pairDegF fockDegF k _ h0 hadd hsmul ?_
  intro b x hx z hz
  revert hx
  refine (fun hx => tensorDeg_induction fockDegF fockDegF b
    (fun x => Φ (x ⊗ₜ[ℂ] z)) (by simpa using h0)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [TensorProduct.add_tmul]; exact hadd _ _ hx hy)
    (fun c x hx => by beta_reduce at hx ⊢; rw [← TensorProduct.smul_tmul']; exact hsmul _ _ hx)
    ?_ x hx)
  intro b' u hu v hv
  refine fockDegF_induction _ (fun u => Φ ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] z)) (by simpa using h0)
    (fun x y hx hy => by
      beta_reduce at hx hy ⊢
      rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; exact hadd _ _ hx hy)
    (fun c x hx => by
      beta_reduce at hx ⊢
      rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul']; exact hsmul _ _ hx)
    ?_ u hu
  intro l0 hl0
  refine fockDegF_induction _ (fun v => Φ ((stWordSF l0 ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] z)) (by simpa using h0)
    (fun x y hx hy => by
      beta_reduce at hx hy ⊢
      rw [TensorProduct.tmul_add, TensorProduct.add_tmul]; exact hadd _ _ hx hy)
    (fun c x hx => by
      beta_reduce at hx ⊢
      rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']; exact hsmul _ _ hx)
    ?_ v hv
  intro l1 hl1
  refine fockDegF_induction _ (fun z => Φ ((stWordSF l0 ⊗ₜ[ℂ] stWordSF l1) ⊗ₜ[ℂ] z))
    (by simpa using h0)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [TensorProduct.tmul_add]; exact hadd _ _ hx hy)
    (fun c x hx => by beta_reduce at hx ⊢; rw [TensorProduct.tmul_smul]; exact hsmul _ _ hx)
    ?_ z hz
  intro l2 hl2
  exact hw l0 l1 l2 (by rw [hl0, hl1, hl2]; abel)

/-- The number of `c` letters of a word. -/
def ncnt (l : SFWord) : ℕ := (l.filter fun p => p.2 = 1).length

theorem ncnt_cons (p : ℕ × Fin 2) (l : SFWord) :
    ncnt (p :: l) = ncnt l + if p.2 = 1 then 1 else 0 := by
  by_cases h : p.2 = 1
  · simp [ncnt, h]
  · rw [if_neg h]
    simp only [ncnt, List.filter_cons]
    rw [if_neg (by simpa using h)]
    simp

theorem c2_modeIdxF (p : ℕ × Fin 2) : c2 (modeIdxF p) = if p.2 = 1 then 2 else 0 := by
  obtain ⟨j, e⟩ := p
  fin_cases e
  · simp [modeIdxF, modeIdx, modeR, ghCharge]
  · by_cases hj : j = 0
    · subst hj; simp [modeIdxF, modeIdx, modeR, ghCharge]
    · simp [modeIdxF, modeIdx, modeR, ghCharge, hj]

theorem c2_wordIdxF (l : SFWord) : c2 (wordIdxF l) = 2 * (ncnt l : ℤ) := by
  induction l with
  | nil => simp [wordIdxF, ncnt]
  | cons p l ih =>
      rw [wordIdxF_cons, map_add, ih, c2_modeIdxF, ncnt_cons]
      split_ifs <;> push_cast <;> ring

theorem nb_add_ncnt (l : SFWord) : nb l + ncnt l = l.length := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      rw [nb_cons, ncnt_cons, List.length_cons, ← ih]
      obtain ⟨j, e⟩ := p
      fin_cases e <;> simp <;> ring

/-- **A fine ghost piece with no `b` and no `c` letters is the vacuum line.** -/
theorem ghostDegF_le_vac {k : KF} (hb : b2 k = 0) (hc : c2 k = 0) :
    ∀ y ∈ ghostDegF k, y ∈ ℂ ∙ gvac := by
  refine ghostDegF_induction k _ (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _)
    (fun c _ h => Submodule.smul_mem _ c h) ?_
  intro l0 l1 l2 hsum
  have hb' := hb
  have hc' := hc
  rw [← hsum, map_add, map_add, b2_wordIdxF, b2_wordIdxF, b2_wordIdxF] at hb'
  rw [← hsum, map_add, map_add, c2_wordIdxF, c2_wordIdxF, c2_wordIdxF] at hc'
  have e0 := nb_add_ncnt l0
  have e1 := nb_add_ncnt l1
  have e2 := nb_add_ncnt l2
  have h0 : l0 = [] := List.eq_nil_of_length_eq_zero (by omega)
  have h1 : l1 = [] := List.eq_nil_of_length_eq_zero (by omega)
  have h2 : l2 = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst h0 h1 h2
  exact Submodule.mem_span_singleton_self _

/-- The `c`-modes of index `≤ N`. -/
def Tc (N : ℕ) : Finset (Fin 3 × (ℕ × Fin 2)) :=
  Finset.univ ×ˢ (Finset.range (N + 1) ×ˢ {1})

theorem mem_Tc {N : ℕ} {a : Fin 3} {p : ℕ × Fin 2} : (a, p) ∈ Tc N ↔ p.1 ≤ N ∧ p.2 = 1 := by
  obtain ⟨j, e⟩ := p
  simp only [Tc, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_range,
    Finset.mem_singleton]
  omega

theorem tcount_Tc {N : ℕ} (a : Fin 3) {l : SFWord} (hl : ghWeight l ≤ N) :
    tcount (Tc N) a l = ncnt l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      rw [ghWeight_cons] at hl
      rw [tcount_cons, ncnt_cons, ih (by omega)]
      congr 1
      by_cases h : p.2 = 1
      · have : p.1 ≤ ghModeWt p := by simp [ghModeWt]
        rw [if_pos (mem_Tc.mpr ⟨by omega, h⟩), if_pos h]
      · rw [if_neg (fun h' => h (mem_Tc.mp h').2), if_neg h]

/-- **`NT (Tc N)` counts the `c` letters on fine pieces of weight `≤ N`.** -/
theorem Nc_ghostDegF (N : ℕ) {k : KF} {q : ℤ} (hq : c2 k = 2 * q)
    (hw : ∀ w : ℕ, (w : ℂ) = k.1.2 → w ≤ N) :
    ∀ y ∈ ghostDegF k, NT (Tc N) y = (q : ℂ) • y := by
  refine ghostDegF_induction k _ (by simp) (fun x y hx hy => by rw [map_add, hx, hy, smul_add])
    (fun c x hx => by rw [map_smul, hx, smul_comm]) ?_
  intro l0 l1 l2 hsum
  have hwt : ghWeight l0 + ghWeight l1 + ghWeight l2 ≤ N := by
    apply hw
    rw [← hsum]
    simp only [Prod.fst_add, Prod.snd_add, wordIdxF_weight]
    push_cast; ring
  have hnc : ((ncnt l0 + ncnt l1 + ncnt l2 : ℕ) : ℤ) = q := by
    have h := hq
    rw [← hsum, map_add, map_add, c2_wordIdxF, c2_wordIdxF, c2_wordIdxF] at h
    push_cast; omega
  rw [NT_W3, tcount_Tc 0 (by omega), tcount_Tc 1 (by omega), tcount_Tc 2 (by omega), ← hnc]
  push_cast; rfl

end

end VOA.KoszulResidual
