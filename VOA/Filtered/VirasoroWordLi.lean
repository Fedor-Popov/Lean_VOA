/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Filtered.AffineCurrentLi
import VOA.Examples.LeeYangGram
import VOA.Examples.LeeYangSingular
import VOA.Examples.VirasoroSimple

/-!
# Virasoro-word description of the Li filtration

For the universal Virasoro vacuum VOA `V(c,0) = virasoroVOA c`, let `C_p` be the span of the
creation words

`L_{-j_1-2} ... L_{-j_b-2} vacuum = negWordVir c [j_1, ..., j_b]`

with `j_1 + ... + j_b >= p`.  Since `L_{-j-2} = omega_(-j-1)` and `omega` has weight two, a
word has Li depth `j_1 + ... + j_b = N - 2 b` (weight `N`, length `b`).

Main results, for **every** central charge `c`:

* `liFiltration_eq_virWordPiece`: `F^p V(c,0) = C_p`;
* `simpleLiFiltration_eq_virWordPiece`: the intrinsic Li filtration of the simple quotient
  `L(c,0) = virasoroSimple c` is the image of `C_p`.

The proof is the Virasoro analogue of `AffineVOA.CurrentLi.liFiltration_eq_currentWordPiece`:
a tracked one-mode estimate from the Virasoro commutator, then the Borcherds iterate formula
for an arbitrary creation word on the left.  Only spanning is used, never PBW independence.
-/

namespace VOA
namespace VirasoroLi

open VOA.VirModule
open VOA.QuotVOA
open VOA.AffineVOA.CurrentLi (currentModeTarget)

noncomputable section

variable (c : ℂ)

/-- Li depth of a Virasoro creation word: entry `j` stands for `L_{-j-2} = omega_(-j-1)`. -/
abbrev virWordLevel (w : List ℕ) : ℕ := w.sum

/-- The span of Virasoro creation words of Li depth at least `p`. -/
def virWordPiece (p : ℕ) : Submodule ℂ (VirUniv c) :=
  Submodule.span ℂ {x | ∃ w : List ℕ, p ≤ virWordLevel w ∧ negWordVir c w = x}

theorem negWordVir_mem_virWordPiece (p : ℕ) (w : List ℕ) (hp : p ≤ virWordLevel w) :
    negWordVir c w ∈ virWordPiece c p :=
  Submodule.subset_span ⟨w, hp, rfl⟩

theorem virWordPiece_antitone {p q : ℕ} (hpq : p ≤ q) :
    virWordPiece c q ≤ virWordPiece c p := by
  rw [virWordPiece, virWordPiece, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  exact negWordVir_mem_virWordPiece c p w (hpq.trans hw)

theorem virWordPiece_zero_eq_top : virWordPiece c 0 = ⊤ := by
  apply le_antisymm le_top
  rw [← negSpanVir_eq_top c, negSpanVir, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact negWordVir_mem_virWordPiece c 0 w (Nat.zero_le _)

/-- The conformal vector as a one-letter generator family of weight two. -/
abbrev virGen : Fin 1 → VirUniv c := fun _ => omegaVir c

/-- Translate a Virasoro index list into a one-generator pair list. -/
abbrev virPairs (w : List ℕ) : List (Fin 1 × ℕ) := w.map (fun j => ((0 : Fin 1), j))

theorem pairsLevel_virPairs (w : List ℕ) : pairsLevel (virPairs w) = virWordLevel w := by
  induction w with
  | nil => rfl
  | cons j rest ih =>
      simp only [virPairs, virWordLevel, List.map_cons, pairsLevel_cons, List.sum_cons] at ih ⊢
      omega

/-- Virasoro creation words are exactly the generic generator words of `omega`. -/
theorem negWordVir_eq_generatorWord :
    ∀ w : List ℕ,
      negWordVir c w =
        wordAct (adjointWeakModule (virasoroVOA c))
          (genWord (virGen c) (fun _ : Fin 1 => 2) (virPairs w)) (virasoroVOA c).vacuum := by
  intro w
  induction w with
  | nil => rfl
  | cons j rest ih =>
      change negWordVir c (j :: rest) = wordAct (adjointWeakModule (virasoroVOA c))
          (genWord (virGen c) (fun _ : Fin 1 => 2) (((0 : Fin 1), j) :: virPairs rest))
          (virasoroVOA c).vacuum
      rw [negWordVir_cons, genWord_cons, wordAct_cons, ← ih]
      change Lop c (-(j : ℤ) - 2) (negWordVir c rest) =
        (virasoroVOA c).smul (omegaVir c) (-(j : ℤ) - 1) (negWordVir c rest)
      rw [LeeYang.smul_omegaVir]
      congr 2
      ring

/-- Easy inclusion: Virasoro word pieces lie in Li's filtration. -/
theorem virWordPiece_le_liFiltration (p : ℕ) :
    virWordPiece c p ≤ liFiltration (virasoroVOA c) p := by
  rw [virWordPiece, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  rw [negWordVir_eq_generatorWord c w]
  exact genWord_mem_Gfil (adjointWeakModule (virasoroVOA c))
    ({(virasoroVOA c).vacuum} : Set (VirUniv c))
    (fun _ => omegaVir_mem_gradingVir_two c) (virPairs w)
    (Set.mem_singleton _) (by rw [pairsLevel_virPairs]; exact_mod_cast hw)

/-- A creation mode prepends a letter and adds its depth. -/
theorem Lop_negSucc_mem_virWordPiece_add (r q : ℕ) {v : VirUniv c}
    (hv : v ∈ virWordPiece c q) :
    Lop c (-(r : ℤ) - 2) v ∈ virWordPiece c (q + r) := by
  rw [virWordPiece] at hv
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨right, hright, rfl⟩ := hz
      rw [← negWordVir_cons]
      exact negWordVir_mem_virWordPiece c (q + r) (r :: right) (by
        simp only [virWordLevel, List.sum_cons] at hright ⊢
        omega)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ihx => rw [map_smul]; exact Submodule.smul_mem _ a ihx

/-- **Tracked Virasoro commutation.**  The mode `omega_(n) = L_{n-1}` acting on a creation word
lands in the word piece predicted by the all-integer Li estimate `max(q-n-1,0)`. -/
theorem Lop_negWordVir_mem_virWordPiece :
    ∀ (right : List ℕ) (n : ℤ),
      Lop c (n - 1) (negWordVir c right) ∈
        virWordPiece c (currentModeTarget (virWordLevel right) n) := by
  intro right
  induction right with
  | nil =>
      intro n
      by_cases hn : 0 ≤ n
      · rw [negWordVir_nil, Lop_vacuum c (by omega)]
        exact Submodule.zero_mem _
      · obtain ⟨r, hr⟩ : ∃ r : ℕ, n = -(r : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
        subst n
        have ht : currentModeTarget (virWordLevel ([] : List ℕ)) (-(r : ℤ) - 1) = r := by
          simp [currentModeTarget, virWordLevel]
        rw [ht, negWordVir_nil, show (-(r : ℤ) - 1 - 1) = -(r : ℤ) - 2 by ring,
          ← negWordVir_nil c, ← negWordVir_cons]
        exact negWordVir_mem_virWordPiece c r [r] (by simp [virWordLevel])
  | cons j rest ih =>
      intro n
      by_cases hn : n < 0
      · obtain ⟨s, hs⟩ : ∃ s : ℕ, n = -(s : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
        subst n
        rw [show (-(s : ℤ) - 1 - 1) = -(s : ℤ) - 2 by ring, ← negWordVir_cons]
        exact negWordVir_mem_virWordPiece c _ (s :: j :: rest) (by
          simp only [currentModeTarget, virWordLevel, List.sum_cons]
          omega)
      · have hn0 : 0 ≤ n := le_of_not_gt hn
        rw [negWordVir_cons, LeeYang.Lop_apply_comm c (n - 1) (-(j : ℤ) - 2)]
        apply Submodule.add_mem
        · apply Submodule.add_mem
          · exact virWordPiece_antitone c (by
              simp only [currentModeTarget, virWordLevel, List.sum_cons]
              omega)
              (Lop_negSucc_mem_virWordPiece_add c j _ (ih n))
          · apply Submodule.smul_mem
            have h := ih (n - (j : ℤ) - 2)
            rw [show n - (j : ℤ) - 2 - 1 = n - 1 + (-(j : ℤ) - 2) by ring] at h
            exact virWordPiece_antitone c (by
              simp only [currentModeTarget, virWordLevel, List.sum_cons]
              omega) h
        · split_ifs with hzero
          · apply Submodule.smul_mem
            exact virWordPiece_antitone c (by
              simp only [currentModeTarget, virWordLevel, List.sum_cons]
              omega)
              (negWordVir_mem_virWordPiece c (virWordLevel rest) rest le_rfl)
          · rw [zero_smul]; exact Submodule.zero_mem _

/-- The tracked estimate extends linearly to a whole word piece. -/
theorem Lop_mem_virWordPiece (n : ℤ) (q : ℕ) {v : VirUniv c}
    (hv : v ∈ virWordPiece c q) :
    Lop c (n - 1) v ∈ virWordPiece c (currentModeTarget q n) := by
  rw [virWordPiece] at hv
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨right, hright, rfl⟩ := hz
      exact virWordPiece_antitone c (p := currentModeTarget q n)
        (q := currentModeTarget (virWordLevel right) n) (by
          simp only [currentModeTarget] at hright ⊢
          omega) (Lop_negWordVir_mem_virWordPiece c right n)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ihx => rw [map_smul]; exact Submodule.smul_mem _ a ihx

theorem smul_omegaVir_mem_virWordPiece (n : ℤ) (q : ℕ) {v : VirUniv c}
    (hv : v ∈ virWordPiece c q) :
    (virasoroVOA c).smul (omegaVir c) n v ∈ virWordPiece c (currentModeTarget q n) := by
  rw [LeeYang.smul_omegaVir]
  exact Lop_mem_virWordPiece c n q hv

theorem negWordVir_cons_eq_smul (j : ℕ) (rest : List ℕ) :
    negWordVir c (j :: rest) =
      (virasoroVOA c).smul (omegaVir c) (-(j : ℤ) - 1) (negWordVir c rest) := by
  rw [LeeYang.smul_omegaVir, negWordVir_cons]
  congr 2
  ring

/-- **All-mode normal-ordering estimate for Virasoro words.**  Mode `N` of any creation word
maps `C_q` into `C_{max(q-N-1,0)}`. -/
theorem negWordVir_mode_mem_virWordPiece :
    ∀ (left : List ℕ) (q : ℕ) (v : VirUniv c),
      v ∈ virWordPiece c q → ∀ N : ℤ,
        (virasoroVOA c).smul (negWordVir c left) N v ∈
          virWordPiece c (currentModeTarget q N) := by
  intro left
  induction left with
  | nil =>
      intro q v hv N
      rw [negWordVir_nil]
      change (virasoroVOA c).smul (virasoroVOA c).vacuum N v ∈ _
      rw [PreVertexAlgebra.smul_vacuum_left]
      split_ifs with hN
      · subst N
        simpa [currentModeTarget] using hv
      · exact Submodule.zero_mem _
  | cons r rest ih =>
      intro q v hv N
      rw [negWordVir_cons_eq_smul, VertexOperatorAlgebra.mode_iterate]
      apply QuotVOA.finsum_mem_submodule
      intro i
      apply Submodule.smul_mem
      apply Submodule.sub_mem
      · apply virWordPiece_antitone c
          (p := currentModeTarget q N)
          (q := currentModeTarget (currentModeTarget q (N + (i : ℤ)))
            (-(r : ℤ) - 1 - (i : ℤ)))
        · simp only [currentModeTarget]
          omega
        · exact smul_omegaVir_mem_virWordPiece c _ _ (ih q v hv (N + (i : ℤ)))
      · apply Submodule.smul_mem
        apply virWordPiece_antitone c
          (p := currentModeTarget q N)
          (q := currentModeTarget (currentModeTarget q (i : ℤ))
            ((-(r : ℤ) - 1) + N - (i : ℤ)))
        · simp only [currentModeTarget]
          omega
        · exact ih (currentModeTarget q (i : ℤ)) _
            (smul_omegaVir_mem_virWordPiece c (i : ℤ) q hv)
            ((-(r : ℤ) - 1) + N - (i : ℤ))

/-- Negative-mode closure of the word filtration, for an arbitrary left state. -/
theorem virWordNegativeModeClosed (q n : ℕ) (u : VirUniv c) {v : VirUniv c}
    (hv : v ∈ virWordPiece c q) :
    (virasoroVOA c).smul u (-(n : ℤ) - 1) v ∈ virWordPiece c (q + n) := by
  have hu : u ∈ Submodule.span ℂ (Set.range (negWordVir c)) := by
    rw [← negSpanVir, negSpanVir_eq_top c]
    exact Submodule.mem_top
  induction hu using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨left, rfl⟩ := hz
      have h := negWordVir_mode_mem_virWordPiece c left q v hv (-(n : ℤ) - 1)
      have ht : currentModeTarget q (-(n : ℤ) - 1) = q + n := by
        simp only [currentModeTarget]
        omega
      rwa [ht] at h
  | zero => rw [PreVertexAlgebra.smul_zero_left]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [PreVertexAlgebra.smul_add_left]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ihx =>
      rw [PreVertexAlgebra.smul_smul_left]; exact Submodule.smul_mem _ a ihx

private theorem wordAct_mem_virWordPiece :
    ∀ l : List (Letter (VirUniv c)),
      wordAct (adjointWeakModule (virasoroVOA c)) l (virasoroVOA c).vacuum ∈
        virWordPiece c (wordLevel l) := by
  intro l
  induction l with
  | nil =>
      change vacVec c ∈ virWordPiece c 0
      rw [← negWordVir_nil c]
      exact negWordVir_mem_virWordPiece c 0 [] (Nat.zero_le _)
  | cons a rest ih =>
      rw [wordAct_cons, wordLevel_cons]
      simpa only [PreVertexAlgebra.smul_def, Nat.add_comm] using
        virWordNegativeModeClosed c (wordLevel rest) a.2.2 a.1 ih

/-- Hard inclusion: every Li-filtration vector is a combination of creation words of at least
the same depth. -/
theorem liFiltration_le_virWordPiece (p : ℕ) :
    liFiltration (virasoroVOA c) p ≤ virWordPiece c p := by
  change Gfil (adjointWeakModule (virasoroVOA c))
      ({(virasoroVOA c).vacuum} : Set (VirUniv c)) (p : ℤ) ≤ virWordPiece c p
  rw [Gfil, Submodule.span_le]
  rintro _ ⟨l, w, _hl, hw, hlevel, rfl⟩
  have hw' : w = (virasoroVOA c).vacuum := Set.mem_singleton_iff.mp hw
  subst w
  exact virWordPiece_antitone c (by exact_mod_cast hlevel) (wordAct_mem_virWordPiece c l)

/-- **Li filtration of the universal Virasoro VOA** equals the creation-word filtration, for
every central charge. -/
theorem liFiltration_eq_virWordPiece (p : ℕ) :
    liFiltration (virasoroVOA c) p = virWordPiece c p :=
  le_antisymm (liFiltration_le_virWordPiece c p) (virWordPiece_le_liFiltration c p)

/-- **Li filtration of the simple Virasoro VOA** `L(c,0)`: the image of the creation-word
filtration under the quotient by the maximal ideal.  Unconditional, for every `c`. -/
theorem simpleLiFiltration_eq_virWordPiece (p : ℕ) :
    liFiltration (VirSimple.virasoroSimple c) p =
      (virWordPiece c p).map (VirSimple.maxIdealVir c).mkQ := by
  rw [← liFiltration_eq_virWordPiece c p]
  exact AffineVOA.CurrentLi.quotientLiFiltration_eq_map (virasoroVOA c)
    (maxGradedIdeal (virasoroVOA c)) (maxGradedIdeal_isIdeal _)
    (maxGradedIdeal_isGradedIdeal _) p

end

end VirasoroLi
end VOA
