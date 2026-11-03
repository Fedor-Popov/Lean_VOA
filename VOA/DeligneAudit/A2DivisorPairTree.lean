/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2DivisorPairGood

/-!
# The generation tree (generated)

Along the BFS tree of `A2DivisorPairCert`, each basis table `tB i` is good with the factor
`H^{dep i} (z_a - z_b)^{lev i} F` (`goodTree_i`); padded uniformly to `H⁴ (z_a - z_b)^{lev i} F`
(`goodLev`).
-/

namespace VOA.DeligneAudit.A2

open PairCert

noncomputable section

variable {m : ℕ} {a b : Fin m} (hab : a ≠ b) {s : Fin m → Fin 8} (hs : IsCanon a b s)
include hab hs

theorem goodTree0 : (Hpair a b ^ 0 * zab a b ^ 0 * Fspec a b) • castT tB0 ∈ Good a b s := by
  simpa using good_base hab hs

theorem goodTree1 : (Hpair a b ^ 1 * zab a b ^ 0 * Fspec a b) • castT tB1 ∈ Good a b s :=
  good_S_castT 3 hab (goodTree0 hab hs) tree1 (by ring)

theorem goodTree2 : (Hpair a b ^ 1 * zab a b ^ 0 * Fspec a b) • castT tB2 ∈ Good a b s :=
  good_S_castT 4 hab (goodTree0 hab hs) tree2 (by ring)

theorem goodTree3 : (Hpair a b ^ 1 * zab a b ^ 0 * Fspec a b) • castT tB3 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree0 hab hs) tree3 (by ring)

theorem goodTree4 : (Hpair a b ^ 2 * zab a b ^ 0 * Fspec a b) • castT tB4 ∈ Good a b s :=
  good_S_castT 3 hab (goodTree1 hab hs) tree4 (by ring)

theorem goodTree5 : (Hpair a b ^ 2 * zab a b ^ 0 * Fspec a b) • castT tB5 ∈ Good a b s :=
  good_S_castT 4 hab (goodTree1 hab hs) tree5 (by ring)

theorem goodTree6 : (Hpair a b ^ 2 * zab a b ^ 0 * Fspec a b) • castT tB6 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree1 hab hs) tree6 (by ring)

theorem goodTree7 : (Hpair a b ^ 2 * zab a b ^ 0 * Fspec a b) • castT tB7 ∈ Good a b s :=
  good_S_castT 4 hab (goodTree2 hab hs) tree7 (by ring)

theorem goodTree8 : (Hpair a b ^ 2 * zab a b ^ 0 * Fspec a b) • castT tB8 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree2 hab hs) tree8 (by ring)

theorem goodTree9 : (Hpair a b ^ 2 * zab a b ^ 0 * Fspec a b) • castT tB9 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree3 hab hs) tree9 (by ring)

theorem goodTree10 : (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) • castT tB10 ∈ Good a b s :=
  good_S_castT 4 hab (goodTree4 hab hs) tree10 (by ring)

theorem goodTree11 : (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) • castT tB11 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree4 hab hs) tree11 (by ring)

theorem goodTree12 : (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) • castT tB12 ∈ Good a b s :=
  good_S_castT 4 hab (goodTree5 hab hs) tree12 (by ring)

theorem goodTree13 : (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) • castT tB13 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree5 hab hs) tree13 (by ring)

theorem goodTree14 : (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) • castT tB14 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree6 hab hs) tree14 (by ring)

theorem goodTree15 : (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) • castT tB15 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree7 hab hs) tree15 (by ring)

theorem goodTree16 : (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) • castT tB16 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree8 hab hs) tree16 (by ring)

theorem goodTree17 : (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) • castT tB17 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree9 hab hs) tree17 (by ring)

theorem goodTree18 : (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) • castT tB18 ∈ Good a b s :=
  good_S_castT 4 hab (goodTree10 hab hs) tree18 (by ring)

theorem goodTree19 : (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) • castT tB19 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree10 hab hs) tree19 (by ring)

theorem goodTree20 : (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) • castT tB20 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree11 hab hs) tree20 (by ring)

theorem goodTree21 : (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) • castT tB21 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree12 hab hs) tree21 (by ring)

theorem goodTree22 : (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) • castT tB22 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree13 hab hs) tree22 (by ring)

theorem goodTree23 : (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) • castT tB23 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree14 hab hs) tree23 (by ring)

theorem goodTree24 : (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) • castT tB24 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree15 hab hs) tree24 (by ring)

theorem goodTree25 : (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) • castT tB25 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree16 hab hs) tree25 (by ring)

theorem goodTree26 : (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) • castT tB26 ∈ Good a b s :=
  good_S_castT 5 hab (goodTree17 hab hs) tree26 (by ring)

theorem goodTree27 : (Hpair a b ^ 1 * zab a b ^ 1 * Fspec a b) • castT tB27 ∈ Good a b s :=
  good_A_castT 3 hab (goodTree0 hab hs) tree27 (by ring)

theorem goodTree28 : (Hpair a b ^ 1 * zab a b ^ 1 * Fspec a b) • castT tB28 ∈ Good a b s :=
  good_A_castT 4 hab (goodTree0 hab hs) tree28 (by ring)

theorem goodTree29 : (Hpair a b ^ 1 * zab a b ^ 1 * Fspec a b) • castT tB29 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree0 hab hs) tree29 (by ring)

theorem goodTree30 : (Hpair a b ^ 2 * zab a b ^ 1 * Fspec a b) • castT tB30 ∈ Good a b s :=
  good_A_castT 4 hab (goodTree1 hab hs) tree30 (by ring)

theorem goodTree31 : (Hpair a b ^ 2 * zab a b ^ 1 * Fspec a b) • castT tB31 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree1 hab hs) tree31 (by ring)

theorem goodTree32 : (Hpair a b ^ 2 * zab a b ^ 1 * Fspec a b) • castT tB32 ∈ Good a b s :=
  good_A_castT 3 hab (goodTree2 hab hs) tree32 (by ring)

theorem goodTree33 : (Hpair a b ^ 2 * zab a b ^ 1 * Fspec a b) • castT tB33 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree2 hab hs) tree33 (by ring)

theorem goodTree34 : (Hpair a b ^ 2 * zab a b ^ 1 * Fspec a b) • castT tB34 ∈ Good a b s :=
  good_A_castT 3 hab (goodTree3 hab hs) tree34 (by ring)

theorem goodTree35 : (Hpair a b ^ 2 * zab a b ^ 1 * Fspec a b) • castT tB35 ∈ Good a b s :=
  good_A_castT 4 hab (goodTree3 hab hs) tree35 (by ring)

theorem goodTree36 : (Hpair a b ^ 2 * zab a b ^ 1 * Fspec a b) • castT tB36 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree3 hab hs) tree36 (by ring)

theorem goodTree37 : (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) • castT tB37 ∈ Good a b s :=
  good_A_castT 4 hab (goodTree4 hab hs) tree37 (by ring)

theorem goodTree38 : (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) • castT tB38 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree4 hab hs) tree38 (by ring)

theorem goodTree39 : (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) • castT tB39 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree5 hab hs) tree39 (by ring)

theorem goodTree40 : (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) • castT tB40 ∈ Good a b s :=
  good_A_castT 4 hab (goodTree6 hab hs) tree40 (by ring)

theorem goodTree41 : (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) • castT tB41 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree6 hab hs) tree41 (by ring)

theorem goodTree42 : (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) • castT tB42 ∈ Good a b s :=
  good_A_castT 3 hab (goodTree7 hab hs) tree42 (by ring)

theorem goodTree43 : (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) • castT tB43 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree7 hab hs) tree43 (by ring)

theorem goodTree44 : (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) • castT tB44 ∈ Good a b s :=
  good_A_castT 3 hab (goodTree8 hab hs) tree44 (by ring)

theorem goodTree45 : (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) • castT tB45 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree8 hab hs) tree45 (by ring)

theorem goodTree46 : (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) • castT tB46 ∈ Good a b s :=
  good_A_castT 3 hab (goodTree9 hab hs) tree46 (by ring)

theorem goodTree47 : (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) • castT tB47 ∈ Good a b s :=
  good_A_castT 4 hab (goodTree9 hab hs) tree47 (by ring)

theorem goodTree48 : (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) • castT tB48 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree9 hab hs) tree48 (by ring)

theorem goodTree49 : (Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b) • castT tB49 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree10 hab hs) tree49 (by ring)

theorem goodTree50 : (Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b) • castT tB50 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree12 hab hs) tree50 (by ring)

theorem goodTree51 : (Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b) • castT tB51 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree13 hab hs) tree51 (by ring)

theorem goodTree52 : (Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b) • castT tB52 ∈ Good a b s :=
  good_A_castT 4 hab (goodTree14 hab hs) tree52 (by ring)

theorem goodTree53 : (Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b) • castT tB53 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree14 hab hs) tree53 (by ring)

theorem goodTree54 : (Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b) • castT tB54 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree16 hab hs) tree54 (by ring)

theorem goodTree55 : (Hpair a b ^ 2 * zab a b ^ 2 * Fspec a b) • castT tB55 ∈ Good a b s :=
  good_A_castT 4 hab (goodTree27 hab hs) tree55 (by ring)

theorem goodTree56 : (Hpair a b ^ 2 * zab a b ^ 2 * Fspec a b) • castT tB56 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree27 hab hs) tree56 (by ring)

theorem goodTree57 : (Hpair a b ^ 2 * zab a b ^ 2 * Fspec a b) • castT tB57 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree28 hab hs) tree57 (by ring)

theorem goodTree58 : (Hpair a b ^ 2 * zab a b ^ 2 * Fspec a b) • castT tB58 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree29 hab hs) tree58 (by ring)

theorem goodTree59 : (Hpair a b ^ 3 * zab a b ^ 2 * Fspec a b) • castT tB59 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree30 hab hs) tree59 (by ring)

theorem goodTree60 : (Hpair a b ^ 3 * zab a b ^ 2 * Fspec a b) • castT tB60 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree31 hab hs) tree60 (by ring)

theorem goodTree61 : (Hpair a b ^ 3 * zab a b ^ 2 * Fspec a b) • castT tB61 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree32 hab hs) tree61 (by ring)

theorem goodTree62 : (Hpair a b ^ 3 * zab a b ^ 2 * Fspec a b) • castT tB62 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree33 hab hs) tree62 (by ring)

theorem goodTree63 : (Hpair a b ^ 4 * zab a b ^ 2 * Fspec a b) • castT tB63 ∈ Good a b s :=
  good_A_castT 5 hab (goodTree39 hab hs) tree63 (by ring)

theorem good_pad {q : Pm m} {T : PairTable m} (p : Pm m) (h : q • T ∈ Good a b s) :
    (p * q) • T ∈ Good a b s := by
  rw [mul_smul]; exact Submodule.smul_mem _ _ h

/-- **Every basis table is good with factor `H⁴ (z_a - z_b)^{lev} F`.** -/
theorem goodLev (i : Fin 64) :
    (Hpair a b ^ 4 * zab a b ^ lev i * Fspec a b) • castT (tB i) ∈ Good a b s := by
  fin_cases i
  · have h := good_pad hab hs (Hpair a b ^ 4) (goodTree0 hab hs)
    rw [show Hpair a b ^ 4 * (Hpair a b ^ 0 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 3) (goodTree1 hab hs)
    rw [show Hpair a b ^ 3 * (Hpair a b ^ 1 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 3) (goodTree2 hab hs)
    rw [show Hpair a b ^ 3 * (Hpair a b ^ 1 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 3) (goodTree3 hab hs)
    rw [show Hpair a b ^ 3 * (Hpair a b ^ 1 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree4 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree5 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree6 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree7 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree8 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree9 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree10 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree11 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree12 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree13 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree14 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree15 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree16 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree17 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree18 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree19 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree20 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree21 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree22 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree23 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree24 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree25 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree26 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 0 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 3) (goodTree27 hab hs)
    rw [show Hpair a b ^ 3 * (Hpair a b ^ 1 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 3) (goodTree28 hab hs)
    rw [show Hpair a b ^ 3 * (Hpair a b ^ 1 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 3) (goodTree29 hab hs)
    rw [show Hpair a b ^ 3 * (Hpair a b ^ 1 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree30 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree31 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree32 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree33 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree34 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree35 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree36 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree37 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree38 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree39 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree40 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree41 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree42 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree43 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree44 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree45 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree46 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree47 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree48 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree49 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree50 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree51 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree52 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree53 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree54 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 1 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree55 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 2 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 2 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree56 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 2 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 2 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree57 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 2 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 2 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 2) (goodTree58 hab hs)
    rw [show Hpair a b ^ 2 * (Hpair a b ^ 2 * zab a b ^ 2 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 2 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree59 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 2 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 2 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree60 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 2 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 2 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree61 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 2 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 2 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 1) (goodTree62 hab hs)
    rw [show Hpair a b ^ 1 * (Hpair a b ^ 3 * zab a b ^ 2 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 2 * Fspec a b by ring] at h
    exact h
  · have h := good_pad hab hs (Hpair a b ^ 0) (goodTree63 hab hs)
    rw [show Hpair a b ^ 0 * (Hpair a b ^ 4 * zab a b ^ 2 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ 2 * Fspec a b by ring] at h
    exact h

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.goodLev
end AxiomAudit
