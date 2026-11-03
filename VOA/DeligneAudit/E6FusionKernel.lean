/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionKernelGeneric
import VOA.DeligneAudit.E6SectorData
import VOA.DeligneAudit.E6FusionKernelData
import VOA.DeligneAudit.E6FusionKernelFixed42
import VOA.DeligneAudit.E6FusionKernelFixed43
import VOA.DeligneAudit.E6FusionKernelFixed44
import VOA.DeligneAudit.E6FusionKernelFixed45
import VOA.DeligneAudit.E6FusionKernelFixed46
import VOA.DeligneAudit.E6FusionKernelFixed47
import VOA.DeligneAudit.E6FusionKernelFixed51
import VOA.DeligneAudit.E6FusionKernelFixed55
import VOA.DeligneAudit.E6FusionKernelFixed56
import VOA.DeligneAudit.E6FusionKernelFixed59
import VOA.DeligneAudit.E6FusionKernelFixed60
import VOA.DeligneAudit.E6FusionKernelFixed62
import VOA.DeligneAudit.E6FusionKernelFixed63
import VOA.DeligneAudit.E6FusionKernelFixed64
import VOA.DeligneAudit.E6FusionKernelFixed66
import VOA.DeligneAudit.E6FusionKernelFixed67
import VOA.DeligneAudit.E6FusionKernelFixed68
import VOA.DeligneAudit.E6FusionKernelFixed69
import VOA.DeligneAudit.E6FusionKernelFixed70
import VOA.DeligneAudit.E6FusionKernelFixed71
import VOA.DeligneAudit.E6FusionKernelFixed72
import VOA.DeligneAudit.E6FusionKernelFixed73
import VOA.DeligneAudit.E6FusionKernelFixed74
import VOA.DeligneAudit.E6FusionKernelFixed75
import VOA.DeligneAudit.E6FusionKernelFixed76
import VOA.DeligneAudit.E6FusionKernelFixed77
import VOA.DeligneAudit.E6FusionKernelRaising06
import VOA.DeligneAudit.E6FusionKernelRaising07
import VOA.DeligneAudit.E6FusionKernelRaising08
import VOA.DeligneAudit.E6FusionKernelRaising09
import VOA.DeligneAudit.E6FusionKernelRaising10
import VOA.DeligneAudit.E6FusionKernelRaising11
import VOA.DeligneAudit.E6FusionKernelRaising12
import VOA.DeligneAudit.E6FusionKernelRaising13
import VOA.DeligneAudit.E6FusionKernelRaising14
import VOA.DeligneAudit.E6FusionKernelRaising15
import VOA.DeligneAudit.E6FusionKernelRaising16
import VOA.DeligneAudit.E6FusionKernelRaising17
import VOA.DeligneAudit.E6FusionKernelRaising18
import VOA.DeligneAudit.E6FusionKernelRaising19
import VOA.DeligneAudit.E6FusionKernelRaising20
import VOA.DeligneAudit.E6FusionKernelRaising21
import VOA.DeligneAudit.E6FusionKernelRaising22
import VOA.DeligneAudit.E6FusionKernelRaising23
import VOA.DeligneAudit.E6FusionKernelRaising24
import VOA.DeligneAudit.E6FusionKernelRaising25
import VOA.DeligneAudit.E6FusionKernelRaising26
import VOA.DeligneAudit.E6FusionKernelRaising27
import VOA.DeligneAudit.E6FusionKernelRaising28
import VOA.DeligneAudit.E6FusionKernelRaising29
import VOA.DeligneAudit.E6FusionKernelRaising30
import VOA.DeligneAudit.E6FusionKernelRaising31
import VOA.DeligneAudit.E6FusionKernelRaising32
import VOA.DeligneAudit.E6FusionKernelRaising33
import VOA.DeligneAudit.E6FusionKernelRaising34
import VOA.DeligneAudit.E6FusionKernelRaising35
import VOA.DeligneAudit.E6FusionKernelRaising36
import VOA.DeligneAudit.E6FusionKernelRaising37
import VOA.DeligneAudit.E6FusionKernelRaising38
import VOA.DeligneAudit.E6FusionKernelRaising39
import VOA.DeligneAudit.E6FusionKernelRaising40
import VOA.DeligneAudit.E6FusionKernelRaising41
import VOA.DeligneAudit.E6FusionKernelCartan00
import VOA.DeligneAudit.E6FusionKernelCartan01
import VOA.DeligneAudit.E6FusionKernelCartan02
import VOA.DeligneAudit.E6FusionKernelCartan03
import VOA.DeligneAudit.E6FusionKernelCartan04
import VOA.DeligneAudit.E6FusionKernelCartan05
import VOA.DeligneAudit.E6FusionKernelSmallChecks

/-!
# `E₆`: the kernel table for Ravinder's family

`e6KernelTable : KernelTable E6sector` collects the structure-constant facts, each checked by kernel `decide` on
the table `e6T`. The table scan is `Notes/deligne/campaign/generators/e6_kernel_scan.py`, and the data is in
`e7_data/kernel_e6.json`. This file was produced from `E7FusionKernel` by `e6_emit_kernel.py`.

* `e_θ = x₄₁` with `s_θ = -1`, and `θ(h₁) = 1`.
* The one simple lowering vector with `θ(h) = 1` is `f_{α₂} = x₄₆`, with `sl₂` partner `e = x₁₀` and `h = h₁`.
* `β(x)` with `[e_β, f_θ] = κ f_x` is given for the 20 fusion roots `x ≠ f_θ`.
* The five simple roots orthogonal to `θ` are lowering vectors with `lowExp = 0`.

The declarations are in the namespace `UnivG.E6K`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.UnivG.E6K

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (E6sector thetaH lowExpE6 fusionE6)

noncomputable section



theorem fE6K_eq (a b c : Fin 78) : E6sector.f a b c = (fZ brK a b c : ℂ) := rfl





theorem fusion_iff : ∀ x : Fin 78, fusionE6 x ↔ x.val ∈ fusL := by
  unfold fusionE6 VOA.DeligneAudit.DeligneCarrier.E6.thetaPair; decide +kernel

theorem lowering_iff (x : Fin 78) : E6sector.lowering x ↔ x.val ∈ lowL := by
  show x.val ∈ [47, 46, 45, 44, 43, 42] ↔ _
  simp only [lowL, List.mem_cons, List.not_mem_nil, or_false]; omega













theorem e6_truncUpZ : ∀ x : Fin 78, x.val ∈ fusL ∨ x.val ∈ lowL →
    (hselK x).val < 6 ∧ fZ brK (hselK x) x x ≠ 0 ∧
      ∀ c : Fin 78, c ≠ x → fZ brK (hselK x) x c = 0 := by
  intro x hx
  rcases hx with h | h
  · simp only [fusL, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
    · have heq : x = (46 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_46
    · have heq : x = (51 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_51
    · have heq : x = (55 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_55
    · have heq : x = (56 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_56
    · have heq : x = (59 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_59
    · have heq : x = (60 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_60
    · have heq : x = (62 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_62
    · have heq : x = (63 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_63
    · have heq : x = (64 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_64
    · have heq : x = (66 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_66
    · have heq : x = (67 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_67
    · have heq : x = (68 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_68
    · have heq : x = (69 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_69
    · have heq : x = (70 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_70
    · have heq : x = (71 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_71
    · have heq : x = (72 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_72
    · have heq : x = (73 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_73
    · have heq : x = (74 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_74
    · have heq : x = (75 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_75
    · have heq : x = (76 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_76
    · have heq : x = (77 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_77
  · simp only [lowL, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with hx | hx | hx | hx | hx | hx
    · have heq : x = (42 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_42
    · have heq : x = (43 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_43
    · have heq : x = (44 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_44
    · have heq : x = (45 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_45
    · have heq : x = (46 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_46
    · have heq : x = (47 : Fin 78) := Fin.ext hx
      subst x
      exact trunc_47

theorem e6_raisThetaZ : ∀ e c : Fin 78, 6 ≤ e.val → e.val < 42 → fZ brK e 77 c ≠ 0 →
    c.val < 6 ∨ (c.val ∈ fusL ∧ c ≠ 77) := by
  intro e c hlo hhi hn
  fin_cases e
  · exact False.elim ((by decide : ¬ (6 ≤ (0 : Fin 78).val ∧ (0 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (1 : Fin 78).val ∧ (1 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (2 : Fin 78).val ∧ (2 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (3 : Fin 78).val ∧ (3 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (4 : Fin 78).val ∧ (4 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (5 : Fin 78).val ∧ (5 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact raising_6 c hn
  · exact raising_7 c hn
  · exact raising_8 c hn
  · exact raising_9 c hn
  · exact raising_10 c hn
  · exact raising_11 c hn
  · exact raising_12 c hn
  · exact raising_13 c hn
  · exact raising_14 c hn
  · exact raising_15 c hn
  · exact raising_16 c hn
  · exact raising_17 c hn
  · exact raising_18 c hn
  · exact raising_19 c hn
  · exact raising_20 c hn
  · exact raising_21 c hn
  · exact raising_22 c hn
  · exact raising_23 c hn
  · exact raising_24 c hn
  · exact raising_25 c hn
  · exact raising_26 c hn
  · exact raising_27 c hn
  · exact raising_28 c hn
  · exact raising_29 c hn
  · exact raising_30 c hn
  · exact raising_31 c hn
  · exact raising_32 c hn
  · exact raising_33 c hn
  · exact raising_34 c hn
  · exact raising_35 c hn
  · exact raising_36 c hn
  · exact raising_37 c hn
  · exact raising_38 c hn
  · exact raising_39 c hn
  · exact raising_40 c hn
  · exact raising_41 c hn
  · exact False.elim ((by decide : ¬ (6 ≤ (42 : Fin 78).val ∧ (42 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (43 : Fin 78).val ∧ (43 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (44 : Fin 78).val ∧ (44 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (45 : Fin 78).val ∧ (45 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (46 : Fin 78).val ∧ (46 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (47 : Fin 78).val ∧ (47 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (48 : Fin 78).val ∧ (48 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (49 : Fin 78).val ∧ (49 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (50 : Fin 78).val ∧ (50 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (51 : Fin 78).val ∧ (51 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (52 : Fin 78).val ∧ (52 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (53 : Fin 78).val ∧ (53 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (54 : Fin 78).val ∧ (54 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (55 : Fin 78).val ∧ (55 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (56 : Fin 78).val ∧ (56 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (57 : Fin 78).val ∧ (57 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (58 : Fin 78).val ∧ (58 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (59 : Fin 78).val ∧ (59 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (60 : Fin 78).val ∧ (60 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (61 : Fin 78).val ∧ (61 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (62 : Fin 78).val ∧ (62 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (63 : Fin 78).val ∧ (63 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (64 : Fin 78).val ∧ (64 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (65 : Fin 78).val ∧ (65 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (66 : Fin 78).val ∧ (66 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (67 : Fin 78).val ∧ (67 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (68 : Fin 78).val ∧ (68 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (69 : Fin 78).val ∧ (69 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (70 : Fin 78).val ∧ (70 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (71 : Fin 78).val ∧ (71 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (72 : Fin 78).val ∧ (72 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (73 : Fin 78).val ∧ (73 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (74 : Fin 78).val ∧ (74 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (75 : Fin 78).val ∧ (75 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (76 : Fin 78).val ∧ (76 : Fin 78).val < 42)) ⟨hlo, hhi⟩)
  · exact False.elim ((by decide : ¬ (6 ≤ (77 : Fin 78).val ∧ (77 : Fin 78).val < 42)) ⟨hlo, hhi⟩)

theorem e6_cartThetaZ : ∀ h c : Fin 78, h.val < 6 →
    fZ brK h 77 c = if c = 77 then -(thetaH h : ℤ) else 0 := by
  intro h c hh
  fin_cases h
  · exact cartan_0 c
  · exact cartan_1 c
  · exact cartan_2 c
  · exact cartan_3 c
  · exact cartan_4 c
  · exact cartan_5 c
  · exact False.elim ((by decide : ¬ (6 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (7 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (8 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (9 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (10 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (11 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (12 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (13 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (14 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (15 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (16 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (17 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (18 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (19 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (20 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (21 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (22 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (23 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (24 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (25 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (26 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (27 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (28 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (29 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (30 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (31 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (32 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (33 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (34 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (35 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (36 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (37 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (38 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (39 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (40 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (41 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (42 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (43 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (44 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (45 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (46 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (47 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (48 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (49 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (50 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (51 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (52 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (53 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (54 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (55 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (56 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (57 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (58 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (59 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (60 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (61 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (62 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (63 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (64 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (65 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (66 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (67 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (68 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (69 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (70 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (71 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (72 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (73 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (74 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (75 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (76 : Fin 78).val < 6) hh)
  · exact False.elim ((by decide : ¬ (77 : Fin 78).val < 6) hh)

theorem e6_lowCommZ : ∀ x c : Fin 78, x.val ∈ fusL ∨ x.val ∈ lowL → fZ brK x 77 c = 0 := by
  intro x c hx
  rcases hx with h | h
  · simp only [fusL, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
    · have heq : x = (46 : Fin 78) := Fin.ext hx
      subst x
      exact low_46 c
    · have heq : x = (51 : Fin 78) := Fin.ext hx
      subst x
      exact low_51 c
    · have heq : x = (55 : Fin 78) := Fin.ext hx
      subst x
      exact low_55 c
    · have heq : x = (56 : Fin 78) := Fin.ext hx
      subst x
      exact low_56 c
    · have heq : x = (59 : Fin 78) := Fin.ext hx
      subst x
      exact low_59 c
    · have heq : x = (60 : Fin 78) := Fin.ext hx
      subst x
      exact low_60 c
    · have heq : x = (62 : Fin 78) := Fin.ext hx
      subst x
      exact low_62 c
    · have heq : x = (63 : Fin 78) := Fin.ext hx
      subst x
      exact low_63 c
    · have heq : x = (64 : Fin 78) := Fin.ext hx
      subst x
      exact low_64 c
    · have heq : x = (66 : Fin 78) := Fin.ext hx
      subst x
      exact low_66 c
    · have heq : x = (67 : Fin 78) := Fin.ext hx
      subst x
      exact low_67 c
    · have heq : x = (68 : Fin 78) := Fin.ext hx
      subst x
      exact low_68 c
    · have heq : x = (69 : Fin 78) := Fin.ext hx
      subst x
      exact low_69 c
    · have heq : x = (70 : Fin 78) := Fin.ext hx
      subst x
      exact low_70 c
    · have heq : x = (71 : Fin 78) := Fin.ext hx
      subst x
      exact low_71 c
    · have heq : x = (72 : Fin 78) := Fin.ext hx
      subst x
      exact low_72 c
    · have heq : x = (73 : Fin 78) := Fin.ext hx
      subst x
      exact low_73 c
    · have heq : x = (74 : Fin 78) := Fin.ext hx
      subst x
      exact low_74 c
    · have heq : x = (75 : Fin 78) := Fin.ext hx
      subst x
      exact low_75 c
    · have heq : x = (76 : Fin 78) := Fin.ext hx
      subst x
      exact low_76 c
    · have heq : x = (77 : Fin 78) := Fin.ext hx
      subst x
      exact low_77 c
  · simp only [lowL, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with hx | hx | hx | hx | hx | hx
    · have heq : x = (42 : Fin 78) := Fin.ext hx
      subst x
      exact low_42 c
    · have heq : x = (43 : Fin 78) := Fin.ext hx
      subst x
      exact low_43 c
    · have heq : x = (44 : Fin 78) := Fin.ext hx
      subst x
      exact low_44 c
    · have heq : x = (45 : Fin 78) := Fin.ext hx
      subst x
      exact low_45 c
    · have heq : x = (46 : Fin 78) := Fin.ext hx
      subst x
      exact low_46 c
    · have heq : x = (47 : Fin 78) := Fin.ext hx
      subst x
      exact low_47 c

theorem e6_simpleZ : (∀ c : Fin 78, fZ brK 10 46 c = if c = 1 then 1 else 0) ∧
    (∀ c : Fin 78, fZ brK 1 46 c = if c = 46 then -2 else 0) := by
  exact small_simpleZ

theorem e6_eθZ : (∀ c : Fin 78, fZ brK 41 77 c ≠ 0 → c.val < 6) ∧ fZ brK 41 77 1 = -2 := by
  exact small_eθZ

theorem e6_rootZ : ∀ x : Fin 78, x.val ∈ fusL → x ≠ 77 →
    6 ≤ (bselK x).val ∧ (bselK x).val < 42 ∧ kselK x ≠ 0 ∧
      ∀ c : Fin 78, fZ brK (bselK x) 77 c = if c = x then kselK x else 0 := by
  intro x h hne
  simp only [fusL, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  · have heq : x = (46 : Fin 78) := Fin.ext hx
    subst x
    exact root_46
  · have heq : x = (51 : Fin 78) := Fin.ext hx
    subst x
    exact root_51
  · have heq : x = (55 : Fin 78) := Fin.ext hx
    subst x
    exact root_55
  · have heq : x = (56 : Fin 78) := Fin.ext hx
    subst x
    exact root_56
  · have heq : x = (59 : Fin 78) := Fin.ext hx
    subst x
    exact root_59
  · have heq : x = (60 : Fin 78) := Fin.ext hx
    subst x
    exact root_60
  · have heq : x = (62 : Fin 78) := Fin.ext hx
    subst x
    exact root_62
  · have heq : x = (63 : Fin 78) := Fin.ext hx
    subst x
    exact root_63
  · have heq : x = (64 : Fin 78) := Fin.ext hx
    subst x
    exact root_64
  · have heq : x = (66 : Fin 78) := Fin.ext hx
    subst x
    exact root_66
  · have heq : x = (67 : Fin 78) := Fin.ext hx
    subst x
    exact root_67
  · have heq : x = (68 : Fin 78) := Fin.ext hx
    subst x
    exact root_68
  · have heq : x = (69 : Fin 78) := Fin.ext hx
    subst x
    exact root_69
  · have heq : x = (70 : Fin 78) := Fin.ext hx
    subst x
    exact root_70
  · have heq : x = (71 : Fin 78) := Fin.ext hx
    subst x
    exact root_71
  · have heq : x = (72 : Fin 78) := Fin.ext hx
    subst x
    exact root_72
  · have heq : x = (73 : Fin 78) := Fin.ext hx
    subst x
    exact root_73
  · have heq : x = (74 : Fin 78) := Fin.ext hx
    subst x
    exact root_74
  · have heq : x = (75 : Fin 78) := Fin.ext hx
    subst x
    exact root_75
  · have heq : x = (76 : Fin 78) := Fin.ext hx
    subst x
    exact root_76
  · have heq : x = (77 : Fin 78) := Fin.ext hx
    subst x
    exact (hne rfl).elim

theorem fus_or_low {x : Fin 78} (hx : E6sector.fusion x ∨ E6sector.lowering x) :
    x.val ∈ fusL ∨ x.val ∈ lowL := by
  rcases hx with hx | hx
  · exact Or.inl ((fusion_iff x).mp hx)
  · exact Or.inr ((lowering_iff x).mp hx)

theorem e6_truncUp (x : Fin 78) (hx : E6sector.fusion x ∨ E6sector.lowering x) :
    ∃ h, E6sector.cartan h ∧ E6sector.f h x x ≠ 0 ∧ ∀ c, c ≠ x → E6sector.f h x c = 0 := by
  obtain ⟨h1, h2, h3⟩ := e6_truncUpZ x (fus_or_low hx)
  refine ⟨hselK x, h1, ?_, fun c hc => ?_⟩
  · rw [fE6K_eq]; exact_mod_cast h2
  · rw [fE6K_eq, h3 c hc, Int.cast_zero]

theorem e6_raisTheta (e : Fin 78) (he : E6sector.raising e) (c : Fin 78)
    (hc : E6sector.f e E6sector.c₀ c ≠ 0) :
    E6sector.cartan c ∨ (E6sector.fusion c ∧ c ≠ E6sector.c₀) := by
  have hc' : fZ brK e 77 c ≠ 0 := by
    intro h0; apply hc; show ((fZ brK e 77 c : ℤ) : ℂ) = 0; rw [h0, Int.cast_zero]
  rcases e6_raisThetaZ e c he.1 he.2 hc' with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨(fusion_iff c).mpr h1, h2⟩

theorem e6_cartTheta (h : Fin 78) (hh : E6sector.cartan h) (c : Fin 78) :
    E6sector.f h E6sector.c₀ c = if c = E6sector.c₀ then -(E6sector.thetaH h : ℂ) else 0 := by
  show ((fZ brK h 77 c : ℤ) : ℂ) = if c = 77 then -((thetaH h : ℕ) : ℂ) else 0
  rw [e6_cartThetaZ h c hh]
  split_ifs <;> simp

theorem e6_lowComm (x : Fin 78) (hx : E6sector.fusion x ∨ E6sector.lowering x) (c : Fin 78) :
    E6sector.f x E6sector.c₀ c = 0 := by
  show ((fZ brK x 77 c : ℤ) : ℂ) = 0
  rw [e6_lowCommZ x c (fus_or_low hx), Int.cast_zero]

theorem e6_lowExp_le (i : Fin 78) : lowExpE6 i ≤ 1 := by
  unfold lowExpE6; split_ifs <;> omega

theorem e6_simple (i : Fin 78) (h1 : lowExpE6 i = 1) :
    ∃ e hi : Fin 78, E6sector.raising e ∧ E6sector.cartan hi ∧
      (∀ c : Fin 78, E6sector.f e i c = if c = hi then 1 else 0) ∧ E6sector.thetaH hi = 1 ∧
      (∀ c : Fin 78, E6sector.f hi i c = if c = i then -2 else 0) := by
  have hi76 : i = (46 : Fin 78) := by
    unfold lowExpE6 at h1
    split_ifs at h1 with h h'
    exact h'
  subst hi76
  refine ⟨(10 : Fin 78), (1 : Fin 78), (show 6 ≤ ((10 : Fin 78) : ℕ) ∧ ((10 : Fin 78) : ℕ) < 42 by decide),
    (show ((1 : Fin 78) : ℕ) < 6 by decide), fun c => ?_, by decide, fun c => ?_⟩
  · show ((fZ brK 10 46 c : ℤ) : ℂ) = if (c : Fin 78) = 1 then 1 else 0
    rw [e6_simpleZ.1 c]; split_ifs <;> simp
  · show ((fZ brK 1 46 c : ℤ) : ℂ) = if (c : Fin 78) = 46 then -2 else 0
    rw [e6_simpleZ.2 c]; split_ifs <;> simp

theorem e6_eθ_cartan (c : Fin 78) (hc : E6sector.f (41 : Fin 78) E6sector.c₀ c ≠ 0) : E6sector.cartan c := by
  have : ((fZ brK 41 77 c : ℤ) : ℂ) ≠ 0 := hc
  exact e6_eθZ.1 c (by exact_mod_cast this)

theorem e6_eθ_theta :
    (-1 : ℂ) * ∑ c : Fin 78, E6sector.f (41 : Fin 78) E6sector.c₀ c * (E6sector.thetaH c : ℂ) = 2 := by
  rw [Finset.sum_eq_single (1 : Fin 78)]
  · show (-1 : ℂ) * (((fZ brK 41 77 1 : ℤ) : ℂ) * ((thetaH 1 : ℕ) : ℂ)) = 2
    rw [e6_eθZ.2]; simp [thetaH]
  · intro c _ hc
    have : thetaH c = 0 := by unfold thetaH; simp [hc]
    show _ * ((thetaH c : ℕ) : ℂ) = 0
    rw [this]; simp
  · simp

theorem e6_fusionRoot (x : Fin 78) (hx : E6sector.fusion x) (hx0 : x ≠ E6sector.c₀) :
    (∃ (β : Fin 78) (κ : ℂ), E6sector.raising β ∧ κ ≠ 0 ∧
      ∀ c : Fin 78, E6sector.f β E6sector.c₀ c = if c = x then κ else 0) ∨
      (E6sector.lowering x ∧ E6sector.lowExp x = 0) := by
  left
  obtain ⟨h1, h2, h3, h4⟩ := e6_rootZ x ((fusion_iff x).mp hx) hx0
  refine ⟨bselK x, (kselK x : ℂ), ⟨h1, h2⟩, by exact_mod_cast h3, fun c => ?_⟩
  show ((fZ brK (bselK x) 77 c : ℤ) : ℂ) = if (c : Fin 78) = x then (kselK x : ℂ) else 0
  rw [h4 c]; split_ifs <;> simp

/-- The `E₆` kernel table in the simply-laced interface. -/
def e6KernelTableSL : KernelTableSL E6sector where
  noN := fun _ hh => hh
  c0_fusion := (fusion_iff 77).mpr (by decide)
  truncUp := e6_truncUp
  raisTheta := e6_raisTheta
  cartTheta := e6_cartTheta
  lowComm := e6_lowComm
  lowExp_le i _ := e6_lowExp_le i
  simple i _ h1 := e6_simple i h1
  eθ := (41 : Fin 78)
  sθ := -1
  eθ_raising := show 6 ≤ ((41 : Fin 78) : ℕ) ∧ ((41 : Fin 78) : ℕ) < 42 by decide
  eθ_cartan := e6_eθ_cartan
  eθ_theta := e6_eθ_theta
  fusionRoot := e6_fusionRoot

/-- **The `E₆` kernel table.** -/
def e6KernelTable : KernelTable E6sector := KernelTable.ofSL e6KernelTableSL

/-- **Ravinder's kernel lemma for `E₆`**, from the integrability input `ThetaNilG`
(proved: `e6_thetaNil`). -/
theorem e6_ravinderKernelRel (hN : ThetaNilG E6sector) :
    RavinderKernelRelG E6sector.f (ravFam E6sector) (ravKw E6sector) :=
  ravinderKernelRelG_of_table E6sector e6KernelTable hN

end

end VOA.DeligneAudit.UnivG.E6K

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.E6K.e6KernelTable
#print axioms VOA.DeligneAudit.UnivG.E6K.e6_ravinderKernelRel
end AxiomAudit
