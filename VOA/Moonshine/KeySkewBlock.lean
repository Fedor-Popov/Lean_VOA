/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaKeyTop

/-!
# KeySkew: Li-type reduction of the self-coupling identity to top-level output data

`SigmaKey.KeySkew D t` (`SigmaKeyAdj.lean`) is the identity `Θ(Y^T(Ψx,z)x) = W(x,z)Ψx` for the
cyclic vector `x = h₀(−½)𝟙 ⊗ t_s`. It is one instance of the **block defect**

  `D_q(v,b) = Θ(v₍q₎ Φb) − W(Φv)₍q₎ b`,   `v, b ∈ V₃⁺`,   (`Dq`)

the difference of the two candidate `V₃⁺ × V₃⁺ → T_{s+1}⁺` blocks of `σ♮ Y♮(v) σ♮` and
`Y♮(Φv)`. This file proves, unconditionally given `D : SigmaData`:

1. `Dq_comm` — **the intertwining commutator formula** for the defect, in the input slot:
   `u₍ₘ₎ D_q(v,b) = D_q(v, u₍ₘ₎b) + ∑_r C(m,r) D_{m+q−r}((σu)₍ᵣ₎v, b)` for `u ∈ V₀⁺`.
   (From the twisted-module commutator `VnatBlock.act_comm`, `leechWsk_comm`, and the
   `σ`-twisted intertwining of `Φ`, `Θ`.)
2. `TPForm_W_top` — against a weight-2 vector only the `i = 0` term of `W` survives:
   `⟨y, W(t)₍q₎φ⟩ = (−1)^{q+1} ⟨y, φ₍q₎ t⟩`.
3. `Dq_eq_zero_of_pair` (Li's lemma, form version): if `⟨x', D_q(v,b)⟩ = 0` for the cyclic
   vector `x'` of `T_{s+1}⁺` and **all** `v, b, q`, then `D ≡ 0`.
4. `pair_of_b0` (input reduction): it suffices to know `⟨y, D_q(v, Ψx)⟩ = 0` for all
   `v ∈ V₃⁺`, `q`, and top-level `y ∈ (T_{s+1}⁺)₂` — i.e. the input may be fixed to the single
   cyclic vector `Ψx`, using single-mode cyclicity (`cyc_Psi`) and the lowest weights
   (`V₃⁺` and `TP` start in weight 2).
5. `keySkew_of_keyTopV : KeyTopV D t → KeySkew D t`, where `KeyTopV` is the
   **top-output identity** `Θ(o(v)x) = (−1)^k (Ψx)₍ₖ₋₁₎ Φ(v)` for homogeneous `v ∈ (V₃⁺)_k`
   (all `k`): every coefficient of `KeySkew` is controlled by the weight-2 output component
   of the block against the one input `Ψx`. And `moonshine_of_keyTopV`.

`KeyTopV` is **not finite**: `v` runs over all weights. At `k = 2` it is the top-level identity
`Θ o(v) x = o(Ψx) Φ(v)`, checked numerically on samples. Making it finite
needs Frenkel–Zhu bimodule theory for `V₃⁺` (`FZBimoduleKey.lean`).

## Status
`sorry`-free; conditional only on `D` and the displayed hypotheses. Imported by the
umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.KeySkew

open Module (End)
open VnatBlock SkewIntertwiner Reconstruction TrialityTw M8h0 IntegralLattice LatGen M8hKey
open LatticeTwisted TwistedHeisenberg FrameT InvForm SkewAdjoint VertexOperatorAlgebra SigmaExist
open SigmaKey

variable (D : SigmaData)

/-! ## §1  The block defect -/

/-- **The block defect** `D_q(v,b) = Θ(v₍q₎ Φb) − W(Φv)₍q₎ b` (mode form). -/
noncomputable def Dq (v b : VPlus) (q : ℤ) : TP :=
  D.Θ (mode (plusModule.YM v) q (D.Φ b)) - mode (leechWsk (D.Φ v)) q b

theorem Dq_mem {v b : VPlus} (hv : v ∈ frameSector 1) (hb : b ∈ frameSector 1) (q : ℤ) :
    Dq D v b q ∈ TPframe (D.s + 1) :=
  Submodule.sub_mem _ (D.Θ_mem _ (YM_mode_V3_flip hv (D.Φ_mem b hb) q))
    (leechWsk_mem_V3 (D.Φ_mem v hv) hb q)

theorem Dq_zero_right (v : VPlus) (q : ℤ) : Dq D v 0 q = 0 := by
  simp [Dq]

theorem Dq_add_right (v b b' : VPlus) (q : ℤ) :
    Dq D v (b + b') q = Dq D v b q + Dq D v b' q := by
  simp only [Dq, map_add]
  abel

theorem Dq_smul_right (v b : VPlus) (c : ℂ) (q : ℤ) :
    Dq D v (c • b) q = c • Dq D v b q := by
  simp only [Dq, map_smul, smul_sub]

/-! ## §2  The commutator formula for the defect -/

/-- **The intertwining commutator formula for the block defect** (input slot):
`u₍ₘ₎ D_q(v,b) = D_q(v, u₍ₘ₎b) + ∑_{r<J} C(m,r) D_{m+q−r}((σu)₍ᵣ₎v, b)`. -/
theorem Dq_comm {v b : VPlus} (hv : v ∈ frameSector 1) (hb : b ∈ frameSector 1)
    (u : V0Sub.carrier) (m q : ℤ) :
    ∃ J : ℕ, actT u m (Dq D v b q) = Dq D v (actV u m b) q
      + ∑ r ∈ Finset.range J, gBinom m r • Dq D (actV (sig u) r v) b (m + q - r) := by
  obtain ⟨N, hN⟩ := PreVertexAlgebra.smul_eventually_zero leechVOAPlus.toPreVertexAlgebra
    ((sig u : V0Sub.carrier) : VPlus) v
  refine ⟨N.toNat, ?_⟩
  have hJ : ∀ j : ℕ, N.toNat ≤ j → leechVOAPlus.smul ((sig u : V0Sub.carrier) : VPlus) j v = 0 :=
    fun j hj => hN j (by omega)
  -- `u₍ᵣ₎ Φv = Φ((σu)₍ᵣ₎ v)`
  have hΦr : ∀ r : ℤ, mode (plusModule.YM (u : VPlus)) r (D.Φ v) = D.Φ (actV (sig u) r v) := by
    intro r
    have e := D.isSigma_Φ (sig u) (Set.mem_univ _) r v hv
    rw [sig_sig] at e
    rw [e]; rfl
  have hJ' : ∀ j : ℕ, N.toNat ≤ j → mode (plusModule.YM (u : VPlus)) j (D.Φ v) = 0 := by
    intro j hj
    rw [hΦr, actV_apply, hJ j hj, map_zero]
  -- the `W` side
  have hW := leechWsk_comm (u : VPlus) m (D.Φ v) q b N.toNat hJ'
  -- the `Θ Y Φ` side
  have hy : mode (plusModule.YM v) q (D.Φ b) ∈ TPframe (D.s + 1) :=
    YM_mode_V3_flip hv (D.Φ_mem b hb) q
  have hΘ : actT u m (D.Θ (mode (plusModule.YM v) q (D.Φ b)))
      = D.Θ (actT (sig u) m (mode (plusModule.YM v) q (D.Φ b))) := by
    have e := D.isSigma_Θ (sig u) (Set.mem_univ _) m _ hy
    rw [sig_sig] at e
    exact e.symm
  have hC := act_comm plusModule.toWeakModule ((sig u : V0Sub.carrier) : VPlus) v m q (D.Φ b)
    N.toNat hJ
  have hΦb : actT (sig u) m (D.Φ b) = D.Φ (actV u m b) :=
    (D.isSigma_Φ u (Set.mem_univ _) m b hb).symm
  simp only [WeakModule.act_def] at hC
  have hC' : actT (sig u) m (mode (plusModule.YM v) q (D.Φ b))
      = mode (plusModule.YM v) q (D.Φ (actV u m b))
        + ∑ r ∈ Finset.range N.toNat, gBinom m r •
            mode (plusModule.YM (actV (sig u) r v)) (m + q - r) (D.Φ b) := by
    rw [← hΦb, actT_eq_mode, actT_eq_mode]
    simp only [actV_apply]
    rw [← hC]
    abel
  rw [Dq, map_sub, hΘ, hC', map_add, map_sum]
  rw [actT_eq_mode, actV_apply] at *
  rw [← sub_eq_zero] at hW ⊢
  simp only [Dq, map_smul]
  rw [show (mode (plusModule.YM (u : VPlus)) m) (mode (leechWsk (D.Φ v)) q b)
      = mode (leechWsk (D.Φ v)) q (leechVOAPlus.smul (u : VPlus) m b)
        + ∑ r ∈ Finset.range N.toNat,
            gBinom m r • mode (leechWsk (mode (plusModule.YM (u : VPlus)) r (D.Φ v))) (m + q - r) b
      by rw [← sub_eq_zero]; rw [sub_eq_zero] at hW; rw [← hW]; abel]
  simp only [hΦr, actV_apply, smul_sub, Finset.sum_sub_distrib]
  abel

/-! ## §3  Weight bookkeeping -/

/-- Against a weight-2 vector only the `i = 0` term of the skew field survives:
`⟨y, W(t)₍q₎φ⟩ = (−1)^{q+1} ⟨y, φ₍q₎ t⟩`. -/
theorem TPForm_W_top {y : TP} (hy : y ∈ plusModule.weight (2 : ℂ)) (t : TP) (q : ℤ) (φ : VPlus) :
    TPForm y (mode (leechWsk t) q φ) = negOnePow (q + 1) * TPForm y (mode (plusModule.YM φ) q t) := by
  obtain ⟨N, hN⟩ := plusModule.toWeakModule.truncation φ t
  set K := (N - q).toNat + 1 with hK
  have hb : ∀ l : ℕ, K ≤ l → mode (plusModule.YM φ) (q + l) t = 0 := fun l hl => hN _ (by omega)
  have hy' : y ∈ plusModule.weight ((2 : ℤ) : ℂ) := by exact_mod_cast hy
  rw [mode_leechWsk_eq_sum t q φ K hb, map_sum]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro l _ hl
    obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
    rw [map_smul, TPForm_Lm1_pow, pow_succ, Module.End.mul_apply, Lp1_weight_two hy']
    simp
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- `V₃⁺` has nothing below weight 2. -/
theorem V3_eq_zero_of_lt {x : VPlus} (hx1 : x ∈ frameSector 1) {m : ℤ}
    (hxm : x ∈ leechVOAPlus.grading m) (hlt : m < 2) : x = 0 := by
  rcases lt_trichotomy m 0 with h | h | h
  · rw [leechVOAPlus.positivity m h] at hxm; exact (Submodule.mem_bot ℂ).mp hxm
  · subst h
    rw [leechVOAPlus.vacuum_grade, Submodule.mem_span_singleton] at hxm
    obtain ⟨c, rfl⟩ := hxm
    have h0 : c • leechVOAPlus.vacuum ∈ frameSector 0 := by
      rw [← V0Sub_carrier]; exact V0Sub.carrier.smul_mem c V0Sub.vacuum_mem
    have hdisj := frameSector_isInternal.submodule_iSupIndep.pairwiseDisjoint
      (show (0 : ZMod 2) ≠ 1 by decide)
    exact (Submodule.disjoint_def.mp hdisj) _ h0 hx1
  · have h1 : m = 1 := by omega
    subst h1
    rw [leechVOAPlus_grading_one] at hxm
    exact (Submodule.mem_bot ℂ).mp hxm

/-- `TP` has nothing below weight 2 (complex-weight form). -/
theorem TP_eq_zero_of_lt {y : TP} {w : ℤ} (hy : y ∈ plusModule.weight (w : ℂ)) (hw : w < 2) :
    y = 0 := by
  rw [plusModule_weight_eq_bot_of_re_lt_two (by simp only [Complex.intCast_re]; exact_mod_cast hw)] at hy
  exact (Submodule.mem_bot ℂ).mp hy

/-! ## §4  Li's lemma: pairing against one cyclic output vector suffices -/

/-- **Li's lemma for the block defect.** If `⟨x', D_q(v,b)⟩ = 0` for one `V₀⁺`-cyclic vector
`x'` of `T_{s+1}⁺` and all `v, b ∈ V₃⁺`, `q`, then the defect vanishes identically. -/
theorem Dq_eq_zero_of_pair {x' : TP}
    (hcyc : Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actT u n x'}
      = TPframe (D.s + 1))
    (hpair : ∀ v ∈ frameSector 1, ∀ b ∈ frameSector 1, ∀ q : ℤ, TPForm x' (Dq D v b q) = 0)
    {v b : VPlus} (hv : v ∈ frameSector 1) (hb : b ∈ frameSector 1) (q : ℤ) : Dq D v b q = 0 := by
  -- every `y ∈ T_{s+1}⁺` pairs to zero with every defect
  have hR : ∀ y ∈ TPframe (D.s + 1),
      ∀ v ∈ frameSector 1, ∀ b ∈ frameSector 1, ∀ q : ℤ, TPForm y (Dq D v b q) = 0 := by
    intro y hy
    refine span_T_induction hcyc
      (fun y => ∀ v ∈ frameSector 1, ∀ b ∈ frameSector 1, ∀ q : ℤ, TPForm y (Dq D v b q) = 0)
      (fun v _ b _ q => by simp)
      (fun a a' h h' v hv b hb q => by
        rw [map_add, LinearMap.add_apply, h v hv b hb q, h' v hv b hb q, add_zero])
      (fun c a h v hv b hb q => by rw [map_smul, LinearMap.smul_apply, h v hv b hb q, smul_zero])
      (fun k u hu n v hv b hb q => ?_) hy
    rw [actT_eq_mode, TPForm_fhlInv hu n x' (Dq D v b q)]
    refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => smul_eq_zero_of_right _ ?_)
    rw [← V0P_coe_L_pow, ← actT_eq_mode]
    obtain ⟨J, hJ⟩ := Dq_comm D hv hb (((V0P.L 1) ^ j) u) (2 * k - n - 2 - (j : ℤ)) q
    rw [hJ, map_add, map_sum, hpair v hv _ (actV_stab _ (Set.mem_univ _) _ _ hb) q, zero_add]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [map_smul, hpair _ (actV_stab _ (Set.mem_univ _) _ _ hv) b hb _, smul_zero]
  apply SimpleNat.TPForm_eq_zero_of_forall
  intro y
  have hy : y ∈ TPframe D.s ⊔ TPframe (D.s + 1) := by
    rw [(TPframe_isCompl' D.s).sup_eq_top]; trivial
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hy
  have ha' : a ∈ TPframe (D.s + 1 + 1) := by rwa [zmod2_add_one_add_one]
  rw [map_add, TPForm_frame_orth' (Dq_mem D hv hb q) ha', TPForm_symm, hR c hc v hv b hb q, add_zero]

/-! ## §5  Input reduction to the single cyclic vector `Ψx` -/

/-- **Input reduction.** With `b₀ = Ψx` (weight 2, `V₀⁺`-cyclic in `V₃⁺`), top-level pairings
`⟨y, D_q(v, b₀)⟩ = 0` (`y ∈ (T_{s+1}⁺)₂`, all `v`, `q`) give the same for every input `b`. -/
theorem pair_of_b0 {b₀ : VPlus} (hb₀ : b₀ ∈ frameSector 1) (hb₀2 : b₀ ∈ leechVOAPlus.grading 2)
    (hcyc : Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actV u n b₀}
      = frameSector 1)
    (h0 : ∀ v ∈ frameSector 1, ∀ q : ℤ, ∀ y ∈ TPframe (D.s + 1), y ∈ plusModule.weight (2 : ℂ) →
      TPForm y (Dq D v b₀ q) = 0)
    {b : VPlus} (hb : b ∈ frameSector 1) :
    ∀ v ∈ frameSector 1, ∀ q : ℤ, ∀ y ∈ TPframe (D.s + 1), y ∈ plusModule.weight (2 : ℂ) →
      TPForm y (Dq D v b q) = 0 := by
  refine span_V3_induction hcyc
    (fun b => ∀ v ∈ frameSector 1, ∀ q : ℤ, ∀ y ∈ TPframe (D.s + 1), y ∈ plusModule.weight (2 : ℂ) →
      TPForm y (Dq D v b q) = 0)
    (fun v _ q y _ _ => by rw [Dq_zero_right, map_zero])
    (fun a a' h h' v hv q y hy hy2 => by
      rw [Dq_add_right, map_add, h v hv q y hy hy2, h' v hv q y hy hy2, add_zero])
    (fun c a h v hv q y hy hy2 => by rw [Dq_smul_right, map_smul, h v hv q y hy hy2, smul_zero])
    (fun k u hu n v hv q y hy hy2 => ?_) hb
  have hm := leechVOAPlus.smul_mem_grading hu hb₀2 n
  by_cases hkn : k + 2 - n - 1 < 2
  · rw [show actV u n b₀ = 0 from V3_eq_zero_of_lt (actV_stab _ (Set.mem_univ _) _ _ hb₀) hm hkn,
      Dq_zero_right, map_zero]
  push Not at hkn
  obtain ⟨J, hJ⟩ := Dq_comm D hv hb₀ u n q
  have e : Dq D v (actV u n b₀) q = actT u n (Dq D v b₀ q)
      - ∑ r ∈ Finset.range J, gBinom n r • Dq D (actV (sig u) r v) b₀ (n + q - r) := by
    rw [hJ]; abel
  rw [e, map_sub, map_sum]
  rw [Finset.sum_eq_zero fun r _ => by
    rw [map_smul, h0 _ (actV_stab _ (Set.mem_univ _) _ _ hv) _ y hy hy2, smul_zero], sub_zero]
  rw [TPForm_symm, actT_eq_mode, TPForm_fhlInv hu n (Dq D v b₀ q) y]
  refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => smul_eq_zero_of_right _ ?_)
  have hj := L_one_pow_mem V0P (k := k) (x := u) hu j
  have hjw := mode_mem_weight plusModule
    (show (((V0P.L 1) ^ j) u : VPlus) ∈ leechVOAPlus.grading (k - j) from hj) hy2
    (2 * k - n - 2 - (j : ℤ))
  rw [← V0P_coe_L_pow] at *
  have hw : ((2 : ℂ) + ((k - j : ℤ) : ℂ) - ((2 * k - n - 2 - (j : ℤ) : ℤ) : ℂ) - 1)
      = (((n - k + 3 : ℤ)) : ℂ) := by push_cast; ring
  rw [hw] at hjw
  by_cases heq : n - k + 3 = 2
  · rw [heq] at hjw
    rw [TPForm_symm]
    exact h0 v hv q _ (actT_stab _ _ (Set.mem_univ _) _ _ hy) (by exact_mod_cast hjw)
  · rw [TP_eq_zero_of_lt hjw (by omega), map_zero]

/-! ## §6  The top-output residual and the reduction of `KeySkew` -/

/-- **The top-output residual** (all weights, one input): for homogeneous `v ∈ (V₃⁺)_k`,
`Θ(o(v) x) = (−1)^k (Ψx)₍ₖ₋₁₎ Φ(v)` in `(T_{s+1}⁺)₂`, with `x = h₀(−½)𝟙 ⊗ t_s`. At `k = 2` this
is the top-level identity `Θ o(v) x = o(Ψx) Φ v` (checked numerically on samples). -/
def KeyTopV (t : ZMod 2 → TLeechT) : Prop :=
  ∀ (k : ℤ), ∀ v ∈ frameSector 1, v ∈ leechVOAPlus.grading k →
    D.Θ (mode (plusModule.YM v) (k - 1) (x0T (t D.s)))
      = negOnePow k • mode (plusModule.YM (D.Ψ (x0T (t D.s)))) (k - 1) (D.Φ v)

/-- The top-output residual specialised to the top level `k = 2` (the finite part). -/
def KeyTopTwo (t : ZMod 2 → TLeechT) : Prop :=
  ∀ v ∈ frameSector 1, v ∈ leechVOAPlus.grading 2 →
    D.Θ (mode (plusModule.YM v) 1 (x0T (t D.s)))
      = mode (plusModule.YM (D.Ψ (x0T (t D.s)))) 1 (D.Φ v)

theorem keyTopTwo_of_keyTopV {t : ZMod 2 → TLeechT} (h : KeyTopV D t) : KeyTopTwo D t := by
  intro v hv hv2
  have := h 2 v hv hv2
  rw [show (2 : ℤ) - 1 = 1 by norm_num] at this
  rw [this, show negOnePow 2 = 1 by simp [negOnePow], one_smul]

/-- `KeyTopV` gives the top-level pairings of the defect against `b₀ = Ψx`, for every `v`. -/
theorem pair_b0_of_keyTopV {t : ZMod 2 → TLeechT} (ht : ∀ s, t s ∈ leechFrameT s)
    (ht0 : ∀ s, t s ≠ 0) (hk : KeyTopV D t) :
    ∀ v ∈ frameSector 1, ∀ q : ℤ, ∀ y ∈ TPframe (D.s + 1), y ∈ plusModule.weight (2 : ℂ) →
      TPForm y (Dq D v (D.Ψ (x0T (t D.s))) q) = 0 := by
  set x := x0T (t D.s) with hxdef
  have hx : x ∈ TPframe D.s := x0T_mem (ht D.s)
  have hx2 : x ∈ plusModule.weight (2 : ℂ) := x0T_mem_weight (t D.s)
  have hx2' : x ∈ plusModule.weight ((2 : ℤ) : ℂ) := by exact_mod_cast hx2
  have hb₀2 := Psi_L0 D hx hx2'
  -- the form identity, linear in `v`
  have key : ∀ v ∈ frameSector 1, ∀ q : ℤ, ∀ y ∈ TPframe (D.s + 1), y ∈ plusModule.weight (2 : ℂ) →
      TPForm y (D.Θ (mode (plusModule.YM v) q x))
        = negOnePow (q + 1) * TPForm y (mode (plusModule.YM (D.Ψ x)) q (D.Φ v)) := by
    intro v hv
    refine span_V3_induction (cyc_Psi D hx (cyc_T (ht D.s) (ht0 D.s)))
      (fun v => ∀ q : ℤ, ∀ y ∈ TPframe (D.s + 1), y ∈ plusModule.weight (2 : ℂ) →
        TPForm y (D.Θ (mode (plusModule.YM v) q x))
          = negOnePow (q + 1) * TPForm y (mode (plusModule.YM (D.Ψ x)) q (D.Φ v)))
      (fun q y _ _ => by simp)
      (fun a a' h h' q y hy hy2 => by
        simp only [map_add, mode_add, LinearMap.add_apply, h q y hy hy2, h' q y hy hy2]; ring)
      (fun c a h q y hy hy2 => by
        simp only [map_smul, mode_smul, LinearMap.smul_apply, h q y hy hy2, smul_eq_mul]; ring)
      (fun k' u hu n q y hy hy2 => ?_) hv
    -- homogeneous generator `w = u₍ₙ₎ b₀` of weight `k = k' + 1 − n`
    set w := actV u n (D.Ψ x) with hwdef
    have hw1 : w ∈ frameSector 1 := actV_stab _ (Set.mem_univ _) _ _ (D.Ψ_mem x hx)
    have hwk : w ∈ leechVOAPlus.grading (k' + 2 - n - 1) := leechVOAPlus.smul_mem_grading hu hb₀2 n
    set k := k' + 2 - n - 1 with hkdef
    by_cases hq : q = k - 1
    · subst hq
      rw [hk k w hw1 hwk, map_smul, smul_eq_mul, sub_add_cancel]
    · have hL : D.Θ (mode (plusModule.YM w) q x) ∈ plusModule.weight (((2 + k - q - 1 : ℤ)) : ℂ) := by
        have := mode_mem_weight plusModule hwk hx2 q
        have e : (2 : ℂ) + (k : ℂ) - (q : ℂ) - 1 = (((2 + k - q - 1 : ℤ)) : ℂ) := by push_cast; ring
        rw [e] at this
        exact Theta_weight D (YM_mode_V3_flip hw1 hx q) this
      have hR : mode (plusModule.YM (D.Ψ x)) q (D.Φ w) ∈ plusModule.weight (((2 + k - q - 1 : ℤ)) : ℂ) := by
        have := mode_mem_weight plusModule hb₀2 (Phi_weight D hw1 hwk) q
        have e : (k : ℂ) + ((2 : ℤ) : ℂ) - (q : ℂ) - 1 = (((2 + k - q - 1 : ℤ)) : ℂ) := by push_cast; ring
        rw [e] at this
        exact this
      have hne : (2 : ℂ) ≠ (((2 + k - q - 1 : ℤ)) : ℂ) := by
        intro h
        have : (2 : ℤ) = 2 + k - q - 1 := by exact_mod_cast h
        omega
      rw [TPForm_weightOrth _ _ hne y hy2 _ hL, TPForm_weightOrth _ _ hne y hy2 _ hR, mul_zero]
  intro v hv q y hy hy2
  rw [Dq, D.ΦΨ x hx, map_sub, TPForm_W_top hy2, key v hv q y hy hy2, sub_self]

/-- **`KeySkew` from the top-output residual.** -/
theorem keySkew_of_keyTopV {t : ZMod 2 → TLeechT} (ht : ∀ s, t s ∈ leechFrameT s)
    (ht0 : ∀ s, t s ≠ 0) (hk : KeyTopV D t) : KeySkew D t := by
  set x := x0T (t D.s) with hxdef
  have hx : x ∈ TPframe D.s := x0T_mem (ht D.s)
  have hx2' : x ∈ plusModule.weight ((2 : ℤ) : ℂ) := by
    have := x0T_mem_weight (t D.s); exact_mod_cast this
  have hb₀ : D.Ψ x ∈ frameSector 1 := D.Ψ_mem x hx
  have hb₀2 := Psi_L0 D hx hx2'
  have hpair0 := pair_b0_of_keyTopV D ht ht0 hk
  have hall : ∀ b ∈ frameSector 1, ∀ v ∈ frameSector 1, ∀ q : ℤ, ∀ y ∈ TPframe (D.s + 1),
      y ∈ plusModule.weight (2 : ℂ) → TPForm y (Dq D v b q) = 0 :=
    fun b hb => pair_of_b0 D hb₀ hb₀2 (cyc_Psi D hx (cyc_T (ht D.s) (ht0 D.s))) hpair0 hb
  have hx' : x0T (t (D.s + 1)) ∈ TPframe (D.s + 1) := x0T_mem (ht (D.s + 1))
  have hzero : ∀ q : ℤ, Dq D (D.Ψ x) (D.Ψ x) q = 0 := fun q =>
    Dq_eq_zero_of_pair D (cyc_T (ht (D.s + 1)) (ht0 (D.s + 1)))
      (fun v hv b hb q => hall b hb v hv q _ hx' (x0T_mem_weight _)) hb₀ hb₀ q
  intro p
  have h := hzero (-p - 1)
  rw [Dq, D.ΦΨ x hx, sub_eq_zero, mode_apply, mode_apply, show -(-p - 1) - 1 = p by ring] at h
  exact h

/-- **The Moonshine module** from `D`, the two finite isometry statements and the
top-output residual `KeyTopV`. -/
theorem moonshine_of_keyTopV {β : leech.carrier} (hβ : β ∉ lambda0) {t : ZMod 2 → TLeechT}
    (ht : ∀ s, t s ∈ leechFrameT s) (ht0 : ∀ s, t s ≠ 0)
    (hΦ : PhiTop D t) (hΘ : ThetaTop D t) (hk : KeyTopV D t) :
    ∃ V : VertexOperatorAlgebra Vnat,
      V.Y = Ynat VnatAxioms.wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
      V.centralCharge = 24 ∧
      V.grading 1 = ⊥ ∧
      Module.finrank ℂ (V.grading 2) = 196884 ∧
      (∀ n : ℕ, (Module.finrank ℂ (V.grading (n : ℤ)) : ℂ) = PowerSeries.coeff n JShift) ∧
      V.IsSimple :=
  moonshine_of_top D hβ ht ht0 hΦ hΘ (keySkew_of_keyTopV D ht ht0 hk)

end VOA.Moonshine.KeySkew
