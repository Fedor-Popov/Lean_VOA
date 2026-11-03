/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionUnivGGrade
import VOA.DeligneAudit.DeligneFusionGarlandSl3

/-!
# Ravinder's family and kernel lemma for a sector (generic part)

For sector data `S`:

* `ravSpec S k d`: the relations of `M_{a,b}` with `k = a + b`, `d = 2a + b`: the local Weyl
  relations for `kθ`, the truncations `(f_x ⊗ t^k) w = 0` for fusion `x ≠ θ`, and
  `(f_θ ⊗ t^d) w = 0`.
  `ravFam S a b := ravSpec S (a+b) (2a+b)`, `ravKw S a b := [(c₀, 2a+b+1)]`; `ravFam_zero`
  (`= lwSpec`), `ravFam_step` (`SpecStep`), `ravKw_deg`.
* `KernelTable S`: finitely many structure-constant facts (decidable per type).
* Named input `ThetaNilG S`: in any module, a vector of weight `kθ` killed by `n⁺` with
  `f_i^{kθ(h_i)+1} w = 0` satisfies `f_θ^{2k+1} w = 0`. This is the classical integrability of
  `V(kθ)` (Humphreys §21, Kac Lemma 3.4). For `sl₃` it is derived from a Heisenberg pair of simple
  roots; for `D₄` it is proved by a Heisenberg chain plus `sl₂` sharpening (`D4FusionKernelTheta`).
  It is proved for every non-`A₂` sector: `g2_thetaNil`, `d4_thetaNil`, `f4_thetaNil`,
  `e6_thetaNil`, `e7_thetaNil`, `e8_thetaNil` (the `*FusionKernelTheta.lean`/`F4LieKernel.lean`
  files).
* `kernel_sat`: from `KernelTable` and `ThetaNilG`, the kernel vector `(f_θ ⊗ t^{d+1}) w` of a
  module with `ravSpec S (K+1) (D+2)` satisfies `ravSpec S K D`. This is the sl₃ argument made
  generic: the raising and Cartan relations by commutation, the lowering relations by sl₂ algebra,
  the truncations by the `θ`-Garland identity (`garland_two`).
* `ravinderKernelRelG_of_table`.
-/

namespace VOA.DeligneAudit.UnivG

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector

noncomputable section

local notation "deg" => VOA.DeligneAudit.SectorGraded.wordDeg

variable (S : DeligneSectorData)

/-- **Ravinder's relations** for `M_{a,b}`, `k = a + b`, `d = 2a + b`. -/
def ravSpec (k d : ℕ) : RelSpec S.n where
  tails := {t | (∃ e r, S.raising e ∧ t = [(e, r)]) ∨ (∃ h r, S.cartan h ∧ 1 ≤ r ∧ t = [(h, r)]) ∨
    (∃ i, S.lowering i ∧ t = List.replicate (k * S.lowExp i + 1) (i, 0)) ∨
    (∃ x, S.fusion x ∧ t = [(x, if x = S.c₀ then d else k)]) ∨
    (∃ h r, S.cartanN h ∧ 1 ≤ r ∧ t = [(h, r)])}
  eig := {q | (∃ h, S.cartan h ∧ q = (h, ((k * S.thetaH h : ℕ) : ℂ))) ∨
    (∃ h, S.cartanN h ∧ q = (h, -((k * S.thetaN h : ℕ) : ℂ)))}

theorem ravSpec_self (m : ℕ) : ravSpec S m m = lwSpec S m := by
  simp only [ravSpec, lwSpec, ite_self]

/-- The family `M_{a,b}`. -/
def ravFam (a b : ℕ) : RelSpec S.n := ravSpec S (a + b) (2 * a + b)

/-- The kernel words `f_θ ⊗ t^{2a+b+1}`. -/
def ravKw (a b : ℕ) : List (Ltr S.n) := [(S.c₀, 2 * a + b + 1)]

theorem ravFam_zero (m : ℕ) : ravFam S 0 m = lwSpec S m := by
  change ravSpec S (0 + m) (2 * 0 + m) = _
  simp only [Nat.mul_zero, Nat.zero_add]
  exact ravSpec_self S m

theorem ravSpec_step (k d d' : ℕ) : SpecStep (ravSpec S k d) (ravSpec S k d') [(S.c₀, d')] where
  tail t ht := by
    simp only [ravSpec, Set.mem_setOf_eq] at ht ⊢
    rcases ht with h | h | h | ⟨x, hx, rfl⟩ | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · by_cases hx0 : x = S.c₀
      · subst hx0; exact Or.inr ⟨[], by simp⟩
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, hx, by simp [hx0]⟩))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
  eig := fun _ hq => hq

theorem ravFam_step (a b : ℕ) :
    SpecStep (ravFam S (a + 1) b) (ravFam S a (b + 1)) (ravKw S a b) := by
  have := ravSpec_step S (a + 1 + b) (2 * (a + 1) + b) (2 * a + b + 1)
  rw [ravFam, ravFam, ravKw, show a + (b + 1) = a + 1 + b by omega,
    show 2 * a + (b + 1) = 2 * a + b + 1 by omega]
  exact this

theorem ravKw_deg (a b : ℕ) : deg (ravKw S a b) = 2 * a + b + 1 := by
  simp [ravKw, VOA.DeligneAudit.SectorGraded.wordDeg]

/-! ## Reading the relations -/

section Read

variable {S} {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule S.f V} {w : V} {k d : ℕ}

theorem rs_raising (h : Sat S.f ρ w (ravSpec S k d)) {e : Fin S.n} (he : S.raising e) (r : ℕ) :
    ρ.op e r w = 0 :=
  h.tail [(e, r)] (Or.inl ⟨e, r, he, rfl⟩)

theorem rs_cartan_pos (h : Sat S.f ρ w (ravSpec S k d)) {c : Fin S.n} (hc : S.cartan c) (r : ℕ)
    (hr : 1 ≤ r) : ρ.op c r w = 0 :=
  h.tail [(c, r)] (Or.inr (Or.inl ⟨c, r, hc, hr, rfl⟩))

theorem rs_cartan_zero (h : Sat S.f ρ w (ravSpec S k d)) {c : Fin S.n} (hc : S.cartan c) :
    ρ.op c 0 w = ((k * S.thetaH c : ℕ) : ℂ) • w :=
  h.eig (c, _) (Or.inl ⟨c, hc, rfl⟩)

theorem rs_cartanN_pos (h : Sat S.f ρ w (ravSpec S k d)) {c : Fin S.n} (hc : S.cartanN c) (r : ℕ)
    (hr : 1 ≤ r) : ρ.op c r w = 0 :=
  h.tail [(c, r)] (Or.inr (Or.inr (Or.inr (Or.inr ⟨c, r, hc, hr, rfl⟩))))

theorem rs_cartanN_zero (h : Sat S.f ρ w (ravSpec S k d)) {c : Fin S.n} (hc : S.cartanN c) :
    ρ.op c 0 w = (-((k * S.thetaN c : ℕ) : ℂ)) • w :=
  h.eig (c, _) (Or.inr ⟨c, hc, rfl⟩)

theorem rs_lowering (h : Sat S.f ρ w (ravSpec S k d)) {i : Fin S.n} (hi : S.lowering i) :
    (ρ.op i 0)^[k * S.lowExp i + 1] w = 0 := by
  rw [iterate_eq_wordOpG]
  exact h.tail _ (Or.inr (Or.inr (Or.inl ⟨i, hi, rfl⟩)))

theorem rs_fusion (h : Sat S.f ρ w (ravSpec S k d)) {x : Fin S.n} (hx : S.fusion x) :
    ρ.op x (if x = S.c₀ then d else k) w = 0 :=
  h.tail [(x, _)] (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, hx, rfl⟩))))

end Read

/-! ## Structure-constant data -/

/-- **Table facts** for the kernel lemma (decidable per type). `τ h` is the signed value `θ(h)` on
the Cartan basis (`θH` on `cartan`, `-θN` on `cartanN`). -/
structure KernelTable where
  τ : Fin S.n → ℂ
  tauH : ∀ h, S.cartan h → τ h = (S.thetaH h : ℂ)
  tauN : ∀ h, S.cartanN h → τ h = -(S.thetaN h : ℂ)
  c0_fusion : S.fusion S.c₀
  truncUp : ∀ x, S.fusion x ∨ S.lowering x →
    ∃ h, (S.cartan h ∨ S.cartanN h) ∧ S.f h x x ≠ 0 ∧ ∀ c, c ≠ x → S.f h x c = 0
  raisTheta : ∀ e, S.raising e → ∀ c, S.f e S.c₀ c ≠ 0 →
    (S.cartan c ∨ S.cartanN c) ∨ (S.fusion c ∧ c ≠ S.c₀)
  cartTau : ∀ h, S.cartan h ∨ S.cartanN h → ∀ c, S.f h S.c₀ c = if c = S.c₀ then -τ h else 0
  lowComm : ∀ x, S.fusion x ∨ S.lowering x → ∀ c, S.f x S.c₀ c = 0
  lowExp_le : ∀ i, S.lowering i → S.lowExp i ≤ 1
  simple : ∀ i, S.lowering i → S.lowExp i = 1 → ∃ (e : Fin S.n) (s : ℂ), S.raising e ∧
    (∀ c, S.f e i c ≠ 0 → S.cartan c ∨ S.cartanN c) ∧ ∑ c, s * S.f e i c * τ c = 1 ∧
    ∀ d, ∑ c, s * S.f e i c * S.f c i d = if d = i then -2 else 0
  eθ : Fin S.n
  sθ : ℂ
  eθ_raising : S.raising eθ
  eθ_cartan : ∀ c, S.f eθ S.c₀ c ≠ 0 → S.cartan c ∨ S.cartanN c
  eθ_theta : sθ * ∑ c, S.f eθ S.c₀ c * τ c = 2
  /-- Root vectors killing the generator at grade `0` (orthogonal to `θ`), generated by brackets
  from the simple ones with `θ(h_i) = 0`; `rk` makes the generation well founded. -/
  kill0 : Fin S.n → Prop
  rk : Fin S.n → ℕ
  kill0_low : ∀ x, kill0 x → S.fusion x ∨ S.lowering x
  kill0_gen : ∀ x, kill0 x → (S.lowering x ∧ S.lowExp x = 0) ∨
    ∃ (a b : Fin S.n) (κ : ℂ), κ ≠ 0 ∧ kill0 a ∧ kill0 b ∧ rk a < rk x ∧ rk b < rk x ∧
      ∀ c, S.f a b c = if c = x then κ else 0
  fusionRoot : ∀ x, S.fusion x → x ≠ S.c₀ →
    (∃ β κ, S.raising β ∧ κ ≠ 0 ∧ ∀ c, S.f β S.c₀ c = if c = x then κ else 0) ∨ kill0 x

/-- **Table facts for a simply-laced sector** (the simply-laced interface: no `cartanN`, a single
Cartan basis element for each simple `sl₂` with `θ(h) = 1`). `KernelTable.ofSL` converts it. -/
structure KernelTableSL where
  noN : ∀ h, ¬ S.cartanN h
  c0_fusion : S.fusion S.c₀
  truncUp : ∀ x, S.fusion x ∨ S.lowering x →
    ∃ h, S.cartan h ∧ S.f h x x ≠ 0 ∧ ∀ c, c ≠ x → S.f h x c = 0
  raisTheta : ∀ e, S.raising e → ∀ c, S.f e S.c₀ c ≠ 0 → S.cartan c ∨ (S.fusion c ∧ c ≠ S.c₀)
  cartTheta : ∀ h, S.cartan h → ∀ c, S.f h S.c₀ c = if c = S.c₀ then -(S.thetaH h : ℂ) else 0
  lowComm : ∀ x, S.fusion x ∨ S.lowering x → ∀ c, S.f x S.c₀ c = 0
  lowExp_le : ∀ i, S.lowering i → S.lowExp i ≤ 1
  simple : ∀ i, S.lowering i → S.lowExp i = 1 → ∃ e hi, S.raising e ∧ S.cartan hi ∧
    (∀ c, S.f e i c = if c = hi then 1 else 0) ∧ S.thetaH hi = 1 ∧
    (∀ c, S.f hi i c = if c = i then -2 else 0)
  eθ : Fin S.n
  sθ : ℂ
  eθ_raising : S.raising eθ
  eθ_cartan : ∀ c, S.f eθ S.c₀ c ≠ 0 → S.cartan c
  eθ_theta : sθ * ∑ c, S.f eθ S.c₀ c * (S.thetaH c : ℂ) = 2
  fusionRoot : ∀ x, S.fusion x → x ≠ S.c₀ →
    (∃ β κ, S.raising β ∧ κ ≠ 0 ∧ ∀ c, S.f β S.c₀ c = if c = x then κ else 0) ∨
      (S.lowering x ∧ S.lowExp x = 0)

variable {S} in
/-- The general table from a simply-laced one (`τ = θ`). -/
def KernelTable.ofSL (T : KernelTableSL S) : KernelTable S where
  τ c := (S.thetaH c : ℂ)
  tauH _ _ := rfl
  tauN h hh := (T.noN h hh).elim
  c0_fusion := T.c0_fusion
  truncUp x hx := by
    obtain ⟨h, h1, h2, h3⟩ := T.truncUp x hx
    exact ⟨h, Or.inl h1, h2, h3⟩
  raisTheta e he c hc := (T.raisTheta e he c hc).imp_left Or.inl
  cartTau h hh c := hh.elim (fun hh => T.cartTheta h hh c) (fun hh => (T.noN h hh).elim)
  lowComm := T.lowComm
  lowExp_le := T.lowExp_le
  simple i hi h1 := by
    obtain ⟨e, hi', he, hhc, hei, hth, hhf⟩ := T.simple i hi h1
    refine ⟨e, 1, he, fun c hc => Or.inl ?_, ?_, fun d => ?_⟩
    · by_cases hci : c = hi'
      · rw [hci]; exact hhc
      · rw [hei c, if_neg hci] at hc; exact absurd rfl hc
    · rw [Finset.sum_eq_single hi' (fun c _ hc => by rw [hei c, if_neg hc, mul_zero, zero_mul])
        (by simp), hei, if_pos rfl, hth]; simp
    · rw [Finset.sum_eq_single hi' (fun c _ hc => by rw [hei c, if_neg hc, mul_zero, zero_mul])
        (by simp), hei, if_pos rfl, mul_one, one_mul, hhf d]
  eθ := T.eθ
  sθ := T.sθ
  eθ_raising := T.eθ_raising
  eθ_cartan c hc := Or.inl (T.eθ_cartan c hc)
  eθ_theta := T.eθ_theta
  kill0 x := S.lowering x ∧ S.lowExp x = 0
  rk _ := 0
  kill0_low _ h := Or.inr h.1
  kill0_gen _ h := Or.inl h
  fusionRoot := T.fusionRoot

/-- **Named input (integrability of `V(kθ)`)**: `f_θ^{2k+1} w = 0` for a highest-weight vector of
weight `kθ` with the simple lowering relations.  Proved per sector: `g2_thetaNil`, `d4_thetaNil`,
`f4_thetaNil`, `e6_thetaNil`, `e7_thetaNil`, `e8_thetaNil`. -/
def ThetaNilG : Prop :=
  ∀ (k : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
    (∀ e, S.raising e → ρ.op e 0 w = 0) →
    (∀ h, S.cartan h → ρ.op h 0 w = ((k * S.thetaH h : ℕ) : ℂ) • w) →
    (∀ h, S.cartanN h → ρ.op h 0 w = (-((k * S.thetaN h : ℕ) : ℂ)) • w) →
    (∀ i, S.lowering i → (ρ.op i 0)^[k * S.lowExp i + 1] w = 0) →
    ((ρ.op S.c₀ 0) ^ (2 * k + 1)) w = 0

/-! ## The kernel lemma -/

section Kernel

variable {S} (T : KernelTable S) {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule S.f V}

theorem commG (a b : Fin S.n) (r s : ℕ) (x : V) :
    ρ.op a r (ρ.op b s x) = ρ.op b s (ρ.op a r x) + ∑ e, S.f a b e • ρ.op e (r + s) x := by
  rw [← ρ.comm a b r s x]; abel

theorem op_comm_endG (a b : Fin S.n) (r s : ℕ) :
    ρ.op a r * ρ.op b s - ρ.op b s * ρ.op a r = ∑ e, S.f a b e • ρ.op e (r + s) := by
  ext x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  exact ρ.comm a b r s x

include T in
theorem trunc_upG {w : V} {x : Fin S.n} (hx : S.fusion x ∨ S.lowering x) {N0 : ℕ}
    (h0 : ρ.op x N0 w = 0) (hc : ∀ h, S.cartan h ∨ S.cartanN h → ∀ r, 1 ≤ r → ρ.op h r w = 0) :
    ∀ N, N0 ≤ N → ρ.op x N w = 0 := by
  intro N hN
  obtain ⟨j, rfl⟩ : ∃ j, N = N0 + j := ⟨N - N0, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simpa using h0
  obtain ⟨h, hh, hne, hz⟩ := T.truncUp x hx
  have hcomm := ρ.comm h x j N0 w
  rw [h0, map_zero, hc h hh j hj, map_zero, sub_zero,
    Finset.sum_eq_single x (fun e _ he => by rw [hz e he, zero_smul]) (by simp), add_comm j N0]
    at hcomm
  exact (smul_eq_zero.mp hcomm.symm).resolve_left hne

include T in
theorem comm_c0 {x : Fin S.n} (hx : S.fusion x ∨ S.lowering x) (r s : ℕ) (v : V) :
    ρ.op x r (ρ.op S.c₀ s v) = ρ.op S.c₀ s (ρ.op x r v) := by
  rw [commG]; simp [T.lowComm x hx]

include T in
theorem iterate_comm_c0 {x : Fin S.n} (hx : S.fusion x ∨ S.lowering x) (s : ℕ) :
    ∀ (n : ℕ) (v : V), (ρ.op x 0)^[n] (ρ.op S.c₀ s v) = ρ.op S.c₀ s ((ρ.op x 0)^[n] v)
  | 0, _ => rfl
  | n + 1, v => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_comm_c0 hx s n v,
        comm_c0 T hx]

theorem two_eq_zeroG {x : V} (hx : x + x = 0) : x = 0 := by
  rw [← two_smul ℂ, smul_eq_zero] at hx
  exact hx.resolve_left two_ne_zero

variable {w : V} {K D : ℕ}

include T in
/-- The `θ`-Garland identity for a module with `ravSpec S (K+1) (D+2)`. -/
theorem theta_garlandG (hN : ThetaNilG S) (h : Sat S.f ρ w (ravSpec S (K + 1) (D + 2))) (s : ℕ)
    (hs : 2 * (K + 1) + 1 ≤ s + 2) :
    ∑ x ∈ Finset.antidiagonal s, ρ.op S.c₀ x.1 (ρ.op S.c₀ x.2 w) = 0 := by
  have hFF : ∀ j k, ρ.op S.c₀ j * ρ.op S.c₀ k = ρ.op S.c₀ k * ρ.op S.c₀ j := by
    intro j k
    rw [← sub_eq_zero, op_comm_endG]
    simp [T.lowComm S.c₀ (Or.inl T.c0_fusion)]
  refine Garland.garland_two (E1 := T.sθ • ρ.op T.eθ 1)
    (H := fun m => T.sθ • ∑ c, S.f T.eθ S.c₀ c • ρ.op c m) (F := fun s => ρ.op S.c₀ s)
    ?_ ?_ hFF ?_ ?_ (hN (K + 1) V ρ w (fun e he => rs_raising h he 0)
      (fun c hc => rs_cartan_zero h hc) (fun c hc => rs_cartanN_zero h hc)
      (fun i hi => rs_lowering h hi)) s hs
  · intro k
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, op_comm_endG, add_comm 1 k]
  · intro m k
    have hterm : ∀ c, S.f T.eθ S.c₀ c •
        (ρ.op c (m + 1) * ρ.op S.c₀ k - ρ.op S.c₀ k * ρ.op c (m + 1))
        = (S.f T.eθ S.c₀ c * -T.τ c) • ρ.op S.c₀ (m + 1 + k) := by
      intro c
      by_cases hf : S.f T.eθ S.c₀ c = 0
      · simp [hf]
      have hc := T.eθ_cartan c hf
      rw [op_comm_endG, Finset.sum_eq_single S.c₀
        (fun d _ hd => by rw [T.cartTau c hc d, if_neg hd, zero_smul]) (by simp),
        T.cartTau c hc, if_pos rfl, smul_smul]
    have hexp : (T.sθ • ∑ c, S.f T.eθ S.c₀ c • ρ.op c (m + 1)) * ρ.op S.c₀ k -
        ρ.op S.c₀ k * (T.sθ • ∑ c, S.f T.eθ S.c₀ c • ρ.op c (m + 1)) =
        T.sθ • ∑ c, S.f T.eθ S.c₀ c •
          (ρ.op c (m + 1) * ρ.op S.c₀ k - ρ.op S.c₀ k * ρ.op c (m + 1)) := by
      rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, Finset.sum_mul, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [smul_mul_assoc, mul_smul_comm, smul_sub]
    rw [hexp, Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_smul, smul_smul]
    congr 1
    have := T.eθ_theta
    simp only [mul_neg, Finset.sum_neg_distrib, mul_neg]
    linear_combination -this
  · change T.sθ • ρ.op T.eθ 1 w = 0
    rw [rs_raising h T.eθ_raising 1, smul_zero]
  · intro m
    change (T.sθ • ∑ c, S.f T.eθ S.c₀ c • ρ.op c (m + 1)) w = 0
    rw [LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]
    rw [Finset.sum_eq_zero, smul_zero]
    intro c _
    by_cases hf : S.f T.eθ S.c₀ c = 0
    · simp [hf]
    · rcases T.eθ_cartan c hf with hc | hc
      · rw [LinearMap.smul_apply, rs_cartan_pos h hc (m + 1) (by omega), smul_zero]
      · rw [LinearMap.smul_apply, rs_cartanN_pos h hc (m + 1) (by omega), smul_zero]

include T in
/-- **The kernel lemma**: `v = (f_θ ⊗ t^{D+1}) w` satisfies `ravSpec S K D`. -/
theorem kernel_sat (hN : ThetaNilG S) (hKD : K ≤ D) (h : Sat S.f ρ w (ravSpec S (K + 1) (D + 2))) :
    Sat S.f ρ (ρ.op S.c₀ (D + 1) w) (ravSpec S K D) := by
  have hC : ∀ c, S.cartan c ∨ S.cartanN c → ∀ r, 1 ≤ r → ρ.op c r w = 0 := by
    rintro c (hc | hc) r hr
    · exact rs_cartan_pos h hc r hr
    · exact rs_cartanN_pos h hc r hr
  have hCw : ∀ c, S.cartan c ∨ S.cartanN c → ρ.op c 0 w = (((K + 1 : ℕ) : ℂ) * T.τ c) • w := by
    rintro c (hc | hc)
    · rw [rs_cartan_zero h hc, T.tauH c hc]; push_cast; ring_nf
    · rw [rs_cartanN_zero h hc, T.tauN c hc]; push_cast; ring_nf
  have hFx : ∀ x, S.fusion x → x ≠ S.c₀ → ∀ N, K + 1 ≤ N → ρ.op x N w = 0 := by
    intro x hx hx0
    have := rs_fusion h hx
    rw [if_neg hx0] at this
    exact trunc_upG T (Or.inl hx) this hC
  have hFθ : ∀ N, D + 2 ≤ N → ρ.op S.c₀ N w = 0 := by
    have := rs_fusion h T.c0_fusion
    rw [if_pos rfl] at this
    exact trunc_upG T (Or.inl T.c0_fusion) this hC
  have hL0 : ∀ x, S.lowering x → S.lowExp x = 0 → ∀ N, ρ.op x N w = 0 := by
    intro x hx hx0
    have := rs_lowering h hx
    rw [hx0, mul_zero, zero_add, Function.iterate_one] at this
    exact fun N => trunc_upG T (Or.inr hx) this hC N (Nat.zero_le _)
  have hK00 : ∀ m x, T.rk x ≤ m → T.kill0 x → ρ.op x 0 w = 0 := by
    intro m
    induction m with
    | zero =>
      intro x hx hk
      rcases T.kill0_gen x hk with ⟨hl, h0⟩ | ⟨a, b, κ, _, _, _, ha, _⟩
      · exact hL0 x hl h0 0
      · omega
    | succ m ih =>
      intro x hx hk
      rcases T.kill0_gen x hk with ⟨hl, h0⟩ | ⟨a, b, κ, hκ, hka, hkb, ha, hb, hab⟩
      · exact hL0 x hl h0 0
      · have hc := ρ.comm a b 0 0 w
        rw [ih b (by omega) hkb, map_zero, ih a (by omega) hka, map_zero, sub_zero,
          Finset.sum_eq_single x (fun c _ hc => by rw [hab c, if_neg hc, zero_smul]) (by simp),
          hab x, if_pos rfl, zero_add] at hc
        exact (smul_eq_zero.mp hc.symm).resolve_left hκ
  have hK0 : ∀ x, T.kill0 x → ∀ N, ρ.op x N w = 0 := fun x hk N =>
    trunc_upG T (T.kill0_low x hk) (hK00 _ x le_rfl hk) hC N (Nat.zero_le _)
  -- raising
  have hR : ∀ e, S.raising e → ∀ r, ρ.op e r (ρ.op S.c₀ (D + 1) w) = 0 := by
    intro e he r
    rw [commG, rs_raising h he r, map_zero, zero_add]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hf : S.f e S.c₀ c = 0
    · rw [hf, zero_smul]
    rcases T.raisTheta e he c hf with hc | ⟨hc, hne⟩
    · rw [hC c hc _ (by omega), smul_zero]
    · rw [hFx c hc hne _ (by omega), smul_zero]
  -- Cartan
  have hCp : ∀ c, S.cartan c ∨ S.cartanN c → ∀ r, 1 ≤ r →
      ρ.op c r (ρ.op S.c₀ (D + 1) w) = 0 := by
    intro c hc r hr
    rw [commG, hC c hc r hr, map_zero, zero_add]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [T.cartTau c hc e]
    split_ifs with he
    · subst he; rw [hFθ _ (by omega), smul_zero]
    · rw [zero_smul]
  have hCv : ∀ c, S.cartan c ∨ S.cartanN c →
      ρ.op c 0 (ρ.op S.c₀ (D + 1) w) = ((K : ℂ) * T.τ c) • ρ.op S.c₀ (D + 1) w := by
    intro c hc
    rw [commG, hCw c hc, map_smul, Finset.sum_eq_single S.c₀
      (fun e _ he => by rw [T.cartTau c hc e, if_neg he, zero_smul]) (by simp),
      T.cartTau c hc, if_pos rfl, zero_add, ← add_smul]
    congr 1
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · simp only [ravSpec, Set.mem_setOf_eq]
    rintro t (⟨e, r, he, rfl⟩ | ⟨c, r, hc, hr, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨x, hx, rfl⟩ |
      ⟨c, r, hc, hr, rfl⟩)
    · exact hR e he r
    · exact hCp c (Or.inl hc) r hr
    · -- lowering
      rw [← iterate_eq_wordOpG]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (T.lowExp_le i hi) with h0 | h1
      · rw [h0, mul_zero, zero_add, Function.iterate_one, comm_c0 T (Or.inr hi), hL0 i hi h0,
          map_zero]
      · obtain ⟨e, sE, he, hec, hsum1, hsum2⟩ := T.simple i hi h1
        rw [h1, mul_one]
        set v := ρ.op S.c₀ (D + 1) w with hv
        set H : V →ₗ[ℂ] V := ∑ c, (sE * S.f e i c) • ρ.op c 0 with hHdef
        have hHy : ∀ y, H y = ∑ c, (sE * S.f e i c) • ρ.op c 0 y := by
          intro y; simp [hHdef]
        have hin : ∀ c y, ρ.op c 0 (ρ.op i 0 y) - ρ.op i 0 (ρ.op c 0 y) =
            ∑ d, S.f c i d • ρ.op d 0 y := fun c y => by simpa using ρ.comm c i 0 0 y
        have hEF : ∀ y, (sE • ρ.op e 0) (ρ.op i 0 y) - ρ.op i 0 ((sE • ρ.op e 0) y) = H y := by
          intro y
          have := ρ.comm e i 0 0 y
          simp only [add_zero] at this
          rw [hHy, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, ← smul_sub, this,
            Finset.smul_sum]
          simp only [smul_smul]
        have hHF : ∀ y, H (ρ.op i 0 y) - ρ.op i 0 (H y) = (-2 : ℂ) • ρ.op i 0 y := by
          intro y
          calc H (ρ.op i 0 y) - ρ.op i 0 (H y)
              = ∑ c, (sE * S.f e i c) • (ρ.op c 0 (ρ.op i 0 y) - ρ.op i 0 (ρ.op c 0 y)) := by
                rw [hHy, hHy, map_sum, ← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun c _ => ?_
                rw [map_smul, smul_sub]
            _ = ∑ d, (∑ c, sE * S.f e i c * S.f c i d) • ρ.op d 0 y := by
                simp only [hin, Finset.smul_sum, smul_smul]
                rw [Finset.sum_comm]
                simp only [Finset.sum_smul]
            _ = (-2 : ℂ) • ρ.op i 0 y := by
                simp only [hsum2, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
                  if_true]
        have hE : (sE • ρ.op e 0) v = 0 := by rw [LinearMap.smul_apply, hR e he 0, smul_zero]
        have hH : H v = (K : ℂ) • v := by
          rw [hHy]
          have hterm : ∀ c, (sE * S.f e i c) • ρ.op c 0 v =
              (sE * S.f e i c * ((K : ℂ) * T.τ c)) • v := by
            intro c
            by_cases hf : S.f e i c = 0
            · simp [hf]
            · rw [hv, hCv c (hec c hf), smul_smul]
          rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_smul]
          congr 1
          rw [show (∑ c, sE * S.f e i c * ((K : ℂ) * T.τ c)) =
              (K : ℂ) * ∑ c, sE * S.f e i c * T.τ c by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring, hsum1, mul_one]
        set u := (ρ.op i 0)^[K + 1] v with hu
        have hFu : ρ.op i 0 u = 0 := by
          rw [hu, ← Function.iterate_succ_apply' (ρ.op i 0), hv, iterate_comm_c0 T (Or.inr hi)]
          have := rs_lowering h hi
          rw [h1, mul_one] at this
          rw [this, map_zero]
        have hEu : (sE • ρ.op e 0) u = 0 := by
          rw [hu, sl2_E_Fpow (sE • ρ.op e 0) (ρ.op i 0) H hEF hHF v _ hE hH K]
          simp
        have hHu : H u = ((K : ℂ) - 2 * ((K + 1 : ℕ) : ℂ)) • u :=
          sl2_H_Fpow (ρ.op i 0) H hHF v _ hH (K + 1)
        refine sl2_vanish (sE • ρ.op e 0) (ρ.op i 0) H hEF ?_ hEu hFu hHu
        push_cast
        intro h0
        have h2 : ((K : ℝ) + 2) = 0 := by
          have := congrArg Complex.re h0
          simp at this
          linarith
        have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
        linarith
    · -- truncations
      change ρ.op x (if x = S.c₀ then D else K) (ρ.op S.c₀ (D + 1) w) = 0
      by_cases hx0 : x = S.c₀
      · subst hx0
        rw [if_pos rfl]
        have hG := theta_garlandG T hN h (2 * D + 1) (by omega)
        rw [Finset.sum_eq_add_of_mem (D, D + 1) (D + 1, D)
          (Finset.mem_antidiagonal.mpr (by simp; omega))
          (Finset.mem_antidiagonal.mpr (by simp; omega)) (by simp) ?_] at hG
        · rw [comm_c0 T (Or.inl T.c0_fusion) (D + 1) D] at hG
          exact two_eq_zeroG hG
        · rintro ⟨i, j⟩ hx ⟨h1, h2⟩
          rw [Finset.mem_antidiagonal] at hx
          simp only [ne_eq, Prod.mk.injEq] at h1 h2 hx
          by_cases hj : D + 2 ≤ j
          · rw [hFθ j hj, map_zero]
          · rw [comm_c0 T (Or.inl T.c0_fusion), hFθ i (by omega), map_zero]
      · rw [if_neg hx0]
        rcases T.fusionRoot x hx hx0 with ⟨β, κ, hβ, hκ, hβc⟩ | hxl
        · have hbr : ∀ i (y : V), ρ.op β 0 (ρ.op S.c₀ i y) =
              ρ.op S.c₀ i (ρ.op β 0 y) + κ • ρ.op x i y := by
            intro i y
            rw [commG, Finset.sum_eq_single x (fun c _ hc => by rw [hβc c, if_neg hc, zero_smul])
              (by simp), hβc, if_pos rfl, zero_add]
          have hG := congrArg (ρ.op β 0) (theta_garlandG T hN h (K + (D + 1)) (by omega))
          rw [map_sum, map_zero] at hG
          simp only [hbr, rs_raising h hβ, map_zero, zero_add, map_smul] at hG
          simp only [← smul_add] at hG
          rw [← Finset.smul_sum] at hG
          have hsum := (smul_eq_zero.mp hG).resolve_left hκ
          simp only [comm_c0 T (Or.inl hx)] at hsum
          rw [Finset.sum_add_distrib,
            ← Finset.Nat.sum_antidiagonal_swap
              (f := fun y : ℕ × ℕ => ρ.op S.c₀ y.1 (ρ.op x y.2 w))] at hsum
          simp only [Prod.fst_swap, Prod.snd_swap] at hsum
          have hS := two_eq_zeroG hsum
          rw [Finset.sum_eq_single (K, D + 1)] at hS
          · rw [comm_c0 T (Or.inl hx)]; exact hS
          · rintro ⟨i, j⟩ hij hne
            rw [Finset.mem_antidiagonal] at hij
            simp only [ne_eq, Prod.mk.injEq] at hne hij
            by_cases hi : K + 1 ≤ i
            · rw [hFx x hx hx0 i hi, map_zero]
            · rw [← comm_c0 T (Or.inl hx), hFθ j (by omega), map_zero]
          · intro hn; exact absurd (Finset.mem_antidiagonal.mpr (by simp)) hn
        · rw [comm_c0 T (Or.inl hx), hK0 x hxl, map_zero]
    · exact hCp c (Or.inr hc) r hr
  · simp only [ravSpec, Set.mem_setOf_eq]
    rintro q (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    · change ρ.op c 0 _ = _
      rw [hCv c (Or.inl hc), T.tauH c hc]; push_cast; ring_nf
    · change ρ.op c 0 _ = _
      rw [hCv c (Or.inr hc), T.tauN c hc]; push_cast; ring_nf

end Kernel

/-- **`RavinderKernelRelG` for Ravinder's family** from the table and `ThetaNilG`. -/
theorem ravinderKernelRelG_of_table (T : KernelTable S) (hN : ThetaNilG S) :
    RavinderKernelRelG S.f (ravFam S) (ravKw S) := by
  intro a b V _ _ ρ w h
  have h' : Sat S.f ρ w (ravSpec S (a + b + 1) (2 * a + b + 2)) := by
    rw [ravFam, show a + 1 + b = a + b + 1 by omega, show 2 * (a + 1) + b = 2 * a + b + 2 by omega]
      at h
    exact h
  have := kernel_sat T hN (K := a + b) (D := 2 * a + b) (by omega) h'
  exact this

end

end VOA.DeligneAudit.UnivG

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.ravFam_step
#print axioms VOA.DeligneAudit.UnivG.theta_garlandG
#print axioms VOA.DeligneAudit.UnivG.kernel_sat
#print axioms VOA.DeligneAudit.UnivG.ravinderKernelRelG_of_table
end AxiomAudit
