/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.VnatGenuine

/-!
# M8h: the twisted × twisted locality splits into DGM (4.22) and (4.23)

For two off-diagonal block fields `offdiag(c, d)` and `offdiag(c', d')` on `V × M`, the product
is block-diagonal, `offdiag(c,d)(z₁) offdiag(c',d')(z₂) = diag(c(z₁)d'(z₂), d(z₁)c'(z₂))`, so
locality is **equivalent** to the two `End`-valued relations

* on `V`:  `(z₁−z₂)ᴺ (c(z₁) d'(z₂) − c'(z₂) d(z₁)) = 0`,
* on `M`:  `(z₁−z₂)ᴺ (d(z₁) c'(z₂) − d'(z₂) c(z₁)) = 0`.

For `Y♮(t) = offdiag(W̄(t), W(t))` these are exactly DGM CMP 179 (1996) eq. (4.22)
(`W̄(t₁,z₁)W(t₂,z₂) ~ W̄(t₂,z₂)W(t₁,z₁)` on `V_Λ^+`) and eq. (4.23)
(`W(t₁,z₁)W̄(t₂,z₂) ~ W(t₂,z₂)W̄(t₁,z₁)` on `TP`).

## Main results
* `local_off_off_iff` — the generic equivalence.
* `YnatT_local_iff` — `Local (YnatT Wbar t₁) (YnatT Wbar t₂) ↔ VPBlockLocal ∧ TPBlockLocal`.
* `reconstruct_nat_of_blocks` — `reconstruct_nat_genuine` with `htt` replaced by the two
  block relations (4.22), (4.23) for the genuine `W̄ = leechWbar`.

## Status
`sorry`-free; all statements are equivalences or direct specialisations (no new hypotheses).
-/

namespace VOA.Moonshine

open Module (End)
open VnatBlock SkewIntertwiner Reconstruction

section Generic

variable {V : Type*} {M : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]

theorem blockOp_eq_zero_iff (a : End ℂ V) (c : M →ₗ[ℂ] V) (d : V →ₗ[ℂ] M) (b : End ℂ M) :
    blockOp a c d b = 0 ↔ a = 0 ∧ c = 0 ∧ d = 0 ∧ b = 0 := by
  constructor
  · intro h
    have h1 : ∀ x : V, a x = 0 ∧ d x = 0 := fun x => by
      have := congrArg (fun f => f (x, (0 : M))) h
      simp only [blockOp_apply, map_zero, add_zero, LinearMap.zero_apply] at this
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    have h2 : ∀ y : M, c y = 0 ∧ b y = 0 := fun y => by
      have := congrArg (fun f => f ((0 : V), y)) h
      simp only [blockOp_apply, map_zero, zero_add, LinearMap.zero_apply] at this
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    exact ⟨LinearMap.ext fun x => (h1 x).1, LinearMap.ext fun y => (h2 y).1,
      LinearMap.ext fun x => (h1 x).2, LinearMap.ext fun y => (h2 y).2⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact blockOp_zero

theorem blockF₂_eq_zero_iff (A : FormalDist₂ (End ℂ V)) (C : FormalDist₂ (M →ₗ[ℂ] V))
    (D : FormalDist₂ (V →ₗ[ℂ] M)) (B : FormalDist₂ (End ℂ M)) :
    blockF₂ A C D B = 0 ↔ A = 0 ∧ C = 0 ∧ D = 0 ∧ B = 0 := by
  constructor
  · intro h
    have hk : ∀ m n, A m n = 0 ∧ C m n = 0 ∧ D m n = 0 ∧ B m n = 0 := fun m n =>
      (blockOp_eq_zero_iff _ _ _ _).1 (congrFun (congrFun h m) n)
    exact ⟨FormalDist₂.ext fun m n => (hk m n).1, FormalDist₂.ext fun m n => (hk m n).2.1,
      FormalDist₂.ext fun m n => (hk m n).2.2.1, FormalDist₂.ext fun m n => (hk m n).2.2.2⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact FormalDist₂.ext fun m n => blockOp_zero

/-- The commutator of two off-diagonal block fields is block-diagonal. -/
theorem bracketDist_offF (c c' : FormalDist (M →ₗ[ℂ] V)) (d d' : FormalDist (V →ₗ[ℂ] M)) :
    bracketDist (offF c d) (offF c' d')
      = blockF₂ (fun m n => c m ∘ₗ d' n - c' n ∘ₗ d m) 0 0
          (fun m n => d m ∘ₗ c' n - d' n ∘ₗ c m) := by
  rw [offF, offF, bracketDist_blockF]
  refine FormalDist₂.ext fun m n => ?_
  simp only [blockF₂, formalDist_zero_apply]
  congr 1 <;> first | rfl | simp [LinearMap.comp_zero, LinearMap.zero_comp] <;> rfl

/-- **Off-diagonal–off-diagonal locality is equivalent to the two diagonal relations.** -/
theorem local_off_off_iff (c c' : FormalDist (M →ₗ[ℂ] V)) (d d' : FormalDist (V →ₗ[ℂ] M)) :
    Local (offF c d) (offF c' d') ↔
      (∃ N : ℕ, mulBySubPow N
        ((fun m n => c m ∘ₗ d' n - c' n ∘ₗ d m) : FormalDist₂ (End ℂ V)) = 0) ∧
      (∃ N : ℕ, mulBySubPow N
        ((fun m n => d m ∘ₗ c' n - d' n ∘ₗ c m) : FormalDist₂ (End ℂ M)) = 0) := by
  constructor
  · rintro ⟨N, hN⟩
    rw [bracketDist_offF, mulBySubPow_blockF₂, blockF₂_eq_zero_iff] at hN
    exact ⟨⟨N, hN.1⟩, ⟨N, hN.2.2.2⟩⟩
  · rintro ⟨⟨N₁, h₁⟩, ⟨N₂, h₂⟩⟩
    refine ⟨max N₁ N₂, ?_⟩
    rw [bracketDist_offF]
    refine mulBySubPow_blockF₂_eq_zero ?_ (map_zero _) (map_zero _) ?_
    · exact mulBySubPow_eq_zero_of_le (le_max_left N₁ N₂) h₁
    · exact mulBySubPow_eq_zero_of_le (le_max_right N₁ N₂) h₂

end Generic

/-! ## The moonshine specialisation -/

/-- **DGM (4.22)**: `W̄(t₁,z₁)W(t₂,z₂) ~ W̄(t₂,z₂)W(t₁,z₁)` on `V_Λ^+`. -/
def VPBlockLocal (Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)) (t₁ t₂ : TP) : Prop :=
  ∃ N : ℕ, mulBySubPow N
    ((fun m n => Wbar t₁ m ∘ₗ leechWsk t₂ n - Wbar t₂ n ∘ₗ leechWsk t₁ m) :
      FormalDist₂ (End ℂ SkewVP)) = 0

/-- **DGM (4.23)**: `W(t₁,z₁)W̄(t₂,z₂) ~ W(t₂,z₂)W̄(t₁,z₁)` on `TP` — the lattice-dependent
relation (step M8h). -/
def TPBlockLocal (Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)) (t₁ t₂ : TP) : Prop :=
  ∃ N : ℕ, mulBySubPow N
    ((fun m n => leechWsk t₁ m ∘ₗ Wbar t₂ n - leechWsk t₂ n ∘ₗ Wbar t₁ m) :
      FormalDist₂ (End ℂ TP)) = 0

/-- **tt-locality = (4.22) ∧ (4.23).** -/
theorem YnatT_local_iff (Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)) (t₁ t₂ : TP) :
    Local (YnatT Wbar t₁) (YnatT Wbar t₂) ↔
      VPBlockLocal Wbar t₁ t₂ ∧ TPBlockLocal Wbar t₁ t₂ :=
  local_off_off_iff _ _ _ _

/-- **`reconstruct_nat` for the genuine `W̄`, with `htt` split into DGM (4.22) and (4.23).** -/
theorem reconstruct_nat_of_blocks {κ : Type*} (g : κ → TP)
    (h422 : ∀ i j, VPBlockLocal leechWbar (g i) (g j))
    (h423 : ∀ i j, TPBlockLocal leechWbar (g i) (g j))
    (hspan : Submodule.span ℂ
      (Set.range (NonlinearConformal.wordSt (genNat leechWbar g) vacNat)) = ⊤) :
    ∃ YA : Vnat →ₗ[ℂ] FormalDist (End ℂ Vnat),
      (∀ u : Vnat, IsField (YA u)) ∧
      (∀ u v : Vnat, Local (YA u) (YA v)) ∧
      (∀ u : Vnat, (YA u) 0 vacNat = u) ∧
      (∀ u : Vnat, ∀ q : ℤ, q < 0 → (YA u) q vacNat = 0) ∧
      (∀ u : Vnat, DCovariant Tnat (YA u)) ∧
      (∀ u : SkewVP, YA (u, 0) = YnatU u) ∧
      (∀ i, YA (0, g i) = YnatT leechWbar (g i)) :=
  reconstruct_nat_genuine g (fun i j => (YnatT_local_iff _ _ _).2 ⟨h422 i j, h423 i j⟩) hspan

end VOA.Moonshine
