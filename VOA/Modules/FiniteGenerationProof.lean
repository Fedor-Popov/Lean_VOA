/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.FiniteGeneration

/-!
# `degStep` discharged — finite generation 5.3.11a unconditional (Gannon 5.3.11a)

This file closes the single `degStep` residual left by `Modules.FiniteGeneration`: it discharges
the per-degree closure step **unconditionally**, hence `iterProdSpan W S = ⊤` for any homogeneous
set `S` with `span S ⊔ O₂ = ⊤` (e.g. lifts of an `A₂(𝒱)`-basis).

The genuine new content is the **convergent master peeling** (`genPeel_master`): the all-`ℤ`
Borcherds iterate `Core.Reconstruction.mode_iterate` peels a homogeneous product `a₍₋ℓ₎b` into two
families — `span S` left factors are single `S`-steps, `O₂⊓𝒱ₚ` left factors recurse through
`genPeel_master_gen` — driven by a double induction (outer degree `n`, inner left-factor degree
`p`). Both families strictly lower `p` and feed right factors of strictly lower degree `< n`, so
the induction converges.

* **`genPeel_master`** — the convergent master peeling (double induction, `mode_iterate`).
* **`genPeel_discharged`** — the per-degree generator obligation, the `ℓ = 2` instance.
* **`degStep_unconditional`** — the per-degree closure step, unconditional.
* **`iterProdSpan_eq_top`** (+ `…_of_finite`) — finite generation 5.3.11a, unconditional.

## Status
`sorry`-free, with no project axioms.  `genPeel_master`, `degStep_unconditional`,
`iterProdSpan_eq_top` are all `[propext, Classical.choice, Quot.sound]` — discharging the
`degStep` hypothesis of `Modules.FiniteGeneration`, so 5.3.11a holds unconditionally.

## References
* Gannon 5.3.11a; Zhu [574]; Frenkel–Zhu; Dong–Li–Mason; Buhl/Gaberdiel–Neitzke (PBW spanning).
-/

namespace VOA
open VertexOperatorAlgebra
open scoped BigOperators
open Classical
open DirectSum

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

noncomputable instance gradDecomp (W : VertexOperatorAlgebra 𝒱) :
    DirectSum.Decomposition W.grading :=
  W.isInternal.chooseDecomposition W.grading

/-- The homogeneous projection onto degree `n` (`π_n`). -/
noncomputable def piHom (W : VertexOperatorAlgebra 𝒱) (n : ℤ) : 𝒱 →ₗ[ℂ] 𝒱 :=
  (W.grading n).subtype.comp
    ((DirectSum.component ℂ ℤ (fun i => (W.grading i : Submodule ℂ 𝒱)) n).comp
      (DirectSum.decomposeLinearEquiv W.grading).toLinearMap)

theorem piHom_apply (W : VertexOperatorAlgebra 𝒱) (n : ℤ) (x : 𝒱) :
    piHom W n x = ((DirectSum.decompose W.grading x) n : 𝒱) := rfl

theorem piHom_mem (W : VertexOperatorAlgebra 𝒱) (n : ℤ) (x : 𝒱) :
    piHom W n x ∈ W.grading n := by
  rw [piHom_apply]; exact ((DirectSum.decompose W.grading x) n).2

theorem piHom_of_mem (W : VertexOperatorAlgebra 𝒱) {n : ℤ} {x : 𝒱} (hx : x ∈ W.grading n) :
    piHom W n x = x := by
  rw [piHom_apply]
  have hdec : DirectSum.decompose W.grading x
      = DirectSum.of (fun i => (W.grading i : Submodule ℂ 𝒱)) n ⟨x, hx⟩ :=
    DirectSum.decompose_coe (ℳ := fun i => (W.grading i : Submodule ℂ 𝒱)) (⟨x, hx⟩ : W.grading n)
  rw [hdec]
  simp

theorem piHom_of_mem_ne (W : VertexOperatorAlgebra 𝒱) {n k : ℤ} (hnk : k ≠ n) {x : 𝒱}
    (hx : x ∈ W.grading k) : piHom W n x = 0 := by
  rw [piHom_apply]
  have hdec : DirectSum.decompose W.grading x
      = DirectSum.of (fun i => (W.grading i : Submodule ℂ 𝒱)) k ⟨x, hx⟩ :=
    DirectSum.decompose_coe (ℳ := fun i => (W.grading i : Submodule ℂ 𝒱)) (⟨x, hx⟩ : W.grading k)
  rw [hdec]
  simp only [DirectSum.of_eq_of_ne (β := fun i => (W.grading i : Submodule ℂ 𝒱))
    k n (⟨x, hx⟩ : W.grading k) hnk.symm, ZeroMemClass.coe_zero]

/-- If every element of `G` is homogeneous, then `π_n` maps `span G` into `span G`. -/
theorem piHom_maps_span_homog (W : VertexOperatorAlgebra 𝒱) (n : ℤ) (G : Set 𝒱)
    (hG : ∀ g ∈ G, IsHomog W g) {x : 𝒱} (hx : x ∈ Submodule.span ℂ G) :
    piHom W n x ∈ Submodule.span ℂ G := by
  refine Submodule.span_induction
    (p := fun x _ => piHom W n x ∈ Submodule.span ℂ G) ?_ ?_ ?_ ?_ hx
  · intro g hg
    obtain ⟨k, hk⟩ := hG g hg
    by_cases hkn : k = n
    · subst hkn
      rw [piHom_of_mem W hk]; exact Submodule.subset_span hg
    · rw [piHom_of_mem_ne W hkn hk]; exact (Submodule.span ℂ G).zero_mem
  · simp only [map_zero]; exact (Submodule.span ℂ G).zero_mem
  · intro y z _ _ hy hz; rw [map_add]; exact (Submodule.span ℂ G).add_mem hy hz
  · intro c y _ hy; rw [map_smul]; exact (Submodule.span ℂ G).smul_mem c hy

/-- The homogeneous `O₂`-generators are homogeneous (degree `p+q+1`). -/
theorem O₂homGen_homog (W : VertexOperatorAlgebra 𝒱) {g : 𝒱} (hg : g ∈ O₂homGen W) :
    IsHomog W g := by
  obtain ⟨p, q, a, b, ha, hb, rfl⟩ := hg
  exact ⟨p + q + 1, gen_mem_grading W ha hb⟩

/-- `π_n` maps `O₂` into `O₂`. -/
theorem piHom_maps_O₂ (W : VertexOperatorAlgebra 𝒱) (n : ℤ) {x : 𝒱} (hx : x ∈ O₂ W) :
    piHom W n x ∈ O₂ W := by
  rw [O₂_eq_span_homGen] at hx ⊢
  exact piHom_maps_span_homog W n (O₂homGen W) (fun g hg => O₂homGen_homog W hg) hx

/-- **Graded spanning (part (i)).** For a homogeneous spanning-mod-`O₂` set `S`
(`span S ⊔ O₂ = ⊤`), every degree-`n` piece lies in `span S ⊔ (O₂ ⊓ 𝒱ₙ)`. -/
theorem grading_le_span_sup_O₂_inf (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W) (n : ℤ) :
    W.grading n ≤ Submodule.span ℂ S ⊔ (O₂ W ⊓ W.grading n) := by
  intro x hx
  have hxtop : x ∈ Submodule.span ℂ S ⊔ O₂ W := htop ▸ Submodule.mem_top
  rw [Submodule.mem_sup] at hxtop
  obtain ⟨a, ha, b, hb, rfl⟩ := hxtop
  -- apply π_n; x ∈ 𝒱ₙ so π_n x = x
  have hpix : piHom W n (a + b) = a + b := piHom_of_mem W hx
  rw [map_add] at hpix
  have hpa_S : piHom W n a ∈ Submodule.span ℂ S := piHom_maps_span_homog W n S hShom ha
  have hpa_g : piHom W n a ∈ W.grading n := piHom_mem W n a
  have hpb_O : piHom W n b ∈ O₂ W := piHom_maps_O₂ W n hb
  have hpb_g : piHom W n b ∈ W.grading n := piHom_mem W n b
  rw [← hpix]
  exact Submodule.add_mem_sup hpa_S ⟨hpb_O, hpb_g⟩

/-! ## Part (ii): the degree-`n` homogeneous `O₂`-generators and the graded reduction. -/

/-- The homogeneous `O₂`-generators of *exact* degree `n`: `a₍₋₂₎b`, `a∈𝒱ₚ`, `b∈𝒱_q`, `p+q+1=n`. -/
def O₂homGenDeg (W : VertexOperatorAlgebra 𝒱) (n : ℤ) : Set 𝒱 :=
  {x | ∃ (p q : ℤ) (a b : 𝒱), a ∈ W.grading p ∧ b ∈ W.grading q ∧ p + q + 1 = n ∧
    x = W.smul a (-2) b}

/-- A degree-`n` homogeneous generator is homogeneous of degree `n`. -/
theorem O₂homGenDeg_mem_grading (W : VertexOperatorAlgebra 𝒱) {n : ℤ} {g : 𝒱}
    (hg : g ∈ O₂homGenDeg W n) : g ∈ W.grading n := by
  obtain ⟨p, q, a, b, ha, hb, hpq, rfl⟩ := hg
  rw [← hpq]; exact gen_mem_grading W ha hb

/-- `π_n` sends a general homogeneous `O₂`-generator into `span (O₂homGenDeg W n)`. -/
theorem piHom_homGen_mem (W : VertexOperatorAlgebra 𝒱) (n : ℤ) {g : 𝒱}
    (hg : g ∈ O₂homGen W) : piHom W n g ∈ Submodule.span ℂ (O₂homGenDeg W n) := by
  obtain ⟨p, q, a, b, ha, hb, rfl⟩ := hg
  by_cases hd : p + q + 1 = n
  · rw [piHom_of_mem W (by rw [← hd]; exact gen_mem_grading W ha hb)]
    exact Submodule.subset_span ⟨p, q, a, b, ha, hb, hd, rfl⟩
  · rw [piHom_of_mem_ne W (k := p + q + 1) (by omega) (gen_mem_grading W ha hb)]
    exact (Submodule.span ℂ (O₂homGenDeg W n)).zero_mem

/-- **Graded reduction of `O₂ ⊓ 𝒱ₙ`**: it lies in the span of the *degree-`n`* homogeneous
generators. -/
theorem O₂_inf_grading_le_span_deg (W : VertexOperatorAlgebra 𝒱) (n : ℤ) :
    O₂ W ⊓ W.grading n ≤ Submodule.span ℂ (O₂homGenDeg W n) := by
  intro x hx
  obtain ⟨hxO, hxg⟩ := hx
  rw [O₂_eq_span_homGen] at hxO
  -- x = π_n x (since x ∈ 𝒱ₙ), and π_n maps span(O₂homGen) into span(O₂homGenDeg n)
  rw [← piHom_of_mem W hxg]
  refine Submodule.span_induction
    (p := fun y _ => piHom W n y ∈ Submodule.span ℂ (O₂homGenDeg W n)) ?_ ?_ ?_ ?_ hxO
  · intro g hg; exact piHom_homGen_mem W n hg
  · simp only [map_zero]; exact (Submodule.span ℂ (O₂homGenDeg W n)).zero_mem
  · intro y z _ _ hy hz; rw [map_add]
    exact (Submodule.span ℂ (O₂homGenDeg W n)).add_mem hy hz
  · intro c y _ hy; rw [map_smul]
    exact (Submodule.span ℂ (O₂homGenDeg W n)).smul_mem c hy

/-! ## Assembling parts (i)+(ii)-graded into `degStep`, modulo the per-generator peeling. -/

/-- **`degStep` from the per-generator peeling.**  If every degree-`n` homogeneous generator
`a₍₋₂₎b` lies in `T = iterProdSpan W S` (the peeling obligation), then the full per-degree
closure step holds, for a homogeneous spanning-mod-`O₂` set `S`. -/
theorem degStep_of_genPeel (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (genPeel : ∀ n : ℤ, 0 ≤ n → (∀ k : ℤ, k < n → W.grading k ≤ iterProdSpan W S) →
      ∀ g ∈ O₂homGenDeg W n, g ∈ iterProdSpan W S)
    (n : ℤ) (hn : 0 ≤ n) (ih : ∀ k : ℤ, k < n → W.grading k ≤ iterProdSpan W S) :
    W.grading n ≤ iterProdSpan W S := by
  -- (i) graded spanning: 𝒱ₙ ≤ span S ⊔ (O₂ ⊓ 𝒱ₙ)
  refine le_trans (grading_le_span_sup_O₂_inf W S hShom htop n) ?_
  refine sup_le (span_S_le_iterProdSpan W S) ?_
  -- (ii) O₂ ⊓ 𝒱ₙ ≤ span(degree-n homGens) ≤ T
  refine le_trans (O₂_inf_grading_le_span_deg W n) ?_
  rw [Submodule.span_le]
  exact fun g hg => genPeel n hn ih g hg

/-! ## The single peeling step (mode_iterate expansion of `(s₍₋k₎a')₍₋₂₎b`).

The genuine `mode_iterate`-peeling content of `genPeel`.  Writing a degree-`n` generator's left
factor as an `S`-step `a = s₍₋k₎a'`, the all-`ℤ` Borcherds iterate expands `(s₍₋k₎a')₍₋₂₎b` into
two families, each a single `smul` (mode) product whose membership in `T` is the residual. -/

/-- The `i`-th summand of `(s₍₋k₎a')₍₋₂₎b`. -/
noncomputable def peelTerm (W : VertexOperatorAlgebra 𝒱) (s a' b : 𝒱) (k : ℤ) (i : ℕ) : 𝒱 :=
  ((-1 : ℂ) ^ i * gBinom (-k) i) •
    (W.smul s (-k - (i : ℤ)) (W.smul a' (-2 + (i : ℤ)) b)
      - ((-1 : ℂ) ^ (-k)) • W.smul a' (-k + -2 - (i : ℤ)) (W.smul s (i : ℤ) b))

/-- The peel expansion: `(s₍₋k₎a')₍₋₂₎b = ∑ᶠ i, peelTerm`. -/
theorem peel_expand (W : VertexOperatorAlgebra 𝒱) (s a' b : 𝒱) (k : ℤ) :
    W.smul (W.smul s (-k) a') (-2) b = ∑ᶠ i : ℕ, peelTerm W s a' b k i := by
  have h := mode_iterate W s a' (-k) (-2) b
  simpa only [peelTerm] using h

/-- **Family-A closure.** Each Family-A factor `s₍₋(k+i)₎(·)` (an `S`-step, since `k ≥ 1`)
keeps `T = iterProdSpan W S` invariant: if `s ∈ S` and `y ∈ T` then `s₍₋k-i₎y ∈ T`. -/
theorem familyA_mem (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱) {s : 𝒱} (hs : s ∈ S)
    {k : ℤ} (hk : 1 ≤ k) (i : ℕ) {y : 𝒱} (hy : y ∈ iterProdSpan W S) :
    W.smul s (-k - (i : ℤ)) y ∈ iterProdSpan W S := by
  have hm : 1 ≤ k + (i : ℤ) := by have : (0:ℤ) ≤ (i:ℤ) := Int.ofNat_nonneg i; omega
  have := smul_mem_iterProdSpan W S hs hm hy
  rwa [show -(k + (i : ℤ)) = -k - (i : ℤ) from by ring] at this

/-! ## The `span S` left-factor case is a direct `S`-step (no peeling needed). -/

/-- For a *generator* `s ∈ S` and any `b ∈ T`, the degree-raising product `s₍₋₂₎b` is an
`S`-step (mode `-2`, `m = 2 ≥ 1`), hence in `T`. -/
theorem smul_neg_two_mem_of_S (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱) {s : 𝒱} (hs : s ∈ S)
    {b : 𝒱} (hb : b ∈ iterProdSpan W S) : W.smul s (-2) b ∈ iterProdSpan W S := by
  have := smul_mem_iterProdSpan W S hs (show (1:ℤ) ≤ 2 from by norm_num) hb
  rwa [show -(2:ℤ) = (-2 : ℤ) from rfl] at this

/-- **`span S` left-factor case.** For `a ∈ span ℂ S` and `b ∈ T`, `a₍₋₂₎b ∈ T`.  (The hard
left factors are the `O₂ ⊓ 𝒱ₚ` ones; the `span S` ones peel in one `S`-step.) -/
theorem spanS_left_neg_two_mem (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    {a : 𝒱} (ha : a ∈ Submodule.span ℂ S) {b : 𝒱} (hb : b ∈ iterProdSpan W S) :
    W.smul a (-2) b ∈ iterProdSpan W S := by
  refine Submodule.span_induction
    (p := fun a _ => W.smul a (-2) b ∈ iterProdSpan W S) ?_ ?_ ?_ ?_ ha
  · intro s hs; exact smul_neg_two_mem_of_S W S hs hb
  · simp only [PreVertexAlgebra.smul_zero_left]; exact (iterProdSpan W S).zero_mem
  · intro x y _ _ hx hy; rw [PreVertexAlgebra.smul_add_left]
    exact (iterProdSpan W S).add_mem hx hy
  · intro c x _ hx; rw [PreVertexAlgebra.smul_smul_left]
    exact (iterProdSpan W S).smul_mem c hx

/-! ## The convergent master peeling: double induction (outer degree `n`, inner left-degree `p`).

Strategy (Zhu): with the degree IH `∀k<n, 𝒱ₖ ≤ T`, prove for every left-factor degree `p` and
every mode `ℓ ≥ 2` that a homogeneous product `a₍₋ℓ₎b` (`a∈𝒱ₚ`, `b∈𝒱_q`, of total degree `n`)
lies in `T`, by strong induction on `p`.  Peel `a` by part (i):
* `a ∈ span S`  → `a₍₋ℓ₎b` is a single `S`-step (`smul_mem_iterProdSpan`), closed.
* `a ∈ O₂⊓𝒱ₚ` → `a = a'₍₋₂₎c`; `mode_iterate` rewrites `(a'₍₋₂₎c)₍₋ℓ₎b` into Family-A
  `a'₍₋(2+i)₎(c₍₋ℓ+i₎b)` (recurse on `p' < p`, right factor of degree `< n` ⊆ `T` by degree IH)
  and Family-B `c₍₋(2+ℓ+i)₎(a'₍ᵢ₎b)` (recurse on `p'' < p`, right factor `a'₍ᵢ₎b` of degree `< n`).
Both feedback families strictly lower `p` and feed right factors of strictly lower degree `n`. -/

/-- A homogeneous product `a₍ₘ₎b` is homogeneous (degree `p+q-m-1`). -/
theorem smul_homog (W : VertexOperatorAlgebra 𝒱) {p q : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (m : ℤ) : IsHomog W (W.smul a m b) :=
  ⟨p + q - m - 1, W.smul_mem_grading ha hb m⟩

/-- The general `peelTerm` for `(a'₍₋₂₎c)₍₋ℓ₎b` (outer mode `-ℓ`). -/
noncomputable def peelTerm2 (W : VertexOperatorAlgebra 𝒱) (a' c b : 𝒱) (ℓ : ℤ) (i : ℕ) : 𝒱 :=
  ((-1 : ℂ) ^ i * gBinom (-2 : ℤ) i) •
    (W.smul a' (-2 - (i : ℤ)) (W.smul c (-ℓ + (i : ℤ)) b)
      - ((-1 : ℂ) ^ (-2 : ℤ)) • W.smul c (-2 + -ℓ - (i : ℤ)) (W.smul a' (i : ℤ) b))

theorem peel2_expand (W : VertexOperatorAlgebra 𝒱) (a' c b : 𝒱) (ℓ : ℤ) :
    W.smul (W.smul a' (-2) c) (-ℓ) b = ∑ᶠ i : ℕ, peelTerm2 W a' c b ℓ i := by
  have h := mode_iterate W a' c (-2) (-ℓ) b
  simpa only [peelTerm2] using h

/-- Finiteness of the `peelTerm2` support (from VA5 regularity in both inner products). -/
theorem peelTerm2_support_finite (W : VertexOperatorAlgebra 𝒱) (a' c b : 𝒱) (ℓ : ℤ) :
    (Function.support (peelTerm2 W a' c b ℓ)).Finite := by
  obtain ⟨Nc, hNc⟩ := W.regularity c b   -- c₍ₙ₎b = 0 for n ≥ Nc
  obtain ⟨Na, hNa⟩ := W.regularity a' b  -- a'₍ₙ₎b = 0 for n ≥ Na
  apply Set.Finite.subset (Set.finite_Icc 0 (max (Nc + ℓ) Na).toNat)
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  rw [not_le] at hbig
  apply hi
  simp only [peelTerm2]
  have hA : W.smul c (-ℓ + (i : ℤ)) b = 0 :=
    hNc (-ℓ + (i : ℤ)) (by
      have h1 : Nc + ℓ ≤ max (Nc + ℓ) Na := le_max_left _ _
      have h2 : (max (Nc + ℓ) Na) < (i : ℤ) :=
        lt_of_le_of_lt (Int.self_le_toNat _) (by exact_mod_cast hbig)
      omega)
  have hB : W.smul a' (i : ℤ) b = 0 :=
    hNa (i : ℤ) (by
      have h1 : Na ≤ max (Nc + ℓ) Na := le_max_right _ _
      have h2 : (max (Nc + ℓ) Na) < (i : ℤ) :=
        lt_of_le_of_lt (Int.self_le_toNat _) (by exact_mod_cast hbig)
      omega)
  rw [hA, hB, PreVertexAlgebra.smul_zero_right, PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero,
    smul_zero]

/-- **Master peeling (single-`O₂`-generator case).**  Given the degree IH, for a degree-`p`
homogeneous `O₂`-generator `g = a'₍₋₂₎c` and a homogeneous `b ∈ 𝒱_q` with
`p + q + ℓ - 1 = n` (`ℓ ≥ 2`), the product `g₍₋ℓ₎b ∈ T`, ASSUMING the master claim at all
strictly smaller left-degrees `p' < p` (`recP`).  This is the inductive core. -/
theorem genPeel_master_gen (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (n : ℤ) (ih : ∀ k : ℤ, k < n → W.grading k ≤ iterProdSpan W S)
    {p q ℓ : ℤ} {a' c b : 𝒱} {p' p'' : ℤ}
    (recP : ∀ pr : ℤ, pr ≥ 0 → pr < p → ∀ q' ℓ' (a₂ b₂ : 𝒱), 2 ≤ ℓ' → a₂ ∈ W.grading pr →
      b₂ ∈ W.grading q' → pr + q' + ℓ' - 1 = n → W.smul a₂ (-ℓ') b₂ ∈ iterProdSpan W S)
    (hℓ : 2 ≤ ℓ) (ha' : a' ∈ W.grading p') (hc : c ∈ W.grading p'')
    (hb : b ∈ W.grading q) (hppp : p' + p'' + 1 = p) (hp'lt : p' < p) (hp''lt : p'' < p)
    (hp'0 : 0 ≤ p') (hp''0 : 0 ≤ p'') (hq0 : 0 ≤ q)
    (htot : p + q + ℓ - 1 = n) :
    W.smul (W.smul a' (-2) c) (-ℓ) b ∈ iterProdSpan W S := by
  rw [peel2_expand W a' c b ℓ]
  apply finsum_mem_submodule_pd
  intro i
  simp only [peelTerm2]
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · -- Family A: a'₍₋(2+i)₎(c₍₋ℓ+i₎b), recurse on p' < p
    -- inner right factor c₍₋ℓ+i₎b ∈ 𝒱_{p''+q+ℓ-i-1}; total degree = n
    have hmA : W.smul a' (-2 - (i : ℤ)) (W.smul c (-ℓ + (i : ℤ)) b)
        = W.smul a' (-(2 + (i : ℤ))) (W.smul c (-ℓ + (i : ℤ)) b) := by
      rw [show -(2 + (i : ℤ)) = -2 - (i : ℤ) from by ring]
    rw [hmA]
    refine recP p' hp'0 hp'lt (p'' + q - (-ℓ + (i:ℤ)) - 1) (2 + (i : ℤ)) a'
      (W.smul c (-ℓ + (i : ℤ)) b) (by have : (0:ℤ) ≤ (i:ℤ) := Int.ofNat_nonneg i; omega)
      ha' (W.smul_mem_grading hc hb _) (by omega)
  · -- Family B: c₍₋(2+ℓ+i)₎(a'₍ᵢ₎b), recurse on p'' < p
    apply Submodule.smul_mem
    have hmB : W.smul c (-2 + -ℓ - (i : ℤ)) (W.smul a' (i : ℤ) b)
        = W.smul c (-(2 + ℓ + (i : ℤ))) (W.smul a' (i : ℤ) b) := by
      rw [show -(2 + ℓ + (i : ℤ)) = -2 + -ℓ - (i : ℤ) from by ring]
    rw [hmB]
    refine recP p'' hp''0 hp''lt (p' + q - (i:ℤ) - 1) (2 + ℓ + (i : ℤ)) c
      (W.smul a' (i : ℤ) b) (by have : (0:ℤ) ≤ (i:ℤ) := Int.ofNat_nonneg i; omega)
      hc (W.smul_mem_grading ha' hb _) (by omega)

/-- **`span S` left-factor case, general mode.** For `a ∈ span ℂ S`, `b ∈ T`, and `ℓ ≥ 1`,
`a₍₋ℓ₎b ∈ T` (a single `S`-step). -/
theorem spanS_left_mem (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱) {ℓ : ℤ} (hℓ : 1 ≤ ℓ)
    {a : 𝒱} (ha : a ∈ Submodule.span ℂ S) {b : 𝒱} (hb : b ∈ iterProdSpan W S) :
    W.smul a (-ℓ) b ∈ iterProdSpan W S := by
  refine Submodule.span_induction
    (p := fun a _ => W.smul a (-ℓ) b ∈ iterProdSpan W S) ?_ ?_ ?_ ?_ ha
  · intro s hs; exact smul_mem_iterProdSpan W S hs hℓ hb
  · simp only [PreVertexAlgebra.smul_zero_left]; exact (iterProdSpan W S).zero_mem
  · intro x y _ _ hx hy; rw [PreVertexAlgebra.smul_add_left]
    exact (iterProdSpan W S).add_mem hx hy
  · intro c x _ hx; rw [PreVertexAlgebra.smul_smul_left]
    exact (iterProdSpan W S).smul_mem c hx

/-- **The convergent master peeling.**  Given the degree IH `∀k<n, 𝒱ₖ ≤ T`, every homogeneous
product `a₍₋ℓ₎b` (`a∈𝒱ₚ`, `b∈𝒱_q`, `ℓ ≥ 2`, total degree `p+q+ℓ-1 = n`) lies in `T`.  Proved by
strong induction on the left-factor degree `p` (`p.toNat`), peeling `a` by part (i):
`span S` factors are single `S`-steps, `O₂⊓𝒱ₚ` factors recurse through `genPeel_master_gen`. -/
theorem genPeel_master (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (n : ℤ) (ih : ∀ k : ℤ, k < n → W.grading k ≤ iterProdSpan W S) :
    ∀ p : ℤ, 0 ≤ p → ∀ (q ℓ : ℤ) (a b : 𝒱), 2 ≤ ℓ → a ∈ W.grading p → b ∈ W.grading q →
      p + q + ℓ - 1 = n → W.smul a (-ℓ) b ∈ iterProdSpan W S := by
  intro p hp0
  -- strong induction on p.toNat
  obtain ⟨P, hP⟩ : ∃ P : ℕ, p = (P : ℤ) := ⟨p.toNat, by omega⟩
  subst hP
  induction P using Nat.strong_induction_on with
  | _ P ihP =>
    intro q ℓ a b hℓ ha hb htot
    -- dispatch the trivial b = 0 case (product vanishes)
    by_cases hb0 : b = 0
    · subst hb0; rw [PreVertexAlgebra.smul_zero_right]; exact (iterProdSpan W S).zero_mem
    have hq0 : 0 ≤ q := by
      by_contra h; push_neg at h
      exact hb0 (by rw [W.positivity q h, Submodule.mem_bot] at hb; exact hb)
    -- right factor b ∈ T (degree q < n)?  q = n - p - ℓ + 1; with ℓ≥2 ⟹ q ≤ n-1 < n.
    have hbT : b ∈ iterProdSpan W S := ih q (by omega) hb
    -- part (i) at degree P: a ∈ span S ⊔ (O₂ ⊓ 𝒱_P)
    have hai := grading_le_span_sup_O₂_inf W S hShom htop (P : ℤ) ha
    rw [Submodule.mem_sup] at hai
    obtain ⟨aS, haS, aO, ⟨haO_O, haO_g⟩, hsum⟩ := hai
    -- a₍₋ℓ₎b = aS₍₋ℓ₎b + aO₍₋ℓ₎b
    have hsplit : W.smul a (-ℓ) b = W.smul aS (-ℓ) b + W.smul aO (-ℓ) b := by
      rw [← hsum, PreVertexAlgebra.smul_add_left]
    rw [hsplit]
    refine (iterProdSpan W S).add_mem ?_ ?_
    · -- span S factor: single S-step
      exact spanS_left_mem W S (by omega) haS hbT
    · -- O₂ ⊓ 𝒱_P factor: reduce to generators, recurse via genPeel_master_gen
      have haO_span : aO ∈ Submodule.span ℂ (O₂homGenDeg W (P : ℤ)) :=
        O₂_inf_grading_le_span_deg W (P : ℤ) ⟨haO_O, haO_g⟩
      -- linear in aO: span induction over O₂homGenDeg
      refine Submodule.span_induction
        (p := fun aO _ => W.smul aO (-ℓ) b ∈ iterProdSpan W S) ?_ ?_ ?_ ?_ haO_span
      · -- single generator g = a'₍₋₂₎c, degree P
        rintro g ⟨p', p'', a', c, ha', hc, hpq', rfl⟩
        by_cases hg0 : W.smul a' (-2) c = 0
        · rw [hg0, PreVertexAlgebra.smul_zero_left]; exact (iterProdSpan W S).zero_mem
        · -- nonzero ⟹ a',c ≠ 0 ⟹ p',p'' ≥ 0 (positivity)
          have hp'0 : 0 ≤ p' := by
            by_contra h; push_neg at h
            exact hg0 (by rw [show a' = 0 by
              rw [W.positivity p' h, Submodule.mem_bot] at ha'; exact ha', W.smul_zero_left])
          have hp''0 : 0 ≤ p'' := by
            by_contra h; push_neg at h
            exact hg0 (by rw [show c = 0 by
              rw [W.positivity p'' h, Submodule.mem_bot] at hc; exact hc, W.smul_zero_right])
          refine genPeel_master_gen W S n ih ?_ hℓ ha' hc hb hpq'
            (by omega) (by omega) hp'0 hp''0 hq0 (by omega)
          -- recP: master at strictly smaller left-degree pr < P
          intro pr hpr0 hprlt qr ℓr ar br hℓr har hbr htotr
          obtain ⟨Pr, hPr⟩ : ∃ Pr : ℕ, pr = (Pr : ℤ) := ⟨pr.toNat, by omega⟩
          subst hPr
          exact ihP Pr (by exact_mod_cast hprlt) (by exact_mod_cast hpr0) qr ℓr ar br
            hℓr har hbr htotr
      · simp only [PreVertexAlgebra.smul_zero_left]; exact (iterProdSpan W S).zero_mem
      · intro x y _ _ hx hy; rw [PreVertexAlgebra.smul_add_left]
        exact (iterProdSpan W S).add_mem hx hy
      · intro c' x _ hx; rw [PreVertexAlgebra.smul_smul_left]
        exact (iterProdSpan W S).smul_mem c' hx

/-- **`genPeel` (the per-degree generator obligation), discharged.**  Every degree-`n`
homogeneous generator `a₍₋₂₎b` lies in `T`, granted the degree IH — the `ℓ = 2` instance of the
master peeling. -/
theorem genPeel_discharged (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (n : ℤ) (hn : 0 ≤ n) (ih : ∀ k : ℤ, k < n → W.grading k ≤ iterProdSpan W S) :
    ∀ g ∈ O₂homGenDeg W n, g ∈ iterProdSpan W S := by
  rintro g ⟨p, q, a, b, ha, hb, hpq, rfl⟩
  by_cases hg0 : W.smul a (-2) b = 0
  · rw [hg0]; exact (iterProdSpan W S).zero_mem
  · -- a ≠ 0 ⟹ p ≥ 0 (positivity)
    have hp0 : 0 ≤ p := by
      by_contra h; push_neg at h
      exact hg0 (by rw [show a = 0 by
        rw [W.positivity p h, Submodule.mem_bot] at ha; exact ha, W.smul_zero_left])
    have := genPeel_master W S hShom htop n ih p hp0 q 2 a b (le_refl 2) ha hb (by omega)
    simpa using this

/-! ## The headline: `degStep` unconditionally, hence `iterProdSpan W S = ⊤` (Gannon 5.3.11a). -/

/-- **`degStep`, unconditionally** (the per-degree closure step), for any homogeneous
spanning-mod-`O₂` set `S`: combining the graded spanning (i) with the discharged peeling (ii). -/
theorem degStep_unconditional (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (n : ℤ) (hn : 0 ≤ n) (ih : ∀ k : ℤ, k < n → W.grading k ≤ iterProdSpan W S) :
    W.grading n ≤ iterProdSpan W S :=
  degStep_of_genPeel W S hShom htop (fun n hn ih => genPeel_discharged W S hShom htop n hn ih)
    n hn ih

/-- **Finite generation (Gannon 5.3.11a), unconditional.**  For any *homogeneous* set `S` with
`span S ⊔ O₂ = ⊤` (e.g. lifts of an `A₂(𝒱)`-spanning set), the iterated-product span is all of
`𝒱`: `iterProdSpan W S = ⊤`.  This closes the `degStep` residual of `Modules.FiniteGeneration`. -/
theorem iterProdSpan_eq_top (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W) :
    iterProdSpan W S = ⊤ :=
  iterProdSpan_eq_top_of_degStep W S htop (degStep_unconditional W S hShom htop)

/-! ## Finite generation as a `Module.Finite` statement. -/

/-- **Finite generation, `Module.Finite` form.**  If a *finite* homogeneous set `S` spans `𝒱`
modulo `O₂` (`span S ⊔ O₂ = ⊤`), then the (closure of the) iterated products generate `𝒱` — and
in particular `𝒱` is a finitely-generated `ℂ`-module *iff* finitely many iterated products of `S`
already span it.  The conceptual content is `iterProdSpan W S = ⊤`: `𝒱` is spanned by the
iterated products `s^{i₁}₍₋m₁₎⋯𝟙` of `S` (Gannon 5.3.11a). -/
theorem iterProdSpan_eq_top_of_finite (W : VertexOperatorAlgebra 𝒱) (S : Finset 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (S : Set 𝒱) ⊔ O₂ W) :
    iterProdSpan W (S : Set 𝒱) = ⊤ :=
  iterProdSpan_eq_top W (S : Set 𝒱) (fun s hs => hShom s hs) htop

end VOA
