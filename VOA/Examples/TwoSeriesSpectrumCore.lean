/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesSocleDualCore

/-!
# Socle data from one cyclic functional, and transfer of socle data

Two abstract facts about the socle data `SocleSpectrum` of `TwoSeriesSocleDualCore`, for an
arbitrary module `M` with an action `ρ` of the nonnegative current modes `J^a_j`
(`a ∈ {e, f, h} = {0, 1, 2}`).

* `ZeroModeRel ρ` — the three commutation facts with `e₀` that are used:
  `J^a_{j+1} e₀ x = 0` whenever all `J^b_{j+1} x = 0`; `[f₀, e₀] = -h₀`; `[h₀, e₀] = 2e₀`.
* `sing_cyclic` — **a cyclic functional detects every singular vector.**  Let `w` be cyclic
  (its translates by mode words separate points), supported in degree `r`, of `h₀`-charge
  `-2r` (negative transpose), and assume the `h₀`-eigenvalues of `M` are of the form
  `-2r + m`, `m ∈ ℕ`.  Then a nonzero singular vector of degree `d` and charge `c` has
  `d = r`, `c = -2r` and `w s ≠ 0`.  (The translates of a singular vector are spanned by its
  `e₀`-string; only the string's bottom can carry charge `-2r`.)
* `socleSpectrum_of_cyclic` — hence **socle data with one label per degree**: the singular
  spaces are zero except `sing r (-2r)`, which has dimension `≤ 1`, and it is transversal to
  `avoid r r` whenever `w` kills the Cartan piece `Cart r`.
* `SocleSpectrum.comap` — **socle data pull back along injective intertwiners** that respect
  the grading and map `Cart N` into `Cart' N`.  This is the transfer step of a strict symbol
  map `gr_r L_k ↪ (model)`.

Everything is proved outright.
-/

namespace VOA.SocleDual

open Module VOA.CyclicEval
open scoped BigOperators

noncomputable section

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (ρ : Fin 3 × ℕ → Module.End ℂ M) (Mdeg : ℤ → Submodule ℂ M)

/-- The commutation facts with `e₀ = ρ (0, 0)` used to control the translates of a singular
vector. -/
structure ZeroModeRel : Prop where
  pos : ∀ (a : Fin 3) (j : ℕ) (x : M), (∀ b : Fin 3, ρ (b, j + 1) x = 0) →
    ρ (a, j + 1) (ρ (0, 0) x) = 0
  fe : ∀ x, ρ (1, 0) (ρ (0, 0) x) = ρ (0, 0) (ρ (1, 0) x) - ρ (2, 0) x
  he : ∀ x, ρ (2, 0) (ρ (0, 0) x) = ρ (0, 0) (ρ (2, 0) x) + (2 : ℂ) • ρ (0, 0) x

/-- The `e₀`-string of `s`. -/
def eString (s : M) : Submodule ℂ M :=
  Submodule.span ℂ (Set.range fun k : ℕ => (ρ (0, 0) ^ k) s)

variable {ρ Mdeg}

theorem eString_pow_mem (s : M) (k : ℕ) : (ρ (0, 0) ^ k) s ∈ eString ρ s :=
  Submodule.subset_span ⟨k, rfl⟩

theorem pow_succ_apply' (s : M) (k : ℕ) :
    (ρ (0, 0) ^ (k + 1)) s = ρ (0, 0) ((ρ (0, 0) ^ k) s) := by
  rw [pow_succ', Module.End.mul_apply]

/-- The string is stable under every nonnegative mode, for a singular vector. -/
theorem eString_stable (R : ZeroModeRel ρ) {s : M} {c : ℂ}
    (hpos : ∀ a j, ρ (a, j + 1) s = 0) (hf : ρ (1, 0) s = 0) (hh : ρ (2, 0) s = c • s) :
    ∀ (k : Fin 3 × ℕ), ∀ x ∈ eString ρ s, ρ k x ∈ eString ρ s := by
  -- facts on the string vectors
  have hP : ∀ (k : ℕ) (a : Fin 3) (j : ℕ), ρ (a, j + 1) ((ρ (0, 0) ^ k) s) = 0 := by
    intro k
    induction k with
    | zero => intro a j; simpa using hpos a j
    | succ k ih =>
      intro a j
      rw [pow_succ_apply']
      exact R.pos a j _ (fun b => ih b j)
  have hH : ∀ k : ℕ, ρ (2, 0) ((ρ (0, 0) ^ k) s) = (c + 2 * (k : ℂ)) • (ρ (0, 0) ^ k) s := by
    intro k
    induction k with
    | zero => simpa using hh
    | succ k ih =>
      rw [pow_succ_apply', R.he, ih, map_smul]
      push_cast
      module
  have hE : ∀ x ∈ eString ρ s, ρ (0, 0) x ∈ eString ρ s := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [← pow_succ_apply']
      exact eString_pow_mem s (k + 1)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul t x _ hx => rw [map_smul]; exact Submodule.smul_mem _ t hx
  have hF : ∀ k : ℕ, ρ (1, 0) ((ρ (0, 0) ^ k) s) ∈ eString ρ s := by
    intro k
    induction k with
    | zero => simp [hf]
    | succ k ih =>
      rw [pow_succ_apply', R.fe, hH]
      exact sub_mem (hE _ ih) (Submodule.smul_mem _ _ (eString_pow_mem s k))
  rintro ⟨a, j⟩ x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    cases j with
    | succ j => rw [hP]; exact zero_mem _
    | zero =>
      fin_cases a
      · change ρ (0, 0) ((ρ (0, 0) ^ k) s) ∈ _
        rw [← pow_succ_apply']; exact eString_pow_mem s (k + 1)
      · exact hF k
      · change ρ (2, 0) ((ρ (0, 0) ^ k) s) ∈ _
        rw [hH]; exact Submodule.smul_mem _ _ (eString_pow_mem s k)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul t x _ hx => rw [map_smul]; exact Submodule.smul_mem _ t hx

theorem word_mem_eString (R : ZeroModeRel ρ) {s : M} {c : ℂ}
    (hpos : ∀ a j, ρ (a, j + 1) s = 0) (hf : ρ (1, 0) s = 0) (hh : ρ (2, 0) s = c • s) :
    ∀ l : List (Fin 3 × ℕ), word ρ l s ∈ eString ρ s
  | [] => by simpa [word] using eString_pow_mem (ρ := ρ) s 0
  | k :: l => by
    rw [word_cons_apply]
    exact eString_stable R hpos hf hh k _ (word_mem_eString R hpos hf hh l)

/-- **A cyclic functional detects every singular vector.** -/
theorem sing_cyclic (R : ZeroModeRel ρ) {r : ℕ} (w : Module.Dual ℂ M)
    (cyc : ∀ m : M, (∀ l : List (Fin 3 × ℕ), w (word ρ l m) = 0) → m = 0)
    (supp : ∀ d : ℤ, d ≠ (r : ℤ) → ∀ m ∈ Mdeg d, w m = 0)
    (charge : w ∘ₗ ρ (2, 0) = (-(2 * (r : ℂ))) • w)
    (bound : ∀ (c : ℂ) (x : M), x ≠ 0 → ρ (2, 0) x = c • x → ∃ m : ℕ, c = -(2 * (r : ℂ)) + m)
    {d : ℤ} {c : ℂ} {s : M} (hs : s ∈ sing ρ Mdeg d c) (hs0 : s ≠ 0) :
    d = r ∧ c = -(2 * (r : ℂ)) ∧ w s ≠ 0 := by
  obtain ⟨hsd, hpos, hf, hh⟩ := hs
  -- some string vector has nonzero `w`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, w ((ρ (0, 0) ^ k) s) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hs0
    refine cyc s fun l => ?_
    have hmem := word_mem_eString R hpos hf hh l
    refine Submodule.span_induction (p := fun x _ => w x = 0) ?_ (map_zero w) ?_ ?_ hmem
    · rintro _ ⟨k, rfl⟩; exact hall k
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro t x _ hx; rw [map_smul, hx, smul_zero]
  -- its charge
  have hH : ρ (2, 0) ((ρ (0, 0) ^ k) s) = (c + 2 * (k : ℂ)) • (ρ (0, 0) ^ k) s := by
    clear hk
    induction k with
    | zero => simpa using hh
    | succ k ih =>
      rw [pow_succ_apply', R.he, ih, map_smul]
      push_cast
      module
  have hc : c + 2 * (k : ℂ) = -(2 * (r : ℂ)) := by
    have h1 := LinearMap.congr_fun charge ((ρ (0, 0) ^ k) s)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [hH, map_smul, smul_eq_mul] at h1
    exact mul_right_cancel₀ hk h1
  obtain ⟨m, hm⟩ := bound c s hs0 hh
  have hk0 : k = 0 ∧ m = 0 := by
    have : ((m + 2 * k : ℕ) : ℂ) = 0 := by push_cast; linear_combination hc - hm
    have : m + 2 * k = 0 := by exact_mod_cast this
    omega
  obtain ⟨rfl, rfl⟩ := hk0
  have hws : w s ≠ 0 := by simpa using hk
  refine ⟨?_, by simpa using hm, hws⟩
  by_contra hd
  exact hws (supp d hd s hsd)

variable {ι : Type*} [Finite ι] {deg : ι → ℕ} {cl : ι → ℕ} {Cart : ℕ → Submodule ℂ M}

/-- **Socle data from one cyclic functional.** -/
theorem socleSpectrum_of_cyclic (R : ZeroModeRel ρ) {r : ℕ}
    (w : Module.Dual ℂ M)
    (cyc : ∀ m : M, (∀ l : List (Fin 3 × ℕ), w (word ρ l m) = 0) → m = 0)
    (supp : ∀ d : ℤ, d ≠ (r : ℤ) → ∀ m ∈ Mdeg d, w m = 0)
    (charge : w ∘ₗ ρ (2, 0) = (-(2 * (r : ℂ))) • w)
    (bound : ∀ (c : ℂ) (x : M), x ≠ 0 → ρ (2, 0) x = c • x → ∃ m : ℕ, c = -(2 * (r : ℂ)) + m)
    (cart : ∀ m ∈ Cart r, w m = 0) (i₀ : ι) (hdeg : deg i₀ = r) (hcl : cl i₀ = r) :
    SocleSpectrum ρ Mdeg deg cl Cart where
  rank_le d c := by
    by_cases hdc : d = r ∧ c = -(2 * (r : ℂ))
    · obtain ⟨rfl, rfl⟩ := hdc
      have hinj : Function.Injective (w ∘ₗ (sing ρ Mdeg r (-(2 * (r : ℂ)))).subtype) := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro s hs
        by_contra hs0
        have hs0' : (s : M) ≠ 0 := fun h => hs0 (Subtype.ext h)
        exact (sing_cyclic R w cyc supp charge bound s.2 hs0').2.2 hs
      have h1 := LinearMap.finrank_le_finrank_of_injective hinj
      rw [Module.finrank_self] at h1
      refine h1.trans ?_
      haveI : Nonempty {i : ι // (deg i : ℤ) = r ∧ -(2 * (r : ℂ)) = -(2 * (cl i : ℂ))} :=
        ⟨⟨i₀, by rw [hdeg], by rw [hcl]⟩⟩
      exact Nat.one_le_iff_ne_zero.mpr (Nat.card_pos.ne')
    · have hbot : sing ρ Mdeg d c = ⊥ := by
        rw [eq_bot_iff]
        intro s hs
        rw [Submodule.mem_bot]
        by_contra hs0
        obtain ⟨h1, h2, -⟩ := sing_cyclic R w cyc supp charge bound hs hs0
        exact hdc ⟨h1, h2⟩
      rw [hbot, finrank_bot]
      exact Nat.zero_le _
  transverse d N := by
    rw [Submodule.disjoint_def]
    intro s hs hav
    by_contra hs0
    obtain ⟨rfl, hN, hws⟩ := sing_cyclic R w cyc supp charge bound hs hs0
    have hN' : N = r := by
      have : (N : ℂ) = r := by linear_combination -hN / 2
      exact_mod_cast this
    subst hN'
    apply hws
    have hle : avoid ρ Mdeg Cart (N : ℤ) N ≤ LinearMap.ker w := by
      refine sup_le (sup_le (fun m hm => cart m hm) ?_) ?_
      · refine iSup_le fun d' => iSup_le fun hd' => fun m hm => supp d' hd' m hm
      · rintro _ ⟨m, rfl⟩
        rw [LinearMap.mem_ker]
        have h1 := LinearMap.congr_fun charge m
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h1
        simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add,
          map_smul, h1, smul_eq_mul]
        ring
    exact hle hav

/-! ### Transfer along injective intertwiners -/

variable {M' : Type*} [AddCommGroup M'] [Module ℂ M']
variable {ρ' : Fin 3 × ℕ → Module.End ℂ M'} {Mdeg' : ℤ → Submodule ℂ M'}
variable {Cart' : ℕ → Submodule ℂ M'}

theorem map_sing (f : M →ₗ[ℂ] M') (hf : ∀ k, f ∘ₗ ρ k = ρ' k ∘ₗ f)
    (hdeg : ∀ d, ∀ m ∈ Mdeg d, f m ∈ Mdeg' d) {d : ℤ} {c : ℂ} {s : M}
    (hs : s ∈ sing ρ Mdeg d c) : f s ∈ sing ρ' Mdeg' d c := by
  have e : ∀ k m, f (ρ k m) = ρ' k (f m) := fun k m => LinearMap.congr_fun (hf k) m
  obtain ⟨h1, h2, h3, h4⟩ := hs
  exact ⟨hdeg d s h1, fun a j => by rw [← e, h2, map_zero], by rw [← e, h3, map_zero],
    by rw [← e, h4, map_smul]⟩

theorem map_avoid (f : M →ₗ[ℂ] M') (hf : ∀ k, f ∘ₗ ρ k = ρ' k ∘ₗ f)
    (hdeg : ∀ d, ∀ m ∈ Mdeg d, f m ∈ Mdeg' d) (hCart : ∀ N, ∀ m ∈ Cart N, f m ∈ Cart' N)
    (d : ℤ) (N : ℕ) : ∀ m ∈ avoid ρ Mdeg Cart d N, f m ∈ avoid ρ' Mdeg' Cart' d N := by
  intro m hm
  have hle : avoid ρ Mdeg Cart d N ≤ (avoid ρ' Mdeg' Cart' d N).comap f := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (hCart N x hx))
    · refine iSup_le fun d' => iSup_le fun hd' => fun x hx => ?_
      exact Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.mem_iSup_of_mem d' (Submodule.mem_iSup_of_mem hd' (hdeg d' x hx))))
    · rintro _ ⟨x, rfl⟩
      refine Submodule.mem_sup_right ⟨f x, ?_⟩
      have e := LinearMap.congr_fun (hf (2, 0)) x
      simp only [LinearMap.comp_apply] at e
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add,
        map_smul, e]
  exact hle hm

omit [Finite ι] in
/-- **Socle data pull back along injective, grading-preserving intertwiners** that map the
Cartan pieces into the Cartan pieces. -/
theorem SocleSpectrum.comap (S : SocleSpectrum ρ' Mdeg' deg cl Cart')
    (hfin : ∀ d, FiniteDimensional ℂ (Mdeg' d)) (f : M →ₗ[ℂ] M') (hinj : Function.Injective f)
    (hf : ∀ k, f ∘ₗ ρ k = ρ' k ∘ₗ f) (hdeg : ∀ d, ∀ m ∈ Mdeg d, f m ∈ Mdeg' d)
    (hCart : ∀ N, ∀ m ∈ Cart N, f m ∈ Cart' N) : SocleSpectrum ρ Mdeg deg cl Cart where
  rank_le d c := by
    haveI := hfin d
    haveI : FiniteDimensional ℂ (sing ρ' Mdeg' d c) :=
      Submodule.finiteDimensional_of_le (fun s hs => hs.1)
    let g : sing ρ Mdeg d c →ₗ[ℂ] sing ρ' Mdeg' d c :=
      (f.comp (sing ρ Mdeg d c).subtype).codRestrict _ fun s => map_sing f hf hdeg s.2
    have hg : Function.Injective g := fun a b h =>
      Subtype.ext (hinj (congrArg Subtype.val h))
    exact (LinearMap.finrank_le_finrank_of_injective hg).trans (S.rank_le d c)
  transverse d N := by
    rw [Submodule.disjoint_def]
    intro s hs hav
    apply hinj
    rw [map_zero]
    exact (Submodule.disjoint_def.mp (S.transverse d N)) _ (map_sing f hf hdeg hs)
      (map_avoid f hf hdeg hCart d N s hav)

end

end VOA.SocleDual
