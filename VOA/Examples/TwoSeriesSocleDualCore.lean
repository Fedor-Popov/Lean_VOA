/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.CyclicEvalCore

/-!
# Socle duals from socle data: the abstract construction

Let `M` be a module with an action `ρ` of the nonnegative current modes `J^a_j`
(`a ∈ {e, f, h} = {0, 1, 2}`, `j ≥ 0`) and a conformal grading `Mdeg` that is bounded below,
finite-dimensional in each degree, exhausts `M`, and is shifted by `J^a_j` by `-j`; assume
`[h₀, f₀] = -2 f₀`.  Call a vector **singular of degree `d` and charge `c`** if it lies in
degree `d`, is killed by all positive modes `J^a_{j+1}` and by `f₀`, and has `h₀`-eigenvalue
`c` (`sing ρ Mdeg d c`, the lowest-weight `𝔤[t]`-singular vectors).

* `exists_sing_of_ne` — every nonzero homogeneous vector of a mode-stable subspace produces a
  nonzero singular vector in that subspace (minimal degree, then an `h₀`-eigenvector pushed
  down by `f₀` until it dies, using finiteness of the spectrum of `h₀`).
* `exists_socleDuals` — **socle data ⇒ socle duals.**  Given a finite family of labels with
  degrees `deg i` and cluster numbers `cl i`, and subspaces `Cart N` (in the application: the
  image of the Cartan ideal `I_N`), suppose
  1. (`SocleSpectrum.rank_le`) the singular vectors of degree `d` and charge `c` have dimension
     at most the number of labels with `deg i = d` and `c = -2·cl i`;
  2. (`SocleSpectrum.transverse`) the singular vectors of degree `d` and charge `-2N` meet
     `Cart N + (other degrees) + range(h₀ + 2N)` only in `0`.
  Then there are functionals `w i` that are jointly cyclic under mode words, supported in
  degree `deg i`, of charge `-2·cl i` under `h₀`, and vanishing on `Cart (cl i)`.

Everything here is proved outright, for an arbitrary module; nothing about `L_k(sl₂)` is used.
-/

namespace VOA.SocleDual

open Module VOA.CyclicEval
open scoped BigOperators

noncomputable section

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (ρ : Fin 3 × ℕ → Module.End ℂ M) (Mdeg : ℤ → Submodule ℂ M)

/-- The lowest-weight `𝔤[t]`-singular vectors of degree `d` and `h₀`-charge `c`:
`s ∈ M_d`, `J^a_{j+1} s = 0` for all `a, j`, `f₀ s = 0`, `h₀ s = c s`. -/
def sing (d : ℤ) (c : ℂ) : Submodule ℂ M where
  carrier := {s | s ∈ Mdeg d ∧ (∀ a j, ρ (a, j + 1) s = 0) ∧ ρ (1, 0) s = 0 ∧
    ρ (2, 0) s = c • s}
  add_mem' {x y} hx hy := ⟨add_mem hx.1 hy.1, fun a j => by rw [map_add, hx.2.1, hy.2.1, add_zero],
    by rw [map_add, hx.2.2.1, hy.2.2.1, add_zero], by rw [map_add, hx.2.2.2, hy.2.2.2, smul_add]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => map_zero _, map_zero _, by rw [map_zero, smul_zero]⟩
  smul_mem' t x hx := ⟨Submodule.smul_mem _ t hx.1, fun a j => by rw [map_smul, hx.2.1, smul_zero],
    by rw [map_smul, hx.2.2.1, smul_zero], by rw [map_smul, hx.2.2.2, smul_comm]⟩

theorem mem_sing {d : ℤ} {c : ℂ} {s : M} :
    s ∈ sing ρ Mdeg d c ↔ s ∈ Mdeg d ∧ (∀ a j, ρ (a, j + 1) s = 0) ∧ ρ (1, 0) s = 0 ∧
      ρ (2, 0) s = c • s := Iff.rfl

/-- The grading hypotheses on a mode module. -/
structure ModeGrading : Prop where
  span : ⨆ d, Mdeg d = ⊤
  neg : ∀ d : ℤ, d < 0 → Mdeg d = ⊥
  fin : ∀ d, FiniteDimensional ℂ (Mdeg d)
  deg : ∀ (k : Fin 3 × ℕ) (d : ℤ), ∀ m ∈ Mdeg d, ρ k m ∈ Mdeg (d - (k.2 : ℤ))
  hf : ρ (2, 0) * ρ (1, 0) - ρ (1, 0) * ρ (2, 0) = (-2 : ℂ) • ρ (1, 0)

variable {ρ Mdeg}

/-- The total mode weight of a word. -/
def wordWt (l : List (Fin 3 × ℕ)) : ℤ := (l.map fun k => (k.2 : ℤ)).sum

theorem word_cons_apply (k : Fin 3 × ℕ) (l : List (Fin 3 × ℕ)) (m : M) :
    word ρ (k :: l) m = ρ k (word ρ l m) := by
  simp [word, Module.End.mul_apply]

theorem word_append_apply (l : List (Fin 3 × ℕ)) (k : Fin 3 × ℕ) (m : M) :
    word ρ (l ++ [k]) m = word ρ l (ρ k m) := by
  simp [word, List.prod_append, Module.End.mul_apply]

theorem word_mem (G : ModeGrading ρ Mdeg) :
    ∀ (l : List (Fin 3 × ℕ)) (d : ℤ), ∀ m ∈ Mdeg d, word ρ l m ∈ Mdeg (d - wordWt l)
  | [], d, m, hm => by simpa [word, wordWt] using hm
  | k :: l, d, m, hm => by
    rw [word_cons_apply]
    have h := G.deg k _ _ (word_mem G l d m hm)
    have he : d - wordWt l - (k.2 : ℤ) = d - wordWt (k :: l) := by
      simp only [wordWt, List.map_cons, List.sum_cons]; ring
    rwa [he] at h

/-- A vector in the span of the graded pieces is a finite sum of homogeneous pieces. -/
theorem exists_decomp {x : M} (hx : x ∈ ⨆ d, Mdeg d) :
    ∃ (s : Finset ℤ) (f : ℤ → M), (∀ d, f d ∈ Mdeg d) ∧ (∀ d ∉ s, f d = 0) ∧
      x = ∑ d ∈ s, f d := by
  classical
  refine Submodule.iSup_induction Mdeg (motive := fun x => ∃ (s : Finset ℤ) (f : ℤ → M),
    (∀ d, f d ∈ Mdeg d) ∧ (∀ d ∉ s, f d = 0) ∧ x = ∑ d ∈ s, f d) hx ?_ ?_ ?_
  · intro d y hy
    refine ⟨{d}, fun d' => if d' = d then y else 0, fun d' => ?_, fun d' hd' => ?_, by simp⟩
    · beta_reduce
      split_ifs with h
      · subst h; exact hy
      · exact zero_mem _
    · rw [Finset.mem_singleton] at hd'; simp [hd']
  · exact ⟨∅, 0, fun _ => zero_mem _, fun _ _ => rfl, by simp⟩
  · intro x y hx hy
    obtain ⟨s, f, hf, hfs, rfl⟩ := hx
    obtain ⟨t, g, hg, hgt, rfl⟩ := hy
    refine ⟨s ∪ t, f + g, fun d => add_mem (hf d) (hg d), fun d hd => ?_, ?_⟩
    · rw [Finset.mem_union, not_or] at hd
      simp [hfs d hd.1, hgt d hd.2]
    · rw [Pi.add_def, Finset.sum_add_distrib,
        Finset.sum_subset Finset.subset_union_left (fun d _ hd => hfs d hd),
        Finset.sum_subset Finset.subset_union_right (fun d _ hd => hgt d hd)]

/-- **A nonzero homogeneous vector of a mode-stable subspace yields a nonzero singular
vector in it.** -/
theorem exists_sing_of_ne (G : ModeGrading ρ Mdeg) (K : Submodule ℂ M)
    (hK : ∀ k, ∀ m ∈ K, ρ k m ∈ K) (h : ∃ d, ∃ m ∈ K ⊓ Mdeg d, m ≠ 0) :
    ∃ d c, ∃ s ∈ K ⊓ sing ρ Mdeg d c, s ≠ 0 := by
  classical
  have hex : ∃ n : ℕ, ∃ m ∈ K ⊓ Mdeg (n : ℤ), m ≠ 0 := by
    obtain ⟨d, m, hm, hm0⟩ := h
    have hd : 0 ≤ d := by
      by_contra hd
      push Not at hd
      have h2 : m ∈ Mdeg d := (Submodule.mem_inf.mp hm).2
      rw [G.neg d hd, Submodule.mem_bot] at h2
      exact hm0 h2
    exact ⟨d.toNat, m, by rwa [Int.toNat_of_nonneg hd], hm0⟩
  obtain ⟨n, ⟨m, hm, hm0⟩, hmin⟩ : ∃ n : ℕ, (∃ m ∈ K ⊓ Mdeg (n : ℤ), m ≠ 0) ∧
      ∀ n' < n, ¬ ∃ m ∈ K ⊓ Mdeg (n' : ℤ), m ≠ 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun n' h => Nat.find_min hex h⟩
  set V := K ⊓ Mdeg (n : ℤ) with hVdef
  -- positive modes kill `V`, by minimality of `n`
  have hpos : ∀ v ∈ V, ∀ a j, ρ (a, j + 1) v = 0 := by
    intro v hv a j
    have hmem : ρ (a, j + 1) v ∈ K ⊓ Mdeg ((n : ℤ) - ((j + 1 : ℕ) : ℤ)) :=
      ⟨hK _ v hv.1, G.deg (a, j + 1) n v hv.2⟩
    by_contra hne
    by_cases hlt : (n : ℤ) - ((j + 1 : ℕ) : ℤ) < 0
    · have h2 : ρ (a, j + 1) v ∈ Mdeg ((n : ℤ) - ((j + 1 : ℕ) : ℤ)) := hmem.2
      rw [G.neg _ hlt, Submodule.mem_bot] at h2
      exact hne h2
    · push Not at hlt
      have hjn : j + 1 ≤ n := by omega
      have hcast : ((n - (j + 1) : ℕ) : ℤ) = (n : ℤ) - ((j + 1 : ℕ) : ℤ) := by
        push_cast [hjn]; ring
      exact hmin (n - (j + 1)) (by omega) ⟨_, by rw [hcast]; exact hmem, hne⟩
  have hzero : ∀ a, ∀ v ∈ V, ρ (a, 0) v ∈ V := by
    intro a v hv
    refine ⟨hK _ v hv.1, ?_⟩
    have := G.deg (a, 0) n v hv.2
    simpa using this
  haveI : FiniteDimensional ℂ (Mdeg (n : ℤ)) := G.fin n
  haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_right
  haveI : Nontrivial V := ⟨⟨⟨m, hm⟩, 0, fun h => hm0 (congrArg Subtype.val h)⟩⟩
  let H : Module.End ℂ V := (ρ (2, 0)).restrict (hzero 2)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue H
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hHv : ρ (2, 0) (v : M) = c • (v : M) := by
    have := Module.End.mem_eigenspace_iff.mp hv.1
    exact congrArg Subtype.val this
  have hv0 : (v : M) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  -- the `f₀`-string
  let u : ℕ → M := fun j => (ρ (1, 0) ^ j) (v : M)
  have hu_succ : ∀ j, u (j + 1) = ρ (1, 0) (u j) := fun j => by
    simp only [u, pow_succ', Module.End.mul_apply]
  have hu_mem : ∀ j, u j ∈ V := by
    intro j
    induction j with
    | zero => simp [u]
    | succ j ih => rw [hu_succ]; exact hzero 1 _ ih
  have hcomm : ∀ x : M, ρ (2, 0) (ρ (1, 0) x) = ρ (1, 0) (ρ (2, 0) x) - (2 : ℂ) • ρ (1, 0) x := by
    intro x
    have := LinearMap.congr_fun G.hf x
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [← sub_eq_zero] at this ⊢
    rw [← this]; module
  have hu_eig : ∀ j : ℕ, ρ (2, 0) (u j) = (c - 2 * (j : ℂ)) • u j := by
    intro j
    induction j with
    | zero => simpa [u] using hHv
    | succ j ih =>
      rw [hu_succ, hcomm, ih, map_smul]; push_cast; module
  -- some `u j` vanishes, by finiteness of the spectrum of `H`
  have hdie : ∃ j, u j = 0 := by
    by_contra hall
    push Not at hall
    have hinf : Set.Infinite H.HasEigenvalue := by
      refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => c - 2 * (j : ℂ)) ?_ ?_
      · intro i j hij
        simp only [sub_right_inj, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false,
          Nat.cast_inj] at hij
        exact hij
      · intro j
        refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨u j, hu_mem j⟩) ⟨?_, ?_⟩
        · rw [Module.End.mem_eigenspace_iff]
          exact Subtype.ext (hu_eig j)
        · exact fun h => hall j (congrArg Subtype.val h)
    exact hinf (Module.End.finite_hasEigenvalue H)
  obtain ⟨j0, hj0, hj0min⟩ : ∃ j0, u j0 = 0 ∧ ∀ j < j0, u j ≠ 0 :=
    ⟨Nat.find hdie, Nat.find_spec hdie, fun j h => Nat.find_min hdie h⟩
  have hj0pos : j0 ≠ 0 := by
    rintro rfl; exact hv0 (by simpa [u] using hj0)
  obtain ⟨j, rfl⟩ : ∃ j, j0 = j + 1 := ⟨j0 - 1, by omega⟩
  refine ⟨n, c - 2 * (j : ℂ), u j, ⟨(hu_mem j).1, (hu_mem j).2, fun a i => hpos _ (hu_mem j) a i,
    by rw [← hu_succ]; exact hj0, hu_eig j⟩, hj0min j (by omega)⟩

/-! ### The construction -/

variable {ι : Type*} [Finite ι] (deg : ι → ℕ) (cl : ι → ℕ) (Cart : ℕ → Submodule ℂ M)

variable (ρ Mdeg) in
/-- The subspace on which the dual vector of slot `(d, N)` must vanish:
`Cart N + Σ_{d' ≠ d} M_{d'} + range (h₀ + 2N)`. -/
def avoid (d : ℤ) (N : ℕ) : Submodule ℂ M :=
  Cart N ⊔ (⨆ (d' : ℤ) (_ : d' ≠ d), Mdeg d') ⊔
    LinearMap.range (ρ (2, 0) + (2 * (N : ℂ)) • (1 : Module.End ℂ M))

variable (ρ Mdeg) in
/-- **Socle data** for a family of labels: the singular spaces are no bigger than the label
count, and the singular vectors of charge `-2N` are transversal to `avoid d N`. -/
structure SocleSpectrum : Prop where
  rank_le : ∀ (d : ℤ) (c : ℂ), finrank ℂ (sing ρ Mdeg d c) ≤
    Nat.card {i : ι // (deg i : ℤ) = d ∧ c = -(2 * (cl i : ℂ))}
  transverse : ∀ (d : ℤ) (N : ℕ),
    Disjoint (sing ρ Mdeg d (-(2 * (N : ℂ)))) (avoid ρ Mdeg Cart d N)

/-- A finite-dimensional space of dimension `≤ |J|` is separated by `J`-many functionals. -/
theorem exists_separating {S : Type*} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    {J : Type*} [Finite J] (h : finrank ℂ S ≤ Nat.card J) :
    ∃ ψ : J → Module.Dual ℂ S, ∀ s : S, (∀ j, ψ j s = 0) → s = 0 := by
  classical
  haveI := Fintype.ofFinite J
  rw [Nat.card_eq_fintype_card] at h
  let b := Module.finBasis ℂ S
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin (finrank ℂ S)) (β := J) (by simpa using h)
  refine ⟨fun j => if hj : ∃ t, e t = j then b.coord hj.choose else 0, fun s hs => ?_⟩
  rw [← b.forall_coord_eq_zero_iff]
  intro t
  have hex : ∃ t', e t' = e t := ⟨t, rfl⟩
  have : (if hj : ∃ t', e t' = e t then b.coord hj.choose else 0) s = 0 := hs (e t)
  rw [dif_pos hex] at this
  have hch : hex.choose = t := e.injective hex.choose_spec
  rwa [hch] at this

/-- **Socle data ⇒ jointly cyclic socle duals.** -/
theorem exists_socleDuals (G : ModeGrading ρ Mdeg)
    (S : SocleSpectrum ρ Mdeg deg cl Cart) :
    ∃ w : ι → Module.Dual ℂ M,
      (∀ m, (∀ i l, w i (word ρ l m) = 0) → m = 0) ∧
      (∀ i (d : ℤ), d ≠ (deg i : ℤ) → ∀ m ∈ Mdeg d, w i m = 0) ∧
      (∀ i, w i ∘ₗ ρ (2, 0) = (-(2 * (cl i : ℂ))) • w i) ∧
      (∀ i, ∀ m ∈ Cart (cl i), w i m = 0) := by
  classical
  let J : ℤ → ℕ → Type _ := fun d N => {i : ι // (deg i : ℤ) = d ∧ cl i = N}
  let Sg : ℤ → ℕ → Submodule ℂ M := fun d N => sing ρ Mdeg d (-(2 * (N : ℂ)))
  have hfin : ∀ d N, FiniteDimensional ℂ (Sg d N) := fun d N => by
    haveI := G.fin d
    exact Submodule.finiteDimensional_of_le (fun s hs => hs.1)
  have hsep : ∀ d N, ∃ ψ : J d N → Module.Dual ℂ (Sg d N),
      ∀ s : Sg d N, (∀ j, ψ j s = 0) → s = 0 := by
    intro d N
    haveI := hfin d N
    refine exists_separating ?_
    refine (S.rank_le d _).trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight ?_)))
    intro i
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have : (N : ℂ) = (cl i : ℂ) := by linear_combination -h2 / 2
      exact_mod_cast this.symm
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [h2]⟩
  have hext : ∀ d N, ∃ h : (M ⧸ avoid ρ Mdeg Cart d N) →ₗ[ℂ] Sg d N,
      h ∘ₗ ((avoid ρ Mdeg Cart d N).mkQ ∘ₗ (Sg d N).subtype) = LinearMap.id := by
    intro d N
    apply LinearMap.exists_leftInverse_of_injective
    rw [LinearMap.ker_eq_bot']
    intro s hs
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hs
    exact Subtype.ext ((Submodule.disjoint_def.mp (S.transverse d N)) _ s.2 hs)
  choose ψ hψ using hsep
  choose h hh using hext
  let w : ι → Module.Dual ℂ M := fun i =>
    ψ (deg i) (cl i) ⟨i, rfl, rfl⟩ ∘ₗ h (deg i) (cl i) ∘ₗ (avoid ρ Mdeg Cart (deg i) (cl i)).mkQ
  have hw_avoid : ∀ i, ∀ m ∈ avoid ρ Mdeg Cart (deg i) (cl i), w i m = 0 := by
    intro i m hm
    simp only [w, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).mpr hm, map_zero]
  have hw_sing : ∀ i (s : Sg (deg i) (cl i)), w i s = ψ (deg i) (cl i) ⟨i, rfl, rfl⟩ s := by
    intro i s
    have := LinearMap.congr_fun (hh (deg i) (cl i)) s
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this
    simp only [w, LinearMap.comp_apply]
    rw [this]
  have hsupp : ∀ i (d : ℤ), d ≠ (deg i : ℤ) → ∀ m ∈ Mdeg d, w i m = 0 := by
    intro i d hd m hm
    exact hw_avoid i m (Submodule.mem_sup_left (Submodule.mem_sup_right
      (Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hd hm))))
  refine ⟨w, ?_, hsupp, ?_, fun i m hm => hw_avoid i m
    (Submodule.mem_sup_left (Submodule.mem_sup_left hm))⟩
  · -- cyclicity
    intro m hm
    by_contra hm0
    let K : Submodule ℂ M := ⨅ (i : ι) (l : List (Fin 3 × ℕ)), LinearMap.ker (w i ∘ₗ word ρ l)
    have hmemK : ∀ x, x ∈ K ↔ ∀ i l, w i (word ρ l x) = 0 := by
      intro x; simp [K]
    have hK : ∀ k, ∀ x ∈ K, ρ k x ∈ K := by
      intro k x hx
      rw [hmemK] at hx ⊢
      intro i l
      rw [← word_append_apply]; exact hx i _
    have hhom : ∃ d, ∃ y ∈ K ⊓ Mdeg d, y ≠ 0 := by
      by_contra hno
      push Not at hno
      obtain ⟨s, f, hf, hfs, hdec⟩ := exists_decomp (Mdeg := Mdeg)
        (show m ∈ ⨆ d, Mdeg d by rw [G.span]; trivial)
      have hfK : ∀ d, f d ∈ K := by
        intro d
        rw [hmemK]
        intro i l
        by_cases hdl : d - wordWt l = (deg i : ℤ)
        · have h0 := hm i l
          rw [hdec, map_sum, map_sum] at h0
          rw [Finset.sum_eq_single d] at h0
          · exact h0
          · intro b _ hb
            exact hsupp i _ (by omega) _ (word_mem G l b _ (hf b))
          · intro hd
            rw [hfs d hd, map_zero, map_zero]
        · exact hsupp i _ hdl _ (word_mem G l d _ (hf d))
      apply hm0
      rw [hdec]
      exact Finset.sum_eq_zero fun d _ => hno d (f d) ⟨hfK d, hf d⟩
    obtain ⟨d, c, s, ⟨hsK, hsS⟩, hs0⟩ := exists_sing_of_ne G K hK hhom
    -- a label of this slot exists
    have hpos : 0 < Nat.card {i : ι // (deg i : ℤ) = d ∧ c = -(2 * (cl i : ℂ))} := by
      haveI := G.fin d
      haveI : FiniteDimensional ℂ (sing ρ Mdeg d c) :=
        Submodule.finiteDimensional_of_le (fun s hs => hs.1)
      have hne : sing ρ Mdeg d c ≠ ⊥ := fun hb => hs0 (by rw [hb] at hsS; exact hsS)
      have := Submodule.finrank_eq_zero.not.mpr hne
      exact lt_of_lt_of_le (Nat.pos_of_ne_zero this) (S.rank_le d c)
    obtain ⟨⟨i, hdi, hci⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    subst hdi hci
    have hsS' : s ∈ Sg (deg i) (cl i) := hsS
    obtain ⟨⟨i', hd', hN'⟩, hj⟩ : ∃ j, ψ (deg i) (cl i) j ⟨s, hsS'⟩ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hs0 (congrArg Subtype.val (hψ _ _ ⟨s, hsS'⟩ hall))
    have hdeg : deg i' = deg i := by exact_mod_cast hd'
    have key : w i' s ≠ 0 := by
      have hsS'' : s ∈ Sg (deg i') (cl i') := by rw [hdeg, hN']; exact hsS'
      rw [show s = ((⟨s, hsS''⟩ : Sg (deg i') (cl i')) : M) from rfl, hw_sing]
      revert hj hsS''
      generalize hD : deg i = D at *
      generalize hC : cl i = C at *
      subst hdeg hN'
      intro hj _
      exact hj
    exact key (by simpa [word] using (hmemK s).mp hsK i' [])
  · intro i
    ext m
    have hr : (ρ (2, 0) + (2 * (cl i : ℂ)) • (1 : Module.End ℂ M)) m ∈
        avoid ρ Mdeg Cart (deg i) (cl i) :=
      Submodule.mem_sup_right (LinearMap.mem_range_self _ m)
    have h0 := hw_avoid i _ hr
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add,
      map_smul, smul_eq_mul] at h0
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination h0

end

end VOA.SocleDual
