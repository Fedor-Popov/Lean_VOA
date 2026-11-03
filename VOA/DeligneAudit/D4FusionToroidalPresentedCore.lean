import VOA.DeligneAudit.D4FusionToroidalGarlandSymbol

/-! The free word space and syntactic toroidal relations. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ} {m : ℕ}

/-- Formal linear combinations of toroidal words. -/
abbrev FreeT (n : ℕ) := List (TLtr n) →₀ ℂ

def swT (l : List (TLtr n)) : FreeT n := Finsupp.single l 1

def consT (x : TLtr n) : FreeT n →ₗ[ℂ] FreeT n :=
  Finsupp.lmapDomain ℂ ℂ (List.cons x)

theorem consT_swT (x : TLtr n) (l : List (TLtr n)) :
    consT x (swT l) = swT (x :: l) := by
  simp [consT, swT, Finsupp.mapDomain_single]

/-- Prefix a formal word combination by a fixed list. -/
def prefixT : List (TLtr n) → FreeT n →ₗ[ℂ] FreeT n
  | [] => LinearMap.id
  | x :: p => (consT x).comp (prefixT p)

theorem prefixT_swT (p l : List (TLtr n)) :
    prefixT p (swT l) = swT (p ++ l) := by
  induction p with
  | nil => rfl
  | cons x p ih => simp [prefixT, ih, consT_swT]

def commBaseT (s : List (TLtr n)) (x y : TLtr n) : FreeT n :=
  swT (x :: y :: s) - swT (y :: x :: s) -
    (if x.2.2 + y.2.2 < m then
      ∑ e, f x.1 y.1 e • swT ((e, x.2.1 + y.2.1, x.2.2 + y.2.2) :: s)
    else 0)

def highBaseT (s : List (TLtr n)) (x : TLtr n) : FreeT n := swT (x :: s)

/-- The Garland polynomial as a formal combination of words. -/
def gpowSyntax (c₀ : Fin n) : ℕ → ℕ → FreeT n
  | 0, s => if s = 0 then swT [] else 0
  | j + 1, s => ∑ p ∈ Finset.antidiagonal s,
      consT (c₀, 1, p.1) (gpowSyntax c₀ j p.2)

def psymSyntax (c₀ : Fin n) (j N : ℕ) : FreeT n :=
  ∑ p ∈ Finset.antidiagonal N, consT (c₀, 0, p.1) (gpowSyntax c₀ j p.2)

/-- The explicit word forms of the `Jprime` generator relations. -/
def JprimeSyntax (m : ℕ) : Set (FreeT 28) :=
  {z | (∃ t ∈ (ravFam D4sector m 0).tails,
      z = swT (symbolLetters m t)) ∨
    (∃ j N, 1 ≤ j ∧ j + 1 ≤ m ∧ m ≤ N + j ∧
      z = psymSyntax D4sector.c₀ j N)}

/-- Closure under all left words is built into the presentation. -/
def JTgen (f : Fin n → Fin n → Fin n → ℂ) (m : ℕ)
    (S : Set (FreeT n)) : Set (FreeT n) :=
  {z | ∃ p : List (TLtr n),
    (∃ s x y, z = prefixT p (commBaseT (f := f) (m := m) s x y)) ∨
    (∃ s x, m ≤ x.2.2 ∧ z = prefixT p (highBaseT s x)) ∨
    (∃ q ∈ S, z = prefixT p q)}

def JT (f : Fin n → Fin n → Fin n → ℂ) (m : ℕ)
    (S : Set (FreeT n)) : Submodule ℂ (FreeT n) :=
  Submodule.span ℂ (JTgen f m S)

theorem consT_prefixT (x : TLtr n) (p : List (TLtr n)) (z : FreeT n) :
    consT x (prefixT p z) = prefixT (x :: p) z := rfl

theorem consT_mem_JT (f : Fin n → Fin n → Fin n → ℂ) (m : ℕ)
    (S : Set (FreeT n)) (x : TLtr n) :
    JT f m S ≤ (JT f m S).comap (consT x) := by
  rw [JT, Submodule.span_le]
  rintro z ⟨p, ⟨s, a, b, rfl⟩ | ⟨s, a, ha, rfl⟩ | ⟨q, hq, rfl⟩⟩
  · exact Submodule.subset_span ⟨x :: p, Or.inl ⟨s, a, b, rfl⟩⟩
  · exact Submodule.subset_span ⟨x :: p, Or.inr (Or.inl ⟨s, a, ha, rfl⟩)⟩
  · exact Submodule.subset_span ⟨x :: p, Or.inr (Or.inr ⟨q, hq, rfl⟩)⟩

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def evalT (ρ : ToroidalModule f m V) (v : V) : FreeT n →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ (fun l => wordOpT ρ l v)

theorem evalT_swT (ρ : ToroidalModule f m V) (v : V)
    (l : List (TLtr n)) : evalT ρ v (swT l) = wordOpT ρ l v := by
  simp [evalT, swT]

theorem wordOpT_append (ρ : ToroidalModule f m V) (p s : List (TLtr n))
    (v : V) : wordOpT ρ (p ++ s) v = wordOpT ρ p (wordOpT ρ s v) := by
  induction p with
  | nil => rfl
  | cons x p ih => simp only [List.cons_append, wordOpT, ih]

theorem wordOpT_add (ρ : ToroidalModule f m V) (p : List (TLtr n))
    (v w : V) : wordOpT ρ p (v + w) = wordOpT ρ p v + wordOpT ρ p w := by
  induction p with
  | nil => rfl
  | cons x p ih => simp only [wordOpT, ih, map_add]

theorem wordOpT_smul (ρ : ToroidalModule f m V) (p : List (TLtr n))
    (a : ℂ) (v : V) : wordOpT ρ p (a • v) = a • wordOpT ρ p v := by
  induction p with
  | nil => rfl
  | cons x p ih => simp only [wordOpT, ih, map_smul]

theorem wordOpT_zero (ρ : ToroidalModule f m V) (p : List (TLtr n)) :
    wordOpT ρ p (0 : V) = 0 := by
  induction p with
  | nil => rfl
  | cons x p ih => simp only [wordOpT, ih, map_zero]

theorem wordOpT_sub (ρ : ToroidalModule f m V) (p : List (TLtr n))
    (v w : V) : wordOpT ρ p (v - w) = wordOpT ρ p v - wordOpT ρ p w := by
  induction p with
  | nil => rfl
  | cons x p ih => simp only [wordOpT, ih, map_sub]

theorem wordOpT_sum (ρ : ToroidalModule f m V) (p : List (TLtr n))
    {α : Type*} (t : Finset α) (g : α → V) :
    wordOpT ρ p (∑ a ∈ t, g a) = ∑ a ∈ t, wordOpT ρ p (g a) := by
  induction p with
  | nil => rfl
  | cons x p ih => simp only [wordOpT, ih, map_sum]

theorem evalT_consT (ρ : ToroidalModule f m V) (v : V)
    (x : TLtr n) (z : FreeT n) :
    evalT ρ v (consT x z) = ρ.op x.1 x.2.1 x.2.2 (evalT ρ v z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single l a =>
      have h : Finsupp.single l a = a • swT l := by simp [swT]
      simp only [h, map_smul, consT_swT, evalT_swT, wordOpT]

theorem evalT_prefixT (ρ : ToroidalModule f m V) (v : V)
    (p : List (TLtr n)) (z : FreeT n) :
    evalT ρ v (prefixT p z) = wordOpT ρ p (evalT ρ v z) := by
  induction p with
  | nil => rfl
  | cons x p ih => simp only [prefixT, LinearMap.comp_apply, evalT_consT, ih, wordOpT]

theorem evalT_gpowSyntax (ρ : ToroidalModule f m V) (v : V)
    (c₀ : Fin n) : ∀ j s,
    evalT ρ v (gpowSyntax c₀ j s) = gpow ρ c₀ j s v
  | 0, s => by
      simp only [gpowSyntax, gpow]
      split_ifs <;> simp [evalT_swT, wordOpT]
  | j + 1, s => by
      simp only [gpowSyntax, gpow, map_sum, evalT_consT]
      simp only [evalT_gpowSyntax ρ v c₀ j]

theorem evalT_psymSyntax (ρ : ToroidalModule f m V) (v : V)
    (c₀ : Fin n) (j N : ℕ) :
    evalT ρ v (psymSyntax c₀ j N) = Psym ρ c₀ j N v := by
  simp only [psymSyntax, Psym, map_sum, evalT_consT]
  simp only [evalT_gpowSyntax]

end

end VOA.DeligneAudit.Toroidal
