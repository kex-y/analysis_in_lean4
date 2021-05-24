import Analysis.Logic 
import Analysis.Prelude

def Set (α : Type u) := α → Prop

def setOf (p : α → Prop) : Set α := p

namespace Set

/-! ## Basic Definitions -/

instance : EmptyCollection (Set α) := ⟨λ x => False⟩ 

variable {α : Type u} {s : Set α}

def mem (a : α) (s : Set α) := s a

instance : Mem α (Set α) := ⟨mem⟩

-- We note that the reverse direction is a bit more subtle and requires 
-- the definition of images
instance [Coe β α] : Coe (Set α) (Set β) := ⟨λ S => λ x => (x : α) ∈ S⟩

instance : CoeSort (Set α) (Type u) where 
  coe s := Subtype s

theorem ext {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := 
  funext <| λ x => propext <| h x

-- Declaring the index category
declare_syntax_cat index
syntax ident : index
syntax ident ":" term : index 
syntax ident "∈" term : index

-- Notation for sets
syntax "{" index "|" term "}" : term

macro_rules 
| `({ $x:ident : $t | $p }) => `(setOf (λ ($x:ident : $t) => $p))
| `({ $x:ident | $p }) => `(setOf (λ ($x:ident) => $p))
| `({ $x:ident ∈ $s | $p }) => `(setOf (λ $x => $x ∈ $s ∧ $p))

def union (s t : Set α) : Set α := { x : α | x ∈ s ∨ x ∈ t } 

def inter (s t : Set α) : Set α := { x : α | x ∈ s ∧ x ∈ t }

theorem unionDef (s t : Set α) : union s t = λ x => s x ∨ t x := rfl

theorem interDef (s t : Set α) : inter s t = λ x => s x ∧ t x := rfl

infix:60 " ∪ " => Set.union
infix:60 " ∩ " => Set.inter

def Union [h : Coe β (Set α)] (s : Set β) : Set α := 
  { x : α | ∃ t : β, t ∈ s ∧ (t : Set α) x }

def Inter [h : Coe β (Set α)] (s : Set β) : Set α := 
  { x : α | ∀ t : β, t ∈ s → (t : Set α) x }

def UnionDef [h : Coe β (Set α)] (s : Set β) : Union s = 
  λ x => ∃ t : β, t ∈ s ∧ (t : Set α) x := rfl

def InterDef [h : Coe β (Set α)] (s : Set β) : Inter s = 
  λ x => ∀ t : β, t ∈ s → (t : Set α) x := rfl

syntax " ⋃ " index "," term : term
syntax " ⋂ " index "," term : term

macro_rules
| `(⋃ $s:ident ∈ $c, $s) => `(Union $c)
| `(⋂ $s:ident ∈ $c, $s) => `(Inter $c)
| `(⋃ $s:ident ∈ $c, $coe $s) => `(Union {h := coe} $c)
| `(⋂ $s:ident ∈ $c, $coe $s) => `(Inion {h := coe} $c)

-- Notation for ∀ x ∈ s, p and ∃ x ∈ s, p
syntax " ∀ " index "," term : term
syntax " ∃ " index "," term : term

macro_rules
| `(∀ $x:ident ∈ $s, $p) => `(∀ $x:ident, $x ∈ $s → $p)
| `(∃ $x:ident ∈ $s, $p) => `(∃ $x:ident, $x ∈ $s ∧ $p)

def compl (s : Set α) := { x | x ∉ s }

postfix:100 "ᶜ " => compl

theorem compl.def (s : Set α) (x) : x ∈ sᶜ ↔ ¬ s x := Iff.rfl

def Subset (s t : Set α) := ∀ x ∈ s, x ∈ t

infix:50 " ⊆ " => Subset

theorem Subset.def {s t : Set α} : s ⊆ t ↔ ∀ x ∈ s, x ∈ t := Iff.rfl

namespace Subset

theorem refl {s : Set α} : s ⊆ s := λ _ hx => hx

theorem trans {s t v : Set α} (hst : s ⊆ t) (htv : t ⊆ v) : s ⊆ v := 
  λ x hx => htv _ (hst x hx)

theorem antisymm {s t : Set α} (hst : s ⊆ t) (hts : t ⊆ s) : s = t := 
  Set.ext λ x => ⟨ λ hx => hst x hx, λ hx => hts x hx ⟩

theorem antisymmIff {s t : Set α} : s = t ↔ s ⊆ t ∧ t ⊆ s :=
  ⟨ by { intro hst; subst hst; exact ⟨ refl, refl ⟩ }, 
    λ ⟨ hst, hts ⟩ => antisymm hst hts ⟩ 

-- ↓ Uses classical logic
theorem notSubset : ¬ s ⊆ t ↔ ∃ x ∈ s, x ∉ t := by 
  apply Iff.intro
  { intro hst; 
    rw Classical.Exists.notAnd;
    apply Classical.notForall;
    exact λ h => hst λ x hx => h x hx }
  { intro h hst;
    let ⟨ x, ⟨ hxs, hxt ⟩ ⟩ := h;
    exact hxt <| hst x hxs }

end Subset

/-! ## Easy Lemmas-/

theorem memEmptySet {x : α} (h : x ∈ (∅ : Set α)) : False := h

@[simp] theorem memEmptySetIff : (∃ (x : α), x ∈ (∅ : Set α)) ↔ False := 
  Iff.intro (λ h => h.2) False.elim 

@[simp] theorem setOfFalse : { a : α | False } = ∅ := rfl

def univ : Set α := { x | True }

@[simp] theorem memUniv (x : α) : x ∈ (univ : Set α) := True.intro

theorem Subset.empty (s : Set α) : ∅ ⊆ s := λ _ h => False.elim h

theorem Subset.subsetUniv {s : Set α} : s ⊆ univ := λ x _ => memUniv x 

theorem Subset.univSubsetIff {s : Set α} : univ ⊆ s ↔ univ = s := by
  apply Iff.intro λ hs => Subset.antisymm hs Subset.subsetUniv 
  { intro h; subst h; exact Subset.refl }

theorem eqUnivIff {s : Set α} : s = univ ↔ ∀ x, x ∈ s := by 
  apply Iff.intro 
  { intro h x; subst h; exact memUniv x }
  { exact λ h => ext λ x => Iff.intro (λ _ => memUniv _) λ _ => h x }

/-! ## Unions and Intersections -/

macro "extia" x:term : tactic => `(tactic| apply ext; intro $x; apply Iff.intro)

theorem unionSelf {s : Set α} : s ∪ s = s := by 
  extia x
  { intro hx; cases hx; assumption; assumption }
  { exact Or.inl }

theorem interSelf {s : Set α} : s ∩ s = s := by 
  extia x
  { intro h; exact h.1 }
  { intro h; exact ⟨ h, h ⟩}

theorem unionEmpty {s : Set α} : s ∪ ∅ = s := by 
  extia x
  { intro hx; cases hx with 
    | inl   => assumption
    | inr h => exact False.elim <| memEmptySet h }
  { exact Or.inl }

theorem unionSymm {s t : Set α} : s ∪ t = t ∪ s := by 
  extia x 
  allGoals { intro hx; cases hx with 
             | inl hx => exact Or.inr hx
             | inr hx => exact Or.inl hx }

theorem emptyUnion {s : Set α} : ∅ ∪ s = s := by 
  rw unionSymm; exact unionEmpty

theorem unionAssoc {s t w : Set α} : s ∪ t ∪ w = s ∪ (t ∪ w) := by 
  extia x
  { intro hx; cases hx with 
    | inr hx   => exact Or.inr <| Or.inr hx
    | inl hx   => cases hx with 
      | inr hx => exact Or.inr <| Or.inl hx
      | inl hx => exact Or.inl hx }
  { intro hx; cases hx with 
    | inl hx   => exact Or.inl <| Or.inl hx
    | inr hx   => cases hx with 
      | inr hx => exact Or.inr hx
      | inl hx => exact Or.inl <| Or.inr hx }

theorem subsetInter {s t u : Set α} (ht : s ⊆ t) (hu : s ⊆ u) : s ⊆ t ∩ u := 
λ x hx => ⟨ ht x hx, hu x hx ⟩

end Set