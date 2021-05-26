import Analysis.Filter

/-- A topological space on `α` is predicate `is_open` on `Set α` such that 
  - the whole set is open;
  - the intersection of two open sets is open; 
  - and the union of a collection of open sets is open. -/
class topologicalSpace (α : Type u) where 
  is_open : Set α → Prop
  is_open_univ : is_open Set.univ
  is_open_inter : ∀ s t, is_open s → is_open t → is_open (s ∩ t)
  is_open_Union : ∀ (s : Set (Set α)) (hs : ∀ t ∈ s, is_open t), 
    is_open (⋃ t ∈ s, t)

-- Short hand so we don't need to write `topologicalSpace` all the time
def is_open [topologicalSpace α] (s : Set α) := topologicalSpace.is_open s 

def is_open_univ [topologicalSpace α] : is_open (Set.univ : Set α) := 
topologicalSpace.is_open_univ 

def is_open_inter [topologicalSpace α] {s t : Set α} 
  (hs : is_open s) (ht : is_open t) : is_open (s ∩ t) := 
topologicalSpace.is_open_inter s t hs ht 

def is_open_Union [topologicalSpace α] (s : Set (Set α)) 
  (hs : ∀ t ∈ s, is_open t) : is_open (⋃ t ∈ s, t : Set α) := 
topologicalSpace.is_open_Union s hs 

namespace topologicalSpace

open Set Filter

theorem ext (π τ : topologicalSpace α) (h : π.is_open = τ.is_open) : π = τ := by 
  cases π; cases τ; subst h; rfl

variable [topologicalSpace α]

set_option pp.all true

theorem is_openEmpty : is_open (∅ : Set α) := 
UnionEmpty ▸ is_open_Union ∅ (λ _ h => False.elim h)

class Hausdorff (α : Type u) [topologicalSpace α] where
  t2 : ∀ (x y : α) (hxy : x ≠ y), 
    ∃ u v : Set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ 

section Hausdorff

variable [Hausdorff α]

theorem t2 (x y : α) (hxy : x ≠ y) : 
  ∃ u v : Set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ := 
Hausdorff.t2 x y hxy

/-- A filter `F` on a Hausdorff space `X` has at most one limit -/
theorem tendstoUnique {x y : α} {F : Filter α} [H : neBot F] 
  (hx : F ⟶ x) (hy : F ⟶ y) : x = y := by
  apply Classical.byContradiction 
  intro h
  cases t2 x y h with | intro u huv =>
  cases huv      with | intro v huv =>
  let ⟨hu₁, ⟨hv₁, ⟨hu₂, ⟨hv₂, huv⟩⟩⟩⟩ := huv
  exact H.ne_bot <| (eqBotIff F).2 <| huv ▸ inter_sets _ 
    (preimageId u ▸ hx u ((memNeighbourhoodIff x u).2 hu₂)) 
    (preimageId v ▸ hy v ((memNeighbourhoodIff y v).2 hv₂))

/-- The filter generate by the union of two neighbourhoods. -/
def aux (x y : α) : Filter α := 
  generatedFrom ((𝓝 x) ∪ 𝓝 y)

theorem auxTendstoLeft (x y : α) : aux x y ⟶ x := by 
  rw [tendstoNeighberhoodIff]
  intro z hz
  apply leGeneratedFrom ((𝓝 x) ∪ 𝓝 y) z
  rw [memIff, memPrincipalIff] at hz
  exact Or.inl <| Filter.sets_of_superset _ (selfMemPrincipal _) hz

theorem auxTendstoRight (x y : α) : aux x y ⟶ y := by 
  rw [tendstoNeighberhoodIff]
  intro z hz
  apply leGeneratedFrom ((𝓝 x) ∪ 𝓝 y) z
  rw [memIff, memPrincipalIff] at hz
  exact Or.inr <| Filter.sets_of_superset _ (selfMemPrincipal _) hz

/-- A topological space is Hausdorff if all filter `F` has a unique limit. -/
def HausdorffOfTendstoUnique 
  (hF : ∀ (F : Filter α) x y (hy : F ⟶ y) (hx : F ⟶ x), x = y) : 
  Hausdorff α := 
{ t2 := λ x y hxy => False.elim <| hxy <| 
  hF (aux x y) x y (auxTendstoRight x y) (auxTendstoLeft x y) }

end Hausdorff

end topologicalSpace