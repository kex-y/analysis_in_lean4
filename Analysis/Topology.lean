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

namespace topologicalSpace

theorem ext (π τ : topologicalSpace α) (h : π.is_open = τ.is_open) : π = τ := by 
  cases π; cases τ; subst h; rfl

variable [topologicalSpace α]

-- theorem is_openEmpty : is_open (∅ : Set α) := 
--   is_open_Union ∅ 

end topologicalSpace