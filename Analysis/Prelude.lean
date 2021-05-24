class Mem (α : outParam $ Type u) (γ : Type v) where
  mem : α → γ → Prop

infix:55 " ∈ " => Mem.mem
notation:55 x " ∉ " s => ¬ x ∈ s

instance : Coe α α := ⟨id⟩