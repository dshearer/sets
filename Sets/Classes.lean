namespace Classes

/--***** Classes *****--/

-- There are things called "classes"
axiom Class : Type

/--***** Membership *****--/

-- Classes have a "membership" relation with each other
protected axiom mem : Class -> Class -> Prop
infix:50 " ∈ " => Classes.mem

protected def nmem (a b : Class) : Prop := ¬(a ∈ b)
infix:50 " ∉ " => Classes.nmem

-- Membership determines the identity of a class -- a class is nothing more than its members
axiom P₁ : ∀ a b, (∀ x, x ∈ a ↔ x ∈ b) → a = b

protected def subclass (a b : Class) : Prop := ∀ x, x ∈ a -> x ∈ b
infix:50 " ⊆ " => Classes.subclass

protected theorem equality_sub_1 {a b} : (a ⊆ b ∧ b ⊆ a) → a = b :=
  fun h => P₁ a b (fun x => ⟨ h.left x, h.right x ⟩)

protected theorem equality_sub_2 {a b} : a = b → (a ⊆ b ∧ b ⊆ a) :=
  fun h => ⟨ fun _ x_in_a => h ▸ x_in_a, fun _ x_in_b => h ▸ x_in_b ⟩

theorem equality_sub {a b} : a = b ↔ (a ⊆ b ∧ b ⊆ a) :=
  Iff.intro Classes.equality_sub_2 Classes.equality_sub_1

theorem subclass_is_transitive {a b c} (a_sub_b : a ⊆ b) (b_sub_c : b ⊆ c) : a ⊆ c :=
  fun x => fun x_in_a =>
  have x_in_b : x ∈ b := a_sub_b x x_in_a
  b_sub_c x x_in_b

theorem subclass_is_reflexive {a} : a ⊆ a := fun _ => fun x_in_a => x_in_a

end Classes
