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
  fun h =>
  have cond : ∀ x, x ∈ a ↔ x ∈ b :=
    fun x =>
    have a_then_b : x ∈ a → x ∈ b := h.left x
    have b_then_a : x ∈ b → x ∈ a := h.right x
    Iff.intro a_then_b b_then_a
  P₁ a b cond

protected theorem equality_sub_2 {a b} : a = b → (a ⊆ b ∧ b ⊆ a) :=
  fun h =>
  have a_sub_b : a ⊆ b := fun _ => fun x_in_a => h ▸ x_in_a
  have b_sub_a : b ⊆ a := fun _ => fun x_in_a => h ▸ x_in_a
  ⟨ a_sub_b, b_sub_a ⟩

theorem equality_sub {a b} : a = b ↔ (a ⊆ b ∧ b ⊆ a) :=
  Iff.intro Classes.equality_sub_2 Classes.equality_sub_1

end Classes
