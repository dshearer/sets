import Sets.Classes

namespace Sets
open Classical
open Classes

/--***** Sets *****--/

-- There's one class in particular called "V"
axiom V : Class

-- V contains all the classes that can be members (and we call these "sets")
axiom all_classes_come_from_v : ∀ (a : Class), a ⊆ V

def Set : Type := { x : Class // x ∈ V }
instance : Coe Set Class := ⟨Subtype.val⟩

-- theorem members_are_sets {a b : Class} (a_in_b : a ∈ b) : a ∈ V :=
--   have b_is_subclass_of_v := all_classes_come_from_v b
--   b_is_subclass_of_v a a_in_b

/--
P₁: Separation. This is an informal meta-axiom. It says that you can add any axiom of this form:

  ∀ A₁ ... Aₙ, ∃ B, ∀ x, x ∈ V → (x ∈ B ↔ φ(A₁, ..., Aₙ, x))

We'll prefix our instances of P₁ with "P₁_". We usually do this with two axioms: one to name the
class (B), and one to describe it (φ).

The Separation principle plus all_classes_come_from_v is how we avoid Russel's paradox: all members (sets)
are classes, but only certain classes are members (sets).
--/

-- Theorem 1.1: Not all classes are sets

protected axiom P₂_Ordinary : Class
protected axiom P₂_Ordinary_φ : ∀ (x : Set), x ∈ P₂_Ordinary ↔ x ∉ x

theorem T_1_1 : ∃ a, a ∉ V :=
  have Ordinary_not_in_V :=
    byContradiction
      fun O_in_V =>
      have O_in_and_not_in_self := Sets.P₂_Ordinary_φ ⟨ Sets.P₂_Ordinary, (not_not.mp O_in_V) ⟩
      Or.elim (em (Sets.P₂_Ordinary ∈ Sets.P₂_Ordinary))
        (fun is_in =>
          have is_not_in := O_in_and_not_in_self.mp is_in
          absurd is_in is_not_in)
        (fun is_not_in =>
          have is_in := O_in_and_not_in_self.mpr is_not_in
          absurd is_not_in (not_not.mpr is_in))
  Exists.intro Sets.P₂_Ordinary Ordinary_not_in_V

-- Theorem 1.2: For any class A there is a subclass B of A s.t. B is not an element of A

protected axiom P₂_MakeOrdinary (a : Class) : ∃ b, ∀ x, x ∈ b ↔ (x ∈ a ∧ x ∉ x)

theorem T_1_2 : ∀ a, ∃ b, b ⊆ a ∧ b ∉ a :=
  fun a =>
  let ⟨ b, b_is_ord_subset_of_a ⟩ := (Sets.P₂_MakeOrdinary a)
  have b_sub_a : b ⊆ a :=
    fun (x) (x_in_b : x ∈ b) => ((b_is_ord_subset_of_a x).mp x_in_b).left
  have b_not_in_a : b ∉ a :=
    byContradiction
      fun b_in_a =>
      Or.elim (em (b ∈ b))
        (fun is_in =>
         have is_not_in := ((b_is_ord_subset_of_a b).mp is_in).right
         absurd is_in is_not_in)
        (fun is_not_in =>
         have is_in := (b_is_ord_subset_of_a b).mpr ⟨ (not_not.mp b_in_a), is_not_in ⟩
         absurd is_in is_not_in)
  Exists.intro b (And.intro b_sub_a b_not_in_a)

/--***** Transitivity and supercompleteness *****--/

def is_transitive (a : Class) : Prop := ∀ x y, x ∈ y ∧ y ∈ a → x ∈ a
def is_swelled (a : Class) : Prop := ∀ x y, x ⊆ y → y ∈ a → x ∈ a

axiom A₁ : is_transitive V
axiom A₂ : is_swelled V

theorem T_2_3 : V ∉ V :=
  byContradiction
    fun v_in_v =>
    have every_subset_in_v : ∀ x, x ⊆ V -> x ∈ V:=
      fun (x) (x_sub_v : x ⊆ V) => A₂ x V x_sub_v (not_not.mp v_in_v)
    let ⟨ b, b_not_in_v ⟩ := T_1_1
    have b_sub_v := all_classes_come_from_v b
    have b_in_v := every_subset_in_v b b_sub_v
    absurd b_in_v b_not_in_v

theorem all_members_are_sets {a b : Class} (h : a ∈ b) : a ∈ V := (all_classes_come_from_v b) a h

/--***** The empty set *****--/

axiom Null : Class
axiom Null_φ : ∀ x, x ∉ Null

-- NOTE: At this point, V may well be empty. A₃ changes that.

axiom A₃ : Null ∈ V

/--***** Pairing *****--/

axiom Pair (a b : Set) : Class
axiom Pair_φ (a b : Set) : ∀ (x : Class), x ∈ (Pair a b) ↔ x = a ∨ x = b

noncomputable abbrev Single (a : Set) := Pair a a

axiom A₄ (a b : Set) : Pair a b ∈ V

theorem C_4_1 (a : Set) : Pair a a ∈ V := A₄ a a

theorem pair_has_left (a b : Set) : a ∈ Pair a b :=
  have a_is_a_or_b : a.val = a.val ∨ a.val = b.val := Or.inl rfl
  (Pair_φ a b a).mpr a_is_a_or_b

theorem pair_has_right (a b : Set) : b ∈ Pair a b :=
  have b_is_a_or_b : b.val = a.val ∨ b.val = b.val := Or.inr rfl
  (Pair_φ a b b).mpr b_is_a_or_b

theorem in_single {x : Class} {y : Set} (h : x ∈ Single y) : x = y :=
  have poss := (Pair_φ y y x).mp h
  poss.elim (fun h => h) (fun h => h)

/--***** Union *****--/

axiom Yunion (a : Class) : Class
axiom Yunion_prop (a : Class) : ∀ x, x ∈ (Yunion a) ↔ ∃ y, y ∈ a ∧ x ∈ y

axiom A₅ : ∀ (x : Set), (Yunion x) ∈ V

def is_non_empty (a : Class) : Prop := ∃ x, x ∈ a

protected axiom P₂_union (a b : Class) : Class
axiom P₂_union_φ (a b : Class) : ∀ x, x ∈ (Sets.P₂_union a b) ↔ (x ∈ a ∨ x ∈ b)
infix:60 " U " => Sets.P₂_union

theorem union_sub_left (a : Class) { b : Class }: a ⊆ a U b :=
  fun x =>
  fun x_in_a : x ∈ a =>
  have prop := P₂_union_φ a b x
  prop.mpr (Or.inl x_in_a)

theorem union_sub_right (b : Class) { a : Class }: b ⊆ a U b :=
  fun x =>
  fun x_in_b : x ∈ b =>
  have prop := P₂_union_φ a b x
  prop.mpr (Or.inr x_in_b)

theorem union_pair_sub_union {x y} : Yunion (Pair x y) ⊆ x U y :=
  fun z =>
  fun (h : z ∈ Yunion (Pair x y)) =>
  have z_in_k : ∃ k, k ∈ Pair x y ∧ z ∈ k := (Yunion_prop (Pair x y) z).mp h
  let ⟨ k, hk ⟩ := z_in_k
  have k_in_v : k ∈ V := all_members_are_sets hk.left
  have k_is_x_or_y : k = x ∨ k = y := (Pair_φ x y k ).mp hk.left
  have z_in_x_or_y : z ∈ x ∨ z ∈ y :=
    Or.elim k_is_x_or_y
    (fun k_is_x =>
      have z_in_x : z ∈ x := by rw [←k_is_x]; exact hk.right
      Or.intro_left (z ∈ y) z_in_x)
    (fun k_is_y =>
      have z_in_y : z ∈ y := by rw [←k_is_y]; exact hk.right
      Or.intro_right (z ∈ x) z_in_y)
  (P₂_union_φ x y z).mpr z_in_x_or_y

theorem union_sub_union_pair {x y : Set} : x U y ⊆ Yunion (Pair x y) :=
  fun z =>
  fun (h : z ∈ x U y) =>
  have z_in_x_or_y : z ∈ x ∨ z ∈ y := (P₂_union_φ x y z).mp h
  have exists_k : ∃ k, k ∈ (Pair x y) ∧ z ∈ k :=
    z_in_x_or_y.elim
    (fun z_in_x =>
      have x_in_pair : x ∈ Pair x y := pair_has_left x y
      Exists.intro x ⟨ x_in_pair, z_in_x ⟩)
    (fun z_in_y =>
      have y_in_pair : y ∈ Pair x y := pair_has_right x y
      Exists.intro y ⟨ y_in_pair, z_in_y ⟩)
  (Yunion_prop (Pair x y) z).mpr exists_k

theorem union_of_sets_is_set {x y : Set} : x U y ∈ V :=
  have union_pair_is_set : Yunion (Pair x y) ∈ V := A₅ ⟨ (Pair x y), A₄ x y ⟩
  have union_equals_union_pair := equality_sub ⟨ union_sub_union_pair, union_pair_sub_union ⟩
  by rw [union_equals_union_pair]; assumption

-- Intersection

axiom Intersect (a : Class) : Class
axiom Intersect_φ (a : Class) : ∀ x, x ∈ (Intersect a) ↔ ∀ y, y ∈ a → x ∈ y

-- Theorem 5.1 part 1: For any non-empty class A, Intersect A is a set.

theorem T5_1_1 : ∀ a, is_non_empty a → (Intersect a) ∈ V :=
  fun a =>
  fun a_is_non_empty : is_non_empty a =>
  let ⟨ x, x_in_a ⟩ := a_is_non_empty
  have x_in_v : x ∈ V := all_classes_come_from_v a x x_in_a
  have intersect_a_sub_x : (Intersect a) ⊆ x :=
    fun (y : Class) (y_in_intersect_a : y ∈ (Intersect a)) =>
    (Intersect_φ a y).mp y_in_intersect_a x x_in_a
  A₂ (Intersect a) x intersect_a_sub_x x_in_v

/--***** Power *****--/

axiom 𝒫 (a : Set) : Class
axiom 𝒫_φ (a : Set): ∀ x, x ∈ (𝒫 a) ↔ x ⊆ a

axiom A₆ : ∀ (x : Set), (𝒫 x) ∈ V

end Sets
