import Sets.Classes

namespace Sets
open Classical
open Classes

/--***** Sets *****--/

-- There's one class in particular called "V"
axiom V : Class

-- V contains all the classes that can be members (and we call these "sets")
axiom all_classes_come_from_v : ∀ (a : Class), a ⊆ V

class IsSet (a : Class) : Prop where
  in_v : a ∈ V

theorem all_members_are_sets {a b : Class} (h : a ∈ b) : a ∈ V := (all_classes_come_from_v b) a h

instance {a b} {h : a ∈ b} : IsSet a where
  in_v := all_members_are_sets h

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

axiom P₂ (p : (x : Class) → [IsSet x] → Prop) : ∃ B, ∀ {x} [IsSet x], (x ∈ B ↔ p x)

-- Theorem 1.1: Not all classes are sets

def is_ordinary (a : Class) [IsSet a]: Prop := a ∉ a

protected def Ordinary := P₂ is_ordinary

theorem T_1_1 : ∃ a, a ∉ V :=
  have Ordinary_not_in_V : Sets.Ordinary.choose ∉ V :=
    -- by contradiction
    fun Ordinary_in_v : Sets.Ordinary.choose ∈ V =>
    haveI : IsSet Sets.Ordinary.choose := ⟨Ordinary_in_v⟩
    Or.elim (em (Sets.Ordinary.choose ∈ Sets.Ordinary.choose))
      (fun is_in_self =>
        absurd is_in_self (Sets.Ordinary.choose_spec.mp is_in_self))
      (fun is_not_in_self =>
        have is_in_self : Sets.Ordinary.choose ∈ Sets.Ordinary.choose := Sets.Ordinary.choose_spec.mpr is_not_in_self
        absurd is_in_self is_not_in_self)
  Exists.intro Sets.Ordinary.choose Ordinary_not_in_V

protected def MakeOrdinary (a) := P₂ (fun x => x ∈ a ∧ is_ordinary x)

-- Theorem 1.2: For any class A there is a subclass B of A s.t. B is not an element of A

theorem T_1_2 : ∀ a, ∃ b, b ⊆ a ∧ b ∉ a :=
  fun a =>
  let ⟨ b, b_is_ord_subset_of_a ⟩ := (Sets.MakeOrdinary a)
  have b_sub_a : b ⊆ a :=
    fun (x) (x_in_b : x ∈ b) =>
      haveI : IsSet x := ⟨(all_classes_come_from_v b) x x_in_b⟩
      (b_is_ord_subset_of_a.mp x_in_b).left
  have b_not_in_a : b ∉ a := fun b_in_a =>
    haveI : IsSet b := ⟨(all_classes_come_from_v a) b b_in_a⟩
    Or.elim (em (b ∈ b))
      (fun is_in =>
        absurd is_in (b_is_ord_subset_of_a.mp is_in).right)
      (fun is_not_in =>
        have is_in := b_is_ord_subset_of_a.mpr ⟨ b_in_a, is_not_in ⟩
        absurd is_in is_not_in)
  Exists.intro b (And.intro b_sub_a b_not_in_a)

/--***** Transitivity and supercompleteness *****--/

def is_transitive (a : Class) : Prop := ∀ x y, x ∈ y ∧ y ∈ a → x ∈ a
def is_swelled (a : Class) : Prop := ∀ x y, x ⊆ y → y ∈ a → x ∈ a

axiom A₁ : is_transitive V
axiom A₂ : is_swelled V

theorem T_2_3 : V ∉ V :=
  fun v_in_v =>
  have every_subset_in_v : ∀ x, x ⊆ V -> x ∈ V:=
    fun (x) (x_sub_v : x ⊆ V) => A₂ x V x_sub_v v_in_v
  let ⟨ b, b_not_in_v ⟩ := T_1_1
  absurd (every_subset_in_v b (all_classes_come_from_v b)) b_not_in_v

theorem members_of_trans_are_subsets {a b : Class} (h1 : is_transitive b) (h2 : a ∈ b) : a ⊆ b :=
  fun x => fun x_in_a => h1 x a ⟨ x_in_a, h2 ⟩

/--***** The empty set *****--/

protected def Null_P₂ := P₂ (fun x => x ≠ x)

noncomputable def Null := Sets.Null_P₂.choose

-- NOTE: At this point, V may well be empty. A₃ changes that.

axiom A₃ : Null ∈ V

instance : IsSet Null where
  in_v := A₃

theorem null_empty : ∀ x, x ∉ Null :=
  fun x =>
  have x_is_or_is_not_set : IsSet x ∨ ¬ IsSet x := em (IsSet x)
  Or.elim x_is_or_is_not_set
    (fun _ => fun x_in_null : x ∈ Null => (Sets.Null_P₂.choose_spec.mp x_in_null) rfl)
    (fun x_is_not_set => fun x_in_null : x ∈ Null => x_is_not_set ⟨(all_classes_come_from_v Null) x x_in_null⟩)

theorem null_sub_everything (a) : Null ⊆ a := fun x => fun x_in_null => absurd x_in_null (null_empty x)

/--***** Pairing *****--/

protected def Pair_P₂ (a b) [IsSet a] [IsSet b] := P₂ (fun x => x = a ∨ x = b)

noncomputable def Pair (a b) [IsSet a] [IsSet b] : Class := (Sets.Pair_P₂ a b).choose

noncomputable def Pair_φ {a b} [IsSet a] [IsSet b] (x) [IsSet x] := (Sets.Pair_P₂ a b).choose_spec (x := x)

def is_pair (a : Class) : Prop := ∃ (x y : Class) (_ : IsSet x) (_ : IsSet y), a = Pair x y

class IsPair (a) where
  prop : is_pair a

instance (a b) [IsSet a] [IsSet b] : IsPair (Pair a b) where
  prop :=
    let p := Pair a b
    let eq : p = Pair a b := rfl
    ⟨a, b, inferInstance, inferInstance, eq⟩

noncomputable def Single (a : Class) [IsSet a] := Pair a a

axiom A₄ (a) [IsPair a] : a ∈ V

instance (a) [IsPair a] : IsSet (a) where
  in_v := A₄ a

theorem C_4_1 (a) [IsSet a] : Pair a a ∈ V := A₄ (Pair a a)

instance (a) [IsSet a] : IsSet (Single a) where
  in_v := C_4_1 a

theorem in_pair {a b x} [IsSet a] [IsSet b] [IsSet x] (h : x ∈ Pair a b) : x = a ∨ x = b :=
  (Pair_φ x).mp h

theorem pair_has_left (a b) [IsSet a] [IsSet b] : a ∈ Pair a b :=
  (Pair_φ a).mpr (Or.inl rfl)

theorem pair_has_right (a b) [IsSet a] [IsSet b] : b ∈ Pair a b :=
  (Pair_φ b).mpr (Or.inr rfl)

theorem in_own_single {x} [IsSet x] : x ∈ Single x :=
  pair_has_left x x

theorem in_single {x y : Class} [IsSet x] [IsSet y] (h : x ∈ Single y) : x = y :=
  (Pair_φ x).mp h |>.elim id id

theorem single_id {x y} [IsSet x] [IsSet y] (h : Single x = Single y) : x = y :=
  have x_in_own : x ∈ Single x := in_own_single
  have x_in_other : x ∈ Single y := h ▸ x_in_own
  in_single x_in_other

theorem single_pair_eq {x y z} [IsSet x] [IsSet y] [IsSet z] (h : Single x = Pair y z) : x = y ∧ x = z :=
  have y_in_pair : y ∈ Pair y z := pair_has_left y z
  have y_in_single : y ∈ Single x := h ▸ y_in_pair
  have y_eq_x : y = x := in_single y_in_single
  have z_in_pair : z ∈ Pair y z := pair_has_right y z
  have z_in_single : z ∈ Single x := h ▸ z_in_pair
  have z_eq_x : z = x := in_single z_in_single
  ⟨ eq_comm.mp y_eq_x, eq_comm.mp z_eq_x ⟩

/--***** Union *****--/

protected def Yunion_P₂ (a) := P₂ (fun x => ∃ y, y ∈ a ∧ x ∈ y)

noncomputable def Yunion (a) := (Sets.Yunion_P₂ a).choose

def Yunion_φ (a x) [IsSet x] := (Sets.Yunion_P₂ a).choose_spec (x := x)

axiom A₅ : ∀ (x) [IsSet x], (Yunion x) ∈ V

def is_non_empty (a : Class) : Prop := ∃ x, x ∈ a

protected def union_P₂ (a b) := P₂ (fun x => x ∈ a ∨ x ∈ b)

protected noncomputable def union (a b) := (Sets.union_P₂ a b).choose

def union_φ (a b x) [IsSet x] := (Sets.union_P₂ a b).choose_spec (x := x)

infix:60 " ∪ " => Sets.union

theorem union_sub_left (a : Class) { b : Class }: a ⊆ a ∪ b :=
  fun x =>
  fun x_in_a : x ∈ a =>
  haveI : IsSet x := ⟨(all_classes_come_from_v a) x x_in_a⟩
  have prop := (Sets.union_P₂ a b).choose_spec (x := x)
  prop.mpr (Or.inl x_in_a)

theorem union_sub_right (b : Class) { a : Class }: b ⊆ a ∪ b :=
  fun x =>
  fun x_in_b : x ∈ b =>
  haveI : IsSet x := ⟨(all_classes_come_from_v b) x x_in_b⟩
  have prop := (Sets.union_P₂ a b).choose_spec (x := x)
  prop.mpr (Or.inr x_in_b)

theorem yunion_pair_sub_union {x y} [IsSet x] [IsSet y] : Yunion (Pair x y) ⊆ x ∪ y :=
  fun z =>
  fun (h : z ∈ Yunion (Pair x y)) =>
  haveI : IsSet z := ⟨(all_classes_come_from_v (Yunion (Pair x y))) z h⟩
  have z_in_k : ∃ k, k ∈ Pair x y ∧ z ∈ k := (Yunion_φ (Pair x y) z).mp h
  let ⟨ k, hk ⟩ := z_in_k
  haveI : IsSet k := ⟨(all_classes_come_from_v (Pair x y)) k hk.left⟩
  have k_is_x_or_y : k = x ∨ k = y := (Pair_φ k ).mp hk.left
  have z_in_x_or_y : z ∈ x ∨ z ∈ y :=
    Or.elim k_is_x_or_y
    (fun k_is_x =>
      have z_in_x : z ∈ x := by rw [←k_is_x]; exact hk.right
      Or.intro_left (z ∈ y) z_in_x)
    (fun k_is_y =>
      have z_in_y : z ∈ y := by rw [←k_is_y]; exact hk.right
      Or.intro_right (z ∈ x) z_in_y)
  ((Sets.union_P₂ x y).choose_spec (x := z)).mpr z_in_x_or_y

theorem union_sub_yunion_pair {x y} [IsSet x] [IsSet y] : x ∪ y ⊆ Yunion (Pair x y) :=
  fun z =>
  fun (h : z ∈ x ∪ y) =>
  haveI : IsSet z := ⟨(all_classes_come_from_v (x ∪ y)) z h⟩
  have z_in_x_or_y : z ∈ x ∨ z ∈ y := ((Sets.union_P₂ x y).choose_spec (x := z)).mp h
  have exists_k : ∃ k, k ∈ (Pair x y) ∧ z ∈ k :=
    z_in_x_or_y.elim
    (fun z_in_x =>
      have x_in_pair : x ∈ Pair x y := pair_has_left x y
      Exists.intro x ⟨ x_in_pair, z_in_x ⟩)
    (fun z_in_y =>
      have y_in_pair : y ∈ Pair x y := pair_has_right x y
      Exists.intro y ⟨ y_in_pair, z_in_y ⟩)
  (Yunion_φ (Pair x y) z).mpr exists_k

protected theorem yunion_pair_eq_union {x y} [IsSet x] [IsSet y] : x ∪ y = Yunion (Pair x y) :=
  equality_sub.mpr ⟨ union_sub_yunion_pair, yunion_pair_sub_union ⟩

theorem union_is_yunion {x y} [IsSet x] [IsSet y] : Yunion (Pair x y) = x ∪ y :=
  equality_sub.mpr ⟨ yunion_pair_sub_union, union_sub_yunion_pair ⟩

theorem union_of_sets_in_v {x y} [IsSet x] [IsSet y] : x ∪ y ∈ V :=
  have union_pair_in_v : Yunion (Pair x y) ∈ V := A₅ (Pair x y)
  have eq : x ∪ y = Yunion (Pair x y) := Sets.yunion_pair_eq_union
  have union_in_v : x ∪ y ∈ V := eq ▸ union_pair_in_v
  union_in_v

instance (x y) [IsSet x] [IsSet y] : IsSet (x ∪ y) where
  in_v := union_of_sets_in_v

-- Intersection

protected def Intersection_P₂ (a) := P₂ (fun x => ∀ y, y ∈ a → x ∈ y)

noncomputable def Intersection (a) := (Sets.Intersection_P₂ a).choose

def Intersection_φ (a x) [IsSet x] := (Sets.Intersection_P₂ a).choose_spec (x := x)

-- Theorem 5.1 part 1: For any non-empty class A, Intersect A is a set.

theorem T5_1_1 : ∀ a, is_non_empty a → (Intersection a) ∈ V :=
  fun a =>
  fun a_is_non_empty : is_non_empty a =>
  let ⟨ x, x_in_a ⟩ := a_is_non_empty
  have x_in_v : x ∈ V := all_classes_come_from_v a x x_in_a
  have intersect_a_sub_x : (Intersection a) ⊆ x :=
    fun (y : Class) (y_in_intersect_a : y ∈ (Intersection a)) =>
    haveI : IsSet y := ⟨(all_classes_come_from_v (Intersection a)) y y_in_intersect_a⟩
    (Intersection_φ a y).mp y_in_intersect_a x x_in_a
  A₂ (Intersection a) x intersect_a_sub_x x_in_v

/--***** Power *****--/

protected def 𝒫_P₂ (a) [IsSet a] := P₂ (fun x => x ⊆ a)

noncomputable def 𝒫 (a) [IsSet a] := (Sets.𝒫_P₂ a).choose

def 𝒫_φ (a x) [IsSet a] [IsSet x] := (Sets.𝒫_P₂ a).choose_spec (x := x)

axiom A₆ (x : Class) [IsSet x] : (𝒫 x) ∈ V

end Sets
