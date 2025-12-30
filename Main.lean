open Classical

/--***** Classes *****--/

-- There are things called "classes"
axiom Class : Type

/--***** Membership *****--/

-- Classes have a "membership" relation with each other
axiom mem : Class -> Class -> Prop
infix:50 " ∈ " => mem

def nmem (a b : Class) : Prop := ¬(a ∈ b)
infix:50 " ∉ " => nmem

-- Membership determines the identity of a class -- a class is nothing more than its members
axiom P₁ : ∀ a b, (∀ x, x ∈ a ↔ x ∈ b) → a = b

def subclass (a b : Class) : Prop := ∀ x, x ∈ a -> x ∈ b
infix:50 " ⊆ " => subclass

theorem equality_sub {a b} : (a ⊆ b ∧ b ⊆ a) → a = b :=
  fun h =>
  have cond : ∀ x, x ∈ a ↔ x ∈ b :=
    fun x =>
    have a_then_b : x ∈ a → x ∈ b := h.left x
    have b_then_a : x ∈ b → x ∈ a := h.right x
    Iff.intro a_then_b b_then_a
  P₁ a b cond

/--***** Sets *****--/

-- There's one class in particular called "V"
axiom V : Class

-- V contains all the classes that can be members (and we call these "sets")
axiom AllClassesComeFromV : ∀ a, a ⊆ V

def Set : Type := { x : Class // x ∈ V }
instance : Coe Set Class := ⟨Subtype.val⟩

-- theorem members_are_sets {a b : Class} (a_in_b : a ∈ b) : a ∈ V :=
--   have b_is_subclass_of_v := AllClassesComeFromV b
--   b_is_subclass_of_v a a_in_b

/--
P₁: Separation. This is an informal meta-axiom. It says that you can add any axiom of this form:

  ∀ A₁ ... Aₙ, ∃ B, ∀ x, x ∈ V → (x ∈ B ↔ φ(A₁, ..., Aₙ, x))

We'll prefix our instances of P₁ with "P₁_". We usually do this with two axioms: one to name the
class (B), and one to describe it (φ).

The Separation principle plus AllClassesComeFromV is how we avoid Russel's paradox: all members (sets)
are classes, but only certain classes are members (sets).
--/

-- Theorem 1.1: Not all classes are sets

axiom P₁_Ordinary : Class
axiom P₁_Ordinary_φ : ∀ (x : Set), x ∈ P₁_Ordinary ↔ x ∉ x

theorem T_1_1 : ∃ a, a ∉ V :=
  have Ordinary_not_in_V :=
    byContradiction
      fun O_in_V =>
      have O_in_and_not_in_self := P₁_Ordinary_φ ⟨ P₁_Ordinary, (not_not.mp O_in_V) ⟩
      Or.elim (em (P₁_Ordinary ∈ P₁_Ordinary))
        (fun is_in =>
          have is_not_in := O_in_and_not_in_self.mp is_in
          absurd is_in is_not_in)
        (fun is_not_in =>
          have is_in := O_in_and_not_in_self.mpr is_not_in
          absurd is_not_in (not_not.mpr is_in))
  Exists.intro P₁_Ordinary Ordinary_not_in_V

-- Theorem 1.2: For any class A there is a subclass B of A s.t. B is not an element of A

axiom P₁_MakeOrdinary (a : Class) : ∃ b, ∀ x, x ∈ b ↔ (x ∈ a ∧ x ∉ x)

theorem T_1_2 : ∀ a, ∃ b, b ⊆ a ∧ b ∉ a :=
  fun a =>
  let ⟨ b, b_is_ord_subset_of_a ⟩ := (P₁_MakeOrdinary a)
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
    have b_sub_v := AllClassesComeFromV b
    have b_in_v := every_subset_in_v b b_sub_v
    absurd b_in_v b_not_in_v

theorem all_members_are_sets {a b : Class} (h : a ∈ b) : a ∈ V := (AllClassesComeFromV b) a h

/--***** The empty set *****--/

axiom Null : Class
axiom Null_prop : ∀ x, x ∉ Null

-- NOTE: At this point, V may well be empty. A₃ changes that.

axiom A₃ : Null ∈ V

/--***** Pairing *****--/

axiom Pair (a b : Set) : Class
axiom P₁_Pair_φ (a b : Set) : ∀ (x : Class), x ∈ (Pair a b) ↔ x = a ∨ x = b

noncomputable abbrev Single (a : Set) := Pair a a

axiom A₄ (a b : Set) : Pair a b ∈ V

theorem C_4_1 (a : Set) : (Pair a a) ∈ V := A₄ a a

theorem pair_has_left (a b : Set) : a ∈ Pair a b :=
  have a_is_a_or_b : a.val = a.val ∨ a.val = b.val := Or.inl rfl
  (P₁_Pair_φ a b a).mpr a_is_a_or_b

theorem pair_has_right (a b : Set) : b ∈ Pair a b :=
  have b_is_a_or_b : b.val = a.val ∨ b.val = b.val := Or.inr rfl
  (P₁_Pair_φ a b b).mpr b_is_a_or_b

theorem in_single {x : Class} {y : Set} (h : x ∈ Single y) : x = y :=
  have poss := (P₁_Pair_φ y y x).mp h
  poss.elim (fun h => h) (fun h => h)

/--***** Union *****--/

axiom Yunion (a : Class) : Class
axiom Yunion_prop (a : Class) : ∀ x, x ∈ (Yunion a) ↔ ∃ y, y ∈ a ∧ x ∈ y

axiom A₅ : ∀ (x : Set), (Yunion x) ∈ V

def is_non_empty (a : Class) : Prop := ∃ x, x ∈ a

axiom P₁_union (a b : Class) : Class
axiom P₁_union_φ (a b : Class) : ∀ x, x ∈ (P₁_union a b) ↔ (x ∈ a ∨ x ∈ b)
infix:60 " U " => P₁_union

theorem union_sub_left (a : Class) { b : Class }: a ⊆ a U b :=
  fun x =>
  fun x_in_a : x ∈ a =>
  have prop := P₁_union_φ a b x
  prop.mpr (Or.inl x_in_a)

theorem union_sub_right (b : Class) { a : Class }: b ⊆ a U b :=
  fun x =>
  fun x_in_b : x ∈ b =>
  have prop := P₁_union_φ a b x
  prop.mpr (Or.inr x_in_b)

theorem union_pair_sub_union {x y} : Yunion (Pair x y) ⊆ x U y :=
  fun z =>
  fun (h : z ∈ Yunion (Pair x y)) =>
  have z_in_k : ∃ k, k ∈ Pair x y ∧ z ∈ k := (Yunion_prop (Pair x y) z).mp h
  let ⟨ k, hk ⟩ := z_in_k
  have k_in_v : k ∈ V := all_members_are_sets hk.left
  have k_is_x_or_y : k = x ∨ k = y := (P₁_Pair_φ x y k ).mp hk.left
  have z_in_x_or_y : z ∈ x ∨ z ∈ y :=
    Or.elim k_is_x_or_y
    (fun k_is_x =>
      have z_in_x : z ∈ x := by rw [←k_is_x]; exact hk.right
      Or.intro_left (z ∈ y) z_in_x)
    (fun k_is_y =>
      have z_in_y : z ∈ y := by rw [←k_is_y]; exact hk.right
      Or.intro_right (z ∈ x) z_in_y)
  (P₁_union_φ x y z).mpr z_in_x_or_y

theorem union_sub_union_pair {x y : Set} : x U y ⊆ Yunion (Pair x y) :=
  fun z =>
  fun (h : z ∈ x U y) =>
  have z_in_x_or_y : z ∈ x ∨ z ∈ y := (P₁_union_φ x y z).mp h
  have exists_k : ∃ k, k ∈ (Pair x y) ∧ z ∈ k :=
    z_in_x_or_y.elim
    (fun z_in_x =>
      have x_in_pair : x ∈ Pair x y := pair_has_left x y
      Exists.intro x ⟨ x_in_pair, z_in_x ⟩)
    (fun z_in_y =>
      have y_in_pair : y ∈ Pair x y := pair_has_right x y
      Exists.intro y ⟨ y_in_pair, z_in_y ⟩)
  (Yunion_prop (Pair x y) z).mpr exists_k

theorem union_equals_union_pair {x y : Set} : x U y = Yunion (Pair x y) :=
  equality_sub ⟨ union_sub_union_pair, union_pair_sub_union ⟩

theorem union_of_sets_is_set {x y : Set} : x U y ∈ V :=
  have union_pair_is_set : Yunion (Pair x y) ∈ V := A₅ ⟨ (Pair x y), A₄ x y ⟩
  by rw [union_equals_union_pair]; assumption

-- Intersection

axiom Intersect (a : Class) : Class
axiom Intersect_prop (a : Class) : ∀ x, x ∈ (Intersect a) ↔ ∀ y, y ∈ a → x ∈ y

-- Theorem 5.1 part 1: For any non-empty class A, Intersect A is a set.

theorem T5_1_1 : ∀ a, is_non_empty a → (Intersect a) ∈ V :=
  fun a =>
  fun a_is_non_empty : is_non_empty a =>
  let ⟨ x, x_in_a ⟩ := a_is_non_empty
  have x_in_v : x ∈ V := AllClassesComeFromV a x x_in_a
  have intersect_a_sub_x : (Intersect a) ⊆ x :=
    fun (y : Class) (y_in_intersect_a : y ∈ (Intersect a)) =>
    (Intersect_prop a y).mp y_in_intersect_a x x_in_a
  A₂ (Intersect a) x intersect_a_sub_x x_in_v

/--***** Power *****--/

axiom 𝒫 (a : Set) : Class
axiom 𝒫_φ (a : Set): ∀ x, x ∈ (𝒫 a) ↔ x ⊆ a

axiom A₆ : ∀ (x : Set), (𝒫 x) ∈ V

/--***** Numbers *****--/

noncomputable def suc (x : Set) := x U Single x

theorem number_in_successor (n : Set) : n ∈ suc n :=
  have n_in_single : n ∈ Single n := pair_has_left n n
  have n_in_either : n ∈ n ∨ n ∈ Single n := Or.inr n_in_single
  (P₁_union_φ n (Single n) n).mpr n_in_either

theorem number_sub_successor (n : Set) : n ⊆ suc n := union_sub_left n

def is_inductive_set (x : Class) : Prop := (x ∈ V) ∧ (Null ∈ x) ∧ (∀ (y : Set), y ∈ x → suc y ∈ x)

def is_number (x : Class) : Prop := ∀ (y : Class), is_inductive_set y → x ∈ y

def Number : Type := { x : Set // is_number x}
instance : Coe Number Set := ⟨Subtype.val⟩

theorem successor_possibilities {x : Class} {n : Number} (h : x ∈ suc n) : x ∈ n ∨ x = n :=
  have x_in_n_or_x_in_single := (P₁_union_φ n (Single n) x).mp h
  x_in_n_or_x_in_single.elim
    (fun x_in_n => Or.inl x_in_n)
    (fun (x_in_single : x ∈ Single n) =>
      have x_is_x : x = n := in_single x_in_single
      Or.inr x_is_x)

axiom ω : Class
axiom P₂_ω_φ (x : Class) : x ∈ ω ↔ is_number x

axiom A₇ : ω ∈ V

theorem peano_1 : is_number Null :=
  fun _ => fun y_is_inductive =>
  y_is_inductive.right.left

theorem peano_2 (n : Number) : is_number (suc n) :=
  fun y => fun y_is_inductive =>
  have n_in_y : n ∈ y := n.property y y_is_inductive
  y_is_inductive.right.right n n_in_y

theorem peano_3 (n : Number) : suc n ≠ Null :=
  byContradiction
    fun suc_eq_null =>
    have n_in_suc : n ∈ suc n := number_in_successor n
    have n_in_null : n ∈ Null := Eq.subst (not_not.mp suc_eq_null) n_in_suc
    have n_not_in_null : n ∉ Null := Null_prop n
    absurd n_in_null n_not_in_null

theorem peano_5 (a : Set) : is_inductive_set a → ∀ (n : Number), n ∈ a :=
  fun a_is_inductive =>
  fun n =>
  n.property a a_is_inductive

-- def is_transitive (a : Class) : Prop := ∀ x y, x ∈ y ∧ y ∈ a → x ∈ a

theorem succ_n_transitive {n : Number} (h : is_transitive n) : is_transitive (suc n) :=
  fun (x y : Class) =>
  fun (h1 : x ∈ y ∧ y ∈ suc n) =>
  (successor_possibilities h1.right).elim
    (fun h2 : y ∈ n =>
      -- // x ∈ suc n
      have x_in_n : x ∈ n := h x y ⟨ h1.left, h2 ⟩
      (number_sub_successor n) x x_in_n)
    (fun h2 : y = n =>
      -- // x ∈ suc n
      have x_in_n : x ∈ n := Eq.subst h2 h1.left
      (number_sub_successor n) x x_in_n)

theorem null_transitive : is_transitive Null :=
  fun x y =>
  fun h : x ∈ y ∧ y ∈ Null =>
  have y_not_in_null : y ∉ Null := Null_prop y
  absurd h.right y_not_in_null

axiom P₂_transitive_numbers : Class
axiom P₂_transitive_numbers_φ {x : Class} : x ∈ P₂_transitive_numbers ↔ is_number x ∧ is_transitive x

-- def is_swelled (a : Class) : Prop := ∀ x y, x ⊆ y → y ∈ a → x ∈ a

theorem class_of_trans_nbrs_is_set : P₂_transitive_numbers ∈ V :=
  have is_subset_of_ω : P₂_transitive_numbers ⊆ ω :=
    fun x => fun x_in_trans =>
    have x_is_nbr : is_number x := (P₂_transitive_numbers_φ.mp x_in_trans).left
    (P₂_ω_φ x).mpr x_is_nbr
  A₂ P₂_transitive_numbers ω is_subset_of_ω A₇

theorem class_of_trans_nbrs_is_inductive : is_inductive_set P₂_transitive_numbers :=
  have null_is_in_class : Null ∈ P₂_transitive_numbers := P₂_transitive_numbers_φ.mpr ⟨ peano_1, null_transitive ⟩
  have class_has_successors : ∀ (y : Set), y ∈ P₂_transitive_numbers → suc y ∈ P₂_transitive_numbers :=
    fun y => fun y_in_class : y ∈ P₂_transitive_numbers =>
    let y_num : Number := ⟨ y, (P₂_transitive_numbers_φ.mp y_in_class).left ⟩
    have y_is_trans : is_transitive y_num := (P₂_transitive_numbers_φ.mp y_in_class).right
    have suc_is_transitive := succ_n_transitive y_is_trans
    have suc_is_nbr := peano_2 y_num
    P₂_transitive_numbers_φ.mpr ⟨ suc_is_nbr, suc_is_transitive ⟩
  ⟨ class_of_trans_nbrs_is_set, null_is_in_class, class_has_successors ⟩

theorem T_3_1 (n : Number) : is_transitive n :=
  have n_is_in_class : n ∈ P₂_transitive_numbers := n.property P₂_transitive_numbers class_of_trans_nbrs_is_inductive
  (P₂_transitive_numbers_φ.mp n_is_in_class).right

theorem peano_4 (n m : Number) : suc n = suc m → n = m :=
  _
