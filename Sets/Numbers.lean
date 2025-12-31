import Sets.Sets

namespace Numbers
open Classes
open Sets
open Classical

/--***** Numbers *****--/

noncomputable def suc (x : Set) := x U Single x

theorem number_in_successor (n : Set) : n ∈ suc n :=
  have n_in_single : n ∈ Single n := pair_has_left n n
  have n_in_either : n ∈ n ∨ n ∈ Single n := Or.inr n_in_single
  (P₂_union_φ n (Single n) n).mpr n_in_either

theorem number_sub_successor (n : Set) : n ⊆ suc n := union_sub_left n

def is_inductive (x : Class) : Prop := (x ∈ V) ∧ (Null ∈ x) ∧ (∀ (y : Set), y ∈ x → suc y ∈ x)

def is_number (x : Class) : Prop := ∀ (y : Class), is_inductive y → x ∈ y

def Number : Type := { x : Set // is_number x}
instance : Coe Number Set := ⟨Subtype.val⟩

theorem successor_possibilities {x : Class} {n : Number} (h : x ∈ suc n) : x ∈ n ∨ x = n :=
  have x_in_n_or_x_in_single := (P₂_union_φ n (Single n) x).mp h
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
    have n_not_in_null : n ∉ Null := Null_φ n
    absurd n_in_null n_not_in_null

theorem peano_5 (a : Set) : is_inductive a → ∀ (n : Number), n ∈ a :=
  fun a_is_inductive =>
  fun n =>
  n.property a a_is_inductive

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

protected axiom P₂_transitive_numbers : Class
protected axiom P₂_transitive_numbers_φ {x : Class} : x ∈ Numbers.P₂_transitive_numbers ↔ is_number x ∧ is_transitive x

protected theorem class_of_trans_nbrs_is_set : Numbers.P₂_transitive_numbers ∈ V :=
  have is_subset_of_ω : Numbers.P₂_transitive_numbers ⊆ ω :=
    fun x => fun x_in_trans =>
    have x_is_nbr : is_number x := (Numbers.P₂_transitive_numbers_φ.mp x_in_trans).left
    (P₂_ω_φ x).mpr x_is_nbr
  A₂ Numbers.P₂_transitive_numbers ω is_subset_of_ω A₇

theorem class_of_trans_nbrs_is_inductive : is_inductive Numbers.P₂_transitive_numbers :=
  have null_transitive :=
    fun x y =>
    fun h : x ∈ y ∧ y ∈ Null =>
    have y_not_in_null : y ∉ Null := Null_φ y
    absurd h.right y_not_in_null
  have null_is_in_class : Null ∈ Numbers.P₂_transitive_numbers := Numbers.P₂_transitive_numbers_φ.mpr ⟨ peano_1, null_transitive ⟩
  have class_has_successors : ∀ (y : Set), y ∈ Numbers.P₂_transitive_numbers → suc y ∈ Numbers.P₂_transitive_numbers :=
    fun y => fun y_in_class : y ∈ Numbers.P₂_transitive_numbers =>
    let y_num : Number := ⟨ y, (Numbers.P₂_transitive_numbers_φ.mp y_in_class).left ⟩
    have y_is_trans : is_transitive y_num := (Numbers.P₂_transitive_numbers_φ.mp y_in_class).right
    have suc_is_transitive := succ_n_transitive y_is_trans
    have suc_is_nbr := peano_2 y_num
    Numbers.P₂_transitive_numbers_φ.mpr ⟨ suc_is_nbr, suc_is_transitive ⟩
  ⟨ Numbers.class_of_trans_nbrs_is_set, null_is_in_class, class_has_successors ⟩

theorem T_3_1 (n : Number) : is_transitive n :=
  have n_is_in_class : n ∈ Numbers.P₂_transitive_numbers := n.property Numbers.P₂_transitive_numbers class_of_trans_nbrs_is_inductive
  (Numbers.P₂_transitive_numbers_φ.mp n_is_in_class).right

theorem peano_4 (n m : Number) : suc n = suc m → n = m :=
  _

end Numbers
