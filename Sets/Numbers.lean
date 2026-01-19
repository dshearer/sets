import Sets.Sets
namespace Numbers
open Classes
open Sets
open Classical

/--***** Numbers *****--/

noncomputable def suc (n) [IsSet n] := n ∪ Single n

theorem number_in_successor (n) [IsSet n] : n ∈ suc n :=
  (P₂_union_φ n (Single n) n).mpr (Or.inr (pair_has_left n n))

theorem number_sub_successor (n) [IsSet n] : n ⊆ suc n := union_sub_left n

def is_inductive (x : Class) : Prop := (x ∈ V) ∧ (Null ∈ x) ∧ (∀ y [IsSet y], y ∈ x → suc y ∈ x)

def is_number (x : Class) : Prop := x ∈ V ∧ (∀ y, is_inductive y → x ∈ y)

class IsNumber (a) [IsSet a]: Prop where
  prop : is_number a

theorem successor_possibilities {x n} [IsSet x] [IsSet n] : x ∈ suc n ↔ x ∈ n ∨ x = n :=
  have h1 : x ∈ suc n → x ∈ n ∨ x = n :=
    fun x_in_suc =>
    (P₂_union_φ n (Single n) x).mp x_in_suc |>.elim Or.inl (Or.inr ∘ in_single)
  have h2 : x ∈ n ∨ x = n → x ∈ suc n :=
    fun or_exp => or_exp.elim (number_sub_successor n x) (· ▸ number_in_successor n)
  ⟨ h1, h2 ⟩

axiom ω : Class
axiom P₂_ω_φ (x : Class) : x ∈ ω ↔ is_number x

axiom A₇ : ω ∈ V

theorem peano_1 : is_number Null :=
  ⟨ A₃, fun _ => fun y_is_inductive => y_is_inductive.right.left ⟩

theorem peano_2 {n} [IsSet n] [IsNumber n] : is_number (suc n) :=
  have suc_in_v : suc n ∈ V := union_of_sets_is_set
  have in_every_inductive : (∀ y, is_inductive y → suc n ∈ y) :=
    fun y => fun y_is_inductive =>
    have n_is_number : is_number n := IsNumber.prop
    have n_in_y : n ∈ y := n_is_number.right y y_is_inductive
    y_is_inductive.right.right n n_in_y
  ⟨ suc_in_v, in_every_inductive ⟩

theorem peano_3 {n} [IsSet n] [IsNumber n] : suc n ≠ Null :=
  fun suc_eq_null =>
  have n_in_suc : n ∈ suc n := number_in_successor n
  have n_in_null : n ∈ Null := suc_eq_null ▸ n_in_suc
  absurd n_in_null (Null_φ n)

theorem peano_5 (a) [IsSet a] : is_inductive a → ∀ n [IsSet n] [IsNumber n], n ∈ a :=
  fun a_is_inductive => fun _ => IsNumber.prop.right a a_is_inductive

theorem succ_n_transitive {n} [IsSet n] [IsNumber n] (h : is_transitive n) : is_transitive (suc n) :=
  fun (x y : Class) =>
  fun (h1 : x ∈ y ∧ y ∈ suc n) =>
  -- Since y ∈ suc n, then either:
  have y_in_v : y ∈ V := all_members_are_sets h1.right
  haveI : IsSet y := ⟨ y_in_v ⟩
  (successor_possibilities.mp h1.right).elim
    (fun h2 : y ∈ n =>
      -- // x ∈ suc n
      have x_in_n : x ∈ n := h x y ⟨ h1.left, h2 ⟩
      (number_sub_successor n) x x_in_n)
    (fun h2 : y = n =>
      -- // x ∈ suc n
      have x_in_n : x ∈ n := Eq.subst h2 h1.left
      (number_sub_successor n) x x_in_n)

abbrev make_nbr_φ (a : Class) (p : Class → Prop) := ∀ {x : Class}, x ∈ a ↔ is_number x ∧ p x

theorem not_nbr_then_not_in_class {a x} {p : Class -> Prop} (φ : make_nbr_φ a p) : ¬ is_number x → x ∉ a :=
  fun h =>
  have not_is_nbr_and_p : ¬ (is_number x ∧ p x) :=
    have not_nbr_or : ¬ is_number x ∨ ¬ p x := Or.inl h
    not_and_iff_not_or_not.mpr not_nbr_or
  -- modus tollens
  mt φ.mp not_is_nbr_and_p

theorem not_p_then_not_in_class {a x} {p : Class -> Prop} (φ : make_nbr_φ a p) : ¬ p x → x ∉ a :=
  fun not_p =>
  have not_nbr_and_p : ¬ (is_number x ∧ p x) := fun h => not_p h.right
  fun x_in_a : x ∈ a => not_nbr_and_p (φ.mp x_in_a) -- by contradiction

theorem not_in_class_then_not_p {a x} [IsSet x] [IsNumber x] {p : Class → Prop} (φ : make_nbr_φ a p) : x ∉ a → ¬ p x :=
  fun not_in_class =>
  have not_nbr_and_p : ¬ (is_number x ∧ p x) := fun h => not_in_class (φ.mpr h) -- by contradiction
  not_and.mp not_nbr_and_p IsNumber.prop

protected axiom P₂_transitive_numbers : Class
protected axiom P₂_transitive_numbers_φ : make_nbr_φ Numbers.P₂_transitive_numbers is_transitive

theorem class_of_nbrs_is_set {a} {p : Class -> Prop} (φ : {x : Class} → (x ∈ a ↔ is_number x ∧ p x)) : a ∈ V :=
  have is_subset_of_ω : a ⊆ ω :=
    fun x => fun x_in_class =>
    have x_is_nbr : is_number x := (φ.mp x_in_class).left
    (P₂_ω_φ x).mpr x_is_nbr
  A₂ a ω is_subset_of_ω A₇

theorem class_of_trans_nbrs_is_inductive : is_inductive Numbers.P₂_transitive_numbers :=
  have null_transitive : is_transitive Null :=
    fun _ y h => absurd h.right (Null_φ y)
  have null_is_in_class : Null ∈ Numbers.P₂_transitive_numbers := Numbers.P₂_transitive_numbers_φ.mpr ⟨ peano_1, null_transitive ⟩
  have class_has_successors : ∀ y [IsSet y], y ∈ Numbers.P₂_transitive_numbers → suc y ∈ Numbers.P₂_transitive_numbers :=
    fun y => fun y_in_class : y ∈ Numbers.P₂_transitive_numbers =>
    have y_is_nbr : is_number y := (Numbers.P₂_transitive_numbers_φ.mp y_in_class).left
    have y_is_trans : is_transitive y := (Numbers.P₂_transitive_numbers_φ.mp y_in_class).right
    haveI : IsNumber y := ⟨ y_is_nbr ⟩
    have suc_is_transitive : is_transitive (suc y) := succ_n_transitive y_is_trans
    have suc_is_nbr : is_number (suc y) := peano_2
    Numbers.P₂_transitive_numbers_φ.mpr ⟨ suc_is_nbr, suc_is_transitive ⟩
  have class_of_trans_nbrs_is_set := class_of_nbrs_is_set Numbers.P₂_transitive_numbers_φ
  ⟨ class_of_trans_nbrs_is_set, null_is_in_class, class_has_successors ⟩

theorem T_3_1 {n} (h : is_number n) : is_transitive n :=
  -- Class of transitive numbers is inductive. All numbers are in all inductive classes. So all numbers are transitive.
  have n_is_in_class : n ∈ Numbers.P₂_transitive_numbers := h.right Numbers.P₂_transitive_numbers class_of_trans_nbrs_is_inductive
  (Numbers.P₂_transitive_numbers_φ.mp n_is_in_class).right

protected axiom P₂_ordinary_numbers : Class
protected axiom P₂_ordinary_numbers_φ : make_nbr_φ Numbers.P₂_ordinary_numbers is_ordinary

protected theorem class_of_ord_nbrs_is_inductive : is_inductive Numbers.P₂_ordinary_numbers :=
  -- Null is ordinary
  have null_ordinary : is_ordinary Null := Null_φ Null
  -- Null is in the class of ordinary numbers
  have null_is_in_class : Null ∈ Numbers.P₂_ordinary_numbers := Numbers.P₂_ordinary_numbers_φ.mpr ⟨ peano_1, null_ordinary ⟩
  -- The class of ordinary numbers contains successors
  have class_has_successors : ∀ y [IsSet y], y ∈ Numbers.P₂_ordinary_numbers → suc y ∈ Numbers.P₂_ordinary_numbers :=
    fun y =>
    have tollens : suc y ∉ Numbers.P₂_ordinary_numbers → y ∉ Numbers.P₂_ordinary_numbers :=
      fun suc_not_in_ordinary =>
      Or.elim (em (is_number y))
        (fun y_is_nbr =>
          haveI : IsNumber y := ⟨ y_is_nbr ⟩
          have not_nbr_or_not_ord := not_and_iff_not_or_not.mp (mt Numbers.P₂_ordinary_numbers_φ.mpr suc_not_in_ordinary)
          Or.elim not_nbr_or_not_ord
            -- If suc n is not a number, then n is not ordinary
            (fun suc_not_nbr : ¬ is_number (suc y) =>
              have y_not_nbr : ¬ is_number y := fun _ => suc_not_nbr peano_2
              not_nbr_then_not_in_class Numbers.P₂_ordinary_numbers_φ y_not_nbr)
            -- If suc n is in itself, then n is not ordinary
            (fun suc_not_ordinary =>
              have suc_in_self : suc y ∈ suc y := not_not.mp suc_not_ordinary
              have suc_in_v : suc y ∈ V := all_members_are_sets suc_in_self
              haveI : IsSet (suc y) := ⟨ suc_in_v ⟩
              Or.elim (successor_possibilities.mp suc_in_self)
                (fun suc_y_in_y =>
                  have suc_sub_h : suc y ⊆ y := Sets.members_of_trans_are_subsets (T_3_1 y_is_nbr) suc_y_in_y
                  have y_in_suc : y ∈ suc y := number_in_successor y
                  have y_in_self : y ∈ y := suc_sub_h y y_in_suc
                  not_p_then_not_in_class Numbers.P₂_ordinary_numbers_φ (not_not.mpr y_in_self))
                (fun suc_y_is_y =>
                  have suc_sub_h : suc y ⊆ y := (Classes.equality_sub.mp suc_y_is_y).left
                  have y_in_suc : y ∈ suc y := number_in_successor y
                  have y_in_self : y ∈ y := suc_sub_h y y_in_suc
                  not_p_then_not_in_class Numbers.P₂_ordinary_numbers_φ (not_not.mpr y_in_self))))
        (fun y_is_not_nbr => not_nbr_then_not_in_class Numbers.P₂_ordinary_numbers_φ y_is_not_nbr)
    fun h : y ∈ Numbers.P₂_ordinary_numbers =>
      have h2 : ¬ (y ∉ Numbers.P₂_ordinary_numbers) := not_not.mpr h
      not_not.mp (mt tollens h2)
  have class_of_ord_nbrs_is_set := class_of_nbrs_is_set Numbers.P₂_ordinary_numbers_φ
  -- Given all these, the class of ordinary numbers is inductive
  ⟨ class_of_ord_nbrs_is_set, null_is_in_class, class_has_successors ⟩

theorem T_3_2 {n} [IsSet n] [IsNumber n] : n ∉ n :=
  -- Class of ordinary numbers is inductive. All numbers are in all inductive classes. So all numbers are ordinary.
  have n_is_in_class : n ∈ Numbers.P₂_ordinary_numbers := IsNumber.prop.right Numbers.P₂_ordinary_numbers Numbers.class_of_ord_nbrs_is_inductive
  (Numbers.P₂_ordinary_numbers_φ.mp n_is_in_class).right

theorem T_3_3 {n m} [IsSet n] [IsSet m] [IsNumber n] [IsNumber m] : ¬ (n ∈ m ∧ m ∈ n) :=
  fun opposite =>
  have m_sub_n : m ⊆ n := Sets.members_of_trans_are_subsets (T_3_1 IsNumber.prop) opposite.right
  have n_in_n : n ∈ n := m_sub_n n opposite.left
  have n_not_in_n : n ∉ n := T_3_2
  absurd n_in_n n_not_in_n

protected axiom P₂_hereditary_numbers : Class
protected axiom P₂_hereditary_numbers_φ : make_nbr_φ Numbers.P₂_hereditary_numbers (fun n => ∀ (x : Class), x ∈ n → is_number x)

protected theorem class_of_hereditary_nbrs_is_inductive : is_inductive Numbers.P₂_hereditary_numbers :=
  -- Null is hereditary (all its elements are numbers, vacuously)
  have null_hereditary : ∀ (x : Class), x ∈ Null → is_number x :=
    fun x x_in_null => absurd x_in_null (Null_φ x)
  -- Null is in the class of hereditary numbers
  have null_is_in_class : Null ∈ Numbers.P₂_hereditary_numbers := Numbers.P₂_hereditary_numbers_φ.mpr ⟨ peano_1, null_hereditary ⟩
  -- The class of hereditary numbers contains successors
  have class_has_successors : ∀ y [IsSet y], y ∈ Numbers.P₂_hereditary_numbers → suc y ∈ Numbers.P₂_hereditary_numbers :=
    fun y => fun y_in_class =>
    have y_is_nbr : is_number y := (Numbers.P₂_hereditary_numbers_φ.mp y_in_class).left
    have y_hereditary : ∀ (x : Class), x ∈ y → is_number x := (Numbers.P₂_hereditary_numbers_φ.mp y_in_class).right
    haveI : IsNumber y := ⟨ y_is_nbr ⟩
    have suc_is_nbr : is_number (suc y) := peano_2
    have suc_hereditary : ∀ (x : Class), x ∈ suc y → is_number x :=
      fun x => fun x_in_suc =>
      have x_in_v : x ∈ V := all_members_are_sets x_in_suc
      haveI : IsSet x := ⟨ x_in_v ⟩
      Or.elim (successor_possibilities.mp x_in_suc)
        (fun x_in_y => y_hereditary x x_in_y)
        (fun x_eq_y => x_eq_y ▸ y_is_nbr)
    Numbers.P₂_hereditary_numbers_φ.mpr ⟨ suc_is_nbr, suc_hereditary ⟩
  have class_of_hereditary_nbrs_is_set := class_of_nbrs_is_set Numbers.P₂_hereditary_numbers_φ
  ⟨ class_of_hereditary_nbrs_is_set, null_is_in_class, class_has_successors ⟩

theorem peano_4 {n m} [IsSet n] [IsSet m] [IsNumber n] [IsNumber m] : suc n = suc m → n = m :=
  fun h => byContradiction fun n_not_m =>
  have n_in_m : n ∈ m := or_iff_not_imp_right.mp (successor_possibilities.mp (h ▸ number_in_successor n)) n_not_m
  have m_in_n : m ∈ n := or_iff_not_imp_right.mp (successor_possibilities.mp (h ▸ number_in_successor m)) (Ne.symm n_not_m)
  absurd ⟨ n_in_m, m_in_n ⟩ T_3_3

theorem T_3_4 {n} [IsSet n] [IsNumber n] (x) : x ∈ n → is_number x :=
  /-
  By induction:
  All elements of 0 are numbers, since 0 is empty.
  Suppose k is a number such that all its elements are numbers. Then all elements of (suc k) are numbers,
  since every element of (suc k) is either an element of k or is k itself.
  -/
  fun x_in_n =>
  -- Class of hereditary numbers is inductive. All numbers are in all inductive classes.
  -- So all numbers are hereditary (their elements are numbers).
  have n_is_in_class : n ∈ Numbers.P₂_hereditary_numbers := IsNumber.prop.right Numbers.P₂_hereditary_numbers Numbers.class_of_hereditary_nbrs_is_inductive
  (Numbers.P₂_hereditary_numbers_φ.mp n_is_in_class).right x x_in_n

end Numbers
