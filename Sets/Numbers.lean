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

theorem successor_possibilities {x : Class} {n : Set} : x ∈ suc n ↔ x ∈ n ∨ x = n :=
  have h1 : x ∈ suc n → x ∈ n ∨ x = n :=
    fun x_in_suc =>
    have x_in_n_or_x_in_single := (P₂_union_φ n (Single n) x).mp x_in_suc
    x_in_n_or_x_in_single.elim
      (fun x_in_n => Or.inl x_in_n)
      (fun (x_in_single : x ∈ Single n) =>
        have x_is_x : x = n := in_single x_in_single
        Or.inr x_is_x)
  have h2 : x ∈ n ∨ x = n → x ∈ suc n :=
    fun or_exp : x ∈ n ∨ x = n =>
    or_exp.elim
      (fun x_in_n => (number_sub_successor n) x x_in_n)
      (fun x_is_n => x_is_n ▸ (number_in_successor n))
  ⟨ h1, h2 ⟩

axiom ω : Class
axiom P₂_ω_φ (x : Class) : x ∈ ω ↔ is_number x

axiom A₇ : ω ∈ V

theorem peano_1 : is_number Null :=
  fun _ => fun y_is_inductive =>
  y_is_inductive.right.left

theorem peano_2 {n : Set} (h : is_number n) : is_number (suc n) :=
  fun y => fun y_is_inductive =>
  have n_in_y : n ∈ y := h y y_is_inductive
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
  -- Since y ∈ suc n, then either:
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

theorem not_nbr_then_not_in_class {a : Class} {x : Class} {p : Class -> Prop} (φ : make_nbr_φ a p) : ¬ is_number x → x ∉ a :=
  fun h =>
  have not_is_nbr_and_p : ¬ (is_number x ∧ p x) :=
    have not_nbr_or : ¬ is_number x ∨ ¬ p x := Or.inl h
    not_and_iff_not_or_not.mpr not_nbr_or
  -- modus tollens
  mt φ.mp not_is_nbr_and_p

theorem not_p_then_not_in_class {a : Class} {x : Class} {p : Class -> Prop} (φ : make_nbr_φ a p) : ¬ p x → x ∉ a :=
  fun not_p =>
  have not_nbr_and_p : ¬ (is_number x ∧ p x) := fun h => not_p h.right
  fun x_in_a : x ∈ a => not_nbr_and_p (φ.mp x_in_a) -- by contradiction

theorem not_in_class_then_not_p {a : Class} {x : Number} {p : Class → Prop} (φ : make_nbr_φ a p) : x ∉ a → ¬ p x :=
  fun not_in_class =>
  have not_nbr_and_p : ¬ (is_number x ∧ p x) := fun h => not_in_class (φ.mpr h) -- by contradiction
  not_and.mp not_nbr_and_p x.property

protected axiom P₂_transitive_numbers : Class
protected axiom P₂_transitive_numbers_φ : make_nbr_φ Numbers.P₂_transitive_numbers is_transitive

theorem class_of_nbrs_is_set {a : Class} {p : Class -> Prop} (φ : {x : Class} → (x ∈ a ↔ is_number x ∧ p x)) : a ∈ V :=
  have is_subset_of_ω : a ⊆ ω :=
    fun x => fun x_in_class =>
    have x_is_nbr : is_number x := (φ.mp x_in_class).left
    (P₂_ω_φ x).mpr x_is_nbr
  A₂ a ω is_subset_of_ω A₇

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
    have suc_is_nbr := peano_2 y_num.property
    Numbers.P₂_transitive_numbers_φ.mpr ⟨ suc_is_nbr, suc_is_transitive ⟩
  have class_of_trans_nbrs_is_set := class_of_nbrs_is_set Numbers.P₂_transitive_numbers_φ
  ⟨ class_of_trans_nbrs_is_set, null_is_in_class, class_has_successors ⟩

theorem T_3_1 {n : Class} (h : is_number n) : is_transitive n :=
  -- Class of transitive numbers is inductive. All numbers are in all inductive classes. So all numbers are transitive.
  have n_is_in_class : n ∈ Numbers.P₂_transitive_numbers := h Numbers.P₂_transitive_numbers class_of_trans_nbrs_is_inductive
  (Numbers.P₂_transitive_numbers_φ.mp n_is_in_class).right

protected axiom P₂_ordinary_numbers : Class
protected axiom P₂_ordinary_numbers_φ : make_nbr_φ Numbers.P₂_ordinary_numbers is_ordinary

protected theorem class_of_ord_nbrs_is_inductive : is_inductive Numbers.P₂_ordinary_numbers :=
  -- Null is ordinary
  have null_ordinary : is_ordinary Null :=
    byContradiction
      fun null_not_ordinary =>
      have null_in_null : Null ∈ Null := not_not.mp null_not_ordinary
      have null_not_in_null : Null ∉ Null := Null_φ Null
      absurd null_in_null null_not_in_null
  -- Null is in the class of ordinary numbers
  have null_is_in_class : Null ∈ Numbers.P₂_ordinary_numbers := Numbers.P₂_ordinary_numbers_φ.mpr ⟨ peano_1, null_ordinary ⟩
  -- The class of ordinary numbers contains successors
  have class_has_successors : ∀ (y : Set), y ∈ Numbers.P₂_ordinary_numbers → suc y ∈ Numbers.P₂_ordinary_numbers :=
    fun y =>
    have tollens : suc y ∉ Numbers.P₂_ordinary_numbers → y ∉ Numbers.P₂_ordinary_numbers :=
      fun suc_not_in_ordinary =>
      Or.elim (em (is_number y))
        (fun y_is_nbr =>
          have not_nbr_or_not_ord := not_and_iff_not_or_not.mp (mt Numbers.P₂_ordinary_numbers_φ.mpr suc_not_in_ordinary)
          Or.elim not_nbr_or_not_ord
            -- If suc n is not a number, then n is not ordinary
            (fun suc_not_nbr =>
              have y_not_nbr : ¬ is_number y := mt peano_2 suc_not_nbr
              not_nbr_then_not_in_class Numbers.P₂_ordinary_numbers_φ y_not_nbr)
            -- If suc n is in itself, then n is not ordinary
            (fun suc_not_ordinary =>
              have suc_in_self : suc y ∈ suc y := not_not.mp suc_not_ordinary
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

theorem T_3_2 (n : Number) : n ∉ n :=
  -- Class of ordinary numbers is inductive. All numbers are in all inductive classes. So all numbers are ordinary.
  have n_is_in_class : n ∈ Numbers.P₂_ordinary_numbers := n.property Numbers.P₂_ordinary_numbers Numbers.class_of_ord_nbrs_is_inductive
  (Numbers.P₂_ordinary_numbers_φ.mp n_is_in_class).right

theorem T_3_3 (n m : Number) : ¬ (n ∈ m ∧ m ∈ n) :=
  fun opposite =>
  have m_sub_n : m ⊆ n := Sets.members_of_trans_are_subsets (T_3_1 n.property) opposite.right
  have n_in_n : n ∈ n := m_sub_n n opposite.left
  have n_not_in_n : n ∉ n := T_3_2 n
  absurd n_in_n n_not_in_n

protected axiom P₂_hereditary_numbers : Class
protected axiom P₂_hereditary_numbers_φ : make_nbr_φ Numbers.P₂_hereditary_numbers (fun n => ∀ (x : Class), x ∈ n → is_number x)

protected theorem class_of_hereditary_nbrs_is_inductive : is_inductive Numbers.P₂_hereditary_numbers :=
  -- Null is hereditary (all its elements are numbers, vacuously)
  have null_hereditary : ∀ (x : Class), x ∈ Null → is_number x :=
    fun x => fun x_in_null =>
    have x_not_in_null : x ∉ Null := Null_φ x
    absurd x_in_null x_not_in_null
  -- Null is in the class of hereditary numbers
  have null_is_in_class : Null ∈ Numbers.P₂_hereditary_numbers := Numbers.P₂_hereditary_numbers_φ.mpr ⟨ peano_1, null_hereditary ⟩
  -- The class of hereditary numbers contains successors
  have class_has_successors : ∀ (y : Set), y ∈ Numbers.P₂_hereditary_numbers → suc y ∈ Numbers.P₂_hereditary_numbers :=
    fun y => fun y_in_class =>
    have y_is_nbr : is_number y := (Numbers.P₂_hereditary_numbers_φ.mp y_in_class).left
    have y_hereditary : ∀ (x : Class), x ∈ y → is_number x := (Numbers.P₂_hereditary_numbers_φ.mp y_in_class).right
    have suc_is_nbr : is_number (suc y) := peano_2 y_is_nbr
    have suc_hereditary : ∀ (x : Class), x ∈ suc y → is_number x :=
      fun x => fun x_in_suc =>
      Or.elim (successor_possibilities.mp x_in_suc)
        (fun x_in_y => y_hereditary x x_in_y)
        (fun x_eq_y => x_eq_y ▸ y_is_nbr)
    Numbers.P₂_hereditary_numbers_φ.mpr ⟨ suc_is_nbr, suc_hereditary ⟩
  have class_of_hereditary_nbrs_is_set := class_of_nbrs_is_set Numbers.P₂_hereditary_numbers_φ
  ⟨ class_of_hereditary_nbrs_is_set, null_is_in_class, class_has_successors ⟩

theorem peano_4 (n m : Number) : suc n = suc m → n = m :=
  fun h =>
  have n_in_suc_m : n ∈ suc m := h ▸ number_in_successor n
  have m_in_suc_n : m ∈ suc n := h ▸ number_in_successor m
  byContradiction fun (n_not_m : ¬ n = m) =>
    have n_in_m : n ∈ m :=
      have pos : n.val.val ∈ m.val.val ∨ n.val.val = m.val.val := successor_possibilities.mp n_in_suc_m
      have pos' : n ∈ m ∨ n = m := pos.imp_right (fun h => Subtype.ext (Subtype.ext h))
      or_iff_not_imp_right.mp pos' n_not_m
    have m_in_n : m ∈ n :=
      have pos : m.val.val ∈ n.val.val ∨ m.val.val = n.val.val := successor_possibilities.mp m_in_suc_n
      have pos' : m ∈ n ∨ m = n := pos.imp_right (fun h => Subtype.ext (Subtype.ext h))
      have m_not_n : m ≠ n := Ne.symm n_not_m
      or_iff_not_imp_right.mp pos' m_not_n
    absurd ⟨ n_in_m, m_in_n ⟩ (T_3_3 n m)

theorem T_3_4 (n : Number) (x : Class) : x ∈ n → is_number x :=
  /-
  By induction:
  All elements of 0 are numbers, since 0 is empty.
  Suppose k is a number such that all its elements are numbers. Then all elements of (suc k) are numbers,
  since every element of (suc k) is either an element of k or is k itself.
  -/
  fun x_in_n =>
  -- Class of hereditary numbers is inductive. All numbers are in all inductive classes.
  -- So all numbers are hereditary (their elements are numbers).
  have n_is_in_class : n ∈ Numbers.P₂_hereditary_numbers := n.property Numbers.P₂_hereditary_numbers Numbers.class_of_hereditary_nbrs_is_inductive
  (Numbers.P₂_hereditary_numbers_φ.mp n_is_in_class).right x x_in_n

end Numbers
