import Sets.Sets

namespace Structures
open Classes
open Sets

noncomputable def OrdPair (a b : Class) [IsSet a] [IsSet b] := Pair (Single a) (Pair a b)

theorem ord_pair_is_set (a b) [IsSet a] [IsSet b] : OrdPair a b ∈ V := A₄ (Single a) (Pair a b)

theorem L_2_4_3 (a b d) [IsSet a] [IsSet b] [IsSet d] : Pair a b = Pair a d → b = d :=
  fun h =>
  have b_in_first : b ∈ Pair a b := pair_has_right a b
  have b_in_second : b ∈ Pair a d := h ▸ b_in_first
  have b_is_a_or_d : b = a ∨ b = d := (Pair_φ b).mp b_in_second
  Or.elim b_is_a_or_d
    (fun b_eq_a =>
      have a_b_is_single : Pair a b = Single a := by subst b_eq_a; rfl
      have d_in_a_d : d ∈ Pair a d := pair_has_right a d
      have d_in_a_b : d ∈ Pair a b := h ▸ d_in_a_d
      have d_in_single_a : d ∈ Single a := a_b_is_single ▸ d_in_a_b
      have d_eq_a : d = a := in_single d_in_single_a
      eq_comm.mp (b_eq_a ▸ d_eq_a))
    (fun b_eq_d => b_eq_d)

-- Given two classes, there is a particular class called "product"
axiom Product (a b : Class) : Class
axiom Product_φ (A B : Class) : ∀ x, (x ∈ Product A B ↔ (∃ (a : Class) (b : Class) (_ : IsSet a) (_ : IsSet b), x = OrdPair a b ∧ a ∈ A ∧ b ∈ B))

theorem T_2_7_1 (a b) [IsSet a] [IsSet b] : (Product a b) ∈ V :=
  have a_u_b_in_v : a ∪ b ∈ V := union_of_sets_is_set
  haveI : IsSet (a ∪ b) := ⟨ a_u_b_in_v ⟩
  have p_a_u_b_in_v : 𝒫 (a ∪ b) ∈ V := A₆ (a ∪ b)
  haveI : IsSet (𝒫 (a ∪ b)) := ⟨ p_a_u_b_in_v ⟩
  have p_p_a_u_b_in_v : 𝒫 (𝒫 (a ∪ b)) ∈ V := A₆ (𝒫 (a ∪ b))
  have product_is_subclass : Product a b ⊆ 𝒫 (𝒫 (a ∪ b)) :=
    fun x => fun x_in_prod : x ∈ Product a b =>
    have x_is_ord_pair := (Product_φ a b x).mp x_in_prod
    let ⟨ c, d, c_is_set, d_is_set, p ⟩ := x_is_ord_pair
    have c_in_a : c ∈ a := p.right.left
    have d_in_b : d ∈ b := p.right.right
    have x_eq : x = OrdPair c d := p.left
    haveI : IsSet c := c_is_set
    haveI : IsSet d := d_is_set
    have single_c_sub_a_u_b : Single c ⊆ a ∪ b :=
      fun y => fun y_in_single : y ∈ Single c =>
      haveI : IsSet y := ⟨ all_members_are_sets y_in_single ⟩
      have y_eq_c : y = c := in_single y_in_single
      have c_in_a_u_b : c ∈ a ∪ b := (P₂_union_φ a b c).mpr (Or.inl c_in_a)
      by rw [y_eq_c]; exact c_in_a_u_b
    have pair_c_d_sub_a_u_b : Pair c d ⊆ a ∪ b :=
      fun y => fun y_in_pair : y ∈ Pair c d =>
      haveI : IsSet y := ⟨ all_members_are_sets y_in_pair ⟩
      have y_eq : y = c ∨ y = d := (Pair_φ y).mp y_in_pair
      y_eq.elim
        (fun y_eq_c =>
          have c_in_a_u_b : c ∈ a ∪ b := (P₂_union_φ a b c).mpr (Or.inl c_in_a)
          by rw [y_eq_c]; exact c_in_a_u_b)
        (fun y_eq_d =>
          have d_in_a_u_b : d ∈ a ∪ b := (P₂_union_φ a b d).mpr (Or.inr d_in_b)
          by rw [y_eq_d]; exact d_in_a_u_b)
    have single_c_in_power : Single c ∈ 𝒫 (a ∪ b) := (𝒫_φ (a ∪ b) (Single c)).mpr single_c_sub_a_u_b
    have pair_c_d_in_power : Pair c d ∈ 𝒫 (a ∪ b) := (𝒫_φ (a ∪ b) (Pair c d)).mpr pair_c_d_sub_a_u_b
    have x_sub_power : x ⊆ 𝒫 (a ∪ b) :=
      fun z => fun z_in_x : z ∈ x =>
      have x_is_pair : x = Pair (Single c) (Pair c d) := by rw [x_eq]; rfl
      have z_in_pair : z ∈ Pair (Single c) (Pair c d) := by rw [←x_is_pair]; exact z_in_x
      haveI : IsSet z := ⟨ all_members_are_sets z_in_pair ⟩
      have z_eq : z = Single c ∨ z = Pair c d := (Pair_φ z).mp z_in_pair
      z_eq.elim
        (fun z_eq_single => by rw [z_eq_single]; exact single_c_in_power)
        (fun z_eq_pair => by rw [z_eq_pair]; exact pair_c_d_in_power)
    (𝒫_φ (𝒫 (a ∪ b)) x).mpr x_sub_power
  A₂ (Product a b) (𝒫 (𝒫 (a ∪ b))) product_is_subclass p_p_a_u_b_in_v

class IsRelation (r: Class) : Prop where
  prop : r ⊆ Product V V

axiom Dom (r) [IsRelation r] : Class
axiom Dom_φ (r) [IsRelation r] (x) [IsSet x] : x ∈ Dom r ↔ ∃ (y : Class) (_ : IsSet y), (OrdPair x y) ∈ r

class InDom (x r) [IsRelation r] : Prop where
  prop : x ∈ Dom r

theorem in_dom_implies_is_set (x r) [IsRelation r] [InDom x r] : IsSet x :=
  have h := @InDom.prop x r
  ⟨ Sets.all_members_are_sets h ⟩

axiom Ran (r) [IsRelation r] : Class
axiom Ran_φ (r) [IsRelation r] (x) [IsSet x] : x ∈ Ran r ↔ ∃ (y : Class) (_ : IsSet y), (OrdPair y x) ∈ r

class IsFunction (r : Class) [IsRelation r] : Prop where
  prop {x y z} [IsSet x] [IsSet y] [IsSet z] : OrdPair x y ∈ r → OrdPair x z ∈ r → y = z

class Is11Function (r : Class) [IsRelation r] [IsFunction r] : Prop where
  prop {x y x' y'} [IsSet x] [IsSet y] [IsSet x'] [IsSet y'] : OrdPair x x' ∈ r → OrdPair y y' ∈ r → x ≠ y → x' ≠ y'

noncomputable def apply (r x) [IsRelation r] [IsFunction r] [IsSet x] [InDom x r] :
    {y : Class // ∃ (_ : IsSet y), OrdPair x y ∈ r} :=
  ⟨Classical.choose ((Dom_φ r x).mp InDom.prop), Classical.choose_spec ((Dom_φ r x).mp InDom.prop)⟩

noncomputable instance apply_is_set (r x) [IsRelation r] [IsFunction r] [IsSet x] [InDom x r]
    : IsSet (apply r x).val :=
  Classical.choose (apply r x).property

notation:100 f " ⟨ " x " ⟩ " => apply f x

end Structures
