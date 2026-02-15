import Sets.Sets

namespace Structures
open Classes
open Sets

noncomputable def OrdPair (a b : Class) [IsSet a] [IsSet b] : Class := Pair (Single a) (Pair a b)

def is_ord_pair (a : Class) : Prop := ∃ (x y : Class) (_ : IsSet x) (_ : IsSet y), a = OrdPair x y

class IsOrdPair (a) where
  prop : is_ord_pair a

instance (a b) [IsSet a] [IsSet b] : IsOrdPair (OrdPair a b) where
  prop := ⟨ a, b, inferInstance, inferInstance, rfl ⟩

instance {p} (h : is_ord_pair p) : IsOrdPair p where
  prop := h

instance (a) [IsOrdPair a] : IsPair a where
  prop :=
    let ⟨ x, y, x_is_set, y_is_set, a_eq_ordpair ⟩ := IsOrdPair.prop (a := a)
    haveI : IsSet x := x_is_set
    haveI : IsSet y := y_is_set
    ⟨Single x, Pair x y, inferInstance, inferInstance, a_eq_ordpair⟩

instance (a) [IsOrdPair a] : IsSet a where
  in_v := A₄ a

theorem L_2_4_3 {a b d} [IsSet a] [IsSet b] [IsSet d] (h : Pair a b = Pair a d) : b = d :=
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

theorem ord_pair_ident {a b c d} [IsSet a] [IsSet b] [IsSet c] [IsSet d] (h : OrdPair a b = OrdPair c d) : a = c ∧ b = d :=
  have t : Pair (Single a) (Pair a b) = Pair (Single c) (Pair c d) := h
  have single_a_eq_single_c : Single a = Single c :=
    have t1 : Single a ∈ Pair (Single a) (Pair a b) := pair_has_left (Single a) (Pair a b)
    have t2 : Single a ∈ Pair (Single c) (Pair c d) := t ▸ t1
    have t3 : Single a = Single c ∨ Single a = Pair c d := in_pair t2
    Or.elim t3
      (fun single_a_eq_single_c => single_a_eq_single_c)
      (fun single_a_eq_pair =>
        have t4 : a = c ∧ a = d := single_pair_eq single_a_eq_pair
        have t5 : Single a = Single a := rfl
        t4.left ▸ t5)
  have pair_ab_eq_pair_cd : Pair a b = Pair c d :=
    have t1 : Pair a b ∈ Pair (Single a) (Pair a b) := pair_has_right (Single a) (Pair a b)
    have t2 : Pair a b ∈ Pair (Single c) (Pair c d) := t ▸ t1
    have t3 : Pair a b = Single c ∨ Pair a b = Pair c d := in_pair t2
    t3.elim
      (fun pair_ab_eq_single_c =>
        -- When Pair a b = Single c, we show that Single c = Pair c d
        have single_c_eq_pair_cd : Single c = Pair c d := by
          -- From t and substitutions, derive Pair (Single c) (Single c) = Pair (Single c) (Pair c d)
          have h1 : Pair (Single a) (Single c) = Pair (Single c) (Pair c d) := by
            calc Pair (Single a) (Single c)
              = Pair (Single a) (Pair a b) := by simp [pair_ab_eq_single_c]
              _ = Pair (Single c) (Pair c d) := t
          have h2 : Pair (Single c) (Single c) = Pair (Single c) (Pair c d) := by
            calc Pair (Single c) (Single c)
              = Pair (Single a) (Single c) := by simp [single_a_eq_single_c]
              _ = Pair (Single c) (Pair c d) := h1
          exact L_2_4_3 h2
        Eq.trans pair_ab_eq_single_c single_c_eq_pair_cd)
      (fun pair_ab_eq_pair_cd => pair_ab_eq_pair_cd)
  have a_eq_c : a = c := single_id single_a_eq_single_c
  have pair_ab_eq_pair_ad : Pair a b = Pair a d := a_eq_c ▸ pair_ab_eq_pair_cd
  have b_eq_d : b = d := L_2_4_3 pair_ab_eq_pair_ad
  ⟨ a_eq_c, b_eq_d ⟩

-- Given two classes, there is a particular class called "product"

protected def product_P₂ (A B) := P₂ (fun x => ∃ (a : Class) (b : Class) (_ : IsSet a) (_ : IsSet b), x = OrdPair a b ∧ a ∈ A ∧ b ∈ B)
noncomputable def Product (A B) := (Structures.product_P₂ A B).choose
noncomputable def Product_φ (A B x) [IsSet x] := (Structures.product_P₂ A B).choose_spec (x := x)

theorem T_2_7_1 (a b) [IsSet a] [IsSet b] : (Product a b) ∈ V :=
  have a_u_b_in_v : a ∪ b ∈ V := union_of_sets_in_v
  haveI : IsSet (a ∪ b) := ⟨ a_u_b_in_v ⟩
  have p_a_u_b_in_v : 𝒫 (a ∪ b) ∈ V := A₆ (a ∪ b)
  haveI : IsSet (𝒫 (a ∪ b)) := ⟨ p_a_u_b_in_v ⟩
  have p_p_a_u_b_in_v : 𝒫 (𝒫 (a ∪ b)) ∈ V := A₆ (𝒫 (a ∪ b))
  have product_is_subclass : Product a b ⊆ 𝒫 (𝒫 (a ∪ b)) :=
    fun x => fun x_in_prod : x ∈ Product a b =>
    haveI : IsSet x := ⟨ all_members_are_sets x_in_prod ⟩
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
      have c_in_a_u_b : c ∈ a ∪ b := (union_φ a b c).mpr (Or.inl c_in_a)
      by rw [y_eq_c]; exact c_in_a_u_b
    have pair_c_d_sub_a_u_b : Pair c d ⊆ a ∪ b :=
      fun y => fun y_in_pair : y ∈ Pair c d =>
      haveI : IsSet y := ⟨ all_members_are_sets y_in_pair ⟩
      have y_eq : y = c ∨ y = d := (Pair_φ y).mp y_in_pair
      y_eq.elim
        (fun y_eq_c =>
          have c_in_a_u_b : c ∈ a ∪ b := (union_φ a b c).mpr (Or.inl c_in_a)
          by rw [y_eq_c]; exact c_in_a_u_b)
        (fun y_eq_d =>
          have d_in_a_u_b : d ∈ a ∪ b := (union_φ a b d).mpr (Or.inr d_in_b)
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
    haveI : IsSet x := ⟨ all_members_are_sets x_in_prod ⟩
    (𝒫_φ (𝒫 (a ∪ b)) x).mpr x_sub_power
  A₂ (Product a b) (𝒫 (𝒫 (a ∪ b))) product_is_subclass p_p_a_u_b_in_v

class IsRelation (r: Class) : Prop where
  prop : r ⊆ Product V V

theorem v_x_v_has_all_ord_pairs (p) [IsOrdPair p] : p ∈ Product V V :=
  let ⟨ x, y, x_is_set, y_is_set, prop ⟩ := IsOrdPair.prop (a := p)
  haveI : IsSet x := x_is_set
  haveI : IsSet y := y_is_set
  have x_in_v : x ∈ V := x_is_set.in_v
  have y_in_v : y ∈ V := y_is_set.in_v
  have cond : p = OrdPair x y ∧ x ∈ V ∧ y ∈ V := And.intro prop (And.intro x_in_v y_in_v)
  have exists_cond : ∃ (a b : Class) (_ : IsSet a) (_: IsSet b), (p = OrdPair a b ∧ a ∈ V ∧ b ∈ V) := ⟨ x, y, inferInstance, inferInstance, cond ⟩
  haveI : IsSet p := inferInstance
  (Product_φ V V p).mpr exists_cond

protected def dom_P₂ (r) [IsRelation r] := P₂ (fun x => ∃ (y : Class) (_ : IsSet y), (OrdPair x y) ∈ r)
noncomputable def Dom (r) [IsRelation r] : Class := (Structures.dom_P₂ r).choose
noncomputable def Dom_φ (r x) [IsRelation r] [IsSet x] := (Structures.dom_P₂ r).choose_spec (x := x)

class InDom (x r) [IsRelation r] : Prop where
  prop : x ∈ Dom r

theorem in_dom_implies_is_set (x r) [IsRelation r] [InDom x r] : IsSet x :=
  have h := @InDom.prop x r
  ⟨ all_members_are_sets h ⟩

protected def ran_P₂ (r) [IsRelation r] := P₂ (fun x => ∃ (y : Class) (_ : IsSet x) (_ : IsSet y), (OrdPair y x) ∈ r)
noncomputable def Ran (r) [IsRelation r] : Class := (Structures.ran_P₂ r).choose
noncomputable def Ran_φ (r x) [IsRelation r] [IsSet x] := (Structures.ran_P₂ r).choose_spec (x := x)

class IsFunction (r : Class) [IsRelation r] : Prop where
  prop {x y z} [IsSet x] [IsSet y] [IsSet z] : OrdPair x y ∈ r → OrdPair x z ∈ r → y = z

class Is11Function (r : Class) [IsRelation r] [IsFunction r] : Prop where
  prop {x y x' y'} [IsSet x] [IsSet y] [IsSet x'] [IsSet y'] : OrdPair x x' ∈ r → OrdPair y y' ∈ r → x ≠ y → x' ≠ y'

noncomputable def apply (r x) [IsRelation r] [IsFunction r] [IsSet x] [InDom x r] :
    {y : Class // ∃ (_ : IsSet y), OrdPair x y ∈ r} :=
  have x_in_dom : x ∈ Dom r := InDom.prop
  have y_exists := (Structures.Dom_φ r x).mp x_in_dom
  ⟨ Classical.choose y_exists, Classical.choose_spec y_exists ⟩

noncomputable instance apply_is_set (r x) [IsRelation r] [IsFunction r] [IsSet x] [InDom x r]
    : IsSet (apply r x).val :=
  let ⟨ y_is_set, _ ⟩ := (apply r x).property
  y_is_set

set_option quotPrecheck false in
notation:10000 f "⟨" x "⟩" => (apply f x).val

theorem fun_apply (f x) [IsRelation f] [IsFunction f] [IsSet x] [InDom x f] : (OrdPair x f⟨x⟩) ∈ f :=
  let ⟨ _, ord_pair_in_f ⟩ := (apply f x).property
  ord_pair_in_f

theorem equal_args_equal_values {f x y} [IsRelation f] [IsFunction f] [IsSet x] [IsSet y] [InDom x f] [InDom y f] (x_eq_y : x = y) : f⟨x⟩ = f⟨y⟩ :=
  have fx_eq_fx : f⟨x⟩ = f⟨x⟩ := rfl
  x_eq_y ▸ fx_eq_fx

-- Subtraction

protected def subtract_P₂ (a x : Class) [IsSet x] := P₂ (fun y => y ∈ a ∧ y ≠ x)
protected noncomputable def subtract (a x : Class) [IsSet x] : Class := (Structures.subtract_P₂ a x).choose
noncomputable def subtract_φ (a x y : Class) [IsSet x] [IsSet y] := (Structures.subtract_P₂ a x).choose_spec (x := y)

infix:60 " - " => Structures.subtract

theorem subtract_is_sub {a x : Class} [IsSet x] : a - x ⊆ a :=
  fun y => fun y_in_asx =>
  haveI : IsSet y := ⟨ all_members_are_sets y_in_asx ⟩
  have y_in_a : y ∈ a := ((subtract_φ a x y).mp y_in_asx).left
  y_in_a

instance {a x : Class} [IsSet a] [IsSet x] : IsSet (a - x) where
  in_v := A₂ (a - x) a subtract_is_sub (IsSet.in_v)

end Structures
