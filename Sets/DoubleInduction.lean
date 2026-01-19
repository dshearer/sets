import Sets.Numbers
import Sets.Structures

namespace DoubleInduction
open Numbers
open Classes
open Sets
open Structures

variable (m r g : Class) [IsRelation r] [IsRelation g] [IsFunction g]

def is_closed_under (a f : Class) [IsRelation f] [IsFunction f] : Prop :=
  ∀ x [IsSet x] [InDom x f], x ∈ a → (f ⟨ x ⟩).val ∈ a

def is_inductive_under (a f : Class) [IsRelation f] [IsFunction f] : Prop :=
  Null ∈ a ∧ is_closed_under a f

def is_min_inductive_under (a f : Class) [IsRelation f] [IsFunction f] : Prop :=
  is_inductive_under a f ∧ ∀ b, b ⊆ a → is_inductive_under b f → b = a

protected def is_double_ind_relation_1 : Prop :=
  ∀ x [IsSet x], x ∈ m → (OrdPair x Null) ∈ r

protected def is_double_ind_relation_2 : Prop :=
  ∀ x y [IsSet x] [IsSet y] [InDom y g], x ∈ m → y ∈ m → (OrdPair x y) ∈ r → (OrdPair y x) ∈ r → (OrdPair x (g ⟨ y ⟩).val) ∈ r

-- Properties of R in Theorem 4.3 (Double Induction Principle)
protected def is_double_ind_relation : Prop :=
  DoubleInduction.is_double_ind_relation_1 m r ∧ DoubleInduction.is_double_ind_relation_2 m r g

def is_left_normal (x) [IsSet x] : Prop :=
  x ∈ m ∧ ∀ y [IsSet y], y ∈ m → (OrdPair x y) ∈ r

def is_right_normal (x) [IsSet x] : Prop :=
  x ∈ m ∧ ∀ y [IsSet y], y ∈ m → (OrdPair y x) ∈ r

protected axiom P₂_y_for_which_Rxy (m r x : Class) [IsRelation r] [IsSet x] : Class
protected axiom P₂_y_for_which_Rxy_φ (x y) [IsSet x] [IsSet y] :
  y ∈ DoubleInduction.P₂_y_for_which_Rxy m r x ↔ y ∈ m ∧ (OrdPair x y) ∈ r

protected theorem P₂_y_for_which_Rxy_is_sub (x) [IsSet x] : DoubleInduction.P₂_y_for_which_Rxy m r x ⊆ m :=
  fun y => fun hy =>
  haveI : IsSet y := ⟨ Sets.all_members_are_sets hy ⟩
  ((DoubleInduction.P₂_y_for_which_Rxy_φ m r x y).mp hy).left

protected theorem P₂_y_in_m_is_closed (x) [IsSet x] (hm : is_min_inductive_under m g) (hx : is_right_normal m r x) (hr : DoubleInduction.is_double_ind_relation m r g) : is_closed_under (DoubleInduction.P₂_y_for_which_Rxy m r x) g :=
  fun y [IsSet y] [InDom y g] => fun y_in =>
  have Rxy : (OrdPair x y) ∈ r := ((DoubleInduction.P₂_y_for_which_Rxy_φ m r x y).mp y_in).right
  have y_in_m : y ∈ m := ((DoubleInduction.P₂_y_for_which_Rxy_φ m r x y).mp y_in).left
  have Ryx : (OrdPair y x) ∈ r := hx.right y y_in_m
  let gy := (g ⟨ y ⟩).val
  have Rxgy : (OrdPair x gy ∈ r) := hr.right x y hx.left y_in_m Rxy Ryx
  have gy_in_m : gy ∈ m := hm.left.right y y_in_m
  (DoubleInduction.P₂_y_for_which_Rxy_φ m r x gy).mpr ⟨ gy_in_m, Rxgy ⟩

protected theorem P₂_y_in_m_is_inductive (x) [IsSet x] (hm : is_min_inductive_under m g) (hr : DoubleInduction.is_double_ind_relation m r g) (hx : is_right_normal m r x) :
  is_inductive_under (DoubleInduction.P₂_y_for_which_Rxy m r x) g :=
  have has_null : Null ∈ (DoubleInduction.P₂_y_for_which_Rxy m r x) :=
    -- // Null ∈ m ∧ (OrdPair x Null) ∈ r
    have null_in_m : Null ∈ m := hm.left.left
    have pair_in_r : (OrdPair x Null) ∈ r := hr.left x hx.left
    (DoubleInduction.P₂_y_for_which_Rxy_φ m r x Null).mpr ⟨ null_in_m, pair_in_r ⟩
  And.intro has_null (DoubleInduction.P₂_y_in_m_is_closed m r g x hm hx hr)

protected theorem DIP_step1 (g x) [IsSet x] [IsRelation g] [IsFunction g] (hm : is_min_inductive_under m g) (hr : DoubleInduction.is_double_ind_relation m r g) : is_right_normal m r x → is_left_normal m r x :=
  fun x_right_norm =>
  let k := (DoubleInduction.P₂_y_for_which_Rxy m r x)
  have k_inductive : is_inductive_under k g := DoubleInduction.P₂_y_in_m_is_inductive m r g x hm hr x_right_norm
  have k_is_m : k = m := hm.right k (DoubleInduction.P₂_y_for_which_Rxy_is_sub m r x) k_inductive
  have right :=
    fun y [IsSet y] => fun y_in_m =>
    have y_in_k : y ∈ k := k_is_m ▸ y_in_m
    have h2 := (DoubleInduction.P₂_y_for_which_Rxy_φ m r x y).mp y_in_k
    h2.right
  have x_in_m : x ∈ m := x_right_norm.left
  And.intro x_in_m right

protected axiom P₂_right_normal_in_m (m : Class) : Class

protected axiom P₂_right_normal_in_m_φ (x : Class) [IsSet x] : x ∈ DoubleInduction.P₂_right_normal_in_m m ↔ x ∈ m ∧ is_right_normal m r x

protected theorem P₂_right_normal_in_m_is_inductive (hm : is_min_inductive_under m g) (hr : DoubleInduction.is_double_ind_relation m r g) : is_inductive_under (DoubleInduction.P₂_right_normal_in_m m) g :=
  let k := DoubleInduction.P₂_right_normal_in_m m
  have has_null : Null ∈ k :=
    have null_in_m : Null ∈ m := hm.left.left
    have null_right_normal : is_right_normal m r Null :=
      have h : ∀ y [IsSet y], y ∈ m → (OrdPair y Null) ∈ r :=
        fun y => fun y_in_m =>
        hr.left y y_in_m
      And.intro null_in_m h
    (DoubleInduction.P₂_right_normal_in_m_φ m r Null).mpr ⟨ null_in_m, null_right_normal ⟩
  have is_closed : is_closed_under k g :=
    fun x => fun x_in_k =>
    let gx := (g ⟨ x ⟩).val
    let ⟨ x_in_m, x_right_normal ⟩ := ((DoubleInduction.P₂_right_normal_in_m_φ m r x).mp x_in_k)
    have x_left_normal : is_left_normal m r x := DoubleInduction.DIP_step1 m r g x hm hr x_right_normal
    have m_inductive : is_inductive_under m g := hm.left
    have m_closed : is_closed_under m g := m_inductive.right
    have gx_in_m : gx ∈ m := m_closed x x_in_m
    have gx_right_normal : is_right_normal m r gx :=
      have h : ∀ y [IsSet y], y ∈ m → (OrdPair y gx) ∈ r :=
        fun y => fun y_in_m =>
        have Ryx : (OrdPair y x) ∈ r := x_right_normal.right y y_in_m
        have Rxy : (OrdPair x y) ∈ r := x_left_normal.right y y_in_m
        hr.right y x y_in_m x_in_m Ryx Rxy
      And.intro gx_in_m h
    (DoubleInduction.P₂_right_normal_in_m_φ m r gx).mpr ⟨ gx_in_m, gx_right_normal ⟩
  And.intro has_null is_closed

protected theorem DIP_step2 (hm : is_min_inductive_under m g) (hr : DoubleInduction.is_double_ind_relation m r g) : ∀ x [IsSet x], x ∈ m → is_right_normal m r x :=
  fun x [IsSet x] => fun x_in_m =>
  let all_right_normals := DoubleInduction.P₂_right_normal_in_m m
  have is_sub : all_right_normals ⊆ m :=
    fun x => fun x_in_all_right_normals =>
    haveI : IsSet x := ⟨ Sets.all_members_are_sets x_in_all_right_normals ⟩
    ((DoubleInduction.P₂_right_normal_in_m_φ m r x).mp x_in_all_right_normals).left
  have all_right_normals_is_m : all_right_normals = m := hm.right all_right_normals is_sub (DoubleInduction.P₂_right_normal_in_m_is_inductive m r g hm hr)
  have x_in_all_right_normals : x ∈ all_right_normals := all_right_normals_is_m ▸ x_in_m
  ((DoubleInduction.P₂_right_normal_in_m_φ m r x).mp x_in_all_right_normals).right

#check DoubleInduction.DIP_step2

theorem DIP : is_min_inductive_under m g → DoubleInduction.is_double_ind_relation m r g → ∀ x y [IsSet x] [IsSet y], x ∈ m → y ∈ m → (OrdPair x y) ∈ r :=
  fun min_ind => fun r_props => fun x y _ _ => fun x_in_m => fun y_in_m =>
  have x_is_right_norm := DoubleInduction.DIP_step2 m r g min_ind r_props x x_in_m
  have x_is_left_norm := DoubleInduction.DIP_step1 m r g x min_ind r_props x_is_right_norm
  x_is_left_norm.right y y_in_m

end DoubleInduction
