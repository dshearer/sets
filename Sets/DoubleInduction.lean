import Sets.Numbers
import Sets.Structures

namespace DoubleInduction
open Numbers
open Classes
open Sets
open Structures
open Classical

section

variable (m r g : Class) [IsRelation r] [IsRelation g] [IsFunction g]

def is_closed_under (a f : Class) [IsRelation f] [IsFunction f] : Prop :=
  a ⊆ Dom f ∧ ∀ x [IsSet x] [InDom x f], x ∈ a → f⟨x⟩ ∈ a

def is_inductive_under (a f : Class) [IsRelation f] [IsFunction f] : Prop :=
  Null ∈ a ∧ is_closed_under a f

def is_min_inductive_under (a f : Class) [IsRelation f] [IsFunction f] : Prop :=
  is_inductive_under a f ∧ ∀ b, b ⊆ a → is_inductive_under b f → b = a

protected def is_double_ind_relation_1 : Prop :=
  ∀ x [IsSet x], x ∈ m → (OrdPair x Null) ∈ r

protected def is_double_ind_relation_2 : Prop :=
  ∀ x y [IsSet x] [IsSet y] [InDom y g], x ∈ m → y ∈ m → (OrdPair x y) ∈ r → (OrdPair y x) ∈ r → (OrdPair x g⟨y⟩) ∈ r

-- Properties of R in Theorem 4.3 (Double Induction Principle)
protected def is_double_ind_relation : Prop :=
  DoubleInduction.is_double_ind_relation_1 m r ∧ DoubleInduction.is_double_ind_relation_2 m r g

protected def is_left_normal (x) [IsSet x] : Prop :=
  x ∈ m ∧ ∀ y [IsSet y], y ∈ m → (OrdPair x y) ∈ r

protected def is_right_normal (x) [IsSet x] : Prop :=
  x ∈ m ∧ ∀ y [IsSet y], y ∈ m → (OrdPair y x) ∈ r

protected axiom P₂_y_for_which_Rxy (m r x : Class) [IsRelation r] [IsSet x] : Class
protected axiom P₂_y_for_which_Rxy_φ (x y) [IsSet x] [IsSet y] :
  y ∈ DoubleInduction.P₂_y_for_which_Rxy m r x ↔ y ∈ m ∧ (OrdPair x y) ∈ r

protected theorem P₂_y_for_which_Rxy_is_sub (x) [IsSet x] : DoubleInduction.P₂_y_for_which_Rxy m r x ⊆ m :=
  fun y => fun hy =>
  haveI : IsSet y := ⟨ all_members_are_sets hy ⟩
  ((DoubleInduction.P₂_y_for_which_Rxy_φ m r x y).mp hy).left

protected theorem P₂_y_in_m_is_closed (x) [IsSet x] (hm : is_min_inductive_under m g) (hx : DoubleInduction.is_right_normal m r x) (hr : DoubleInduction.is_double_ind_relation m r g) : is_closed_under (DoubleInduction.P₂_y_for_which_Rxy m r x) g :=
  have m_sub_dom : m ⊆ Dom g := hm.1.2.1
  have sub_dom : DoubleInduction.P₂_y_for_which_Rxy m r x ⊆ Dom g :=
    fun y => fun y_in =>
    haveI : IsSet y := ⟨ all_members_are_sets y_in ⟩
    have y_in_m : y ∈ m := ((DoubleInduction.P₂_y_for_which_Rxy_φ m r x y).mp y_in).left
    m_sub_dom y y_in_m
  have closed : ∀ y [IsSet y] [InDom y g], y ∈ DoubleInduction.P₂_y_for_which_Rxy m r x → g⟨y⟩ ∈ DoubleInduction.P₂_y_for_which_Rxy m r x :=
    fun y [IsSet y] [InDom y g] => fun y_in =>
    have Rxy : (OrdPair x y) ∈ r := ((DoubleInduction.P₂_y_for_which_Rxy_φ m r x y).mp y_in).right
    have y_in_m : y ∈ m := ((DoubleInduction.P₂_y_for_which_Rxy_φ m r x y).mp y_in).left
    have Ryx : (OrdPair y x) ∈ r := hx.right y y_in_m
    let gy := g⟨y⟩
    have Rxgy : (OrdPair x gy ∈ r) := hr.right x y hx.left y_in_m Rxy Ryx
    have gy_in_m : gy ∈ m := hm.left.right.right y y_in_m
    (DoubleInduction.P₂_y_for_which_Rxy_φ m r x gy).mpr ⟨ gy_in_m, Rxgy ⟩
  And.intro sub_dom closed

protected theorem P₂_y_in_m_is_inductive (x) [IsSet x] (hm : is_min_inductive_under m g) (hr : DoubleInduction.is_double_ind_relation m r g) (hx : DoubleInduction.is_right_normal m r x) :
  is_inductive_under (DoubleInduction.P₂_y_for_which_Rxy m r x) g :=
  have has_null : Null ∈ (DoubleInduction.P₂_y_for_which_Rxy m r x) :=
    -- // Null ∈ m ∧ (OrdPair x Null) ∈ r
    have null_in_m : Null ∈ m := hm.left.left
    have pair_in_r : (OrdPair x Null) ∈ r := hr.left x hx.left
    (DoubleInduction.P₂_y_for_which_Rxy_φ m r x Null).mpr ⟨ null_in_m, pair_in_r ⟩
  And.intro has_null (DoubleInduction.P₂_y_in_m_is_closed m r g x hm hx hr)

protected theorem DIP_step1 (g x) [IsSet x] [IsRelation g] [IsFunction g] (hm : is_min_inductive_under m g) (hr : DoubleInduction.is_double_ind_relation m r g) : DoubleInduction.is_right_normal m r x → DoubleInduction.is_left_normal m r x :=
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

protected axiom P₂_right_normal_in_m_φ (x : Class) [IsSet x] : x ∈ DoubleInduction.P₂_right_normal_in_m m ↔ x ∈ m ∧ DoubleInduction.is_right_normal m r x

protected theorem P₂_right_normal_in_m_is_inductive (hm : is_min_inductive_under m g) (hr : DoubleInduction.is_double_ind_relation m r g) : is_inductive_under (DoubleInduction.P₂_right_normal_in_m m) g :=
  let k := DoubleInduction.P₂_right_normal_in_m m
  have has_null : Null ∈ k :=
    have null_in_m : Null ∈ m := hm.left.left
    have null_right_normal : DoubleInduction.is_right_normal m r Null :=
      have h : ∀ y [IsSet y], y ∈ m → (OrdPair y Null) ∈ r :=
        fun y => fun y_in_m =>
        hr.left y y_in_m
      And.intro null_in_m h
    (DoubleInduction.P₂_right_normal_in_m_φ m r Null).mpr ⟨null_in_m, null_right_normal⟩
  have is_closed : is_closed_under k g :=
    have m_sub_dom : m ⊆ Dom g := hm.1.2.1
    have sub_dom : k ⊆ Dom g :=
      fun x => fun x_in_k =>
      haveI : IsSet x := ⟨all_members_are_sets x_in_k⟩
      let ⟨ x_in_m, _ ⟩ := ((DoubleInduction.P₂_right_normal_in_m_φ m r x).mp x_in_k)
      m_sub_dom x x_in_m
    have closed : ∀ x [IsSet x] [InDom x g], x ∈ k → g⟨x⟩ ∈ k :=
      fun x [IsSet x] [InDom x g] => fun x_in_k =>
      let ⟨ x_in_m, x_right_normal ⟩ := ((DoubleInduction.P₂_right_normal_in_m_φ m r x).mp x_in_k)
      let gx := g⟨x⟩
      have x_left_normal : DoubleInduction.is_left_normal m r x := DoubleInduction.DIP_step1 m r g x hm hr x_right_normal
      have m_inductive : is_inductive_under m g := hm.left
      have m_closed : is_closed_under m g := m_inductive.right
      have gx_in_m : gx ∈ m := m_closed.right x x_in_m
      have gx_right_normal : DoubleInduction.is_right_normal m r gx :=
        have h : ∀ y [IsSet y], y ∈ m → (OrdPair y gx) ∈ r :=
          fun y => fun y_in_m =>
          have Ryx : (OrdPair y x) ∈ r := x_right_normal.right y y_in_m
          have Rxy : (OrdPair x y) ∈ r := x_left_normal.right y y_in_m
          hr.right y x y_in_m x_in_m Ryx Rxy
        And.intro gx_in_m h
      (DoubleInduction.P₂_right_normal_in_m_φ m r gx).mpr ⟨ gx_in_m, gx_right_normal ⟩
    And.intro sub_dom closed
  And.intro has_null is_closed

protected theorem DIP_step2 (hm : is_min_inductive_under m g) (hr : DoubleInduction.is_double_ind_relation m r g) : ∀ x [IsSet x], x ∈ m → DoubleInduction.is_right_normal m r x :=
  fun x [IsSet x] => fun x_in_m =>
  let all_right_normals := DoubleInduction.P₂_right_normal_in_m m
  have is_sub : all_right_normals ⊆ m :=
    fun x => fun x_in_all_right_normals =>
    haveI : IsSet x := ⟨all_members_are_sets x_in_all_right_normals⟩
    ((DoubleInduction.P₂_right_normal_in_m_φ m r x).mp x_in_all_right_normals).left
  have all_right_normals_is_m : all_right_normals = m := hm.right all_right_normals is_sub (DoubleInduction.P₂_right_normal_in_m_is_inductive m r g hm hr)
  have x_in_all_right_normals : x ∈ all_right_normals := all_right_normals_is_m ▸ x_in_m
  ((DoubleInduction.P₂_right_normal_in_m_φ m r x).mp x_in_all_right_normals).right

theorem DIP : is_min_inductive_under m g → DoubleInduction.is_double_ind_relation m r g → ∀ x y [IsSet x] [IsSet y], x ∈ m → y ∈ m → (OrdPair x y) ∈ r :=
  fun min_ind => fun r_props => fun x y _ _ => fun x_in_m => fun y_in_m =>
  have x_is_right_norm := DoubleInduction.DIP_step2 m r g min_ind r_props x x_in_m
  have x_is_left_norm := DoubleInduction.DIP_step1 m r g x min_ind r_props x_is_right_norm
  x_is_left_norm.right y y_in_m

end

def is_progressing (g) [IsRelation g] [IsFunction g] : Prop := ∀ x [IsSet x] [InDom x g], x ⊆ g⟨x⟩

def are_comparable (a b) [IsSet a] [IsSet b] : Prop := a ⊆ b ∨ b ⊆ a

theorem comparable_is_reflexive (a) [IsSet a] : are_comparable a a := Or.inr subclass_is_reflexive

def is_nest (a: Class) : Prop := ∀ x y [IsSet x] [IsSet y], x ∈ a → y ∈ a → are_comparable x y

abbrev make_relation_φ (a : Class) (p : Class → Class → Prop) := ∀ {x}, x ∈ a ↔ ∃ (y z : Class) (_ : IsSet y) (_ : IsSet z), x = OrdPair y z ∧ p y z

-- Progressing Function Lemma

protected def gx_sub_y_or_y_sub_x (x y g) [IsSet x] [IsSet y] [IsRelation g] [IsFunction g] [InDom x g] := g⟨x⟩ ⊆ y ∨ y ⊆ x

-- For a function g, (R g) is the relation {(x, y) | g⟨x⟩ ⊆ y ∨ y ⊆ x}.
protected def gx_sub_y_or_y_sub_x_P₂ (g) [IsRelation g] [IsFunction g] := P₂ (fun p => ∃ (x y : Class) (_ : IsSet x) (_ : IsSet y) (_ : InDom x g), p = OrdPair x y ∧ DoubleInduction.gx_sub_y_or_y_sub_x x y g)
protected noncomputable def R (g) [IsRelation g] [IsFunction g] : Class := (DoubleInduction.gx_sub_y_or_y_sub_x_P₂ g).choose
protected noncomputable def gx_sub_y_or_y_sub_x_φ (g x) [IsRelation g] [IsFunction g] [IsSet x] := (DoubleInduction.gx_sub_y_or_y_sub_x_P₂ g).choose_spec (x := x)

protected theorem gx_sub_y_or_y_sub_x_φ_pair (g x y) [IsRelation g] [IsFunction g] [IsSet x] [IsSet y] [InDom x g] : OrdPair x y ∈ DoubleInduction.R g ↔ g⟨x⟩ ⊆ y ∨ y ⊆ x :=
  have mp : OrdPair x y ∈ DoubleInduction.R g → g⟨x⟩ ⊆ y ∨ y ⊆ x :=
    fun h =>
    let ⟨ x2, y2, _, _, _, prop ⟩ := (DoubleInduction.gx_sub_y_or_y_sub_x_φ g (OrdPair x y)).mp h
    have gx2_sub_y2_or_y2_sub_x2 := prop.right
    have equals : x = x2 ∧ y = y2 := ord_pair_ident prop.left
    equals.left ▸ equals.right ▸ gx2_sub_y2_or_y2_sub_x2
  have mpr : g⟨x⟩ ⊆ y ∨ y ⊆ x → OrdPair x y ∈ DoubleInduction.R g :=
    fun h =>
    have pair_eq_pair : OrdPair x y = OrdPair x y := rfl
    have prop := And.intro pair_eq_pair h
    have e : ∃ (x1 y1 : Class) (_ : IsSet x1) (_ : IsSet y1) (_ : InDom x1 g), OrdPair x y = OrdPair x1 y1 ∧ (g⟨x1⟩ ⊆ y1 ∨ y1 ⊆ x1) := ⟨ x, y, inferInstance, inferInstance, inferInstance, prop ⟩
    (DoubleInduction.gx_sub_y_or_y_sub_x_φ g (OrdPair x y)).mpr e
  Iff.intro mp mpr

protected instance (g) [IsRelation g] [IsFunction g] : IsRelation (DoubleInduction.R g) where
  prop :=
    let r := DoubleInduction.R g
    fun (p) (p_in_r : p ∈ r) =>
    haveI : IsSet p := ⟨all_members_are_sets p_in_r⟩
    let ⟨ x, y, _, _, _, prop ⟩ := (DoubleInduction.gx_sub_y_or_y_sub_x_φ g p).mp p_in_r
    have p_eq_ordpair: p = OrdPair x y := prop.left
    have p_is_ordpair : is_ord_pair p := ⟨x, y, inferInstance, inferInstance, p_eq_ordpair⟩
    haveI : IsOrdPair p := ⟨p_is_ordpair⟩
    v_x_v_has_all_ord_pairs p

theorem ProgressingFunctionLemma_1 (g) [IsRelation g] [IsFunction g] : ∀ y [IsSet y] [InDom y g], (OrdPair y Null) ∈ DoubleInduction.R g :=
  fun x [x_set : IsSet x] [x_dom : InDom x g] =>
  have null_sub_x : Null ⊆ x := Sets.null_sub_everything x
  have either : g⟨x⟩ ⊆ Null ∨ Null ⊆ x := Or.inr null_sub_x
  have pair_eq : OrdPair x Null = OrdPair x Null := rfl
  have witness : ∃ (y z : Class) (_ : IsSet y) (_ : IsSet z) (_ : InDom y g),
      OrdPair x Null = OrdPair y z ∧ (g⟨y⟩ ⊆ z ∨ z ⊆ y) :=
    ⟨x, Null, x_set, inferInstance, x_dom, pair_eq, either⟩
  (DoubleInduction.gx_sub_y_or_y_sub_x_φ g (OrdPair x Null)).mpr witness

theorem ProgressingFunctionLemma_2 (g) [IsRelation g] [IsFunction g] : ∀ x y [IsSet x] [IsSet y] [InDom x g] [InDom y g], is_progressing g → (OrdPair x y) ∈ DoubleInduction.R g → (OrdPair y x) ∈ DoubleInduction.R g → (OrdPair x g⟨y⟩) ∈ DoubleInduction.R g :=
  fun x y => fun g_progressing => fun xy_in_r => fun yx_in_r =>
  have gx_sub_y_or_y_sub_x : g⟨x⟩ ⊆ y ∨ y ⊆ x := (DoubleInduction.gx_sub_y_or_y_sub_x_φ_pair g x y).mp xy_in_r
  have gy_sub_x_or_x_sub_y : g⟨y⟩ ⊆ x ∨ x ⊆ y := (DoubleInduction.gx_sub_y_or_y_sub_x_φ_pair g y x).mp yx_in_r
  have gx_sub_gy_or_gy_sub_x : g⟨x⟩ ⊆ g⟨y⟩ ∨ g⟨y⟩ ⊆ x :=
    have gx_sub_y_then_r : g⟨x⟩ ⊆ y → (g⟨x⟩ ⊆ g⟨y⟩ ∨ g⟨y⟩ ⊆ x) :=
      fun gx_sub_y =>
      have y_sub_gy : y ⊆ g⟨y⟩ := g_progressing y
      have gx_sub_gy : g⟨x⟩ ⊆ g⟨y⟩ := Classes.subclass_is_transitive gx_sub_y y_sub_gy
      Or.inl gx_sub_gy
    have gy_sub_x_then_r : g⟨y⟩ ⊆ x → (g⟨x⟩ ⊆ g⟨y⟩ ∨ g⟨y⟩ ⊆ x) := fun gy_sub_x => Or.inr gy_sub_x
    have y_sub_x_and_x_sub_y_then_r : (y ⊆ x ∧ x ⊆ y) → (g⟨x⟩ ⊆ g⟨y⟩ ∨ g⟨y⟩ ⊆ x) :=
      fun y_sub_x_and_x_sub_y =>
      have y_eq_x : y = x := Classes.equality_sub.mpr y_sub_x_and_x_sub_y
      have gy_sub_gy : g⟨y⟩ ⊆ g⟨y⟩ := Classes.subclass_is_reflexive
      have gx_sub_gy : g⟨x⟩ ⊆ g⟨y⟩ := y_eq_x ▸ gy_sub_gy
      Or.inl gx_sub_gy
    Or.elim gx_sub_y_or_y_sub_x
      (fun gx_sub_y =>
       have y_sub_gy : y ⊆ g⟨y⟩ := g_progressing y
       have gx_sub_gy : g⟨x⟩ ⊆ g⟨y⟩ := Classes.subclass_is_transitive gx_sub_y y_sub_gy
       Or.inl gx_sub_gy)
      (fun y_sub_x =>
       Or.elim gy_sub_x_or_x_sub_y
        (fun gy_sub_x => Or.inr gy_sub_x)
        (fun x_sub_y =>
         have y_eq_x : y = x := Classes.equality_sub.mpr ⟨ y_sub_x, x_sub_y ⟩
         have gy_sub_gy : g⟨y⟩ ⊆ g⟨y⟩ := Classes.subclass_is_reflexive
         have gx_sub_gy : g⟨x⟩ ⊆ g⟨y⟩ := y_eq_x ▸ gy_sub_gy
         Or.inl gx_sub_gy))
  (DoubleInduction.gx_sub_y_or_y_sub_x_φ_pair g x g⟨y⟩).mpr gx_sub_gy_or_gy_sub_x

theorem P₂_PFL_R_is_double_ind_relation (m g : Class) [IsRelation g] [IsFunction g] (m_sub_dom : m ⊆ Dom g) (g_prog : is_progressing g) : DoubleInduction.is_double_ind_relation m (DoubleInduction.R g) g:=
  let r := DoubleInduction.R g
  have l1 : DoubleInduction.is_double_ind_relation_1 m r :=
    fun x => fun x_in_m =>
    haveI : InDom x g := InDom.mk (m_sub_dom x x_in_m)
    ProgressingFunctionLemma_1 g x
  have l2 : DoubleInduction.is_double_ind_relation_2 m r g :=
    fun x => fun y => fun x_in_m => fun y_in_m => fun xy_in_r => fun yx_in_r =>
    haveI : InDom x g := InDom.mk (m_sub_dom x x_in_m)
    haveI : InDom y g := InDom.mk (m_sub_dom y y_in_m)
    ProgressingFunctionLemma_2 g x y g_prog xy_in_r yx_in_r
  And.intro l1 l2

theorem T_4_4_7 (M g) [IsRelation g] [IsFunction g] : M ⊆ Dom g → is_min_inductive_under M g → is_progressing g →
  (is_nest M ∧ ∀ x y [IsSet x] [IsSet y] [InDom x g], x ∈ M → y ∈ M → DoubleInduction.gx_sub_y_or_y_sub_x x y g) :=

  let r := DoubleInduction.R g
  fun m_sub_domg => fun hm => fun hg =>
  have r_is_double_ind_r : DoubleInduction.is_double_ind_relation M r g := P₂_PFL_R_is_double_ind_relation M g m_sub_domg hg
  have in_r : ∀ x y [IsSet x] [IsSet y] [InDom x g], x ∈ M → y ∈ M → DoubleInduction.gx_sub_y_or_y_sub_x x y g :=
    fun x y _ _ _ x_in_m y_in_m =>
    have xy_in_r : (OrdPair x y) ∈ r := DIP M r g hm r_is_double_ind_r x y x_in_m y_in_m
    let ⟨ a, b, _, _, _, prop ⟩ := (DoubleInduction.gx_sub_y_or_y_sub_x_φ g (OrdPair x y)).mp xy_in_r
    have op_eq_op : OrdPair x y = OrdPair a b := prop.left
    have term_eq : x = a ∧ y = b := ord_pair_ident op_eq_op
    term_eq.right ▸ (term_eq.left ▸ prop.right)
  have m_is_nest : is_nest M :=
    fun (x y) (_ : IsSet x) (_ : IsSet y) (x_in_m) (y_in_m) =>
    haveI : InDom x g := ⟨ m_sub_domg x x_in_m ⟩
    have t1 : DoubleInduction.gx_sub_y_or_y_sub_x x y g := in_r x y x_in_m y_in_m
    Or.elim t1
      (fun gx_sub_y =>
        have x_sub_gx : x ⊆ g⟨x⟩ := hg x
        have x_sub_y : x ⊆ y := subclass_is_transitive x_sub_gx gx_sub_y
        Or.inl x_sub_y)
      (fun y_sub_x => Or.inr y_sub_x)
  And.intro m_is_nest in_r

def is_least (x a) := ∀ y, y ∈ a → x ⊆ y

def is_greatest (x a) := ∀ y, y ∈ a → y ⊆ x

def is_well_ordered_under_inclusion (a) := is_nest a ∧ ∀ b, b ⊆ a → is_non_empty b → ∃ x, is_least x b

protected def proper_subclass (a b : Class) := a ⊆ b ∧ ¬ (b ⊆ a)
infix: 50 " ⊂ " => DoubleInduction.proper_subclass

theorem sub_and_neq_then_ssub {a b} (a_neq_b : a ≠ b) (a_sub_b : a ⊆ b) : a ⊂ b :=
  have not_b_sub_a : ¬ (b ⊆ a) :=
    -- by contradiction
    fun b_sub_a : b ⊆ a =>
    have a_eq_b : a = b := equality_sub.mpr (And.intro a_sub_b b_sub_a)
    a_neq_b a_eq_b
  And.intro a_sub_b not_b_sub_a

section Lemma_4_4_9

variable {N g x y : Class} [IsRelation g] [IsFunction g] [IsSet x] [IsSet y] [InDom x g] [InDom y g]

protected theorem N_is_nest (N_closed : is_closed_under N g) (h : ∀ a b [IsSet a] [IsSet b] [InDom a g], a ∈ N → b ∈ N → DoubleInduction.gx_sub_y_or_y_sub_x a b g) (g_progressing : is_progressing g) : is_nest N :=
  fun a b _ _ a_in_N b_in_N =>
  have N_sub_dom := N_closed.1
  haveI : InDom a g := ⟨ N_sub_dom a a_in_N ⟩
  have h2 : DoubleInduction.gx_sub_y_or_y_sub_x a b g := h a b a_in_N b_in_N
  (em (a = b)).elim
    (fun eq =>
      eq ▸ comparable_is_reflexive a)
    (fun neq =>
      h2.elim
        (fun ga_sub_b =>
          have a_sub_b : a ⊆ b := subclass_is_transitive (g_progressing a) ga_sub_b
          Or.inl a_sub_b)
        (fun b_sub_a => Or.inr b_sub_a)
      )

-- The sandwich principle: If x ⊆ y ⊆ g⟨x⟩ then either x = y or y = g⟨x⟩.
omit [InDom y g] in
theorem L_4_4_9_1 (h : ∀ a b [IsSet a] [IsSet b] [InDom a g], a ∈ N → b ∈ N → DoubleInduction.gx_sub_y_or_y_sub_x a b g) (x_in_N : x ∈ N) (y_in_N : y ∈ N) (x_sub_y : x ⊆ y) (y_sub_gx : y ⊆ g⟨x⟩) : x = y ∨ y = g⟨x⟩ :=
  have gx_sub_y_or_y_sub_x : DoubleInduction.gx_sub_y_or_y_sub_x x y g := h x y x_in_N y_in_N
  gx_sub_y_or_y_sub_x.elim
    (fun gx_sub_y =>
      have y_eq_gx : y = g⟨x⟩ := equality_sub.mpr ⟨ y_sub_gx, gx_sub_y ⟩
      Or.inr y_eq_gx)
    (fun y_sub_x =>
      have x_eq_y : x = y := equality_sub.mpr ⟨ x_sub_y, y_sub_x ⟩
      Or.inl x_eq_y)

-- If x ⊂ y then g⟨x⟩ ⊆ y.
omit [InDom y g] in
theorem L_4_4_9_2 (h : ∀ a b [IsSet a] [IsSet b] [InDom a g], a ∈ N → b ∈ N → DoubleInduction.gx_sub_y_or_y_sub_x a b g) (x_in_N : x ∈ N) (y_in_N : y ∈ N) : x ⊂ y → g⟨x⟩ ⊆ y :=
  fun x_ssub_y =>
    have gx_sub_y_or_y_sub_x : DoubleInduction.gx_sub_y_or_y_sub_x x y g := h x y x_in_N y_in_N
    gx_sub_y_or_y_sub_x.elim
      (fun gx_sub_y => gx_sub_y)
      (fun y_sub_x => False.elim (x_ssub_y.right y_sub_x))

-- If x ⊆ y then g⟨x⟩ ⊆ g⟨y⟩.
theorem L_4_4_9_3 (h : ∀ a b [IsSet a] [IsSet b] [InDom a g], a ∈ N → b ∈ N → DoubleInduction.gx_sub_y_or_y_sub_x a b g) (x_in_N : x ∈ N) (y_in_N : y ∈ N) (g_prog : is_progressing g) : x ⊆ y → g⟨x⟩ ⊆ g⟨y⟩ :=
  fun x_sub_y =>
  (em (x = y)).elim
    (fun x_eq_y =>
      have gx_eq_gy : g⟨x⟩ = g⟨y⟩ := equal_args_equal_values x_eq_y
      (equality_sub.mp gx_eq_gy).left)
    (fun x_neq_y =>
      have x_ssub_y : x ⊂ y := sub_and_neq_then_ssub x_neq_y x_sub_y
      have gx_sub_y : g⟨x⟩ ⊆ y := L_4_4_9_2 h x_in_N y_in_N x_ssub_y
      have y_sub_gy : y ⊆ g⟨y⟩ := g_prog y
      subclass_is_transitive gx_sub_y y_sub_gy)

end Lemma_4_4_9

section Theorem_4_4_10

variable {M g x y : Class} [IsRelation g] [IsFunction g] [IsSet x] [IsSet y] [InDom x g] [InDom y g]

omit [InDom y g] in
theorem T_4_4_10_1 (min_induct : is_min_inductive_under M g) (M_in_g : M ⊆ Dom g) (g_prog : is_progressing g) (x_in_M : x ∈ M) (y_in_M : y ∈ M) (x_sub_y : x ⊆ y) (y_sub_gx : y ⊆ g⟨x⟩) : x = y ∨ y = g⟨x⟩ :=
  have prop := T_4_4_7 M g M_in_g min_induct g_prog
  L_4_4_9_1 prop.right x_in_M y_in_M x_sub_y y_sub_gx

omit [InDom y g] in
theorem T_4_4_10_2 (min_induct : is_min_inductive_under M g) (M_in_g : M ⊆ Dom g) (g_prog : is_progressing g) (x_in_M : x ∈ M) (y_in_M : y ∈ M) (x_ssub_y : x ⊂ y) : g⟨x⟩ ⊆ y :=
  have prop := T_4_4_7 M g M_in_g min_induct g_prog
  L_4_4_9_2 prop.right x_in_M y_in_M x_ssub_y

theorem T_4_4_10_3 (min_induct : is_min_inductive_under M g) (M_in_g : M ⊆ Dom g) (g_prog : is_progressing g) (x_in_M : x ∈ M) (y_in_M : y ∈ M) (x_sub_y : x ⊆ y) : g⟨x⟩ ⊆ g⟨y⟩ :=
  have prop := T_4_4_7 M g M_in_g min_induct g_prog
  L_4_4_9_3 prop.right x_in_M y_in_M g_prog x_sub_y

end Theorem_4_4_10

end DoubleInduction
