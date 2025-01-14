import FMCn.CFR1.Useful
import FMCn.IRI.Bool.Definitions

namespace data

open Bool

theorem if_then_else_true (a a' : α) :
  (if Bool.true then a else a') = a :=
by
  rw [if_then_else]

theorem if_then_else_false (a a' : α) :
  (if Bool.false then a else a') = a' :=
by
  rw [if_then_else]

theorem not_true :
  not true = .false :=
by
  rw [not]

theorem not_false :
  not false = .true :=
by
  rw [not]

theorem not_not_eq_id (b : Bool) :
  not (not b) = b :=
by
  cases b with
  | true => rw [not, not]
  | false => rw [not, not]

theorem and_id (b : Bool) :
  b and true = b ∧ true and b = b :=
by
  cases b with
  | true => refine ⟨rfl, rfl⟩
  | false => refine ⟨rfl, rfl⟩

theorem or_id (b : Bool) :
  b or false = b ∧ false or b = b :=
by
  cases b with
  | true => refine ⟨rfl, rfl⟩
  | false => refine ⟨rfl, rfl⟩

theorem xor_id (b : Bool) :
  b xor false = b ∧ false xor b = b :=
by
  cases b with
  | true => refine ⟨rfl, rfl⟩
  | false => refine ⟨rfl, rfl⟩

theorem and_annul (b : Bool) :
  b and false = .false ∧ false and b = .false :=
by
  cases b with
  | true => refine ⟨rfl, rfl⟩
  | false => refine ⟨rfl, rfl⟩

theorem or_annul (b : Bool) :
  b or true = .true ∧ true or b = .true :=
by
  cases b with
  | true => refine ⟨rfl, rfl⟩
  | false => refine ⟨rfl, rfl⟩

theorem xor_inv (b : Bool) :
  b xor true = not b ∧ true xor b = not b :=
by
  cases b with
  | true => refine ⟨rfl, rfl⟩
  | false => refine ⟨rfl, rfl⟩

theorem nor_eq_not_or (b b' : Bool) :
  b nor b' = not (b or b') :=
by
  rw [bnor, curry_fun, comp_def, uncurry_fun]

theorem nand_eq_not_and (b b' : Bool) :
  b nand b' = not (b and b') :=
by
  rw [bnand, curry_fun, comp_def, uncurry_fun]

theorem xnor_eq_not_xor (b b' : Bool) :
  b xnor b' = not (b xor b') :=
by
  rw [bxnor, curry_fun, comp_def, uncurry_fun]

theorem nand_inv (b : Bool) :
  b nand true = not b ∧ true nand b = not b :=
by
  refine ⟨?_, ?_⟩
  · rw [nand_eq_not_and, (and_id b).1]
  · rw [nand_eq_not_and, (and_id b).2]

theorem nand_denier (b : Bool) :
  b nand false = .true ∧ false nand b = .true :=
by
  refine ⟨?_, ?_⟩
  · rw [nand_eq_not_and, (and_annul b).1, not_false]
  · rw [nand_eq_not_and, (and_annul b).2, not_false]

theorem nor_inv (b : Bool) :
  b nor false = not b ∧ false nor b = not b :=
by
  refine ⟨?_, ?_⟩
  · rw [nor_eq_not_or, (or_id b).1]
  · rw [nor_eq_not_or, (or_id b).2]

theorem nor_denier (b : Bool) :
  b nor true = .false ∧ true nor b = .false :=
by
  refine ⟨?_, ?_⟩
  · rw [nor_eq_not_or, (or_annul b).1, not_true]
  · rw [nor_eq_not_or, (or_annul b).2, not_true]

theorem xnor_id (b : Bool) :
  b xnor true = b ∧ true xnor b = b :=
by
  refine ⟨?_, ?_⟩
  · rw [xnor_eq_not_xor, (xor_inv b).1, not_not_eq_id]
  · rw [xnor_eq_not_xor, (xor_inv b).2, not_not_eq_id]

theorem xnor_inv (b : Bool) :
  b xnor false = not b ∧ false xnor b = not b :=
by
  refine ⟨?_, ?_⟩
  · rw [xnor_eq_not_xor, (xor_id b).1]
  · rw [xnor_eq_not_xor, (xor_id b).2]

theorem and_com (b b' : Bool) :
  b and b' = b' and b :=
by
  cases b with
  | true => rw [(and_id b').2, (and_id b').1]
  | false => rw [(and_annul b').2, (and_annul b').1]

theorem or_com (b b' : Bool) :
  b or b' = b' or b :=
by
  cases b with
  | true => rw [(or_annul b').1, (or_annul b').2]
  | false => rw [(or_id b').1, (or_id b').2]

theorem xor_com (b b' : Bool) :
  b xor b' = b' xor b :=
by
  cases b with
  | true => rw [(xor_inv b').2, (xor_inv b').1]
  | false => rw [(xor_id b').2, (xor_id b').1]

theorem nand_com (b b' : Bool) :
  b nand b' = b' nand b :=
by
  cases b with
  | true => rw [(nand_inv b').1, (nand_inv b').2]
  | false => rw [(nand_denier b').1, (nand_denier b').2]

theorem nor_com (b b' : Bool) :
  b nor b' = b' nor b :=
by
  cases b with
  | true => rw [(nor_denier b').1, (nor_denier b').2]
  | false => rw [(nor_inv b').1, (nor_inv b').2]

theorem xnor_com (b b' : Bool) :
  b xnor b' = b' xnor b :=
by
  cases b with
  | true => rw [(xnor_id b').2, (xnor_id b').1]
  | false => rw [(xnor_inv b').2, (xnor_inv b').1]

theorem xor_not (b b' : Bool) :
  not b xor b' = not (b xor b') :=
by
  cases b with
  | true => rw [not_true, (xor_id b').2, (xor_inv b').2,
                not_not_eq_id]
  | false => rw [not_false, (xor_inv b').2, (xor_id b').2]

theorem or_not (b b' : Bool) :
  not b or b' = not (b and not b') :=
by
  cases b with
  | true => rw [not_true, (or_id b').2,
                (and_id (not b')).2, not_not_eq_id]
  | false => rw [not_false, (or_annul b').2,
                 (and_annul (not b')).2, not_false]

theorem nor_not (b b' : Bool) :
  not b nor b' = b and not b' :=
by
  rw [nor_eq_not_or, or_not, not_not_eq_id]

theorem and_ass (b b' b'' : Bool) :
  (b and b') and b'' = b and (b' and b'') :=
by
  cases b with
  | true => rw [(and_id b').2, (and_id (b' and b'')).2]
  | false => rw [(and_annul b').2, (and_annul b'').2,
                 (and_annul (b' and b'')).2]

theorem or_ass (b b' b'' : Bool) :
  (b or b') or b'' = b or (b' or b'') :=
by
  cases b with
  | true => rw [(or_annul b').2, (or_annul b'').2,
                (or_annul (b' or b'')).2]
  | false => rw [(or_id b').2, (or_id (b' or b'')).2]

theorem xor_ass (b b' b'' : Bool) :
  (b xor b') xor b'' = b xor (b' xor b'') :=
by
  cases b with
  | true => rw [(xor_inv b').2, (xor_inv (b' xor b'')).2,
                xor_not]
  | false => rw [(xor_id b').2, (xor_id (b' xor b'')).2]

theorem and_to_nor (b b' : Bool) :
  b and b' = (not b) nor (not b') :=
by
  cases b with
  | true => rw [not_true, (and_id b').2, (nor_inv (not b')).2,
                not_not_eq_id]
  | false => rw [(and_annul b').2, not_false,
                 (nor_denier (not b')).2]
theorem not_ands_to_nor (b b' : Bool) :
  (not b) and (not b') = b nor b' :=
by
  rw [and_to_nor, not_not_eq_id, not_not_eq_id]

theorem or_to_nor (b b' : Bool) :
  b or b' = not (b nor b') :=
by
  rw [nor_eq_not_or, not_not_eq_id]

theorem and_to_nand (b b' : Bool) :
  b and b' = not (b nand b') :=
by
  rw [nand_eq_not_and, not_not_eq_id]

theorem or_to_nand (b b' : Bool) :
  b or b' = (not b) nand (not b') :=
by
  cases b with
  | true => rw [(or_annul b').2, not_true,
                (nand_denier (not b')).2]
  | false => rw [(or_id b').2, not_false,
                 (nand_inv (not b')).2, not_not_eq_id]

theorem xor_to_or (b b' : Bool) :
  b xor b' = (b and not b') or (not b and b') :=
by
  cases b with
  | true => rw [(xor_inv b').2, (and_id (not b')).2, not_true,
                (and_annul b').2, (or_id (not b')).1]
  | false => rw [(xor_id b').2, (and_annul (not b')).2, not_false,
                 (and_id b').2, (or_id b').2]

theorem not_eq_nand (b : Bool) :
  not b = b nand b :=
by
  cases b with
  | true => rw [(nand_inv true).1]
  | false => rw [nand_eq_not_and, (and_annul false).1]

theorem not_eq_nor (b : Bool) :
  not b = b nor b :=
by
  cases b with
  | true => rw [nor_eq_not_or, (or_annul true).1]
  | false => rw [nor_eq_not_or, (or_id false).1]

theorem silly (A B C D : Bool) :
  (not A) or (B and C and (not D)) = not ((not A) nor ((not B) nor (not ((not C) nor D)))) :=
by
  rw [or_to_nor, and_to_nor, and_to_nor, not_not_eq_id]
  cases B with
  | true => rw [not_true, (nor_inv (not (not C nor D))).2,
                (nor_inv (not C)).2, not_not_eq_id,
                not_not_eq_id]
  | false => rw [not_false, (nor_denier (not C)).2,
                 (nor_denier (not (not C nor D))).2,
                 not_false, (nor_denier D).2]

theorem sillier (A B C D E : Bool) :
  (A and (B or C)) or (D and E) = (A nand ((not B) nand (not C))) nand (D nand E) :=
by
  rw [and_to_nand, and_to_nand, or_to_nand, or_to_nand,
      not_not_eq_id, not_not_eq_id]
