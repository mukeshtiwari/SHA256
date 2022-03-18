
type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

module Nat :
 sig
  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool
 end

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred_N : positive -> n

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val pow : positive -> positive -> positive

  val size : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> n

  val coq_lxor : positive -> positive -> n

  val shiftl : positive -> n -> positive

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_succ_nat : nat -> positive
 end

module N :
 sig
  val succ_double : n -> n

  val double : n -> n

  val pred : n -> n

  val add : n -> n -> n

  val sub : n -> n -> n

  val mul : n -> n -> n

  val compare : n -> n -> comparison

  val leb : n -> n -> bool

  val div2 : n -> n

  val pow : n -> n -> n

  val log2 : n -> n

  val pos_div_eucl : positive -> n -> (n, n) prod

  val div_eucl : n -> n -> (n, n) prod

  val div : n -> n -> n

  val modulo : n -> n -> n

  val coq_lor : n -> n -> n

  val coq_land : n -> n -> n

  val coq_lxor : n -> n -> n

  val shiftl : n -> n -> n

  val shiftr : n -> n -> n

  val to_nat : n -> nat

  val of_nat : nat -> n

  val ones : n -> n

  val lnot : n -> n -> n
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val to_N : z -> n

  val of_N : n -> z

  val pos_div_eucl : positive -> z -> (z, z) prod

  val div_eucl : z -> z -> (z, z) prod

  val modulo : z -> z -> z
 end

val to_N0 : char -> n

val of_N0 : n -> char option

val list_ascii_of_string : char list -> char list

val list_byte_of_string : char list -> char list

val np_total : n -> char

val log256 : n -> n

val byte_list_from_N_fuel : nat -> n -> char list

val byte_list_from_N : n -> char list

val big_endien_list_N : n -> char list

val word : n

val add0 : n -> n -> n

val shift_left : n -> n -> n

val shift_right : n -> n -> n

val bitwise_and : n -> n -> n

val bitwise_or : n -> n -> n

val bitwise_xor : n -> n -> n

val bitwise_neg : n -> n

val rOTR : n -> n -> n

val sHR : n -> n -> n

val ch : n -> n -> n -> n

val maj : n -> n -> n -> n

val sigma_UU2080_ : n -> n

val sigma_UU2081_ : n -> n

val sigma_UU2080_0 : n -> n

val sigma_UU2081_0 : n -> n

val h_UU2080_ : n list

val k : n list

val get_zero_bytes : nat -> char list

val message_padding : nat -> char list

val append_zero_in_length_byte : char list -> char list

val message_length_byte : char list -> char list

val prepared_message : char list -> char list

val big_endien_32_bit_to_N : char -> char -> char -> char -> n

val m : char list -> nat -> nat -> n

val from_n : nat -> nat list

val upto_n : nat -> nat list

val w : char list -> nat -> n list

val sha256_intermediate : n list -> n list -> n list

val sha256 : char list -> n list

val concat_bytes : char list -> n

val sha256_string : char list -> n
