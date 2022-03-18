
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

type byte =
| X00
| X01
| X02
| X03
| X04
| X05
| X06
| X07
| X08
| X09
| X0a
| X0b
| X0c
| X0d
| X0e
| X0f
| X10
| X11
| X12
| X13
| X14
| X15
| X16
| X17
| X18
| X19
| X1a
| X1b
| X1c
| X1d
| X1e
| X1f
| X20
| X21
| X22
| X23
| X24
| X25
| X26
| X27
| X28
| X29
| X2a
| X2b
| X2c
| X2d
| X2e
| X2f
| X30
| X31
| X32
| X33
| X34
| X35
| X36
| X37
| X38
| X39
| X3a
| X3b
| X3c
| X3d
| X3e
| X3f
| X40
| X41
| X42
| X43
| X44
| X45
| X46
| X47
| X48
| X49
| X4a
| X4b
| X4c
| X4d
| X4e
| X4f
| X50
| X51
| X52
| X53
| X54
| X55
| X56
| X57
| X58
| X59
| X5a
| X5b
| X5c
| X5d
| X5e
| X5f
| X60
| X61
| X62
| X63
| X64
| X65
| X66
| X67
| X68
| X69
| X6a
| X6b
| X6c
| X6d
| X6e
| X6f
| X70
| X71
| X72
| X73
| X74
| X75
| X76
| X77
| X78
| X79
| X7a
| X7b
| X7c
| X7d
| X7e
| X7f
| X80
| X81
| X82
| X83
| X84
| X85
| X86
| X87
| X88
| X89
| X8a
| X8b
| X8c
| X8d
| X8e
| X8f
| X90
| X91
| X92
| X93
| X94
| X95
| X96
| X97
| X98
| X99
| X9a
| X9b
| X9c
| X9d
| X9e
| X9f
| Xa0
| Xa1
| Xa2
| Xa3
| Xa4
| Xa5
| Xa6
| Xa7
| Xa8
| Xa9
| Xaa
| Xab
| Xac
| Xad
| Xae
| Xaf
| Xb0
| Xb1
| Xb2
| Xb3
| Xb4
| Xb5
| Xb6
| Xb7
| Xb8
| Xb9
| Xba
| Xbb
| Xbc
| Xbd
| Xbe
| Xbf
| Xc0
| Xc1
| Xc2
| Xc3
| Xc4
| Xc5
| Xc6
| Xc7
| Xc8
| Xc9
| Xca
| Xcb
| Xcc
| Xcd
| Xce
| Xcf
| Xd0
| Xd1
| Xd2
| Xd3
| Xd4
| Xd5
| Xd6
| Xd7
| Xd8
| Xd9
| Xda
| Xdb
| Xdc
| Xdd
| Xde
| Xdf
| Xe0
| Xe1
| Xe2
| Xe3
| Xe4
| Xe5
| Xe6
| Xe7
| Xe8
| Xe9
| Xea
| Xeb
| Xec
| Xed
| Xee
| Xef
| Xf0
| Xf1
| Xf2
| Xf3
| Xf4
| Xf5
| Xf6
| Xf7
| Xf8
| Xf9
| Xfa
| Xfb
| Xfc
| Xfd
| Xfe
| Xff

val of_bits :
  (bool, (bool, (bool, (bool, (bool, (bool, (bool, bool) prod) prod) prod)
  prod) prod) prod) prod -> byte

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

val to_N0 : byte -> n

val of_N0 : n -> byte option

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val byte_of_ascii : ascii -> byte

type string =
| EmptyString
| String of ascii * string

val list_ascii_of_string : string -> ascii list

val list_byte_of_string : string -> byte list

val np_total : n -> byte

val log256 : n -> n

val byte_list_from_N_fuel : nat -> n -> byte list

val byte_list_from_N : n -> byte list

val big_endien_list_N : n -> byte list

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

val get_zero_bytes : nat -> byte list

val message_padding : nat -> byte list

val append_zero_in_length_byte : byte list -> byte list

val message_length_byte : byte list -> byte list

val prepared_message : byte list -> byte list

val big_endien_32_bit_to_N : byte -> byte -> byte -> byte -> n

val m : byte list -> nat -> nat -> n

val from_n : nat -> nat list

val upto_n : nat -> nat list

val w : byte list -> nat -> n list

val sha256_intermediate : n list -> n list -> n list

val sha256 : byte list -> n list

val concat_bytes : byte list -> n

val sha256_string : string -> n
