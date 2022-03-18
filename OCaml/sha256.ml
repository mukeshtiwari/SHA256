
type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m0 =
  match l with
  | Nil -> m0
  | Cons (a, l1) -> Cons (a, (app l1 m0))

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)
 let rec add n0 m0 =
   match n0 with
   | O -> m0
   | S p -> S (add p m0)
end
include Coq__1

(** val mul : nat -> nat -> nat **)

let rec mul n0 m0 =
  match n0 with
  | O -> O
  | S p -> add m0 (mul p m0)

(** val sub : nat -> nat -> nat **)

let rec sub n0 m0 =
  match n0 with
  | O -> n0
  | S k0 -> (match m0 with
             | O -> n0
             | S l -> sub k0 l)

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

(** val of_bits :
    (bool, (bool, (bool, (bool, (bool, (bool, (bool, bool) prod) prod) prod)
    prod) prod) prod) prod -> byte **)

let of_bits = function
| Pair (b0, p) ->
  if b0
  then let Pair (b1, p0) = p in
       if b1
       then let Pair (b2, p1) = p0 in
            if b2
            then let Pair (b3, p2) = p1 in
                 if b3
                 then let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xff else X7f
                                else if b7 then Xbf else X3f
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xdf else X5f
                                else if b7 then X9f else X1f
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xef else X6f
                                else if b7 then Xaf else X2f
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xcf else X4f
                                else if b7 then X8f else X0f
                 else let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xf7 else X77
                                else if b7 then Xb7 else X37
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xd7 else X57
                                else if b7 then X97 else X17
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xe7 else X67
                                else if b7 then Xa7 else X27
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xc7 else X47
                                else if b7 then X87 else X07
            else let Pair (b3, p2) = p1 in
                 if b3
                 then let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xfb else X7b
                                else if b7 then Xbb else X3b
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xdb else X5b
                                else if b7 then X9b else X1b
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xeb else X6b
                                else if b7 then Xab else X2b
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xcb else X4b
                                else if b7 then X8b else X0b
                 else let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xf3 else X73
                                else if b7 then Xb3 else X33
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xd3 else X53
                                else if b7 then X93 else X13
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xe3 else X63
                                else if b7 then Xa3 else X23
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xc3 else X43
                                else if b7 then X83 else X03
       else let Pair (b2, p1) = p0 in
            if b2
            then let Pair (b3, p2) = p1 in
                 if b3
                 then let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xfd else X7d
                                else if b7 then Xbd else X3d
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xdd else X5d
                                else if b7 then X9d else X1d
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xed else X6d
                                else if b7 then Xad else X2d
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xcd else X4d
                                else if b7 then X8d else X0d
                 else let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xf5 else X75
                                else if b7 then Xb5 else X35
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xd5 else X55
                                else if b7 then X95 else X15
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xe5 else X65
                                else if b7 then Xa5 else X25
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xc5 else X45
                                else if b7 then X85 else X05
            else let Pair (b3, p2) = p1 in
                 if b3
                 then let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xf9 else X79
                                else if b7 then Xb9 else X39
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xd9 else X59
                                else if b7 then X99 else X19
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xe9 else X69
                                else if b7 then Xa9 else X29
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xc9 else X49
                                else if b7 then X89 else X09
                 else let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xf1 else X71
                                else if b7 then Xb1 else X31
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xd1 else X51
                                else if b7 then X91 else X11
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xe1 else X61
                                else if b7 then Xa1 else X21
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xc1 else X41
                                else if b7 then X81 else X01
  else let Pair (b1, p0) = p in
       if b1
       then let Pair (b2, p1) = p0 in
            if b2
            then let Pair (b3, p2) = p1 in
                 if b3
                 then let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xfe else X7e
                                else if b7 then Xbe else X3e
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xde else X5e
                                else if b7 then X9e else X1e
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xee else X6e
                                else if b7 then Xae else X2e
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xce else X4e
                                else if b7 then X8e else X0e
                 else let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xf6 else X76
                                else if b7 then Xb6 else X36
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xd6 else X56
                                else if b7 then X96 else X16
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xe6 else X66
                                else if b7 then Xa6 else X26
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xc6 else X46
                                else if b7 then X86 else X06
            else let Pair (b3, p2) = p1 in
                 if b3
                 then let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xfa else X7a
                                else if b7 then Xba else X3a
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xda else X5a
                                else if b7 then X9a else X1a
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xea else X6a
                                else if b7 then Xaa else X2a
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xca else X4a
                                else if b7 then X8a else X0a
                 else let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xf2 else X72
                                else if b7 then Xb2 else X32
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xd2 else X52
                                else if b7 then X92 else X12
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xe2 else X62
                                else if b7 then Xa2 else X22
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xc2 else X42
                                else if b7 then X82 else X02
       else let Pair (b2, p1) = p0 in
            if b2
            then let Pair (b3, p2) = p1 in
                 if b3
                 then let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xfc else X7c
                                else if b7 then Xbc else X3c
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xdc else X5c
                                else if b7 then X9c else X1c
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xec else X6c
                                else if b7 then Xac else X2c
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xcc else X4c
                                else if b7 then X8c else X0c
                 else let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xf4 else X74
                                else if b7 then Xb4 else X34
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xd4 else X54
                                else if b7 then X94 else X14
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xe4 else X64
                                else if b7 then Xa4 else X24
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xc4 else X44
                                else if b7 then X84 else X04
            else let Pair (b3, p2) = p1 in
                 if b3
                 then let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xf8 else X78
                                else if b7 then Xb8 else X38
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xd8 else X58
                                else if b7 then X98 else X18
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xe8 else X68
                                else if b7 then Xa8 else X28
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xc8 else X48
                                else if b7 then X88 else X08
                 else let Pair (b4, p3) = p2 in
                      if b4
                      then let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xf0 else X70
                                else if b7 then Xb0 else X30
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xd0 else X50
                                else if b7 then X90 else X10
                      else let Pair (b5, p4) = p3 in
                           if b5
                           then let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xe0 else X60
                                else if b7 then Xa0 else X20
                           else let Pair (b6, b7) = p4 in
                                if b6
                                then if b7 then Xc0 else X40
                                else if b7 then X80 else X00

module Nat =
 struct
  (** val leb : nat -> nat -> bool **)

  let rec leb n0 m0 =
    match n0 with
    | O -> true
    | S n' -> (match m0 with
               | O -> false
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n0 m0 =
    leb (S n0) m0
 end

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n0 l default =
  match n0 with
  | O -> (match l with
          | Nil -> default
          | Cons (x, _) -> x)
  | S m0 -> (match l with
             | Nil -> default
             | Cons (_, t) -> nth m0 t default)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t) -> Cons ((f a), (map f t))

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| Nil -> Nil
| Cons (x, t) -> app (f x) (flat_map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | Nil -> a0
  | Cons (b, t) -> fold_left f t (f a0 b)

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

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val pow : positive -> positive -> positive **)

  let pow x =
    iter (mul x) XH

  (** val size : positive -> positive **)

  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH -> (match q with
             | XO q0 -> XI q0
             | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH -> (match q with
             | XO _ -> N0
             | _ -> Npos XH)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)

  (** val shiftl : positive -> n -> positive **)

  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter (fun x -> XO x) p n1

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module N =
 struct
  (** val succ_double : n -> n **)

  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val double : n -> n **)

  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val pred : n -> n **)

  let pred = function
  | N0 -> N0
  | Npos p -> Coq_Pos.pred_N p

  (** val add : n -> n -> n **)

  let add n0 m0 =
    match n0 with
    | N0 -> m0
    | Npos p -> (match m0 with
                 | N0 -> n0
                 | Npos q -> Npos (Coq_Pos.add p q))

  (** val sub : n -> n -> n **)

  let sub n0 m0 =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m0 with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val mul : n -> n -> n **)

  let mul n0 m0 =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m0 with
                 | N0 -> N0
                 | Npos q -> Npos (Coq_Pos.mul p q))

  (** val compare : n -> n -> comparison **)

  let compare n0 m0 =
    match n0 with
    | N0 -> (match m0 with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m0 with
                  | N0 -> Gt
                  | Npos m' -> Coq_Pos.compare n' m')

  (** val leb : n -> n -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val div2 : n -> n **)

  let div2 = function
  | N0 -> N0
  | Npos p0 -> (match p0 with
                | XI p -> Npos p
                | XO p -> Npos p
                | XH -> N0)

  (** val pow : n -> n -> n **)

  let pow n0 = function
  | N0 -> Npos XH
  | Npos p0 -> (match n0 with
                | N0 -> N0
                | Npos q -> Npos (Coq_Pos.pow q p0))

  (** val log2 : n -> n **)

  let log2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | XI p -> Npos (Coq_Pos.size p)
     | XO p -> Npos (Coq_Pos.size p)
     | XH -> N0)

  (** val pos_div_eucl : positive -> n -> (n, n) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r'
      then Pair ((succ_double q), (sub r' b))
      else Pair ((double q), r')
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r'
      then Pair ((succ_double q), (sub r' b))
      else Pair ((double q), r')
    | XH ->
      (match b with
       | N0 -> Pair (N0, (Npos XH))
       | Npos p ->
         (match p with
          | XH -> Pair ((Npos XH), N0)
          | _ -> Pair (N0, (Npos XH))))

  (** val div_eucl : n -> n -> (n, n) prod **)

  let div_eucl a b =
    match a with
    | N0 -> Pair (N0, N0)
    | Npos na ->
      (match b with
       | N0 -> Pair (N0, a)
       | Npos _ -> pos_div_eucl na b)

  (** val div : n -> n -> n **)

  let div a b =
    fst (div_eucl a b)

  (** val modulo : n -> n -> n **)

  let modulo a b =
    snd (div_eucl a b)

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m0 =
    match n0 with
    | N0 -> m0
    | Npos p ->
      (match m0 with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m0 =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m0 with
                 | N0 -> N0
                 | Npos q -> Coq_Pos.coq_land p q)

  (** val coq_lxor : n -> n -> n **)

  let coq_lxor n0 m0 =
    match n0 with
    | N0 -> m0
    | Npos p -> (match m0 with
                 | N0 -> n0
                 | Npos q -> Coq_Pos.coq_lxor p q)

  (** val shiftl : n -> n -> n **)

  let shiftl a n0 =
    match a with
    | N0 -> N0
    | Npos a0 -> Npos (Coq_Pos.shiftl a0 n0)

  (** val shiftr : n -> n -> n **)

  let shiftr a = function
  | N0 -> a
  | Npos p -> Coq_Pos.iter div2 a p

  (** val to_nat : n -> nat **)

  let to_nat = function
  | N0 -> O
  | Npos p -> Coq_Pos.to_nat p

  (** val of_nat : nat -> n **)

  let of_nat = function
  | O -> N0
  | S n' -> Npos (Coq_Pos.of_succ_nat n')

  (** val ones : n -> n **)

  let ones n0 =
    pred (shiftl (Npos XH) n0)

  (** val lnot : n -> n -> n **)

  let lnot a n0 =
    coq_lxor a (ones n0)
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Coq_Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m0 n0 =
    add m0 (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val to_N : z -> n **)

  let to_N = function
  | Zpos p -> Npos p
  | _ -> N0

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val pos_div_eucl : positive -> z -> (z, z) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then Pair ((mul (Zpos (XO XH)) q), r')
      else Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then Pair ((mul (Zpos (XO XH)) q), r')
      else Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XH ->
      if leb (Zpos (XO XH)) b
      then Pair (Z0, (Zpos XH))
      else Pair ((Zpos XH), Z0)

  (** val div_eucl : z -> z -> (z, z) prod **)

  let div_eucl a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos _ ->
         let Pair (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in Pair (q, (opp r)))

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let Pair (_, r) = div_eucl a b in r
 end

(** val to_N0 : byte -> n **)

let to_N0 = function
| X00 -> N0
| X01 -> Npos XH
| X02 -> Npos (XO XH)
| X03 -> Npos (XI XH)
| X04 -> Npos (XO (XO XH))
| X05 -> Npos (XI (XO XH))
| X06 -> Npos (XO (XI XH))
| X07 -> Npos (XI (XI XH))
| X08 -> Npos (XO (XO (XO XH)))
| X09 -> Npos (XI (XO (XO XH)))
| X0a -> Npos (XO (XI (XO XH)))
| X0b -> Npos (XI (XI (XO XH)))
| X0c -> Npos (XO (XO (XI XH)))
| X0d -> Npos (XI (XO (XI XH)))
| X0e -> Npos (XO (XI (XI XH)))
| X0f -> Npos (XI (XI (XI XH)))
| X10 -> Npos (XO (XO (XO (XO XH))))
| X11 -> Npos (XI (XO (XO (XO XH))))
| X12 -> Npos (XO (XI (XO (XO XH))))
| X13 -> Npos (XI (XI (XO (XO XH))))
| X14 -> Npos (XO (XO (XI (XO XH))))
| X15 -> Npos (XI (XO (XI (XO XH))))
| X16 -> Npos (XO (XI (XI (XO XH))))
| X17 -> Npos (XI (XI (XI (XO XH))))
| X18 -> Npos (XO (XO (XO (XI XH))))
| X19 -> Npos (XI (XO (XO (XI XH))))
| X1a -> Npos (XO (XI (XO (XI XH))))
| X1b -> Npos (XI (XI (XO (XI XH))))
| X1c -> Npos (XO (XO (XI (XI XH))))
| X1d -> Npos (XI (XO (XI (XI XH))))
| X1e -> Npos (XO (XI (XI (XI XH))))
| X1f -> Npos (XI (XI (XI (XI XH))))
| X20 -> Npos (XO (XO (XO (XO (XO XH)))))
| X21 -> Npos (XI (XO (XO (XO (XO XH)))))
| X22 -> Npos (XO (XI (XO (XO (XO XH)))))
| X23 -> Npos (XI (XI (XO (XO (XO XH)))))
| X24 -> Npos (XO (XO (XI (XO (XO XH)))))
| X25 -> Npos (XI (XO (XI (XO (XO XH)))))
| X26 -> Npos (XO (XI (XI (XO (XO XH)))))
| X27 -> Npos (XI (XI (XI (XO (XO XH)))))
| X28 -> Npos (XO (XO (XO (XI (XO XH)))))
| X29 -> Npos (XI (XO (XO (XI (XO XH)))))
| X2a -> Npos (XO (XI (XO (XI (XO XH)))))
| X2b -> Npos (XI (XI (XO (XI (XO XH)))))
| X2c -> Npos (XO (XO (XI (XI (XO XH)))))
| X2d -> Npos (XI (XO (XI (XI (XO XH)))))
| X2e -> Npos (XO (XI (XI (XI (XO XH)))))
| X2f -> Npos (XI (XI (XI (XI (XO XH)))))
| X30 -> Npos (XO (XO (XO (XO (XI XH)))))
| X31 -> Npos (XI (XO (XO (XO (XI XH)))))
| X32 -> Npos (XO (XI (XO (XO (XI XH)))))
| X33 -> Npos (XI (XI (XO (XO (XI XH)))))
| X34 -> Npos (XO (XO (XI (XO (XI XH)))))
| X35 -> Npos (XI (XO (XI (XO (XI XH)))))
| X36 -> Npos (XO (XI (XI (XO (XI XH)))))
| X37 -> Npos (XI (XI (XI (XO (XI XH)))))
| X38 -> Npos (XO (XO (XO (XI (XI XH)))))
| X39 -> Npos (XI (XO (XO (XI (XI XH)))))
| X3a -> Npos (XO (XI (XO (XI (XI XH)))))
| X3b -> Npos (XI (XI (XO (XI (XI XH)))))
| X3c -> Npos (XO (XO (XI (XI (XI XH)))))
| X3d -> Npos (XI (XO (XI (XI (XI XH)))))
| X3e -> Npos (XO (XI (XI (XI (XI XH)))))
| X3f -> Npos (XI (XI (XI (XI (XI XH)))))
| X40 -> Npos (XO (XO (XO (XO (XO (XO XH))))))
| X41 -> Npos (XI (XO (XO (XO (XO (XO XH))))))
| X42 -> Npos (XO (XI (XO (XO (XO (XO XH))))))
| X43 -> Npos (XI (XI (XO (XO (XO (XO XH))))))
| X44 -> Npos (XO (XO (XI (XO (XO (XO XH))))))
| X45 -> Npos (XI (XO (XI (XO (XO (XO XH))))))
| X46 -> Npos (XO (XI (XI (XO (XO (XO XH))))))
| X47 -> Npos (XI (XI (XI (XO (XO (XO XH))))))
| X48 -> Npos (XO (XO (XO (XI (XO (XO XH))))))
| X49 -> Npos (XI (XO (XO (XI (XO (XO XH))))))
| X4a -> Npos (XO (XI (XO (XI (XO (XO XH))))))
| X4b -> Npos (XI (XI (XO (XI (XO (XO XH))))))
| X4c -> Npos (XO (XO (XI (XI (XO (XO XH))))))
| X4d -> Npos (XI (XO (XI (XI (XO (XO XH))))))
| X4e -> Npos (XO (XI (XI (XI (XO (XO XH))))))
| X4f -> Npos (XI (XI (XI (XI (XO (XO XH))))))
| X50 -> Npos (XO (XO (XO (XO (XI (XO XH))))))
| X51 -> Npos (XI (XO (XO (XO (XI (XO XH))))))
| X52 -> Npos (XO (XI (XO (XO (XI (XO XH))))))
| X53 -> Npos (XI (XI (XO (XO (XI (XO XH))))))
| X54 -> Npos (XO (XO (XI (XO (XI (XO XH))))))
| X55 -> Npos (XI (XO (XI (XO (XI (XO XH))))))
| X56 -> Npos (XO (XI (XI (XO (XI (XO XH))))))
| X57 -> Npos (XI (XI (XI (XO (XI (XO XH))))))
| X58 -> Npos (XO (XO (XO (XI (XI (XO XH))))))
| X59 -> Npos (XI (XO (XO (XI (XI (XO XH))))))
| X5a -> Npos (XO (XI (XO (XI (XI (XO XH))))))
| X5b -> Npos (XI (XI (XO (XI (XI (XO XH))))))
| X5c -> Npos (XO (XO (XI (XI (XI (XO XH))))))
| X5d -> Npos (XI (XO (XI (XI (XI (XO XH))))))
| X5e -> Npos (XO (XI (XI (XI (XI (XO XH))))))
| X5f -> Npos (XI (XI (XI (XI (XI (XO XH))))))
| X60 -> Npos (XO (XO (XO (XO (XO (XI XH))))))
| X61 -> Npos (XI (XO (XO (XO (XO (XI XH))))))
| X62 -> Npos (XO (XI (XO (XO (XO (XI XH))))))
| X63 -> Npos (XI (XI (XO (XO (XO (XI XH))))))
| X64 -> Npos (XO (XO (XI (XO (XO (XI XH))))))
| X65 -> Npos (XI (XO (XI (XO (XO (XI XH))))))
| X66 -> Npos (XO (XI (XI (XO (XO (XI XH))))))
| X67 -> Npos (XI (XI (XI (XO (XO (XI XH))))))
| X68 -> Npos (XO (XO (XO (XI (XO (XI XH))))))
| X69 -> Npos (XI (XO (XO (XI (XO (XI XH))))))
| X6a -> Npos (XO (XI (XO (XI (XO (XI XH))))))
| X6b -> Npos (XI (XI (XO (XI (XO (XI XH))))))
| X6c -> Npos (XO (XO (XI (XI (XO (XI XH))))))
| X6d -> Npos (XI (XO (XI (XI (XO (XI XH))))))
| X6e -> Npos (XO (XI (XI (XI (XO (XI XH))))))
| X6f -> Npos (XI (XI (XI (XI (XO (XI XH))))))
| X70 -> Npos (XO (XO (XO (XO (XI (XI XH))))))
| X71 -> Npos (XI (XO (XO (XO (XI (XI XH))))))
| X72 -> Npos (XO (XI (XO (XO (XI (XI XH))))))
| X73 -> Npos (XI (XI (XO (XO (XI (XI XH))))))
| X74 -> Npos (XO (XO (XI (XO (XI (XI XH))))))
| X75 -> Npos (XI (XO (XI (XO (XI (XI XH))))))
| X76 -> Npos (XO (XI (XI (XO (XI (XI XH))))))
| X77 -> Npos (XI (XI (XI (XO (XI (XI XH))))))
| X78 -> Npos (XO (XO (XO (XI (XI (XI XH))))))
| X79 -> Npos (XI (XO (XO (XI (XI (XI XH))))))
| X7a -> Npos (XO (XI (XO (XI (XI (XI XH))))))
| X7b -> Npos (XI (XI (XO (XI (XI (XI XH))))))
| X7c -> Npos (XO (XO (XI (XI (XI (XI XH))))))
| X7d -> Npos (XI (XO (XI (XI (XI (XI XH))))))
| X7e -> Npos (XO (XI (XI (XI (XI (XI XH))))))
| X7f -> Npos (XI (XI (XI (XI (XI (XI XH))))))
| X80 -> Npos (XO (XO (XO (XO (XO (XO (XO XH)))))))
| X81 -> Npos (XI (XO (XO (XO (XO (XO (XO XH)))))))
| X82 -> Npos (XO (XI (XO (XO (XO (XO (XO XH)))))))
| X83 -> Npos (XI (XI (XO (XO (XO (XO (XO XH)))))))
| X84 -> Npos (XO (XO (XI (XO (XO (XO (XO XH)))))))
| X85 -> Npos (XI (XO (XI (XO (XO (XO (XO XH)))))))
| X86 -> Npos (XO (XI (XI (XO (XO (XO (XO XH)))))))
| X87 -> Npos (XI (XI (XI (XO (XO (XO (XO XH)))))))
| X88 -> Npos (XO (XO (XO (XI (XO (XO (XO XH)))))))
| X89 -> Npos (XI (XO (XO (XI (XO (XO (XO XH)))))))
| X8a -> Npos (XO (XI (XO (XI (XO (XO (XO XH)))))))
| X8b -> Npos (XI (XI (XO (XI (XO (XO (XO XH)))))))
| X8c -> Npos (XO (XO (XI (XI (XO (XO (XO XH)))))))
| X8d -> Npos (XI (XO (XI (XI (XO (XO (XO XH)))))))
| X8e -> Npos (XO (XI (XI (XI (XO (XO (XO XH)))))))
| X8f -> Npos (XI (XI (XI (XI (XO (XO (XO XH)))))))
| X90 -> Npos (XO (XO (XO (XO (XI (XO (XO XH)))))))
| X91 -> Npos (XI (XO (XO (XO (XI (XO (XO XH)))))))
| X92 -> Npos (XO (XI (XO (XO (XI (XO (XO XH)))))))
| X93 -> Npos (XI (XI (XO (XO (XI (XO (XO XH)))))))
| X94 -> Npos (XO (XO (XI (XO (XI (XO (XO XH)))))))
| X95 -> Npos (XI (XO (XI (XO (XI (XO (XO XH)))))))
| X96 -> Npos (XO (XI (XI (XO (XI (XO (XO XH)))))))
| X97 -> Npos (XI (XI (XI (XO (XI (XO (XO XH)))))))
| X98 -> Npos (XO (XO (XO (XI (XI (XO (XO XH)))))))
| X99 -> Npos (XI (XO (XO (XI (XI (XO (XO XH)))))))
| X9a -> Npos (XO (XI (XO (XI (XI (XO (XO XH)))))))
| X9b -> Npos (XI (XI (XO (XI (XI (XO (XO XH)))))))
| X9c -> Npos (XO (XO (XI (XI (XI (XO (XO XH)))))))
| X9d -> Npos (XI (XO (XI (XI (XI (XO (XO XH)))))))
| X9e -> Npos (XO (XI (XI (XI (XI (XO (XO XH)))))))
| X9f -> Npos (XI (XI (XI (XI (XI (XO (XO XH)))))))
| Xa0 -> Npos (XO (XO (XO (XO (XO (XI (XO XH)))))))
| Xa1 -> Npos (XI (XO (XO (XO (XO (XI (XO XH)))))))
| Xa2 -> Npos (XO (XI (XO (XO (XO (XI (XO XH)))))))
| Xa3 -> Npos (XI (XI (XO (XO (XO (XI (XO XH)))))))
| Xa4 -> Npos (XO (XO (XI (XO (XO (XI (XO XH)))))))
| Xa5 -> Npos (XI (XO (XI (XO (XO (XI (XO XH)))))))
| Xa6 -> Npos (XO (XI (XI (XO (XO (XI (XO XH)))))))
| Xa7 -> Npos (XI (XI (XI (XO (XO (XI (XO XH)))))))
| Xa8 -> Npos (XO (XO (XO (XI (XO (XI (XO XH)))))))
| Xa9 -> Npos (XI (XO (XO (XI (XO (XI (XO XH)))))))
| Xaa -> Npos (XO (XI (XO (XI (XO (XI (XO XH)))))))
| Xab -> Npos (XI (XI (XO (XI (XO (XI (XO XH)))))))
| Xac -> Npos (XO (XO (XI (XI (XO (XI (XO XH)))))))
| Xad -> Npos (XI (XO (XI (XI (XO (XI (XO XH)))))))
| Xae -> Npos (XO (XI (XI (XI (XO (XI (XO XH)))))))
| Xaf -> Npos (XI (XI (XI (XI (XO (XI (XO XH)))))))
| Xb0 -> Npos (XO (XO (XO (XO (XI (XI (XO XH)))))))
| Xb1 -> Npos (XI (XO (XO (XO (XI (XI (XO XH)))))))
| Xb2 -> Npos (XO (XI (XO (XO (XI (XI (XO XH)))))))
| Xb3 -> Npos (XI (XI (XO (XO (XI (XI (XO XH)))))))
| Xb4 -> Npos (XO (XO (XI (XO (XI (XI (XO XH)))))))
| Xb5 -> Npos (XI (XO (XI (XO (XI (XI (XO XH)))))))
| Xb6 -> Npos (XO (XI (XI (XO (XI (XI (XO XH)))))))
| Xb7 -> Npos (XI (XI (XI (XO (XI (XI (XO XH)))))))
| Xb8 -> Npos (XO (XO (XO (XI (XI (XI (XO XH)))))))
| Xb9 -> Npos (XI (XO (XO (XI (XI (XI (XO XH)))))))
| Xba -> Npos (XO (XI (XO (XI (XI (XI (XO XH)))))))
| Xbb -> Npos (XI (XI (XO (XI (XI (XI (XO XH)))))))
| Xbc -> Npos (XO (XO (XI (XI (XI (XI (XO XH)))))))
| Xbd -> Npos (XI (XO (XI (XI (XI (XI (XO XH)))))))
| Xbe -> Npos (XO (XI (XI (XI (XI (XI (XO XH)))))))
| Xbf -> Npos (XI (XI (XI (XI (XI (XI (XO XH)))))))
| Xc0 -> Npos (XO (XO (XO (XO (XO (XO (XI XH)))))))
| Xc1 -> Npos (XI (XO (XO (XO (XO (XO (XI XH)))))))
| Xc2 -> Npos (XO (XI (XO (XO (XO (XO (XI XH)))))))
| Xc3 -> Npos (XI (XI (XO (XO (XO (XO (XI XH)))))))
| Xc4 -> Npos (XO (XO (XI (XO (XO (XO (XI XH)))))))
| Xc5 -> Npos (XI (XO (XI (XO (XO (XO (XI XH)))))))
| Xc6 -> Npos (XO (XI (XI (XO (XO (XO (XI XH)))))))
| Xc7 -> Npos (XI (XI (XI (XO (XO (XO (XI XH)))))))
| Xc8 -> Npos (XO (XO (XO (XI (XO (XO (XI XH)))))))
| Xc9 -> Npos (XI (XO (XO (XI (XO (XO (XI XH)))))))
| Xca -> Npos (XO (XI (XO (XI (XO (XO (XI XH)))))))
| Xcb -> Npos (XI (XI (XO (XI (XO (XO (XI XH)))))))
| Xcc -> Npos (XO (XO (XI (XI (XO (XO (XI XH)))))))
| Xcd -> Npos (XI (XO (XI (XI (XO (XO (XI XH)))))))
| Xce -> Npos (XO (XI (XI (XI (XO (XO (XI XH)))))))
| Xcf -> Npos (XI (XI (XI (XI (XO (XO (XI XH)))))))
| Xd0 -> Npos (XO (XO (XO (XO (XI (XO (XI XH)))))))
| Xd1 -> Npos (XI (XO (XO (XO (XI (XO (XI XH)))))))
| Xd2 -> Npos (XO (XI (XO (XO (XI (XO (XI XH)))))))
| Xd3 -> Npos (XI (XI (XO (XO (XI (XO (XI XH)))))))
| Xd4 -> Npos (XO (XO (XI (XO (XI (XO (XI XH)))))))
| Xd5 -> Npos (XI (XO (XI (XO (XI (XO (XI XH)))))))
| Xd6 -> Npos (XO (XI (XI (XO (XI (XO (XI XH)))))))
| Xd7 -> Npos (XI (XI (XI (XO (XI (XO (XI XH)))))))
| Xd8 -> Npos (XO (XO (XO (XI (XI (XO (XI XH)))))))
| Xd9 -> Npos (XI (XO (XO (XI (XI (XO (XI XH)))))))
| Xda -> Npos (XO (XI (XO (XI (XI (XO (XI XH)))))))
| Xdb -> Npos (XI (XI (XO (XI (XI (XO (XI XH)))))))
| Xdc -> Npos (XO (XO (XI (XI (XI (XO (XI XH)))))))
| Xdd -> Npos (XI (XO (XI (XI (XI (XO (XI XH)))))))
| Xde -> Npos (XO (XI (XI (XI (XI (XO (XI XH)))))))
| Xdf -> Npos (XI (XI (XI (XI (XI (XO (XI XH)))))))
| Xe0 -> Npos (XO (XO (XO (XO (XO (XI (XI XH)))))))
| Xe1 -> Npos (XI (XO (XO (XO (XO (XI (XI XH)))))))
| Xe2 -> Npos (XO (XI (XO (XO (XO (XI (XI XH)))))))
| Xe3 -> Npos (XI (XI (XO (XO (XO (XI (XI XH)))))))
| Xe4 -> Npos (XO (XO (XI (XO (XO (XI (XI XH)))))))
| Xe5 -> Npos (XI (XO (XI (XO (XO (XI (XI XH)))))))
| Xe6 -> Npos (XO (XI (XI (XO (XO (XI (XI XH)))))))
| Xe7 -> Npos (XI (XI (XI (XO (XO (XI (XI XH)))))))
| Xe8 -> Npos (XO (XO (XO (XI (XO (XI (XI XH)))))))
| Xe9 -> Npos (XI (XO (XO (XI (XO (XI (XI XH)))))))
| Xea -> Npos (XO (XI (XO (XI (XO (XI (XI XH)))))))
| Xeb -> Npos (XI (XI (XO (XI (XO (XI (XI XH)))))))
| Xec -> Npos (XO (XO (XI (XI (XO (XI (XI XH)))))))
| Xed -> Npos (XI (XO (XI (XI (XO (XI (XI XH)))))))
| Xee -> Npos (XO (XI (XI (XI (XO (XI (XI XH)))))))
| Xef -> Npos (XI (XI (XI (XI (XO (XI (XI XH)))))))
| Xf0 -> Npos (XO (XO (XO (XO (XI (XI (XI XH)))))))
| Xf1 -> Npos (XI (XO (XO (XO (XI (XI (XI XH)))))))
| Xf2 -> Npos (XO (XI (XO (XO (XI (XI (XI XH)))))))
| Xf3 -> Npos (XI (XI (XO (XO (XI (XI (XI XH)))))))
| Xf4 -> Npos (XO (XO (XI (XO (XI (XI (XI XH)))))))
| Xf5 -> Npos (XI (XO (XI (XO (XI (XI (XI XH)))))))
| Xf6 -> Npos (XO (XI (XI (XO (XI (XI (XI XH)))))))
| Xf7 -> Npos (XI (XI (XI (XO (XI (XI (XI XH)))))))
| Xf8 -> Npos (XO (XO (XO (XI (XI (XI (XI XH)))))))
| Xf9 -> Npos (XI (XO (XO (XI (XI (XI (XI XH)))))))
| Xfa -> Npos (XO (XI (XO (XI (XI (XI (XI XH)))))))
| Xfb -> Npos (XI (XI (XO (XI (XI (XI (XI XH)))))))
| Xfc -> Npos (XO (XO (XI (XI (XI (XI (XI XH)))))))
| Xfd -> Npos (XI (XO (XI (XI (XI (XI (XI XH)))))))
| Xfe -> Npos (XO (XI (XI (XI (XI (XI (XI XH)))))))
| Xff -> Npos (XI (XI (XI (XI (XI (XI (XI XH)))))))

(** val of_N0 : n -> byte option **)

let of_N0 = function
| N0 -> Some X00
| Npos p ->
  (match p with
   | XI p0 ->
     (match p0 with
      | XI p1 ->
        (match p1 with
         | XI p2 ->
           (match p2 with
            | XI p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xff
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xbf
                                 | _ -> None)
                     | XH -> Some X7f)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xdf
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X9f
                                 | _ -> None)
                     | XH -> Some X5f)
                  | XH -> Some X3f)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xef
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xaf
                                 | _ -> None)
                     | XH -> Some X6f)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xcf
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X8f
                                 | _ -> None)
                     | XH -> Some X4f)
                  | XH -> Some X2f)
               | XH -> Some X1f)
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xf7
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xb7
                                 | _ -> None)
                     | XH -> Some X77)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xd7
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X97
                                 | _ -> None)
                     | XH -> Some X57)
                  | XH -> Some X37)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xe7
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xa7
                                 | _ -> None)
                     | XH -> Some X67)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xc7
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X87
                                 | _ -> None)
                     | XH -> Some X47)
                  | XH -> Some X27)
               | XH -> Some X17)
            | XH -> Some X0f)
         | XO p2 ->
           (match p2 with
            | XI p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xfb
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xbb
                                 | _ -> None)
                     | XH -> Some X7b)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xdb
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X9b
                                 | _ -> None)
                     | XH -> Some X5b)
                  | XH -> Some X3b)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xeb
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xab
                                 | _ -> None)
                     | XH -> Some X6b)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xcb
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X8b
                                 | _ -> None)
                     | XH -> Some X4b)
                  | XH -> Some X2b)
               | XH -> Some X1b)
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xf3
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xb3
                                 | _ -> None)
                     | XH -> Some X73)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xd3
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X93
                                 | _ -> None)
                     | XH -> Some X53)
                  | XH -> Some X33)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xe3
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xa3
                                 | _ -> None)
                     | XH -> Some X63)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xc3
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X83
                                 | _ -> None)
                     | XH -> Some X43)
                  | XH -> Some X23)
               | XH -> Some X13)
            | XH -> Some X0b)
         | XH -> Some X07)
      | XO p1 ->
        (match p1 with
         | XI p2 ->
           (match p2 with
            | XI p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xfd
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xbd
                                 | _ -> None)
                     | XH -> Some X7d)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xdd
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X9d
                                 | _ -> None)
                     | XH -> Some X5d)
                  | XH -> Some X3d)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xed
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xad
                                 | _ -> None)
                     | XH -> Some X6d)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xcd
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X8d
                                 | _ -> None)
                     | XH -> Some X4d)
                  | XH -> Some X2d)
               | XH -> Some X1d)
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xf5
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xb5
                                 | _ -> None)
                     | XH -> Some X75)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xd5
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X95
                                 | _ -> None)
                     | XH -> Some X55)
                  | XH -> Some X35)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xe5
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xa5
                                 | _ -> None)
                     | XH -> Some X65)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xc5
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X85
                                 | _ -> None)
                     | XH -> Some X45)
                  | XH -> Some X25)
               | XH -> Some X15)
            | XH -> Some X0d)
         | XO p2 ->
           (match p2 with
            | XI p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xf9
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xb9
                                 | _ -> None)
                     | XH -> Some X79)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xd9
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X99
                                 | _ -> None)
                     | XH -> Some X59)
                  | XH -> Some X39)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xe9
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xa9
                                 | _ -> None)
                     | XH -> Some X69)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xc9
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X89
                                 | _ -> None)
                     | XH -> Some X49)
                  | XH -> Some X29)
               | XH -> Some X19)
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xf1
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xb1
                                 | _ -> None)
                     | XH -> Some X71)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xd1
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X91
                                 | _ -> None)
                     | XH -> Some X51)
                  | XH -> Some X31)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xe1
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xa1
                                 | _ -> None)
                     | XH -> Some X61)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xc1
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X81
                                 | _ -> None)
                     | XH -> Some X41)
                  | XH -> Some X21)
               | XH -> Some X11)
            | XH -> Some X09)
         | XH -> Some X05)
      | XH -> Some X03)
   | XO p0 ->
     (match p0 with
      | XI p1 ->
        (match p1 with
         | XI p2 ->
           (match p2 with
            | XI p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xfe
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xbe
                                 | _ -> None)
                     | XH -> Some X7e)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xde
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X9e
                                 | _ -> None)
                     | XH -> Some X5e)
                  | XH -> Some X3e)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xee
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xae
                                 | _ -> None)
                     | XH -> Some X6e)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xce
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X8e
                                 | _ -> None)
                     | XH -> Some X4e)
                  | XH -> Some X2e)
               | XH -> Some X1e)
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xf6
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xb6
                                 | _ -> None)
                     | XH -> Some X76)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xd6
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X96
                                 | _ -> None)
                     | XH -> Some X56)
                  | XH -> Some X36)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xe6
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xa6
                                 | _ -> None)
                     | XH -> Some X66)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xc6
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X86
                                 | _ -> None)
                     | XH -> Some X46)
                  | XH -> Some X26)
               | XH -> Some X16)
            | XH -> Some X0e)
         | XO p2 ->
           (match p2 with
            | XI p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xfa
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xba
                                 | _ -> None)
                     | XH -> Some X7a)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xda
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X9a
                                 | _ -> None)
                     | XH -> Some X5a)
                  | XH -> Some X3a)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xea
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xaa
                                 | _ -> None)
                     | XH -> Some X6a)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xca
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X8a
                                 | _ -> None)
                     | XH -> Some X4a)
                  | XH -> Some X2a)
               | XH -> Some X1a)
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xf2
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xb2
                                 | _ -> None)
                     | XH -> Some X72)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xd2
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X92
                                 | _ -> None)
                     | XH -> Some X52)
                  | XH -> Some X32)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xe2
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xa2
                                 | _ -> None)
                     | XH -> Some X62)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xc2
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X82
                                 | _ -> None)
                     | XH -> Some X42)
                  | XH -> Some X22)
               | XH -> Some X12)
            | XH -> Some X0a)
         | XH -> Some X06)
      | XO p1 ->
        (match p1 with
         | XI p2 ->
           (match p2 with
            | XI p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xfc
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xbc
                                 | _ -> None)
                     | XH -> Some X7c)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xdc
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X9c
                                 | _ -> None)
                     | XH -> Some X5c)
                  | XH -> Some X3c)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xec
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xac
                                 | _ -> None)
                     | XH -> Some X6c)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xcc
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X8c
                                 | _ -> None)
                     | XH -> Some X4c)
                  | XH -> Some X2c)
               | XH -> Some X1c)
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xf4
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xb4
                                 | _ -> None)
                     | XH -> Some X74)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xd4
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X94
                                 | _ -> None)
                     | XH -> Some X54)
                  | XH -> Some X34)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xe4
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xa4
                                 | _ -> None)
                     | XH -> Some X64)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xc4
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X84
                                 | _ -> None)
                     | XH -> Some X44)
                  | XH -> Some X24)
               | XH -> Some X14)
            | XH -> Some X0c)
         | XO p2 ->
           (match p2 with
            | XI p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xf8
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xb8
                                 | _ -> None)
                     | XH -> Some X78)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xd8
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X98
                                 | _ -> None)
                     | XH -> Some X58)
                  | XH -> Some X38)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xe8
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xa8
                                 | _ -> None)
                     | XH -> Some X68)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xc8
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X88
                                 | _ -> None)
                     | XH -> Some X48)
                  | XH -> Some X28)
               | XH -> Some X18)
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xf0
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xb0
                                 | _ -> None)
                     | XH -> Some X70)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xd0
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X90
                                 | _ -> None)
                     | XH -> Some X50)
                  | XH -> Some X30)
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xe0
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some Xa0
                                 | _ -> None)
                     | XH -> Some X60)
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some Xc0
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some X80
                                 | _ -> None)
                     | XH -> Some X40)
                  | XH -> Some X20)
               | XH -> Some X10)
            | XH -> Some X08)
         | XH -> Some X04)
      | XH -> Some X02)
   | XH -> Some X01)

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val byte_of_ascii : ascii -> byte **)

let byte_of_ascii = function
| Ascii (b0, b1, b2, b3, b4, b5, b6, b7) ->
  of_bits (Pair (b0, (Pair (b1, (Pair (b2, (Pair (b3, (Pair (b4, (Pair (b5,
    (Pair (b6, b7))))))))))))))

type string =
| EmptyString
| String of ascii * string

(** val list_ascii_of_string : string -> ascii list **)

let rec list_ascii_of_string = function
| EmptyString -> Nil
| String (ch0, s0) -> Cons (ch0, (list_ascii_of_string s0))

(** val list_byte_of_string : string -> byte list **)

let list_byte_of_string s =
  map byte_of_ascii (list_ascii_of_string s)

(** val np_total : n -> byte **)

let np_total np =
  let o = of_N0 np in
  (match o with
   | Some a -> a
   | None -> assert false (* absurd case *))

(** val log256 : n -> n **)

let log256 n0 =
  N.div (N.log2 n0) (Npos (XO (XO (XO XH))))

(** val byte_list_from_N_fuel : nat -> n -> byte list **)

let rec byte_list_from_N_fuel n0 up =
  match n0 with
  | O ->
    Cons
      ((np_total
         (N.modulo up (Npos (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))))),
      Nil)
  | S n' ->
    let r = N.modulo up (Npos (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))) in
    let t = N.div up (Npos (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))) in
    Cons ((np_total r), (byte_list_from_N_fuel n' t))

(** val byte_list_from_N : n -> byte list **)

let byte_list_from_N np =
  byte_list_from_N_fuel (N.to_nat (log256 np)) np

(** val big_endien_list_N : n -> byte list **)

let big_endien_list_N np =
  rev (byte_list_from_N np)

(** val word : n **)

let word =
  Npos (XO (XO (XO (XO (XO XH)))))

(** val add0 : n -> n -> n **)

let add0 x y =
  N.modulo (N.add x y) (N.pow (Npos (XO XH)) word)

(** val shift_left : n -> n -> n **)

let shift_left x n0 =
  N.modulo (N.shiftl x n0) (N.pow (Npos (XO XH)) word)

(** val shift_right : n -> n -> n **)

let shift_right =
  N.shiftr

(** val bitwise_and : n -> n -> n **)

let bitwise_and =
  N.coq_land

(** val bitwise_or : n -> n -> n **)

let bitwise_or =
  N.coq_lor

(** val bitwise_xor : n -> n -> n **)

let bitwise_xor =
  N.coq_lxor

(** val bitwise_neg : n -> n **)

let bitwise_neg x =
  N.lnot x word

(** val rOTR : n -> n -> n **)

let rOTR n0 x =
  bitwise_or (shift_right x n0) (shift_left x (N.sub word n0))

(** val sHR : n -> n -> n **)

let sHR n0 x =
  shift_right x n0

(** val ch : n -> n -> n -> n **)

let ch x y z0 =
  bitwise_xor (bitwise_and x y) (bitwise_and (bitwise_neg x) z0)

(** val maj : n -> n -> n -> n **)

let maj x y z0 =
  bitwise_xor (bitwise_xor (bitwise_and x y) (bitwise_and x z0))
    (bitwise_and y z0)

(** val sigma_UU2080_ : n -> n **)

let sigma_UU2080_ x =
  bitwise_xor
    (bitwise_xor (rOTR (Npos (XO XH)) x) (rOTR (Npos (XI (XO (XI XH)))) x))
    (rOTR (Npos (XO (XI (XI (XO XH))))) x)

(** val sigma_UU2081_ : n -> n **)

let sigma_UU2081_ x =
  bitwise_xor
    (bitwise_xor (rOTR (Npos (XO (XI XH))) x)
      (rOTR (Npos (XI (XI (XO XH)))) x))
    (rOTR (Npos (XI (XO (XO (XI XH))))) x)

(** val sigma_UU2080_0 : n -> n **)

let sigma_UU2080_0 x =
  bitwise_xor
    (bitwise_xor (rOTR (Npos (XI (XI XH))) x)
      (rOTR (Npos (XO (XI (XO (XO XH))))) x)) (sHR (Npos (XI XH)) x)

(** val sigma_UU2081_0 : n -> n **)

let sigma_UU2081_0 x =
  bitwise_xor
    (bitwise_xor (rOTR (Npos (XI (XO (XO (XO XH))))) x)
      (rOTR (Npos (XI (XI (XO (XO XH))))) x)) (sHR (Npos (XO (XI (XO XH)))) x)

(** val h_UU2080_ : n list **)

let h_UU2080_ =
  Cons ((Npos (XI (XI (XI (XO (XO (XI (XI (XO (XO (XI (XI (XO (XO (XI (XI (XI
    (XI (XO (XO (XI (XO (XO (XO (XO (XO (XI (XO (XI (XO (XI
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XI (XO (XO (XO
    (XO (XI (XO (XI (XI (XI (XO (XI (XO (XI (XI (XI (XI (XO (XO (XI (XI (XO
    (XI (XI (XO (XI (XI (XI (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XO (XI (XO (XO (XI (XI (XI (XO (XI (XI (XO (XO (XI (XI (XI (XI
    (XO (XI (XI (XI (XO (XI (XI (XO (XO (XO (XI (XI (XI
    XH)))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XO (XI (XI (XI
    (XO (XO (XI (XO (XI (XO (XI (XI (XI (XI (XI (XI (XI (XI (XO (XO (XI (XO
    (XI (XO (XI (XO (XO (XI (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XI (XI (XI (XI (XI (XI (XI (XO (XO (XI (XO (XO (XI (XO (XI (XO
    (XO (XI (XI (XI (XO (XO (XO (XO (XI (XO (XO (XO (XI (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XI (XI (XO (XO
    (XO (XI (XO (XO (XO (XI (XO (XI (XI (XO (XI (XO (XI (XO (XO (XO (XO (XO
    (XI (XI (XO (XI (XI (XO (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XI (XI (XO (XI (XO (XI (XO (XI (XI (XO (XO (XI (XI (XO (XI (XI
    (XI (XI (XO (XO (XO (XO (XO (XI (XI (XI (XI (XI
    XH))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XO (XI (XI (XO (XO
    (XO (XI (XO (XI (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XI (XI (XI (XI
    (XI (XO (XI (XI (XO XH))))))))))))))))))))))))))))))), Nil)))))))))))))))

(** val k : n list **)

let k =
  Cons ((Npos (XO (XO (XO (XI (XI (XO (XO (XI (XI (XI (XI (XI (XO (XI (XO (XO
    (XO (XI (XO (XI (XO (XO (XO (XI (XO (XI (XO (XO (XO (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XO (XO (XI (XO
    (XO (XI (XO (XO (XI (XO (XO (XO (XI (XO (XI (XI (XI (XO (XI (XI (XO (XO
    (XI (XO (XO (XO (XI (XI XH))))))))))))))))))))))))))))))), (Cons ((Npos
    (XI (XI (XI (XI (XO (XO (XI (XI (XI (XI (XO (XI (XI (XI (XI (XI (XO (XO
    (XO (XO (XO (XO (XI (XI (XI (XO (XI (XO (XI (XI (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XI (XO (XO (XI
    (XO (XI (XI (XI (XO (XI (XI (XO (XI (XI (XI (XO (XI (XO (XI (XI (XO (XI
    (XI (XO (XO (XI (XO (XI (XI XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XI (XI (XO (XI (XI (XO (XI (XO (XO (XI (XO (XO (XO (XO (XI (XI
    (XO (XI (XI (XO (XI (XO (XI (XO (XI (XO (XO (XI (XI
    XH)))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XO (XO (XI (XI
    (XI (XI (XI (XO (XO (XO (XI (XO (XO (XO (XI (XO (XO (XO (XI (XI (XI (XI
    (XI (XO (XO (XI (XI (XO XH))))))))))))))))))))))))))))))), (Cons ((Npos
    (XO (XO (XI (XO (XO (XI (XO (XI (XO (XI (XO (XO (XO (XO (XO (XI (XI (XI
    (XI (XI (XI (XI (XO (XO (XO (XI (XO (XO (XI (XO (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XI (XO (XI (XO
    (XI (XI (XO (XI (XI (XI (XI (XO (XI (XO (XO (XO (XI (XI (XI (XO (XO (XO
    (XI (XI (XO (XI (XO (XI (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XO (XO (XO (XI (XI (XO (XO (XI (XO (XI (XO (XI (XO (XI (XO (XI
    (XI (XI (XI (XO (XO (XO (XO (XO (XO (XO (XO (XI (XI (XO (XI
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XO (XO (XO (XO
    (XO (XO (XI (XI (XO (XI (XI (XO (XI (XO (XI (XI (XO (XO (XO (XO (XO (XI
    (XO (XI (XO (XO XH))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XI
    (XI (XI (XI (XO (XI (XI (XO (XI (XO (XO (XO (XO (XI (XI (XO (XO (XO (XI
    (XI (XO (XO (XO (XO (XI (XO (XO XH)))))))))))))))))))))))))))))), (Cons
    ((Npos (XI (XI (XO (XO (XO (XO (XI (XI (XI (XO (XI (XI (XI (XI (XI (XO
    (XO (XO (XI (XI (XO (XO (XO (XO (XI (XO (XI (XO (XI (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XI (XO (XI (XI
    (XI (XO (XI (XO (XI (XI (XI (XO (XI (XO (XO (XI (XI (XI (XI (XI (XO (XI
    (XO (XI (XO (XO (XI (XI XH))))))))))))))))))))))))))))))), (Cons ((Npos
    (XO (XI (XI (XI (XI (XI (XI (XI (XI (XO (XO (XO (XI (XI (XO (XI (XO (XI
    (XI (XI (XI (XO (XI (XI (XO (XO (XO (XO (XO (XO (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XI (XO (XO (XI
    (XO (XI (XO (XI (XI (XO (XO (XO (XO (XO (XO (XO (XI (XI (XI (XO (XI (XI
    (XI (XI (XO (XI (XI (XO (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XO (XO (XI (XO (XI (XI (XI (XO (XI (XO (XO (XO (XI (XI (XI (XI
    (XI (XI (XO (XI (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XI
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XO (XO (XO (XO
    (XI (XI (XI (XO (XO (XI (XO (XI (XI (XO (XI (XI (XO (XI (XI (XO (XO (XI
    (XO (XO (XI (XO (XO (XI (XI XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XO (XI (XI (XO (XO (XO (XO (XI (XI (XI (XI (XO (XO (XO (XI (XO
    (XO (XI (XI (XI (XI (XI (XO (XI (XI (XI (XI (XI (XO (XI (XI
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XI (XO (XO (XO
    (XI (XI (XI (XO (XI (XI (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XI (XI
    (XI (XI (XI XH)))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XI (XI
    (XO (XO (XI (XI (XI (XO (XO (XO (XO (XI (XO (XI (XO (XO (XI (XI (XO (XO
    (XO (XO (XO (XO (XI (XO (XO XH)))))))))))))))))))))))))))))), (Cons
    ((Npos (XI (XI (XI (XI (XO (XI (XI (XO (XO (XO (XI (XI (XO (XI (XO (XO
    (XI (XO (XO (XI (XO (XI (XI (XI (XI (XO (XI (XI (XO
    XH)))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XO (XI (XO (XI
    (XO (XI (XO (XO (XI (XO (XO (XO (XO (XI (XO (XO (XI (XO (XI (XI (XI (XO
    (XO (XI (XO (XI (XO (XO XH))))))))))))))))))))))))))))))), (Cons ((Npos
    (XO (XO (XI (XI (XI (XO (XI (XI (XI (XO (XO (XI (XO (XI (XO (XI (XO (XO
    (XO (XO (XI (XI (XO (XI (XO (XO (XI (XI (XI (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XO (XI (XI (XO
    (XI (XI (XO (XO (XO (XI (XO (XO (XO (XI (XI (XO (XO (XI (XI (XI (XI (XI
    (XO (XI (XI (XO (XI (XI XH))))))))))))))))))))))))))))))), (Cons ((Npos
    (XO (XI (XO (XO (XI (XO (XI (XO (XI (XO (XO (XO (XI (XO (XI (XO (XO (XI
    (XI (XI (XI (XI (XO (XO (XO (XO (XO (XI (XI (XO (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XI (XI (XO (XI
    (XI (XO (XO (XI (XI (XO (XO (XO (XI (XI (XI (XO (XO (XO (XI (XI (XO (XO
    (XO (XO (XO (XI (XO (XI (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XO (XO (XO (XI (XO (XO (XI (XI (XI (XI (XI (XO (XO (XI (XO (XO
    (XI (XI (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XI (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XI (XO (XO (XO
    (XI (XI (XI (XI (XI (XI (XI (XI (XI (XO (XI (XO (XO (XI (XI (XO (XI (XO
    (XI (XI (XI (XI (XI (XI (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XI (XI (XO (XO (XI (XI (XI (XI (XI (XI (XO (XI (XO (XO (XO (XO
    (XO (XO (XO (XO (XO (XI (XI (XI (XO (XI (XI (XO (XO (XO (XI
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XI (XO (XO (XO
    (XI (XO (XI (XO (XO (XO (XI (XO (XO (XI (XI (XI (XI (XO (XO (XI (XO (XI
    (XI (XO (XI (XO (XI (XO (XI XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XI (XO (XO (XO (XI (XO (XI (XO (XI (XI (XO (XO (XO (XI (XI (XO
    (XO (XI (XO (XI (XO (XO (XI (XI (XO (XI XH))))))))))))))))))))))))))),
    (Cons ((Npos (XI (XI (XI (XO (XO (XI (XI (XO (XI (XO (XO (XI (XO (XI (XO
    (XO (XI (XO (XO (XI (XO (XI (XO (XO (XO (XO (XI (XO
    XH))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XI (XO (XO (XO (XO
    (XI (XO (XI (XO (XI (XO (XO (XO (XO (XI (XI (XI (XO (XI (XI (XO (XI (XI
    (XI (XI (XO (XO XH)))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO
    (XO (XI (XI (XI (XO (XO (XI (XO (XO (XO (XO (XI (XO (XO (XI (XI (XO (XI
    (XI (XO (XO (XO (XO (XI (XI (XI (XO XH)))))))))))))))))))))))))))))),
    (Cons ((Npos (XO (XO (XI (XI (XI (XI (XI (XI (XI (XO (XI (XI (XO (XI (XI
    (XO (XO (XO (XI (XI (XO (XI (XO (XO (XI (XO (XI (XI (XO (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XO (XO (XI (XO
    (XO (XO (XI (XO (XI (XI (XO (XO (XO (XO (XO (XO (XO (XI (XI (XI (XO (XO
    (XI (XI (XO (XO (XI (XO XH))))))))))))))))))))))))))))))), (Cons ((Npos
    (XO (XO (XI (XO (XI (XO (XI (XO (XI (XI (XO (XO (XI (XI (XI (XO (XO (XI
    (XO (XI (XO (XO (XO (XO (XI (XO (XI (XO (XO (XI
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XO (XI (XI (XI
    (XO (XI (XO (XI (XO (XI (XO (XO (XO (XO (XO (XI (XO (XI (XO (XI (XI (XO
    (XO (XI (XI (XO (XI (XI XH))))))))))))))))))))))))))))))), (Cons ((Npos
    (XO (XI (XI (XI (XO (XI (XO (XO (XI (XO (XO (XI (XO (XO (XI (XI (XO (XI
    (XO (XO (XO (XO (XI (XI (XI (XO (XO (XO (XO (XO (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XI (XO (XO (XO
    (XO (XI (XO (XO (XI (XI (XO (XI (XO (XO (XO (XI (XO (XO (XI (XI (XI (XO
    (XO (XI (XO (XO (XI (XO (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XI (XO (XO (XO (XO (XI (XO (XI (XO (XO (XO (XI (XO (XI (XI (XI
    (XI (XI (XI (XI (XI (XI (XO (XI (XO (XI (XO (XO (XO (XI (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XO (XI (XO (XO
    (XI (XO (XO (XI (XI (XO (XO (XI (XI (XO (XO (XI (XO (XI (XI (XO (XO (XO
    (XO (XO (XO (XI (XO (XI (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XO (XO (XO (XO (XI (XI (XI (XO (XI (XI (XO (XI (XO (XO (XO (XI
    (XI (XI (XO (XI (XO (XO (XI (XO (XO (XI (XO (XO (XO (XO (XI
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XO (XO (XO (XI
    (XO (XI (XI (XO (XO (XO (XI (XO (XI (XO (XO (XO (XI (XI (XO (XI (XI (XO
    (XI (XI (XI (XO (XO (XO (XI XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XO (XI (XO (XI (XI (XI
    (XO (XI (XO (XO (XI (XO (XO (XI (XI (XO (XO (XO (XI (XO (XI
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XI (XO (XO (XI
    (XO (XO (XO (XI (XI (XO (XO (XO (XO (XO (XI (XO (XO (XI (XI (XO (XO (XI
    (XO (XI (XI (XO (XI (XO (XI XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XI (XO (XI (XO (XO (XO (XO (XI (XI (XO (XI (XO (XI (XI (XO (XO
    (XO (XI (XI (XI (XO (XO (XO (XO (XO (XO (XI (XO (XI (XI (XI
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XO (XO (XI (XI
    (XI (XO (XO (XO (XO (XO (XO (XI (XO (XI (XO (XI (XO (XI (XO (XI (XI (XO
    (XO (XO (XO (XO XH))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XI
    (XO (XI (XO (XO (XO (XI (XO (XO (XO (XO (XO (XI (XI (XO (XO (XI (XO (XO
    (XI (XO (XI (XI (XO (XO (XI XH))))))))))))))))))))))))))))), (Cons ((Npos
    (XO (XO (XO (XI (XO (XO (XO (XO (XO (XO (XI (XI (XO (XI (XI (XO (XI (XI
    (XI (XO (XI (XI (XO (XO (XO (XI (XI (XI XH))))))))))))))))))))))))))))),
    (Cons ((Npos (XO (XO (XI (XI (XO (XO (XI (XO (XI (XI (XI (XO (XI (XI (XI
    (XO (XO (XO (XO (XI (XO (XO (XI (XO (XI (XI (XI (XO (XO
    XH)))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XI (XO (XI (XI
    (XO (XI (XO (XO (XI (XI (XI (XI (XO (XI (XO (XO (XO (XO (XI (XI (XO (XI
    (XO (XO (XI (XO (XI XH)))))))))))))))))))))))))))))), (Cons ((Npos (XI
    (XI (XO (XO (XI (XI (XO (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XO (XI
    (XI (XI (XO (XO (XO (XI (XO (XO (XI (XI XH)))))))))))))))))))))))))))))),
    (Cons ((Npos (XO (XI (XO (XI (XO (XO (XI (XO (XO (XI (XO (XI (XO (XI (XO
    (XI (XO (XO (XO (XI (XI (XO (XI (XI (XO (XI (XI (XI (XO (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XI (XI (XO (XO
    (XI (XO (XO (XI (XO (XI (XO (XO (XI (XI (XO (XO (XI (XI (XI (XO (XO (XI
    (XI (XI (XO (XI (XI (XO XH))))))))))))))))))))))))))))))), (Cons ((Npos
    (XI (XI (XO (XO (XI (XI (XI (XI (XI (XI (XI (XI (XO (XI (XI (XO (XO (XI
    (XI (XI (XO (XI (XO (XO (XO (XO (XO (XI (XO (XI
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XI (XI (XO (XI
    (XI (XI (XO (XI (XO (XO (XO (XO (XO (XI (XI (XI (XI (XI (XO (XO (XO (XI
    (XO (XO (XI (XO (XI (XI XH))))))))))))))))))))))))))))))), (Cons ((Npos
    (XI (XI (XI (XI (XO (XI (XI (XO (XI (XI (XO (XO (XO (XI (XI (XO (XI (XO
    (XI (XO (XO (XI (XO (XI (XO (XO (XO (XI (XI (XI
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XI (XO (XI (XO
    (XO (XO (XO (XO (XO (XI (XI (XI (XI (XO (XO (XO (XO (XI (XO (XO (XI (XI
    (XO (XO (XI (XO (XO (XO (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XO (XO (XO (XI (XO (XO (XO (XO (XO (XI (XO (XO (XO (XO (XO (XO
    (XI (XI (XI (XO (XO (XO (XI (XI (XO (XO (XI (XI (XO (XO (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XO (XI (XI (XI
    (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XO (XI (XI (XI (XI (XI (XO (XI
    (XO (XO (XO (XO (XI (XO (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XI (XI (XO (XI (XO (XI (XI (XI (XO (XO (XI (XI (XO (XI (XI (XO
    (XO (XO (XO (XO (XI (XO (XI (XO (XO (XO (XI (XO (XO (XI (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XI (XO (XI (XI
    (XI (XI (XI (XI (XO (XO (XO (XI (XO (XI (XI (XO (XO (XI (XI (XI (XI (XI
    (XO (XI (XI (XI (XI (XI (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Npos (XO (XI (XO (XO (XI (XI (XI (XI (XO (XO (XO (XI (XI (XI (XI (XO
    (XI (XO (XO (XO (XI (XI (XI (XO (XO (XI (XI (XO (XO (XO (XI
    XH)))))))))))))))))))))))))))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val get_zero_bytes : nat -> byte list **)

let rec get_zero_bytes = function
| O -> Nil
| S v' -> Cons (X00, (get_zero_bytes v'))

(** val message_padding : nat -> byte list **)

let message_padding = function
| O -> Nil
| S v' -> Cons (X80, (get_zero_bytes v'))

(** val append_zero_in_length_byte : byte list -> byte list **)

let append_zero_in_length_byte lb =
  let nl = length lb in
  if Nat.leb nl (S (S (S (S (S (S (S (S O))))))))
  then app (get_zero_bytes (sub (S (S (S (S (S (S (S (S O)))))))) nl)) lb
  else lb

(** val message_length_byte : byte list -> byte list **)

let message_length_byte m0 =
  let n0 = N.of_nat (length m0) in
  let mbits = N.mul (Npos (XO (XO (XO XH)))) n0 in
  append_zero_in_length_byte (big_endien_list_N mbits)

(** val prepared_message : byte list -> byte list **)

let prepared_message m0 =
  let n0 = N.of_nat (length m0) in
  let mbits = N.mul (Npos (XO (XO (XO XH)))) n0 in
  let k0 =
    Z.to_N
      (Z.modulo
        (Z.sub (Zpos (XO (XO (XO (XO (XO (XO (XI (XI XH)))))))))
          (Z.add (Z.of_N mbits) (Zpos XH))) (Zpos (XO (XO (XO (XO (XO (XO (XO
        (XO (XO XH)))))))))))
  in
  let wt = N.div (N.add (Npos XH) k0) (Npos (XO (XO (XO XH)))) in
  app m0 (app (message_padding (N.to_nat wt)) (message_length_byte m0))

(** val big_endien_32_bit_to_N : byte -> byte -> byte -> byte -> n **)

let big_endien_32_bit_to_N a b c d =
  N.add
    (N.mul
      (N.add
        (N.mul
          (N.add
            (N.mul (to_N0 a) (Npos (XO (XO (XO (XO (XO (XO (XO (XO
              XH)))))))))) (to_N0 b)) (Npos (XO (XO (XO (XO (XO (XO (XO (XO
          XH)))))))))) (to_N0 c)) (Npos (XO (XO (XO (XO (XO (XO (XO (XO
      XH)))))))))) (to_N0 d)

(** val m : byte list -> nat -> nat -> n **)

let m m0 i j =
  big_endien_32_bit_to_N
    (nth
      (add
        (mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) i)
        (mul (S (S (S (S O)))) j)) (prepared_message m0) X00)
    (nth
      (add
        (add
          (mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            i) (mul (S (S (S (S O)))) j)) (S O)) (prepared_message m0) X00)
    (nth
      (add
        (add
          (mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            i) (mul (S (S (S (S O)))) j)) (S (S O))) (prepared_message m0)
      X00)
    (nth
      (add
        (add
          (mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            i) (mul (S (S (S (S O)))) j)) (S (S (S O))))
      (prepared_message m0) X00)

(** val from_n : nat -> nat list **)

let rec from_n = function
| O -> Nil
| S n' -> Cons (n', (from_n n'))

(** val upto_n : nat -> nat list **)

let upto_n n0 =
  rev (from_n n0)

(** val w : byte list -> nat -> n list **)

let w m0 i =
  fold_left (fun acc t ->
    let wtp =
      if Nat.ltb t (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))
      then m m0 i t
      else let a = nth (sub t (S (S O))) acc N0 in
           let b = nth (sub t (S (S (S (S (S (S (S O)))))))) acc N0 in
           let c =
             nth
               (sub t (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 O)))))))))))))))) acc N0
           in
           let d =
             nth
               (sub t (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 O))))))))))))))))) acc N0
           in
           add0 (add0 (add0 (sigma_UU2081_0 a) b) (sigma_UU2080_0 c)) d
    in
    app acc (Cons (wtp, Nil)))
    (upto_n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) Nil

(** val sha256_intermediate : n list -> n list -> n list **)

let sha256_intermediate w0 h =
  let a = nth O h N0 in
  let b = nth (S O) h N0 in
  let c = nth (S (S O)) h N0 in
  let d = nth (S (S (S O))) h N0 in
  let e = nth (S (S (S (S O)))) h N0 in
  let f = nth (S (S (S (S (S O))))) h N0 in
  let g = nth (S (S (S (S (S (S O)))))) h N0 in
  let h0 = nth (S (S (S (S (S (S (S O))))))) h N0 in
  let Pair (p, h1) =
    fold_left (fun pat t ->
      let Pair (y, h1) = pat in
      let Pair (y0, g0) = y in
      let Pair (y1, f0) = y0 in
      let Pair (y2, e0) = y1 in
      let Pair (y3, d0) = y2 in
      let Pair (y4, c0) = y3 in
      let Pair (a0, b0) = y4 in
      let t_UU2081_ =
        add0
          (add0 (add0 (add0 h1 (sigma_UU2081_ e0)) (ch e0 f0 g0))
            (nth t k N0)) (nth t w0 N0)
      in
      let t_UU2082_ = add0 (sigma_UU2080_ a0) (maj a0 b0 c0) in
      let e1 = add0 d0 t_UU2081_ in
      let a1 = add0 t_UU2081_ t_UU2082_ in
      Pair ((Pair ((Pair ((Pair ((Pair ((Pair ((Pair (a1, a0)), b0)), c0)),
      e1)), e0)), f0)), g0))
      (upto_n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (Pair ((Pair ((Pair ((Pair ((Pair ((Pair ((Pair (a, b)), c)), d)), e)),
      f)), g)), h0))
  in
  let Pair (p0, g0) = p in
  let Pair (p1, f0) = p0 in
  let Pair (p2, e0) = p1 in
  let Pair (p3, d0) = p2 in
  let Pair (p4, c0) = p3 in
  let Pair (a0, b0) = p4 in
  Cons ((add0 a0 (nth O h N0)), (Cons ((add0 b0 (nth (S O) h N0)), (Cons
  ((add0 c0 (nth (S (S O)) h N0)), (Cons ((add0 d0 (nth (S (S (S O))) h N0)),
  (Cons ((add0 e0 (nth (S (S (S (S O)))) h N0)), (Cons
  ((add0 f0 (nth (S (S (S (S (S O))))) h N0)), (Cons
  ((add0 g0 (nth (S (S (S (S (S (S O)))))) h N0)), (Cons
  ((add0 h1 (nth (S (S (S (S (S (S (S O))))))) h N0)), Nil)))))))))))))))

(** val sha256 : byte list -> n list **)

let sha256 m0 =
  let n0 = N.of_nat (length m0) in
  let mbits = N.mul (Npos (XO (XO (XO XH)))) n0 in
  let k0 =
    Z.to_N
      (Z.modulo
        (Z.sub (Zpos (XO (XO (XO (XO (XO (XO (XI (XI XH)))))))))
          (Z.add (Z.of_N mbits) (Zpos XH))) (Zpos (XO (XO (XO (XO (XO (XO (XO
        (XO (XO XH)))))))))))
  in
  let wt = N.div (N.add (Npos XH) k0) (Npos (XO (XO (XO XH)))) in
  let ms =
    N.div (N.add (N.add n0 wt) (Npos (XO (XO (XO XH))))) (Npos (XO (XO (XO
      (XO (XO (XO XH)))))))
  in
  fold_left (fun h i -> sha256_intermediate (w m0 i) h)
    (upto_n (N.to_nat ms)) h_UU2080_

(** val concat_bytes : byte list -> n **)

let concat_bytes bs =
  fold_left (fun acc b ->
    N.add (N.mul acc (N.shiftl (Npos XH) (Npos (XO (XO (XO XH)))))) (to_N0 b))
    bs N0

(** val sha256_string : string -> n **)

let sha256_string s =
  concat_bytes (flat_map big_endien_list_N (sha256 (list_byte_of_string s)))
