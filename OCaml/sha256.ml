
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
    | XO p -> (match y with
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
    | XH -> (match y with
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
    | XH -> (match q with
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
      if leb b r' then Pair ((succ_double q), (sub r' b)) else Pair ((double q), r')
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then Pair ((succ_double q), (sub r' b)) else Pair ((double q), r')
    | XH ->
      (match b with
       | N0 -> Pair (N0, (Npos XH))
       | Npos p -> (match p with
                    | XH -> Pair ((Npos XH), N0)
                    | _ -> Pair (N0, (Npos XH))))

  (** val div_eucl : n -> n -> (n, n) prod **)

  let div_eucl a b =
    match a with
    | N0 -> Pair (N0, N0)
    | Npos na -> (match b with
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
    | Npos p -> (match m0 with
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
    | Zneg x' -> (match y with
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
    | XH -> if leb (Zpos (XO XH)) b then Pair (Z0, (Zpos XH)) else Pair ((Zpos XH), Z0)

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
       | Zneg b' -> let Pair (q, r) = pos_div_eucl a' (Zpos b') in Pair (q, (opp r)))

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let Pair (_, r) = div_eucl a b in r
 end

(** val to_N0 : char -> n **)

let to_N0 = function
| '\x00' -> N0
| '\x01' -> Npos XH
| '\x02' -> Npos (XO XH)
| '\x03' -> Npos (XI XH)
| '\x04' -> Npos (XO (XO XH))
| '\x05' -> Npos (XI (XO XH))
| '\x06' -> Npos (XO (XI XH))
| '\x07' -> Npos (XI (XI XH))
| '\x08' -> Npos (XO (XO (XO XH)))
| '\t' -> Npos (XI (XO (XO XH)))
| '\n' -> Npos (XO (XI (XO XH)))
| '\x0b' -> Npos (XI (XI (XO XH)))
| '\x0c' -> Npos (XO (XO (XI XH)))
| '\r' -> Npos (XI (XO (XI XH)))
| '\x0e' -> Npos (XO (XI (XI XH)))
| '\x0f' -> Npos (XI (XI (XI XH)))
| '\x10' -> Npos (XO (XO (XO (XO XH))))
| '\x11' -> Npos (XI (XO (XO (XO XH))))
| '\x12' -> Npos (XO (XI (XO (XO XH))))
| '\x13' -> Npos (XI (XI (XO (XO XH))))
| '\x14' -> Npos (XO (XO (XI (XO XH))))
| '\x15' -> Npos (XI (XO (XI (XO XH))))
| '\x16' -> Npos (XO (XI (XI (XO XH))))
| '\x17' -> Npos (XI (XI (XI (XO XH))))
| '\x18' -> Npos (XO (XO (XO (XI XH))))
| '\x19' -> Npos (XI (XO (XO (XI XH))))
| '\x1a' -> Npos (XO (XI (XO (XI XH))))
| '\x1b' -> Npos (XI (XI (XO (XI XH))))
| '\x1c' -> Npos (XO (XO (XI (XI XH))))
| '\x1d' -> Npos (XI (XO (XI (XI XH))))
| '\x1e' -> Npos (XO (XI (XI (XI XH))))
| '\x1f' -> Npos (XI (XI (XI (XI XH))))
| ' ' -> Npos (XO (XO (XO (XO (XO XH)))))
| '!' -> Npos (XI (XO (XO (XO (XO XH)))))
| '"' -> Npos (XO (XI (XO (XO (XO XH)))))
| '#' -> Npos (XI (XI (XO (XO (XO XH)))))
| '$' -> Npos (XO (XO (XI (XO (XO XH)))))
| '%' -> Npos (XI (XO (XI (XO (XO XH)))))
| '&' -> Npos (XO (XI (XI (XO (XO XH)))))
| '\'' -> Npos (XI (XI (XI (XO (XO XH)))))
| '(' -> Npos (XO (XO (XO (XI (XO XH)))))
| ')' -> Npos (XI (XO (XO (XI (XO XH)))))
| '*' -> Npos (XO (XI (XO (XI (XO XH)))))
| '+' -> Npos (XI (XI (XO (XI (XO XH)))))
| ',' -> Npos (XO (XO (XI (XI (XO XH)))))
| '-' -> Npos (XI (XO (XI (XI (XO XH)))))
| '.' -> Npos (XO (XI (XI (XI (XO XH)))))
| '/' -> Npos (XI (XI (XI (XI (XO XH)))))
| '0' -> Npos (XO (XO (XO (XO (XI XH)))))
| '1' -> Npos (XI (XO (XO (XO (XI XH)))))
| '2' -> Npos (XO (XI (XO (XO (XI XH)))))
| '3' -> Npos (XI (XI (XO (XO (XI XH)))))
| '4' -> Npos (XO (XO (XI (XO (XI XH)))))
| '5' -> Npos (XI (XO (XI (XO (XI XH)))))
| '6' -> Npos (XO (XI (XI (XO (XI XH)))))
| '7' -> Npos (XI (XI (XI (XO (XI XH)))))
| '8' -> Npos (XO (XO (XO (XI (XI XH)))))
| '9' -> Npos (XI (XO (XO (XI (XI XH)))))
| ':' -> Npos (XO (XI (XO (XI (XI XH)))))
| ';' -> Npos (XI (XI (XO (XI (XI XH)))))
| '<' -> Npos (XO (XO (XI (XI (XI XH)))))
| '=' -> Npos (XI (XO (XI (XI (XI XH)))))
| '>' -> Npos (XO (XI (XI (XI (XI XH)))))
| '?' -> Npos (XI (XI (XI (XI (XI XH)))))
| '@' -> Npos (XO (XO (XO (XO (XO (XO XH))))))
| 'A' -> Npos (XI (XO (XO (XO (XO (XO XH))))))
| 'B' -> Npos (XO (XI (XO (XO (XO (XO XH))))))
| 'C' -> Npos (XI (XI (XO (XO (XO (XO XH))))))
| 'D' -> Npos (XO (XO (XI (XO (XO (XO XH))))))
| 'E' -> Npos (XI (XO (XI (XO (XO (XO XH))))))
| 'F' -> Npos (XO (XI (XI (XO (XO (XO XH))))))
| 'G' -> Npos (XI (XI (XI (XO (XO (XO XH))))))
| 'H' -> Npos (XO (XO (XO (XI (XO (XO XH))))))
| 'I' -> Npos (XI (XO (XO (XI (XO (XO XH))))))
| 'J' -> Npos (XO (XI (XO (XI (XO (XO XH))))))
| 'K' -> Npos (XI (XI (XO (XI (XO (XO XH))))))
| 'L' -> Npos (XO (XO (XI (XI (XO (XO XH))))))
| 'M' -> Npos (XI (XO (XI (XI (XO (XO XH))))))
| 'N' -> Npos (XO (XI (XI (XI (XO (XO XH))))))
| 'O' -> Npos (XI (XI (XI (XI (XO (XO XH))))))
| 'P' -> Npos (XO (XO (XO (XO (XI (XO XH))))))
| 'Q' -> Npos (XI (XO (XO (XO (XI (XO XH))))))
| 'R' -> Npos (XO (XI (XO (XO (XI (XO XH))))))
| 'S' -> Npos (XI (XI (XO (XO (XI (XO XH))))))
| 'T' -> Npos (XO (XO (XI (XO (XI (XO XH))))))
| 'U' -> Npos (XI (XO (XI (XO (XI (XO XH))))))
| 'V' -> Npos (XO (XI (XI (XO (XI (XO XH))))))
| 'W' -> Npos (XI (XI (XI (XO (XI (XO XH))))))
| 'X' -> Npos (XO (XO (XO (XI (XI (XO XH))))))
| 'Y' -> Npos (XI (XO (XO (XI (XI (XO XH))))))
| 'Z' -> Npos (XO (XI (XO (XI (XI (XO XH))))))
| '[' -> Npos (XI (XI (XO (XI (XI (XO XH))))))
| '\\' -> Npos (XO (XO (XI (XI (XI (XO XH))))))
| ']' -> Npos (XI (XO (XI (XI (XI (XO XH))))))
| '^' -> Npos (XO (XI (XI (XI (XI (XO XH))))))
| '_' -> Npos (XI (XI (XI (XI (XI (XO XH))))))
| '`' -> Npos (XO (XO (XO (XO (XO (XI XH))))))
| 'a' -> Npos (XI (XO (XO (XO (XO (XI XH))))))
| 'b' -> Npos (XO (XI (XO (XO (XO (XI XH))))))
| 'c' -> Npos (XI (XI (XO (XO (XO (XI XH))))))
| 'd' -> Npos (XO (XO (XI (XO (XO (XI XH))))))
| 'e' -> Npos (XI (XO (XI (XO (XO (XI XH))))))
| 'f' -> Npos (XO (XI (XI (XO (XO (XI XH))))))
| 'g' -> Npos (XI (XI (XI (XO (XO (XI XH))))))
| 'h' -> Npos (XO (XO (XO (XI (XO (XI XH))))))
| 'i' -> Npos (XI (XO (XO (XI (XO (XI XH))))))
| 'j' -> Npos (XO (XI (XO (XI (XO (XI XH))))))
| 'k' -> Npos (XI (XI (XO (XI (XO (XI XH))))))
| 'l' -> Npos (XO (XO (XI (XI (XO (XI XH))))))
| 'm' -> Npos (XI (XO (XI (XI (XO (XI XH))))))
| 'n' -> Npos (XO (XI (XI (XI (XO (XI XH))))))
| 'o' -> Npos (XI (XI (XI (XI (XO (XI XH))))))
| 'p' -> Npos (XO (XO (XO (XO (XI (XI XH))))))
| 'q' -> Npos (XI (XO (XO (XO (XI (XI XH))))))
| 'r' -> Npos (XO (XI (XO (XO (XI (XI XH))))))
| 's' -> Npos (XI (XI (XO (XO (XI (XI XH))))))
| 't' -> Npos (XO (XO (XI (XO (XI (XI XH))))))
| 'u' -> Npos (XI (XO (XI (XO (XI (XI XH))))))
| 'v' -> Npos (XO (XI (XI (XO (XI (XI XH))))))
| 'w' -> Npos (XI (XI (XI (XO (XI (XI XH))))))
| 'x' -> Npos (XO (XO (XO (XI (XI (XI XH))))))
| 'y' -> Npos (XI (XO (XO (XI (XI (XI XH))))))
| 'z' -> Npos (XO (XI (XO (XI (XI (XI XH))))))
| '{' -> Npos (XI (XI (XO (XI (XI (XI XH))))))
| '|' -> Npos (XO (XO (XI (XI (XI (XI XH))))))
| '}' -> Npos (XI (XO (XI (XI (XI (XI XH))))))
| '~' -> Npos (XO (XI (XI (XI (XI (XI XH))))))
| '\x7f' -> Npos (XI (XI (XI (XI (XI (XI XH))))))
| '\x80' -> Npos (XO (XO (XO (XO (XO (XO (XO XH)))))))
| '\x81' -> Npos (XI (XO (XO (XO (XO (XO (XO XH)))))))
| '\x82' -> Npos (XO (XI (XO (XO (XO (XO (XO XH)))))))
| '\x83' -> Npos (XI (XI (XO (XO (XO (XO (XO XH)))))))
| '\x84' -> Npos (XO (XO (XI (XO (XO (XO (XO XH)))))))
| '\x85' -> Npos (XI (XO (XI (XO (XO (XO (XO XH)))))))
| '\x86' -> Npos (XO (XI (XI (XO (XO (XO (XO XH)))))))
| '\x87' -> Npos (XI (XI (XI (XO (XO (XO (XO XH)))))))
| '\x88' -> Npos (XO (XO (XO (XI (XO (XO (XO XH)))))))
| '\x89' -> Npos (XI (XO (XO (XI (XO (XO (XO XH)))))))
| '\x8a' -> Npos (XO (XI (XO (XI (XO (XO (XO XH)))))))
| '\x8b' -> Npos (XI (XI (XO (XI (XO (XO (XO XH)))))))
| '\x8c' -> Npos (XO (XO (XI (XI (XO (XO (XO XH)))))))
| '\x8d' -> Npos (XI (XO (XI (XI (XO (XO (XO XH)))))))
| '\x8e' -> Npos (XO (XI (XI (XI (XO (XO (XO XH)))))))
| '\x8f' -> Npos (XI (XI (XI (XI (XO (XO (XO XH)))))))
| '\x90' -> Npos (XO (XO (XO (XO (XI (XO (XO XH)))))))
| '\x91' -> Npos (XI (XO (XO (XO (XI (XO (XO XH)))))))
| '\x92' -> Npos (XO (XI (XO (XO (XI (XO (XO XH)))))))
| '\x93' -> Npos (XI (XI (XO (XO (XI (XO (XO XH)))))))
| '\x94' -> Npos (XO (XO (XI (XO (XI (XO (XO XH)))))))
| '\x95' -> Npos (XI (XO (XI (XO (XI (XO (XO XH)))))))
| '\x96' -> Npos (XO (XI (XI (XO (XI (XO (XO XH)))))))
| '\x97' -> Npos (XI (XI (XI (XO (XI (XO (XO XH)))))))
| '\x98' -> Npos (XO (XO (XO (XI (XI (XO (XO XH)))))))
| '\x99' -> Npos (XI (XO (XO (XI (XI (XO (XO XH)))))))
| '\x9a' -> Npos (XO (XI (XO (XI (XI (XO (XO XH)))))))
| '\x9b' -> Npos (XI (XI (XO (XI (XI (XO (XO XH)))))))
| '\x9c' -> Npos (XO (XO (XI (XI (XI (XO (XO XH)))))))
| '\x9d' -> Npos (XI (XO (XI (XI (XI (XO (XO XH)))))))
| '\x9e' -> Npos (XO (XI (XI (XI (XI (XO (XO XH)))))))
| '\x9f' -> Npos (XI (XI (XI (XI (XI (XO (XO XH)))))))
| '\xa0' -> Npos (XO (XO (XO (XO (XO (XI (XO XH)))))))
| '\xa1' -> Npos (XI (XO (XO (XO (XO (XI (XO XH)))))))
| '\xa2' -> Npos (XO (XI (XO (XO (XO (XI (XO XH)))))))
| '\xa3' -> Npos (XI (XI (XO (XO (XO (XI (XO XH)))))))
| '\xa4' -> Npos (XO (XO (XI (XO (XO (XI (XO XH)))))))
| '\xa5' -> Npos (XI (XO (XI (XO (XO (XI (XO XH)))))))
| '\xa6' -> Npos (XO (XI (XI (XO (XO (XI (XO XH)))))))
| '\xa7' -> Npos (XI (XI (XI (XO (XO (XI (XO XH)))))))
| '\xa8' -> Npos (XO (XO (XO (XI (XO (XI (XO XH)))))))
| '\xa9' -> Npos (XI (XO (XO (XI (XO (XI (XO XH)))))))
| '\xaa' -> Npos (XO (XI (XO (XI (XO (XI (XO XH)))))))
| '\xab' -> Npos (XI (XI (XO (XI (XO (XI (XO XH)))))))
| '\xac' -> Npos (XO (XO (XI (XI (XO (XI (XO XH)))))))
| '\xad' -> Npos (XI (XO (XI (XI (XO (XI (XO XH)))))))
| '\xae' -> Npos (XO (XI (XI (XI (XO (XI (XO XH)))))))
| '\xaf' -> Npos (XI (XI (XI (XI (XO (XI (XO XH)))))))
| '\xb0' -> Npos (XO (XO (XO (XO (XI (XI (XO XH)))))))
| '\xb1' -> Npos (XI (XO (XO (XO (XI (XI (XO XH)))))))
| '\xb2' -> Npos (XO (XI (XO (XO (XI (XI (XO XH)))))))
| '\xb3' -> Npos (XI (XI (XO (XO (XI (XI (XO XH)))))))
| '\xb4' -> Npos (XO (XO (XI (XO (XI (XI (XO XH)))))))
| '\xb5' -> Npos (XI (XO (XI (XO (XI (XI (XO XH)))))))
| '\xb6' -> Npos (XO (XI (XI (XO (XI (XI (XO XH)))))))
| '\xb7' -> Npos (XI (XI (XI (XO (XI (XI (XO XH)))))))
| '\xb8' -> Npos (XO (XO (XO (XI (XI (XI (XO XH)))))))
| '\xb9' -> Npos (XI (XO (XO (XI (XI (XI (XO XH)))))))
| '\xba' -> Npos (XO (XI (XO (XI (XI (XI (XO XH)))))))
| '\xbb' -> Npos (XI (XI (XO (XI (XI (XI (XO XH)))))))
| '\xbc' -> Npos (XO (XO (XI (XI (XI (XI (XO XH)))))))
| '\xbd' -> Npos (XI (XO (XI (XI (XI (XI (XO XH)))))))
| '\xbe' -> Npos (XO (XI (XI (XI (XI (XI (XO XH)))))))
| '\xbf' -> Npos (XI (XI (XI (XI (XI (XI (XO XH)))))))
| '\xc0' -> Npos (XO (XO (XO (XO (XO (XO (XI XH)))))))
| '\xc1' -> Npos (XI (XO (XO (XO (XO (XO (XI XH)))))))
| '\xc2' -> Npos (XO (XI (XO (XO (XO (XO (XI XH)))))))
| '\xc3' -> Npos (XI (XI (XO (XO (XO (XO (XI XH)))))))
| '\xc4' -> Npos (XO (XO (XI (XO (XO (XO (XI XH)))))))
| '\xc5' -> Npos (XI (XO (XI (XO (XO (XO (XI XH)))))))
| '\xc6' -> Npos (XO (XI (XI (XO (XO (XO (XI XH)))))))
| '\xc7' -> Npos (XI (XI (XI (XO (XO (XO (XI XH)))))))
| '\xc8' -> Npos (XO (XO (XO (XI (XO (XO (XI XH)))))))
| '\xc9' -> Npos (XI (XO (XO (XI (XO (XO (XI XH)))))))
| '\xca' -> Npos (XO (XI (XO (XI (XO (XO (XI XH)))))))
| '\xcb' -> Npos (XI (XI (XO (XI (XO (XO (XI XH)))))))
| '\xcc' -> Npos (XO (XO (XI (XI (XO (XO (XI XH)))))))
| '\xcd' -> Npos (XI (XO (XI (XI (XO (XO (XI XH)))))))
| '\xce' -> Npos (XO (XI (XI (XI (XO (XO (XI XH)))))))
| '\xcf' -> Npos (XI (XI (XI (XI (XO (XO (XI XH)))))))
| '\xd0' -> Npos (XO (XO (XO (XO (XI (XO (XI XH)))))))
| '\xd1' -> Npos (XI (XO (XO (XO (XI (XO (XI XH)))))))
| '\xd2' -> Npos (XO (XI (XO (XO (XI (XO (XI XH)))))))
| '\xd3' -> Npos (XI (XI (XO (XO (XI (XO (XI XH)))))))
| '\xd4' -> Npos (XO (XO (XI (XO (XI (XO (XI XH)))))))
| '\xd5' -> Npos (XI (XO (XI (XO (XI (XO (XI XH)))))))
| '\xd6' -> Npos (XO (XI (XI (XO (XI (XO (XI XH)))))))
| '\xd7' -> Npos (XI (XI (XI (XO (XI (XO (XI XH)))))))
| '\xd8' -> Npos (XO (XO (XO (XI (XI (XO (XI XH)))))))
| '\xd9' -> Npos (XI (XO (XO (XI (XI (XO (XI XH)))))))
| '\xda' -> Npos (XO (XI (XO (XI (XI (XO (XI XH)))))))
| '\xdb' -> Npos (XI (XI (XO (XI (XI (XO (XI XH)))))))
| '\xdc' -> Npos (XO (XO (XI (XI (XI (XO (XI XH)))))))
| '\xdd' -> Npos (XI (XO (XI (XI (XI (XO (XI XH)))))))
| '\xde' -> Npos (XO (XI (XI (XI (XI (XO (XI XH)))))))
| '\xdf' -> Npos (XI (XI (XI (XI (XI (XO (XI XH)))))))
| '\xe0' -> Npos (XO (XO (XO (XO (XO (XI (XI XH)))))))
| '\xe1' -> Npos (XI (XO (XO (XO (XO (XI (XI XH)))))))
| '\xe2' -> Npos (XO (XI (XO (XO (XO (XI (XI XH)))))))
| '\xe3' -> Npos (XI (XI (XO (XO (XO (XI (XI XH)))))))
| '\xe4' -> Npos (XO (XO (XI (XO (XO (XI (XI XH)))))))
| '\xe5' -> Npos (XI (XO (XI (XO (XO (XI (XI XH)))))))
| '\xe6' -> Npos (XO (XI (XI (XO (XO (XI (XI XH)))))))
| '\xe7' -> Npos (XI (XI (XI (XO (XO (XI (XI XH)))))))
| '\xe8' -> Npos (XO (XO (XO (XI (XO (XI (XI XH)))))))
| '\xe9' -> Npos (XI (XO (XO (XI (XO (XI (XI XH)))))))
| '\xea' -> Npos (XO (XI (XO (XI (XO (XI (XI XH)))))))
| '\xeb' -> Npos (XI (XI (XO (XI (XO (XI (XI XH)))))))
| '\xec' -> Npos (XO (XO (XI (XI (XO (XI (XI XH)))))))
| '\xed' -> Npos (XI (XO (XI (XI (XO (XI (XI XH)))))))
| '\xee' -> Npos (XO (XI (XI (XI (XO (XI (XI XH)))))))
| '\xef' -> Npos (XI (XI (XI (XI (XO (XI (XI XH)))))))
| '\xf0' -> Npos (XO (XO (XO (XO (XI (XI (XI XH)))))))
| '\xf1' -> Npos (XI (XO (XO (XO (XI (XI (XI XH)))))))
| '\xf2' -> Npos (XO (XI (XO (XO (XI (XI (XI XH)))))))
| '\xf3' -> Npos (XI (XI (XO (XO (XI (XI (XI XH)))))))
| '\xf4' -> Npos (XO (XO (XI (XO (XI (XI (XI XH)))))))
| '\xf5' -> Npos (XI (XO (XI (XO (XI (XI (XI XH)))))))
| '\xf6' -> Npos (XO (XI (XI (XO (XI (XI (XI XH)))))))
| '\xf7' -> Npos (XI (XI (XI (XO (XI (XI (XI XH)))))))
| '\xf8' -> Npos (XO (XO (XO (XI (XI (XI (XI XH)))))))
| '\xf9' -> Npos (XI (XO (XO (XI (XI (XI (XI XH)))))))
| '\xfa' -> Npos (XO (XI (XO (XI (XI (XI (XI XH)))))))
| '\xfb' -> Npos (XI (XI (XO (XI (XI (XI (XI XH)))))))
| '\xfc' -> Npos (XO (XO (XI (XI (XI (XI (XI XH)))))))
| '\xfd' -> Npos (XI (XO (XI (XI (XI (XI (XI XH)))))))
| '\xfe' -> Npos (XO (XI (XI (XI (XI (XI (XI XH)))))))
| '\xff' -> Npos (XI (XI (XI (XI (XI (XI (XI XH)))))))

(** val of_N0 : n -> char option **)

let of_N0 = function
| N0 -> Some '\x00'
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
                                 | XH -> Some '\xff'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xbf'
                                 | _ -> None)
                     | XH -> Some '\x7f')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xdf'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x9f'
                                 | _ -> None)
                     | XH -> Some '_')
                  | XH -> Some '?')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xef'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xaf'
                                 | _ -> None)
                     | XH -> Some 'o')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xcf'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x8f'
                                 | _ -> None)
                     | XH -> Some 'O')
                  | XH -> Some '/')
               | XH -> Some '\x1f')
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xf7'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xb7'
                                 | _ -> None)
                     | XH -> Some 'w')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xd7'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x97'
                                 | _ -> None)
                     | XH -> Some 'W')
                  | XH -> Some '7')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xe7'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xa7'
                                 | _ -> None)
                     | XH -> Some 'g')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xc7'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x87'
                                 | _ -> None)
                     | XH -> Some 'G')
                  | XH -> Some '\'')
               | XH -> Some '\x17')
            | XH -> Some '\x0f')
         | XO p2 ->
           (match p2 with
            | XI p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xfb'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xbb'
                                 | _ -> None)
                     | XH -> Some '{')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xdb'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x9b'
                                 | _ -> None)
                     | XH -> Some '[')
                  | XH -> Some ';')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xeb'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xab'
                                 | _ -> None)
                     | XH -> Some 'k')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xcb'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x8b'
                                 | _ -> None)
                     | XH -> Some 'K')
                  | XH -> Some '+')
               | XH -> Some '\x1b')
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xf3'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xb3'
                                 | _ -> None)
                     | XH -> Some 's')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xd3'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x93'
                                 | _ -> None)
                     | XH -> Some 'S')
                  | XH -> Some '3')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xe3'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xa3'
                                 | _ -> None)
                     | XH -> Some 'c')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xc3'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x83'
                                 | _ -> None)
                     | XH -> Some 'C')
                  | XH -> Some '#')
               | XH -> Some '\x13')
            | XH -> Some '\x0b')
         | XH -> Some '\x07')
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
                                 | XH -> Some '\xfd'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xbd'
                                 | _ -> None)
                     | XH -> Some '}')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xdd'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x9d'
                                 | _ -> None)
                     | XH -> Some ']')
                  | XH -> Some '=')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xed'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xad'
                                 | _ -> None)
                     | XH -> Some 'm')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xcd'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x8d'
                                 | _ -> None)
                     | XH -> Some 'M')
                  | XH -> Some '-')
               | XH -> Some '\x1d')
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xf5'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xb5'
                                 | _ -> None)
                     | XH -> Some 'u')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xd5'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x95'
                                 | _ -> None)
                     | XH -> Some 'U')
                  | XH -> Some '5')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xe5'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xa5'
                                 | _ -> None)
                     | XH -> Some 'e')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xc5'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x85'
                                 | _ -> None)
                     | XH -> Some 'E')
                  | XH -> Some '%')
               | XH -> Some '\x15')
            | XH -> Some '\r')
         | XO p2 ->
           (match p2 with
            | XI p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xf9'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xb9'
                                 | _ -> None)
                     | XH -> Some 'y')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xd9'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x99'
                                 | _ -> None)
                     | XH -> Some 'Y')
                  | XH -> Some '9')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xe9'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xa9'
                                 | _ -> None)
                     | XH -> Some 'i')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xc9'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x89'
                                 | _ -> None)
                     | XH -> Some 'I')
                  | XH -> Some ')')
               | XH -> Some '\x19')
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xf1'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xb1'
                                 | _ -> None)
                     | XH -> Some 'q')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xd1'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x91'
                                 | _ -> None)
                     | XH -> Some 'Q')
                  | XH -> Some '1')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xe1'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xa1'
                                 | _ -> None)
                     | XH -> Some 'a')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xc1'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x81'
                                 | _ -> None)
                     | XH -> Some 'A')
                  | XH -> Some '!')
               | XH -> Some '\x11')
            | XH -> Some '\t')
         | XH -> Some '\x05')
      | XH -> Some '\x03')
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
                                 | XH -> Some '\xfe'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xbe'
                                 | _ -> None)
                     | XH -> Some '~')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xde'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x9e'
                                 | _ -> None)
                     | XH -> Some '^')
                  | XH -> Some '>')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xee'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xae'
                                 | _ -> None)
                     | XH -> Some 'n')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xce'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x8e'
                                 | _ -> None)
                     | XH -> Some 'N')
                  | XH -> Some '.')
               | XH -> Some '\x1e')
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xf6'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xb6'
                                 | _ -> None)
                     | XH -> Some 'v')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xd6'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x96'
                                 | _ -> None)
                     | XH -> Some 'V')
                  | XH -> Some '6')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xe6'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xa6'
                                 | _ -> None)
                     | XH -> Some 'f')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xc6'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x86'
                                 | _ -> None)
                     | XH -> Some 'F')
                  | XH -> Some '&')
               | XH -> Some '\x16')
            | XH -> Some '\x0e')
         | XO p2 ->
           (match p2 with
            | XI p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xfa'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xba'
                                 | _ -> None)
                     | XH -> Some 'z')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xda'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x9a'
                                 | _ -> None)
                     | XH -> Some 'Z')
                  | XH -> Some ':')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xea'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xaa'
                                 | _ -> None)
                     | XH -> Some 'j')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xca'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x8a'
                                 | _ -> None)
                     | XH -> Some 'J')
                  | XH -> Some '*')
               | XH -> Some '\x1a')
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xf2'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xb2'
                                 | _ -> None)
                     | XH -> Some 'r')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xd2'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x92'
                                 | _ -> None)
                     | XH -> Some 'R')
                  | XH -> Some '2')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xe2'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xa2'
                                 | _ -> None)
                     | XH -> Some 'b')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xc2'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x82'
                                 | _ -> None)
                     | XH -> Some 'B')
                  | XH -> Some '"')
               | XH -> Some '\x12')
            | XH -> Some '\n')
         | XH -> Some '\x06')
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
                                 | XH -> Some '\xfc'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xbc'
                                 | _ -> None)
                     | XH -> Some '|')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xdc'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x9c'
                                 | _ -> None)
                     | XH -> Some '\\')
                  | XH -> Some '<')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xec'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xac'
                                 | _ -> None)
                     | XH -> Some 'l')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xcc'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x8c'
                                 | _ -> None)
                     | XH -> Some 'L')
                  | XH -> Some ',')
               | XH -> Some '\x1c')
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xf4'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xb4'
                                 | _ -> None)
                     | XH -> Some 't')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xd4'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x94'
                                 | _ -> None)
                     | XH -> Some 'T')
                  | XH -> Some '4')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xe4'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xa4'
                                 | _ -> None)
                     | XH -> Some 'd')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xc4'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x84'
                                 | _ -> None)
                     | XH -> Some 'D')
                  | XH -> Some '$')
               | XH -> Some '\x14')
            | XH -> Some '\x0c')
         | XO p2 ->
           (match p2 with
            | XI p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xf8'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xb8'
                                 | _ -> None)
                     | XH -> Some 'x')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xd8'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x98'
                                 | _ -> None)
                     | XH -> Some 'X')
                  | XH -> Some '8')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xe8'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xa8'
                                 | _ -> None)
                     | XH -> Some 'h')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xc8'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x88'
                                 | _ -> None)
                     | XH -> Some 'H')
                  | XH -> Some '(')
               | XH -> Some '\x18')
            | XO p3 ->
              (match p3 with
               | XI p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xf0'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xb0'
                                 | _ -> None)
                     | XH -> Some 'p')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xd0'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x90'
                                 | _ -> None)
                     | XH -> Some 'P')
                  | XH -> Some '0')
               | XO p4 ->
                 (match p4 with
                  | XI p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xe0'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\xa0'
                                 | _ -> None)
                     | XH -> Some '`')
                  | XO p5 ->
                    (match p5 with
                     | XI p6 -> (match p6 with
                                 | XH -> Some '\xc0'
                                 | _ -> None)
                     | XO p6 -> (match p6 with
                                 | XH -> Some '\x80'
                                 | _ -> None)
                     | XH -> Some '@')
                  | XH -> Some ' ')
               | XH -> Some '\x10')
            | XH -> Some '\x08')
         | XH -> Some '\x04')
      | XH -> Some '\x02')
   | XH -> Some '\x01')

(** val list_ascii_of_string : char list -> char list **)

let rec list_ascii_of_string = function
| [] -> Nil
| ch0::s0 -> Cons (ch0, (list_ascii_of_string s0))

(** val list_byte_of_string : char list -> char list **)

let list_byte_of_string s =
  map (fun x -> x) (list_ascii_of_string s)

(** val np_total : n -> char **)

let np_total np =
  let o = of_N0 np in (match o with
                       | Some a -> a
                       | None -> assert false (* absurd case *))

(** val log256 : n -> n **)

let log256 n0 =
  N.div (N.log2 n0) (Npos (XO (XO (XO XH))))

(** val byte_list_from_N_fuel : nat -> n -> char list **)

let rec byte_list_from_N_fuel n0 up =
  match n0 with
  | O ->
    Cons ((np_total (N.modulo up (Npos (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))))),
      Nil)
  | S n' ->
    let r = N.modulo up (Npos (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))) in
    let t = N.div up (Npos (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))) in
    Cons ((np_total r), (byte_list_from_N_fuel n' t))

(** val byte_list_from_N : n -> char list **)

let byte_list_from_N np =
  byte_list_from_N_fuel (N.to_nat (log256 np)) np

(** val big_endien_list_N : n -> char list **)

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
  bitwise_xor (bitwise_xor (bitwise_and x y) (bitwise_and x z0)) (bitwise_and y z0)

(** val sigma_UU2080_ : n -> n **)

let sigma_UU2080_ x =
  bitwise_xor (bitwise_xor (rOTR (Npos (XO XH)) x) (rOTR (Npos (XI (XO (XI XH)))) x))
    (rOTR (Npos (XO (XI (XI (XO XH))))) x)

(** val sigma_UU2081_ : n -> n **)

let sigma_UU2081_ x =
  bitwise_xor
    (bitwise_xor (rOTR (Npos (XO (XI XH))) x) (rOTR (Npos (XI (XI (XO XH)))) x))
    (rOTR (Npos (XI (XO (XO (XI XH))))) x)

(** val sigma_UU2080_0 : n -> n **)

let sigma_UU2080_0 x =
  bitwise_xor
    (bitwise_xor (rOTR (Npos (XI (XI XH))) x) (rOTR (Npos (XO (XI (XO (XO XH))))) x))
    (sHR (Npos (XI XH)) x)

(** val sigma_UU2081_0 : n -> n **)

let sigma_UU2081_0 x =
  bitwise_xor
    (bitwise_xor (rOTR (Npos (XI (XO (XO (XO XH))))) x)
      (rOTR (Npos (XI (XI (XO (XO XH))))) x)) (sHR (Npos (XO (XI (XO XH)))) x)

(** val h_UU2080_ : n list **)

let h_UU2080_ =
  Cons ((Npos (XI (XI (XI (XO (XO (XI (XI (XO (XO (XI (XI (XO (XO (XI (XI (XI (XI (XO
    (XO (XI (XO (XO (XO (XO (XO (XI (XO (XI (XO (XI XH))))))))))))))))))))))))))))))),
    (Cons ((Npos (XI (XO (XI (XO (XO (XO (XO (XI (XO (XI (XI (XI (XO (XI (XO (XI (XI (XI
    (XI (XO (XO (XI (XI (XO (XI (XI (XO (XI (XI (XI (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XO (XO (XI (XI (XI (XO (XI
    (XI (XO (XO (XI (XI (XI (XI (XO (XI (XI (XI (XO (XI (XI (XO (XO (XO (XI (XI (XI
    XH)))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XO (XI (XI (XI (XO (XO (XI
    (XO (XI (XO (XI (XI (XI (XI (XI (XI (XI (XI (XO (XO (XI (XO (XI (XO (XI (XO (XO (XI
    (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XI (XI (XI (XI (XI (XO
    (XO (XI (XO (XO (XI (XO (XI (XO (XO (XI (XI (XI (XO (XO (XO (XO (XI (XO (XO (XO (XI
    (XO XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XI (XI (XO (XO (XO (XI
    (XO (XO (XO (XI (XO (XI (XI (XO (XI (XO (XI (XO (XO (XO (XO (XO (XI (XI (XO (XI (XI
    (XO (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XO (XI (XO (XI (XO
    (XI (XI (XO (XO (XI (XI (XO (XI (XI (XI (XI (XO (XO (XO (XO (XO (XI (XI (XI (XI (XI
    XH))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XO (XI (XI (XO (XO (XO (XI
    (XO (XI (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XI (XI (XI (XI (XI (XO (XI (XI (XO
    XH))))))))))))))))))))))))))))))), Nil)))))))))))))))

(** val k : n list **)

let k =
  Cons ((Npos (XO (XO (XO (XI (XI (XO (XO (XI (XI (XI (XI (XI (XO (XI (XO (XO (XO (XI
    (XO (XI (XO (XO (XO (XI (XO (XI (XO (XO (XO (XO XH))))))))))))))))))))))))))))))),
    (Cons ((Npos (XI (XO (XO (XO (XI (XO (XO (XI (XO (XO (XI (XO (XO (XO (XI (XO (XI (XI
    (XI (XO (XI (XI (XO (XO (XI (XO (XO (XO (XI (XI XH))))))))))))))))))))))))))))))),
    (Cons ((Npos (XI (XI (XI (XI (XO (XO (XI (XI (XI (XI (XO (XI (XI (XI (XI (XI (XO (XO
    (XO (XO (XO (XO (XI (XI (XI (XO (XI (XO (XI (XI (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XI (XO (XO (XI (XO (XI (XI
    (XI (XO (XI (XI (XO (XI (XI (XI (XO (XI (XO (XI (XI (XO (XI (XI (XO (XO (XI (XO (XI
    (XI XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XO (XI (XI (XO (XI (XO
    (XO (XI (XO (XO (XO (XO (XI (XI (XO (XI (XI (XO (XI (XO (XI (XO (XI (XO (XO (XI (XI
    XH)))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XO (XO (XI (XI (XI (XI (XI
    (XO (XO (XO (XI (XO (XO (XO (XI (XO (XO (XO (XI (XI (XI (XI (XI (XO (XO (XI (XI (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XI (XO (XO (XI (XO (XI (XO
    (XI (XO (XO (XO (XO (XO (XI (XI (XI (XI (XI (XI (XI (XO (XO (XO (XI (XO (XO (XI (XO
    (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XI (XO (XI (XO (XI (XI
    (XO (XI (XI (XI (XI (XO (XI (XO (XO (XO (XI (XI (XI (XO (XO (XO (XI (XI (XO (XI (XO
    (XI (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XO (XI (XI (XO (XO
    (XI (XO (XI (XO (XI (XO (XI (XO (XI (XI (XI (XI (XO (XO (XO (XO (XO (XO (XO (XO (XI
    (XI (XO (XI XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XO (XO (XO (XO
    (XO (XO (XI (XI (XO (XI (XI (XO (XI (XO (XI (XI (XO (XO (XO (XO (XO (XI (XO (XI (XO
    (XO XH))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XI (XI (XI (XI (XO (XI
    (XI (XO (XI (XO (XO (XO (XO (XI (XI (XO (XO (XO (XI (XI (XO (XO (XO (XO (XI (XO (XO
    XH)))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XO (XO (XO (XO (XI (XI (XI
    (XO (XI (XI (XI (XI (XI (XO (XO (XO (XI (XI (XO (XO (XO (XO (XI (XO (XI (XO (XI (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XI (XO (XI (XI (XI (XO (XI
    (XO (XI (XI (XI (XO (XI (XO (XO (XI (XI (XI (XI (XI (XO (XI (XO (XI (XO (XO (XI (XI
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XI (XI (XI (XI (XI (XI (XI
    (XO (XO (XO (XI (XI (XO (XI (XO (XI (XI (XI (XI (XO (XI (XI (XO (XO (XO (XO (XO (XO
    (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XI (XO (XO (XI (XO (XI
    (XO (XI (XI (XO (XO (XO (XO (XO (XO (XO (XI (XI (XI (XO (XI (XI (XI (XI (XO (XI (XI
    (XO (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XI (XO (XI (XI (XI
    (XO (XI (XO (XO (XO (XI (XI (XI (XI (XI (XI (XO (XI (XI (XO (XO (XI (XI (XO (XO (XO
    (XO (XO (XI XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XO (XO (XO (XO
    (XI (XI (XI (XO (XO (XI (XO (XI (XI (XO (XI (XI (XO (XI (XI (XO (XO (XI (XO (XO (XI
    (XO (XO (XI (XI XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XI (XO (XO
    (XO (XO (XI (XI (XI (XI (XO (XO (XO (XI (XO (XO (XI (XI (XI (XI (XI (XO (XI (XI (XI
    (XI (XI (XO (XI (XI XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XI (XO
    (XO (XO (XI (XI (XI (XO (XI (XI (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XI (XI (XI
    (XI (XI XH)))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XI (XI (XO (XO (XI (XI
    (XI (XO (XO (XO (XO (XI (XO (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XO (XI (XO (XO
    XH)))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XI (XI (XO (XI (XI (XO (XO
    (XO (XI (XI (XO (XI (XO (XO (XI (XO (XO (XI (XO (XI (XI (XI (XI (XO (XI (XI (XO
    XH)))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XO (XI (XO (XI (XO (XI (XO
    (XO (XI (XO (XO (XO (XO (XI (XO (XO (XI (XO (XI (XI (XI (XO (XO (XI (XO (XI (XO (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XI (XI (XI (XO (XI (XI (XI
    (XO (XO (XI (XO (XI (XO (XI (XO (XO (XO (XO (XI (XI (XO (XI (XO (XO (XI (XI (XI (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XO (XI (XI (XO (XI (XI (XO
    (XO (XO (XI (XO (XO (XO (XI (XI (XO (XO (XI (XI (XI (XI (XI (XO (XI (XI (XO (XI (XI
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XO (XO (XI (XO (XI (XO (XI
    (XO (XO (XO (XI (XO (XI (XO (XO (XI (XI (XI (XI (XI (XO (XO (XO (XO (XO (XI (XI (XO
    (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XI (XI (XO (XI (XI (XO
    (XO (XI (XI (XO (XO (XO (XI (XI (XI (XO (XO (XO (XI (XI (XO (XO (XO (XO (XO (XI (XO
    (XI (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XO (XI (XO (XO (XI
    (XI (XI (XI (XI (XO (XO (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
    (XI (XI (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XI (XO (XO (XO
    (XI (XI (XI (XI (XI (XI (XI (XI (XI (XO (XI (XO (XO (XI (XI (XO (XI (XO (XI (XI (XI
    (XI (XI (XI (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XO (XO (XI
    (XI (XI (XI (XI (XI (XO (XI (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XI (XI (XO (XI
    (XI (XO (XO (XO (XI XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XI (XO
    (XO (XO (XI (XO (XI (XO (XO (XO (XI (XO (XO (XI (XI (XI (XI (XO (XO (XI (XO (XI (XI
    (XO (XI (XO (XI (XO (XI XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XO
    (XO (XI (XO (XI (XO (XI (XI (XO (XO (XO (XI (XI (XO (XO (XI (XO (XI (XO (XO (XI (XI
    (XO (XI XH))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XI (XO (XO (XI (XI (XO
    (XI (XO (XO (XI (XO (XI (XO (XO (XI (XO (XO (XI (XO (XI (XO (XO (XO (XO (XI (XO
    XH))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XI (XO (XO (XO (XO (XI (XO
    (XI (XO (XI (XO (XO (XO (XO (XI (XI (XI (XO (XI (XI (XO (XI (XI (XI (XI (XO (XO
    XH)))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XO (XI (XI (XI (XO (XO (XI
    (XO (XO (XO (XO (XI (XO (XO (XI (XI (XO (XI (XI (XO (XO (XO (XO (XI (XI (XI (XO
    XH)))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XI (XI (XI (XI (XI (XI (XI
    (XO (XI (XI (XO (XI (XI (XO (XO (XO (XI (XI (XO (XI (XO (XO (XI (XO (XI (XI (XO (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XO (XO (XI (XO (XO (XO (XI
    (XO (XI (XI (XO (XO (XO (XO (XO (XO (XO (XI (XI (XI (XO (XO (XI (XI (XO (XO (XI (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XI (XO (XI (XO (XI (XO (XI
    (XI (XO (XO (XI (XI (XI (XO (XO (XI (XO (XI (XO (XO (XO (XO (XI (XO (XI (XO (XO (XI
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XO (XI (XI (XI (XO (XI (XO
    (XI (XO (XI (XO (XO (XO (XO (XO (XI (XO (XI (XO (XI (XI (XO (XO (XI (XI (XO (XI (XI
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XI (XI (XO (XI (XO (XO (XI
    (XO (XO (XI (XO (XO (XI (XI (XO (XI (XO (XO (XO (XO (XI (XI (XI (XO (XO (XO (XO (XO
    (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XI (XO (XO (XO (XO (XI
    (XO (XO (XI (XI (XO (XI (XO (XO (XO (XI (XO (XO (XI (XI (XI (XO (XO (XI (XO (XO (XI
    (XO (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XO (XO (XO (XI (XO
    (XI (XO (XO (XO (XI (XO (XI (XI (XI (XI (XI (XI (XI (XI (XI (XO (XI (XO (XI (XO (XO
    (XO (XI (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XO (XI (XO (XO
    (XI (XO (XO (XI (XI (XO (XO (XI (XI (XO (XO (XI (XO (XI (XI (XO (XO (XO (XO (XO (XO
    (XI (XO (XI (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XO (XO (XI
    (XI (XI (XO (XI (XI (XO (XI (XO (XO (XO (XI (XI (XI (XO (XI (XO (XO (XI (XO (XO (XI
    (XO (XO (XO (XO (XI XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XO (XO
    (XO (XI (XO (XI (XI (XO (XO (XO (XI (XO (XI (XO (XO (XO (XI (XI (XO (XI (XI (XO (XI
    (XI (XI (XO (XO (XO (XI XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XO
    (XI (XI (XO (XO (XO (XO (XO (XO (XI (XO (XI (XI (XI (XO (XI (XO (XO (XI (XO (XO (XI
    (XI (XO (XO (XO (XI (XO (XI XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO
    (XI (XO (XO (XI (XO (XO (XO (XI (XI (XO (XO (XO (XO (XO (XI (XO (XO (XI (XI (XO (XO
    (XI (XO (XI (XI (XO (XI (XO (XI XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI
    (XO (XI (XO (XO (XO (XO (XI (XI (XO (XI (XO (XI (XI (XO (XO (XO (XI (XI (XI (XO (XO
    (XO (XO (XO (XO (XI (XO (XI (XI (XI XH)))))))))))))))))))))))))))))))), (Cons ((Npos
    (XO (XO (XO (XO (XI (XI (XI (XO (XO (XO (XO (XO (XO (XI (XO (XI (XO (XI (XO (XI (XO
    (XI (XI (XO (XO (XO (XO (XO XH))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI
    (XI (XO (XI (XO (XO (XO (XI (XO (XO (XO (XO (XO (XI (XI (XO (XO (XI (XO (XO (XI (XO
    (XI (XI (XO (XO (XI XH))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XO (XI
    (XO (XO (XO (XO (XO (XO (XI (XI (XO (XI (XI (XO (XI (XI (XI (XO (XI (XI (XO (XO (XO
    (XI (XI (XI XH))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XI (XI (XO (XO
    (XI (XO (XI (XI (XI (XO (XI (XI (XI (XO (XO (XO (XO (XI (XO (XO (XI (XO (XI (XI (XI
    (XO (XO XH)))))))))))))))))))))))))))))), (Cons ((Npos (XI (XO (XI (XO (XI (XI (XO
    (XI (XO (XO (XI (XI (XI (XI (XO (XI (XO (XO (XO (XO (XI (XI (XO (XI (XO (XO (XI (XO
    (XI XH)))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XO (XO (XI (XI (XO (XI
    (XO (XO (XI (XI (XO (XO (XO (XO (XO (XO (XI (XI (XI (XO (XO (XO (XI (XO (XO (XI (XI
    XH)))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XO (XI (XO (XO (XI (XO (XO
    (XI (XO (XI (XO (XI (XO (XI (XO (XO (XO (XI (XI (XO (XI (XI (XO (XI (XI (XI (XO (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XI (XI (XO (XO (XI (XO (XO
    (XI (XO (XI (XO (XO (XI (XI (XO (XO (XI (XI (XI (XO (XO (XI (XI (XI (XO (XI (XI (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XO (XO (XI (XI (XI (XI (XI
    (XI (XI (XI (XO (XI (XI (XO (XO (XI (XI (XI (XO (XI (XO (XO (XO (XO (XO (XI (XO (XI
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XI (XI (XO (XI (XI (XI (XO
    (XI (XO (XO (XO (XO (XO (XI (XI (XI (XI (XI (XO (XO (XO (XI (XO (XO (XI (XO (XI (XI
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XI (XI (XO (XI (XI (XO (XI
    (XI (XO (XO (XO (XI (XI (XO (XI (XO (XI (XO (XO (XI (XO (XI (XO (XO (XO (XI (XI (XI
    XH))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XI (XO (XI (XO (XO (XO (XO
    (XO (XO (XI (XI (XI (XI (XO (XO (XO (XO (XI (XO (XO (XI (XI (XO (XO (XI (XO (XO (XO
    (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XO (XO (XI (XO (XO (XO (XO
    (XO (XI (XO (XO (XO (XO (XO (XO (XI (XI (XI (XO (XO (XO (XI (XI (XO (XO (XI (XI (XO
    (XO (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XO (XI (XI (XI (XI
    (XI (XI (XI (XI (XI (XI (XI (XI (XI (XO (XI (XI (XI (XI (XI (XO (XI (XO (XO (XO (XO
    (XI (XO (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XO (XI (XO (XI
    (XI (XI (XO (XO (XI (XI (XO (XI (XI (XO (XO (XO (XO (XO (XI (XO (XI (XO (XO (XO (XI
    (XO (XO (XI (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XI (XI (XI (XO (XI
    (XI (XI (XI (XI (XI (XO (XO (XO (XI (XO (XI (XI (XO (XO (XI (XI (XI (XI (XI (XO (XI
    (XI (XI (XI (XI (XO XH)))))))))))))))))))))))))))))))), (Cons ((Npos (XO (XI (XO (XO
    (XI (XI (XI (XI (XO (XO (XO (XI (XI (XI (XI (XO (XI (XO (XO (XO (XI (XI (XI (XO (XO
    (XI (XI (XO (XO (XO (XI XH)))))))))))))))))))))))))))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val get_zero_bytes : nat -> char list **)

let rec get_zero_bytes = function
| O -> Nil
| S v' -> Cons ('\x00', (get_zero_bytes v'))

(** val message_padding : nat -> char list **)

let message_padding = function
| O -> Nil
| S v' -> Cons ('\x80', (get_zero_bytes v'))

(** val append_zero_in_length_byte : char list -> char list **)

let append_zero_in_length_byte lb =
  let nl = length lb in
  if Nat.leb nl (S (S (S (S (S (S (S (S O))))))))
  then app (get_zero_bytes (sub (S (S (S (S (S (S (S (S O)))))))) nl)) lb
  else lb

(** val message_length_byte : char list -> char list **)

let message_length_byte m0 =
  let n0 = N.of_nat (length m0) in
  let mbits = N.mul (Npos (XO (XO (XO XH)))) n0 in
  append_zero_in_length_byte (big_endien_list_N mbits)

(** val prepared_message : char list -> char list **)

let prepared_message m0 =
  let n0 = N.of_nat (length m0) in
  let mbits = N.mul (Npos (XO (XO (XO XH)))) n0 in
  let k0 =
    Z.to_N
      (Z.modulo
        (Z.sub (Zpos (XO (XO (XO (XO (XO (XO (XI (XI XH)))))))))
          (Z.add (Z.of_N mbits) (Zpos XH))) (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO
        XH)))))))))))
  in
  let wt = N.div (N.add (Npos XH) k0) (Npos (XO (XO (XO XH)))) in
  app m0 (app (message_padding (N.to_nat wt)) (message_length_byte m0))

(** val big_endien_32_bit_to_N : char -> char -> char -> char -> n **)

let big_endien_32_bit_to_N a b c d =
  N.add
    (N.mul
      (N.add
        (N.mul
          (N.add (N.mul (to_N0 a) (Npos (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))))
            (to_N0 b)) (Npos (XO (XO (XO (XO (XO (XO (XO (XO XH)))))))))) (to_N0 c))
      (Npos (XO (XO (XO (XO (XO (XO (XO (XO XH)))))))))) (to_N0 d)

(** val m : char list -> nat -> nat -> n **)

let m m0 i j =
  big_endien_32_bit_to_N
    (nth
      (add
        (mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) i)
        (mul (S (S (S (S O)))) j)) (prepared_message m0) '\x00')
    (nth
      (add
        (add
          (mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) i)
          (mul (S (S (S (S O)))) j)) (S O)) (prepared_message m0) '\x00')
    (nth
      (add
        (add
          (mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) i)
          (mul (S (S (S (S O)))) j)) (S (S O))) (prepared_message m0) '\x00')
    (nth
      (add
        (add
          (mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) i)
          (mul (S (S (S (S O)))) j)) (S (S (S O)))) (prepared_message m0) '\x00')

(** val from_n : nat -> nat list **)

let rec from_n = function
| O -> Nil
| S n' -> Cons (n', (from_n n'))

(** val upto_n : nat -> nat list **)

let upto_n n0 =
  rev (from_n n0)

(** val w : char list -> nat -> n list **)

let w m0 i =
  fold_left (fun acc t ->
    let wtp =
      if Nat.ltb t (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))
      then m m0 i t
      else let a = nth (sub t (S (S O))) acc N0 in
           let b = nth (sub t (S (S (S (S (S (S (S O)))))))) acc N0 in
           let c =
             nth (sub t (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))
               acc N0
           in
           let d =
             nth
               (sub t (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))
               acc N0
           in
           add0 (add0 (add0 (sigma_UU2081_0 a) b) (sigma_UU2080_0 c)) d
    in
    app acc (Cons (wtp, Nil)))
    (upto_n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S
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
        add0 (add0 (add0 (add0 h1 (sigma_UU2081_ e0)) (ch e0 f0 g0)) (nth t k N0))
          (nth t w0 N0)
      in
      let t_UU2082_ = add0 (sigma_UU2080_ a0) (maj a0 b0 c0) in
      let e1 = add0 d0 t_UU2081_ in
      let a1 = add0 t_UU2081_ t_UU2082_ in
      Pair ((Pair ((Pair ((Pair ((Pair ((Pair ((Pair (a1, a0)), b0)), c0)), e1)), e0)),
      f0)), g0))
      (upto_n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Pair ((Pair
      ((Pair ((Pair ((Pair ((Pair ((Pair (a, b)), c)), d)), e)), f)), g)), h0))
  in
  let Pair (p0, g0) = p in
  let Pair (p1, f0) = p0 in
  let Pair (p2, e0) = p1 in
  let Pair (p3, d0) = p2 in
  let Pair (p4, c0) = p3 in
  let Pair (a0, b0) = p4 in
  Cons ((add0 a0 (nth O h N0)), (Cons ((add0 b0 (nth (S O) h N0)), (Cons
  ((add0 c0 (nth (S (S O)) h N0)), (Cons ((add0 d0 (nth (S (S (S O))) h N0)), (Cons
  ((add0 e0 (nth (S (S (S (S O)))) h N0)), (Cons
  ((add0 f0 (nth (S (S (S (S (S O))))) h N0)), (Cons
  ((add0 g0 (nth (S (S (S (S (S (S O)))))) h N0)), (Cons
  ((add0 h1 (nth (S (S (S (S (S (S (S O))))))) h N0)), Nil)))))))))))))))

(** val sha256 : char list -> n list **)

let sha256 m0 =
  let n0 = N.of_nat (length m0) in
  let mbits = N.mul (Npos (XO (XO (XO XH)))) n0 in
  let k0 =
    Z.to_N
      (Z.modulo
        (Z.sub (Zpos (XO (XO (XO (XO (XO (XO (XI (XI XH)))))))))
          (Z.add (Z.of_N mbits) (Zpos XH))) (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO
        XH)))))))))))
  in
  let wt = N.div (N.add (Npos XH) k0) (Npos (XO (XO (XO XH)))) in
  let ms =
    N.div (N.add (N.add n0 wt) (Npos (XO (XO (XO XH))))) (Npos (XO (XO (XO (XO (XO (XO
      XH)))))))
  in
  fold_left (fun h i -> sha256_intermediate (w m0 i) h) (upto_n (N.to_nat ms)) h_UU2080_

(** val concat_bytes : char list -> n **)

let concat_bytes bs =
  fold_left (fun acc b ->
    N.add (N.mul acc (N.shiftl (Npos XH) (Npos (XO (XO (XO XH)))))) (to_N0 b)) bs N0

(** val sha256_string : char list -> n **)

let sha256_string s =
  concat_bytes (flat_map big_endien_list_N (sha256 (list_byte_of_string s)))
