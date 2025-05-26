module CoqSolver where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec =
  and_rect

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

data CompareSpecT =
   CompEqT
 | CompLtT
 | CompGtT

compareSpec2Type :: Comparison -> CompareSpecT
compareSpec2Type c =
  case c of {
   Eq -> CompEqT;
   Lt -> CompLtT;
   Gt -> CompGtT}

type CompSpecT a = CompareSpecT

compSpec2Type :: a1 -> a1 -> Comparison -> CompSpecT a1
compSpec2Type _ _ =
  compareSpec2Type

sumbool_rect :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rect f f0 s =
  case s of {
   Prelude.True -> f __;
   Prelude.False -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rec =
  sumbool_rect

data Uint =
   Nil
 | D0 Uint
 | D1 Uint
 | D2 Uint
 | D3 Uint
 | D4 Uint
 | D5 Uint
 | D6 Uint
 | D7 Uint
 | D8 Uint
 | D9 Uint

data Signed_int =
   Pos Uint
 | Neg Uint

revapp :: Uint -> Uint -> Uint
revapp d d' =
  case d of {
   Nil -> d';
   D0 d0 -> revapp d0 (D0 d');
   D1 d0 -> revapp d0 (D1 d');
   D2 d0 -> revapp d0 (D2 d');
   D3 d0 -> revapp d0 (D3 d');
   D4 d0 -> revapp d0 (D4 d');
   D5 d0 -> revapp d0 (D5 d');
   D6 d0 -> revapp d0 (D6 d');
   D7 d0 -> revapp d0 (D7 d');
   D8 d0 -> revapp d0 (D8 d');
   D9 d0 -> revapp d0 (D9 d')}

rev :: Uint -> Uint
rev d =
  revapp d Nil

double :: Uint -> Uint
double d =
  case d of {
   Nil -> Nil;
   D0 d0 -> D0 (double d0);
   D1 d0 -> D2 (double d0);
   D2 d0 -> D4 (double d0);
   D3 d0 -> D6 (double d0);
   D4 d0 -> D8 (double d0);
   D5 d0 -> D0 (succ_double d0);
   D6 d0 -> D2 (succ_double d0);
   D7 d0 -> D4 (succ_double d0);
   D8 d0 -> D6 (succ_double d0);
   D9 d0 -> D8 (succ_double d0)}

succ_double :: Uint -> Uint
succ_double d =
  case d of {
   Nil -> D1 Nil;
   D0 d0 -> D1 (double d0);
   D1 d0 -> D3 (double d0);
   D2 d0 -> D5 (double d0);
   D3 d0 -> D7 (double d0);
   D4 d0 -> D9 (double d0);
   D5 d0 -> D1 (succ_double d0);
   D6 d0 -> D3 (succ_double d0);
   D7 d0 -> D5 (succ_double d0);
   D8 d0 -> D7 (succ_double d0);
   D9 d0 -> D9 (succ_double d0)}

data Uint0 =
   Nil0
 | D10 Uint0
 | D11 Uint0
 | D12 Uint0
 | D13 Uint0
 | D14 Uint0
 | D15 Uint0
 | D16 Uint0
 | D17 Uint0
 | D18 Uint0
 | D19 Uint0
 | Da Uint0
 | Db Uint0
 | Dc Uint0
 | Dd Uint0
 | De Uint0
 | Df Uint0

data Signed_int0 =
   Pos0 Uint0
 | Neg0 Uint0

revapp0 :: Uint0 -> Uint0 -> Uint0
revapp0 d d' =
  case d of {
   Nil0 -> d';
   D10 d0 -> revapp0 d0 (D10 d');
   D11 d0 -> revapp0 d0 (D11 d');
   D12 d0 -> revapp0 d0 (D12 d');
   D13 d0 -> revapp0 d0 (D13 d');
   D14 d0 -> revapp0 d0 (D14 d');
   D15 d0 -> revapp0 d0 (D15 d');
   D16 d0 -> revapp0 d0 (D16 d');
   D17 d0 -> revapp0 d0 (D17 d');
   D18 d0 -> revapp0 d0 (D18 d');
   D19 d0 -> revapp0 d0 (D19 d');
   Da d0 -> revapp0 d0 (Da d');
   Db d0 -> revapp0 d0 (Db d');
   Dc d0 -> revapp0 d0 (Dc d');
   Dd d0 -> revapp0 d0 (Dd d');
   De d0 -> revapp0 d0 (De d');
   Df d0 -> revapp0 d0 (Df d')}

rev0 :: Uint0 -> Uint0
rev0 d =
  revapp0 d Nil0

double0 :: Uint0 -> Uint0
double0 d =
  case d of {
   Nil0 -> Nil0;
   D10 d0 -> D10 (double0 d0);
   D11 d0 -> D12 (double0 d0);
   D12 d0 -> D14 (double0 d0);
   D13 d0 -> D16 (double0 d0);
   D14 d0 -> D18 (double0 d0);
   D15 d0 -> Da (double0 d0);
   D16 d0 -> Dc (double0 d0);
   D17 d0 -> De (double0 d0);
   D18 d0 -> D10 (succ_double0 d0);
   D19 d0 -> D12 (succ_double0 d0);
   Da d0 -> D14 (succ_double0 d0);
   Db d0 -> D16 (succ_double0 d0);
   Dc d0 -> D18 (succ_double0 d0);
   Dd d0 -> Da (succ_double0 d0);
   De d0 -> Dc (succ_double0 d0);
   Df d0 -> De (succ_double0 d0)}

succ_double0 :: Uint0 -> Uint0
succ_double0 d =
  case d of {
   Nil0 -> D11 Nil0;
   D10 d0 -> D11 (double0 d0);
   D11 d0 -> D13 (double0 d0);
   D12 d0 -> D15 (double0 d0);
   D13 d0 -> D17 (double0 d0);
   D14 d0 -> D19 (double0 d0);
   D15 d0 -> Db (double0 d0);
   D16 d0 -> Dd (double0 d0);
   D17 d0 -> Df (double0 d0);
   D18 d0 -> D11 (succ_double0 d0);
   D19 d0 -> D13 (succ_double0 d0);
   Da d0 -> D15 (succ_double0 d0);
   Db d0 -> D17 (succ_double0 d0);
   Dc d0 -> D19 (succ_double0 d0);
   Dd d0 -> Db (succ_double0 d0);
   De d0 -> Dd (succ_double0 d0);
   Df d0 -> Df (succ_double0 d0)}

data Uint1 =
   UIntDecimal Uint
 | UIntHexadecimal Uint0

data Signed_int1 =
   IntDecimal Signed_int
 | IntHexadecimal Signed_int0

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

max :: Nat -> Nat -> Nat
max n m =
  case n of {
   O -> m;
   S n' -> case m of {
            O -> n;
            S m' -> S (max n' m')}}

min :: Nat -> Nat -> Nat
min n m =
  case n of {
   O -> O;
   S n' -> case m of {
            O -> O;
            S m' -> S (min n' m')}}

data Reflect =
   ReflectT
 | ReflectF

iff_reflect :: Prelude.Bool -> Reflect
iff_reflect b =
  case b of {
   Prelude.True -> and_rec (\_ _ -> ReflectT);
   Prelude.False -> and_rec (\_ _ -> ReflectF)}

data Positive =
   XI Positive
 | XO Positive
 | XH

positive_rect :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                 Positive -> a1
positive_rect f f0 f1 p =
  case p of {
   XI p0 -> f p0 (positive_rect f f0 f1 p0);
   XO p0 -> f0 p0 (positive_rect f f0 f1 p0);
   XH -> f1}

positive_rec :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                Positive -> a1
positive_rec =
  positive_rect

data N =
   N0
 | Npos Positive

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add0 :: Positive -> Positive -> Positive
add0 x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add0 p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add0 p q);
     XO q -> XO (add0 p q);
     XH -> XI p};
   XH -> case y of {
          XI q -> XO (succ q);
          XO q -> XI q;
          XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add0 p q);
     XH -> XO (succ p)};
   XH -> case y of {
          XI q -> XI (succ q);
          XO q -> XO (succ q);
          XH -> XI XH}}

pred_double :: Positive -> Positive
pred_double x =
  case x of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double p);
   XH -> XH}

compare_cont :: Comparison -> Positive -> Positive -> Comparison
compare_cont r x y =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont r p q;
     XO q -> compare_cont Gt p q;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont Lt p q;
     XO q -> compare_cont r p q;
     XH -> Gt};
   XH -> case y of {
          XH -> r;
          _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare =
  compare_cont Eq

min0 :: Positive -> Positive -> Positive
min0 p p' =
  case compare p p' of {
   Gt -> p';
   _ -> p}

max0 :: Positive -> Positive -> Positive
max0 p p' =
  case compare p p' of {
   Gt -> p;
   _ -> p'}

eqb :: Positive -> Positive -> Prelude.Bool
eqb p q =
  case p of {
   XI p0 -> case q of {
             XI q0 -> eqb p0 q0;
             _ -> Prelude.False};
   XO p0 -> case q of {
             XO q0 -> eqb p0 q0;
             _ -> Prelude.False};
   XH -> case q of {
          XH -> Prelude.True;
          _ -> Prelude.False}}

double1 :: Z -> Z
double1 x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (XO p);
   Zneg p -> Zneg (XO p)}

succ_double1 :: Z -> Z
succ_double1 x =
  case x of {
   Z0 -> Zpos XH;
   Zpos p -> Zpos (XI p);
   Zneg p -> Zneg (pred_double p)}

pred_double0 :: Z -> Z
pred_double0 x =
  case x of {
   Z0 -> Zneg XH;
   Zpos p -> Zpos (pred_double p);
   Zneg p -> Zneg (XI p)}

pos_sub :: Positive -> Positive -> Z
pos_sub x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double1 (pos_sub p q);
     XO q -> succ_double1 (pos_sub p q);
     XH -> Zpos (XO p)};
   XO p ->
    case y of {
     XI q -> pred_double0 (pos_sub p q);
     XO q -> double1 (pos_sub p q);
     XH -> Zpos (pred_double p)};
   XH ->
    case y of {
     XI q -> Zneg (XO q);
     XO q -> Zneg (pred_double q);
     XH -> Z0}}

add1 :: Z -> Z -> Z
add1 x y =
  case x of {
   Z0 -> y;
   Zpos x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> Zpos (add0 x' y');
     Zneg y' -> pos_sub x' y'};
   Zneg x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> pos_sub y' x';
     Zneg y' -> Zneg (add0 x' y')}}

compare0 :: Z -> Z -> Comparison
compare0 x y =
  case x of {
   Z0 -> case y of {
          Z0 -> Eq;
          Zpos _ -> Lt;
          Zneg _ -> Gt};
   Zpos x' -> case y of {
               Zpos y' -> compare x' y';
               _ -> Gt};
   Zneg x' -> case y of {
               Zneg y' -> compOpp (compare x' y');
               _ -> Lt}}

leb :: Z -> Z -> Prelude.Bool
leb x y =
  case compare0 x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

ltb :: Z -> Z -> Prelude.Bool
ltb x y =
  case compare0 x y of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

max1 :: Z -> Z -> Z
max1 n m =
  case compare0 n m of {
   Lt -> m;
   _ -> n}

type T = Positive

succ0 :: Positive -> Positive
succ0 x =
  case x of {
   XI p -> XO (succ0 p);
   XO p -> XI p;
   XH -> XO XH}

add2 :: Positive -> Positive -> Positive
add2 x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry0 p q);
     XO q -> XI (add2 p q);
     XH -> XO (succ0 p)};
   XO p ->
    case y of {
     XI q -> XI (add2 p q);
     XO q -> XO (add2 p q);
     XH -> XI p};
   XH -> case y of {
          XI q -> XO (succ0 q);
          XO q -> XI q;
          XH -> XO XH}}

add_carry0 :: Positive -> Positive -> Positive
add_carry0 x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry0 p q);
     XO q -> XO (add_carry0 p q);
     XH -> XI (succ0 p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry0 p q);
     XO q -> XI (add2 p q);
     XH -> XO (succ0 p)};
   XH -> case y of {
          XI q -> XI (succ0 q);
          XO q -> XO (succ0 q);
          XH -> XI XH}}

pred_double1 :: Positive -> Positive
pred_double1 x =
  case x of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double1 p);
   XH -> XH}

pred :: Positive -> Positive
pred x =
  case x of {
   XI p -> XO p;
   XO p -> pred_double1 p;
   XH -> XH}

pred_N :: Positive -> N
pred_N x =
  case x of {
   XI p -> Npos (XO p);
   XO p -> Npos (pred_double1 p);
   XH -> N0}

data Mask =
   IsNul
 | IsPos Positive
 | IsNeg

mask_rect :: a1 -> (Positive -> a1) -> a1 -> Mask -> a1
mask_rect f f0 f1 m =
  case m of {
   IsNul -> f;
   IsPos p -> f0 p;
   IsNeg -> f1}

mask_rec :: a1 -> (Positive -> a1) -> a1 -> Mask -> a1
mask_rec =
  mask_rect

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos XH;
   IsPos p -> IsPos (XI p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos (XO p);
   x0 -> x0}

double_pred_mask :: Positive -> Mask
double_pred_mask x =
  case x of {
   XI p -> IsPos (XO (XO p));
   XO p -> IsPos (XO (pred_double1 p));
   XH -> IsNul}

pred_mask :: Mask -> Mask
pred_mask p =
  case p of {
   IsPos q -> case q of {
               XH -> IsNul;
               _ -> IsPos (pred q)};
   _ -> IsNeg}

sub_mask :: Positive -> Positive -> Mask
sub_mask x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double_mask (sub_mask p q);
     XO q -> succ_double_mask (sub_mask p q);
     XH -> IsPos (XO p)};
   XO p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double1 p)};
   XH -> case y of {
          XH -> IsNul;
          _ -> IsNeg}}

sub_mask_carry :: Positive -> Positive -> Mask
sub_mask_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double1 p)};
   XO p ->
    case y of {
     XI q -> double_mask (sub_mask_carry p q);
     XO q -> succ_double_mask (sub_mask_carry p q);
     XH -> double_pred_mask p};
   XH -> IsNeg}

sub :: Positive -> Positive -> Positive
sub x y =
  case sub_mask x y of {
   IsPos z -> z;
   _ -> XH}

mul :: Positive -> Positive -> Positive
mul x y =
  case x of {
   XI p -> add2 y (XO (mul p y));
   XO p -> XO (mul p y);
   XH -> y}

iter :: (a1 -> a1) -> a1 -> Positive -> a1
iter f x n =
  case n of {
   XI n' -> f (iter f (iter f x n') n');
   XO n' -> iter f (iter f x n') n';
   XH -> f x}

pow :: Positive -> Positive -> Positive
pow x =
  iter (mul x) XH

square :: Positive -> Positive
square p =
  case p of {
   XI p0 -> XI (XO (add2 (square p0) p0));
   XO p0 -> XO (XO (square p0));
   XH -> XH}

div2 :: Positive -> Positive
div2 p =
  case p of {
   XI p0 -> p0;
   XO p0 -> p0;
   XH -> XH}

div2_up :: Positive -> Positive
div2_up p =
  case p of {
   XI p0 -> succ0 p0;
   XO p0 -> p0;
   XH -> XH}

size_nat :: Positive -> Nat
size_nat p =
  case p of {
   XI p0 -> S (size_nat p0);
   XO p0 -> S (size_nat p0);
   XH -> S O}

size :: Positive -> Positive
size p =
  case p of {
   XI p0 -> succ0 (size p0);
   XO p0 -> succ0 (size p0);
   XH -> XH}

compare_cont0 :: Comparison -> Positive -> Positive -> Comparison
compare_cont0 r x y =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont0 r p q;
     XO q -> compare_cont0 Gt p q;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont0 Lt p q;
     XO q -> compare_cont0 r p q;
     XH -> Gt};
   XH -> case y of {
          XH -> r;
          _ -> Lt}}

compare1 :: Positive -> Positive -> Comparison
compare1 =
  compare_cont0 Eq

min1 :: Positive -> Positive -> Positive
min1 p p' =
  case compare1 p p' of {
   Gt -> p';
   _ -> p}

max2 :: Positive -> Positive -> Positive
max2 p p' =
  case compare1 p p' of {
   Gt -> p;
   _ -> p'}

eqb0 :: Positive -> Positive -> Prelude.Bool
eqb0 p q =
  case p of {
   XI p0 -> case q of {
             XI q0 -> eqb0 p0 q0;
             _ -> Prelude.False};
   XO p0 -> case q of {
             XO q0 -> eqb0 p0 q0;
             _ -> Prelude.False};
   XH -> case q of {
          XH -> Prelude.True;
          _ -> Prelude.False}}

leb0 :: Positive -> Positive -> Prelude.Bool
leb0 x y =
  case compare1 x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

ltb0 :: Positive -> Positive -> Prelude.Bool
ltb0 x y =
  case compare1 x y of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

sqrtrem_step :: (Positive -> Positive) -> (Positive -> Positive) -> ((,)
                Positive Mask) -> (,) Positive Mask
sqrtrem_step f g p =
  case p of {
   (,) s y ->
    case y of {
     IsPos r ->
      let {s' = XI (XO s)} in
      let {r' = g (f r)} in
      case leb0 s' r' of {
       Prelude.True -> (,) (XI s) (sub_mask r' s');
       Prelude.False -> (,) (XO s) (IsPos r')};
     _ -> (,) (XO s) (sub_mask (g (f XH)) (XO (XO XH)))}}

sqrtrem :: Positive -> (,) Positive Mask
sqrtrem p =
  case p of {
   XI p0 ->
    case p0 of {
     XI p1 -> sqrtrem_step (\x -> XI x) (\x -> XI x) (sqrtrem p1);
     XO p1 -> sqrtrem_step (\x -> XO x) (\x -> XI x) (sqrtrem p1);
     XH -> (,) XH (IsPos (XO XH))};
   XO p0 ->
    case p0 of {
     XI p1 -> sqrtrem_step (\x -> XI x) (\x -> XO x) (sqrtrem p1);
     XO p1 -> sqrtrem_step (\x -> XO x) (\x -> XO x) (sqrtrem p1);
     XH -> (,) XH (IsPos XH)};
   XH -> (,) XH IsNul}

sqrt :: Positive -> Positive
sqrt p =
  fst (sqrtrem p)

gcdn :: Nat -> Positive -> Positive -> Positive
gcdn n a b =
  case n of {
   O -> XH;
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare1 a' b' of {
         Eq -> a;
         Lt -> gcdn n0 (sub b' a') a;
         Gt -> gcdn n0 (sub a' b') b};
       XO b0 -> gcdn n0 a b0;
       XH -> XH};
     XO a0 ->
      case b of {
       XI _ -> gcdn n0 a0 b;
       XO b0 -> XO (gcdn n0 a0 b0);
       XH -> XH};
     XH -> XH}}

gcd :: Positive -> Positive -> Positive
gcd a b =
  gcdn (add (size_nat a) (size_nat b)) a b

ggcdn :: Nat -> Positive -> Positive -> (,) Positive ((,) Positive Positive)
ggcdn n a b =
  case n of {
   O -> (,) XH ((,) a b);
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare1 a' b' of {
         Eq -> (,) a ((,) XH XH);
         Lt ->
          case ggcdn n0 (sub b' a') a of {
           (,) g p ->
            case p of {
             (,) ba aa -> (,) g ((,) aa (add2 aa (XO ba)))}};
         Gt ->
          case ggcdn n0 (sub a' b') b of {
           (,) g p ->
            case p of {
             (,) ab bb -> (,) g ((,) (add2 bb (XO ab)) bb)}}};
       XO b0 ->
        case ggcdn n0 a b0 of {
         (,) g p -> case p of {
                     (,) aa bb -> (,) g ((,) aa (XO bb))}};
       XH -> (,) XH ((,) a XH)};
     XO a0 ->
      case b of {
       XI _ ->
        case ggcdn n0 a0 b of {
         (,) g p -> case p of {
                     (,) aa bb -> (,) g ((,) (XO aa) bb)}};
       XO b0 -> case ggcdn n0 a0 b0 of {
                 (,) g p -> (,) (XO g) p};
       XH -> (,) XH ((,) a XH)};
     XH -> (,) XH ((,) XH b)}}

ggcd :: Positive -> Positive -> (,) Positive ((,) Positive Positive)
ggcd a b =
  ggcdn (add (size_nat a) (size_nat b)) a b

nsucc_double :: N -> N
nsucc_double x =
  case x of {
   N0 -> Npos XH;
   Npos p -> Npos (XI p)}

ndouble :: N -> N
ndouble n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (XO p)}

lor :: Positive -> Positive -> Positive
lor p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> XI (lor p0 q0);
     XO q0 -> XI (lor p0 q0);
     XH -> p};
   XO p0 ->
    case q of {
     XI q0 -> XI (lor p0 q0);
     XO q0 -> XO (lor p0 q0);
     XH -> XI p0};
   XH -> case q of {
          XO q0 -> XI q0;
          _ -> q}}

land :: Positive -> Positive -> N
land p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> nsucc_double (land p0 q0);
     XO q0 -> ndouble (land p0 q0);
     XH -> Npos XH};
   XO p0 ->
    case q of {
     XI q0 -> ndouble (land p0 q0);
     XO q0 -> ndouble (land p0 q0);
     XH -> N0};
   XH -> case q of {
          XO _ -> N0;
          _ -> Npos XH}}

ldiff :: Positive -> Positive -> N
ldiff p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> ndouble (ldiff p0 q0);
     XO q0 -> nsucc_double (ldiff p0 q0);
     XH -> Npos (XO p0)};
   XO p0 ->
    case q of {
     XI q0 -> ndouble (ldiff p0 q0);
     XO q0 -> ndouble (ldiff p0 q0);
     XH -> Npos p};
   XH -> case q of {
          XO _ -> Npos XH;
          _ -> N0}}

lxor :: Positive -> Positive -> N
lxor p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> ndouble (lxor p0 q0);
     XO q0 -> nsucc_double (lxor p0 q0);
     XH -> Npos (XO p0)};
   XO p0 ->
    case q of {
     XI q0 -> nsucc_double (lxor p0 q0);
     XO q0 -> ndouble (lxor p0 q0);
     XH -> Npos (XI p0)};
   XH -> case q of {
          XI q0 -> Npos (XO q0);
          XO q0 -> Npos (XI q0);
          XH -> N0}}

shiftl_nat :: Positive -> Nat -> Positive
shiftl_nat p =
  nat_rect p (\_ x -> XO x)

shiftr_nat :: Positive -> Nat -> Positive
shiftr_nat p =
  nat_rect p (\_ -> div2)

shiftl :: Positive -> N -> Positive
shiftl p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter (\x -> XO x) p n0}

shiftr :: Positive -> N -> Positive
shiftr p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter div2 p n0}

testbit_nat :: Positive -> Nat -> Prelude.Bool
testbit_nat p n =
  case p of {
   XI p0 -> case n of {
             O -> Prelude.True;
             S n' -> testbit_nat p0 n'};
   XO p0 -> case n of {
             O -> Prelude.False;
             S n' -> testbit_nat p0 n'};
   XH -> case n of {
          O -> Prelude.True;
          S _ -> Prelude.False}}

testbit :: Positive -> N -> Prelude.Bool
testbit p n =
  case p of {
   XI p0 ->
    case n of {
     N0 -> Prelude.True;
     Npos n0 -> testbit p0 (pred_N n0)};
   XO p0 ->
    case n of {
     N0 -> Prelude.False;
     Npos n0 -> testbit p0 (pred_N n0)};
   XH -> case n of {
          N0 -> Prelude.True;
          Npos _ -> Prelude.False}}

iter_op :: (a1 -> a1 -> a1) -> Positive -> a1 -> a1
iter_op op p a =
  case p of {
   XI p0 -> op a (iter_op op p0 (op a a));
   XO p0 -> iter_op op p0 (op a a);
   XH -> a}

to_nat :: Positive -> Nat
to_nat x =
  iter_op add x (S O)

of_nat :: Nat -> Positive
of_nat n =
  case n of {
   O -> XH;
   S x -> case x of {
           O -> XH;
           S _ -> succ0 (of_nat x)}}

of_succ_nat :: Nat -> Positive
of_succ_nat n =
  case n of {
   O -> XH;
   S x -> succ0 (of_succ_nat x)}

of_uint_acc :: Uint -> Positive -> Positive
of_uint_acc d acc =
  case d of {
   Nil -> acc;
   D0 l -> of_uint_acc l (mul (XO (XI (XO XH))) acc);
   D1 l -> of_uint_acc l (add2 XH (mul (XO (XI (XO XH))) acc));
   D2 l -> of_uint_acc l (add2 (XO XH) (mul (XO (XI (XO XH))) acc));
   D3 l -> of_uint_acc l (add2 (XI XH) (mul (XO (XI (XO XH))) acc));
   D4 l -> of_uint_acc l (add2 (XO (XO XH)) (mul (XO (XI (XO XH))) acc));
   D5 l -> of_uint_acc l (add2 (XI (XO XH)) (mul (XO (XI (XO XH))) acc));
   D6 l -> of_uint_acc l (add2 (XO (XI XH)) (mul (XO (XI (XO XH))) acc));
   D7 l -> of_uint_acc l (add2 (XI (XI XH)) (mul (XO (XI (XO XH))) acc));
   D8 l -> of_uint_acc l (add2 (XO (XO (XO XH))) (mul (XO (XI (XO XH))) acc));
   D9 l -> of_uint_acc l (add2 (XI (XO (XO XH))) (mul (XO (XI (XO XH))) acc))}

of_uint :: Uint -> N
of_uint d =
  case d of {
   Nil -> N0;
   D0 l -> of_uint l;
   D1 l -> Npos (of_uint_acc l XH);
   D2 l -> Npos (of_uint_acc l (XO XH));
   D3 l -> Npos (of_uint_acc l (XI XH));
   D4 l -> Npos (of_uint_acc l (XO (XO XH)));
   D5 l -> Npos (of_uint_acc l (XI (XO XH)));
   D6 l -> Npos (of_uint_acc l (XO (XI XH)));
   D7 l -> Npos (of_uint_acc l (XI (XI XH)));
   D8 l -> Npos (of_uint_acc l (XO (XO (XO XH))));
   D9 l -> Npos (of_uint_acc l (XI (XO (XO XH))))}

of_hex_uint_acc :: Uint0 -> Positive -> Positive
of_hex_uint_acc d acc =
  case d of {
   Nil0 -> acc;
   D10 l -> of_hex_uint_acc l (mul (XO (XO (XO (XO XH)))) acc);
   D11 l -> of_hex_uint_acc l (add2 XH (mul (XO (XO (XO (XO XH)))) acc));
   D12 l -> of_hex_uint_acc l (add2 (XO XH) (mul (XO (XO (XO (XO XH)))) acc));
   D13 l -> of_hex_uint_acc l (add2 (XI XH) (mul (XO (XO (XO (XO XH)))) acc));
   D14 l ->
    of_hex_uint_acc l (add2 (XO (XO XH)) (mul (XO (XO (XO (XO XH)))) acc));
   D15 l ->
    of_hex_uint_acc l (add2 (XI (XO XH)) (mul (XO (XO (XO (XO XH)))) acc));
   D16 l ->
    of_hex_uint_acc l (add2 (XO (XI XH)) (mul (XO (XO (XO (XO XH)))) acc));
   D17 l ->
    of_hex_uint_acc l (add2 (XI (XI XH)) (mul (XO (XO (XO (XO XH)))) acc));
   D18 l ->
    of_hex_uint_acc l
      (add2 (XO (XO (XO XH))) (mul (XO (XO (XO (XO XH)))) acc));
   D19 l ->
    of_hex_uint_acc l
      (add2 (XI (XO (XO XH))) (mul (XO (XO (XO (XO XH)))) acc));
   Da l ->
    of_hex_uint_acc l
      (add2 (XO (XI (XO XH))) (mul (XO (XO (XO (XO XH)))) acc));
   Db l ->
    of_hex_uint_acc l
      (add2 (XI (XI (XO XH))) (mul (XO (XO (XO (XO XH)))) acc));
   Dc l ->
    of_hex_uint_acc l
      (add2 (XO (XO (XI XH))) (mul (XO (XO (XO (XO XH)))) acc));
   Dd l ->
    of_hex_uint_acc l
      (add2 (XI (XO (XI XH))) (mul (XO (XO (XO (XO XH)))) acc));
   De l ->
    of_hex_uint_acc l
      (add2 (XO (XI (XI XH))) (mul (XO (XO (XO (XO XH)))) acc));
   Df l ->
    of_hex_uint_acc l
      (add2 (XI (XI (XI XH))) (mul (XO (XO (XO (XO XH)))) acc))}

of_hex_uint :: Uint0 -> N
of_hex_uint d =
  case d of {
   Nil0 -> N0;
   D10 l -> of_hex_uint l;
   D11 l -> Npos (of_hex_uint_acc l XH);
   D12 l -> Npos (of_hex_uint_acc l (XO XH));
   D13 l -> Npos (of_hex_uint_acc l (XI XH));
   D14 l -> Npos (of_hex_uint_acc l (XO (XO XH)));
   D15 l -> Npos (of_hex_uint_acc l (XI (XO XH)));
   D16 l -> Npos (of_hex_uint_acc l (XO (XI XH)));
   D17 l -> Npos (of_hex_uint_acc l (XI (XI XH)));
   D18 l -> Npos (of_hex_uint_acc l (XO (XO (XO XH))));
   D19 l -> Npos (of_hex_uint_acc l (XI (XO (XO XH))));
   Da l -> Npos (of_hex_uint_acc l (XO (XI (XO XH))));
   Db l -> Npos (of_hex_uint_acc l (XI (XI (XO XH))));
   Dc l -> Npos (of_hex_uint_acc l (XO (XO (XI XH))));
   Dd l -> Npos (of_hex_uint_acc l (XI (XO (XI XH))));
   De l -> Npos (of_hex_uint_acc l (XO (XI (XI XH))));
   Df l -> Npos (of_hex_uint_acc l (XI (XI (XI XH))))}

of_num_uint :: Uint1 -> N
of_num_uint d =
  case d of {
   UIntDecimal d0 -> of_uint d0;
   UIntHexadecimal d0 -> of_hex_uint d0}

of_int :: Signed_int -> Prelude.Maybe Positive
of_int d =
  case d of {
   Pos d0 ->
    case of_uint d0 of {
     N0 -> Prelude.Nothing;
     Npos p -> Prelude.Just p};
   Neg _ -> Prelude.Nothing}

of_hex_int :: Signed_int0 -> Prelude.Maybe Positive
of_hex_int d =
  case d of {
   Pos0 d0 ->
    case of_hex_uint d0 of {
     N0 -> Prelude.Nothing;
     Npos p -> Prelude.Just p};
   Neg0 _ -> Prelude.Nothing}

of_num_int :: Signed_int1 -> Prelude.Maybe Positive
of_num_int d =
  case d of {
   IntDecimal d0 -> of_int d0;
   IntHexadecimal d0 -> of_hex_int d0}

to_little_uint :: Positive -> Uint
to_little_uint p =
  case p of {
   XI p0 -> succ_double (to_little_uint p0);
   XO p0 -> double (to_little_uint p0);
   XH -> D1 Nil}

to_uint :: Positive -> Uint
to_uint p =
  rev (to_little_uint p)

to_little_hex_uint :: Positive -> Uint0
to_little_hex_uint p =
  case p of {
   XI p0 -> succ_double0 (to_little_hex_uint p0);
   XO p0 -> double0 (to_little_hex_uint p0);
   XH -> D11 Nil0}

to_hex_uint :: Positive -> Uint0
to_hex_uint p =
  rev0 (to_little_hex_uint p)

to_num_uint :: Positive -> Uint1
to_num_uint p =
  UIntDecimal (to_uint p)

to_num_hex_uint :: Positive -> Uint1
to_num_hex_uint n =
  UIntHexadecimal (to_hex_uint n)

to_int :: Positive -> Signed_int
to_int n =
  Pos (to_uint n)

to_hex_int :: Positive -> Signed_int0
to_hex_int p =
  Pos0 (to_hex_uint p)

to_num_int :: Positive -> Signed_int1
to_num_int n =
  IntDecimal (to_int n)

to_num_hex_int :: Positive -> Signed_int1
to_num_hex_int n =
  IntHexadecimal (to_hex_int n)

eq_dec :: Positive -> Positive -> Prelude.Bool
eq_dec x y =
  positive_rec (\_ h x0 ->
    case x0 of {
     XI p -> sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (h p);
     _ -> Prelude.False}) (\_ h x0 ->
    case x0 of {
     XO p -> sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (h p);
     _ -> Prelude.False}) (\x0 ->
    case x0 of {
     XH -> Prelude.True;
     _ -> Prelude.False}) x y

peano_rect :: a1 -> (Positive -> a1 -> a1) -> Positive -> a1
peano_rect a f p =
  let {f2 = peano_rect (f XH a) (\p0 x -> f (succ0 (XO p0)) (f (XO p0) x))}
  in
  case p of {
   XI q -> f (XO q) (f2 q);
   XO q -> f2 q;
   XH -> a}

peano_rec :: a1 -> (Positive -> a1 -> a1) -> Positive -> a1
peano_rec =
  peano_rect

data PeanoView =
   PeanoOne
 | PeanoSucc Positive PeanoView

peanoView_rect :: a1 -> (Positive -> PeanoView -> a1 -> a1) -> Positive ->
                  PeanoView -> a1
peanoView_rect f f0 _ p0 =
  case p0 of {
   PeanoOne -> f;
   PeanoSucc p p1 -> f0 p p1 (peanoView_rect f f0 p p1)}

peanoView_rec :: a1 -> (Positive -> PeanoView -> a1 -> a1) -> Positive ->
                 PeanoView -> a1
peanoView_rec =
  peanoView_rect

peanoView_xO :: Positive -> PeanoView -> PeanoView
peanoView_xO _ q =
  case q of {
   PeanoOne -> PeanoSucc XH PeanoOne;
   PeanoSucc p0 q0 -> PeanoSucc (succ0 (XO p0)) (PeanoSucc (XO p0)
    (peanoView_xO p0 q0))}

peanoView_xI :: Positive -> PeanoView -> PeanoView
peanoView_xI _ q =
  case q of {
   PeanoOne -> PeanoSucc (succ0 XH) (PeanoSucc XH PeanoOne);
   PeanoSucc p0 q0 -> PeanoSucc (succ0 (XI p0)) (PeanoSucc (XI p0)
    (peanoView_xI p0 q0))}

peanoView :: Positive -> PeanoView
peanoView p =
  case p of {
   XI p0 -> peanoView_xI p0 (peanoView p0);
   XO p0 -> peanoView_xO p0 (peanoView p0);
   XH -> PeanoOne}

peanoView_iter :: a1 -> (Positive -> a1 -> a1) -> Positive -> PeanoView -> a1
peanoView_iter a f _ q =
  case q of {
   PeanoOne -> a;
   PeanoSucc p0 q0 -> f p0 (peanoView_iter a f p0 q0)}

eqb_spec :: Positive -> Positive -> Reflect
eqb_spec x y =
  iff_reflect (eqb0 x y)

switch_Eq :: Comparison -> Comparison -> Comparison
switch_Eq c c' =
  case c' of {
   Eq -> c;
   x -> x}

mask2cmp :: Mask -> Comparison
mask2cmp p =
  case p of {
   IsNul -> Eq;
   IsPos _ -> Gt;
   IsNeg -> Lt}

leb_spec0 :: Positive -> Positive -> Reflect
leb_spec0 x y =
  iff_reflect (leb0 x y)

ltb_spec0 :: Positive -> Positive -> Reflect
ltb_spec0 x y =
  iff_reflect (ltb0 x y)

max_case_strong :: Positive -> Positive -> (Positive -> Positive -> () -> a1
                   -> a1) -> (() -> a1) -> (() -> a1) -> a1
max_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat n (max0 n m) __ (hl __);
   _ -> compat m (max0 n m) __ (hr __)}

max_case :: Positive -> Positive -> (Positive -> Positive -> () -> a1 -> a1)
            -> a1 -> a1 -> a1
max_case n m x x0 x1 =
  max_case_strong n m x (\_ -> x0) (\_ -> x1)

max_dec :: Positive -> Positive -> Prelude.Bool
max_dec n m =
  max_case n m (\_ _ _ h0 -> h0) Prelude.True Prelude.False

min_case_strong :: Positive -> Positive -> (Positive -> Positive -> () -> a1
                   -> a1) -> (() -> a1) -> (() -> a1) -> a1
min_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat m (min0 n m) __ (hr __);
   _ -> compat n (min0 n m) __ (hl __)}

min_case :: Positive -> Positive -> (Positive -> Positive -> () -> a1 -> a1)
            -> a1 -> a1 -> a1
min_case n m x x0 x1 =
  min_case_strong n m x (\_ -> x0) (\_ -> x1)

min_dec :: Positive -> Positive -> Prelude.Bool
min_dec n m =
  min_case n m (\_ _ _ h0 -> h0) Prelude.True Prelude.False

max_case_strong0 :: Positive -> Positive -> (() -> a1) -> (() -> a1) -> a1
max_case_strong0 n m x x0 =
  max_case_strong n m (\_ _ _ x1 -> eq_rect __ x1 __) x x0

max_case0 :: Positive -> Positive -> a1 -> a1 -> a1
max_case0 n m x x0 =
  max_case_strong0 n m (\_ -> x) (\_ -> x0)

max_dec0 :: Positive -> Positive -> Prelude.Bool
max_dec0 =
  max_dec

min_case_strong0 :: Positive -> Positive -> (() -> a1) -> (() -> a1) -> a1
min_case_strong0 n m x x0 =
  min_case_strong n m (\_ _ _ x1 -> eq_rect __ x1 __) x x0

min_case0 :: Positive -> Positive -> a1 -> a1 -> a1
min_case0 n m x x0 =
  min_case_strong0 n m (\_ -> x) (\_ -> x0)

min_dec0 :: Positive -> Positive -> Prelude.Bool
min_dec0 =
  min_dec

type T0 = Z

_0 :: Z
_0 =
  Z0

_1 :: Z
_1 =
  Zpos XH

_2 :: Z
_2 =
  Zpos (XO XH)

add3 :: Z -> Z -> Z
add3 =
  add1

max3 :: Z -> Z -> Z
max3 =
  max1

ltb1 :: Z -> Z -> Prelude.Bool
ltb1 =
  ltb

leb1 :: Z -> Z -> Prelude.Bool
leb1 =
  leb

data Literal =
   Var Positive
 | Not Positive

data Clause =
   Bottom
 | Or Clause Literal

data CNF =
   Top
 | And CNF Clause

type Elt = Positive

data Tree =
   Leaf
 | Node T0 Tree Positive Tree

empty :: Tree
empty =
  Leaf

is_empty :: Tree -> Prelude.Bool
is_empty t =
  case t of {
   Leaf -> Prelude.True;
   Node _ _ _ _ -> Prelude.False}

mem :: Positive -> Tree -> Prelude.Bool
mem x t =
  case t of {
   Leaf -> Prelude.False;
   Node _ l k r ->
    case compare_cont0 Eq x k of {
     Eq -> Prelude.True;
     Lt -> mem x l;
     Gt -> mem x r}}

min_elt :: Tree -> Prelude.Maybe Elt
min_elt t =
  case t of {
   Leaf -> Prelude.Nothing;
   Node _ l x _ ->
    case l of {
     Leaf -> Prelude.Just x;
     Node _ _ _ _ -> min_elt l}}

max_elt :: Tree -> Prelude.Maybe Elt
max_elt t =
  case t of {
   Leaf -> Prelude.Nothing;
   Node _ _ x r ->
    case r of {
     Leaf -> Prelude.Just x;
     Node _ _ _ _ -> max_elt r}}

choose :: Tree -> Prelude.Maybe Elt
choose =
  min_elt

fold :: (Elt -> a1 -> a1) -> Tree -> a1 -> a1
fold f t base =
  case t of {
   Leaf -> base;
   Node _ l x r -> fold f r (f x (fold f l base))}

elements_aux :: (([]) Positive) -> Tree -> ([]) Positive
elements_aux acc s =
  case s of {
   Leaf -> acc;
   Node _ l x r -> elements_aux ((:) x (elements_aux acc r)) l}

elements :: Tree -> ([]) Positive
elements =
  elements_aux ([])

rev_elements_aux :: (([]) Positive) -> Tree -> ([]) Positive
rev_elements_aux acc s =
  case s of {
   Leaf -> acc;
   Node _ l x r -> rev_elements_aux ((:) x (rev_elements_aux acc l)) r}

rev_elements :: Tree -> ([]) Positive
rev_elements =
  rev_elements_aux ([])

cardinal :: Tree -> Nat
cardinal s =
  case s of {
   Leaf -> O;
   Node _ l _ r -> S (add (cardinal l) (cardinal r))}

maxdepth :: Tree -> Nat
maxdepth s =
  case s of {
   Leaf -> O;
   Node _ l _ r -> S (max (maxdepth l) (maxdepth r))}

mindepth :: Tree -> Nat
mindepth s =
  case s of {
   Leaf -> O;
   Node _ l _ r -> S (min (mindepth l) (mindepth r))}

for_all :: (Elt -> Prelude.Bool) -> Tree -> Prelude.Bool
for_all f s =
  case s of {
   Leaf -> Prelude.True;
   Node _ l x r ->
    case case f x of {
          Prelude.True -> for_all f l;
          Prelude.False -> Prelude.False} of {
     Prelude.True -> for_all f r;
     Prelude.False -> Prelude.False}}

exists_ :: (Elt -> Prelude.Bool) -> Tree -> Prelude.Bool
exists_ f s =
  case s of {
   Leaf -> Prelude.False;
   Node _ l x r ->
    case case f x of {
          Prelude.True -> Prelude.True;
          Prelude.False -> exists_ f l} of {
     Prelude.True -> Prelude.True;
     Prelude.False -> exists_ f r}}

data Enumeration =
   End
 | More Elt Tree Enumeration

cons :: Tree -> Enumeration -> Enumeration
cons s e =
  case s of {
   Leaf -> e;
   Node _ l x r -> cons l (More x r e)}

compare_more :: Positive -> (Enumeration -> Comparison) -> Enumeration ->
                Comparison
compare_more x1 cont e2 =
  case e2 of {
   End -> Gt;
   More x2 r2 e3 ->
    case compare_cont0 Eq x1 x2 of {
     Eq -> cont (cons r2 e3);
     x -> x}}

compare_cont1 :: Tree -> (Enumeration -> Comparison) -> Enumeration ->
                 Comparison
compare_cont1 s1 cont e2 =
  case s1 of {
   Leaf -> cont e2;
   Node _ l1 x1 r1 ->
    compare_cont1 l1 (compare_more x1 (compare_cont1 r1 cont)) e2}

compare_end :: Enumeration -> Comparison
compare_end e2 =
  case e2 of {
   End -> Eq;
   More _ _ _ -> Lt}

compare2 :: Tree -> Tree -> Comparison
compare2 s1 s2 =
  compare_cont1 s1 compare_end (cons s2 End)

equal :: Tree -> Tree -> Prelude.Bool
equal s1 s2 =
  case compare2 s1 s2 of {
   Eq -> Prelude.True;
   _ -> Prelude.False}

subsetl :: (Tree -> Prelude.Bool) -> Positive -> Tree -> Prelude.Bool
subsetl subset_l1 x1 s2 =
  case s2 of {
   Leaf -> Prelude.False;
   Node _ l2 x2 r2 ->
    case compare_cont0 Eq x1 x2 of {
     Eq -> subset_l1 l2;
     Lt -> subsetl subset_l1 x1 l2;
     Gt ->
      case mem x1 r2 of {
       Prelude.True -> subset_l1 s2;
       Prelude.False -> Prelude.False}}}

subsetr :: (Tree -> Prelude.Bool) -> Positive -> Tree -> Prelude.Bool
subsetr subset_r1 x1 s2 =
  case s2 of {
   Leaf -> Prelude.False;
   Node _ l2 x2 r2 ->
    case compare_cont0 Eq x1 x2 of {
     Eq -> subset_r1 r2;
     Lt ->
      case mem x1 l2 of {
       Prelude.True -> subset_r1 s2;
       Prelude.False -> Prelude.False};
     Gt -> subsetr subset_r1 x1 r2}}

subset :: Tree -> Tree -> Prelude.Bool
subset s1 s2 =
  case s1 of {
   Leaf -> Prelude.True;
   Node _ l1 x1 r1 ->
    case s2 of {
     Leaf -> Prelude.False;
     Node _ l2 x2 r2 ->
      case compare_cont0 Eq x1 x2 of {
       Eq ->
        case subset l1 l2 of {
         Prelude.True -> subset r1 r2;
         Prelude.False -> Prelude.False};
       Lt ->
        case subsetl (subset l1) x1 l2 of {
         Prelude.True -> subset r1 s2;
         Prelude.False -> Prelude.False};
       Gt ->
        case subsetr (subset r1) x1 r2 of {
         Prelude.True -> subset l1 s2;
         Prelude.False -> Prelude.False}}}}

type T1 = Tree

height :: T1 -> T0
height s =
  case s of {
   Leaf -> _0;
   Node h _ _ _ -> h}

singleton :: Positive -> Tree
singleton x =
  Node _1 Leaf x Leaf

create :: T1 -> Positive -> T1 -> Tree
create l x r =
  Node (add3 (max3 (height l) (height r)) _1) l x r

assert_false :: T1 -> Positive -> T1 -> Tree
assert_false =
  create

bal :: T1 -> Positive -> T1 -> Tree
bal l x r =
  let {hl = height l} in
  let {hr = height r} in
  case ltb1 (add3 hr _2) hl of {
   Prelude.True ->
    case l of {
     Leaf -> assert_false l x r;
     Node _ ll lx lr ->
      case leb1 (height lr) (height ll) of {
       Prelude.True -> create ll lx (create lr x r);
       Prelude.False ->
        case lr of {
         Leaf -> assert_false l x r;
         Node _ lrl lrx lrr -> create (create ll lx lrl) lrx (create lrr x r)}}};
   Prelude.False ->
    case ltb1 (add3 hl _2) hr of {
     Prelude.True ->
      case r of {
       Leaf -> assert_false l x r;
       Node _ rl rx rr ->
        case leb1 (height rl) (height rr) of {
         Prelude.True -> create (create l x rl) rx rr;
         Prelude.False ->
          case rl of {
           Leaf -> assert_false l x r;
           Node _ rll rlx rlr ->
            create (create l x rll) rlx (create rlr rx rr)}}};
     Prelude.False -> create l x r}}

add4 :: Positive -> Tree -> Tree
add4 x s =
  case s of {
   Leaf -> Node _1 Leaf x Leaf;
   Node h l y r ->
    case compare_cont0 Eq x y of {
     Eq -> Node h l y r;
     Lt -> bal (add4 x l) y r;
     Gt -> bal l y (add4 x r)}}

join :: Tree -> Elt -> T1 -> T1
join l =
  case l of {
   Leaf -> add4;
   Node lh ll lx lr -> (\x ->
    let {
     join_aux r =
       case r of {
        Leaf -> add4 x l;
        Node rh rl rx rr ->
         case ltb1 (add3 rh _2) lh of {
          Prelude.True -> bal ll lx (join lr x r);
          Prelude.False ->
           case ltb1 (add3 lh _2) rh of {
            Prelude.True -> bal (join_aux rl) rx rr;
            Prelude.False -> create l x r}}}}
    in join_aux)}

remove_min :: Tree -> Elt -> T1 -> (,) T1 Elt
remove_min l x r =
  case l of {
   Leaf -> (,) r x;
   Node _ ll lx lr ->
    case remove_min ll lx lr of {
     (,) l' m -> (,) (bal l' x r) m}}

merge :: Tree -> Tree -> Tree
merge s1 s2 =
  case s1 of {
   Leaf -> s2;
   Node _ _ _ _ ->
    case s2 of {
     Leaf -> s1;
     Node _ l2 x2 r2 ->
      case remove_min l2 x2 r2 of {
       (,) s2' m -> bal s1 m s2'}}}

remove :: Positive -> Tree -> Tree
remove x s =
  case s of {
   Leaf -> Leaf;
   Node _ l y r ->
    case compare_cont0 Eq x y of {
     Eq -> merge l r;
     Lt -> bal (remove x l) y r;
     Gt -> bal l y (remove x r)}}

concat :: Tree -> Tree -> Tree
concat s1 s2 =
  case s1 of {
   Leaf -> s2;
   Node _ _ _ _ ->
    case s2 of {
     Leaf -> s1;
     Node _ l2 x2 r2 ->
      case remove_min l2 x2 r2 of {
       (,) s2' m -> join s1 m s2'}}}

data Triple =
   Mktriple T1 Prelude.Bool T1

t_left :: Triple -> T1
t_left t =
  case t of {
   Mktriple t_left0 _ _ -> t_left0}

t_in :: Triple -> Prelude.Bool
t_in t =
  case t of {
   Mktriple _ t_in0 _ -> t_in0}

t_right :: Triple -> T1
t_right t =
  case t of {
   Mktriple _ _ t_right0 -> t_right0}

split :: Positive -> Tree -> Triple
split x s =
  case s of {
   Leaf -> Mktriple Leaf Prelude.False Leaf;
   Node _ l y r ->
    case compare_cont0 Eq x y of {
     Eq -> Mktriple l Prelude.True r;
     Lt ->
      case split x l of {
       Mktriple ll b rl -> Mktriple ll b (join rl y r)};
     Gt ->
      case split x r of {
       Mktriple rl b rr -> Mktriple (join l y rl) b rr}}}

inter :: Tree -> Tree -> Tree
inter s1 s2 =
  case s1 of {
   Leaf -> Leaf;
   Node _ l1 x1 r1 ->
    case s2 of {
     Leaf -> Leaf;
     Node _ _ _ _ ->
      case split x1 s2 of {
       Mktriple l2' pres r2' ->
        case pres of {
         Prelude.True -> join (inter l1 l2') x1 (inter r1 r2');
         Prelude.False -> concat (inter l1 l2') (inter r1 r2')}}}}

diff :: Tree -> Tree -> Tree
diff s1 s2 =
  case s1 of {
   Leaf -> Leaf;
   Node _ l1 x1 r1 ->
    case s2 of {
     Leaf -> s1;
     Node _ _ _ _ ->
      case split x1 s2 of {
       Mktriple l2' pres r2' ->
        case pres of {
         Prelude.True -> concat (diff l1 l2') (diff r1 r2');
         Prelude.False -> join (diff l1 l2') x1 (diff r1 r2')}}}}

union :: Tree -> Tree -> Tree
union s1 s2 =
  case s1 of {
   Leaf -> s2;
   Node _ l1 x1 r1 ->
    case s2 of {
     Leaf -> s1;
     Node _ _ _ _ ->
      case split x1 s2 of {
       Mktriple l2' _ r2' -> join (union l1 l2') x1 (union r1 r2')}}}

filter :: (Elt -> Prelude.Bool) -> Tree -> Tree
filter f s =
  case s of {
   Leaf -> Leaf;
   Node _ l x r ->
    let {l' = filter f l} in
    let {r' = filter f r} in
    case f x of {
     Prelude.True -> join l' x r';
     Prelude.False -> concat l' r'}}

partition :: (Elt -> Prelude.Bool) -> T1 -> (,) T1 T1
partition f s =
  case s of {
   Leaf -> (,) Leaf Leaf;
   Node _ l x r ->
    case partition f l of {
     (,) l1 l2 ->
      case partition f r of {
       (,) r1 r2 ->
        case f x of {
         Prelude.True -> (,) (join l1 x r1) (concat l2 r2);
         Prelude.False -> (,) (concat l1 r1) (join l2 x r2)}}}}

ltb_tree :: Positive -> Tree -> Prelude.Bool
ltb_tree x s =
  case s of {
   Leaf -> Prelude.True;
   Node _ l y r ->
    case compare_cont0 Eq x y of {
     Gt -> (Prelude.&&) (ltb_tree x l) (ltb_tree x r);
     _ -> Prelude.False}}

gtb_tree :: Positive -> Tree -> Prelude.Bool
gtb_tree x s =
  case s of {
   Leaf -> Prelude.True;
   Node _ l y r ->
    case compare_cont0 Eq x y of {
     Lt -> (Prelude.&&) (gtb_tree x l) (gtb_tree x r);
     _ -> Prelude.False}}

isok :: Tree -> Prelude.Bool
isok s =
  case s of {
   Leaf -> Prelude.True;
   Node _ l x r ->
    (Prelude.&&)
      ((Prelude.&&) ((Prelude.&&) (isok l) (isok r)) (ltb_tree x l))
      (gtb_tree x r)}

type T2 = Positive

compare3 :: Positive -> Positive -> Comparison
compare3 =
  compare_cont0 Eq

eq_dec0 :: Positive -> Positive -> Prelude.Bool
eq_dec0 =
  eq_dec

type T3 = Positive

compare4 :: Positive -> Positive -> Comparison
compare4 =
  compare_cont0 Eq

eq_dec1 :: Positive -> Positive -> Prelude.Bool
eq_dec1 =
  eq_dec0

eq_dec2 :: Positive -> Positive -> Prelude.Bool
eq_dec2 =
  eq_dec

lt_dec :: Positive -> Positive -> Prelude.Bool
lt_dec x y =
  let {c = compSpec2Type x y (compare_cont0 Eq x y)} in
  case c of {
   CompLtT -> Prelude.True;
   _ -> Prelude.False}

eqb1 :: Positive -> Positive -> Prelude.Bool
eqb1 x y =
  case eq_dec2 x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

data R_min_elt =
   R_min_elt_0 Tree
 | R_min_elt_1 Tree T0 Tree Positive Tree
 | R_min_elt_2 Tree T0 Tree Positive Tree T0 Tree Positive Tree (Prelude.Maybe
                                                                Elt) 
 R_min_elt

data R_max_elt =
   R_max_elt_0 Tree
 | R_max_elt_1 Tree T0 Tree Positive Tree
 | R_max_elt_2 Tree T0 Tree Positive Tree T0 Tree Positive Tree (Prelude.Maybe
                                                                Elt) 
 R_max_elt

type T4 = Positive

compare5 :: Positive -> Positive -> Comparison
compare5 =
  compare_cont0 Eq

eq_dec3 :: Positive -> Positive -> Prelude.Bool
eq_dec3 =
  eq_dec

type T5 = Positive

compare6 :: Positive -> Positive -> Comparison
compare6 =
  compare_cont0 Eq

eq_dec4 :: Positive -> Positive -> Prelude.Bool
eq_dec4 =
  eq_dec3

eq_dec5 :: Positive -> Positive -> Prelude.Bool
eq_dec5 =
  eq_dec

lt_dec0 :: Positive -> Positive -> Prelude.Bool
lt_dec0 x y =
  let {c = compSpec2Type x y (compare_cont0 Eq x y)} in
  case c of {
   CompLtT -> Prelude.True;
   _ -> Prelude.False}

eqb2 :: Positive -> Positive -> Prelude.Bool
eqb2 x y =
  case eq_dec5 x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

flatten_e :: Enumeration -> ([]) Elt
flatten_e e =
  case e of {
   End -> ([]);
   More x t r -> (:) x (app (elements t) (flatten_e r))}

data R_bal =
   R_bal_0 T1 Positive T1
 | R_bal_1 T1 Positive T1 T0 Tree Positive Tree
 | R_bal_2 T1 Positive T1 T0 Tree Positive Tree
 | R_bal_3 T1 Positive T1 T0 Tree Positive Tree T0 Tree Positive Tree
 | R_bal_4 T1 Positive T1
 | R_bal_5 T1 Positive T1 T0 Tree Positive Tree
 | R_bal_6 T1 Positive T1 T0 Tree Positive Tree
 | R_bal_7 T1 Positive T1 T0 Tree Positive Tree T0 Tree Positive Tree
 | R_bal_8 T1 Positive T1

data R_remove_min =
   R_remove_min_0 Tree Elt T1
 | R_remove_min_1 Tree Elt T1 T0 Tree Positive Tree ((,) T1 Elt) R_remove_min 
 T1 Elt

data R_merge =
   R_merge_0 Tree Tree
 | R_merge_1 Tree Tree T0 Tree Positive Tree
 | R_merge_2 Tree Tree T0 Tree Positive Tree T0 Tree Positive Tree T1 
 Elt

data R_concat =
   R_concat_0 Tree Tree
 | R_concat_1 Tree Tree T0 Tree Positive Tree
 | R_concat_2 Tree Tree T0 Tree Positive Tree T0 Tree Positive Tree T1 
 Elt

data R_inter =
   R_inter_0 Tree Tree
 | R_inter_1 Tree Tree T0 Tree Positive Tree
 | R_inter_2 Tree Tree T0 Tree Positive Tree T0 Tree Positive Tree T1 
 Prelude.Bool T1 Tree R_inter Tree R_inter
 | R_inter_3 Tree Tree T0 Tree Positive Tree T0 Tree Positive Tree T1 
 Prelude.Bool T1 Tree R_inter Tree R_inter

data R_diff =
   R_diff_0 Tree Tree
 | R_diff_1 Tree Tree T0 Tree Positive Tree
 | R_diff_2 Tree Tree T0 Tree Positive Tree T0 Tree Positive Tree T1 
 Prelude.Bool T1 Tree R_diff Tree R_diff
 | R_diff_3 Tree Tree T0 Tree Positive Tree T0 Tree Positive Tree T1 
 Prelude.Bool T1 Tree R_diff Tree R_diff

data R_union =
   R_union_0 Tree Tree
 | R_union_1 Tree Tree T0 Tree Positive Tree
 | R_union_2 Tree Tree T0 Tree Positive Tree T0 Tree Positive Tree T1 
 Prelude.Bool T1 Tree R_union Tree R_union

type T6 = Positive

compare7 :: Positive -> Positive -> Comparison
compare7 =
  compare_cont0 Eq

eq_dec6 :: Positive -> Positive -> Prelude.Bool
eq_dec6 =
  eq_dec

type Elt0 = Positive

type T_ = T1
  -- singleton inductive, whose constructor was Mkt
  
this :: T_ -> T1
this t =
  t

type T7 = T_

mem0 :: Elt0 -> T7 -> Prelude.Bool
mem0 x s =
  mem x (this s)

add5 :: Elt0 -> T7 -> T7
add5 x s =
  add4 x (this s)

remove0 :: Elt0 -> T7 -> T7
remove0 x s =
  remove x (this s)

singleton0 :: Elt0 -> T7
singleton0 =
  singleton

union0 :: T7 -> T7 -> T7
union0 s s' =
  union (this s) (this s')

inter0 :: T7 -> T7 -> T7
inter0 s s' =
  inter (this s) (this s')

diff0 :: T7 -> T7 -> T7
diff0 s s' =
  diff (this s) (this s')

equal0 :: T7 -> T7 -> Prelude.Bool
equal0 s s' =
  equal (this s) (this s')

subset0 :: T7 -> T7 -> Prelude.Bool
subset0 s s' =
  subset (this s) (this s')

empty0 :: T7
empty0 =
  empty

is_empty0 :: T7 -> Prelude.Bool
is_empty0 s =
  is_empty (this s)

elements0 :: T7 -> ([]) Elt0
elements0 s =
  elements (this s)

choose0 :: T7 -> Prelude.Maybe Elt0
choose0 s =
  choose (this s)

fold0 :: (Elt0 -> a1 -> a1) -> T7 -> a1 -> a1
fold0 f s =
  fold f (this s)

cardinal0 :: T7 -> Nat
cardinal0 s =
  cardinal (this s)

filter0 :: (Elt0 -> Prelude.Bool) -> T7 -> T7
filter0 f s =
  filter f (this s)

for_all0 :: (Elt0 -> Prelude.Bool) -> T7 -> Prelude.Bool
for_all0 f s =
  for_all f (this s)

exists_0 :: (Elt0 -> Prelude.Bool) -> T7 -> Prelude.Bool
exists_0 f s =
  exists_ f (this s)

partition0 :: (Elt0 -> Prelude.Bool) -> T7 -> (,) T7 T7
partition0 f s =
  let {p = partition f (this s)} in (,) (fst p) (snd p)

eq_dec7 :: T7 -> T7 -> Prelude.Bool
eq_dec7 s0 s'0 =
  let {b = equal s0 s'0} in
  case b of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

compare8 :: T7 -> T7 -> Comparison
compare8 s s' =
  compare2 (this s) (this s')

min_elt0 :: T7 -> Prelude.Maybe Elt0
min_elt0 s =
  min_elt (this s)

max_elt0 :: T7 -> Prelude.Maybe Elt0
max_elt0 s =
  max_elt (this s)

type Model = T7

litToVar :: Literal -> Positive
litToVar l =
  case l of {
   Var v -> v;
   Not v -> v}

varsClause :: Clause -> T7
varsClause c =
  case c of {
   Bottom -> empty0;
   Or c' l -> add5 (litToVar l) (varsClause c')}

varsCnf :: CNF -> T7
varsCnf cnf =
  case cnf of {
   Top -> empty0;
   And cnf' c -> union0 (varsClause c) (varsCnf cnf')}

anyVar :: CNF -> Prelude.Maybe Positive
anyVar cnf =
  choose0 (varsCnf cnf)

sameLiterals :: Literal -> Literal -> Prelude.Bool
sameLiterals l l' =
  case l of {
   Var v -> case l' of {
             Var v' -> eqb v v';
             Not _ -> Prelude.False};
   Not v -> case l' of {
             Var _ -> Prelude.False;
             Not v' -> eqb v v'}}

oppositeLiterals :: Literal -> Literal -> Prelude.Bool
oppositeLiterals l l' =
  case l of {
   Var v -> case l' of {
             Var _ -> Prelude.False;
             Not v' -> eqb v v'};
   Not v -> case l' of {
             Var v' -> eqb v v';
             Not _ -> Prelude.False}}

clauseContains :: Clause -> Literal -> Prelude.Bool
clauseContains c l =
  case c of {
   Bottom -> Prelude.False;
   Or c' any ->
    case sameLiterals any l of {
     Prelude.True -> Prelude.True;
     Prelude.False -> clauseContains c' l}}

containsBottom :: CNF -> Prelude.Bool
containsBottom cnf =
  case cnf of {
   Top -> Prelude.False;
   And cnf' c ->
    case c of {
     Bottom -> Prelude.True;
     Or _ _ -> containsBottom cnf'}}

propagateClause :: Clause -> Literal -> Clause
propagateClause c l =
  case c of {
   Bottom -> Bottom;
   Or c' l' ->
    case oppositeLiterals l l' of {
     Prelude.True -> propagateClause c' l;
     Prelude.False -> Or (propagateClause c' l) l'}}

removeSatisfied :: CNF -> Literal -> CNF
removeSatisfied cnf l =
  case cnf of {
   Top -> Top;
   And cnf' c ->
    case clauseContains c l of {
     Prelude.True -> removeSatisfied cnf' l;
     Prelude.False -> And (removeSatisfied cnf' l) c}}

propagateCnf :: CNF -> Literal -> CNF
propagateCnf cnf l =
  case cnf of {
   Top -> Top;
   And cnf' c -> And (propagateCnf cnf' l) (propagateClause c l)}

cleanCnf :: CNF -> Literal -> CNF
cleanCnf cnf l =
  propagateCnf (removeSatisfied cnf l) l

findPure :: CNF -> Prelude.Maybe Literal
findPure cnf =
  case cnf of {
   Top -> Prelude.Nothing;
   And cnf' c ->
    case c of {
     Bottom -> findPure cnf';
     Or c0 l ->
      case c0 of {
       Bottom -> Prelude.Just l;
       Or _ _ -> findPure cnf'}}}

expandModel :: Model -> Literal -> Model
expandModel m l =
  case l of {
   Var v -> add5 v m;
   Not v -> remove0 v m}

expandResult :: (Prelude.Maybe Model) -> Literal -> Prelude.Maybe Model
expandResult r l =
  case r of {
   Prelude.Just m -> Prelude.Just (expandModel m l);
   Prelude.Nothing -> Prelude.Nothing}

solverDecreasing :: CNF -> Nat -> Prelude.Maybe Model
solverDecreasing cnf steps =
  case containsBottom cnf of {
   Prelude.True -> Prelude.Nothing;
   Prelude.False ->
    case steps of {
     O -> Prelude.Just empty0;
     S vs ->
      case findPure cnf of {
       Prelude.Just l ->
        expandResult (solverDecreasing (cleanCnf cnf l) vs) l;
       Prelude.Nothing ->
        case anyVar cnf of {
         Prelude.Just v ->
          case solverDecreasing (cleanCnf cnf (Var v)) vs of {
           Prelude.Just m -> expandResult (Prelude.Just m) (Var v);
           Prelude.Nothing ->
            expandResult (solverDecreasing (cleanCnf cnf (Not v)) vs) (Not v)};
         Prelude.Nothing -> Prelude.Just empty0}}}}

vars :: CNF -> Nat
vars cnf =
  cardinal0 (varsCnf cnf)

solver :: CNF -> Prelude.Maybe Model
solver cnf =
  solverDecreasing cnf (vars cnf)

