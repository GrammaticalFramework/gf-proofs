abstract Nat = {

cat N ;
data z : N ;
     s : N -> N ;

cat Eq N N ;
data refl : (n : N) -> Eq n n ;

fun symmetric_eq : ({x,y} : N) -> Eq x y -> Eq y x ;
def symmetric_eq (refl x) = refl x ;

fun transitive_eq : ({x,y,z} : N) -> Eq x y -> Eq y z -> Eq x z ;
def transitive_eq (refl x) (refl ~x) = refl x ;

fun lift_eq : ({x,y} : N) -> Eq x y -> Eq (s x) (s y) ;
def lift_eq (refl x) = refl (s x) ;

fun plus : N -> N -> N ;
def plus z     y = y ;
    plus (s x) y = s (plus x y) ;

fun minus : N -> N -> N ;
def minus z     y     = y ;
    minus (s x) (s y) = minus x y ;

fun mul : N -> N -> N ;
def mul z     y = y ;
    mul (s x) y = plus y (mul x y) ;

fun z_plus : (x : N) -> Eq x (plus z x) ;
def z_plus x = refl x ;

fun plus_z : (x : N) -> Eq x (plus x z) ;
def plus_z z     = refl z ;
    plus_z (s x) = lift_eq (plus_z x) ;

fun s_plus : (x,y : N) -> Eq (plus (s x) y) (plus x (s y)) ;
def s_plus z     y = refl (s y) ;
    s_plus (s x) y = lift_eq (s_plus x y) ;

fun commute : (x,y : N) -> Eq (plus x y) (plus y x) ; 
def commute z     y = plus_z y ;
    commute (s x) y = transitive_eq (lift_eq (commute x y)) (s_plus y x) ;

}
