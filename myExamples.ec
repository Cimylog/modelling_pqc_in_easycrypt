require import Bool AllCore Int Distr DBool.

type ringEl.
op (+) : ringEl -> ringEl -> ringEl.
op id : ringEl.
op [-] : ringEl -> ringEl.
abbrev (-) (x y : ringEl) = x + -y.

axiom ringAddR0 : forall (x : ringEl), x + id = x.
axiom ringAddLI : forall (x : ringEl), - x + x = id.
axiom ringAddC : forall (x y : ringEl), x + y = y + x.
axiom ringAddA : forall (x y z: ringEl), (x + y) + z = x + (y + z).

lemma ringAddE (x y z : ringEl) : x = y => x + z = y + z.
proof.
move => xy_eq.
rewrite xy_eq. trivial.
qed.

lemma ringAddK (x y : ringEl) : (x - y) + y = x
  by rewrite ringAddA ringAddLI ringAddR0.


module Sort = {
    var x, y : int

    proc swapping() : unit = {
        var z : int;
        z <- x;
        x <- y;
        y <- z;
    }

    proc main() : unit = {
        if (y < x) {
            swapping();
        }
    }
}.

lemma swapping_correct (x' y' : int) :
    hoare[Sort.swapping :
    Sort.x = x' /\ Sort.y = y' ==>
    Sort.x = y' /\ Sort.y = x'].
proof.
proc; wp; trivial.
qed.


op dbool : bool distr.

axiom dboolE (E : bool -> bool) :
 mu dbool E = (if E true  then 1%r/2%r else 0%r)
            + (if E false then 1%r/2%r else 0%r).
axiom dbool_ll : is_lossless dbool.
axiom dbool_uni : is_uniform dbool.

module Random_bit = {
    proc main() : bool = {
        var x : bool;
        x <$ {0,1};
        return x;
    }
}.

lemma random_bit_half &m :
    phoare[Random_bit.main : true ==> res] = (1%r / 2%r).
proof.
proc.
rnd; skip; progress.
rewrite dboolE //.
qed.

module Random_xor = {
    proc main() : bool = {
        var x, y : bool;
        x <$ {0,1};
        y <$ {0,1};
        return x ^^ y;       
    }
}.

lemma Random_bit_xor_eq &m :
    equiv[Random_bit.main ~ Random_xor.main : true ==> ={res}].
proof.
proc.
seq 0 1 : true. rnd{2}.     
auto; progress. rnd (fun z => x{2} ^^ z).  
skip; progress.
by rewrite -xorA xorK xorC xor_false.
by rewrite -xorA xorK xorC xor_false.
qed.
