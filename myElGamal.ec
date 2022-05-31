(********************************************************************************)
(***               Require and import necessary theories                      ***)
(********************************************************************************)

require import AllCore DBool DInterval Distr Int IntDiv.
require PKE PKE_CPA Group.

(********************************************************************************)
(***         Instantiation of the PKE library with types for ElGamal          ***)
(********************************************************************************)

clone import Group.CyclicGroup as Group_EG.

type skey = int.
type pkey = group.
type ptxt = group.
type ctxt = group * group.

clone import PKE as PKE_EG with
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- ptxt,
  type ciphertext <- ctxt.
 
(********************************************************************************)
(***                      ElGamal Encryption scheme                           ***)
(********************************************************************************)


module ElGamal: Scheme = {
  proc kg(): pkey * skey = {
    var sk;
    sk <$ [0..(order-1)];
    return (g^sk, sk);
  }

  proc enc(pk: pkey, m: ptxt): ctxt = {
    var y;
    y <$ [0..(order-1)];
    return (g^y, m * pk^y);
  }

  proc dec (sk: skey, c: ctxt): ptxt option = {
    var gy, my;
    (gy, my) <- c;
    return Some (my * gy^(-sk));
  }  
}.

lemma elgamal_correctness &m : forall (m: ptxt), Pr[Correctness(ElGamal).main(m) @ &m : res] = 1%r.
    proof.
    move => m.
byphoare => //; proc; inline *.
auto; progress.
apply dinter_ll. rewrite -ltzS /= order_gt0.
rewrite -expM -expM -mulcA -expD.
by rewrite mulrN mulzC subrr exp0 mulc1.
qed.


(********************************************************************************)
(***                    Decisional Diffie Hellman (DDH)                       ***)
(********************************************************************************)

module type A_DDH = {
  proc guess(gx gy gz:group): bool
}.

module DDH0 (A:A_DDH) = {
  proc main() : bool = {
    var b, x, y;
    x <$ [0..(order-1)];
    y <$ [0..(order-1)];
    b <@ A.guess(g ^ x, g ^ y, g ^ (x*y));
    return b;
  }
}.

module DDH1 (A:A_DDH) = {
  proc main() : bool = {
    var b, x, y, z;
    x <$ [0..(order-1)];
    y <$ [0..(order-1)];
    z <$ [0..(order-1)];
    b <@ A.guess(g ^ x, g ^ y, g ^ z);
    return b;
  }
}.

module Red_A_EG_DDH (A: Adversary): A_DDH = {
  proc guess(gx gy gz: group): bool = {
    var m0, m1, b, b';
    (m0, m1) <- A.choose(gx);
    b        <$ {0,1};
    b'       <@ A.guess(gy, gz * (b?m1:m0));
    return b' = b;
  }
}.
    
(********************************************************************************)
(***                         Games sequence + proofs                          ***)
(********************************************************************************)

module G1 (A: Adversary) = {
  proc main () : bool = {
    var x, m0, m1, b, y, z, b';
    x       <$ [0..(order-1)];
    (m0,m1) <@ A.choose(g^x);
    b       <$ {0,1};
    y       <$ [0..(order-1)];
    z       <$ [0..(order-1)];
    b'      <@ A.guess((g^y, g^z));
    return b' = b;
  }
}.

lemma g1_half &m (A <: Adversary) :
    islossless A.choose => islossless A.guess =>
    Pr[G1(A).main() @ &m : res] = 1%r/2%r.
proof.
move => Ac_ll Ag_ll.    
byphoare=> //; proc; inline *.
swap 3 3.
rnd  (pred1 b')=> //=.
conseq (: _ ==> true).
+ by move=> /> b; rewrite dbool1E pred1E.
by islossless; apply dinter_ll; rewrite -ltzS /= order_gt0.
qed.

lemma ddh0_g0_eq &m (A <: Adversary) :
    Pr[CPA(ElGamal, A).main() @ &m : res] =
    Pr[DDH0(Red_A_EG_DDH(A)).main() @ &m : res].
proof.
byequiv=> //; proc; inline *.
swap{1} 7 -5. 
auto; call (_: true).
auto; call (_: true).
auto => /> sk _ y _ r b _.
rewrite expM mulcC //.
qed.

lemma ddh1_g1_eq &m (A <: Adversary) :
    Pr[G1(A).main() @ &m : res] =
    Pr[DDH1(Red_A_EG_DDH(A)).main() @ &m : res].
proof.
byequiv=> //; proc; inline *.
swap{2} 6 2. swap{2} 3 4. swap{1} 4 -2.
auto; call (_: true); wp.
rnd(fun z, ((z - log (if b then m1 else m0){1}) %% order))
  (fun z, ((z + log (if b then m1 else m0){1}) %% order)).
auto; call (_: true).
auto. progress.
smt(modzDml subrK pmod_small supp_dinter).
smt(dinter1E).
smt(supp_dinter modz_ge0 ltz_pmod).
rewrite modzDml subrK.
rewrite supp_dinter in H6.
rewrite pmod_small //=. smt().
smt(expD expg_modz logVr expgK).
qed.

lemma conclusion &m (A <: Adversary) :
    islossless A.choose => islossless A.guess =>
  `| Pr[CPA(ElGamal, A).main() @ &m : res] - 1%r/2%r | =
  `| Pr[DDH0(Red_A_EG_DDH(A)).main() @ &m : res] -
       Pr[DDH1(Red_A_EG_DDH(A)).main() @ &m : res] |.
proof.
move => Ac_ll Ag_ll.
by rewrite (ddh0_g0_eq &m A) -(ddh1_g1_eq &m A) (g1_half &m A). 
qed.

