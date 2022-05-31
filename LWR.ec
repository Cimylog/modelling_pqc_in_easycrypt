(********************************************************************************)
(***              Require and import necessary theories                       ***)
(********************************************************************************)
require import AllCore List Distr DBool DInterval FloorCeil IntDiv DMap Bool. 
require (*  *) Mat ZModP Subtype PKE.
import StdBigop.Bigreal.BRM.

(********************************************************************************)
(***                      Specification of LWR parameters                     ***)
(********************************************************************************)

const p : { int | 2 <= p } as ge2_p.
const q : { int | 2 <= q } as ge2_q.
const n, m: int.
const bet: int.

axiom pltq: p < q.
axiom p_div_q: p %| q.
axiom n_ge0: 0 <= n.
axiom m_ge0: 0 <= m.
axiom bet_rg: 0 <= bet < q.


(********************************************************************************)
(**         Instantiation of the rings and matrices over these rings           **)
(********************************************************************************)

(* The ring Z/pZ *)
clone import ZModP.ZModRing as ZP with
op p <- p.

(* Matrices over Z/pZ *)
clone import Self.Mat as MatZP with
  type ZR.t     <- ZP.zmod,
   op  ZR.zeror <- ZP.zero,
   op  ZR.oner  <- ZP.one,
   op  ZR.( + ) <- ZP.( + ),
   op  ZR.( * ) <- ZP.( * ),
   op  ZR.([-]) <- ZP.([-]),
   op  ZR.invr  <- ZP.inv,
  pred ZR.unit  <- ZP.unit
  rename [type] "vector" as "zpvector"
  rename [type] "matrix" as "zpmatrix"
proof ZR.addrA by exact/ZModule.addrA, 
      ZR.addrC by exact/ZModule.addrC, 
      ZR.add0r by exact/ZModule.add0r, 
      ZR.addNr by exact/ZModule.addNr,
      ZR.oner_neq0 by exact/ZModpRing.oner_neq0, 
      ZR.mulrA by exact/ZModpRing.mulrA, 
      ZR.mulrC by exact/ZModpRing.mulrC, 
      ZR.mul1r by exact/ZModpRing.mul1r, 
      ZR.mulrDl by exact/ZModpRing.mulrDl, 
      ZR.mulVr by exact/ZModpRing.mulVr, 
      ZR.unitP by exact/ZModpRing.unitP, 
      ZR.unitout by exact/ZModpRing.unitout.

(* Uniform distribution on Z/pZ *)
clone include DZmodP.  
op dzpu = DZmodP.dunifin.

(* Lemmas to check that the distribution over Z/pZ behaves as expected *)
lemma dzpu_ll  : is_lossless dzpu by rewrite /dzpu dunifin_ll.    
lemma dzpu_uni : is_uniform  dzpu by rewrite /dzpu dunifin_uni.
lemma dzpu_funi: is_funiform dzpu by rewrite /dzpu dunifin_funi.
lemma dzpu_fu  : is_full     dzpu by rewrite /dzpu dunifin_fu.
lemma mu1_dzpu (z:ZP.zmod) : mu1 dzpu z = 1%r/p%r by smt(@DZmodP).

(* The ring Z/qZ *)
clone import ZModP.ZModRing as ZQ with
  op p  <- q.

(* Matrices over Z/qZ *)
clone import Self.Mat as MatZQ with
  type ZR.t     <- ZQ.zmod,
   op  ZR.zeror <- ZQ.zero,
   op  ZR.oner  <- ZQ.one,
   op  ZR.( + ) <- ZQ.( + ),
   op  ZR.( * ) <- ZQ.( * ),
   op  ZR.([-]) <- ZQ.([-]),
   op  ZR.invr  <- ZQ.inv,
  pred ZR.unit  <- ZQ.unit
  rename [type] "vector" as "zqvector"
  rename [type] "matrix" as "zqmatrix"
proof ZR.addrA by exact/ZModule.addrA, 
      ZR.addrC by exact/ZModule.addrC, 
      ZR.add0r by exact/ZModule.add0r, 
      ZR.addNr by exact/ZModule.addNr,
      ZR.oner_neq0 by exact/ZModpRing.oner_neq0, 
      ZR.mulrA by exact/ZModpRing.mulrA, 
      ZR.mulrC by exact/ZModpRing.mulrC, 
      ZR.mul1r by exact/ZModpRing.mul1r, 
      ZR.mulrDl by exact ZModpRing.mulrDl, 
      ZR.mulVr by exact/ZModpRing.mulVr, 
      ZR.unitP by exact/ZModpRing.unitP, 
      ZR.unitout by exact/ZModpRing.unitout.

(* Uniform distribution on Z/qZ *)
clone import DZmodP as DZmodQ.  
op dzqu = DZmodP.dunifin.  

(* Lemmas to check that the distribution over Z/qZ behaves as expected *)
lemma dzqu_ll  : is_lossless dzqu by rewrite /dzqu dunifin_ll.    
lemma dzqu_uni : is_uniform  dzqu by rewrite /dzqu dunifin_uni.
lemma dzqu_funi: is_funiform dzqu by rewrite /dzqu dunifin_funi.
lemma dzqu_fu  : is_full     dzqu by rewrite /dzqu dunifin_fu.
lemma mu1_dzqu (z:ZQ.zmod) : mu1 dzqu z = 1%r/q%r by smt(@DZmodP).

(* The ring Z/2Z *)
clone import ZModP.ZModRing as Z2 with
  op p  <- 2.

(* Matrices over Z/2Z *)
clone import Self.Mat as MatZ2 with
  type ZR.t     <- Z2.zmod,
   op  ZR.zeror <- Z2.zero,
   op  ZR.oner  <- Z2.one,
   op  ZR.( + ) <- Z2.( + ),
   op  ZR.( * ) <- Z2.( * ),
   op  ZR.([-]) <- Z2.([-]),
   op  ZR.invr  <- Z2.inv,
  pred ZR.unit  <- Z2.unit
  rename [type] "vector" as "z2vector"
  rename [type] "matrix" as "z2matrix"
proof ZR.addrA by exact/ZModule.addrA, 
      ZR.addrC by exact/ZModule.addrC, 
      ZR.add0r by exact/ZModule.add0r, 
      ZR.addNr by exact/ZModule.addNr,
      ZR.oner_neq0 by exact/ZModpRing.oner_neq0, 
      ZR.mulrA by exact/ZModpRing.mulrA, 
      ZR.mulrC by exact/ZModpRing.mulrC, 
      ZR.mul1r by exact/ZModpRing.mul1r, 
      ZR.mulrDl by exact ZModpRing.mulrDl, 
      ZR.mulVr by exact/ZModpRing.mulVr, 
      ZR.unitP by exact/ZModpRing.unitP, 
      ZR.unitout by exact/ZModpRing.unitout.

(* Uniform distribution on Z/2Z *)
clone import DZmodP as DZmod2.  
op dz2u = DZmodP.dunifin.

(* Lemmas to check that the distribution over Z/2Z behaves as expected *)
lemma dz2u_ll  : is_lossless dz2u by rewrite /dz2u dunifin_ll.    
lemma dz2u_uni : is_uniform  dz2u by rewrite /dz2u dunifin_uni.
lemma dz2u_funi: is_funiform dz2u by rewrite /dz2u dunifin_funi.
lemma dz2u_fu  : is_full     dz2u by rewrite /dz2u dunifin_fu.
lemma mu1_dz2u (z:Z2.zmod) : mu1 dz2u z = 1%r/2%r by smt(@DZmodP).
    

(* Operator giving distance between two numbers modulo q and its properties*)
op distmodq (a b : ZQ.zmod) = 
    min (`|asint a - asint b|) (q - `|asint a - asint b|).

lemma mod_exists a p: exists m, a %% p = a - m * p by smt(divzE).

lemma abs_asint a: `|ZQ.asint a| = ZQ.asint a by smt(ZQ.rg_asint).

lemma asint_inzmod_half: asint (ZQ.inzmod (q %/ 2)) = q %/ 2.
proof.
rewrite inzmodK.
smt(ge2_q).
qed.

lemma add_asint a c: exists b, (b = 0 \/ b = 1) /\ ZQ.asint a + ZQ.asint c = ZQ.asint (a + c) + b * q.
proof.
elim (mod_exists (asint a + asint c) q) => b' H0.
exists b' => />.
split. smt(ZQ.rg_asint).
rewrite addE H0. algebra.
qed.

lemma sub_asint a c: exists b, (b = 0 \/ b = 1) /\ ZQ.asint a - ZQ.asint c = ZQ.asint (a - c) - b * q.
proof.
elim (add_asint (a - c) c) => m [H0 H1].
exists m => />.
print ZR.addrA.
rewrite -MatZQ.ZR.addrA (MatZQ.ZR.addrC _ c) MatZQ.ZR.subrr MatZQ.ZR.addr0 in H1.
smt().
qed.

lemma distmodq_zero a b: distmodq a b = distmodq (a - b) ZQ.zero.
proof.
rewrite /distmodq zeroE /=.
elim (sub_asint a b) => c [[-> | ->] /= H] //=.
by rewrite H.
have rel_asint: asint a - asint b < 0.
smt(ZQ.rg_asint).
rewrite StdOrder.IntOrder.ltr0_norm // H /= abs_asint /#.
qed.

lemma dist_asint_low a: distmodq a ZQ.zero < q %/ 4 => 
        distmodq a ZQ.zero < distmodq a (ZQ.inzmod (q %/ 2)). 
rewrite /distmodq zeroE /= abs_asint.
rewrite {1}/min.
case (asint a < q - asint a) => H1.
rewrite /min H1 /= asint_inzmod_half.
smt(ZQ.rg_asint).
rewrite /min H1 /= asint_inzmod_half.
smt(ZQ.rg_asint).
qed.

lemma asint_neg (a: ZQ.zmod): a <> ZQ.zero => asint (-a) = q - asint a.
proof. 
move => H.
rewrite oppE.
have: asint a <> 0.
by rewrite -asint_eq zeroE in H.
smt(ZQ.rg_asint ge2_q).
qed.

lemma dist_neg (a b: ZQ.zmod): distmodq (-a) (-b) = distmodq a b.
proof.
rewrite eq_sym distmodq_zero eq_sym distmodq_zero MatZQ.ZR.addrC.
rewrite MatZQ.ZR.opprK /distmodq zeroE /= 2!abs_asint.
case (a - b = ZQ.zero) => H.
have ->: b - a = ZQ.zero by smt(@MatZQ.ZR).
by rewrite H.
apply asint_neg in H.
smt(@MatZQ.ZR).
qed.

lemma inzmod0: ZQ.inzmod 0 = ZQ.zero by rewrite -ZQ.zeroE ZQ.asintK.

(********************************************************************************)
(***    Proving missing matrix and vector properties (also added in Mat.ec)   ***)
(********************************************************************************)

(* Scalar multiplication for matrices and lemmas about properties *)
op mulmxs (m: zqmatrix) (s: ZQ.zmod) = m * diagc (cols m) s.

lemma rows_mulmxs (m: zqmatrix) (s: ZQ.zmod): rows (mulmxs m s) = rows m.
proof.
rewrite /mulmxs.
rewrite rows_mulmx; last trivial.
rewrite rows_diagmx size_vectc.
by rewrite max0cols.
qed.

lemma cols_mulmxs (m: zqmatrix) (s: ZQ.zmod): cols (mulmxs m s) = cols m.
proof.
rewrite /mulmxs.
rewrite cols_mulmx. rewrite rows_diagmx size_vectc.
by rewrite max0cols.
  rewrite cols_diagmx size_vectc.
by rewrite max0cols.
qed.

lemma size_mulmxs (m: zqmatrix) (s: ZQ.zmod): size (mulmxs m s) = size m
  by rewrite rows_mulmxs cols_mulmxs //=.

lemma mulmxsE (m: zqmatrix) (s: ZQ.zmod) (i j: int): 0 <= i < rows m => 0 <= j < cols m =>
    (mulmxs m s).[i, j] = m.[i, j] * s.
    proof.
move => i_rg j_rg.
rewrite /mulmxs.
rewrite /( * ) rows_diagmx size_vectc max0cols /=. 
rewrite offunmE /=. 
rewrite i_rg j_rg //=.
rewrite /dotp.
rewrite 2!size_offunv.
rewrite rows_diagmx size_vectc 2!max0cols /=.
rewrite (MatZQ.Big.BAdd.bigD1 _ _ j).
rewrite mem_range /#.
rewrite range_uniq.
rewrite MatZQ.Big.BAdd.big1 /=.
move => k. rewrite /predC1 => ineq /=.
rewrite ineq /= MatZQ.ZR.mulr0 //.
rewrite vectcE; first smt().
rewrite MatZQ.ZR.addr0.
rewrite inzmodM //=. do rewrite asintK.
trivial.
qed.

(* Scalar multiplication for vectors and lemmas about properties *)
op mulvs (z: zqvector) (s: ZQ.zmod) = col (mulmxs (colmx z) s) 0.

lemma size_mulvs (z: zqvector) (s: ZQ.zmod): size (mulvs z s) = size z.
proof.
rewrite /mulvs.
rewrite size_col rows_mulmxs; done.
qed.

lemma mulvsE (z: zqvector) (s: ZQ.zmod) (i: int): 0 <= i < size z => (mulvs z s).[i] = z.[i] * s.
proof.
move => i_rg.
rewrite /mulvs.
rewrite colE.
rewrite mulmxsE; first rewrite rows_colmx i_rg.
rewrite cols_colmx //=.
rewrite colmxE //=.
qed.

lemma dotp_mulvs (z1 z2: zqvector) (s: ZQ.zmod): size z1 = size z2 =>
    (dotp z1 z2) * s = dotp z1 (mulvs z2 s).
proof.
move => size_eq.
rewrite /mulvs.
rewrite /mulmxs.
rewrite /dotp.
do rewrite size_col. rewrite rows_mulmx. rewrite rows_diagmx cols_colmx size_vectc /#.
rewrite rows_colmx /=.
rewrite size_eq /=. 
rewrite MatZQ.Big.BAdd.mulr_suml.
rewrite (MatZQ.Big.BAdd.eq_big_int 0 (size z2) (fun (i : int) => (fun (i0 : int) => z1.[i0] * z2.[i0]) i * s)
  (fun (i : int) => z1.[i] * (colmx z2 * diagc 1 s).[i, 0])).
move => i i_rg.
simplify.
rewrite mulmxE.
rewrite /dotp.
rewrite size_row size_col cols_colmx rows_diagmx size_vectc.
have ->: max 0 1 = 1 by smt().
rewrite MatZQ.Big.BAdd.big_int1 /=.
rewrite vectcE; first smt().
rewrite MatZQ.ZR.mulrA //. 
trivial.
qed.

(* Exxtended module-like properties of vectors *)
lemma oppvD (v1 v2: zqvector): size v1 = size v2 => -(v1 + v2) = -v1 + -v2.
proof.
move => eq_size.
rewrite eq_vectorP. split.
rewrite sizeN size_addv.
rewrite eq_size /=.
rewrite eq_size //=.
move => i bound.
rewrite getvN getvD.
rewrite eq_size //=.
rewrite getvD.
rewrite 2!sizeN eq_size //=.
rewrite MatZQ.ZR.opprD.
by rewrite 2!getvN.
qed.

lemma oppvK (v: zqvector): - (- v) = v.
proof.
rewrite eq_vectorP. split.
rewrite 2!sizeN //=.
move => i bound.
rewrite 2!getvN.
by rewrite MatZQ.ZR.opprK.
qed.

(* relation between concatenation and subm of matrices *)
lemma concat_down_subm_rowmx (m: zqmatrix): 0 < rows m =>
    m = subm m 0 (rows m -1) 0 (cols m) / rowmx (row m (rows m -1)).
proof.
move => bound.
  rewrite eq_matrixP; split.
rewrite size_concat_down.
rewrite cols_subm cols_rowmx.
rewrite size_row /#.
rewrite rows_subm cols_subm rows_rowmx /=.
have ->: max 0 (rows m - 1) = (rows m - 1) by smt().
by simplify.
move => i j mrange.
rewrite concat_downE.
rewrite cols_subm cols_rowmx.
smt().
rewrite rows_subm /=.
have ->: max 0 (rows m - 1) = (rows m - 1) by smt().
case (0 <= i < rows m - 1) => bound_i.
rewrite submE. 
smt().
smt().
have ->: (rowmx (row m (rows m - 1))).[i - (rows m - 1), j] = ZQ.zero.
rewrite getm0E.
smt(). done.
simplify.
by rewrite MatZQ.ZR.addr0.
have ->: i = rows m - 1 by smt().
have ->: (subm m 0 (rows m - 1) 0 (cols m)).[rows m - 1, j] = ZQ.zero.
rewrite getm0E.
smt(). done.
simplify.
by rewrite MatZQ.ZR.add0r.
qed.


(********************************************************************************)
(***    Defining rounding and lifting functions and lemmas about relations    ***)
(********************************************************************************)

(* Defining all operators *)
op ZP2ZQ (z : ZP.zmod) = ZQ.inzmod (ZP.asint z).
op Z22ZP (z: Z2.zmod) = ZP.inzmod (Z2.asint z).
op Z22ZQ (z: Z2.zmod) = ZQ.inzmod (Z2.asint z).
op ZPv2ZQ (z: zpvector) = MatZQ.Vectors.offunv (fun (i: int) => ZP2ZQ z.[i], size z).
op Z2v2ZP (z: z2vector) = MatZP.Vectors.offunv (fun (i: int) => Z22ZP z.[i], size z).
op Z2v2ZQ (z: z2vector) = MatZQ.Vectors.offunv (fun (i: int) => Z22ZQ z.[i], size z).

op rnd2ZP (z: ZQ.zmod) = ZP.inzmod (floor ((p%r/q%r) * (ZQ.asint z)%r)).
op rndv2ZP (z: zqvector) = MatZP.Vectors.offunv (fun (i: int) => rnd2ZP z.[i], size z).
op lift2ZQ (z: ZP.zmod) = ZQ.inzmod (ZP.asint z) * ZQ.inzmod (q %/ p).
op liftv2ZQ (z: zpvector) = MatZQ.Vectors.offunv (fun (i: int) => lift2ZQ z.[i], size z).

(* Size lemmas for modulus conversion *)
lemma size_Z2v2ZQ (z: z2vector) : size (Z2v2ZQ z) = size z by rewrite size_offunv /#.

lemma size_Z2v2ZP (z: z2vector) : size (Z2v2ZP z) = size z by rewrite size_offunv /#.
    
lemma size_ZPv2ZQ (z: zpvector) : size (ZPv2ZQ z) = size z by rewrite size_offunv /#.

(* Properties of the rounding operator *)
lemma size_rndv (z: zqvector) : size (rndv2ZP z) = size z by rewrite /rndv2ZP size_offunv /#.

lemma rndvE (z: zqvector) (i: int) : 0 <= i < size z => (rndv2ZP z).[i] = rnd2ZP z.[i].
proof.
move => bound.
rewrite /rndv2ZP offunvE.
apply bound. smt().
qed.

lemma rndv_offunv (z: zqvector) :
    rndv2ZP (offunv ((fun i => z.[i]), size z)) = (offunv ((fun i => rnd2ZP z.[i]), size z)).
proof.
rewrite /rndv2ZP. congr.
have ->: (offunv (fun (i0: int) => z.[i0], size z)) = (offunv (tofunv z)) by smt().
rewrite tofunvK.
trivial.
qed.

lemma rndv_subv (z: zqvector) (i, j: int): 0 <= i < size z => 0 <= j < size z => i <= j =>
    rndv2ZP (subv z i j) = subv (rndv2ZP z) i j.
proof. 
move => i_rg j_rg i_lt_j.
rewrite eq_vectorP. split; first rewrite size_subv size_rndv /#. 
rewrite size_rndv size_subv.
move => i0 i0_rg.
  rewrite subvE; first smt().
rewrite rndvE; first rewrite size_subv /#.
rewrite rndvE; first smt().
rewrite subvE //; first smt().
qed.

lemma rndv_concat (z1, z2: zqvector): rndv2ZP (z1 || z2) = ((rndv2ZP z1) || (rndv2ZP z2)).
proof.
rewrite eq_vectorP. split.
rewrite size_rndv 2!size_concat 2!size_rndv //.
rewrite size_rndv.
move => i i_rg.
rewrite concatE rndvE. apply i_rg.
rewrite concatE.
rewrite size_rndv.
rewrite size_concat in i_rg.
case: (i < size z1).
move => i_lt_sizez1.
have ->: z2.[i - size z1] = ZQ.zero by smt(MatZQ.Vectors.getv0E).
rewrite rndvE; first smt().
have ->: (rndv2ZP z2).[i - size z1] = ZP.zero by smt(MatZP.Vectors.getv0E).
rewrite MatZQ.ZR.addr0 MatZP.ZR.addr0 //.
rewrite -lezNgt.
move => i_ge_sizez1.
have ->: z1.[i] = ZQ.zero by smt(MatZQ.Vectors.getv0E).
have ->: (rndv2ZP z1).[i] = ZP.zero.
rewrite MatZP.Vectors.getv0E //. rewrite size_rndv /#.
rewrite MatZQ.ZR.add0r MatZP.ZR.add0r //.
rewrite rndvE //; first smt().
qed.

(* Properties of the lifting operator *)
lemma size_liftv (z: zpvector) : size (liftv2ZQ z) = size z by rewrite size_offunv /#.

lemma liftvE (z: zpvector) (i: int) : 0 <= i < size z => (liftv2ZQ z).[i] = lift2ZQ z.[i].
proof.
move => bound.
rewrite /liftv2ZQ offunvE.
apply bound. smt().
qed.

(* Decomposition of elements in Zq and its properties *)
op multiple (z: ZQ.zmod) = ((ZQ.asint z) %/ (q %/ p)).

op remainder (z: ZQ.zmod) = ((ZQ.asint z) %% (q %/ p)).

lemma zmod_form (z: ZQ.zmod) : z = ZQ.inzmod ((multiple z) * (q %/ p) + (remainder z))
    /\ ((q %/ p) <> 0 => 0 <= (remainder z) < `|(q %/ p)|).
proof.
rewrite /multiple /remainder.
case: (edivzP_r (ZQ.asint z) (q %/ p)). 
move => H0 H1.
rewrite -H0.
rewrite ZQ.asintK /=.
by apply H1.
qed.

lemma reciprocal_floor (z: ZQ.zmod) : floor (asint z %/ (q %/ p))%r = floor (p%r * (asint z)%r / q%r).
proof.
have: (q %/ p)%r = (q%r / p%r). rewrite fromint_div //=. smt(p_div_q).
move => H0.
admit.
qed.

lemma multiple_range (z: ZQ.zmod) : 0 <= (multiple z) < p.
proof.
rewrite /multiple. split.
smt.
move => lower_bound.
have: asint z < q by rewrite ZQ.gtp_asint.
move => H0.
have ->: asint z %/ (q %/ p) = floor (asint z %/ (q %/ p))%r. by rewrite from_int_floor.
rewrite reciprocal_floor.
have : (floor (p%r * (asint z)%r / q%r))%r <= (p%r * (asint z)%r / q%r). by apply floor_le.
move => H1.
smt.
qed.    

(* Lemmas about the form of the result after rounding or/and lifting an element or vector *)
lemma rnd_form (z: ZQ.zmod) : rnd2ZP z = ZP.inzmod (multiple z).
proof.
rewrite /rnd2ZP /multiple. print floorE.
rewrite (floorE (asint z %/ (q %/ p)) (p%r / q%r * (ZQ.asint z)%r)) //=.
split.
admit. admit.
qed.

lemma lift_rnd_form (z: ZQ.zmod) : lift2ZQ (rnd2ZP z) = ZQ.inzmod ((multiple z) * (q %/ p)).
proof.
rewrite rnd_form /lift2ZQ.
search inzmod.
rewrite -inzmodM.
rewrite inzmodK.
have ->: (multiple z %% p) = (multiple z).
rewrite modz_small //=.
smt(multiple_range).
done.
qed.

lemma rndv_form (z: zqvector) : rndv2ZP z = MatZP.Vectors.offunv (fun (i: int) =>
    ZP.inzmod (multiple z.[i]), size z).
proof.
rewrite eq_vectorP; split.
rewrite size_rndv size_offunv.
by rewrite max0size.
rewrite size_rndv.
move => i bound.
rewrite rndvE.
apply bound.
rewrite rnd_form.
rewrite offunvE //=.
qed.

lemma liftv_rndv_form (z: zqvector) : liftv2ZQ (rndv2ZP z) = MatZQ.Vectors.offunv (fun (i: int) =>
    ZQ.inzmod ((multiple z.[i]) * (q %/ p)), size z).
proof.
rewrite eq_vectorP; split.
rewrite size_liftv size_rndv size_offunv.
  by rewrite max0size.
rewrite size_liftv.
move => i bound.
rewrite liftvE.
apply bound.
rewrite size_rndv in bound.
rewrite rndvE.
apply bound.
rewrite lift_rnd_form.
rewrite offunvE //=.
qed.

(* Defining the error of rounding and lifting an element or vector and their bound *)
op rnd_err (z: ZQ.zmod) = z - (lift2ZQ (rnd2ZP z)).

lemma rnd_err_bound (z: ZQ.zmod) : 0 <= ZQ.asint (rnd_err z) < `|q %/ p|.
proof.
split.
rewrite /rnd_err addE.
rewrite modz_ge0. smt(ge2_q).
move => lower_bound.
rewrite /rnd_err.
rewrite lift_rnd_form. rewrite {1}zmod_form.
rewrite -inzmodB.
have ->: (multiple z * (q %/ p) + remainder z - multiple z * (q %/ p)) = remainder z by smt().
rewrite inzmodK.
smt.
qed.

op rndv_err (z: zqvector) = z - (liftv2ZQ (rndv2ZP z)).

lemma size_rndv_err (z: zqvector): size (rndv_err z) = size z.
proof.
rewrite /rndv_err size_addv.
rewrite sizeN size_liftv size_rndv.
by simplify.
qed.

lemma rndv_errE (z: zqvector) (i: int): 0 <= i < size z => (rndv_err z).[i] = rnd_err z.[i].
proof.
move => bound.
rewrite /rndv_err.
rewrite getvD.
by rewrite sizeN size_liftv size_rndv.
rewrite getvN liftvE. 
rewrite size_rndv.
apply bound.
rewrite rndvE.
apply bound. smt().
qed.

lemma rndv_err_bound (z: zqvector) : forall i, 0 <= i < size z => 0 <= ZQ.asint (rndv_err z).[i] < `|q %/ p|.
proof.
move => i bound.
rewrite rndv_errE.
apply bound.
rewrite rnd_err_bound.
qed.

(* Introducing operators for the error of lifting or rounding the message term *)
op floor_half_lift_err = if 2 %| p then (if 2 %| q then 0%r else (1%r/2%r))
  else (if 2 %| q then (-q%r/(2*p)%r) else ((p-q)%r/(2*p)%r)).

op floor_half_rnd_err = if 2 %| p then (if 2 %| q then 0%r else (-p%r/(2*q)%r))
  else (if 2 %| q then (1%r/2%r) else ((q-p)%r/(2*q)%r)).

axiom floor_half_lift_errE : (p %/ 2)%r * (q %/ p)%r = (q %/ 2)%r + floor_half_lift_err.

axiom floor_half_rnd_errE : (q %/ 2)%r * (p %/ q)%r = (p %/ 2)%r + floor_half_rnd_err.

lemma floor_half_lift_err_bound : 0%r <= `|floor_half_lift_err| < 1%r.
proof.
rewrite /floor_half_lift_err.
case (2 %| p) => H0.
case (2 %| q) => H1.
smt. smt.
case (2 %| q) => H1.
 have contrad : (p %| q) by rewrite p_div_q.
smt. smt.
qed.

lemma floor_half_rnd_err_bound : 0%r <= `|floor_half_rnd_err| < 1%r.
proof.
rewrite /floor_half_rnd_err.
  case (2 %| p) => H0.
case (2 %| q) => H1.
smt. smt.
case (2 %| q) => H1.
smt. smt.
qed.

(* Specific lemmas about dotp, lifting and rounding for security proof *)
lemma v'_eq (z1: z2vector) (z2: zqvector) : size z1 = size z2 =>
    rnd2ZP (dotp (Z2v2ZQ z1) (liftv2ZQ (rndv2ZP z2))) = dotp (Z2v2ZP z1) (rndv2ZP z2).
proof.
move => eq_size.
rewrite liftv_rndv_form rndv_form.
rewrite /dotp.
rewrite size_Z2v2ZQ size_offunv max0size eq_size.
rewrite size_Z2v2ZP size_offunv max0size eq_size.
simplify.
rewrite rnd_form.
rewrite /multiple.
admit.
qed.

lemma v_mterm_eq (z1: z2vector) (z2: zqvector) : size z1 = size z2 =>
    rnd2ZP (dotp (Z2v2ZQ z1) (liftv2ZQ (rndv2ZP z2)) + (ZQ.inzmod (q %/ 2)))
    = dotp (Z2v2ZP z1) (rndv2ZP z2) + (ZP.inzmod (p %/ 2)).
proof.
move => eq_size.
rewrite liftv_rndv_form rndv_form.
rewrite /dotp.
rewrite size_Z2v2ZQ size_offunv max0size eq_size.
rewrite size_Z2v2ZP size_offunv max0size eq_size.
simplify.
rewrite /rnd2ZP.
admit.
qed.

(* Specific lemmas about dotp, lifting and rounding for correctness proof *)
lemma rndv_liftv_dotp (z1: z2vector) (z2: zqvector) : size z1 = size z2 =>
    lift2ZQ (rnd2ZP (dotp (Z2v2ZQ z1) (liftv2ZQ (rndv2ZP z2)))) = dotp (Z2v2ZQ z1) (liftv2ZQ (rndv2ZP z2)).
proof.
move => eq_size.
rewrite v'_eq. apply eq_size.
rewrite /dotp.
rewrite size_Z2v2ZQ size_offunv max0size eq_size.
rewrite size_Z2v2ZP size_offunv max0size eq_size.
simplify.
rewrite /lift2ZQ.
rewrite -inzmodM.
admit.
qed.

lemma rndv_liftv_dotp_mterm (z1: z2vector) (z2: zqvector) : size z1 = size z2 =>
    lift2ZQ (rnd2ZP ((dotp (Z2v2ZQ z1) (liftv2ZQ (rndv2ZP z2))) + (ZQ.inzmod (q %/ 2)))) =
    dotp (Z2v2ZQ z1) (liftv2ZQ (rndv2ZP z2)) + (ZQ.inzmod (q %/ 2)).
proof.
move => eq_size.
rewrite {1}liftv_rndv_form.
rewrite {1}/MatZQ.Vectors.dotp.
rewrite size_Z2v2ZQ size_offunv max0size eq_size.
simplify.
rewrite lift_rnd_form.
admit.
qed.


(********************************************************************************)
(***      Instantiation of the PKE library with correct types for LWR         ***)
(********************************************************************************)

type pkey  = zqmatrix * zpvector. 
type skey  = z2vector. 
type ptext = bool. 
type ctext = zpvector * ZP.zmod.

clone import PKE as PKElwr with
  type pkey       <- pkey,
  type skey       <- skey,
  type plaintext  <- ptext,
  type ciphertext <- ctext.
  

(********************************************************************************)
(***                           LWR encryption system                          ***)
(********************************************************************************)


module LWRpke = {
  proc kg() = {
    var pk, sk, s, mA, t', t;
    mA      <$ dmatrix dzqu m n;
    s       <$ dvector dz2u n;     
    t'      <- mA *^ (Z2v2ZQ s);
    t       <- rndv2ZP (t');
    pk      <- (mA, t);
    sk      <- s;
    return (pk, sk);
  }
  
  proc enc(pk:pkey, pt:ptext) = {
    var r, mA, t, u', u, v', v;
    (mA, t) <- pk;
    r       <$ dvector dz2u m;
    u'      <- (Z2v2ZQ r) ^* mA;
    u       <- rndv2ZP (u');
    v'      <- dotp (Z2v2ZQ r) (liftv2ZQ t);
    v       <- rnd2ZP (v' + ZQ.inzmod ((b2i pt) * (q %/ 2)));
    return (u,v);
  }
  
  proc dec(sk:skey, c:ctext) = {
    var u, v, d, pt;
    (u, v)  <- c;
    d       <- lift2ZQ v - (dotp (liftv2ZQ u) (Z2v2ZQ sk));
    
    if (distmodq d ZQ.zero < distmodq d (ZQ.inzmod (q %/ 2))) {
      pt <- false;
    } else {
      pt <- true;
    }
    
    return Some pt;
  }
}.


(********************************************************************************)
(***                Descisional Learning With Rounding (DLWR)                 ***)
(********************************************************************************)

section Hardness_Assumption.

module type A_DLWR = {
  proc guess(_ : zqmatrix * zpvector): bool
}. 

module DLWR0(A: A_DLWR) = {
  proc main(): bool = {
    var mA, s, b;
    mA  <$ dmatrix dzqu m n;
    s   <$ dvector dz2u n;
    b   <- A.guess(mA, rndv2ZP (mA *^ (Z2v2ZQ s)));
    return b;
   }
}. 

module DLWR1(A: A_DLWR) = {
  proc main(): bool = {
    var mA, u, b;
    mA  <$ dmatrix dzqu m n;
    u   <$ dvector dzqu m;
    b   <- A.guess(mA, rndv2ZP (u));
    return b;
  }
}.

    
(********************************************************************************)
(***                  Needed reductions between adversaries                   ***)
(********************************************************************************)

module Red_A_DLWR (A: Adversary): A_DLWR = {
  proc guess(mA, t): bool = {
    var m0, m1, b, r, u', u, v', v, b';
    (m0, m1) <@ A.choose((mA, t));
    b        <$ {0,1};
    r        <$ dvector dz2u m;
    u'      <- (Z2v2ZQ r) ^* mA;
    u       <- rndv2ZP (u');
    v'      <- dotp (Z2v2ZQ r) (liftv2ZQ t);
    v        <- rnd2ZP (v' + ZQ.inzmod ((b2i (b?m1:m0)) * (q %/ 2)));
    b'       <@ A.guess((u, v));
    return b' = b;
  }
}.

lemma red_guess_ll (A <: Adversary): islossless A.choose => islossless A.guess =>
    islossless Red_A_DLWR(A).guess.
proof.
progress; proc.
call (:true); auto; call(:true). 
skip => />; progress.
apply dbool_ll.
apply/dvector_ll/dz2u_ll.
qed.


(********************************************************************************)
(***                 Correctness Proof for the LWR PKE scheme                 ***)
(********************************************************************************)

section Correctness_Proof.

module LWRpke' = {
  var er: ZQ.zmod
  var r, s: z2vector
  var e1, e2: zqvector
  
  proc kg() = {
    var pk, sk, mA, t', t;
    mA      <$ dmatrix dzqu m n;
    s       <$ dvector dz2u n;
    t'      <- mA *^ (Z2v2ZQ s);
    t       <- rndv2ZP (t');
    e1      <- rndv_err(mA *^ (Z2v2ZQ s));
    pk      <- (mA, t);
    sk      <- s;
    return (pk, sk);
  }

  proc enc(pk:pkey, pt:ptext) = {
    var mA, t, u', u, v', v;
    (mA, t) <- pk;
    r       <$ dvector dz2u m;
    u'      <- (Z2v2ZQ r) ^* mA;
    u       <- rndv2ZP (u');
    e2      <- rndv_err ((Z2v2ZQ r) ^* mA);
    v'      <- dotp (Z2v2ZQ r) (liftv2ZQ t);
    v       <- rnd2ZP (v' + ZQ.inzmod ((b2i pt) * (q %/ 2)));
    return (u,v);
  }
  
  proc dec(sk:skey, c:ctext) = {
    var u, v, d, pt;
    (u, v)  <- c;
    er      <- (- dotp (Z2v2ZQ r) e1) + dotp e2 (Z2v2ZQ s);
    d       <- lift2ZQ v - (dotp (liftv2ZQ u) (Z2v2ZQ sk));
    
    if (distmodq d ZQ.zero < distmodq d (ZQ.inzmod (q %/ 2))) {
      pt <- false;
    } else {
      pt <- true;
    }
    
    return Some pt;
  }
}.

(********************************************************************************)
(*** Show that if the total error in LWRpke' is less than q/4, the decryption ***)
(*** algorithm is always correct.                                             ***)
(********************************************************************************)

lemma LWRpke_LWRpke'_eq: 
equiv[Correctness(LWRpke).main ~ Correctness(LWRpke').main : ={arg} ==> ={res}] by sim.

lemma LWRpke'_small_error_correct:
hoare[Correctness(LWRpke').main: 
          true ==> distmodq LWRpke'.er ZQ.zero < q %/ 4 => res].  
proof. 
proc;inline*. 
(*** We show that decryption is correct if total error is less than q/4       ***)
seq 23 : (d = LWRpke'.er + (ZQ.inzmod ((b2i m) * (q %/ 2)) ) ) => //; first last.
case (distmodq LWRpke'.er ZQ.zero < q %/ 4); auto => /> &hr H0. 
split.
case (m{hr}) => /> m.
apply StdOrder.IntOrder.ltr_gtF.
rewrite /b2i /=.
rewrite (distmodq_zero _ (ZQ.inzmod (q %/ 2))).
rewrite -MatZQ.ZR.addrA MatZQ.ZR.subrr MatZQ.ZR.addr0.
rewrite -dist_neg MatZQ.ZR.oppr0 in H0.
apply dist_asint_low in H0.
rewrite -dist_neg MatZQ.ZR.opprK MatZQ.ZR.oppr0 in H0.
rewrite -(dist_neg (_ + ZQ.inzmod _)).
by rewrite MatZQ.ZR.opprD MatZQ.ZR.oppr0 -distmodq_zero.
case (m{hr}) => /> m.
rewrite /b2i /= inzmod0 MatZQ.ZR.addr0.
by apply dist_asint_low.
(*** We show that d = total error plus encrypted bit times q/2                ***)
auto; progress.
apply MatZQ.Matrices.size_dmatrix in H.
apply MatZ2.Matrices.size_dvector in H0.
apply MatZ2.Matrices.size_dvector in H1.
case (m{hr}) => /> _. (* case message is 1 *)
rewrite /b2i /=.
rewrite rndv_liftv_dotp_mterm.
rewrite size_mulmxv.
rewrite size_Z2v2ZQ. smt(n_ge0 m_ge0). smt(n_ge0 m_ge0).
have ->: (liftv2ZQ (rndv2ZP (mA *^ Z2v2ZQ s))) = (mA *^ Z2v2ZQ s) - rndv_err(mA *^ Z2v2ZQ s).
rewrite /rndv_err. 
rewrite oppvD.
by rewrite sizeN size_liftv size_rndv.
rewrite oppvK addvA addNv.
have ->: size (mA *^ Z2v2ZQ s) = size (liftv2ZQ (rndv2ZP (mA *^ Z2v2ZQ s))) by rewrite size_liftv size_rndv.
by rewrite add0v.
rewrite dotpDr.
by rewrite sizeN size_rndv_err.
have ->: (liftv2ZQ (rndv2ZP (Z2v2ZQ r ^* mA))) = (Z2v2ZQ r ^* mA) - rndv_err(Z2v2ZQ r ^* mA).
rewrite /rndv_err. 
rewrite oppvD.
by rewrite sizeN size_liftv size_rndv.
rewrite oppvK addvA addNv.
have ->: size (Z2v2ZQ r ^* mA) = size (liftv2ZQ (rndv2ZP (Z2v2ZQ r ^* mA))) by rewrite size_liftv size_rndv.
by rewrite add0v.
rewrite dotpDl.
by rewrite sizeN size_rndv_err.
simplify.
rewrite MatZQ.ZR.opprD MatZQ.ZR.opprK.
have ->: dotp (Z2v2ZQ r) (mA *^ Z2v2ZQ s) = dotp (Z2v2ZQ r ^* mA) (Z2v2ZQ s). rewrite dotp_mulmxv.
rewrite size_Z2v2ZQ. smt(n_ge0 m_ge0).
rewrite size_Z2v2ZQ. smt(n_ge0 m_ge0). done.
have ->: dotp (Z2v2ZQ r) (- rndv_err (mA *^ Z2v2ZQ s)) = (- dotp (Z2v2ZQ r) (rndv_err (mA *^ Z2v2ZQ s)))
  by rewrite dotpC dotpNv dotpC.
rewrite MatZQ.ZR.addrA. rewrite MatZQ.ZR.addrC.
have ->: (dotp (Z2v2ZQ r ^* mA) (Z2v2ZQ s) - dotp (Z2v2ZQ r) (rndv_err (mA *^ Z2v2ZQ s)) +
  (inzmod (q %/ 2))%ZQ - dotp (Z2v2ZQ r ^* mA) (Z2v2ZQ s)) = ((- dotp (Z2v2ZQ r ^* mA) (Z2v2ZQ s)) +
  dotp (Z2v2ZQ r ^* mA) (Z2v2ZQ s) - dotp (Z2v2ZQ r) (rndv_err (mA *^ Z2v2ZQ s)))%MatZQ.ZR +
  (inzmod (q %/ 2))%ZQ by rewrite MatZQ.ZR.addrC 2!MatZQ.ZR.addrA.
have ->: (- dotp (Z2v2ZQ r ^* mA) (Z2v2ZQ s)) + dotp (Z2v2ZQ r ^* mA) (Z2v2ZQ s) = ZQ.zero.
rewrite MatZQ.ZR.addrC.
by rewrite MatZQ.ZR.addrN. 
rewrite MatZQ.ZR.add0r.
by rewrite MatZQ.ZR.addrA (MatZQ.ZR.addrC (dotp (rndv_err (Z2v2ZQ r ^* mA)) (Z2v2ZQ s)) (- dotp (Z2v2ZQ r) (rndv_err (mA *^ Z2v2ZQ s)))).
(* case message is 0 *)
rewrite /b2i /=.
have ->: ZQ.inzmod 0 = ZQ.zero by smt().
  do rewrite MatZQ.ZR.addr0.
rewrite rndv_liftv_dotp.
rewrite size_mulmxv.
rewrite size_Z2v2ZQ. smt(n_ge0 m_ge0). smt(n_ge0 m_ge0).
have ->: (liftv2ZQ (rndv2ZP (mA *^ Z2v2ZQ s))) = (mA *^ Z2v2ZQ s) - rndv_err(mA *^ Z2v2ZQ s).
rewrite /rndv_err. 
    rewrite oppvD.
by rewrite sizeN size_liftv size_rndv.
rewrite oppvK addvA addNv.
have ->: size (mA *^ Z2v2ZQ s) = size (liftv2ZQ (rndv2ZP (mA *^ Z2v2ZQ s))) by rewrite size_liftv size_rndv.
by rewrite add0v.
rewrite dotpDr.
by rewrite sizeN size_rndv_err.
have ->: (liftv2ZQ (rndv2ZP (Z2v2ZQ r ^* mA))) = (Z2v2ZQ r ^* mA) - rndv_err(Z2v2ZQ r ^* mA).
rewrite /rndv_err. 
    rewrite oppvD.
by rewrite sizeN size_liftv size_rndv.
rewrite oppvK addvA addNv.
have ->: size (Z2v2ZQ r ^* mA) = size (liftv2ZQ (rndv2ZP (Z2v2ZQ r ^* mA))) by rewrite size_liftv size_rndv.
by rewrite add0v.
rewrite dotpDl.
by rewrite sizeN size_rndv_err.
simplify.
rewrite MatZQ.ZR.opprD MatZQ.ZR.opprK.
have ->: dotp (Z2v2ZQ r) (mA *^ Z2v2ZQ s) = dotp (Z2v2ZQ r ^* mA) (Z2v2ZQ s). rewrite dotp_mulmxv.
rewrite size_Z2v2ZQ. smt(n_ge0 m_ge0).
rewrite size_Z2v2ZQ. smt(n_ge0 m_ge0). done.
have ->: dotp (Z2v2ZQ r) (- rndv_err (mA *^ Z2v2ZQ s)) = (- dotp (Z2v2ZQ r) (rndv_err (mA *^ Z2v2ZQ s)))
  by rewrite dotpC dotpNv dotpC.
rewrite MatZQ.ZR.addrA.
have ->: (dotp (Z2v2ZQ r ^* mA) (Z2v2ZQ s) - dotp (Z2v2ZQ r) (rndv_err (mA *^ Z2v2ZQ s)) -
 dotp (Z2v2ZQ r ^* mA) (Z2v2ZQ s)) = (- dotp (Z2v2ZQ r ^* mA) (Z2v2ZQ s)) +
(dotp (Z2v2ZQ r ^* mA) (Z2v2ZQ s) - dotp (Z2v2ZQ r) (rndv_err (mA *^ Z2v2ZQ s))) by rewrite MatZQ.ZR.addrC.
rewrite MatZQ.ZR.addrA.
have ->: (- dotp (Z2v2ZQ r ^* mA) (Z2v2ZQ s)) + dotp (Z2v2ZQ r ^* mA) (Z2v2ZQ s) = ZQ.zero.
rewrite MatZQ.ZR.addrC.
by rewrite MatZQ.ZR.addrN. 
by rewrite MatZQ.ZR.add0r.
qed. 


(********************************************************************************)
(*** Prove that the probability of decrypting correctly in LWRpke is greater  ***)
(*** than or equal to the probability of the total error being below q/4.     ***)
(********************************************************************************)

lemma LWRpke'_correct_bounded_error &m pt : 
    Pr[Correctness(LWRpke').main(pt) @ &m : distmodq LWRpke'.er ZQ.zero < q %/ 4] <=
     Pr[Correctness(LWRpke').main(pt) @ &m : res]. 
byequiv => //.
conseq (_: ={m} /\ m{1} = pt ==> ={res, LWRpke'.er}) (_: true ==> true)
  (_: true ==>  distmodq LWRpke'.er ZQ.zero < q %/ 4 => res) => // />.
exact LWRpke'_small_error_correct.
proc.
call (: ={arg, LWRpke'.s, LWRpke'.r, LWRpke'.e1, LWRpke'.e2} ==> ={res, LWRpke'.er}). 
sim.
call (: ={arg, LWRpke'.s, LWRpke'.e1} ==> ={res, LWRpke'.s, LWRpke'.r, LWRpke'.e1, LWRpke'.e2}).
sim. 
call (: ={arg} ==> ={res, LWRpke'.s, LWRpke'.e1}). 
sim. auto. 
qed.

lemma LWRpke_correct_bounded_error &m pt : 
    Pr[Correctness(LWRpke').main(pt) @ &m : distmodq LWRpke'.er ZQ.zero < q %/ 4] <=
     Pr[Correctness(LWRpke).main(pt) @ &m : res]. 
proof. 
have -> :  Pr[Correctness(LWRpke).main(pt) @ &m : res] = Pr[Correctness(LWRpke').main(pt) @ &m : res]
  by byequiv (LWRpke_LWRpke'_eq). 
exact/LWRpke'_correct_bounded_error. 
qed.

(********************************************************************************)
(***                Security Proof with game sequence and hops                ***)
(********************************************************************************)

section Security_Proof.

(* Declare an IND-CPA adversary with terminating procedures *)
declare module A <: Adversary.
declare axiom Ac_ll : islossless A.choose.
declare axiom Ag_ll : islossless A.guess.


(* Game sequence *)
module G1 = {
  proc main () : bool = {
    var mA, t', t, m0, m1, b, r, u', u, v', v, b';
    mA      <$ dmatrix dzqu m n;
    t'      <$ dvector dzqu m;
    t       <- rndv2ZP t';
    (m0,m1) <@ A.choose((mA, t));
    b       <$ {0,1};
    r       <$ dvector dz2u m;
    u'      <- (Z2v2ZQ r) ^* mA;
    u       <- rndv2ZP (u');
    v'      <- dotp (Z2v2ZQ r) (liftv2ZQ t);
    v       <- rnd2ZP (v' + ZQ.inzmod ((b2i (b?m1:m0)) * (q %/ 2)));
    b'      <@ A.guess((u, v));
    return b' = b;
  }
}.


module G2 = {
  proc main () : bool = {
    var mA, t', t, m0, m1, b, r, u', u, v', v, b';
    mA      <$ dmatrix dzqu m n;
    t'      <$ dvector dzqu m;
    t       <- rndv2ZP t';
    (m0,m1) <@ A.choose((mA, t));
    b       <$ {0,1};
    r       <$ dvector dz2u m;
    u'      <- (Z2v2ZQ r) ^* mA;
    u       <- rndv2ZP (u');
    v'      <- dotp (Z2v2ZP r) t;
    v       <- (v' + ZP.inzmod ((b2i (b?m1:m0)) * (p %/ 2)));
    b'      <@ A.guess((u, v));
    return b' = b;
  }
}.

module G3 = {
  proc main () : bool = {
    var mA, t', t, m0, m1, b, r, u', u, v', v, b';
    mA      <$ dmatrix dzqu m n;
    t'      <$ dvector dzqu m;
    t       <- rndv2ZP t';
    (m0,m1) <@ A.choose((mA, t));
    b       <$ {0,1};
    r       <$ dvector dz2u m;
    u'      <$ dvector dzqu n;
    u       <- rndv2ZP (u');
    v'      <$ dzpu;
    v       <- (v' + ZP.inzmod ((b2i (b?m1:m0)) * (p %/ 2)));
    b'      <@ A.guess((u, v));
    return b' = b;
  }
}.

module G4 = {
  proc main () : bool = {
    var mA, t', t, m0, m1, b, r, u', u, v', v, b';
    mA      <$ dmatrix dzqu m n;
    t'      <$ dvector dzqu m;
    t       <- rndv2ZP t';
    (m0,m1) <@ A.choose((mA, t));
    b       <$ {0,1};
    r       <$ dvector dz2u m;
    u'      <$ dvector dzqu n;
    u       <- rndv2ZP (u');
    v'      <$ dzpu;
    v       <- v';
    b'      <@ A.guess((u, v));
    return b' = b;
  }
}.

module G5 = {
  proc main () : bool = {
    var mA, t', t, m0, m1, b, r, u', u, v', v, b';
    mA      <$ dmatrix dzqu m n;
    t'      <$ dvector dzqu m;
    t       <- rndv2ZP t';
    (m0,m1) <@ A.choose((mA, t));
    r       <$ dvector dz2u m;
    u'      <$ dvector dzqu n;
    u       <- rndv2ZP (u');
    v'      <$ dzpu;
    v       <- v';
    b'      <@ A.guess((u, v));
    b       <$ {0,1};
    return b' = b;
  }
}.


(* Game hopping with equivalence lemmas *)
lemma g0_dlwr0_eq &m:
    Pr[CPA(LWRpke, A).main() @ &m : res] =
    Pr[DLWR0(Red_A_DLWR(A)).main() @ &m : res].
proof.
byequiv=> //; proc; inline *.
auto; call (_: true).
auto. call (_: true).
auto.
qed.

lemma g1_dlwr1_eq &m:
    Pr[G1.main() @ &m : res] =
    Pr[DLWR1(Red_A_DLWR(A)).main() @ &m : res].
proof.
byequiv=> //; proc; inline *.
wp; call (_: true); auto.
call (_: true); auto.
qed.

lemma g1_g2_eq &m:
    Pr[G1.main() @ &m : res] =
    Pr[G2.main() @ &m : res].
proof.    
byequiv=> //; proc; inline*.
call (_: true).
auto. call (_: true).
auto => />; progress.
case bL => H3.
rewrite /b2i /=.
case result_R.`2 => H4 /=.
rewrite v_mterm_eq //=.
apply MatZQ.Matrices.size_dvector in H0.
apply MatZ2.Matrices.size_dvector in H2.
smt(m_ge0).
have ->: ZQ.inzmod 0 = ZQ.zero by smt().
have ->: ZP.inzmod 0 = ZP.zero by smt().
rewrite MatZQ.ZR.addr0 MatZP.ZR.addr0.
rewrite v'_eq //=.
apply MatZQ.Matrices.size_dvector in H0.
apply MatZ2.Matrices.size_dvector in H2.
smt(m_ge0).
case result_R.`1 => H4 /=.
rewrite v_mterm_eq //=.
apply MatZQ.Matrices.size_dvector in H0.
apply MatZ2.Matrices.size_dvector in H2.
smt(m_ge0).
have ->: ZQ.inzmod 0 = ZQ.zero by smt().
have ->: ZP.inzmod 0 = ZP.zero by smt().
rewrite MatZQ.ZR.addr0 MatZP.ZR.addr0.
rewrite v'_eq //=.
apply MatZQ.Matrices.size_dvector in H0.
apply MatZ2.Matrices.size_dvector in H2.
smt(m_ge0).
qed.

lemma g2_g3_eq &m:
    Pr[G2.main() @ &m : res] =
    Pr[G3.main() @ &m : res].
proof.    
byequiv=> //; proc; inline*.
seq 6 6: (={glob A, m0, m1, b}). sim. 
call (_: true).
auto. 
progress.
rewrite MatZQ.Matrices.dvector_ll.
rewrite dzqu_ll.
admit. admit. (* requires the leftover hash lemma *)
qed.

lemma g3_g4_eq &m:
    Pr[G3.main() @ &m : res] =
    Pr[G4.main() @ &m : res].
proof.    
byequiv=> //; proc; inline *. 
call (_: true). wp.
rnd (fun (z: ZP.zmod) => z + (ZP.inzmod (b2i (if b{1} then m1{1} else m0{1}) * (p %/ 2)))) 
    (fun (z: ZP.zmod) => z - (ZP.inzmod (b2i (if b{1} then m1{1} else m0{1}) * (p %/ 2)))).
auto. call (_: true). auto => /> mA' _ R b. progress. 
rewrite -MatZP.ZR.addrA.
rewrite MatZP.ZR.addNr MatZP.ZR.addr0 //.
have ->: v'L + (ZP.inzmod (b2i (if bL then result_R.`2 else result_R.`1) * (p %/ 2))) -
 (ZP.inzmod (b2i (if bL then result_R.`2 else result_R.`1) * (p %/ 2))) = v'L + ZP.zero.
rewrite -MatZP.ZR.addrA.
have ->: (ZP.inzmod (b2i (if bL then result_R.`2 else result_R.`1) * (p %/ 2))) -
 (ZP.inzmod (b2i (if bL then result_R.`2 else result_R.`1) * (p %/ 2))) = ZP.zero by rewrite MatZP.ZR.addrN //.
rewrite MatZP.ZR.addr0 //.
rewrite MatZP.ZR.addr0 //.
qed.

lemma g4_g5_eq &m:
    Pr[G4.main() @ &m : res] =
    Pr[G5.main() @ &m : res].
proof.
byequiv (_: ={glob A} ==> ={res}) => //.
proc; inline *.
swap{2} 11 -6.
call (_: true). auto.
call (_: true). auto.
qed.
    
lemma g5_half &m:
    Pr[G5.main() @ &m : res] = 1%r/2%r.
proof.
byphoare=> //; proc; inline *.    
 rnd  (pred1 b')=> //=.
conseq (: _ ==> true).
by move=> /> b; rewrite dbool1E pred1E. 
islossless; smt(Ag_ll Ac_ll MatZ2.Matrices.dvector_ll dz2u_ll MatZQ.Matrices.dvector_ll
  MatZQ.Matrices.dmatrix_ll dzqu_ll).
qed.

(* Concluding lemma for the security proof of the LWR PKE scheme *)
lemma conclusion &m:
  `| Pr[CPA(LWRpke, A).main() @ &m : res] - 1%r/2%r | =
    `| Pr[DLWR0(Red_A_DLWR(A)).main() @ &m : res]
       - Pr[DLWR1(Red_A_DLWR(A)).main() @ &m : res] |.
proof.
rewrite -(g5_half &m) //.
rewrite -g4_g5_eq -g3_g4_eq -g2_g3_eq -g1_g2_eq.
by rewrite g0_dlwr0_eq g1_dlwr1_eq.
qed.
