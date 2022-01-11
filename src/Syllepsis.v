From HoTT Require Import Basics Types.
  
(* Monoidal isomorphisms *)

Local Definition ulnat {X} {a b : X} {p q : a = b} (alpha : p = q) :
  whiskerL 1 alpha @ concat_1p q = concat_1p p @ alpha.
Proof.
  induction p, alpha. exact 1.
Defined. 

Local Definition urnat {X} {a b : X} {p q : a = b} (alpha : p = q) :
  whiskerR alpha 1 @ concat_p1 q = concat_p1 p @ alpha.
Proof.
  induction p, alpha. exact 1.
Defined. 

Local Definition rightSqueeze {X} {a b : X} {p q : a = b}
  : (p @ 1 = 1 @ q) <~> (p = q).
Proof.
  refine (equiv_compose' _ _).
  - exact (equiv_concat_r (concat_1p _) _).
  - exact (equiv_concat_l (concat_p1 _)^ _).
Defined.

Local Definition downSqueeze {X} {a b : X} {p q : a = b}
  : (1 @ p = q @ 1) <~> (p = q) .
Proof.
  refine (equiv_compose' _ _).
  - exact (equiv_concat_r (concat_p1 _) _).
  - exact (equiv_concat_l (concat_1p _)^ _).
Defined.

Local Definition wlrnat {X} {a b c : X} {p q : a = b} {r s : b = c} alpha beta
  : whiskerL p beta @ whiskerR alpha s = whiskerR alpha r @ whiskerL q beta.
Proof.
  induction alpha, beta. exact 1.
Defined.

Local Definition hconcatnat {X} {a b c : X} {p r : a = b} 
  {q s : b = c} (alpha : p = r) (beta : q = s)
  : alpha @@ beta = whiskerL p beta @ whiskerR alpha s.
Proof.
  induction alpha, beta, p, q. exact 1.
Defined.

(* Eckmann-Hilton *)

Definition EH {X} {a : X} (p q : idpath a = idpath a) :
  p @ q = q @ p.
Proof.
  exact (
    (rightSqueeze (ulnat p) @@ rightSqueeze (urnat q))^
    @ wlrnat q p
    @ (rightSqueeze (urnat q) @@ rightSqueeze (ulnat p))).
Defined.

(* EH on reflexivity (Section 4) *)

Local Definition EH_refl_L_coh {X} {a b c : X} {p q : a = b} {r : b = c} 
  {alpha : p = q} {s : p @ r = q @ r} (theta : whiskerR alpha r = s)
  : (1 @@ theta)^ @ wlrnat alpha (idpath r) @ (theta @@ 1) @ concat_p1 s
      = concat_1p s.
Proof.
  induction theta, alpha. exact 1.
Defined.

Local Definition EH_refl_L {X} {a : X} (p : idpath a = idpath a) :
  EH 1 p @ concat_p1 p = concat_1p p.
Proof.
  unfold EH. 
  srapply (EH_refl_L_coh (p:=1) (q:=1) (r:=1) (rightSqueeze (urnat p))).
Defined.

Local Definition EH_refl_R_coh {X} {a b c : X} {p : a = b} {q r : b = c} {alpha : q = r}
  {s : p @ q = p @ r} (theta : whiskerL p alpha = s)
  : ((theta @@ 1)^ @ wlrnat (idpath p) alpha @ (1 @@ theta)) @ concat_1p s
      = concat_p1 s.
Proof.
  induction theta, alpha. exact 1.
Defined.

Local Definition EH_refl_R {X} {a : X} (p : idpath a = idpath a) :
  EH p idpath @ concat_1p p = concat_p1 p.
Proof.
  unfold EH.
  srapply (EH_refl_R_coh (p:=1) (q:=1) (r:=1) (rightSqueeze (ulnat p))).
Defined.


(* SQUARES (section 5) *)

Section SqConcatV.

  Context {X} {a0 a1 b0 b1 c0 c1 : X}
   {a01 : a0 = a1} {b01 : b0 = b1} {c01 : c0 = c1}
   {ab0 : a0 = b0} {bc0 : b0 = c0}
   {ab1 : a1 = b1} {bc1 : b1 = c1}
   (phi : ab0 @ b01 = a01 @ ab1)
   (theta : bc0 @ c01 = b01 @ bc1).
     
  (* 
      a0 ---a01--- a1
      |            |
     ab0    phi   ab1
      |            |
      b0 ---b01--- b1
      |            |
     bc0   theta   bc1
      |            |   
      c0 ---c01--- c1
  *)

  Local Definition sqConcatV :
    (ab0 @ bc0) @ c01 = a01 @ (ab1 @ bc1).
  Proof.
    refine (concat_pp_p _ _ _ @ _).
    refine (whiskerL ab0 theta @ _).
    refine (concat_p_pp _ _ _ @ _).
    refine (whiskerR phi bc1 @ _).
    srapply concat_pp_p.
  Defined.
  
End SqConcatV.

Infix "[-]" := (sqConcatV) (at level 60).

  (* 
      a ---1--- a
      |         |
      p    phi  q
      |         |
      b ---1--- b
      |         |
      r  theta  s
      |         |   
      c ---1--- c
  *)
  
Local Definition sqConcatVSqueeze{X} {a b c : X} 
  {p : a = b} {q : a = b} {r : b = c} {s : b = c}
  (phi : p @ 1 = 1 @ q) (theta : r @ 1 = 1 @ s)
  : rightSqueeze phi @@ rightSqueeze theta = rightSqueeze (phi [-] theta).
Proof.
  revert phi; srapply (equiv_ind rightSqueeze^-1); intro phi.
  revert theta; srapply (equiv_ind rightSqueeze^-1); intro theta.
  induction phi, theta.
  induction p, r. simpl.
  exact 1.
Defined.

Section SqConcatH.

  Context {X} {a0 b0 c0 a1 b1 c1 : X}
    {a01 : a0 = a1} {ab0 : a0 = b0}
    {ab1 : a1 = b1} {bc0 : b0 = c0} 
    {bc1 : b1 = c1} {b01 : b0 = b1}
    {c01 : c0 = c1}
    (phi : a01 @ ab1 = ab0 @ b01)
    (theta : b01 @ bc1 = bc0 @ c01).

  (*
      a0 --ab0-- b0 --bc0-- c0
      |          |          | 
     a01   phi  b01  theta  c01 
      |          |          |
      a1 --ab1-- b1 --bc1-- c1
  *)
  
  Local Definition sqConcatH :
    a01 @ (ab1 @ bc1) = (ab0 @ bc0) @ c01.
  Proof.
    refine (concat_p_pp _ _ _ @ _).
    refine (whiskerR phi _ @ _).
    refine (concat_pp_p _ _ _ @ _).
    refine (whiskerL _ theta @ _).
    srapply concat_p_pp.
  Defined.

End SqConcatH.

Infix "[I]" := (sqConcatH) (at level 60).

(*
    a --1-- a --1-- a
    |       |       | 
    p  phi  q theta r 
    |       |       |
    b --1-- b --1-- b
*)

Definition sqConcatHSqueeze {X} {a b : X} {p q r : a = b}
    (phi : p @ 1 = 1 @ q) (theta : q @ 1 = 1 @ r)
  : rightSqueeze phi @ rightSqueeze theta = rightSqueeze (phi [I] theta).
Proof.
  revert phi; srapply (equiv_ind rightSqueeze^-1); intro phi.
  revert theta; srapply (equiv_ind rightSqueeze^-1); intro theta.
  induction phi, theta.
  induction p. simpl.
  exact 1.
Defined.
  

Section sqInv.

  Context {X} {a0 a1 b0 b1 : X}.
  Context {a01 : a0 = a1} {b01 : b0 = b1}.
  Context {ab0 : a0 = b0} {ab1 : a1 = b1}.
  Context (phi : ab0 @ b01 = a01 @ ab1).

  Local Definition sqInv :
    ab1 @ b01^ = a01^ @ ab0.
  Proof.
    induction a01; induction b01. simpl. 
    revert phi; srapply (equiv_ind rightSqueeze^-1); intro phi.
    induction phi.
    srapply (rightSqueeze^-1 idpath).
  Defined.

End sqInv.

Notation "phi ^<-" := (sqInv phi) (at level 20).

(*
    a --1-- a 
    |       |
    p  phi  q
    |       |
    b --1-- b
*)

Definition sqInvSqueeze {X} {a b : X} {p q : a = b} (phi : p @ 1 = 1 @ q)
  : (rightSqueeze phi)^ = rightSqueeze (phi^<-).
Proof.
  revert phi; srapply (equiv_ind rightSqueeze^-1); intro phi.
  induction phi, p. simpl.
  exact 1.
Defined.

(*

    CUBICAL INTERCHANGE

    a0 ---i0--- b0 ---j0--- c0
    |           |           |
    p   alpha   q    beta   r
    |           |           |
    a1 ---i1--- b1 ---j1--- c1
    |           |           |
    u   gamma   v   delta   w
    |           |           |
    a2 ---i2--- b2 ---j2--- c2
*)

Definition cubicalitch {X} {a0 a1 a2 b0 b1 b2 c0 c1 c2 : X}
  {p : a0 = a1} {q : b0 = b1} {r : c0 = c1}
  {u : a1 = a2} {v : b1 = b2} {w : c1 = c2}
  {i0 : a0 = b0} {j0 : b0 = c0} {i1 : a1 = b1} {j1 : b1 = c1}
  {i2 : a2 = b2} {j2 : b2 = c2}
  (alpha : p @ i1 = i0 @ q) (beta : q @ j1 = j0 @ r)
  (gamma : u @ i2 = i1 @ v) (delta : v @ j2 = j1 @ w)
  : (alpha [-] gamma) [I] (beta [-] delta) = (alpha [I] beta) [-] (gamma [I] delta).
Proof.
  induction i0, i1, i2, j0, j1, j2.
  revert alpha; srapply (equiv_ind rightSqueeze^-1); intro alpha.
  revert beta; srapply (equiv_ind rightSqueeze^-1); intro beta.
  revert gamma; srapply (equiv_ind rightSqueeze^-1); intro gamma.
  revert delta; srapply (equiv_ind rightSqueeze^-1); intro delta.
  induction alpha, beta, gamma, delta.
  induction p, u.
  unfold "[I]"; unfold "[-]"; simpl.
  exact 1.
Defined.


(* NATURALITY OF EH (section 6) *)

Local Definition EHnatL {X} {a : X} {p q r : idpath a = idpath a} 
    (alpha : p = q)
  : whiskerR alpha r @ EH q r = EH p r @ whiskerL r alpha.
Proof.
  induction alpha. unfold whiskerL. simpl.
  srapply (downSqueeze^-1 idpath).
Defined.

Local Definition EHnatR {X} {a : X} {p q r : idpath a = idpath a}
    (alpha : p = q) 
  : whiskerL r alpha @ EH r q = EH r p @ whiskerR alpha r.
Proof.
  induction alpha. unfold whiskerL. simpl.
  srapply (downSqueeze^-1 idpath).
Defined.


Section EH_ur_ul.

  Context {X} {a : X} {p} (alpha : idpath (idpath a) = p).

  Definition EHnatR_coh
    : EHnatR alpha [I] urnat alpha = whiskerL _ (EH_refl_L p) @ ulnat alpha.
  Proof.
    induction alpha. exact 1.  
  Defined.
  
  Definition EHnatL_coh 
    : EHnatL alpha [I] ulnat alpha = whiskerL _ (EH_refl_R p) @ urnat alpha.
  Proof.
    induction alpha. exact 1.  
  Defined.

End EH_ur_ul.

Definition EH_nat_R {X} {a : X} (p : idpath (idpath a) = idpath (idpath a)) :
  EHnatR p [I] urnat p = ulnat p.
Proof.
  srapply (EHnatR_coh p @ _). 
  srapply (concat_1p _ @ _).
  exact 1.
Defined.

Definition EH_nat_L {X} {a : X} (p : idpath (idpath a) = idpath (idpath a)) :
  EHnatL p [I] ulnat p = urnat p.
Proof.
  srapply (EHnatL_coh p @ _). 
  srapply (concat_1p _ @ _).
  exact 1.
Defined.

(* Square (b) *)

Section Hermitian.
  
  Context {X} {a : X} {p q r s : idpath a = idpath a}
    (alpha : p = q) (beta : r = s).

  Local Definition hermitian_top 
    : (whiskerL p beta @ whiskerR alpha s) @ EH q s
        = EH p r @ (whiskerR beta p @ whiskerL s alpha)
    := (EHnatR beta) [-] (EHnatL alpha).

  Local Definition hermitian_bottom
    : (whiskerR alpha r @ whiskerL q beta) @ EH q s 
       = EH p r @ (whiskerL r alpha @ whiskerR beta q)
    := (EHnatL alpha) [-] (EHnatR beta).
      
End Hermitian.

Local Definition hermitian {X} {a : X} 
  {p q r s : idpath a = idpath a} (alpha : p = q) (beta : r = s)
  : whiskerR (wlrnat alpha beta) _ @ ((EHnatL alpha) [-] (EHnatR beta))
    @ whiskerL _ (wlrnat beta alpha) = ((EHnatR beta) [-] (EHnatL alpha)).
Proof.
  induction alpha, beta.
  cbn. srapply moveR_pM.
  srapply (downSqueeze^-1 1).
Defined.

(* Triangles (a) and (c) *)

Section Triangle.

  Context {X} {a : X} (p q : idpath (idpath a) = idpath (idpath a)).
  
  Check hermitian q p.

  Local Definition triangleU :
    rightSqueeze (EHnatR p [-] EHnatL q)
     @ (rightSqueeze (urnat p) @@ rightSqueeze (ulnat q))
      = rightSqueeze (ulnat p) @@ rightSqueeze (urnat q).
  Proof.
    rewrite sqConcatVSqueeze.
    rewrite sqConcatVSqueeze.
    rewrite sqConcatHSqueeze.
    srapply ap.
    srapply (cubicalitch _ _ _ _ @ _).
    srapply (ap (fun z => z [-] _) (EH_nat_R _)  @ _).
    srapply (ap (fun z => _ [-] z) (EH_nat_L _)  @ _).
    exact 1.
  Defined.
  
  Local Definition triangleD :
    rightSqueeze (EHnatL q [-] EHnatR p)
     @ (rightSqueeze (ulnat q) @@ rightSqueeze (urnat p))
      = rightSqueeze (urnat q) @@ rightSqueeze (ulnat p).
  Proof.
    rewrite sqConcatVSqueeze.
    rewrite sqConcatVSqueeze.
    rewrite sqConcatHSqueeze.
    srapply ap.
    srapply (cubicalitch _ _ _ _ @ _).
    srapply (ap (fun z => z [-] _) (EH_nat_L _)  @ _).
    srapply (ap (fun z => _ [-] z) (EH_nat_R _)  @ _).
    exact 1.
  Defined.

End Triangle.


Section Syllepsis.

  Context {X} {a b : X} {a1 a2 a3 a4 a5 a6 : a = b}
    {a12 : a1 = a2} {a31 : a3 = a1} {a24 : a2 = a4}
    {a53 : a5 = a3} {a46 : a4 = a6} {a65 : a6 = a5}
    {phi : a2 @ 1 = 1 @ a3} {theta : a4 @ 1 = 1 @ a5}.

  (* commuting square *)
  Hypothesis (H_sq : theta @ whiskerL 1 a53 = (whiskerR a24 1)^ @ phi).

  (* commuting upper triangle *)
  Hypothesis (H_tr_up : a12 @ rightSqueeze phi @ a31 = 1).

  (* commuting lower triangle *)
  Hypothesis (H_tr_lo : a46 @ a65 = rightSqueeze theta).

  (* syllepsis *)
  Local Lemma syllepsis_gen : (a12 @ a24 @ a46) @ (a65 @ a53 @ a31) = 1.
  Proof.
    induction a12, a46, a65, a24, a53.
    cbn in H_sq.
    revert H_sq; srapply (equiv_ind rightSqueeze^-1); intro H_sq; induction H_sq.
    rewrite <- H_tr_lo in H_tr_up.
    simpl in H_tr_up.
    cbn.
    rewrite H_tr_up.
    exact 1.
  Qed.

End Syllepsis.

Definition syllepsis {X} {a : X} (p q : idpath (idpath a) = idpath (idpath a))
  : EH p q @ EH q p = 1.
Proof.
  srapply syllepsis_gen.
  - srapply (EHnatR p [-] EHnatL q).
  - srapply (EHnatL q [-] EHnatR p).
  - srapply moveL_Vp.
    refine (concat_p_pp _ _ _ @ _).
    Check (hermitian q p).
    srapply (hermitian q p).
  - refine (concat_pp_p _ _ _ @ _).
    srapply moveR_Vp.
    srapply (_ @ (concat_p1 _)^).
    srapply triangleU.
  - srapply moveR_pV.
    symmetry.
    srapply triangleD.
Qed.