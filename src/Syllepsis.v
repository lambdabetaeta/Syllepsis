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


(* Eckmann-Hilton *)

Definition EH {X} {a : X} (p q : idpath a = idpath a) :
  p @ q = q @ p.
Proof.
  exact (
    (rightSqueeze (ulnat p) @@ rightSqueeze (urnat q))^
    @ wlrnat q p
    @ (rightSqueeze (urnat q) @@ rightSqueeze (ulnat p))
  ).
Defined.

(* EH on reflexivity (Section 4) *)

Local Definition EH_refl_L_coh {X} {a b c : X} {p q : a = b} {r : b = c} 
  {alpha : p = q} {s : p @ r = q @ r} (theta : whiskerR alpha r = s)
  : (1 @@ theta)^ @ wlrnat alpha (idpath r) @ (theta @@ 1)
      = concat_1p s @ (concat_p1 s)^.
Proof.
  induction theta, alpha. exact 1.
Defined.

Local Definition EH_refl_L {X} {a : X} (p : idpath a = idpath a) :
  EH 1 p  = concat_1p p @ (concat_p1 p)^.
Proof.
  unfold EH. 
  srapply (EH_refl_L_coh (p:=1) (q:=1) (r:=1) (rightSqueeze (urnat p))).
Defined.

Local Definition EH_refl_R_coh {X} {a b c : X} {p : a = b} {q r : b = c} {alpha : q = r}
  {s : p @ q = p @ r} (theta : whiskerL p alpha = s)
  : ((theta @@ 1)^ @ wlrnat (idpath p) alpha @ (1 @@ theta))
      = concat_p1 s @ (concat_1p s)^.
Proof.
  induction theta, alpha. exact 1.
Defined.

Local Definition EH_refl_R {X} {a : X} (p : idpath a = idpath a) :
  EH p idpath = concat_p1 p @ (concat_1p p)^.
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

Section SquareInv.

  Context {X} {a0 a1 b0 b1 : X}.
  Context {a01 : a0 = a1} {b01 : b0 = b1}.
  Context {ab0 : a0 = b0} {ab1 : a1 = b1}.
  Context (phi : ab0 @ b01 = a01 @ ab1).

  Local Definition squareInv :
    ab1 @ b01^ = a01^ @ ab0.
  Proof.
    induction a01; induction b01. simpl. 
    revert phi; srapply (equiv_ind rightSqueeze^-1); intro phi.
    induction phi.
    srapply (rightSqueeze^-1 idpath).
  Defined.

End SquareInv.

Notation "phi ^<-" := (squareInv phi) (at level 20).
  

(* NATURALITY OF EH (section 6) *)

Local Definition EH_nat_L {X} {a : X} {p q r : idpath a = idpath a} 
    (alpha : p = q)
  : whiskerR alpha r @ EH q r = EH p r @ whiskerL r alpha.
Proof.
  induction alpha. unfold whiskerL. simpl.
  srapply (downSqueeze^-1 idpath).
Defined.

Local Definition EH_nat_R {X} {a : X} {p q r : idpath a = idpath a}
    (alpha : p = q) 
  : whiskerL r alpha @ EH r q = EH r p @ whiskerR alpha r.
Proof.
  induction alpha. unfold whiskerL. simpl.
  srapply (downSqueeze^-1 idpath).
Defined.


Section EH_ur_ul.

  Context {X} {a : X} {p} (alpha : idpath (idpath a) = p).
  
  Definition EH_nat_R_coh
    : EH_nat_R alpha
        = whiskerL _ (EH_refl_L p) @ (ulnat alpha [I] (urnat alpha)^<-).
  Proof.
    induction alpha. exact 1.  
  Defined.
  
  Definition EH_nat_L_coh 
    : EH_nat_L alpha = whiskerL _ (EH_refl_R p) @ (urnat alpha [I] (ulnat alpha)^<-).
  Proof.
    induction alpha. exact 1.  
  Defined.

End EH_ur_ul.

Definition EH_nat_iso_R {X} {a : X} (p : idpath (idpath a) = idpath (idpath a)) :
  EH_nat_R p = ulnat p [I] (urnat p)^<-.
Proof.
  srapply (EH_nat_R_coh p @ concat_1p _). 
Defined.

Definition EH_nat_iso_L {X} {a : X} (p : idpath (idpath a) = idpath (idpath a)) :
  EH_nat_L p = urnat p [I] (ulnat p)^<-.
Proof.
  srapply (EH_nat_L_coh p @ concat_1p _). 
Defined.

(* Square (b) *)

Local Definition doubleNat {X} {a : X} 
  {p q r s : idpath a = idpath a} (alpha : p = q) (beta : r = s)
  : whiskerR (wlrnat alpha beta) _ @ ((EH_nat_L alpha) [-] (EH_nat_R beta))
    @ whiskerL _ (wlrnat beta alpha) = ((EH_nat_R beta) [-] (EH_nat_L alpha)).
Proof.
  induction alpha, beta.
  cbn. srapply moveR_pM.
  srapply (downSqueeze^-1 1).
Defined.

(* Triangles (a) and (c) *)

Section Triangle_gen.

  Context {X} {a b c : X} {p q r : a = b} {u v w : b = c}
    {alpha : p @ 1 = 1 @ q} {beta : r @ 1 = 1 @ q}
    {gamma : u @ 1 = 1 @ v} {delta : w @ 1 = 1 @ v}
    {phi : p @ 1 = 1 @ r} {theta : u @ 1 = 1 @ w}
    (assn1 : phi = alpha [I] beta^<-)
    (assn2 : theta = gamma [I] delta^<-).

  (* We assume a setup of the form

     a ---1--- a ----1--- a                a --- 1 --- a
     |         |          |                |           |
     p  alpha  q  beta^<- r                p    phi    r
     |         |          |                |           |    
     b ---1--- b ----1--- b                b --- 1 --- b
     |         |          |                |           |
     u  gamma  v delta^<- w                u   theta   w
     |         |          |                |           |
     c ---1--- c ----1--- c                c --- 1 --- c

    and moreover that
       alpha [I] beta^<- = phi
       gamma [I] delta^<-  = theta

    Then, writing rSq := rightSqueeze, we can prove that 

       rSq (phi [-] theta) = (rSq alpha @@ rSq gamma) @ (rSq beta @@ rSq delta)^
  *) 

  Local Definition triangle :
    rightSqueeze (phi [-] theta) 
      = (rightSqueeze alpha @@ rightSqueeze gamma) @ (rightSqueeze beta @@ rightSqueeze delta)^.
  Proof.
    symmetry in assn1, assn2. induction assn1, assn2; clear assn1. clear assn2.
    revert alpha; srapply (equiv_ind rightSqueeze^-1); intro alpha; induction alpha.
    revert beta; srapply (equiv_ind rightSqueeze^-1); intro beta; induction beta.
    revert gamma; srapply (equiv_ind rightSqueeze^-1); intro gamma; induction gamma.
    revert delta; srapply (equiv_ind rightSqueeze^-1); intro delta; induction delta.
    induction r, w.
    simpl.
    exact 1.
  Defined.

End Triangle_gen.


Section Syllepsis.

  Context {X} {a b : X} {a1 a2 a3 a4 a5 a6 : a = b}
    {a21 : a2 = a1} {a31 : a3 = a1} {a24 : a2 = a4}
    {a53 : a5 = a3} {a46 : a4 = a6} {a56 : a5 = a6}
    {phi : a2 @ 1 = 1 @ a3} {theta : a4 @ 1 = 1 @ a5}.

  (* commuting square *)
  Hypothesis (H_sq : theta @ whiskerL 1 a53 = (whiskerR a24 1)^ @ phi).

  (* commuting upper triangle *)
  Hypothesis (H_tr_up : rightSqueeze phi = a21 @ a31^).

  (* commuting lower triangle *)
  Hypothesis (H_tr_lo : rightSqueeze theta = a46 @ a56^).

  (* syllepsis *)
  Local Lemma syllepsis_gen : (a21^ @ a24 @ a46) @ (a56^ @ a53 @ a31) = 1.
  Proof.
    induction a21, a56, a24, a53, a31.
    cbn in *. 
    revert H_tr_up. revert H_tr_lo.
    revert H_sq; srapply (equiv_ind rightSqueeze^-1). intro H_sq.
    induction H_sq; clear H_sq.
    intro H_tr_lo. intro H_tr_up.
    hott_simpl.
    symmetry in H_tr_lo. induction H_tr_lo.
    srapply H_tr_up.
  Qed.

End Syllepsis.

Definition syllepsis {X} {a : X} (p q : idpath (idpath a) = idpath (idpath a))
  : EH p q @ EH q p = 1.
Proof.
  rapply syllepsis_gen.
  - srapply moveL_Vp. 
    refine (concat_p_pp _ _ _ @ _).
    exact (doubleNat q p).
  - exact (triangle (EH_nat_iso_R p) (EH_nat_iso_L q)).
  - exact (triangle (EH_nat_iso_L q) (EH_nat_iso_R p)).
Defined.