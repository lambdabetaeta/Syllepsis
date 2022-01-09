From HoTT Require Import Basics Types.
  
Reserved Infix "[-]" (at level 60).
Reserved Infix "[I]" (at level 50).

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
  refine (((rightSqueeze (ulnat p) @@ rightSqueeze (urnat q))^) @ _).
  refine (wlrnat q p @ _).
  refine (rightSqueeze (urnat q) @@ rightSqueeze (ulnat p)).
Defined.

(* EH on reflexivity *)

Local Definition EH_refl_L_coh {X} {a b c : X} {p q : a = b} {r : b = c} {alpha : p = q}
  {s : p @ r = q @ r} (theta : whiskerR alpha r = s)
  : (1 @@ theta)^ @ (wlrnat alpha (idpath r) @ (theta @@ 1))
      = concat_1p s @ (concat_p1 s)^.
Proof.
  induction theta, alpha. exact 1.
Defined.

Local Definition EH_refl_L {X} {a : X} (p : idpath a = idpath a) :
  EH idpath p = concat_1p p @ (concat_p1 p)^.
Proof.
  unfold EH. 
  srapply (EH_refl_L_coh (p:=1) (q:=1) (r:=1) (rightSqueeze (urnat p))).
Defined.

Local Definition EH_refl_R_coh {X} {a b c : X} {p : a = b} {q r : b = c} {alpha : q = r}
  {s : p @ q = p @ r} (theta : whiskerL p alpha = s)
  : (theta @@ 1)^ @ (wlrnat (idpath p) alpha @ (1 @@ theta))
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

(* Some technology about squares *)

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

Infix "[-]" := (sqConcatV).

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
  
Local Definition sqConcatVSqueeze {X} {a b c : X} 
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
  
  (*
    FIXME
    
      a0 ---1--- a0 --bc0-- c0
      |          |          | 
      p   phi    p  theta  c01 
      |          |          |
      a1 ---1--- a1 --bc1-- c1
  *)

End SqConcatH.

Infix "[I]" := (sqConcatH).

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
  {alpha : p @ i1 = i0 @ q} {beta : q @ j1 = j0 @ r}
  {gamma : u @ i2 = i1 @ v} {delta : v @ j2 = j1 @ w}
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


(* Naturality of Eckmann-Hilton *)

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


(* Local Definition EH_natL_sqConcatV' {X} {a : X} {u} (p : idpath (idpath a) = u) :
  EH_natL p = (whiskerL (whiskerL 1 p) (EH_refl_L u)) @
              (sqConcatV (ulnat p)^ (squareInv (urnat p))^)^.
Proof.
  induction p. exact 1.
Defined.

Local Definition EH_natR_sqConcatV' {X} {a : X} {u} (p : idpath (idpath a) = u) :
  EH_natR p = (whiskerL (whiskerR p 1) (EH_refl_R u)) @
              (sqConcatV (urnat p)^ (squareInv (ulnat p))^)^.
Proof.
  induction p. exact 1.
Defined.

Definition EH_natL_sqConcatV {X} {a : X} (p : idpath (idpath a) = idpath (idpath a)) :
  EH_natL p = (sqConcatV (ulnat p)^ (squareInv (urnat p))^)^.
Proof.
  refine (EH_natL_sqConcatV' _ @ _).
  exact (concat_1p _).
Defined.

Definition EH_natR_sqConcatV {X} {a : X} (p : idpath (idpath a) = idpath (idpath a)) :
  EH_natR p = (sqConcatV (urnat p)^ (squareInv (ulnat p))^)^.
Proof.
  refine (EH_natR_sqConcatV' _ @ _).
  exact (concat_1p _).
Defined. *)

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
  : whiskerR (wlrnat alpha beta) _ @ sesqui_bottom alpha beta 
    = sesqui_top alpha beta @ whiskerL _ (wlrnat beta alpha)^.
Proof.
  induction alpha, beta. simpl.
  srapply (downSqueeze^-1 1).
Defined.

Local Definition EL {X} {a : X} (p q : idpath (idpath a) = idpath (idpath a)) :
  (whiskerL 1 p @ whiskerR q 1) @ 1 = 1 @ (whiskerR p 1 @ whiskerL 1 q).
Proof.
  srapply rightSqueeze^-1.
  refine ((rightSqueeze (ulnat p) @@ rightSqueeze (urnat q)) @ _).
  refine ((rightSqueeze (urnat p) @@ rightSqueeze (ulnat q))^).
Defined.

Local Definition ER {X} {a : X} (p q : idpath (idpath a) = idpath (idpath a)) :
  (whiskerR q 1 @ whiskerL 1 p) @ 1 = 1 @ (whiskerL 1 q @ whiskerR p 1).
Proof.
  srapply rightSqueeze^-1.
  refine ((rightSqueeze (urnat q) @@ rightSqueeze (ulnat p)) @ _).
  refine ((rightSqueeze (ulnat q) @@ rightSqueeze (urnat p))^).
Defined.

Local Definition F {X} {a b c : X} {p0 p1 p2 : a = b} {q0 q1 q2 : b = c}
  {p01 : p0 @ 1 = 1 @ p1} {p12 : p2 @ 1 = 1 @ p1} {p02 : p0 @ 1 = 1 @ p2}
  {q01 : q0 @ 1 = 1 @ q1} {q12 : q2 @ 1 = 1 @ q1} {q02 : q0 @ 1 = 1 @ q2} :
  (sqConcatV p01^ (squareInv p12)^)^ = p02 ->
  (sqConcatV q01^ (squareInv q12)^)^ = q02 ->
  sqConcatV p02 q02 = rightSqueeze^-1 ((rightSqueeze p01 @@ rightSqueeze q01) @ (rightSqueeze p12 @@ rightSqueeze q12)^).
Proof.
  intros phi theta.
  induction phi; induction theta.
  revert p01; srapply (equiv_ind rightSqueeze^-1); intro p01.
  revert q01; srapply (equiv_ind rightSqueeze^-1); intro q01.
  revert p12; srapply (equiv_ind rightSqueeze^-1); intro p12.
  revert q12; srapply (equiv_ind rightSqueeze^-1); intro q12.
  induction p12, q12, p01, q01, p0, q0.
  exact 1.
Defined.

(* Local Definition DL_eq_EL {X} {a : X} (p q : idpath (idpath a) = idpath (idpath a)) :
  sesqui_top p q = EL q p.
Proof.
  srapply F.
  all: symmetry.
  - exact (EH_natL_sqConcatV p).
  - exact (EH_natR_sqConcatV q).
Defined. *)

Local Definition DR_eq_ER {X} {a : X} (p q : idpath (idpath a) = idpath (idpath a)) :
  DR p q = ER p q.
Proof.
  srapply F.
  all: symmetry.
  - exact (EH_natR_sqConcatV q).
  - exact (EH_natL_sqConcatV p).
Defined.

Local Definition T {X} {a : X} (p q : idpath (idpath a) = idpath (idpath a)) :
  EL p q @ whiskerL 1 (wlrnat p q)^ = whiskerR (wlrnat q p) 1 @ ER p q.
Proof.
  refine (whiskerR (DL_eq_EL p q)^ _ @ _).
  refine (_ @ whiskerL _ (DR_eq_ER p q)).
  exact (S p q).
Defined.

Local Definition H {X} {a b : X} {a0 a1 a2 a3 a4 a5 : a = b}
  {a10 : a1 = a0} {a12 : a1 = a2} {a23 : a2 = a3}
  {a43 : a4 = a3} {a45 : a4 = a5} {a50 : a5 = a0} :
  rightSqueeze^-1 (a10 @ a50^) @ whiskerL 1 a45^ = whiskerR a12 1 @ rightSqueeze^-1 (a23 @ a43^) ->
  a10^ @ (a12 @ a23) = (a43^ @ (a45 @ a50))^.
Proof.
  induction a45; induction a43; induction a23; induction a12; induction a50; induction a1.
  cbn; hott_simpl.
  srapply ap.
Defined.

Definition syllepsis {X} {a : X} (p q : idpath (idpath a) = idpath _)
  : EH p q = (EH q p)^.
Proof.
  snrapply H.
  snrapply T.
Defined.