From HoTT Require Import Basics Types.
Require Import Syllepsis.

(* We now prove the hexagon equations for Eckmann-Hilton (aka "coherence #1"). *)

(* Three paths form a triangle if they form a triangle. *)
Definition Triangle {X} {a b c : X} (p : a = c) (q : b = a) (r : b = c) :=
  q^ @ r = p.

(* We have three occurrences of wlrnat in the hexagon equations: wlrnat p q, wlrnat p r, wlrnat p (q @ r). These must together form an octagon. *)
Section Octagon.

  Context {X : Type}.

  (* 0-paths *)
  Context {a0 a1 a2 b0 b1 b2 : X}.

  (* 1-paths *)
  Context {wlx0 : a0 = b0}.
  Context {wlx1 : a1 = b1}.
  Context {wlx2 : a2 = b2}.

  Context {wry0 : b0 = b1}.
  Context {wry1 : a0 = a1}.

  Context {wrz0 : b1 = b2}.
  Context {wrz1 : a1 = a2}.

  Context {wryz0 : b0 = b2}.
  Context {wryz1 : a0 = a2}.

  (* 2-paths *)
  Variable wryz0_wry0_wrz0 : wry0 @ wrz0 = wryz0.
  Variable wryz1_wry1_wrz1 : wry1 @ wrz1 = wryz1.

  Variable wlrnat_x_y : wlx0 @ wry0 = wry1 @ wlx1.
  Variable wlrnat_x_z : wlx1 @ wrz0 = wrz1 @ wlx2.
  Variable wlrnat_x_yz : wlx0 @ wryz0 = wryz1 @ wlx2. 

  Definition Octagon :=
    wlrnat_x_yz = whiskerL wlx0 wryz0_wry0_wrz0^ @
                  concat_p_pp wlx0 wry0 wrz0 @
                  whiskerR wlrnat_x_y wrz0 @
                  concat_pp_p wry1 wlx1 wrz0 @
                  whiskerL wry1 wlrnat_x_z @
                  concat_p_pp wry1 wrz1 wlx2 @
                  whiskerR wryz1_wry1_wrz1 wlx2.

End Octagon.

(* The commutativity of the hexagon abstractly. *)
Section Hexagon.

  Context {X : Type}.

  (* 0-paths *)
  Context {a0 a1 a2 b0 b1 b2 : X}.

  (* 1-paths *)
  Context {wlx0 x0 : a0 = b0}.
  Context {wlx1 x1 : a1 = b1}.
  Context {wlx2 x2 : a2 = b2}.

  Context {wry0 y0 : b0 = b1}.
  Context {wry1 y1 : a0 = a1}.

  Context {wrz0 z0 : b1 = b2}.
  Context {wrz1 z1 : a1 = a2}.

  Context {wryz0 : b0 = b2}.
  Context {wryz1 : a0 = a2}.

  (* 2-paths *)
  Context {wlx0_x0 : wlx0 = x0}.
  Context {wlx1_x1 : wlx1 = x1}.
  Context {wlx2_x2 : wlx2 = x2}.

  Context {wry0_y0 : wry0 = y0}.
  Context {wry1_y1 : wry1 = y1}.

  Context {wrz0_z0 : wrz0 = z0}.
  Context {wrz1_z1 : wrz1 = z1}.

  Context {wryz0_yz0 : wryz0 = y0 @ z0}.
  Context {wryz1_yz1 : wryz1 = y1 @ z1}.

  Context {wryz0_wry0_wrz0 : wry0 @ wrz0 = wryz0}.
  Context {wryz1_wry1_wrz1 : wry1 @ wrz1 = wryz1}.

  Context {wlrnat_x_y : wlx0 @ wry0 = wry1 @ wlx1}.
  Context {wlrnat_x_z : wlx1 @ wrz0 = wrz1 @ wlx2}.
  Context {wlrnat_x_yz : wlx0 @ wryz0 = wryz1 @ wlx2}.

  (* 3-paths *)
  Hypothesis tr0 : Triangle wryz0_yz0 wryz0_wry0_wrz0 (wry0_y0 @@ wrz0_z0).
  Hypothesis tr1 : Triangle wryz1_yz1 wryz1_wry1_wrz1 (wry1_y1 @@ wrz1_z1).
  Hypothesis oct : Octagon wryz0_wry0_wrz0 wryz1_wry1_wrz1 wlrnat_x_y wlrnat_x_z wlrnat_x_yz.

  Definition hexagon :
    let EH_x_y := (wlx0_x0 @@ wry0_y0)^ @ wlrnat_x_y @ (wry1_y1 @@ wlx1_x1) in
    let EH_x_z := (wlx1_x1 @@ wrz0_z0)^ @ wlrnat_x_z @ (wrz1_z1 @@ wlx2_x2) in
    let EH_x_yz := (wlx0_x0 @@ wryz0_yz0)^ @ wlrnat_x_yz @ (wryz1_yz1 @@ wlx2_x2) in
    EH_x_yz = concat_p_pp x0 y0 z0 @
              whiskerR EH_x_y z0 @
              concat_pp_p y1 x1 z0 @
              whiskerL y1 EH_x_z @
              concat_p_pp y1 z1 x2.
  Proof.
    unfold Triangle in tr0; induction tr0; clear tr0.
    unfold Triangle in tr1; induction tr1; clear tr1.
    unfold Octagon in oct; symmetry in oct; induction oct; clear oct.
    induction wryz0_wry0_wrz0, wryz1_wry1_wrz1.
    clear wryz0_wry0_wrz0 wryz1_wry1_wrz1. 
    induction wlx0_x0, wlx1_x1, wlx2_x2, wry0_y0, wry1_y1, wrz0_z0, wrz1_z1.
    clear wlx0_x0 wlx1_x1 wlx2_x2 wry0_y0 wry1_y1 wrz0_z0 wrz1_z1.
    induction wry0, wry1, wrz0, wrz1. 
    clear wry0 wry1 wrz0 wrz1. 
    revert wlrnat_x_y; srapply (equiv_ind rightSqueeze^-1); intro wlrnat_x_y.
    revert wlrnat_x_z; srapply (equiv_ind rightSqueeze^-1); intro wlrnat_x_z.
    induction wlrnat_x_y, wlrnat_x_z.
    clear wlrnat_x_y wlrnat_x_z.
    induction wlx0; clear wlx0.
    reflexivity.
  Defined.

End Hexagon.

(* It now suffices to prove that the triangles and the octagon commute in our particular case. *)

(* the generalized triangle *)
Local Definition triangle {X} {a b : X} {u v w : a = b} (p : u = v) (q : v = w) :
  Triangle (urnat (p @ q))
           (whiskerR (whiskerR_pp 1 p q)^ (concat_p1 w))
           ((urnat p) [-] (urnat q)).
Proof.
  by induction p, q, u.
Defined.

(* getting rid of reflexivites in the generalized triangle *)
Section TrianglePushDown.

  Context {X : Type}.

  (* 0-paths *)
  Context {a b c : X}.

  (* 1-paths *)
  Context {p0 p1 : a = b} {q0 q1 : b = c} {pq0 : a = c}.

  (* 2-paths *)
  Variable p01 : p0 @ 1 = 1 @ p1.
  Variable q01 : q0 @ 1 = 1 @ q1.

  Variable pq0_pq0 : p0 @ q0 = pq0.
  Variable pq0_pq1 : pq0 @ 1 = 1 @ (p1 @ q1).

  (* 3-paths *)
  Hypothesis tr : Triangle pq0_pq1 (whiskerR pq0_pq0 1) (p01 [-] q01).
 
  Local Definition triangle_rightSqueeze :
    Triangle (rightSqueeze pq0_pq1) pq0_pq0 (rightSqueeze p01 @@ rightSqueeze q01).
  Proof.
    unfold Triangle in tr; induction tr; clear tr.
    induction pq0_pq0; clear pq0_pq0.
    revert p01; srapply (equiv_ind rightSqueeze^-1); intro p01.
    revert q01; srapply (equiv_ind rightSqueeze^-1); intro q01.
    induction p01, q01; clear p01 q01.
    by induction p0, q0.
  Defined.

End TrianglePushDown.

(* the generalized octagon *)
Definition octagon {X} {a b c : X} {x y z : a = b} {u v : b = c} (p : u = v) (q : x = y) (r : y = z) :
  Octagon (whiskerR_pp v q r)^ (whiskerR_pp u q r)^ 
          (wlrnat q p) (wlrnat r p) (wlrnat (q @ r) p).
Proof.
  by induction p, q, r, x, u.
Defined.

(* the coherence *)
Theorem EH_hexagon_coherence {X} {a : X} (p q r : idpath a = idpath a) :
  EH p (q @ r) = concat_p_pp p q r @
                 whiskerR (EH p q) r @
                 concat_pp_p q p r @
                 whiskerL q (EH p r) @
                 concat_p_pp q r p.
Proof.
  rapply hexagon.
  - apply triangle_rightSqueeze.
    exact (triangle q r).
  - apply triangle_rightSqueeze.
    exact (triangle q r).
  - exact (octagon p q r).
Defined.