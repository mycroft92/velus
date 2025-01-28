From Coq Require Import BinPos List.
Import List ListNotations.
From Velus Require Import CommonTactics Common.Common.
From Velus Require Import Lustre.Denot.Cpo.
From Velus Require Import Lustre.Denot.CommonList2.

(* TODO: move *)
  (* mettre à jour la k-ième valeur d'un vecteur *)
  Fixpoint lift_at {D} (F : D-C->D) (k:nat) {n} : @nprod D n -C-> @nprod D n :=
    match n with
    | O => ID _
    | S n => match k with
          | O => (* on y est *)
              ((nprod_cons @2_ F @_ nprod_hd) nprod_tl)
          | S k => ((nprod_cons @2_ nprod_hd) (lift_at F k @_ nprod_tl))
          end
    end.

  Lemma nth_lift_at_upd :
    forall D n k f np d,
      k < n ->
      get_nth k d (@lift_at D f k n np) == f (get_nth k d np).
  Proof.
    induction n; intros * Hk.
    - inv Hk.
    - destruct k; simpl.
      + autorewrite with cpodb.
        now setoid_rewrite nprod_hd_cons.
      + setoid_rewrite <- IHn; auto with arith.
        destruct n; auto; lia.
  Qed.

  Lemma nth_lift_at :
    forall D n k f np d m,
      k <> m ->
      get_nth m d (@lift_at D f k n np) == get_nth m d np.
  Proof.
    induction n; intros * Hkm.
    - apply fcont_stable.
      destruct k; auto.
    - destruct k; simpl.
      + destruct m; try lia.
        setoid_rewrite get_nth_tl.
        destruct n,m; auto.
      + destruct m; simpl; auto.
        * now setoid_rewrite nprod_hd_cons.
        * autorewrite with cpodb.
          rewrite <- (IHn k f (nprod_tl np) d m); auto.
          destruct n,m; auto.
  Qed.
(* /TODO: move *)



(** * Streams operations for the Lustre Kahnian semantics *)

Inductive error' :=
| error_Ty'
| error_Op'
.

(* value in the Kahn model : potentially erroneous *)
Inductive errv (A : Type) : Type :=
| val (a: A)
| err' (e : error').

Arguments val {A} a.
Arguments err' {A} e.

(* réécritures nécessaires dans ce fichier, cpodb est trop lourde... *)
Local Hint Rewrite
     ford_fcont_shift_simpl
     curry_Curry
     Curry_simpl
     fcont_comp_simpl
     fcont_comp2_simpl
     fcont_comp3_simpl
     fcont_comp4_simpl
     SND_simpl Snd_simpl
     FST_simpl Fst_simpl
     DSCASE_simpl
     DScase_cons
     @zip_cons
  : localdb.

Section Kunop_binop.

  Context {A B D : Type}.

    Definition kunop (uop : A -> option B) : DS (errv A) -C-> DS (errv B) :=
    MAP (fun x => match x with
               | val v =>
                   match uop v with
                   | Some y => val y
                   | None => err' error_Op'
                   end
               | err' e => err' e
               end).

  Lemma kunop_eq : forall uop u U,
      kunop uop (cons u U)
      == cons match u with
           | val u => match uop u with
                      | Some v => val v
                      | None => err' error_Op'
                      end
           | err' e => err' e
           end (kunop uop U).
  Proof.
    intros.
    unfold kunop.
    rewrite MAP_map, map_eq_cons.
    destruct u; auto.
  Qed.

  Definition kbinop (bop : A -> B -> option D) :
    DS (errv A) -C-> DS (errv B) -C-> DS (errv D) :=
    ZIP (fun va vb =>
           match va, vb with
           | val a, val b =>
               match bop a b with
               | Some v => val v
               | None => err' error_Op'
               end
           | err' e, _ => err' e
           | _, err' e => err' e
           end).

  Lemma kbinop_eq : forall bop u U v V,
      kbinop bop (cons u U) (cons v V)
      == cons match u, v with
           | val a, val b =>
               match bop a b with
               | Some v => val v
               | None => err' error_Op'
               end
           | err' e, _ => err' e
           | _, err' e => err' e
        end (kbinop bop U V).
  Proof.
    intros.
    unfold kbinop.
    now rewrite zip_cons.
  Qed.

  Lemma kbinop_is_cons : forall bop U V,
      is_cons (kbinop bop U V) ->
      is_cons U /\ is_cons V.
  Proof.
    unfold kbinop; intros *.
    now apply zip_is_cons.
  Qed.

End Kunop_binop.


Section Kfunctions.

Context {A B : Type}.

Section Kwhen_merge_case.

  Variable enumtag : Type.
  Variable tag_of_val : B -> option enumtag.
  Variable tag_eqb : enumtag -> enumtag -> bool.

  Hypothesis tag_eqb_eq : forall t1 t2, tag_eqb t1 t2 = true <-> t1 = t2.

  Lemma tag_eqb_refl : forall t, tag_eqb t t = true.
  Proof. intro; now apply tag_eqb_eq. Qed.

  Lemma tag_eqb_neq : forall t1 t2, tag_eqb t1 t2 = false <-> t1 <> t2.
  Proof.
    intros.
    destruct (tag_eqb _ _) eqn:HH.
    - firstorder; congruence.
    - firstorder; intros HHH%tag_eqb_eq; congruence.
  Qed.

  Lemma tag_eq_dec : forall x y : enumtag, { x = y } + { x <> y }.
  Proof.
    intros x y.
    destruct (tag_eqb x y) eqn:Heq.
    - apply tag_eqb_eq in Heq; auto.
    - apply tag_eqb_neq in Heq; auto.
  Qed.


  Definition kwhenf (k : enumtag) :
    (DS (errv A) -C-> DS (errv B) -C-> DS (errv A)) -C-> DS (errv A) -C-> DS (errv B) -C-> DS (errv A).
    apply curry, curry.
    eapply (fcont_comp2 (DSCASE _ _ )).
    2:exact (SND _ _ @_ (FST _ _)).
    apply ford_fcont_shift.
    intro x.
    apply curry.
    eapply (fcont_comp2 (DSCASE _ _)).
    2:exact (SND _ _ @_ (FST _ _)).
    apply ford_fcont_shift.
    intro c.
    apply curry.
    refine
      (match x, c with
         | val x, val c =>
             match tag_of_val c with
             | None =>
                 CTE _ _ (cons (err' error_Ty') 0)
             | Some t =>
                 if tag_eqb k t
                 then
                   (CONS (val x) @_ ((AP _ _ @3_ FST _ _ @_ FST _ _ @_ FST _ _ @_ FST _ _) (SND _ _ @_ FST _ _) (SND _ _)))
                 else
                   ((AP _ _ @3_ FST _ _ @_ FST _ _ @_ FST _ _ @_ FST _ _) (SND _ _ @_ FST _ _) (SND _ _))
             end
       | err' e, _ | _, err' e => (CTE _ _ (cons (err' e) 0))
       end).
  Defined.

  Lemma kwhenf_eq : forall F k c C x X,
      kwhenf k F (cons x X) (cons c C)
      == match x, c with
         | val x, val c =>
             match tag_of_val c with
             | None => cons (err' error_Ty') 0
             | Some t =>
                 if tag_eqb k t
                 then cons (val x) (F X C)
                 else F X C
             end
         | err' e, _ | _, err' e => cons (err' e) 0
         end.
  Proof.
    intros.
    unfold kwhenf.
    repeat (rewrite curry_Curry, Curry_simpl).
    setoid_rewrite fcont_comp_simpl.
    change (fcontit ?a ?b) with (a b).
    repeat rewrite ?fcont_comp_simpl, ?fcont_comp2_simpl.
    setoid_rewrite ford_fcont_shift_simpl.
    rewrite SND_simpl, FST_simpl.
    simpl.
    rewrite DSCASE_simpl, DScase_cons.
    change (fcontit ?a ?b) with (a b).
    repeat (rewrite curry_Curry, Curry_simpl).
    setoid_rewrite fcont_comp_simpl.
    change (fcontit ?a ?b) with (a b).
    repeat rewrite ?fcont_comp_simpl, ?fcont_comp2_simpl.
    setoid_rewrite ford_fcont_shift_simpl.
    rewrite SND_simpl, FST_simpl.
    cases_eqn HH; subst; try congruence.
    all: simpl; rewrite DSCASE_simpl, DScase_cons.
    all: cases_eqn HH; congruence.
  Qed.

  Lemma kwhenf_is_cons :
    forall k F xs cs, is_cons (kwhenf k F xs cs) -> is_cons xs /\ is_cons cs.
  Proof.
    intros * Hc.
    assert (Hcx : is_cons xs).
    { apply DScase_is_cons in Hc.
      assumption. }
    split; auto.
    apply is_cons_elim in Hcx as (?&?&Hx).
    revert Hc.
    rewrite Hx.
    unfold kwhenf.
    setoid_rewrite DSCASE_simpl.
    rewrite DScase_eq_cons; eauto.
    intros Hc%DScase_is_cons; auto.
  Qed.

  Definition  kwhen (k : enumtag) : DS (errv A) -C-> DS (errv B) -C-> DS (errv A) :=
    FIXP _ (kwhenf k).

  Lemma kwhen_eq : forall k c C x X,
      kwhen k (cons x X) (cons c C)
      == match x, c with
         | val x, val c =>
             match tag_of_val c with
             | None => cons (err' error_Ty') 0
             | Some t =>
                 if tag_eqb k t
                 then cons (val x) (kwhen k X C)
                 else kwhen k X C
             end
         | err' e, _ | _, err' e => cons (err' e) 0
         end.
  Proof.
    intros.
    unfold kwhen at 1.
    rewrite FIXP_eq.
    fold (kwhen k).
    now rewrite kwhenf_eq.
  Qed.

  Lemma kwhen_is_cons :
    forall k xs cs, is_cons (kwhen k xs cs) -> is_cons xs /\ is_cons cs.
  Proof.
    intros *.
    unfold kwhen.
    rewrite FIXP_eq.
    apply kwhenf_is_cons.
  Qed.

    (* pas vrai, il faut supposer (safe_DS (kwhen k xs cs)) *)
  Lemma kwhen_is_cons_cond :
    forall k xs cs,
      is_cons (kwhen k xs cs) ->
      isConP (fun c => match c with
                    | val c =>
                        match tag_of_val c with
                        | Some t => tag_eqb k t = true
                        | _ => True
                        end
                    | _ => True
                    end
        ) cs.
  Proof.
    (* intros *. *)
    unfold kwhen.
    setoid_rewrite FIXP_fixp.
    intro k.
    apply fixp_ind; auto.
    admit.
    admit.
    change (fcontit ?a ?b) with (a b).
    intros F HF xs cs Hic.
    apply kwhenf_is_cons in Hic as HH.
    destruct HH as [Hcx Hcc].
    apply is_cons_elim in Hcx as (?&?&Hx).
    apply is_cons_elim in Hcc as (?&?&Hc).
    rewrite Hx, Hc, kwhenf_eq in *.
    cases_eqn HH; subst.
    - apply isConPP; rewrite HH1; auto.
    - apply isConPnP; eauto; rewrite HH1, HH2; auto.
    - apply isConPP; rewrite HH1; auto.
  Abort.

  (* [merge] in Kahn semantics selects the branch to pull *)
  Definition kmergef (l : list enumtag) :
    (DS (errv B) -C-> @nprod (DS (errv A)) (length l) -C-> DS (errv A))
    -C->
    DS (errv B) -C-> @nprod (DS (errv A)) (length l) -C-> DS (errv A).
    apply curry, curry.
    eapply (fcont_comp2 (DSCASE _ _ )).
    2:exact (SND _ _ @_ (FST _ _)).
    apply ford_fcont_shift.
    intro c.
    apply curry.
    pose (errty' := cons (@err' A error_Ty') 0).
    refine
      match c with
        | val c =>
            match tag_of_val c with
            | Some t =>
                match CommonList2.mem_nth _ tag_eq_dec l t with
                | Some n => (APP _ @2_ get_nth n errty' @_ SND _ _ @_ FST _ _) _
                (* | Some n => app (get_nth n errty' np) (kmerge l C (lift_at (REM _) n np)) *)
                | None => CTE _ _ errty'
                end
            | None => CTE _ _ errty'
            end
        | err' e => CTE _ _ (cons (err' e) 0)
      end.
    refine ((AP _ _ @3_ FST _ _ @_ FST _ _ @_ FST _ _) (SND _ _) _).
    refine (lift_at (REM _) n @_ SND _ _ @_ FST _ _).
  Defined.

  Lemma kmergef_eq :
    forall l F c C np,
      let errty' := cons (err' error_Ty') 0 in
      kmergef l F (cons c C) np ==
        match c with
        | val c =>
            match tag_of_val c with
            | Some t =>
                match CommonList2.mem_nth _ tag_eq_dec l t with
                | Some n => app (get_nth n errty' np) (F C (lift_at (REM _) n np))
                | None => errty'
                end
            | None => errty'
            end
        | err' e => cons (err' e) 0
        end.
  Proof.
    intros.
    unfold kmergef at 1.
    setoid_rewrite DSCASE_simpl.
    setoid_rewrite DScase_cons.
    destruct c as [c|]; auto.
    repeat change (fcontit ?a ?b) with (a b).
    rewrite ford_fcont_shift_simpl.
    autorewrite with localdb.
    cases.
  Qed.

  Definition kmerge (l : list enumtag) :
    DS (errv B) -C-> @nprod (DS (errv A)) (length l) -C-> DS (errv A) :=
    FIXP _ (kmergef l).

  Lemma kmerge_eq :
    forall l c C np,
      let errty' := cons (err' error_Ty') 0 in
      kmerge l (cons c C) np ==
        match c with
        | val c =>
            match tag_of_val c with
            | Some t =>
                match CommonList2.mem_nth _ tag_eq_dec l t with
                | Some n => app (get_nth n errty' np) (kmerge l C (lift_at (REM _) n np))
                | None => errty'
                end
            | None => errty'
            end
        | err' e => cons (err' e) 0
        end.
  Proof.
    intros.
    unfold kmerge at 1.
    rewrite FIXP_eq, kmergef_eq; auto.
  Qed.


  Definition kcasef (l : list enumtag) :
    (DS (errv B) -C-> @nprod (DS (errv A)) (length l) -C-> DS (errv A))
    -C->
    DS (errv B) -C-> @nprod (DS (errv A)) (length l) -C-> DS (errv A).
    apply curry, curry.
    eapply (fcont_comp2 (DSCASE _ _ )).
    2:exact (SND _ _ @_ (FST _ _)).
    apply ford_fcont_shift.
    intro c.
    apply curry.
    pose (errty' := cons (@err' A error_Ty') 0).
    refine
      match c with
        | val c =>
            match tag_of_val c with
            | Some t =>
                match CommonList2.mem_nth _ tag_eq_dec l t with
                | Some n => (APP _ @2_ get_nth n errty' @_ SND _ _ @_ FST _ _)
                             ((AP _ _ @3_ FST _ _ @_ FST _ _ @_ FST _ _) (SND _ _)
                                (lift (REM _) @_ SND _ _ @_ FST _ _))
                (* | Some n => app (get_nth n errty' np) (F C (lift (REM _) np)) *)
                | None => CTE _ _ errty'
                end
            | None => CTE _ _ errty'
            end
        | err' e => CTE _ _ (cons (err' e) 0)
      end.
  Defined.

  Lemma kcasef_eq :
    forall l F c C np,
      let errty' := cons (err' error_Ty') 0 in
      kcasef l F (cons c C) np ==
        match c with
        | val c =>
            match tag_of_val c with
            | Some t =>
                match CommonList2.mem_nth _ tag_eq_dec l t with
                | Some n => app (get_nth n errty' np) (F C (lift (REM _) np))
                | None => errty'
                end
            | None => errty'
            end
        | err' e => cons (err' e) 0
        end.
  Proof.
    intros.
    unfold kcasef at 1.
    setoid_rewrite DSCASE_simpl.
    setoid_rewrite DScase_cons.
    destruct c as [c|]; auto.
    repeat change (fcontit ?a ?b) with (a b).
    rewrite ford_fcont_shift_simpl.
    autorewrite with localdb.
    cases.
  Qed.

  Definition kcase (l : list enumtag) :
    DS (errv B) -C-> @nprod (DS (errv A)) (length l) -C-> DS (errv A) :=
    FIXP _ (kcasef l).

  Lemma kcase_eq :
    forall l c C np,
      let errty' := cons (err' error_Ty') 0 in
      kcase l (cons c C) np ==
        match c with
        | val c =>
            match tag_of_val c with
            | Some t =>
                match CommonList2.mem_nth _ tag_eq_dec l t with
                | Some n => app (get_nth n errty' np) (kcase l C (lift (REM _) np))
                | None => errty'
                end
            | None => errty'
            end
        | err' e => cons (err' e) 0
        end.
  Proof.
    intros.
    unfold kcase at 1.
    rewrite FIXP_eq, kcasef_eq; auto.
  Qed.


  (** *** case with default branch *)
  Definition kcase_deff (l : list enumtag) :
    (* condition -> default -> branches -> result *)
    (DS (errv B) -C-> DS (errv A) -C-> @nprod (DS (errv A)) (length l) -C-> DS (errv A))
    -C->
    (DS (errv B) -C-> DS (errv A) -C-> @nprod (DS (errv A)) (length l) -C-> DS (errv A)).
    apply curry, curry,curry.
    eapply (fcont_comp2 (DSCASE _ _ )).
    2:exact (SND _ _ @_ FST _ _ @_ FST _ _).
    apply ford_fcont_shift.
    intro c.
    apply curry.
    pose (errty' := cons (@err' A error_Ty') 0).
    refine
      match c with
        | val c =>
            match tag_of_val c with
            | Some t =>
                match CommonList2.mem_nth _ tag_eq_dec l t with
                (* | Some n => app (get_nth n errty' np) (F C (rem D) (lift (REM _) np)) *)
                | Some n =>
                    ((APP _ @2_ get_nth n errty' @_ SND _ _ @_ FST _ _) _)
                (* | None => app D (F C (rem D) (lift (REM _) np)) *)
                | None =>
                    (APP _ @2_ SND _ _ @_ FST _ _ @_ FST _ _) _
                end
            | None => CTE _ _ errty'
            end
        | err' e => CTE _ _ (cons (err' e) 0)
      end.
    all: refine
      ((AP _ _ @4_ FST _ _ @_ FST _ _ @_ FST _ _ @_ FST _ _)
         (SND _ _)
         (REM _ @_ SND _ _ @_ FST _ _ @_ FST _ _)
         (lift (REM _) @_ SND _ _ @_ FST _ _)
      ).
  Defined.

  Lemma kcase_deff_eq :
    forall l F c C D np,
      let errty' := cons (err' error_Ty') 0 in
      kcase_deff l F (cons c C) D np ==
        match c with
        | val c =>
            match tag_of_val c with
            | Some t =>
                match CommonList2.mem_nth _ tag_eq_dec l t with
                | Some n => app (get_nth n errty' np) (F C (rem D) (lift (REM _) np))
                | None => app D (F C (rem D) (lift (REM _) np))
                end
            | None => errty'
            end
        | err' e => cons (err' e) 0
        end.
  Proof.
    intros.
    unfold kcase_deff at 1.
    setoid_rewrite DSCASE_simpl.
    setoid_rewrite DScase_cons.
    destruct c as [c|]; auto.
    repeat change (fcontit ?a ?b) with (a b).
    rewrite ford_fcont_shift_simpl.
    autorewrite with localdb.
    cases.
  Qed.

  Definition kcase_def_ (l : list enumtag) :
    (* condition -> default -> branches -> result *)
    DS (errv B) -C-> DS (errv A) -C-> @nprod (DS (errv A)) (length l) -C-> DS (errv A) :=
    FIXP _ (kcase_deff l).

  Lemma kcase_def__eq :
    forall l c C D np,
      let errty' := cons (err' error_Ty') 0 in
      kcase_def_ l (cons c C) D np ==
        match c with
        | val c =>
            match tag_of_val c with
            | Some t =>
                match CommonList2.mem_nth _ tag_eq_dec l t with
                | Some n => app (get_nth n errty' np) (kcase_def_ l C (rem D) (lift (REM _) np))
                | None => app D (kcase_def_ l C (rem D) (lift (REM _) np))
                end
            | None => errty'
            end
        | err' e => cons (err' e) 0
        end.
  Proof.
    intros.
    unfold kcase_def_ at 1.
    rewrite FIXP_eq, kcase_deff_eq; auto.
  Qed.

  (* wrapper for [kcase_def_] that permits its usage with functions
     like [lift_nprod] (we load the 2nd argument) *)
  Definition kcase_def (l : list enumtag) :
    DS (errv B) -C-> @nprod (DS (errv A)) (S (length l)) -C-> DS (errv A).
    apply curry.
    refine ((kcase_def_ l @3_ FST _ _) _ _).
    - exact (nprod_hd @_ SND _ _).
    - exact (nprod_tl @_ SND _ _).
  Defined.

  Lemma kcase_def_eq :
    forall l cs ds np,
      l <> [] ->
      kcase_def l cs (nprod_cons ds np) = kcase_def_ l cs ds np.
  Proof.
    intros.
    unfold kcase_def.
    autorewrite with localdb.
    simpl.
    destruct l; auto; congruence.
  Qed.

End Kwhen_merge_case.

End Kfunctions.
