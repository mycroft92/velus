From Coq Require Import BinPos List.

From Velus Require Import Common Ident Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LSemantics Lustre.LOrdered.
From Velus Require Import Lustre.Denot.Cpo Lustre.Denot.SD.

Close Scope equiv_scope. (* conflicting notation "==" *)
Import ListNotations.

Require Import CommonList2 SDfuns EraseAbs.

(** * TEST : une sémantique Kahnienne pour Lustre *)
Module Type LKAHN
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Import Sd    : SD            Ids Op OpAux Cks Senv Syn Lord).


(* filter booléen, plus pratique ? *)
Section FilterB.

  Context {D : Type}.
  Variable P : D -> bool.

  Definition filterb : DS D -C-> DS D.
    refine (@FILTER D (fun x => eq_true (P x)) _).
    intros x; destruct (P x); trivial.
    left. constructor.
    right. intro H. inversion H.
  Defined.

  Lemma filterb_bot : filterb 0 == 0.
  Proof.
    apply filter_bot.
  Qed.

  Lemma filterb_eq_cons : forall a s,
      filterb (cons a s) == if P a then cons a (filterb s) else filterb s.
  Proof.
    intros.
    unfold filterb.
    rewrite FILTER_filter.
    rewrite filter_eq_cons.
    destruct (P a); auto.
  Qed.

End FilterB.



Inductive error' :=
| error_Ty'
| error_Op'
.

(* valeur de Kahn: potentiellement erronée *)
Inductive errv (A : Type) : Type :=
| val (a: A)
| err' (e : error').

Arguments val {A} a.
Arguments err' {A} e.

(* un ea qui change le type *)
Section EA.

(* efface les absences *)
Definition ea {A : Type} : DS (sampl A) -C-> DS (errv A).
  refine (MAP (fun (x:sampl A) => match x with
                     | pres v => val v
                     | err error_Ty => err' error_Ty'
                     | err error_Op => err' error_Op'
                     | abs | err error_Cl => err' error_Ty'
                     end)
            @_ filterb (fun v => match v with abs => false | _ => true end)).
Defined.

Lemma ea_cons :
  forall A (x : sampl A) xs,
    ea (cons x xs)
    == match x with
       | abs => ea xs
       | pres v => cons (val v) (ea xs)
       | err error_Ty => cons (err' error_Ty') (ea xs)
       | err error_Op => cons (err' error_Op') (ea xs)
       | err error_Cl => cons (err' error_Ty') (ea xs)
       end.
Proof.
  intros.
  unfold ea at 1.
  rewrite fcont_comp_simpl, MAP_map, filterb_eq_cons.
  destruct x; auto; rewrite map_eq_cons; auto.
  destruct e; auto.
Qed.

End EA.

Section KWHEN.

  Context {A B : Type}.

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
  Definition kwhen (k : enumtag) : DS (errv A) -C-> DS (errv B) -C-> DS (errv A) :=
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

  Lemma ea_is_cons :
  forall A (xs : DS (sampl A)),
    is_cons (ea xs) ->
    isConP (fun v => v <> abs) xs.
Proof.
  unfold ea, filterb.
  intros * Hc.
  apply map_is_cons in Hc.
  apply filter_is_cons in Hc.
  induction Hc; auto.
  - apply isConPnP; auto.
    intro; subst; cases; now apply H.
  - apply isConPP.
    cases; congruence.
Qed.

  Definition swhen := @swhen A B enumtag tag_of_val tag_eqb.
  Lemma erase_swhen :
    forall k xs cs,
      safe_DS (swhen k xs cs) ->
      ea (swhen k xs cs) == kwhen k (ea xs) (ea cs).
  Proof.
    intros.
    eapply DS_bisimulation_allin1 with
      (R := fun U V => exists xs cs,
                safe_DS (swhen k xs cs)
                /\ U == ea (swhen k xs cs)
                /\ V == kwhen k (ea xs) (ea cs)).
    3:eauto.
    intros * ? Eq1 Eq2; setoid_rewrite <- Eq1; setoid_rewrite <- Eq2; eauto.
    clear.
    intros U V Hc (xs & cs & Hs & Hu & Hv).
    destruct Hc as [Hc | Hc].
    {
      rewrite Hu in Hc.
      apply ea_is_cons in Hc as Hcp.
      remember_ds (swhen k xs cs) as rs.
      revert dependent xs.
      revert dependent cs.
      revert dependent U.
      revert dependent V.
      induction Hcp; intros.
      { rewrite <- eqEps in *; eauto 2. }
      - assert (a = abs); subst.
        { inv Hs. cases. contradict H. congruence. }
        destruct (@is_cons_elim _ xs) as (x & xs' & Hxs).
        { eapply proj1, zip_is_cons.
          unfold swhen, SDfuns.swhen in Hrs.
          rewrite <- Hrs; auto. }
        destruct (@is_cons_elim _ cs) as (c & cs' & Hcs).
        { eapply proj2, zip_is_cons.
          unfold swhen, SDfuns.swhen in Hrs.
          rewrite <- Hrs; auto. }
        rewrite Hxs, Hcs, 2 ea_cons in *.
        unfold swhen in *.
        rewrite swhen_eq in Hrs.
        apply Con_eq_simpl in Hrs as [].
        inv Hs; cases_eqn HH; subst; try congruence.
        eapply IHHcp; eauto.
        eapply IHHcp; auto. eauto.
  - destruct (@is_cons_elim _ xs) as (x & xs' & Hxs).
    { eapply proj1, sbinop_is_cons; rewrite <- Hrs; auto. }
    destruct (@is_cons_elim _ ys) as (y & ys' & Hys).
    { eapply proj2, sbinop_is_cons; rewrite <- Hrs; auto. }
    rewrite Hxs, Hys, 3 ea_cons in *.
    rewrite sbinop_eq in *.
    apply Con_eq_simpl in Hrs as [? Hrs].
    inv Hs.
    destruct x, y; try tauto.
    rewrite sbinop_eq, Hrs in *.
    cases_eqn HH; inv HH.
    rewrite 2 first_cons; split; auto.
    setoid_rewrite Hv.
    setoid_rewrite Hu.
    setoid_rewrite Hrs.
    rewrite 2 rem_cons; eauto.




  Qed.

End KWHEN.

Lemma erase_swhen :
  forall A B C (op:A->B->option C) xs ys,
    safe_DS (swhen op xs ys) ->
    ea (sbinop op xs ys) <= sbinop op (ea xs) (ea ys).
Proof.




Section KDenot_node.

Context {PSyn : list decl -> block -> Prop}.
Context {Prefs : PS.t}.
Variable (G : @global PSyn Prefs).

Section KDenot_exps.

  Hypothesis kdenot_exp_ :
    forall e : exp,
      Dprod (Dprod (Dprodi FI) (DS_prod SI)) (DS_prod SI) -C->
      @nprod (DS (sampl value)) (numstreams e).

  Definition kdenot_exps_ (es : list exp) :
    Dprod (Dprod (Dprodi FI) (DS_prod SI)) (DS_prod SI) -C->
    @nprod (DS (sampl value)) (list_sum (List.map numstreams es)).
    induction es as [|a].
    + exact 0.
    + exact ((nprod_app @2_ (kdenot_exp_ a)) IHes).
  Defined.

  Definition kdenot_expss_ {A} (ess : list (A * list exp)) (n : nat) :
    Dprod (Dprod (Dprodi FI) (DS_prod SI)) (DS_prod SI) -C->
    @nprod (@nprod (DS (sampl value)) n) (length ess).
    induction ess as [|[? es]].
    + exact 0.
    + destruct (Nat.eq_dec (list_sum (List.map numstreams es)) n) as [<-|].
      * exact ((nprod_cons @2_ (kdenot_exps_ es)) IHess).
      * exact 0.
  Defined.

End KDenot_exps.





Definition kdenot_exp_ (ins : list ident)
  (e : exp) :
  (* (nodes * inputs * env) -> streams *)
  Dprod (Dprod (Dprodi FI) (DS_prod SI)) (DS_prod SI) -C->
  @nprod (DS (sampl value)) (numstreams e).

  set (ctx := Dprod _ _).
  epose (denot_var :=
       fun x => if mem_ident x ins
             then PROJ (DS_fam SI) x @_ SND _ _ @_ FST _ _
             else PROJ (DS_fam SI) x @_ SND _ _).
  revert e.
  fix denot_exp_ 1.
  intro e.
  destruct e eqn:He; simpl (nprod _).
  - (* Econst *)
    (* véritable const, pas d'horloge dans le modèle de Kahn *)
    exact (CTE _ _ (DS_const (pres (Vscalar (sem_cconst c))))).
  - (* Eenum *)
    exact (CTE _ _ (DS_const (pres (Venum e0)))).
  - (* Evar *)
    exact (denot_var i).
  - (* Elast *)
    apply CTE, 0.
  - (* Eunop *)

TODO.
 


    eapply fcont_comp. 2: apply (denot_exp_ e0).
    destruct (numstreams e0) as [|[]].
    (* pas le bon nombre de flots: *)
    1,3: apply CTE, errTy.
    destruct (typeof e0) as [|ty []].
    1,3: apply CTE, errTy.
    exact (sunop (fun v => sem_unop u v ty)).
  - (* Ebinop *)
    eapply fcont_comp2.
    3: apply (denot_exp_ e0_2).
    2: apply (denot_exp_ e0_1).
    destruct (numstreams e0_1) as [|[]], (numstreams e0_2) as [|[]].
    (* pas le bon nombre de flots: *)
    1-4,6-9: apply curry, CTE, errTy.
    destruct (typeof e0_1) as [|ty1 []], (typeof e0_2) as [|ty2 []].
    1-4,6-9: apply curry, CTE, errTy.
    exact (sbinop (fun v1 v2 => sem_binop b v1 ty1 v2 ty2)).
  - (* Eextcall *)
    apply CTE, 0.
  - (* Efby *)
    rename l into e0s, l0 into es, l1 into anns.
    clear He.
    pose (s0s := denot_exps_ denot_exp_ e0s).
    pose (ss := denot_exps_ denot_exp_ es).
    (* vérifier le typage *)
    destruct (Nat.eq_dec
                (list_sum (List.map numstreams es))
                (list_sum (List.map numstreams e0s))
             ) as [Heq1|].
    destruct (Nat.eq_dec
                (list_sum (List.map numstreams e0s))
                (length anns)
             ) as [Heq2|].
    (* si les tailles ne correspondent pas : *)
    2,3: apply CTE, (nprod_const _ errTy).
    rewrite Heq1 in ss.
    rewrite <- Heq2.
    exact ((lift2 (SDfuns.fby) @2_ s0s) ss).
  - (* Earrow *)
    apply CTE, 0.
  - (* Ewhen *)
    rename l into es.
    destruct l0 as (tys,ck).
    destruct p as (i,ty). clear He.
    destruct (Nat.eq_dec
                (list_sum (List.map numstreams es))
                (length tys)
             ) as [<-|].
    2: apply CTE, (nprod_const _ errTy).
    pose (ss := denot_exps_ denot_exp_ es).
    exact ((llift (swhenv e0) @2_ ss) (denot_var i)).
  - (* Emerge *)
    rename l into ies.
    destruct l0 as (tys,ck).
    destruct p as [i ty].
    (* on calcule (length tys) flots pour chaque liste de sous-expressions *)
    pose (ses := denot_expss_ denot_exp_ ies (length tys)).
    rewrite <- (map_length fst) in ses.
    exact ((lift_nprod @_ (smergev (List.map fst ies)) @2_ denot_var i) ses).
  - (* Ecase *)
    rename l into ies.
    destruct l0 as (tys,ck).
    (* on calcule (length tys) flots pour chaque liste de sous-expressions *)
    pose (ses := denot_expss_ denot_exp_ ies (length tys)).
    rewrite <- (map_length fst) in ses.
    destruct o as [d_es|].
    + (* avec une branche par défaut *)
      revert ses.
      destruct (Nat.eq_dec
                  (list_sum (List.map numstreams d_es))
                  (length tys)
               ) as [<-|].
      2: apply CTE, CTE, (nprod_const _ errTy).
      intro ses.
      refine ((_ @2_ (denot_exp_ e0)) ((nprod_cons @2_ denot_exps_ denot_exp_ d_es) ses)).
      destruct (numstreams e0) as [|[]].
      1,3: apply CTE, CTE, (nprod_const _ errTy).
      exact (lift_nprod @_ scase_defv (List.map fst ies)).
    + (* case total *)
      (* condition, branches *)
      refine ((_ @2_ (denot_exp_ e0)) ses).
      destruct (numstreams e0) as [|[]].
      1,3: apply CTE, CTE, (nprod_const _ errTy).
      exact (lift_nprod @_ (scasev (List.map fst ies))).
  - (* Eapp *)
    rename l into es, l0 into er, l1 into anns.
    clear He.
    destruct (find_node i G) as [n|].
    destruct (Nat.eq_dec (length (List.map fst n.(n_out))) (length anns)) as [<-|].
    2,3: apply CTE, (nprod_const _ errTy).
    (* dénotation du nœud *)
    pose (f := PROJ _ i @_ FST _ _ @_ FST _ _ : ctx -C-> FI i).
    pose (ss := denot_exps_ denot_exp_ es).
    pose (rs := denot_exps_ denot_exp_ er).
    (* chaînage *)
    refine
      (np_of_env (List.map fst (n_out n)) @_
         (sreset @3_ f) (sbools_of @_ rs) (env_of_np (idents (n_in n)) @_ ss)).
Defined.

Definition denot_exp (ins : list ident) (e : exp) :
  (* (nodes * inputs * env) -> streams *)
  Dprodi FI -C-> DS_prod SI -C-> DS_prod SI -C-> nprod (numstreams e) :=
  curry (curry (denot_exp_ ins e)).

Definition denot_exps (ins : list ident) (es : list exp) :
  Dprodi FI -C-> DS_prod SI -C-> DS_prod SI -C-> nprod (list_sum (List.map numstreams es)) :=
  curry (curry (denot_exps_ (denot_exp_ ins) es)).

Lemma denot_exps_eq :
  forall ins e es envG envI env,
    denot_exps ins (e :: es) envG envI env
    = nprod_app (denot_exp ins e envG envI env) (denot_exps ins es envG envI env).
Proof.
  reflexivity.
Qed.
