From Coq Require Import BinPos List.

From Velus Require Import Common Ident Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LSemantics Lustre.LOrdered.
From Velus Require Import Lustre.Denot.Cpo Lustre.Denot.SD.
From Velus.Lustre.Denot.Cpo Require Import Cpo_streams_type.

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

  Definition swhen := @swhen A B enumtag tag_of_val tag_eqb.

  (* ce côté-là est ok.
     L'autre sens est pénible car nécessite de raisonner
     avec [isConP] sur kwhen etc.
   *)
  Lemma erase_swhen_le1 :
    forall k xs cs,
      safe_DS (swhen k xs cs) ->
      ea (swhen k xs cs) <= kwhen k (ea xs) (ea cs).
  Proof.
    intros.
    apply DSle_rec_eq2 with
      (R := fun U V => exists xs cs,
                safe_DS (swhen k xs cs)
                /\ U == ea (swhen k xs cs)
                /\ V == kwhen k (ea xs) (ea cs)).
    3:eauto.
    intros * ? Eq1 Eq2; setoid_rewrite <- Eq1; setoid_rewrite <- Eq2; eauto.
    clear.
    intros U V Hc (xs & cs & Hs & Hu & Hv).
    rewrite Hu in Hc.
    apply ea_is_cons in Hc as Hcp.
    remember_ds (swhen k xs cs) as rs.
    revert dependent xs.
    revert dependent cs.
    revert dependent U.
    revert dependent V.
    induction Hcp; intros.
    - rewrite <- eqEps in *; eauto 2.
    - (* absent *)
      assert (a = abs); subst.
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
      inv Hs.
      destruct x,c; try congruence.
      + eapply IHHcp; eauto.
      + rewrite kwhen_eq in Hv.
        cases; try congruence.
        eapply IHHcp; eauto.
    - (* non absent *)
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
      inv Hs.
      cases_eqn HH; subst; try congruence.
      inv HH.
      rewrite kwhen_eq in Hv.
      rewrite HH2, HH3, H1 in *.
      rewrite Hu, Hv, 2 first_cons.
      split; auto.
      exists xs', cs'.
      rewrite Hu, Hv, 2 rem_cons; auto.
  Qed.

  (** ** le Merge *)


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

  (* (* @smerge value value enumtag get_tag Nat.eqb. *) *)
  (* Variable mem_nth : list enumtag -> enumtag -> option nat. *)

  (* le merge de kahn sélectionne la branche dans laquelle lire *)
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
    autorewrite with cpodb.
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

  Definition smerge := @smerge A B enumtag tag_of_val tag_eqb.

  (* TODO: move *)
  Lemma lift_ea_abs :
        forall I A (l:list I) (np : nprod (length l)) Hnp,
          l <> [] ->
          Forall (fun '(_, x) => x = abs) (combine l (nprod_hds np Hnp)) ->
          lift ea np == lift (@ea A @_ REM _) np.
      Proof.
        induction l as [|i l]; intros * Hl Hf; try congruence.
        inv Hf.
        unfold projT1 in H1.
        cases; subst.
        destruct s as (xx & Hxx%decomp_eqCon).
        rewrite 2 (nprod_hd_tl np).
        setoid_rewrite lift_cons.
        rewrite Hxx.
              autorewrite with cpodb.
      rewrite nprod_hd_cons, rem_cons, ea_cons.
      apply nprod_cons_Oeq_compat; auto.
      destruct l as [|j l].
      + simpl.
        autorewrite with cpodb.
        rewrite ea_cons; auto.
      + assert (j :: l <> []) as Hll by congruence.
        eauto.
      Qed.

  (* TODO: move *)
      Lemma hds_nth :
        forall A n np Hc k d d' v,
          k < n ->
          nth k (@nprod_hds A n np Hc) d = v ->
          get_nth k d' np == cons v (rem (get_nth k d' np)).
      Proof.
        induction n; intros * Hk Hnth; try lia.
        destruct k; subst.
        + simpl. 
          unfold projT1.
          destruct (uncons _) as (?&?& HH%decomp_eqCon).
          rewrite HH, rem_cons; auto.
        + eapply IHn; simpl; auto with arith.
      Qed.
  (* TODO: move *)
      Lemma NoDup_nth_neq :
          forall A (l:list A) i j d,
            NoDup l ->
            i < length l ->
            j < length l ->
            i <> j ->
            nth i l d <> nth j l d.
        Proof.
          clear.
          induction l; simpl; intros; cases_eqn HH; subst; try congruence; try intro; try lia.
          all: subst; inv H; eauto.
          - apply H5, nth_In ;auto with arith.
          - apply H5, nth_In ;auto with arith.
          - eapply IHl in H3; auto with arith.
        Qed.


  Lemma erase_smerge_le1 :
    forall l cs np,
      l <> [] ->
      NoDup l ->
      safe_DS (smerge l cs np) ->
      ea (smerge l cs np) <= kmerge l (ea cs) (lift ea np).
  Proof.
    intros * Hl Nd Hs.
    apply DSle_rec_eq2 with
      (R := fun U V => exists cs np,
                safe_DS (smerge l cs np)
                /\ U == ea (smerge l cs np)
                /\ V == kmerge l (ea cs) (lift ea np)).
    3:eauto.
    intros * ? Eq1 Eq2; setoid_rewrite <- Eq1; setoid_rewrite <- Eq2; eauto.
    clear Hs np cs.
    intros U V Hc (cs & np & Hs & Hu & Hv).
    rewrite Hu in Hc.
    apply ea_is_cons in Hc as Hcp.
    remember_ds (smerge l cs np) as rs.
    revert dependent cs.
    revert dependent np.
    revert dependent U.
    revert dependent V.
    induction Hcp; intros.
    - rewrite <- eqEps in *; eauto 2.
    - (* absent *)
      assert (a = abs); subst.
      { inv Hs. cases. contradict H. congruence. }
      apply symmetry in Hrs as Hcc.
      apply cons_is_cons, smerge_is_cons in Hcc as [Hcc Hcnp]; auto.
      apply is_cons_elim in Hcc as (c & cs' & Hcs).
      rewrite Hcs, ea_cons in *.
      unfold smerge in *.
      unshelve rewrite smerge_cons in Hrs.
      assumption.
      apply Con_eq_simpl in Hrs as [ Habs].
      inv Hs.
      apply symmetry, fmerge_abs in Habs as [? Habs]; subst.
      eapply IHHcp; eauto 2.
      rewrite Hv, lift_lift.
      eapply fcont_stable, lift_ea_abs; eauto.
    - (* non absent *)
      apply symmetry in Hrs as Hcc.
      apply cons_is_cons, smerge_is_cons in Hcc as [Hcc Hcnp]; auto.
      apply is_cons_elim in Hcc as (c & cs' & Hcs).
      rewrite Hcs, ea_cons in *.
      unfold smerge in *.
      unshelve rewrite smerge_cons in Hrs.
      assumption.
      apply Con_eq_simpl in Hrs as [ Habs].
      inv Hs.
      destruct (fold_right (fun '(j, x) => fmerge enumtag tag_of_val tag_eqb j c x) (defcon c)
                  (combine l (nprod_hds np Hcnp))) eqn:Hf; try tauto || congruence.
      apply fmerge_pres in Hf as (b & t &?& Ht & Hex & Hf); subst; auto.

      (* TEST *)
      clear H Hc H3.
      rewrite kmerge_eq, Ht in *.
      rewrite Hu, first_cons.
      apply Exists_nth in Hex as (k & (d & x) &  Hk & HH).
      rewrite combine_nth in HH; auto using hds_length.
      rewrite combine_length, hds_length, Nat.min_id in *.
      destruct HH; subst.
      rewrite (nth_mem_nth _ _ _ _ k) in Hv; auto using  nth_error_nth'.
      erewrite nth_lift in Hv; auto.
      eapply hds_nth in H1; auto.
      rewrite H1, ea_cons, app_cons in Hv.
      rewrite Hv, first_cons.
      split; auto.
      exists cs',((lift (REM (sampl A)) np)).
      rewrite H0, Hu, Hv, 2 rem_cons in *.
      do 2 (split; auto).
      (* test *)
      apply fcont_stable.
      destruct l; try congruence.
      apply nprod_eq; intros i d' Hi.
      destruct (Nat.eq_dec k i); subst.
      + erewrite nth_lift_at_upd, 3 nth_lift, H1, ea_cons, 2 REM_simpl, 2 rem_cons; auto.
      + eapply Forall_nth with (i := i) in Hf.
        erewrite nth_lift_at, 3 nth_lift; auto.
        2:rewrite combine_length, hds_length, Nat.min_id; auto.
        erewrite combine_nth in Hf; auto using hds_length.
        erewrite hds_nth; auto.
        rewrite Hf, ea_cons, REM_simpl, rem_cons; auto.
        eapply NoDup_nth_neq; eauto.
    Unshelve.
    all: eauto.
  Qed.


  (** ** Le case  *)
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
    autorewrite with cpodb.
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

  Definition scase := @scase A B enumtag tag_of_val tag_eqb.

  Lemma erase_scase_le1 :
    forall l cs np,
      l <> [] ->
      NoDup l ->
      safe_DS (scase l cs np) ->
      ea (scase l cs np) <= kcase l (ea cs) (lift ea np).
  Proof.
    intros * Hl Nd Hs.
    apply DSle_rec_eq2 with
      (R := fun U V => exists cs np,
                safe_DS (scase l cs np)
                /\ U == ea (scase l cs np)
                /\ V == kcase l (ea cs) (lift ea np)).
    3:eauto.
    intros * ? Eq1 Eq2; setoid_rewrite <- Eq1; setoid_rewrite <- Eq2; eauto.
    clear Hs np cs.
    intros U V Hc (cs & np & Hs & Hu & Hv).
    rewrite Hu in Hc.
    apply ea_is_cons in Hc as Hcp.
    remember_ds (scase l cs np) as rs.
    revert dependent cs.
    revert dependent np.
    revert dependent U.
    revert dependent V.
    induction Hcp; intros.
    - rewrite <- eqEps in *; eauto 2.
    - (* absent *)
      assert (a = abs); subst.
      { inv Hs. cases. contradict H. congruence. }
      apply symmetry in Hrs as Hcc.
      apply cons_is_cons, scase_is_cons in Hcc as [Hcc Hcnp]; auto.
      apply is_cons_elim in Hcc as (c & cs' & Hcs).
      rewrite Hcs, ea_cons in *.
      unfold scase in *.
      unshelve rewrite scase_cons in Hrs.
      assumption.
      apply Con_eq_simpl in Hrs as [ Habs].
      inv Hs.
      apply symmetry, fcase_abs in Habs as [? [Habs]]; subst.
      2: destruct l; simpl in *; congruence.
      eapply IHHcp; eauto 2.
      rewrite Hv, lift_lift.
      eapply fcont_stable, lift_ea_abs; eauto.
    - (* non absent *)
      apply symmetry in Hrs as Hcc.
      apply cons_is_cons, scase_is_cons in Hcc as [Hcc Hcnp]; auto.
      apply is_cons_elim in Hcc as (c & cs' & Hcs).
      rewrite Hcs, ea_cons in *.
      unfold scase in *.
      unshelve rewrite scase_cons in Hrs.
      assumption.
      apply Con_eq_simpl in Hrs as [ Habs].
      inv Hs.
      destruct (fold_right (fun '(j, x) => fcase enumtag tag_of_val tag_eqb j c x)
                  (defcon c) (combine l (nprod_hds np Hcnp))) eqn:Hf; try tauto || congruence.
      apply fcase_pres in Hf as (b & t &?& Ht & Hex & Hf); subst; auto.
      clear H Hc H3.
      rewrite kcase_eq, Ht in *.
      rewrite Hu, first_cons.
      apply Exists_nth in Hex as (k & (d & x) &  Hk & HH).
      rewrite combine_nth in HH; auto using hds_length.
      rewrite combine_length, hds_length, Nat.min_id in *.
      destruct HH; subst.
      rewrite (nth_mem_nth _ _ _ _ k) in Hv; auto using  nth_error_nth'.
      erewrite nth_lift in Hv; auto.
      eapply hds_nth in H1; auto.
      rewrite H1, ea_cons, app_cons in Hv.
      rewrite Hv, first_cons.
      split; auto.
      exists cs',((lift (REM (sampl A)) np)).
      rewrite H0, Hu, Hv, 2 rem_cons in *.
      do 2 (split; auto).
      (* test *)
      apply fcont_stable.
      destruct l; try congruence.
      apply nprod_eq; intros i d' Hi.
      eapply Forall_nth with (i := i) in Hf.
      2:rewrite combine_length, hds_length, Nat.min_id; auto.
      erewrite 4 nth_lift; auto.
      erewrite combine_nth in Hf; auto using hds_length.
      destruct Hf as (?&Hf).
      erewrite hds_nth; auto.
      rewrite Hf, ea_cons, 2 REM_simpl, 2 rem_cons; auto.
    Unshelve.
    all: eauto.
  Qed.

End KFUNS.

Section KFBY.

  Lemma erase_fby1 :
  forall A v (xs ys : DS (sampl A)),
    safe_DS (fby1 (Some v) xs ys) ->
    ea (fby1 (Some v) xs ys) <= cons (val v) (ea ys).
Proof.
  intros * Hs.

  apply DSle_rec_eq2 with
    (R := fun U V =>
            (exists v xs ys,
              safe_DS (fby1 (Some v) xs ys)
              /\ U == ea (fby1 (Some v) xs ys)
              /\ V == cons (val v) (ea ys))
            \/
            (exists xs ys,
              safe_DS (fby1AP None xs ys)
              /\ U == ea (fby1AP None xs ys)
              /\ V == ea ys)
    ).
  3: eauto 12.
  intros * ? Eq1 Eq2; setoid_rewrite <- Eq1; setoid_rewrite <- Eq2; eauto 12.
  clear; intros U V Hc [(v & xs & ys & Sf & Hu & Hv) | (xs & ys & Sf & Hu & Hv)].
  - rewrite Hu, Hv in *.
  apply ea_is_cons in Hc as Hcp.
  remember_ds (fby1 (Some v) xs ys) as rs.
  revert dependent xs.
  revert dependent ys.
  revert dependent U.
  revert dependent V.
  revert dependent v.
  induction Hcp; intros.
  { rewrite <- eqEps in *; eauto 2. }
  all: destruct (@is_cons_elim _ xs) as (x & xs' & Hxs);
    [eapply fby1_cons; rewrite <- Hrs; eauto | rewrite Hxs in *].
  + assert (a = abs); subst.
    { apply Decidable.not_not in H; auto.
      unfold Decidable.decidable.
      destruct a; auto; right; congruence. }
    rewrite fby1_eq in Hrs.
    destruct x; apply Con_eq_simpl in Hrs as [? Hrs]; try congruence.
    rewrite ea_cons in *.
    all: destruct (@is_cons_elim _ ys) as (y & ys' & Hys);
      [eapply fby1AP_cons, isConP_is_cons; rewrite <- Hrs; eauto | rewrite Hys in *].
    inversion_clear Sf as [|??? Sf'].
    rewrite fby1AP_eq in Hrs.
    destruct y; rewrite ea_cons in *; eauto 2.
    all: exfalso; clear IHHcp.
    all: destruct (@is_cons_elim _ s) as (vs & s' & Hs);
      [eapply isConP_is_cons; eauto | rewrite Hs in *].
    all: apply symmetry, map_eq_cons_elim in Hrs as (?&?&?&?&?); subst;
      now inversion Sf'.
  + inversion_clear Sf as [|??? Sf'].
    rewrite fby1_eq in Hrs.
    destruct a, x; apply Con_eq_simpl in Hrs as [HH Ht];
      inversion_clear HH; try (tauto || congruence).
     rewrite ea_cons in *.
    rewrite 2 first_cons; split; auto.
    setoid_rewrite Hu.
    setoid_rewrite Hv.
    setoid_rewrite rem_cons.
    setoid_rewrite Ht.
    rewrite Ht in Sf'.
    right.
    exists xs', ys. split; auto.
  -
    rewrite Hu, Hv in *.
    destruct (@is_cons_elim _ ys) as (y & ys' & Hys);
      [eapply  fby1AP_cons, isConP_is_cons, ea_is_cons; eauto
      | rewrite Hys in *].
    rewrite fby1AP_eq in *.
    destruct y; rewrite ea_cons in *.
    1,3: destruct (@is_cons_elim _ xs) as (x & xs' & Hxs);
    [eapply map_is_cons, isConP_is_cons, ea_is_cons, Hc
    | rewrite Hxs, map_eq_cons in *]; now inversion_clear Sf.

    (* on se retrouve dans le même cas qu'avant !! *)
    { clear Hys ys.
      rename a into v.
      rename ys' into ys.
  apply ea_is_cons in Hc as Hcp.
  remember_ds (fby1 (Some v) xs ys) as rs.
  revert dependent xs.
  revert dependent ys.
  revert dependent U.
  revert dependent V.
  revert dependent v.
  induction Hcp; intros.
  { rewrite <- eqEps in *; eauto 2. }
  all: destruct (@is_cons_elim _ xs) as (x & xs' & Hxs);
    [eapply fby1_cons; rewrite <- Hrs; eauto | rewrite Hxs in *].
  + assert (a = abs); subst.
    { apply Decidable.not_not in H; auto.
      unfold Decidable.decidable.
      destruct a; auto; right; congruence. }
    rewrite fby1_eq in Hrs.
    destruct x; apply Con_eq_simpl in Hrs as [? Hrs]; try congruence.
    rewrite ea_cons in *.
    all: destruct (@is_cons_elim _ ys) as (y & ys' & Hys);
      [eapply fby1AP_cons, isConP_is_cons; rewrite <- Hrs; eauto | rewrite Hys in *].
    inversion_clear Sf as [|??? Sf'].
    rewrite fby1AP_eq in Hrs.
    destruct y; rewrite ea_cons in *; eauto 2.
    all: exfalso; clear IHHcp.
    all: destruct (@is_cons_elim _ s) as (vs & s' & Hs);
      [eapply isConP_is_cons; eauto | rewrite Hs in *].
    all: apply symmetry, map_eq_cons_elim in Hrs as (?&?&?&?&?); subst;
      now inversion Sf'.
  + inversion_clear Sf as [|??? Sf'].
    rewrite fby1_eq in Hrs.
    destruct a, x; apply Con_eq_simpl in Hrs as [HH Ht];
      inversion_clear HH; try (tauto || congruence).
     rewrite ea_cons in *.
    rewrite 2 first_cons; split; auto.
    setoid_rewrite Hu.
    setoid_rewrite Hv.
    setoid_rewrite rem_cons.
    setoid_rewrite Ht.
    rewrite Ht in Sf'.
    right.
    exists xs', ys. split; auto.
    }
Qed.

Theorem erase_fby :
  forall A (xs ys : DS (sampl A)),
    safe_DS (fby xs ys) ->
    ea (fby xs ys) <= app (ea xs) (ea ys).
Proof.
  intros * Hs.
  remember_ds (ea (fby xs ys)) as U.
  remember_ds (app (ea xs) (ea ys)) as V.
  revert_all; cofix Cof; intros.
  destruct U as [|u U]; [|clear Cof].
  { constructor; rewrite <- eqEps in *; eapply Cof; eauto. }
  (* on a une valeur sur U, donc un élément non absent dans xs *)
  remember_ds (fby xs ys) as t.
  apply symmetry in HU as HU2.
  apply cons_is_cons, ea_is_cons in HU2.
  rewrite HU, HV.
  clear HU HV U V u.
  revert dependent xs.
  revert dependent ys.
  induction HU2; intros.
  { rewrite <- eqEps in *; auto. }
  all: destruct (@is_cons_elim _ xs) as (x & xs' & Hxs);
    [eapply fby_cons; rewrite <- Ht; eauto | rewrite Hxs in *].
  - assert (a = abs); subst.
    { apply Decidable.not_not in H; auto.
      unfold Decidable.decidable.
      destruct a; auto; right; congruence. }
    rewrite fby_eq in Ht.
    destruct x; apply Con_eq_simpl in Ht as [? Ht]; try congruence.
    all: destruct (@is_cons_elim _ ys) as (y & ys' & Hys);
      [eapply fbyA_cons, isConP_is_cons; rewrite <- Ht; eauto | rewrite Hys in *].
    inversion_clear Hs as [|??? Hs'].
    rewrite fbyA_eq in Ht.
    destruct y; rewrite 3 ea_cons; auto.
    all: destruct (@is_cons_elim _ s) as (vs & s' & Hs);
      [eapply isConP_is_cons; eauto | rewrite Hs in *].
    all: apply symmetry, map_eq_cons_elim in Ht as (?&?&?&?&?); subst;
      now inversion Hs'.
  - inversion_clear Hs as [|??? Hs'].
    rewrite fby_eq in Ht.
    destruct a, x; try (tauto || congruence).
    all: apply Con_eq_simpl in Ht as [HH Ht]; try congruence.
    inversion_clear HH.
    rewrite 2 ea_cons, app_cons.
    apply cons_le_compat; auto.

    clear - Ht Hs'.

    remember_ds (ea s) as U.
    remember_ds (ea ys) as V.
    revert_all; cofix Cof; intros.
    destruct U as [|u U]; [|clear Cof].
    { constructor; rewrite <- eqEps in *; eapply Cof; eauto. }
    destruct (@is_cons_elim _ ys) as (y & ys' & Hys);
      [eapply fby1AP_cons, isConP_is_cons, ea_is_cons; rewrite <- Ht, <- HU; eauto
      | rewrite Hys in *].
    rewrite fby1AP_eq in Ht.
    destruct y; rewrite Ht in *.
    2: (* cas intéressant *)
      rewrite HU, HV, ea_cons, erase_fby1; now auto.
    all:
    destruct (@is_cons_elim _ xs') as (x & xs & Hxs);
      [eapply map_is_cons, isConP_is_cons, ea_is_cons; rewrite <- HU; eauto
      | rewrite Hxs, map_eq_cons in *; now inversion Hs'].
Qed.

End KFBY.

Section KUNOP.

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

  Theorem erase_unop :
    forall (op:A->option B) (xs : DS (sampl A)),
      ea (sunop op xs) == kunop op (ea xs).
  Proof.
    intros.
    apply DS_bisimulation_allin1 with
      (R := fun U V =>
              exists xs,
                U == ea (sunop op xs)
                /\ V == kunop op (ea xs)
      ).
    3: eauto.
  intros * ? Eq1 Eq2; setoid_rewrite <- Eq1; setoid_rewrite <- Eq2; eauto.
  clear; intros U V Hc (xs & Hu & Hv).
  rewrite Hu, Hv in *.
  destruct Hc as [Hc|Hc].
  {
  apply ea_is_cons in Hc as Hcp.
  remember_ds (sunop op xs) as rs.
  revert dependent xs.
  revert dependent U.
  revert dependent V.
  induction Hcp; intros.
  { rewrite <- eqEps in *; eauto 2. }
  - assert (a = abs); subst.
    { destruct a; auto; contradict H; congruence. }
    destruct (@is_cons_elim _ xs) as (x & xs' & Hxs).
    { apply symmetry, cons_is_cons in Hrs.
      unfold sunop in Hrs.
      now apply map_is_cons in Hrs. }
    rewrite Hxs, 2 ea_cons in *.
    rewrite sunop_eq in Hrs.
    apply Con_eq_simpl in Hrs as [].
    cases; congruence.
  - destruct (@is_cons_elim _ xs) as (x & xs' & Hxs).
    { apply symmetry, cons_is_cons in Hrs.
      unfold sunop in Hrs.
      now apply map_is_cons in Hrs. }
    rewrite Hxs, 2 ea_cons in *.
    rewrite sunop_eq in *.
    apply Con_eq_simpl in Hrs as [? Hrs].
    cases_eqn HH; subst; try congruence; inv H0.
    all:rewrite kunop_eq in *; cases_eqn HH; try congruence; try inv HH0.
    all: rewrite 2 first_cons; split; auto.
    all: esplit; rewrite Hu, Hv, 2 rem_cons, Hrs; auto.
  }
  {
  unfold kunop in Hc.
  apply map_is_cons, ea_is_cons in Hc as Hcp.
  revert dependent U.
  revert dependent V.
  induction Hcp; intros.
  { rewrite <- eqEps in *; eauto 2. }
  - assert (a = abs); subst.
    { destruct a; auto; contradict H; congruence. }
    rewrite sunop_eq, 2 ea_cons in * .
    apply IHHcp; auto.
  - rewrite sunop_eq, 2 ea_cons in * .
    cases_eqn HH; subst; try congruence; inv HH.
    all:rewrite kunop_eq in *; cases_eqn HH; try congruence; try inv HH1.
    all: rewrite 2 first_cons; split; auto.
    all: esplit; rewrite Hu, Hv, 2 rem_cons; auto.
  }
  Qed.

End KUNOP.

Section KBINOP.

  Context {A B D : Type}.

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

  Lemma erase_sbinop_1 :
    forall(op:A->B->option D) xs ys,
      safe_DS (sbinop op xs ys) ->
      ea (sbinop op xs ys) <= kbinop op (ea xs) (ea ys).
  Proof.
    intros * Hs.
    apply DSle_rec_eq2 with
      (R := fun U V =>
              (exists xs ys,
                  safe_DS (sbinop op xs ys)
                  /\ U == ea (sbinop op xs ys)
                  /\ V == kbinop op (ea xs) (ea ys))
      ).
  3: eauto.
  intros * ? Eq1 Eq2; setoid_rewrite <- Eq1; setoid_rewrite <- Eq2; eauto.
  clear; intros U V Hc (xs & ys & Hs & Hu & Hv).
  rewrite Hu, Hv in *.
  apply ea_is_cons in Hc as Hcp.
  remember_ds (sbinop op xs ys) as rs.
  revert dependent xs.
  revert dependent ys.
  revert dependent U.
  revert dependent V.
  induction Hcp; intros.
  { rewrite <- eqEps in *; eauto 2. }
  - assert (a = abs); subst.
    { inv Hs. cases. contradict H. congruence. }
    destruct (@is_cons_elim _ xs) as (x & xs' & Hxs).
    { eapply proj1, sbinop_is_cons; rewrite <- Hrs; auto. }
    destruct (@is_cons_elim _ ys) as (y & ys' & Hys).
    { eapply proj2, sbinop_is_cons; rewrite <- Hrs; auto. }
    rewrite Hxs, Hys, 3 ea_cons in *.
    rewrite sbinop_eq in Hrs.
    apply Con_eq_simpl in Hrs as [].
    inv Hs; cases; congruence.
  - destruct (@is_cons_elim _ xs) as (x & xs' & Hxs).
    { eapply proj1, sbinop_is_cons; rewrite <- Hrs; auto. }
    destruct (@is_cons_elim _ ys) as (y & ys' & Hys).
    { eapply proj2, sbinop_is_cons; rewrite <- Hrs; auto. }
    rewrite Hxs, Hys, 3 ea_cons in *.
    rewrite sbinop_eq in *.
    apply Con_eq_simpl in Hrs as [? Hrs].
    inv Hs.
    destruct x, y; try tauto.
    rewrite kbinop_eq, Hrs in *.
    cases_eqn HH; inv HH.
    rewrite 2 first_cons; split; auto.
    setoid_rewrite Hv.
    setoid_rewrite Hu.
    setoid_rewrite Hrs.
    rewrite 2 rem_cons; eauto.
Qed.

Lemma erase_sbinop_2 :
  forall (op:A->B->option D) xs ys,
    safe_DS (sbinop op xs ys) ->
    kbinop op (ea xs) (ea ys) <= ea (sbinop op xs ys).
Proof.
  intros * Hs.
  apply DSle_rec_eq2 with
    (R := fun U V =>
            (exists xs ys,
                safe_DS (sbinop op xs ys)
                /\ U == kbinop op (ea xs) (ea ys)
                /\ V == ea (sbinop op xs ys))
    ).
  3: eauto.
  intros * ? Eq1 Eq2; setoid_rewrite <- Eq1; setoid_rewrite <- Eq2; eauto.
  clear; intros U V Hc (xs & ys & Hs & Hu & Hv).
  rewrite Hu, Hv in *.
  apply kbinop_is_cons in Hc as [Hc1 Hc2].
  apply ea_is_cons in Hc1.
  revert dependent ys.
  revert U V.
  induction Hc1; intros.
  - rewrite <- eqEps in *; apply IHHc1; auto.
  - apply ea_is_cons in Hc2 as Hc2'.
    induction Hc2'.
    + rewrite <- eqEps in *; apply IHHc2'; auto.
    + rewrite sbinop_eq in *.
      inv Hs.
      cases_eqn HH; subst.
      2: contradict H0; congruence.
      repeat rewrite ea_cons in *.
      eapply IHHc1; auto.
    + repeat rewrite ea_cons in *.
      repeat rewrite sbinop_eq in *.
      inv Hs.
      cases_eqn HH; subst; try congruence.
      repeat rewrite ea_cons in *.
      rewrite kbinop_eq in *.
      cases_eqn HH; subst; try congruence.
      inv HH2; inv HH.
      rewrite 2 first_cons; split; auto.
      do 2 esplit; rewrite Hu, Hv, 2 rem_cons; eauto.
  - apply ea_is_cons in Hc2 as Hc2'.
    induction Hc2'.
    + rewrite <- eqEps in *; apply IHHc2'; auto.
    + rewrite sbinop_eq in *.
      inv Hs.
      cases_eqn HH; subst.
      all: contradict H0; congruence.
    + repeat rewrite ea_cons in *.
      repeat rewrite sbinop_eq in *.
      inv Hs.
      cases_eqn HH; subst; try congruence.
      repeat rewrite ea_cons in *.
      rewrite kbinop_eq in *.
      cases_eqn HH; subst; try congruence.
      inv HH2; inv HH.
      rewrite 2 first_cons; split; auto.
      do 2 esplit; rewrite Hu, Hv, 2 rem_cons; eauto.
Qed.

Theorem erase_sbinop :
  forall (op:A->B->option D) xs ys,
    safe_DS (sbinop op xs ys) ->
    ea (sbinop op xs ys) == kbinop op (ea xs) (ea ys).
Proof.
  split; auto using erase_sbinop_1, erase_sbinop_2.
Qed.

End KBINOP.


Section KDenot_node.

Context {PSyn : list decl -> block -> Prop}.
Context {Prefs : PS.t}.
Variable (G : @global PSyn Prefs).

Definition SI' := fun _ : ident => errv value.
Definition FI' := fun _ : ident => (DS_prod SI' -C-> DS_prod SI').
Definition errTy' : DS (errv value) := DS_const (err' error_Ty').

(* l'opérateur kwhen spécialisé aux Velus.Op.value *)
Definition kwhenv :=
  let get_tag := fun v => match v with Venum t => Some t | _ => None end in
  @kwhen value value enumtag get_tag Nat.eqb.

(* l'opérateur kmerge spécialisé aux Velus.Op.value *)
Definition kmergev :=
  let get_tag := fun v => match v with Venum t => Some t | _ => None end in
  @kmerge value value enumtag get_tag Nat.eqb.


Section KDenot_exps.

  Hypothesis kdenot_exp_ :
    forall e : exp,
      Dprod (Dprod (Dprodi FI') (DS_prod SI')) (DS_prod SI') -C->
      @nprod (DS (errv value)) (numstreams e).

  Definition kdenot_exps_ (es : list exp) :
    Dprod (Dprod (Dprodi FI') (DS_prod SI')) (DS_prod SI') -C->
    @nprod (DS (errv value)) (list_sum (List.map numstreams es)).
    induction es as [|a].
    + exact 0.
    + exact ((nprod_app @2_ (kdenot_exp_ a)) IHes).
  Defined.

  Definition kdenot_expss_ {A} (ess : list (A * list exp)) (n : nat) :
    Dprod (Dprod (Dprodi FI') (DS_prod SI')) (DS_prod SI') -C->
    @nprod (@nprod (DS (errv value)) n) (length ess).
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
  Dprod (Dprod (Dprodi FI') (DS_prod SI')) (DS_prod SI') -C->
  @nprod (DS (errv value)) (numstreams e).

  set (ctx := Dprod _ _).
  epose (kdenot_var :=
       fun x => if mem_ident x ins
             then PROJ (DS_fam SI') x @_ SND _ _ @_ FST _ _
             else PROJ (DS_fam SI') x @_ SND _ _).
  revert e.
  fix kdenot_exp_ 1.
  intro e.
  destruct e eqn:He; simpl (nprod _).
  - (* Econst *)
    (* véritable const, pas d'horloge dans le modèle de Kahn *)
    exact (CTE _ _ (DS_const (val (Vscalar (sem_cconst c))))).
  - (* Eenum *)
    exact (CTE _ _ (DS_const (val (Venum e0)))).
  - (* Evar *)
    exact (kdenot_var i).
  - (* Elast *)
    apply CTE, 0.
  - (* Eunop *)
    eapply fcont_comp. 2: apply (kdenot_exp_ e0).
    destruct (numstreams e0) as [|[]].
    (* pas le bon nombre de flots: *)
    1,3: apply CTE, errTy'.
    destruct (typeof e0) as [|ty []].
    1,3: apply CTE, errTy'.
    exact (kunop (fun v => sem_unop u v ty)).
  - (* Ebinop *)
    eapply fcont_comp2.
    3: apply (kdenot_exp_ e0_2).
    2: apply (kdenot_exp_ e0_1).
    destruct (numstreams e0_1) as [|[]], (numstreams e0_2) as [|[]].
    (* pas le bon nombre de flots: *)
    1-4,6-9: apply curry, CTE, errTy'.
    destruct (typeof e0_1) as [|ty1 []], (typeof e0_2) as [|ty2 []].
    1-4,6-9: apply curry, CTE, errTy'.
    exact (kbinop (fun v1 v2 => sem_binop b v1 ty1 v2 ty2)).
  - (* Eextcall *)
    apply CTE, 0.
  - (* Efby *)
    rename l into e0s, l0 into es, l1 into anns.
    clear He.
    pose (s0s := kdenot_exps_ kdenot_exp_ e0s).
    pose (ss := kdenot_exps_ kdenot_exp_ es).
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
    2,3: apply CTE, (nprod_const _ errTy').
    rewrite Heq1 in ss.
    rewrite <- Heq2.
    (* le véritable fby des réseaux de Kahn ! *)
    exact ((lift2 (APP _) @2_ s0s) ss).
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
    2: apply CTE, (nprod_const _ errTy').
    pose (ss := kdenot_exps_ kdenot_exp_ es).
    exact ((llift (kwhenv e0) @2_ ss) (kdenot_var i)).
  - (* Emerge *)
    rename l into ies.
    destruct l0 as (tys,ck).
    destruct p as [i ty].
    (* on calcule (length tys) flots pour chaque liste de sous-expressions *)
    pose (ses := kdenot_expss_ kdenot_exp_ ies (length tys)).
    rewrite <- (map_length fst) in ses.
    exact ((lift_nprod @_ (kmergev (List.map fst ies)) @2_ kdenot_var i) ses).
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
    pose (f := PROJ _ i @_ FST _ _ @_ FST _ _ : ctx -C-> FI' i).
    pose (ss := denot_exps_ denot_exp_ es).
    pose (rs := denot_exps_ denot_exp_ er).
    (* chaînage *)
    refine
      (np_of_env (List.map fst (n_out n)) @_
         (sreset @3_ f) (sbools_of @_ rs) (env_of_np (idents (n_in n)) @_ ss)).
Defined.

Definition denot_exp (ins : list ident) (e : exp) :
  (* (nodes * inputs * env) -> streams *)
  Dprodi FI' -C-> DS_prod SI' -C-> DS_prod SI' -C-> nprod (numstreams e) :=
  curry (curry (denot_exp_ ins e)).

Definition denot_exps (ins : list ident) (es : list exp) :
  Dprodi FI' -C-> DS_prod SI' -C-> DS_prod SI' -C-> nprod (list_sum (List.map numstreams es)) :=
  curry (curry (denot_exps_ (denot_exp_ ins) es)).

Lemma denot_exps_eq :
  forall ins e es envG envI env,
    denot_exps ins (e :: es) envG envI env
    = nprod_app (denot_exp ins e envG envI env) (denot_exps ins es envG envI env).
Proof.
  reflexivity.
Qed.
