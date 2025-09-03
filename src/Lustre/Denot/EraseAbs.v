From Coq Require Import Datatypes List.
Import List.ListNotations.

From Velus Require Import Lustre.Denot.Cpo CommonTactics.
Require Import CommonDS CommonList2 SDfuns Kfuns.


(* TODO: move *)
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

  Lemma isConP_is_cons :
  forall D (P:D->Prop) xs, isConP P xs -> is_cons xs.
Proof.
  induction 1; auto; now constructor.
Qed.
(* /TODO: move *)


(** ** Erase absences : [sampl] -> [errv] *)
Section EA.

Definition ea {A : Type} : DS (sampl A) -C-> DS (errv A) :=
  MAP (fun (x:sampl A) => match x with
                     | pres v => val v
                     | err error_Ty => err' error_Ty'
                     | err error_Op => err' error_Op'
                     | abs | err error_Cl => err' error_Ty'
                     end)
  @_ filterb (fun v => match v with abs => false | _ => true end).

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

(* TODO: mutualiser quelque part ? *)
Definition safe_DS {A} : DS (sampl A) -> Prop :=
  DSForall (fun v => match v with err _ => False | _ => True end).


Section Ea_unop_binop.

Context {A B D : Type}.

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
    generalize dependent xs.
    generalize dependent U.
    generalize dependent V.
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
    generalize dependent U.
    generalize dependent V.
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
  generalize dependent xs.
  generalize dependent ys.
  generalize dependent U.
  generalize dependent V.
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
  generalize dependent ys.
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

End Ea_unop_binop.

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
  generalize dependent xs.
  generalize dependent ys.
  generalize dependent U.
  generalize dependent V.
  generalize dependent v.
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
  - rewrite Hu, Hv in *.
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
  generalize dependent xs.
  generalize dependent ys.
  generalize dependent U.
  generalize dependent V.
  generalize dependent v.
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
  generalize dependent xs.
  generalize dependent ys.
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

(* The other way is false.
   Par ex :
     xs = A 0 A A A A ...
     ys = A 1 A A A A ...
     ea (fby xs ys) = 0
     app (ea xs) (ea ys) = 0 1
 *)
Theorem erase_fby_inf :
  forall A (xs ys : DS (sampl A)),
    infinite (fby xs ys) ->
    safe_DS (fby xs ys) ->
    ea (fby xs ys) == app (ea xs) (ea ys).
Abort.


Section Ea_when_merge_case.

  Context {A B : Type}.
  Variable enumtag : Type.
  Variable tag_of_val : B -> option enumtag.
  Variable tag_eqb : enumtag -> enumtag -> bool.

  Hypothesis tag_eqb_eq : forall t1 t2, tag_eqb t1 t2 = true <-> t1 = t2.

  (* FIXME: is Notation a really good solution here ? *)
  Local Notation swhen := (@swhen A B enumtag tag_of_val tag_eqb).
  Local Notation kwhen := (@kwhen A B enumtag tag_of_val tag_eqb).
  Local Notation smerge := (@smerge A B enumtag tag_of_val tag_eqb).
  (* FIXME: kmerge/kcase needs [tag_eqb_eq] because of mem_nth *)
  Local Notation kmerge := (@kmerge A B enumtag tag_of_val tag_eqb tag_eqb_eq).
  Local Notation scase := (@scase A B enumtag tag_of_val tag_eqb).
  Local Notation kcase := (@kcase A B enumtag tag_of_val tag_eqb tag_eqb_eq).
  Local Notation scase_def_ := (@scase_def_ A B enumtag tag_of_val tag_eqb).
  Local Notation scase_def := (@scase_def A B enumtag tag_of_val tag_eqb).
  Local Notation kcase_def := (@kcase_def A B enumtag tag_of_val tag_eqb tag_eqb_eq).

  (** This side is OK. The other is much more complicated because
      of [isConP] on kwhen, etc., and not very useful. *)
  Theorem erase_swhen_le1 :
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
    generalize dependent xs.
    generalize dependent cs.
    generalize dependent U.
    generalize dependent V.
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

  Lemma lift_ea_pres :
    forall I A (l:list I) (np : nprod (length l)) Hnp,
      l <> [] ->
      Forall (fun '(_, x) => exists v : A, x = pres v) (combine l (nprod_hds np Hnp)) ->
      lift (REM (errv A) @_ ea) np == lift (@ea A @_ REM _) np.
  Proof.
    induction l as [|i l]; intros * Hl Hf; try congruence.
    inv Hf.
    unfold projT1 in H1.
    cases; destruct H1; subst.
    destruct s as (xx & Hxx%decomp_eqCon).
    rewrite 2 (nprod_hd_tl np).
    setoid_rewrite lift_cons.
    rewrite Hxx.
    autorewrite with cpodb.
    rewrite nprod_hd_cons, ea_cons, 2 rem_cons.
    apply nprod_cons_Oeq_compat; auto.
    destruct l as [|j l].
    + simpl.
      autorewrite with cpodb.
      rewrite ea_cons, rem_cons; auto.
    + assert (j :: l <> []) as Hll by congruence.
      eauto.
  Qed.

  Theorem erase_smerge_le1 :
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
    generalize dependent cs.
    generalize dependent np.
    generalize dependent U.
    generalize dependent V.
    induction Hcp; intros.
    - rewrite <- eqEps in *; eauto 2.
    - (* absent *)
      assert (a = abs); subst.
      { inv Hs. cases. contradict H. congruence. }
      apply symmetry in Hrs as Hcc.
      apply cons_is_cons, smerge_is_cons in Hcc as [Hcc Hcnp]; auto.
      apply is_cons_elim in Hcc as (c & cs' & Hcs).
      rewrite Hcs, ea_cons in *.
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
      rewrite length_combine, hds_length, Nat.min_id in *.
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
        2:rewrite length_combine, hds_length, Nat.min_id; auto.
        erewrite combine_nth in Hf; auto using hds_length.
        erewrite hds_nth; auto.
        rewrite Hf, ea_cons, REM_simpl, rem_cons; auto.
        eapply NoDup_nth_neq; eauto.
    Unshelve.
    all: eauto.
  Qed.

  Theorem erase_scase_le1 :
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
    generalize dependent cs.
    generalize dependent np.
    generalize dependent U.
    generalize dependent V.
    induction Hcp; intros.
    - rewrite <- eqEps in *; eauto 2.
    - (* absent *)
      assert (a = abs); subst.
      { inv Hs. cases. contradict H. congruence. }
      apply symmetry in Hrs as Hcc.
      apply cons_is_cons, scase_is_cons in Hcc as [Hcc Hcnp]; auto.
      apply is_cons_elim in Hcc as (c & cs' & Hcs).
      rewrite Hcs, ea_cons in *.
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
      rewrite length_combine, hds_length, Nat.min_id in *.
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
      2:rewrite length_combine, hds_length, Nat.min_id; auto.
      erewrite 4 nth_lift; auto.
      erewrite combine_nth in Hf; auto using hds_length.
      destruct Hf as (?&Hf).
      erewrite hds_nth; auto.
      rewrite Hf, ea_cons, 2 REM_simpl, 2 rem_cons; auto.
    Unshelve.
    all: eauto.
  Qed.

  Theorem erase_scase_def__le1 :
    forall l cs ds np,
      l <> [] ->
      NoDup l ->
      safe_DS (scase_def_ l cs ds np) ->
      ea (scase_def_ l cs ds np) <= kcase_def l (ea cs) (nprod_cons (ea ds) (lift ea np)).
  Proof.
    intros * Hl Nd Hs.
    apply DSle_rec_eq2 with
      (R := fun U V => exists cs ds np,
                safe_DS (scase_def_ l cs ds np)
                /\ U == ea (scase_def_ l cs ds np)
                /\ V == kcase_def l (ea cs) (nprod_cons (ea ds) (lift ea np))).
    3:eauto 6.
    intros * ? Eq1 Eq2; setoid_rewrite <- Eq1; setoid_rewrite <- Eq2; eauto.
    clear Hs np cs ds.
    intros U V Hc (cs & ds & np & Hs & Hu & Hv).
    rewrite Hu in Hc.
    apply ea_is_cons in Hc as Hcp.
    remember_ds (scase_def_ l cs ds np) as rs.
    generalize dependent cs.
    generalize dependent ds.
    generalize dependent np.
    generalize dependent U.
    generalize dependent V.
    induction Hcp; intros.
    - rewrite <- eqEps in *; eauto 2.
    - (* absent *)
      assert (a = abs); subst.
      { inv Hs. cases. contradict H. congruence. }
      apply symmetry in Hrs as Hcc.
      apply cons_is_cons, scase_def__is_cons in Hcc as (Hcc & Hcd & Hcnp); auto.
      apply is_cons_elim in Hcc as (c & cs' & Hcs).
      apply is_cons_elim in Hcd as (d & ds' & Hds).
      rewrite Hcs, Hds, ea_cons in *.
      unshelve rewrite scase_def__cons in Hrs.
      assumption.
      apply Con_eq_simpl in Hrs as [ Habs].
      inv Hs.
      apply symmetry, fcase_abs in Habs as [? [Habs]]; subst.
      2: destruct l; simpl in *; congruence.
      eapply IHHcp; eauto 2.
      rewrite Hv, lift_lift, ea_cons.
      destruct d; simpl in *; try congruence.
      rewrite lift_ea_abs; eauto.
    - (* non absent *)
      apply symmetry in Hrs as Hcc.
      apply cons_is_cons, scase_def__is_cons in Hcc as (Hcc & Hcd & Hcnp); auto.
      apply is_cons_elim in Hcc as (c & cs' & Hcs).
      apply is_cons_elim in Hcd as (d & ds' & Hds).
      rewrite Hcs, Hds, ea_cons in *.
      unshelve rewrite scase_def__cons in Hrs.
      assumption.
      apply Con_eq_simpl in Hrs as [ Habs].
      inv Hs.
      destruct (fold_right (fun '(j, x) => fcase enumtag tag_of_val tag_eqb j c x)
           (defcon2 c d) (combine l (nprod_hds np Hcnp))) eqn:Hf; try tauto || congruence.
      apply fcase_pres2 in Hf as (b &?& t &?& Ht & ? & Hf & Hor ); subst; auto.
      2: destruct l; simpl in *; congruence.
      clear H Hc H3.
      rewrite kcase_def_eq, kcase_def__eq, Ht in *; auto.
      rewrite Hu, first_cons.
      destruct Hor as [Hex | [Hff]]; subst.
      + apply Exists_nth in Hex as (k & (d & y) &  Hk & HH).
        rewrite combine_nth in HH; auto using hds_length.
        rewrite length_combine, hds_length, Nat.min_id in *.
        destruct HH; subst.
        rewrite (nth_mem_nth _ _ _ _ k) in Hv; auto using  nth_error_nth'.
        erewrite nth_lift in Hv; auto.
        eapply hds_nth in H1; auto.
        rewrite H1, ea_cons, app_cons in Hv.
        rewrite Hv, first_cons.
        split; auto.
        exists cs',(rem ds),((lift (REM (sampl A)) np)).
        rewrite Hds, H0, Hu, Hv, ea_cons, 4 rem_cons in *.
        do 2 (split; auto).
        (* test *)
        rewrite kcase_def_eq; auto.
        apply fcont_stable.
        destruct l; try congruence.
        apply nprod_eq; intros i d' Hi.
        eapply Forall_nth with (i := i) in Hf.
        2:rewrite length_combine, hds_length, Nat.min_id; auto.
        erewrite 4 nth_lift; auto.
        erewrite combine_nth in Hf; auto using hds_length.
        destruct Hf as (?&Hf).
        erewrite hds_nth; auto.
        rewrite Hf, ea_cons, 2 REM_simpl, 2 rem_cons; auto.
      + eassert (Hm : mem_nth enumtag _ l t = None); [|rewrite Hm in Hv].
        { clear - Hff.
          induction l; auto; simpl.
          inv Hff.
          cases_eqn HH; subst; try congruence.
          erewrite IHl; eauto.
        }
        rewrite ea_cons, app_cons in Hv.
        rewrite Hv, first_cons.
        split; auto.
        exists cs',(rem ds),((lift (REM (sampl A)) np)).
        rewrite H0, Hds, Hu, Hv, 4 rem_cons in *.
        do 2 (split; auto).
        rewrite kcase_def_eq, 2 lift_lift, lift_ea_pres; eauto.
        Unshelve.
    all: eauto.
  Qed.

End Ea_when_merge_case.
