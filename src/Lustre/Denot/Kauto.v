Require Import Common.Common.
Require Import Cpo.

(** identifiant de variable  *)
Parameter id : Type.
Inductive key : Type :=
| Var : id -> key
| Last : id -> key.

Definition env (A : Type) : cpo := DS_prod (fun _:key => A).

Definition ext_env {A B : Type} : (DS A -C-> DS B) -C-> (env A -C-> env B).
  apply curry, Dprodi_DISTR; intro i.
  refine ((AP _ _ @2_ FST _ _) (PROJ _ i @_ SND _ _)).
Defined.

Lemma ext_env_simpl : forall A B f env i,
    @ext_env A B f env i = f (env i).
Proof.
  trivial.
Qed.

(** Identifiant d'état, ou plus généralement d'un type énuméré *)
Parameter id_st : Type.
Parameter id_st_dec : forall i j : id_st, { i = j } + {~ i = j}.

Definition id_st_eqb (i j : id_st) : bool :=
  match id_st_dec i j with left _ => true | _ => false end.

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
     Dprodi_DISTR_simpl
  : localdb.

(** * Fonctions de flots utiles pour les automates *)
Section OPS.

Context {A B : Type}.

Definition whencf : (DS bool -C-> DS A -C-> DS A) -C-> DS bool -C-> DS A -C-> DS A.
  apply curry, curry.
  apply (fcont_comp2 (DSCASE bool A)).
  2:exact (SND _ _ @_ (FST _ _)).
  apply ford_fcont_shift; intro c.
  apply curry.
  apply (fcont_comp2 (DSCASE A A)).
  2:exact (SND _ _ @_ (FST _ _)).
  apply ford_fcont_shift; intro x.
  apply curry.
  destruct c.
  - refine (CONS x @_ _).
    refine ((_ @3_ ID _) _ _).
    exact (FST _ _ @_ (FST _ _ @_ (FST _ _ @_ (FST _ _)))).
    exact (SND _ _ @_ (FST _ _)).
    exact (SND _ _).
  - refine ((_ @3_ ID _) _ _).
    exact (FST _ _ @_ (FST _ _ @_ (FST _ _ @_ (FST _ _)))).
    exact (SND _ _ @_ (FST _ _)).
    exact (SND _ _).
Defined.

Lemma whencf_eq : forall F x xs c cs,
    whencf F (cons c cs) (cons x xs) ==
      if c
      then cons x (F cs xs)
      else F cs xs.
Proof.
    intros.
    unfold whencf.
    setoid_rewrite DSCASE_simpl.
    do 2 setoid_rewrite DScase_cons.
    destruct c; now simpl.
Qed.

Definition whenc : DS bool -C-> DS A -C-> DS A := FIXP _ whencf.

Lemma whenc_eq : forall x xs c cs,
    whenc (cons c cs) (cons x xs) ==
      if c
      then cons x (whenc cs xs)
      else whenc cs xs.
Proof.
    intros.
    unfold whenc.
    rewrite FIXP_eq at 1.
    now rewrite whencf_eq.
Qed.

Definition when_not := whenc @_ MAP negb.

Definition when_env : DS bool -C-> env A -C-> env A.
  apply curry.
  refine ((ext_env @2_ _) (SND _ _)).
  apply curry.
  refine ((whenc @2_ FST _ _ @_ FST _ _) (SND _ _)).
Defined.

Lemma when_env_simpl : forall cs env i,
    when_env cs env i = whenc cs (env i).
Proof.
  trivial.
Qed.

Definition when_not_env : DS bool -C-> env A -C-> env A.
  apply curry.
  refine ((ext_env @2_ _) (SND _ _)).
  apply curry.
  refine ((when_not @2_ FST _ _ @_ FST _ _) (SND _ _)).
Defined.

Lemma when_not_env_simpl : forall cs env i,
    when_not_env cs env i = when_not cs (env i).
Proof.
  trivial.
Qed.

(** when étendu aux [id_st]  *)
Definition wheni (i : id_st) : DS id_st -C-> DS A -C-> DS A :=
  whenc @_ MAP (fun j => id_st_eqb j i).

Definition wheni_env (i : id_st) : DS id_st -C-> env A -C-> env A :=
  ext_env @_ (wheni i).


Definition mergeif :
  (DS id_st -C-> (DS_prod (fun _:id_st => A)) -C-> DS A) -C->
  DS id_st -C-> (DS_prod (fun _:id_st => A)) -C-> DS A.
  apply curry, curry.
  apply (fcont_comp2 (DSCASE id_st A)).
  2:exact (SND _ _ @_ (FST _ _)).
  apply ford_fcont_shift; intro i.
  apply curry.
  refine ((APP _ @2_ PROJ _ i @_ SND _ _ @_ FST _ _) _).
  refine ((AP _ _ @3_ FST _ _ @_ FST _ _ @_ FST _ _) (SND _ _) _).
  refine (_ @_ SND _ _ @_ FST _ _).
  refine (DMAPi (fun j => if id_st_eqb i j then REM _ else ID _)).
Defined.

Lemma mergeif_simpl : forall F i c istr,
    mergeif F (cons i c) istr ==
      app (istr i) (F c (fun j => if id_st_eqb i j then rem (istr j) else istr j)).
Proof.
    intros.
    unfold mergeif.
    setoid_rewrite DScase_cons.
    simpl.
    eapply (fcont_stable (APP A (istr i))).
    repeat change (fcontit ?a ?b) with (a b).
    apply fcont_stable; simpl.
    apply Oprodi_eq_intro; intro j.
    destruct (id_st_eqb i j); auto.
Qed.

(** merge étendu aux [id_st] *)
Definition mergei :  DS id_st -C-> (DS_prod (fun _:id_st => A)) -C-> DS A :=
  FIXP _ mergeif.

Lemma mergei_simpl : forall i c istr,
    mergei (cons i c) istr ==
      app (istr i) (mergei c (fun j => if id_st_eqb i j then rem (istr j) else istr j)).
Proof.
  intros.
  unfold mergei.
  rewrite FIXP_eq at 1.
  now rewrite mergeif_simpl.
Qed.

(* le même, avec des environnements *)
Definition mergei_envf :
  (DS id_st -C-> (Dprodi (fun _:id_st => env A)) -C-> env A) -C->
  DS id_st -C-> (Dprodi (fun _:id_st => env A)) -C-> env A.
  apply curry, curry.
  apply Dprodi_DISTR; intro x.
  apply (fcont_comp2 (DSCASE id_st A)).
  2:exact (SND _ _ @_ (FST _ _)).
  apply ford_fcont_shift; intro i.
  apply curry.
  refine ((APP _ @2_ PROJ _ x @_ PROJ _ i @_ SND _ _ @_ FST _ _) _).
  refine (PROJ _ x @_ ((AP _ _ @3_ FST _ _ @_ FST _ _ @_ FST _ _) (SND _ _) _)).
  refine (_ @_ SND _ _ @_ FST _ _).
  refine (DMAPi (fun j => if id_st_eqb i j then REM_env else ID _)).
Defined.

Lemma mergei_envf_simpl : forall F i c istr,
    mergei_envf F (cons i c) istr ==
      APP_env (istr i) (F c (fun j => if id_st_eqb i j then REM_env (istr j) else istr j)).
Proof.
  intros.
  unfold mergei_envf.
  apply Oprodi_eq_intro; intro x.
  setoid_rewrite DScase_cons.
  simpl.
  eapply (fcont_stable (APP A _)).
  apply Oprodi_eq_elim with (p := (F c _)).
  apply (fcont_stable (F c)); simpl.
  apply Oprodi_eq_intro; intro j.
  destruct (id_st_eqb i j); auto.
Qed.

Definition mergei_env : DS id_st -C-> (Dprodi (fun _:id_st => env A)) -C-> env A :=
  FIXP _ mergei_envf.

Lemma mergei_env_simpl : forall i c istr,
    mergei_env (cons i c) istr ==
      APP_env (istr i) (mergei_env c (fun j => if id_st_eqb i j then REM_env (istr j) else istr j)).
Proof.
  intros.
  unfold mergei_env.
  rewrite FIXP_eq at 1.
  now rewrite mergei_envf_simpl.
Qed.

(** Switch *)
Definition switch : DS id_st -C-> (Dprodi (fun _:id_st => env A -C-> env A)) -C-> env A -C-> env A.
  apply curry, curry.
  refine ((mergei_env @2_ FST _ _ @_ FST _ _) _).
  apply Dprodi_DISTR; intro i.
  refine ((AP _ _ @2_ PROJ _ i @_ SND _ _ @_ FST _ _) _).
  refine ((wheni_env i @2_ FST _ _ @_ FST _ _) (SND _ _)).
Defined.

Lemma switch_simpl :
  forall c f e,
    switch c f e = mergei_env c (fun i => f i (wheni_env i c e)).
Proof.
  trivial.
Qed.


(** * Automates  *)


(* le "after_unless" de Marc
            c = F F F T F T F F ...
            x = 1 2 3 4 5 6 7 8 ...
   rem_unless =       4 5 6 7 8 .... *)
Definition rem_unlessf : (DS bool -C-> DS A -C-> DS A) -C-> DS bool -C-> DS A -C-> DS A.
  apply curry, curry.
  apply (fcont_comp2 (DSCASE bool A)).
  2:exact (SND _ _ @_ (FST _ _)).
  apply ford_fcont_shift; intro c.
  apply curry.
  apply (fcont_comp2 (DSCASE A A)).
  2:exact (SND _ _ @_ (FST _ _)).
  apply ford_fcont_shift; intro x.
  apply curry.
  destruct c.
  - refine (CONS x @_ SND _ _).
  - refine ((_ @3_ ID _) _ _).
    exact (FST _ _ @_ (FST _ _ @_ (FST _ _ @_ (FST _ _)))).
    exact (SND _ _ @_ (FST _ _)).
    exact (SND _ _).
Defined.

Lemma rem_unlessf_eq : forall F x xs c cs,
    rem_unlessf F (cons c cs) (cons x xs) ==
      if c then cons x xs else F cs xs.
Proof.
    intros.
    unfold rem_unlessf.
    setoid_rewrite DSCASE_simpl.
    do 2 setoid_rewrite DScase_cons.
    destruct c; now simpl.
Qed.

Definition rem_unless : DS bool -C-> DS A -C-> DS A := FIXP _ rem_unlessf.

Lemma rem_unless_eq : forall x xs c cs,
    rem_unless (cons c cs) (cons x xs) ==
      if c then cons x xs else rem_unless cs xs.
Proof.
    intros.
    unfold rem_unless.
    rewrite FIXP_eq at 1.
    now rewrite rem_unlessf_eq.
Qed.

Definition rem_unless_env : DS bool -C-> env A -C-> env A := ext_env @_ rem_unless.

Lemma rem_unless_env_simpl : forall c e i,
    rem_unless_env c e i = rem_unless c (e i).
Proof.
  trivial.
Qed.

(* le "after_until" de Marc
           c = F F F T F T F F ...
           x = 1 2 3 4 5 6 7 8 ...
   rem_until =         5 6 7 8 .... *)
(* TODO: vérifier, mais je crois que c'est aussi simple que ça *)
Definition rem_until : DS bool -C-> DS A -C-> DS A :=
  curry (REM _ @_ (rem_unless @2_ FST _ _) (SND _ _)).

Lemma rem_until_simpl :
  forall cs xs, rem_until cs xs == rem (rem_unless cs xs).
Proof.
  trivial.
Qed.

Definition rem_until_env : DS bool -C-> env A -C-> env A :=
  ext_env @_ rem_until.


(** le merge_unless de Marc étendu aux [env] *)
Definition merge_unlessf :
  (DS bool -C-> env A -C-> env A -C-> env A) -C->
  DS bool -C-> env A -C-> env A -C-> env A.
  apply curry, curry, curry.
  apply Dprodi_DISTR; intro x.
  apply (fcont_comp2 (DSCASE bool A)).
  2:exact (SND _ _ @_ FST _ _ @_ FST _ _).
  apply ford_fcont_shift; intro c.
  apply curry.
    match goal with
    | |- _ (_ (Dprod ?pl ?pr) _) =>
        pose (F := FST _ _ @_ FST _ _ @_ FST _ _ @_ FST pl pr);
        pose (e1 := SND _ _ @_ FST _ _ @_ FST pl pr);
        pose (e2 := SND _ _ @_ FST pl pr);
        idtac
    end.
    destruct c.
    - refine (PROJ _ x @_ e2).
    - refine ((PROJ _ x @_ _)).
      refine ((APP_env @2_ e1) _).
      refine ((AP _ _ @4_ F) (SND _ _) (REM_env @_ e1) e2).
Defined.

Lemma merge_unlessf_simpl : forall F c cs e1 e2,
    merge_unlessf F (cons c cs) e1 e2
    == if c then e2 else APP_env e1 (F cs (REM_env e1) e2).
Proof.
  intros.
  unfold merge_unlessf.
  apply Oprodi_eq_intro; intro x.
  autorewrite with localdb.
  setoid_rewrite DScase_cons.
  destruct c; auto.
Qed.

Definition merge_unless : DS bool -C-> env A -C-> env A -C-> env A :=
  FIXP _ merge_unlessf.

Lemma merge_unless_simpl : forall c cs e1 e2,
    merge_unless (cons c cs) e1 e2
    == if c then e2 else APP_env e1 (merge_unless cs (REM_env e1) e2).
Proof.
  intros.
  unfold merge_unless.
  rewrite FIXP_eq at 1.
  now rewrite merge_unlessf_simpl.
Qed.

Definition merge_until : DS bool -C-> env A -C-> env A -C-> env A :=
  merge_unless @_ CONS false.

Lemma merge_until_simpl : forall c e1 e2,
    merge_until c e1 e2 = merge_unless (cons false c) e1 e2.
Proof.
  trivial.
Qed.

(** le merge_unless de Marc étendu aux indices et aux [env] *)
Definition mergei_unlessf :
  (DS (option B) -C-> env A -C-> Dprodi (fun _:B => env A) -C-> env A) -C->
  DS (option B) -C-> env A -C-> Dprodi (fun _:B => env A) -C-> env A.
  apply curry, curry, curry.
  apply Dprodi_DISTR; intro x.
  apply (fcont_comp2 (DSCASE (option B) A)).
  2:exact (SND _ _ @_ FST _ _ @_ FST _ _).
  apply ford_fcont_shift; intro c.
  apply curry.
    match goal with
    | |- _ (_ (Dprod ?pl ?pr) _) =>
        pose (F := FST _ _ @_ FST _ _ @_ FST _ _ @_ FST pl pr);
        pose (e := SND _ _ @_ FST _ _ @_ FST pl pr);
        pose (fe := SND _ _ @_ FST pl pr);
        idtac
    end.
    destruct c as [i|].
    - refine (PROJ _ x @_ PROJ _ i @_ fe).
    - refine ((PROJ _ x @_ _)).
      refine ((APP_env @2_ e) _).
      refine ((AP _ _ @4_ F) (SND _ _) (REM_env @_ e) fe).
Defined.

Lemma mergei_unlessf_simpl : forall F c cs e fe,
    mergei_unlessf F (cons c cs) e fe
    == match c with
       | Some i => fe i
       | None => APP_env e (F cs (REM_env e) fe)
       end.
Proof.
  intros.
  unfold mergei_unlessf.
  apply Oprodi_eq_intro; intro x.
  autorewrite with localdb.
  setoid_rewrite DScase_cons.
  destruct c; auto.
Qed.

Definition mergei_unless : DS (option B) -C-> env A -C-> Dprodi (fun _:B => env A) -C-> env A :=
  FIXP _ mergei_unlessf.

Lemma mergei_unless_simpl : forall c cs e fe,
    mergei_unless (cons c cs) e fe
    == match c with
       | Some i => fe i
       | None => APP_env e (mergei_unless cs (REM_env e) fe)
       end.
Proof.
  intros.
  unfold mergei_unless.
  rewrite FIXP_eq at 1.
  now rewrite mergei_unlessf_simpl.
Qed.

Definition merge_until_env : DS (option B) -C-> env A -C-> Dprodi (fun _:B => env A) -C-> env A  :=
  mergei_unless @_ CONS None.

Lemma merge_until_env_simpl : forall c e fe,
    merge_until_env c e fe = mergei_unless (cons None c) e fe.
Proof.
  trivial.
Qed.

End OPS.


Section AUTO.

Variable A : Type.

Definition is_some {A} (o : option A) : bool :=
  match o with Some _ => true | _ => false end.


(** ** Transitions fortes réinitialisées *)

Definition auto_reset_strongf :
  Dprodi (fun _:id_st => env A -C-> env A) -C->
  Dprodi (fun _:id_st => env A -C-> DS (option id_st)) -C->
  (Dprodi (fun _:bool =>  Dprodi (fun _:id_st => env A -C-> env A)) -C->
   Dprodi (fun _:bool =>  Dprodi (fun _:id_st => env A -C-> env A))).
  apply curry, curry.
  apply Dprodi_DISTR; intro init.
  apply Dprodi_DISTR; intro i.
  apply curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (fs := FST _ _ @_ FST _ _ @_ FST pl pr);
      pose (ft := SND _ _ @_ FST _ _ @_ FST pl pr);
      pose (F := SND _ _ @_ FST pl pr);
      pose (e := SND pl pr);
      idtac
  end.
  pose (t := if init then (AP _ _ @2_ PROJ _ i @_ ft) e
             else CONS None @_ (AP _ _ @2_ PROJ _ i @_ ft) (REM_env @_ e)).
  pose (e' := (AP _ _ @2_ PROJ _ i @_ fs) e).
  refine ((mergei_unless @3_ t) e' _).
  apply Dprodi_DISTR; intro j.
  pose (re := (rem_unless_env @2_ MAP is_some @_ t) e).
  pose (fi := (PROJ _ j @_ PROJ _ false @_ F)).
  refine ((AP _ _ @2_ fi) re).
Defined.

Lemma auto_reset_strongf_eq :
  forall fs ft F init i e,
    auto_reset_strongf fs ft F init i e ==
      let t := if init then ft i e else cons None (ft i (REM_env e)) in
      let e' := fs i e in
      mergei_unless t e' (fun j => F false j (rem_unless_env (map is_some t) e)).
Proof.
  intros.
  unfold auto_reset_strongf.
  autorewrite with localdb.
  destruct init; auto.
Qed.

Definition auto_reset_strong (i : id_st) :
  Dprodi (fun _:id_st => env A -C-> env A) -C->
  Dprodi (fun _:id_st => env A -C-> DS (option id_st)) -C->
  env A -C->
  env A.
  apply curry, curry.
  eapply fcont_comp2.
  2: refine (((FIXP _ @_ (auto_reset_strongf @2_ FST _ _ @_ FST _ _) (SND _ _ @_ FST _ _)))).
  2: refine (SND _ _).
  apply curry.
  refine ((AP _ _ @2_ PROJ _ i @_ PROJ _ true @_ FST _ _) (SND _ _)).
Defined.

Lemma auto_reset_strong_eq :
  forall i fs ft e,
    auto_reset_strong i fs ft e = FIXP _ (auto_reset_strongf fs ft) true i e.
Proof.
  trivial.
Qed.


(** ** Transitions faibles réinitialisées *)

Definition auto_reset_weakf :
  Dprodi (fun _:id_st => env A -C-> env A) -C->
  Dprodi (fun _:id_st => env A -C-> DS (option id_st)) -C->
  (Dprodi (fun _:id_st => env A -C-> env A) -C->
   Dprodi (fun _:id_st => env A -C-> env A)).
  apply curry, curry.
  apply Dprodi_DISTR; intro i.
  apply curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (fs := FST _ _ @_ FST _ _ @_ FST pl pr);
      pose (ft := SND _ _ @_ FST _ _ @_ FST pl pr);
      pose (F := SND _ _ @_ FST pl pr);
      pose (e := SND pl pr);
      idtac
  end.
  pose (e' := (AP _ _ @2_ PROJ _ i @_ fs) e).
  pose (t := (AP _ _ @2_ PROJ _ i @_ ft) e').
  refine ((merge_until_env @3_ t) e' _).
  apply Dprodi_DISTR; intro j.
  pose (re := (rem_until_env @2_ MAP is_some @_ t) e).
  pose (fi := (PROJ _ j @_ F)).
  refine ((AP _ _ @2_ fi) re).
Defined.

Lemma auto_reset_weakf_eq :
  forall fs ft F i e,
    auto_reset_weakf fs ft F i e ==
      let e' := fs i e in
      (* on évalue les transitions dans le nouvel environnement *)
      let t := ft i e' in
      merge_until_env t e' (fun j => F j (rem_until_env (map is_some t) e)).
Proof.
  intros.
  unfold auto_reset_weakf.
  autorewrite with localdb.
  reflexivity.
Qed.

Definition auto_reset_weak (i : id_st) :
  Dprodi (fun _:id_st => env A -C-> env A) -C->
  Dprodi (fun _:id_st => env A -C-> DS (option id_st)) -C->
  env A -C->
  env A.
  apply curry, curry.
  eapply fcont_comp2.
  2: refine (((FIXP _ @_ (auto_reset_weakf @2_ FST _ _ @_ FST _ _) (SND _ _ @_ FST _ _)))).
  2: refine (SND _ _).
  apply curry.
  refine ((AP _ _ @2_ PROJ _ i @_ FST _ _) (SND _ _)).
Defined.

Lemma auto_reset_weak_eq :
  forall i fs ft e,
    auto_reset_weak i fs ft e = FIXP _ (auto_reset_weakf fs ft) i e.
Proof.
  trivial.
Qed.


(** ** Transitions fortes avec histoire *)

Definition auto_continue_stongf (i : id_st) :
  Dprodi (fun _:id_st => env A -C-> DS (option id_st)) -C->
  env A -C->
  Dprod (Dprodi (fun _:id_st => DS id_st)) (DS id_st) -C->
  Dprod (Dprodi (fun _:id_st => DS id_st)) (DS id_st).
  apply curry, curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (ft := FST _ _ @_ FST pl pr);
      pose (e := SND _ _ @_ FST pl pr);
      pose (ft' := FST _ _ @_ SND pl pr);
      pose (ts := SND _ _ @_ SND pl pr);
      idtac
  end.
  pose (_ts := CONS i @_ (mergei @2_ ts) ft').
  refine ((PAIR _ _ @2_ _) _ts).
  apply Dprodi_DISTR; intro j.
  refine (MAP (or_default j) @_ ((PROJ _ j @2_ ft) _)).
  refine ((wheni_env j @2_ ts) e).
Defined.

Lemma auto_continue_stongf_eq :
  forall i ft e ft' ts,
    auto_continue_stongf i ft e (ft',ts) =
      (fun i => map (or_default i) (ft i (wheni_env i ts e)),
         cons i (mergei ts ft')).
Proof.
  reflexivity.
Qed.

Definition auto_continue_stong (i : id_st) :
  Dprodi (fun _:id_st => env A -C-> env A) -C->
  Dprodi (fun _:id_st => env A -C-> DS (option id_st)) -C->
  env A -C-> env A.
  apply curry, curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (fs := FST _ _ @_ FST pl pr);
      pose (ft := SND _ _ @_ FST pl pr);
      pose (e := SND pl pr);
      idtac
  end.
  pose (F := FIXP _ @_ ((auto_continue_stongf i @2_ ft) e)).
  pose (ts := SND _ _ @_ F).
  refine ((mergei_env @2_ REM _ @_ ts) _).
  apply Dprodi_DISTR; intro j.
  refine ((PROJ _ j @2_ fs) _).
  refine ((wheni_env j @2_ REM _ @_ ts) e).
Defined.

Lemma auto_continue_stong_eq :
  forall i fs ft e,
    auto_continue_stong i fs ft e =
      let '(_, ts) := FIXP _ (auto_continue_stongf i ft e) in
      mergei_env (rem ts) (fun i => fs i (wheni_env i (rem ts) e)).
Proof.
  reflexivity.
Qed.


(** ** Transitions faibles avec histoire *)

Definition auto_continue_weakf (i : id_st) :
  Dprodi (fun _:id_st => env A -C-> env A) -C->
  Dprodi (fun _:id_st => env A -C-> DS (option id_st)) -C->
  env A -C->
  Dprod (Dprod (Dprodi (fun _:id_st => DS id_st)) (DS id_st)) (env A) -C->
  Dprod (Dprod (Dprodi (fun _:id_st => DS id_st)) (DS id_st)) (env A).
  apply curry, curry, curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (fs := FST _ _ @_ FST _ _ @_ FST pl pr);
      pose (ft := SND _ _ @_ FST _ _ @_ FST pl pr);
      pose (e := SND _ _ @_ FST pl pr);
      pose (ft' := FST _ _ @_ FST _ _ @_ SND pl pr);
      pose (ts := SND _ _ @_ FST _ _ @_ SND pl pr);
      pose (e' := SND _ _ @_ SND pl pr);
      idtac
  end.
  refine ((PAIR _ _ @2_ (PAIR _ _ @2_ _) _) _).
  - apply Dprodi_DISTR; intro j.
    refine (MAP (or_default j) @_ ((PROJ _ j @2_ ft) _)).
    refine ((wheni_env j @2_ ts) e').
  - refine (CONS i @_ (mergei @2_ ts) ft').
  - refine ((mergei_env @2_ ts) _).
    apply Dprodi_DISTR; intro j.
    refine ((PROJ _ j @2_ fs) _).
    refine ((wheni_env j @2_ ts) e).
Defined.

Lemma auto_continue_weakf_eq :
  forall i fs ft e ft' ts e',
    auto_continue_weakf i fs ft e (ft',ts,e') =
      (fun i => map (or_default i) (ft i (wheni_env i ts e')),
         cons i (mergei ts ft'),
         mergei_env ts (fun i => fs i (wheni_env i ts e))).
Proof.
  reflexivity.
Qed.

Definition auto_continue_weak (i : id_st) :
  Dprodi (fun _:id_st => env A -C-> env A) -C->
  Dprodi (fun _:id_st => env A -C-> DS (option id_st)) -C->
  env A -C->
  env A.
  apply curry, curry.
  refine (SND _ _ @_ FIXP _ @_ _).
  refine (uncurry (uncurry (auto_continue_weakf i))).
Defined.

Lemma auto_continue_weak_eq :
  forall i fs ft e,
    auto_continue_weak i fs ft e =
      let '(_, _, e') := FIXP _ (auto_continue_weakf i fs ft e) in
      e'.
Proof.
  reflexivity.
Qed.


(** ** Transisions mixtes faibles *)

(* TODO: move *)
Definition chain_AP :
  forall {D1 D2 D3 D4 : cpo},
    (D1 -C-> (D3 -C-> D4)) -> (D1 -C-> (D2 -C-> D3)) -> (D1 -C-> (D2 -C-> D4)).
  intros * f g.
  refine ((_ @2_ f) g).
  apply curry, curry.
  refine ((AP _ _ @2_ _) _).
  apply (FST _ _ @_ FST _ _).
  refine ((AP _ _ @2_ _) _).
  apply (SND _ _ @_ FST _ _).
  apply SND.
Defined.
Lemma chain_AP_eq :
  forall (D1 D2 D3 D4 : cpo) (f : D1 -C-> D3 -C-> D4) (g : D1 -C-> D2 -C-> D3) x y,
    @chain_AP D1 D2 D3 D4 f g x y = f x (g x y).
Proof.
  trivial.
Qed.

Local Hint Rewrite chain_AP_eq : localdb.

(* TODO: move *)
Lemma fcont_stable3 : forall {D1 D2 D3 D4:cpo} (f : D1 -C-> D2 -C-> D3 -C-> D4) (x1 x2 : D1) (y1 y2 : D2) (z1 z2 : D3),
    x1 == x2 -> y1 == y2 -> z1 == z2 -> f x1 y1 z1 == f x2 y2 z2.
Proof.
  intros * -> -> ->; reflexivity.
Qed.

Definition auto_weakf :
  Dprodi (fun _:id_st => env A -C-> env A) -C->
  Dprodi (fun _:id_st => env A -C-> DS (option (id_st * bool))) -C->
  Dprodi (fun '((i,reset):(id_st*bool)) =>
            (* e *)  env A -C->
            (* hist *) (Dprodi (fun i:id_st => env A -C-> env A)) -C->
            (* trim *) (Dprodi (fun '((i,A):id_st*Type) => DS A -C-> DS A)) -C->
            env A)
  -C->
  Dprodi (fun '((i,reset):(id_st*bool)) =>
            (* e *)  env A -C->
            (* hist *) (Dprodi (fun i:id_st => env A -C-> env A)) -C->
            (* trim *) (Dprodi (fun '((i,A):id_st*Type) => DS A -C-> DS A)) -C->
            env A).
  apply curry, curry.
  apply Dprodi_DISTR; intros (i,reset).
  apply curry, curry, curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (fs := FST _ _ @_ FST _ _ @_ FST _ _ @_ FST _ _ @_ FST pl pr);
      pose (ft := SND _ _ @_ FST _ _ @_ FST _ _ @_ FST _ _ @_ FST pl pr);
      pose (F := SND _ _ @_ FST _ _ @_ FST _ _ @_ FST pl pr);
      pose (e := SND _ _ @_ FST _ _ @_ FST pl pr);
      pose (hist := SND _ _ @_ FST pl pr);
      pose (trim := SND pl pr);
      idtac
  end.
  pose (s := if reset
             then (PROJ _ i @2_ fs) e
             else (ext_env @2_ (PROJ _ (i,_) @_ trim)) ((PROJ _ i @2_ fs) ((PROJ _ i @2_ hist) e))).
  pose (t := if reset
             then (PROJ _ i @2_ ft) s
             else (PROJ _ (i,_) @2_ trim) ((PROJ _ i @2_ ft) ((PROJ _ i @2_ hist) e))).
  pose (t' := MAP is_some @_ t).
  refine ((merge_until_env @3_ t) s _).
  apply Dprodi_DISTR; intros (j,r).
  refine ((PROJ _ (j,r) @4_ F) ((rem_until_env @2_ t') e) _ _).
  - (* new hist *)
    apply Dprodi_DISTR; intro k.
    refine (if id_st_eqb k i then _ else PROJ _ k @_ hist).
    refine (chain_AP (PROJ _ i @_ hist)  ((merge_until @2_ t') s)).
  - (* new trim *)
    apply Dprodi_DISTR; intros (k,T).
    refine (if id_st_eqb k i then _ else PROJ _ (k,T) @_ trim).
    refine (chain_AP (rem_until @_ t') (PROJ _ (i,T) @_ trim)).
Defined.

(** on utilise un type dépendant dans [trim] pour pouvoir l'appliquer à la fois
  * à des [DS A] et des [env A] *)
Lemma auto_weakf_eq :
  forall fs ft F i reset e hist trim,
    auto_weakf fs ft F (i,reset) e hist trim ==
      let s := if reset then fs i e else (ext_env (trim (i,_))) (fs i (hist i e)) in
      let t := if reset then ft i s else trim (i,_) (ft i (hist i e)) in
      let t' := map is_some t in
      let hist := fun k =>      if id_st_eqb k i then hist i @_ merge_until t' s else hist k in
      let trim := fun '(k,T) => if id_st_eqb k i then rem_until t' @_ trim (i,T) else trim (k,T) in
      merge_until_env t s (fun '(j,r) => F (j,r) (rem_until_env t' e) hist trim).
Proof.
  intros.
  unfold auto_weakf.
  repeat rewrite ?curry_Curry, ?Curry_simpl, ?Dprodi_DISTR_simpl.
  rewrite fcont_comp3_simpl.
  apply (fcont_stable3 merge_until_env); auto.
  { destruct reset; auto. }
  { destruct reset; auto. }
  apply Oprodi_eq_intro; intros [].
  rewrite Dprodi_DISTR_simpl.
  rewrite fcont_comp4_simpl.
  apply (fcont_stable3 (F (i0,b))).
  - destruct reset; auto.
  - apply Oprodi_eq_intro; intro.
    rewrite Dprodi_DISTR_simpl.
    apply Oprodi_eq_intro; intro.
    destruct (id_st_eqb _ _); auto.
    change (fcontit ?a ?b) with (a b).
    destruct reset; reflexivity.
  - apply Oprodi_eq_intro; intros [].
    rewrite Dprodi_DISTR_simpl.
    apply Oprodi_eq_intro; intro.
    destruct (id_st_eqb _ _); auto.
    destruct reset; auto.
Qed.

Definition auto_weak (i : id_st) :
  Dprodi (fun _:id_st => env A -C-> env A) -C->
  Dprodi (fun _:id_st => env A -C-> DS (option (id_st * bool))) -C->
  env A -C-> env A.
  apply curry, curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (fs := FST _ _ @_ FST pl pr);
      pose (ft := SND _ _ @_ FST pl pr);
      pose (e := SND pl pr);
      idtac
  end.
  pose (F := PROJ _ (i,false) @_ (FIXP _ @_ ((auto_weakf @2_ fs) ft))).
  cbv beta iota in F.
  refine ((AP _ _ @4_ F) e _ _).
  apply CTE; intro; apply ID.
  apply CTE; intros []; apply ID.
Defined.

Lemma auto_weak_eq :
  forall i fs ft e,
    auto_weak i fs ft e =
      (FIXP _ (auto_weakf fs ft)) (i, false) e (fun i => ID _ ) (fun '(i,_) => ID _).
Proof.
  reflexivity.
Qed.


(** ** Transitions mixtes fortes *)

Definition auto_strongf :
  Dprodi (fun _:id_st => env A -C-> env A) -C->
  Dprodi (fun _:id_st => env A -C-> DS (option (id_st * bool))) -C->
  Dprodi (fun '((i,init,reset):(id_st*bool*bool)) =>
            (* e *)  env A -C->
            (* hist *) (Dprodi (fun i:id_st => env A -C-> env A)) -C->
            (* trim *) (Dprodi (fun '((i,A):id_st*Type) => DS A -C-> DS A)) -C->
            env A)
  -C->
  Dprodi (fun '((i,init,reset):(id_st*bool*bool)) =>
            (* e *)  env A -C->
            (* hist *) (Dprodi (fun i:id_st => env A -C-> env A)) -C->
            (* trim *) (Dprodi (fun '((i,A):id_st*Type) => DS A -C-> DS A)) -C->
            env A).
  apply curry, curry.
  apply Dprodi_DISTR; intros ((i & init) & reset).
  apply curry, curry, curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (fs := FST _ _ @_ FST _ _ @_ FST _ _ @_ FST _ _ @_ FST pl pr);
      pose (ft := SND _ _ @_ FST _ _ @_ FST _ _ @_ FST _ _ @_ FST pl pr);
      pose (F := SND _ _ @_ FST _ _ @_ FST _ _ @_ FST pl pr);
      pose (e := SND _ _ @_ FST _ _ @_ FST pl pr);
      pose (hist := SND _ _ @_ FST pl pr);
      pose (trim := SND pl pr);
      idtac
  end.

  pose (t := if init then (PROJ _ i @2_ ft) e else
             (if reset
              then CONS None @_ (PROJ _ i @2_ ft) (REM_env @_ e)
              else CONS None @_ (PROJ _ (i,_) @2_ trim) ((PROJ _ i @2_ ft) ((PROJ _ i @2_ hist) (REM_env @_ e))))).
  pose (s := if reset
             then (PROJ _ i @2_ fs) e
             else (ext_env @2_ (PROJ _ (i,_) @_ trim)) ((PROJ _ i @2_ fs) ((PROJ _ i @2_ hist) e))).
  pose (t' := MAP is_some @_ t).
  refine ((mergei_unless @3_ t) s _).
  apply Dprodi_DISTR; intros (j,r).
  refine ((PROJ _ (j,false,r) @4_ F) ((rem_unless_env @2_ t') e) _ _).
  - (* new hist *)
    apply Dprodi_DISTR; intro k.
    refine (if id_st_eqb k i then _ else PROJ _ k @_ hist).
    refine (chain_AP (PROJ _ i @_ hist)  ((merge_unless @2_ t') s)).
  - (* new trim *)
    apply Dprodi_DISTR; intros (k,T).
    refine (if id_st_eqb k i then _ else PROJ _ (k,T) @_ trim).
    refine (chain_AP (rem_unless @_ t') (PROJ _ (i,T) @_ trim)).
Defined.

(* on utilise un type dépendant dans [trim] pour pouvoir l'appliquer à la fois
 * à des [DS A] et des [env A] *)
Lemma auto_strongf_eq :
  forall fs ft F i init reset e hist trim,
    auto_strongf fs ft F (i,init,reset) e hist trim ==
      let t := if init then ft i e
               else if reset then cons None (ft i (REM_env e))
                    else cons None (trim (i,_) (ft i (hist i (REM_env e)))) in
      let s := if reset then fs i e else ext_env (trim (i,_)) (fs i (hist i e)) in
      let t' := map is_some t in
      let hist := fun k =>      if id_st_eqb k i then hist i @_ merge_unless t' s else hist k in
      let trim := fun '(k,T) => if id_st_eqb k i then rem_unless t' @_ trim (i,T) else trim (k,T) in
      mergei_unless t s (fun '(j,r) => F (j,false,r) (rem_unless_env t' e) hist trim).
Proof.
  intros.
  unfold auto_strongf.
  repeat rewrite ?curry_Curry, ?Curry_simpl, ?Dprodi_DISTR_simpl.
  rewrite fcont_comp3_simpl.
  apply (fcont_stable3 mergei_unless); auto.
  { destruct init, reset; auto. }
  { destruct init, reset; auto. }
  apply Oprodi_eq_intro; intros [].
  rewrite Dprodi_DISTR_simpl.
  rewrite fcont_comp4_simpl.
  apply (fcont_stable3 (F (i0,false,b))).
  - destruct init, reset; auto.
  - apply Oprodi_eq_intro; intro.
    rewrite Dprodi_DISTR_simpl.
    apply Oprodi_eq_intro; intro.
    destruct (id_st_eqb _ _); auto.
    change (fcontit ?a ?b) with (a b).
    destruct init, reset; reflexivity.
  - apply Oprodi_eq_intro; intros [].
    rewrite Dprodi_DISTR_simpl.
    apply Oprodi_eq_intro; intro.
    destruct (id_st_eqb _ _); auto.
    destruct init, reset; auto.
Qed.

Definition auto_strong (i : id_st) :
  Dprodi (fun _:id_st => env A -C-> env A) -C->
  Dprodi (fun _:id_st => env A -C-> DS (option (id_st * bool))) -C->
  env A -C-> env A.
  apply curry, curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (fs := FST _ _ @_ FST pl pr);
      pose (ft := SND _ _ @_ FST pl pr);
      pose (e := SND pl pr);
      idtac
  end.
  pose (F := PROJ _ (i,true,false) @_ (FIXP _ @_ ((auto_strongf @2_ fs) ft))).
  cbv beta iota in F.
  refine ((AP _ _ @4_ F) e _ _).
  apply CTE; intro; apply ID.
  apply CTE; intros []; apply ID.
Defined.

Lemma auto_strong_eq :
  forall i fs ft e,
    auto_strong i fs ft e =
      (FIXP _ (auto_strongf fs ft)) (i, true, false) e (fun i => ID _ ) (fun '(i,_) => ID _).
Proof.
  reflexivity.
Qed.
