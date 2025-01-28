From Coq Require Import BinPos List.

From Velus Require Import Common Ident Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LSemantics Lustre.LOrdered.
From Velus Require Import Lustre.Denot.Cpo Lustre.Denot.SD.
From Velus.Lustre.Denot.Cpo Require Import Cpo_streams_type.

Close Scope equiv_scope. (* conflicting notation "==" *)
Import ListNotations.

Require Import CommonList2 Kfuns.

(** * TEST : une sémantique Kahnienne pour Lustre *)
Module Type LKAHN
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn).
       (* (Import Sd    : SD            Ids Op OpAux Cks Senv Syn Lord). *)

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
  @kmerge value value enumtag get_tag Nat.eqb Nat.eqb_eq.

(* l'opérateur kcase spécialisé aux Velus.Op.value *)
Definition kcasev :=
  let get_tag := fun v => match v with Venum t => Some t | _ => None end in
  @kcase value value enumtag get_tag Nat.eqb Nat.eqb_eq.

(* l'opérateur kcase_def spécialisé aux Velus.Op.value *)
Definition kcase_defv :=
  let get_tag := fun v => match v with Venum t => Some t | _ => None end in
  @kcase_def value value enumtag get_tag Nat.eqb Nat.eqb_eq.


(** On définit tout de suite [kdenot_exps_] en fonction de [kdenot_exp_]
    pour simplifier le raisonnement dans kdenot_exp_eq *)
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
    pose (ses := kdenot_expss_ kdenot_exp_ ies (length tys)).
    rewrite <- (map_length fst) in ses.
    destruct o as [d_es|].
    + (* avec une branche par défaut *)
      revert ses.
      destruct (Nat.eq_dec
                  (list_sum (List.map numstreams d_es))
                  (length tys)
               ) as [<-|].
      2: apply CTE, CTE, (nprod_const _ errTy').
      intro ses.
      refine ((_ @3_ (kdenot_exp_ e0)) (kdenot_exps_ kdenot_exp_ d_es) ses).
      destruct (numstreams e0) as [|[]].
      1,3: apply CTE, CTE, (nprod_const _ errTy').
      exact (lift_nprod @_ kcase_defv (List.map fst ies)).
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
