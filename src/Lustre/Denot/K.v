From Coq Require Import BinPos List.

From Velus Require Import Common Ident Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LSemantics Lustre.LOrdered.
From Velus Require Import Lustre.Denot.Cpo.
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

(*****************  *)
(* FIXME: comment unifier ces trucs là entre SI et SI' ? *)
Definition np_of_env' (l : list ident) : DS_prod SI' -C-> @nprod (DS (errv value)) (length l).
  induction l as [| x l].
  - apply CTE, 0.
  - exact ((nprod_cons @2_ PROJ _ x) IHl).
Defined.
Definition env_of_np' (l : list ident) {n} : nprod n -C-> DS_prod SI' :=
  Dprodi_DISTR _ _ _
    (fun x => match mem_nth ident ident_eq_dec l x with
           | Some n => get_nth n errTy'
           | None => 0
           end).
(*****************  *)


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
    rewrite <- (length_map fst) in ses.
    exact ((lift_nprod @_ (kmergev (List.map fst ies)) @2_ kdenot_var i) ses).
  - (* Ecase *)
    rename l into ies.
    destruct l0 as (tys,ck).
    (* on calcule (length tys) flots pour chaque liste de sous-expressions *)
    pose (ses := kdenot_expss_ kdenot_exp_ ies (length tys)).
    rewrite <- (length_map fst) in ses.
    destruct o as [d_es|].
    + (* avec une branche par défaut *)
      revert ses.
      destruct (Nat.eq_dec
                  (list_sum (List.map numstreams d_es))
                  (length tys)
               ) as [<-|].
      2: apply CTE, CTE, (nprod_const _ errTy').
      intro ses.
      refine ((_ @2_ (kdenot_exp_ e0)) ((nprod_cons @2_ kdenot_exps_ kdenot_exp_ d_es) ses)).
      destruct (numstreams e0) as [|[]].
      1,3: apply CTE, CTE, (nprod_const _ errTy').
      exact (lift_nprod @_ kcase_defv (List.map fst ies)).
    + (* case total *)
      (* condition, branches *)
      refine ((_ @2_ (kdenot_exp_ e0)) ses).
      destruct (numstreams e0) as [|[]].
      1,3: apply CTE, CTE, (nprod_const _ errTy').
      exact (lift_nprod @_ (kcasev (List.map fst ies))).
  - (* Eapp *)
    rename l into es, l0 into er, l1 into anns.
    clear He.
    destruct (find_node i G) as [n|].
    destruct (Nat.eq_dec (length (List.map fst n.(n_out))) (length anns)) as [<-|].
    2,3: apply CTE, (nprod_const _ errTy').
    (* dénotation du nœud *)
    (* pose (f := PROJ _ i @_ FST _ _ @_ FST _ _ : ctx -C-> FI' i). *)
    (* pose (ss := kdenot_exps_ kdenot_exp_ es). *)
    (* pose (rs := kdenot_exps_ kdenot_exp_ er). *)
    (* FIXME: reset !! *)
    pose (ss := kdenot_exps_ kdenot_exp_ es).
    pose (f := PROJ _ i @_ FST _ _ @_ FST _ _ : ctx -C-> FI' i).
    refine
      (np_of_env' (List.map fst (n_out n)) @_
         (f @2_ ID _ ) (env_of_np' (idents (n_in n)) @_ ss)).
    (* refine *)
    (*   (np_of_env (List.map fst (n_out n)) @_ *)
    (*      (sreset @3_ f) (sbools_of @_ rs) (env_of_np (idents (n_in n)) @_ ss)). *)
Defined.

Definition kdenot_exp (ins : list ident) (e : exp) :
  (* (nodes * inputs * env) -> streams *)
  Dprodi FI' -C-> DS_prod SI' -C-> DS_prod SI' -C-> nprod (numstreams e) :=
  curry (curry (kdenot_exp_ ins e)).

Definition kdenot_exps (ins : list ident) (es : list exp) :
  Dprodi FI' -C-> DS_prod SI' -C-> DS_prod SI' -C-> nprod (list_sum (List.map numstreams es)) :=
  curry (curry (kdenot_exps_ (kdenot_exp_ ins) es)).

Lemma kdenot_exps_eq :
  forall ins e es envG envI env,
    kdenot_exps ins (e :: es) envG envI env
    = nprod_app (kdenot_exp ins e envG envI env) (kdenot_exps ins es envG envI env).
Proof.
  reflexivity.
Qed.

Lemma forall_kdenot_exps :
  forall (P : DS (errv value) -> Prop) ins es envG envI env,
    forall_nprod P (kdenot_exps ins es envG envI env)
    <-> Forall (fun e => forall_nprod P (kdenot_exp ins e envG envI env)) es.
Proof.
  induction es; intros; simpl; split; auto.
  - intro Hs. setoid_rewrite kdenot_exps_eq in Hs.
    apply app_forall_nprod in Hs as [].
    constructor; auto.
    now apply IHes.
  - intro Hs. inv Hs.
    setoid_rewrite kdenot_exps_eq.
    apply forall_nprod_app; auto.
    now apply IHes.
Qed.

Definition kdenot_expss {A} (ins : list ident) (ess : list (A * list exp)) (n : nat) :
  Dprodi FI' -C-> DS_prod SI' -C-> DS_prod SI' -C->
  @nprod (@nprod (DS (errv value)) n) (length ess) :=
  curry (curry (kdenot_expss_ (kdenot_exp_ ins) ess n)).

Lemma kdenot_expss_eq :
  forall A ins (x : A) es ess envG envI env n,
    kdenot_expss ins ((x,es) :: ess) n envG envI env
    = match Nat.eq_dec (list_sum (List.map numstreams es)) n with
      | left eqn =>
          nprod_cons
            (eq_rect _ nprod (kdenot_exps ins es envG envI env) _ eqn)
            (kdenot_expss ins ess n envG envI env)
      | _ => 0
      end.
Proof.
  intros.
  unfold kdenot_expss, kdenot_expss_, kdenot_exps at 1.
  simpl (list_rect _ _ _ _).
  generalize (kdenot_exps_ (kdenot_exp_ ins) es); intro.
  cases; auto.
  destruct e; cases.
Qed.

Lemma kdenot_expss_nil :
  forall A ins n envG envI env,
    @kdenot_expss A ins [] n envG envI env == 0.
Proof.
  reflexivity.
Qed.

Lemma forall_kdenot_expss :
  forall A ins (ess : list (A * list exp)) n envG envI env (P : nprod n -> Prop),
    Forall (fun es =>
              match Nat.eq_dec (list_sum (List.map numstreams es)) n with
              | left eqn =>
                  P (eq_rect _ nprod (kdenot_exps ins es envG envI env) n eqn)
              | _ => P 0
              end) (List.map snd ess) ->
    forall_nprod P (kdenot_expss ins ess n envG envI env).
Proof.
  induction ess as [|[]]; intros * Hf; inv Hf.
  - simpl; auto.
  - rewrite kdenot_expss_eq.
    unfold eq_rect in *.
    cases; eauto using forall_nprod_cons, forall_nprod_bot.
Qed.

Lemma forall_forall_kdenot_expss_ :
  forall A ins (ess : list (A * list exp)) n envG envI env (P : DS (errv value) -> Prop),
    P 0 ->
    Forall (fun es => forall_nprod P (kdenot_exps ins (snd es) envG envI env)) ess ->
    forall_nprod (forall_nprod P) (kdenot_expss ins ess n envG envI env).
Proof.
  induction ess as [|[]]; intros * Herr Hf; inv Hf.
  - simpl; auto.
  - rewrite kdenot_expss_eq.
    unfold eq_rect in *.
    cases; eauto using forall_nprod_cons, forall_nprod_bot.
Qed.

Lemma forall_forall_kdenot_expss :
  forall A ins (ess : list (A * list exp)) n envG envI env (P : DS (errv value) -> Prop),
    Forall (fun es => length (annots (snd es)) = n) ess ->
    Forall (fun es => forall_nprod P (kdenot_exps ins (snd es) envG envI env)) ess ->
    forall_nprod (forall_nprod P) (kdenot_expss ins ess n envG envI env).
Proof.
  induction ess as [|[]]; intros * Hlen Hf; inv Hf.
  - simpl; auto.
  - rewrite kdenot_expss_eq.
    inv Hlen.
    unfold eq_rect in *.
    cases; eauto using forall_nprod_cons.
    rewrite annots_numstreams in *; contradiction.
Qed.

Lemma Forall_kdenot_expss :
  forall A P ins (es : list (A * list exp)) n envG envI env,
    Forall (fun es => length (annots (snd es)) = n) es ->
    forall_nprod (forall_nprod P) (kdenot_expss ins es n envG envI env)
    <-> Forall (fun l => Forall (fun e => forall_nprod P (kdenot_exp ins e envG envI env)) l) (List.map snd es).
Proof.
  clear.
  induction es as [|[i es] ess]; intros * Hl.
  - repeat constructor.
  - inv Hl.
    rewrite kdenot_expss_eq.
    unfold eq_rect; cases.
    + (* sans erreurs *)
      simpl (Forall _ _).
      rewrite Forall_cons2.
      rewrite <- (IHess (list_sum (List.map numstreams es))); auto.
      setoid_rewrite forall_nprod_cons_iff.
      now rewrite <- forall_kdenot_exps.
    + now rewrite annots_numstreams in n.
Qed.

Lemma kdenot_exps_nil :
  forall ins envG envI env,
    kdenot_exps ins [] envG envI env = 0.
Proof.
  reflexivity.
Qed.

Lemma kdenot_exps_1 :
  forall ins e envG envI env,
    list_of_nprod (kdenot_exps ins [e] envG envI env)
    = list_of_nprod (kdenot_exp ins e envG envI env).
Proof.
  intros.
  rewrite kdenot_exps_eq.
  setoid_rewrite list_of_nprod_app.
  simpl.
  now rewrite app_nil_r.
Qed.

Definition kdenot_var ins envI env x : DS (errv value) :=
  if mem_ident x ins then envI x else env x.

Lemma kdenot_exp_eq :
  forall ins e envG envI env,
    kdenot_exp ins e envG envI env =
      match e return nprod (numstreams e) with
      | Econst c => DS_const (val (Vscalar (sem_cconst c)))
      | Eenum c _ => DS_const (val (Venum c))
      | Evar x _ => kdenot_var ins envI env x
      | Eunop op e an =>
          let se := kdenot_exp ins e envG envI env in
          match numstreams e as n return nprod n -> nprod 1 with
          | 1 => fun se =>
              match typeof e with
              | [ty] => kunop (fun v => sem_unop op v ty) se
              | _ => errTy'
              end
          | _ => fun _ => errTy'
          end se
      | Ebinop op e1 e2 an =>
          let se1 := kdenot_exp ins e1 envG envI env in
          let se2 := kdenot_exp ins e2 envG envI env in
          match numstreams e1 as n1, numstreams e2 as n2
                return nprod n1 -> nprod n2 -> nprod 1 with
          | 1,1 => fun se1 se2 =>
               match typeof e1, typeof e2 with
               | [ty1],[ty2] => kbinop (fun v1 v2 => sem_binop op v1 ty1 v2 ty2) se1 se2
               | _,_ => errTy'
               end
          | _,_ => fun _ _ => errTy'
          end se1 se2
      | Efby e0s es an =>
          let s0s := kdenot_exps ins e0s envG envI env in
          let ss := kdenot_exps ins es envG envI env in
          let n := (list_sum (List.map numstreams e0s)) in
          let m := (list_sum (List.map numstreams es)) in
          match Nat.eq_dec m n, Nat.eq_dec n (length an) with
          | left eqm, left eqan =>
              eq_rect _ nprod (lift2 (APP _) s0s (eq_rect _ nprod ss _ eqm)) _ eqan
          | _, _ => nprod_const _ errTy'
          end
      | Ewhen es (x,_) k (tys,_) =>
          let ss := kdenot_exps ins es envG envI env in
          match Nat.eq_dec (list_sum (List.map numstreams es)) (length tys) with
          | left eqn =>
              eq_rect _ nprod (llift (kwhenv k) ss (kdenot_var ins envI env x)) _ eqn
          | _ => nprod_const _ errTy'
          end
      | Emerge (x,_) ies (tys,_) =>
          let ss := kdenot_expss ins ies (length tys) envG envI env in
          let ss := eq_rect_r nprod ss (length_map _ _) in
          lift_nprod (kmergev (List.map fst ies) (kdenot_var ins envI env x)) ss
      | Ecase ec ies None (tys,_) =>
          let ss := kdenot_expss ins ies (length tys) envG envI env in
          let ss := eq_rect_r nprod ss (length_map _ _) in
          let cs := kdenot_exp ins ec envG envI env in
          match numstreams ec as n return nprod n -> _ with
          | 1 => fun cs => lift_nprod (kcasev (List.map fst ies) cs) ss
          | _ => fun _ => nprod_const _ errTy'
          end cs
      | Ecase ec ies (Some eds) (tys,_) =>
          let ss := kdenot_expss ins ies (length tys) envG envI env in
          let ss := eq_rect_r nprod ss (length_map _ _) in (* branches *)
          let cs := kdenot_exp ins ec envG envI env in (* condition *)
          let ds := kdenot_exps ins eds envG envI env in (* défaut *)
          match numstreams ec as n, Nat.eq_dec (list_sum (List.map numstreams eds)) (length tys) return nprod n -> _ with
          | 1, left eqm =>
              fun cs => lift_nprod (kcase_defv (List.map fst ies) cs)
                       (nprod_cons (eq_rect _ nprod ds _ eqm) ss)
          | _,_ => fun _ => nprod_const _ errTy'
          end cs
      | Eapp f es er an =>
          let ss := kdenot_exps ins es envG envI env in
          let rs := kdenot_exps ins er envG envI env in
          match find_node f G with
          | Some n =>
              match Nat.eq_dec (length (List.map fst n.(n_out))) (length an) with
              | left eqan =>
                  eq_rect _ nprod
                    (np_of_env' (List.map fst n.(n_out)) (envG f (env_of_np' (idents n.(n_in)) ss)))
                    _ eqan
              | _ => nprod_const _ errTy'
              end
          | _ => nprod_const _ errTy'
          end
      | _ => 0
      end.
Proof.
  (* Le système se sent obligé de dérouler deux fois [kdenot_exp_] lors
     d'un appel à [unfold] et c'est très pénible.
     Cette tactique permet de le renrouler. *)
  Ltac fold_kdenot_exps_ ins :=
    repeat
      match goal with
      | |- context [ kdenot_exps_ ?A ] =>
          change A with (kdenot_exp_ ins)
      | |- context [ kdenot_expss_ ?A ] =>
          change A with (kdenot_exp_ ins)
      end.

  (* On doit souvent abstraire la définition des sous-flots
     pour pouvoir détruire les prédicats d'égalité sous les [eq_rect] etc.
     Cette tactique le fait automatiquement. *)
  Ltac gen_kdenot_sub_exps :=
    repeat
      match goal with
      | |- context [ kdenot_exp_ ?A ?B ] =>
          generalize (kdenot_exp_ A B); intro
      | |- context [ kdenot_exps_ ?A ?B ] =>
          generalize (kdenot_exps_ A B); intro
      | |- context [ kdenot_expss_ ?A ?B ] =>
          generalize (kdenot_expss_ A B); intro
      end.

  destruct e; auto; intros envG envI env.
  - (* Evar *)
    unfold kdenot_exp, kdenot_exp_, kdenot_var at 1.
    cases.
  - (* Eunop *)
    unfold kdenot_exp, kdenot_exp_ at 1.
    fold (kdenot_exp_ ins e).
    generalize (kdenot_exp_ ins e) as ss.
    generalize (numstreams e) as ne.
    destruct ne as [|[]]; intros; auto.
    destruct (typeof e) as [|? []]; auto.
  - (* Ebinop *)
    unfold kdenot_exp, kdenot_exp_ at 1.
    fold (kdenot_exp_ ins e1) (kdenot_exp_ ins e2).
    generalize (kdenot_exp_ ins e1) as ss1.
    generalize (kdenot_exp_ ins e2) as ss2.
    generalize (numstreams e1) as ne1.
    generalize (numstreams e2) as ne2.
    destruct ne1 as [|[]], ne2 as [|[]]; intros; auto.
    destruct (typeof e1) as [|?[]], (typeof e2) as [|?[]]; auto.
  - (* Efby*)
    unfold kdenot_exp, kdenot_exps, kdenot_exp_ at 1.
    fold_kdenot_exps_ ins.
    unfold eq_rect.
    gen_kdenot_sub_exps.
    cases; simpl; cases.
  - (* Ewhen *)
    destruct l0 as (tys,?).
    destruct p as (i,?).
    unfold kdenot_exp, kdenot_exps, kdenot_exp_ at 1.
    fold_kdenot_exps_ ins.
    gen_kdenot_sub_exps.
    unfold kdenot_var, eq_rect.
    cases; simpl; cases.
  - (* Emerge *)
    destruct l0 as (tys,?).
    destruct p as (i,ty).
    unfold kdenot_exp, kdenot_exp_, kdenot_exps, kdenot_expss at 1.
    fold_kdenot_exps_ ins.
    gen_kdenot_sub_exps.
    unfold kdenot_var, eq_rect_r, eq_rect, eq_sym.
    cases.
  - (* Ecase *)
    destruct l0 as (tys,?).
    destruct o.
    + (* defaut *)
      unfold kdenot_exp, kdenot_exp_, kdenot_exps, kdenot_expss at 1.
      fold_kdenot_exps_ ins.
      gen_kdenot_sub_exps.
      unfold eq_rect_r, eq_rect, eq_sym.
      cases; simpl; cases.
    + (* total *)
      unfold kdenot_exp, kdenot_exp_, kdenot_exps, kdenot_expss at 1.
      fold_kdenot_exps_ ins.
      gen_kdenot_sub_exps.
      unfold eq_rect_r, eq_rect, eq_sym.
      cases.
  - (* Eapp *)
    rename l into es, l0 into er, l1 into anns, i into f.
    unfold kdenot_exp, kdenot_exps, kdenot_exp_ at 1.
    fold_kdenot_exps_ ins.
    gen_kdenot_sub_exps.
    cases.
    generalize (np_of_env' (List.map fst (n_out n))); intro.
    unfold eq_rect.
    simpl; destruct e.
    rewrite 3 curry_Curry, 3 Curry_simpl, fcont_comp_simpl.
    reflexivity.
Qed.

Global Opaque kdenot_exp.

(* FIXME: comprendre pourquoi on ne peut pas faire les deux en un ?????? *)
Global Add Parametric Morphism ins : (kdenot_var ins)
    with signature @Oeq (DS_prod SI') ==> @eq (DS_prod SI') ==> @eq ident ==> @Oeq (DS (errv value))
      as denot_var_morph1.
Proof.
  unfold kdenot_var.
  intros; cases.
Qed.
Global Add Parametric Morphism ins : (kdenot_var ins)
    with signature @eq (DS_prod SI') ==> @Oeq (DS_prod SI') ==> @eq ident ==> @Oeq (DS (errv value))
      as kdenot_var_morph2.
Proof.
  unfold kdenot_var.
  intros; cases.
Qed.

Lemma kdenot_var_inf :
  forall ins envI env x,
    all_infinite envI ->
    all_infinite env ->
    infinite (kdenot_var ins envI env x).
Proof.
  unfold kdenot_var.
  intros; cases; eauto.
Qed.

Lemma kdenot_var_nins :
  forall ins envI env x,
    ~ In x ins ->
    kdenot_var ins envI env x = env x.
Proof.
  unfold kdenot_var.
  intros.
  destruct (mem_ident x ins) eqn:Hmem; auto.
  now apply mem_ident_spec in Hmem.
Qed.


(** [env_of_np_ext xs ss env] binds xs to ss in env *)
Definition env_of_np_ext (l : list ident) {n} : nprod n -C-> DS_prod SI' -C-> DS_prod SI' :=
  curry (Dprodi_DISTR _ _ _
           (fun x => match mem_nth ident ident_eq_dec l x with
                  | Some n => get_nth n errTy' @_ FST _ _
                  | None => PROJ _ x @_ SND _ _
                  end)).

Lemma env_of_np_ext_eq :
  forall l n (np : nprod n) env x,
    env_of_np_ext l np env x
    = match mem_nth ident ident_eq_dec l x with
      | Some n => get_nth n errTy' np
      | None => env x
      end.
Proof.
  unfold env_of_np_ext.
  intros.
  autorewrite with cpodb.
  cases.
Qed.

(* signature : envG -> envI -> env -> env_acc -> env
    on utilise les 4 premiers arguments pour évaluer les expressions,
    et on ajoute les nouvelles associations à l'accumulateur *)
Definition kdenot_block (ins : list ident) (b : block) :
  Dprodi FI' -C-> DS_prod SI' -C-> DS_prod SI' -C-> DS_prod SI' -C-> DS_prod SI' :=
  curry (curry (curry
    match b with
    | Beq (xs,es) => ((env_of_np_ext xs @2_
                        uncurry (uncurry (kdenot_exps ins es)) @_ FST _ _)
                       (SND _ _))
    | _ =>  SND _ _ (* garder l'accumulateur *)
    end)).

Lemma kdenot_block_eq :
  forall ins b envG envI env env_acc,
    kdenot_block ins b envG envI env env_acc
    = match b with
      | Beq (xs,es) => env_of_np_ext xs (kdenot_exps ins es envG envI env) env_acc
      | _ => env_acc
      end.
Proof.
  unfold kdenot_block; intros; cases.
Qed.

(* un genre de (fold kdenot_block) sur blks *)
Definition kdenot_blocks (ins : list ident) (blks : list block) :
  (*  envG -> envI -> env -> env *)
  Dprodi FI' -C-> DS_prod SI' -C-> DS_prod SI' -C-> DS_prod SI'.
  apply curry, curry.
  revert blks; fix kdenot_blocks 1.
  intros [| blk blks].
  - apply CTE, 0.
  - refine ((ID _ @2_ uncurry (uncurry (kdenot_block ins blk))) (kdenot_blocks blks)).
Defined.

Lemma kdenot_blocks_eq :
  forall ins envG envI env blks,
    kdenot_blocks ins blks envG envI env
    = fold_right (fun blk => kdenot_block ins blk envG envI env) 0 blks.
Proof.
  induction blks; simpl; auto.
  unfold kdenot_blocks at 1.
  setoid_rewrite <- IHblks.
  reflexivity.
Qed.

Corollary kdenot_blocks_eq_cons :
  forall ins envG envI env blk blks,
    kdenot_blocks ins (blk :: blks) envG envI env
    = kdenot_block ins blk envG envI env
        (kdenot_blocks ins blks envG envI env).
Proof.
  reflexivity.
Qed.

Definition kdenot_top_block (ins : list ident) (b : block) :
  (* envG -> envI -> env -> env *)
  Dprodi FI' -C-> DS_prod SI' -C-> DS_prod SI' -C-> DS_prod SI' :=
  match b with
  | Blocal (Scope _ blks) => kdenot_blocks ins blks
  | _ => 0
  end.

Lemma kdenot_top_block_eq :
  forall ins blk envG envI env,
    kdenot_top_block ins blk envG envI env
    = match blk with
      | Blocal (Scope _ blks) => kdenot_blocks ins blks envG envI env
      | _ => 0
      end.
Proof.
  intros.
  unfold kdenot_top_block.
  cases.
Qed.

Definition kdenot_node (n : @node PSyn Prefs) :
  (* envG -> envI -> env -> env *)
  Dprodi FI' -C-> DS_prod SI' -C-> DS_prod SI' -C-> DS_prod SI'.
  apply curry.
  refine ((kdenot_top_block (List.map fst n.(n_in)) n.(n_block) @2_ _) _).
  - exact (FST _ _). (* envG *)
  - exact (SND _ _). (* envI *)
Defined.

Lemma kdenot_node_eq : forall n envG envI,
    let ins := List.map fst n.(n_in) in
    kdenot_node n envG envI = kdenot_top_block ins n.(n_block) envG envI.
Proof.
  reflexivity.
Qed.

End KDenot_node.

Ltac gen_sub_exps :=
  repeat match goal with
  | |- context [ ?f1 (?f2 (?f3 (kdenot_expss ?e1 ?e2 ?e3 ?e4) ?e5) ?e6) ?e7 ] =>
      generalize (f1 (f2 (f3 (kdenot_expss e1 e2 e3 e4) e5) e6) e7)
  | |- context [ ?f1 (?f2 (?f3 (kdenot_exps ?e1 ?e2 ?e3) ?e4) ?e5) ?e6 ] =>
      generalize (f1 (f2 (f3 (kdenot_exps e1 e2 e3) e4) e5) e6)
  | |- context [ ?f1 (?f2 (?f3 (kdenot_exp ?e1 ?e2 ?e3) ?e4) ?e5) ?e6 ] =>
      generalize (f1 (f2 (f3 (kdenot_exp e1 e2 e3) e4) e5) e6)
    end.

Section KGlobal.

  Definition kdenot_global_ {PSyn Prefs} (G : @global PSyn Prefs) : Dprodi FI' -C-> Dprodi FI'.
    apply Dprodi_DISTR; intro f.
    destruct (find_node f G).
    - exact (curry (FIXP _ @_ (kdenot_node G n @2_ FST _ _) (SND _ _))).
    - apply CTE, CTE, 0.
  Defined.

  Lemma kdenot_global_eq :
    forall {PSyn Prefs},
    forall (G : @global PSyn Prefs) envG f envI,
      kdenot_global_ G envG f envI =
        match find_node f G with
        | Some n => FIXP _ (kdenot_node G n envG envI)
        | None => 0
        end.
  Proof.
    intros.
    unfold kdenot_global_.
    autorewrite with cpodb.
    cases.
  Qed.

  Definition kdenot_global {PSyn Prefs} (G: @global PSyn Prefs) : Dprodi FI' :=
    FIXP _ (kdenot_global_ G).

End KGlobal.

End LKAHN.

Module LKahnFun
  (Ids   : IDS)
  (Op    : OPERATORS)
  (OpAux : OPERATORS_AUX Ids Op)
  (Cks   : CLOCKS        Ids Op OpAux)
  (Senv  : STATICENV     Ids Op OpAux Cks)
  (Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
  (Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
<: LKAHN Ids Op OpAux Cks Senv Syn Lord.
  Include LKAHN Ids Op OpAux Cks Senv Syn Lord.
End LKahnFun.
