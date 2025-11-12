From Coq Require Import BinPos List.

From Velus Require Import Common Ident Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LSemantics Lustre.LOrdered.
From Velus Require Import Lustre.Denot.Cpo.
From Velus.Lustre.Denot.Cpo Require Import Cpo_streams_type.

Close Scope equiv_scope. (* conflicting notation "==" *)
Import ListNotations.

Require Import CommonList2 Kfuns Kenv Kauto.

(** * Une sémantique Kahnienne pour Vélus *)
Module Type LKAHN
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn).


Section KDenot_node.

Context {PSyn : list decl -> block -> Prop}.
Context {Prefs : PS.t}.
Variable (G : @global PSyn Prefs).

Notation SEnv := (@env ident (errv value)).
(* Notation id_st_eqb := (@id_st_eqb ident id_st_dec). *)
Definition FEnv := Dprodi (fun f:ident => (SEnv -C-> SEnv)).

Definition errTy' : DS (errv value) := DS_const (err' error_Ty').

Definition np_of_env' (l : list ident) : SEnv -C-> @nprod (DS (errv value)) (length l).
  induction l as [| x l].
  - apply CTE, 0.
  - exact ((nprod_cons @2_ PROJ _ (Var x)) IHl).
Defined.

(* FIXME: pour l'instant, on ne met que les Var dedans *)
Definition env_of_np' (l : list ident) {n} : nprod n -C-> SEnv :=
  Dprodi_DISTR _ _ _
    (fun x : key =>
       match x with
       | Var x => match mem_nth ident ident_eq_dec l x with
                 | Some n => get_nth n errTy'
                 | None => 0
                 end
       | Last x => 0
       end).

(* l'opérateur kwhen spécialisé aux Velus.Op.value *)
(* TODO: peut-on utiliser [Kauto.wheni] à la place ? *)
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
      Dprod FEnv SEnv -C->
      @nprod (DS (errv value)) (numstreams e).

  Definition kdenot_exps_ (es : list exp) :
    Dprod FEnv SEnv -C->
    @nprod (DS (errv value)) (list_sum (List.map numstreams es)).
    induction es as [|a].
    + exact 0.
    + exact ((nprod_app @2_ (kdenot_exp_ a)) IHes).
  Defined.
  Definition kdenot_expss_ {A} (ess : list (A * list exp)) (n : nat) :
    Dprod FEnv SEnv -C->
    @nprod (@nprod (DS (errv value)) n) (length ess).
    induction ess as [|[? es]].
    + exact 0.
    + destruct (Nat.eq_dec (list_sum (List.map numstreams es)) n) as [<-|].
      * exact ((nprod_cons @2_ (kdenot_exps_ es)) IHess).
      * exact 0.
  Defined.

End KDenot_exps.


(** Casts a [nprod] into a single stream *)
(* TODO: move *)
Definition cast_1 {n} : @nprod (DS (errv value)) n -C-> DS (errv value) :=
  match n as m return nprod m -C-> @nprod (DS (errv value)) 1 with
  | 1 => ID _
  | _ => CTE _ _ errTy'
  end.


Definition kdenot_exp_
  (e : exp) :
  (* (nodes * env) -> streams *)
  Dprod FEnv SEnv -C->
  @nprod (DS (errv value)) (numstreams e).

  set (ctx := Dprod _ _).
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
    refine (PROJ _ (Var i) @_ (SND _ _)).
  - (* Elast *)
    refine (PROJ _ (Last i) @_ (SND _ _)).
  - (* Eunop *)
    destruct (typeof e0) as [|ty []].
    1,3: apply CTE, errTy'.
    refine (kunop (fun v => sem_unop u v ty) @_ cast_1 @_ kdenot_exp_ e0).
  - (* Ebinop *)
    destruct (typeof e0_1) as [|ty1 []], (typeof e0_2) as [|ty2 []].
    1-4,6-9: apply CTE, errTy'.
    refine ((kbinop (fun v1 v2 => sem_binop b v1 ty1 v2 ty2) @2_
               (cast_1 @_ kdenot_exp_ e0_1))
              (cast_1 @_ kdenot_exp_ e0_2)).
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
    (* car en sémantique de Kahn, arrow x y = app x (rem y) *)
    exact ((lift2 (APP _) @2_ s0s) (lift (REM _) @_ ss)).
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
    exact ((llift (kwhenv e0) @2_ ss) (PROJ _ (Var i) @_ SND _ _)).
  - (* Emerge *)
    rename l into ies.
    destruct l0 as (tys,ck).
    destruct p as [i ty].
    (* on calcule (length tys) flots pour chaque liste de sous-expressions *)
    pose (ses := kdenot_expss_ kdenot_exp_ ies (length tys)).
    rewrite <- (length_map fst) in ses.
    exact ((lift_nprod @_ (kmergev (List.map fst ies)) @2_ PROJ _ (Var i) @_ SND _ _) ses).
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
    pose (f := PROJ _ i @_ FST _ _ : ctx -C-> _).
    refine
      (np_of_env' (List.map fst (n_out n)) @_
         (f @2_ ID _ ) (env_of_np' (idents (n_in n)) @_ ss)).
    (* refine *)
    (*   (np_of_env (List.map fst (n_out n)) @_ *)
    (*      (sreset @3_ f) (sbools_of @_ rs) (env_of_np (idents (n_in n)) @_ ss)). *)
Defined.

Definition kdenot_exp (e : exp) :
  (* (nodes * env) -> streams *)
  FEnv -C-> SEnv -C-> nprod (numstreams e) :=
  curry (kdenot_exp_ e).

Definition kdenot_exps (es : list exp) :
  FEnv -C-> SEnv -C-> nprod (list_sum (List.map numstreams es)) :=
  curry (kdenot_exps_ kdenot_exp_ es).

Lemma kdenot_exps_eq :
  forall e es envG env,
    kdenot_exps (e :: es) envG env
    = nprod_app (kdenot_exp e envG env) (kdenot_exps es envG env).
Proof.
  reflexivity.
Qed.

Lemma forall_kdenot_exps :
  forall (P : DS (errv value) -> Prop) es envG env,
    forall_nprod P (kdenot_exps es envG env)
    <-> Forall (fun e => forall_nprod P (kdenot_exp e envG env)) es.
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

Definition kdenot_expss {A} (ess : list (A * list exp)) (n : nat) :
  FEnv -C-> SEnv -C->
  @nprod (@nprod (DS (errv value)) n) (length ess) :=
  curry (kdenot_expss_ kdenot_exp_ ess n).

Lemma kdenot_expss_eq :
  forall A (x : A) es ess envG env n,
    kdenot_expss ((x,es) :: ess) n envG env
    = match Nat.eq_dec (list_sum (List.map numstreams es)) n with
      | left eqn =>
          nprod_cons
            (eq_rect _ nprod (kdenot_exps es envG env) _ eqn)
            (kdenot_expss ess n envG env)
      | _ => 0
      end.
Proof.
  intros.
  unfold kdenot_expss, kdenot_expss_, kdenot_exps at 1.
  simpl (list_rect _ _ _ _).
  generalize (kdenot_exps_ kdenot_exp_ es); intro.
  cases; auto.
  destruct e; cases.
Qed.

Lemma kdenot_expss_nil :
  forall A n envG env,
    @kdenot_expss A [] n envG env == 0.
Proof.
  reflexivity.
Qed.

Lemma forall_kdenot_expss :
  forall A (ess : list (A * list exp)) n envG env (P : nprod n -> Prop),
    Forall (fun es =>
              match Nat.eq_dec (list_sum (List.map numstreams es)) n with
              | left eqn =>
                  P (eq_rect _ nprod (kdenot_exps es envG env) n eqn)
              | _ => P 0
              end) (List.map snd ess) ->
    forall_nprod P (kdenot_expss ess n envG env).
Proof.
  induction ess as [|[]]; intros * Hf; inv Hf.
  - simpl; auto.
  - rewrite kdenot_expss_eq.
    unfold eq_rect in *.
    cases; eauto using forall_nprod_cons, forall_nprod_bot.
Qed.

Lemma forall_forall_kdenot_expss_ :
  forall A (ess : list (A * list exp)) n envG env (P : DS (errv value) -> Prop),
    P 0 ->
    Forall (fun es => forall_nprod P (kdenot_exps (snd es) envG env)) ess ->
    forall_nprod (forall_nprod P) (kdenot_expss ess n envG env).
Proof.
  induction ess as [|[]]; intros * Herr Hf; inv Hf.
  - simpl; auto.
  - rewrite kdenot_expss_eq.
    unfold eq_rect in *.
    cases; eauto using forall_nprod_cons, forall_nprod_bot.
Qed.

Lemma forall_forall_kdenot_expss :
  forall A (ess : list (A * list exp)) n envG env (P : DS (errv value) -> Prop),
    Forall (fun es => length (annots (snd es)) = n) ess ->
    Forall (fun es => forall_nprod P (kdenot_exps (snd es) envG env)) ess ->
    forall_nprod (forall_nprod P) (kdenot_expss ess n envG env).
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
  forall A P (es : list (A * list exp)) n envG env,
    Forall (fun es => length (annots (snd es)) = n) es ->
    forall_nprod (forall_nprod P) (kdenot_expss es n envG env)
    <-> Forall (fun l => Forall (fun e => forall_nprod P (kdenot_exp e envG env)) l) (List.map snd es).
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
  forall envG env,
    kdenot_exps [] envG env = 0.
Proof.
  reflexivity.
Qed.

Lemma kdenot_exps_1 :
  forall e envG env,
    list_of_nprod (kdenot_exps [e] envG env)
    = list_of_nprod (kdenot_exp e envG env).
Proof.
  intros.
  rewrite kdenot_exps_eq.
  setoid_rewrite list_of_nprod_app.
  simpl.
  now rewrite app_nil_r.
Qed.

Lemma kdenot_exp_eq :
  forall e envG env,
    kdenot_exp e envG env =
      match e return nprod (numstreams e) with
      | Econst c => DS_const (val (Vscalar (sem_cconst c)))
      | Eenum c _ => DS_const (val (Venum c))
      | Evar x _ => env (Var x)
      | Elast x _ => env (Last x)
      | Eunop op e an =>
          let se := cast_1 (kdenot_exp e envG env) in
          match typeof e with
          | [ty] => kunop (fun v => sem_unop op v ty) se
          | _ => errTy'
          end
      | Ebinop op e1 e2 an =>
          let se1 := cast_1 (kdenot_exp e1 envG env) in
          let se2 := cast_1 (kdenot_exp e2 envG env) in
          match typeof e1, typeof e2 with
          | [ty1],[ty2] => kbinop (fun v1 v2 => sem_binop op v1 ty1 v2 ty2) se1 se2
          | _,_ => errTy'
          end
      | Eextcall _ _ _ => 0
      | Efby e0s es an =>
          let s0s := kdenot_exps e0s envG env in
          let ss := kdenot_exps es envG env in
          let n := (list_sum (List.map numstreams e0s)) in
          let m := (list_sum (List.map numstreams es)) in
          match Nat.eq_dec m n, Nat.eq_dec n (length an) with
          | left eqm, left eqan =>
              eq_rect _ nprod (lift2 (APP _) s0s (eq_rect _ nprod ss _ eqm)) _ eqan
          | _, _ => nprod_const _ errTy'
          end
      | Earrow e0s es an =>
          let s0s := kdenot_exps e0s envG env in
          let ss := kdenot_exps es envG env in
          let n := (list_sum (List.map numstreams e0s)) in
          let m := (list_sum (List.map numstreams es)) in
          match Nat.eq_dec m n, Nat.eq_dec n (length an) with
          | left eqm, left eqan =>
              eq_rect _ nprod (lift2 (APP _) s0s (eq_rect _ nprod (lift (REM _) ss) _ eqm)) _ eqan
          | _, _ => nprod_const _ errTy'
          end
      | Ewhen es (x,_) k (tys,_) =>
          let ss := kdenot_exps es envG env in
          match Nat.eq_dec (list_sum (List.map numstreams es)) (length tys) with
          | left eqn =>
              eq_rect _ nprod (llift (kwhenv k) ss (env (Var x))) _ eqn
          | _ => nprod_const _ errTy'
          end
      | Emerge (x,_) ies (tys,_) =>
          let ss := kdenot_expss ies (length tys) envG env in
          let ss := eq_rect_r nprod ss (length_map _ _) in
          lift_nprod (kmergev (List.map fst ies) (env (Var x))) ss
      | Ecase ec ies None (tys,_) =>
          let ss := kdenot_expss ies (length tys) envG env in
          let ss := eq_rect_r nprod ss (length_map _ _) in
          let cs := kdenot_exp ec envG env in
          match numstreams ec as n return nprod n -> _ with
          | 1 => fun cs => lift_nprod (kcasev (List.map fst ies) cs) ss
          | _ => fun _ => nprod_const _ errTy'
          end cs
      | Ecase ec ies (Some eds) (tys,_) =>
          let ss := kdenot_expss ies (length tys) envG env in
          let ss := eq_rect_r nprod ss (length_map _ _) in (* branches *)
          let cs := kdenot_exp ec envG env in (* condition *)
          let ds := kdenot_exps eds envG env in (* défaut *)
          match numstreams ec as n, Nat.eq_dec (list_sum (List.map numstreams eds)) (length tys) return nprod n -> _ with
          | 1, left eqm =>
              fun cs => lift_nprod (kcase_defv (List.map fst ies) cs)
                       (nprod_cons (eq_rect _ nprod ds _ eqm) ss)
          | _,_ => fun _ => nprod_const _ errTy'
          end cs
      | Eapp f es er an =>
          let ss := kdenot_exps es envG env in
          let rs := kdenot_exps er envG env in
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
      end.
Proof.
  (* Le système se sent obligé de dérouler deux fois [kdenot_exp_] lors
     d'un appel à [unfold] et c'est très pénible.
     Cette tactique permet de le renrouler. *)
  Ltac fold_kdenot_exps :=
    repeat
      match goal with
      | |- context [ kdenot_exps_ ?A ] =>
          change A with kdenot_exp_
      | |- context [ kdenot_expss_ ?A ] =>
          change A with kdenot_exp_
      end.

  (* On doit souvent abstraire la définition des sous-flots
     pour pouvoir détruire les prédicats d'égalité sous les [eq_rect] etc.
     Cette tactique le fait automatiquement. *)
  Ltac gen_kdenot_sub_exps :=
    repeat
      match goal with
      | |- context [ kdenot_exp_ ?A ] =>
          generalize (kdenot_exp_ A); intro
      | |- context [ kdenot_exps_ ?A ?B ] =>
          generalize (kdenot_exps_ A B); intro
      | |- context [ kdenot_expss_ ?A ?B ] =>
          generalize (kdenot_expss_ A B); intro
      end.

  destruct e; auto; intros envG env.
  - (* Eunop *)
    unfold kdenot_exp, kdenot_exp_ at 1.
    fold (kdenot_exp_ e).
    generalize (kdenot_exp_ e) as ss.
    generalize (numstreams e) as ne.
    destruct (typeof e) as [|? []]; auto.
  - (* Ebinop *)
    unfold kdenot_exp, kdenot_exp_ at 1.
    fold (kdenot_exp_ e1) (kdenot_exp_ e2).
    generalize (kdenot_exp_ e1) as ss1.
    generalize (kdenot_exp_ e2) as ss2.
    destruct (typeof e1) as [|?[]], (typeof e2) as [|?[]]; auto.
  - (* Efby *)
    unfold kdenot_exp, kdenot_exps, kdenot_exp_ at 1.
    fold_kdenot_exps.
    unfold eq_rect.
    gen_kdenot_sub_exps.
    cases; simpl; cases.
  - (* Earrow *)
    unfold kdenot_exp, kdenot_exps, kdenot_exp_ at 1.
    fold_kdenot_exps.
    unfold eq_rect.
    gen_kdenot_sub_exps.
    cases; simpl; cases.
  - (* Ewhen *)
    destruct l0 as (tys,?).
    destruct p as (i,?).
    unfold kdenot_exp, kdenot_exps, kdenot_exp_ at 1.
    fold_kdenot_exps.
    gen_kdenot_sub_exps.
    unfold eq_rect.
    cases; simpl; cases.
  - (* Emerge *)
    destruct l0 as (tys,?).
    destruct p as (i,ty).
    unfold kdenot_exp, kdenot_exp_, kdenot_exps, kdenot_expss at 1.
    fold_kdenot_exps.
    gen_kdenot_sub_exps.
    unfold eq_rect_r, eq_rect, eq_sym.
    cases.
  - (* Ecase *)
    destruct l0 as (tys,?).
    destruct o.
    + (* defaut *)
      unfold kdenot_exp, kdenot_exp_, kdenot_exps, kdenot_expss at 1.
      fold_kdenot_exps.
      gen_kdenot_sub_exps.
      unfold eq_rect_r, eq_rect, eq_sym.
      cases; simpl; cases.
    + (* total *)
      unfold kdenot_exp, kdenot_exp_, kdenot_exps, kdenot_expss at 1.
      fold_kdenot_exps.
      gen_kdenot_sub_exps.
      unfold eq_rect_r, eq_rect, eq_sym.
      cases.
  - (* Eapp *)
    rename l into es, l0 into er, l1 into anns, i into f.
    unfold kdenot_exp, kdenot_exps, kdenot_exp_ at 1.
    fold_kdenot_exps.
    gen_kdenot_sub_exps.
    cases.
    generalize (np_of_env' (List.map fst (n_out n))); intro.
    unfold eq_rect.
    simpl; destruct e.
    rewrite 2 curry_Curry, 2 Curry_simpl, fcont_comp_simpl.
    reflexivity.
Qed.

Global Opaque kdenot_exp.

(** [env_ext_var xs ss env] binds Var(xs) to ss in env *)
Definition env_ext_var (l : list ident) {n} : nprod n -C-> SEnv -C-> SEnv :=
  curry (Dprodi_DISTR _ _ _
           (fun x =>
              match x with
              | Var x =>
                  match mem_nth ident ident_eq_dec l x with
                  | Some n => get_nth n errTy' @_ FST _ _
                  | None => PROJ _ (Var x) @_ SND _ _
                  end
              | Last _ => PROJ _ x @_ SND _ _
              end)).

Lemma env_ext_var_eq :
  forall l n (np : nprod n) env i,
    env_ext_var l np env i =
      match i with
      | Var x => match mem_nth ident ident_eq_dec l x with
                | Some n => get_nth n errTy' np
                | None => env (Var x)
                end
      | Last x => env (Last x)
      end.
Proof.
  unfold env_ext_var.
  intros.
  autorewrite with cpodb.
  cases.
Qed.

(** [env_ext_last xs ss env] binds Last(xs) to ss in env *)
Definition env_ext_last (l : list ident) {n} : nprod n -C-> SEnv -C-> SEnv :=
  curry (Dprodi_DISTR _ _ _
           (fun x =>
              match x with
              | Last x =>
                  match mem_nth ident ident_eq_dec l x with
                  | Some n => get_nth n errTy' @_ FST _ _
                  | None => PROJ _ (Last x) @_ SND _ _
                  end
              | Var _ => PROJ _ x @_ SND _ _
              end)).

Lemma env_ext_last_eq :
  forall l n (np : nprod n) env i,
    env_ext_last l np env i =
      match i with
      | Last x => match mem_nth ident ident_eq_dec l x with
                | Some n => get_nth n errTy' np
                | None => env (Last x)
                end
      | Var x => env (Var x)
      end.
Proof.
  unfold env_ext_last.
  intros.
  autorewrite with cpodb.
  cases.
Qed.

(** union par la gauche de deux environnements *)
Definition union_env (dom : list ident) :
  SEnv -C-> SEnv -C-> SEnv :=
  curry (Dprodi_DISTR _ _ _ (
             fun i => match i with
                   | Var x => if mem_ident x dom
                             then PROJ _ i @_ FST _ _
                             else PROJ _ i @_ SND _ _
                   | Last x => if mem_ident x dom
                              then PROJ _ i @_ FST _ _
                              else PROJ _ i @_ SND _ _
                   end)).

Lemma union_env_simpl :
  forall dom e1 e2 i,
    union_env dom e1 e2 i =
      match i with
      | Var i => if mem_ident i dom then e1 (Var i) else e2 (Var i)
      | Last i => if mem_ident i dom then e1 (Last i) else e2 (Last i)
      end.
Proof.
  unfold union_env; intros.
  autorewrite with cpodb.
  cases.
Qed.

(* TODO: move? *)
Definition tag_of_val (default:enumtag) : errv value -> enumtag :=
  fun v => match v with
        | val (Venum t) => t
        | _ => default
        end.

(* TODO: move *)
Definition assoc_enumtag {A} (x: enumtag) (xs: list (enumtag * A)): option A :=
  match find (fun y => fst y ==b x) xs with
  | Some (_, a) => Some a
  | None => None
  end.


Section KDenot_blocks.

  Hypothesis kdenot_block_ :
    forall b : block, Dprod FEnv SEnv -C-> SEnv.

  (** accumule le résultat des blocs dans la sortie *)
  (* contrairement à dans ma thèse, ce calcul dépend de l'ordre des blocs *)
  Definition kdenot_blocks_ (blks : list block) :
    Dprod FEnv SEnv -C-> SEnv.
    induction blks as [|b].
    + exact (SND _ _).
    + refine ((curry IHblks @2_ FST _ _) (kdenot_block_ b)).
  Defined.

  Lemma kdenot_blocks__simpl :
  forall envG blks env,
    kdenot_blocks_ blks (envG,env) == List.fold_left (fun env b => kdenot_block_ b (envG,env)) blks env.
  Proof.
    induction blks; intros; auto.
    simpl (fold_left _ _).
    rewrite <- IHblks; auto.
  Qed.

End KDenot_blocks.

Definition kswitch {A} := @Kauto.switch ident enumtag Nat.eq_dec A.
Definition auto_weak {A} := @Kauto.auto_weak ident enumtag Nat.eq_dec A.
Definition auto_strong {A} := @Kauto.auto_strong ident enumtag Nat.eq_dec A.

Fixpoint kdenot_block_ (b : block) :
  Dprod FEnv SEnv -C-> SEnv.
  (* TODO: faire la définition directement, sans tactiques ? *)
  (* revert b. *)
  (* fix kdenot_block_ 1. *)
  (* intro b. *)
  refine
  match b with
  (* met à jour les Var associées aux xs *)
  | Beq (xs,es) => (env_ext_var xs @2_ uncurry (kdenot_exps es)) (SND _ _)
  (* met à jour (Last x) dans l'environnement *)
  | Blast x e =>  (@env_ext_last [x] 1 @2_
                    ((APP _ @2_ (cast_1 @_ uncurry (kdenot_exp e)))
                       (PROJ _ (Var x) @_ SND _ _))) (SND _ _)
  | Bswitch ec branches =>
      (* le flot de condition *)
      let cs := MAP (tag_of_val true_tag) @_ cast_1 @_ uncurry (kdenot_exp ec) in
      (* chaque branche définit une fonction *)
      let fs := List.map (fun '(t, Branch _ l) =>
                            (* on ignore les étiquettes de causalité *)
                            (t, kdenot_blocks_ kdenot_block_ l)) branches in
      (kswitch @3_ cs) (Dprodi_DISTR _ _ _
                          (fun i => match assoc_enumtag i fs with
                                 | Some fi => (curry ((curry fi @2_ FST _ _ @_ FST _ _) (SND _ _)))
                                 | None => CTE _ _ 0 (* TODO: plutôt ID ? ou CTE _ error_env ? *)
                                 end))  (SND _ _)
  (* (* version plus jolie mais qui ne passe pas le critère de terminaison... *) *)
  (* | Bswitch ec branches => *)
  (*     let cs := MAP (tag_of_val true_tag) @_ cast_1 @_ uncurry (kdenot_exp ec) in *)
  (*     let f := fun i => match assoc_enumtag i branches with *)
  (*                    | Some (Branch _ l) => (curry ((curry (kdenot_blocks_ kdenot_block_ l) @2_ FST _ _ @_ FST _ _) (SND _ _))) *)
  (*                    | None => CTE _ _ 0 (* TODO: plutôt ID ? ou CTE _ error_env ? *) *)
  (*                    end *)
  (*     in (kswitch @3_ cs) (Dprodi_DISTR _ _ _ f)  (SND _ _) *)

  | Blocal (Scope decls blks) =>
      let vars := List.map fst decls in
      let F := (curry (kdenot_blocks_ kdenot_block_ blks) @2_ FST _ _ @_ FST _ _)
                 ((union_env vars @2_ SND _ _) (SND _ _ @_ FST _ _)) in
      (union_env vars @2_ SND _ _) (FIXP _ @_ curry F)
  | Breset blks e =>                   SND _ _   (* TODO *)
  | Bauto Weak ck (ini, oth) states => SND _ _   (* TODO *)
  | Bauto Strong ck (_, oth) states => SND _ _   (* TODO *)
  end.
Defined.

Definition kdenot_block (b : block) : FEnv -C-> SEnv -C-> SEnv :=
  curry (kdenot_block_ b).

Definition kdenot_blocks (blks : list block) : FEnv -C-> SEnv -C-> SEnv :=
  curry (kdenot_blocks_ kdenot_block_ blks).



Definition kdenot_scope (decls : list decl) (blks : list block) : FEnv -C-> SEnv -C-> SEnv.
Admitted.

(* TODO: commenter *)
Lemma kdenot_scope_eq :
  forall decls blks envG env,
    kdenot_scope decls blks envG env =
      let vars := List.map fst decls in
      let env' := FIXP _ (kdenot_blocks blks envG @_ (union_env vars <___> env)) in
      union_env vars env env'.
Proof.
Admitted.

Definition kdenot_transitions (trans : list transition) :
  FEnv -C-> SEnv -C-> DS (option (enumtag * bool)).
Admitted.

Lemma kdenot_block_eq :
  forall b envG env,
    kdenot_block b envG env
    == match b with
      | Beq (xs,es) => env_ext_var xs (kdenot_exps es envG env) env
      | Blast x e => @env_ext_last [x] 1 (app (cast_1 (kdenot_exp e envG env)) (env (Var x))) env
      | Bswitch ec branches =>
          let cs := map (tag_of_val true_tag) (cast_1 (kdenot_exp ec envG env)) in
          kswitch cs (fun i => match assoc_enumtag i branches with
                            (* ignore causality annotations *)
                            | Some (Branch _ blks) => kdenot_blocks blks envG
                            | None => 0 (* TODO: plutôt ID ? ou CTE _ error_env ? *)
                            end) env
      | Blocal (Scope decls blks) => kdenot_scope decls blks envG env
      | Bauto Strong ck (_, ini) states =>
          let states := List.map (fun '((a,b),c) => (a,c)) states in
          (* le corps et les transitions sont calculés indépendamment *)
          auto_strong ini
            (* corps des états *)
            (fun i => match assoc_enumtag i states with
                   | Some (Branch _ (_, Scope decls (blks, _))) =>
                       kdenot_scope decls blks envG
                   | None => 0
                   end)
            (* transitions *)
            (fun i => match assoc_enumtag i states with
                   (* les transitions fortes sont celles en dehors du scope *)
                   | Some (Branch _ (ts, _)) => kdenot_transitions ts envG
                   | None => 0
                   end)
            env
      | Bauto Weak ck (_, ini) states =>
          let states := List.map (fun '((a,b),c) => (a,c)) states in
          auto_weak ini
            (* corps des états *)
            (fun i => match assoc_enumtag i states with
                   | Some (Branch _ (_, Scope decls (blks, ts))) =>
                       kdenot_scope decls blks envG
                   | None => 0
                   end)
            (* transitions *)
            (fun i => match assoc_enumtag i states with
                   (* les transitions faibles sont dans le scope *)
                   | Some (Branch _ (_, Scope decls (blks, ts))) => kdenot_transitions ts envG
                   | None => 0
                   end)
            env
      | _ => env
      end.
Proof.
  unfold kdenot_block; intros; cases.
  - (* Bswitch *)
    simpl.
    autorewrite with cpodb.
    simpl.
    apply fcont_eq_elim with (f := kswitch _ _).
    apply fcont_stable with (f := kswitch _).
    apply Oprodi_eq_intro; intro i.
    rewrite Dprodi_DISTR_simpl.
    induction l as [|[t [? blks]]]; auto.
    unfold assoc_enumtag. simpl.
    destruct (t ==b i); auto; clear.
    apply Oprodi_eq_intro; auto.
  - (* auto *) simpl. cases.
  - (* Blocal *)
    simpl.
    autorewrite with cpodb.
    apply fcont_stable with (f := union_env _ _).
    apply fcont_stable with (f := FIXP _).
    apply Oprodi_eq_intro; intro i.
    trivial.
Qed.

(* TODO: unifier les notations des lemmes, _eq, _simpl ?? *)
Lemma kdenot_blocks_simpl :
  forall envG env blks,
    kdenot_blocks blks envG env == List.fold_left (fun env b => kdenot_block b envG env) blks env.
Proof.
  unfold kdenot_blocks; intros.
  now rewrite curry_Curry, Curry_simpl, kdenot_blocks__simpl.
Qed.

(* fait l'union des environnements envI et env avant d'évaluer le bloc principal *)
Definition kdenot_node (n : @node PSyn Prefs) :
  FEnv -C-> SEnv -C-> SEnv.
  apply curry.
  refine (FIXP _ @_ _).
  apply curry.
  refine ((kdenot_block (n_block n) @2_ FST _ _ @_ FST _ _)
            ((union_env (idents (n_in n)) @2_ SND _ _ @_ FST _ _) (SND _ _ ))).
Defined.

Lemma kdenot_node_eq : forall n envG envI,
    kdenot_node n envG envI ==
      FIXP _ (kdenot_block (n_block n) envG @_ (union_env (idents (n_in n)) envI)).
Proof.
  unfold kdenot_node; intros.
  autorewrite with cpodb.
  apply fcont_stable.
  apply Oprodi_eq_intro; intro env.
  trivial.
Qed.

End KDenot_node.

Section KGlobal.

  Definition kdenot_global_ {PSyn Prefs} (G : @global PSyn Prefs) : FEnv -C-> FEnv.
    apply Dprodi_DISTR; intro f.
    destruct (find_node f G).
    - apply (kdenot_node G n).
    - apply CTE, 0.
  Defined.

  Lemma kdenot_global_eq :
    forall {PSyn Prefs},
    forall (G : @global PSyn Prefs) envG f,
      kdenot_global_ G envG f ==
        match find_node f G with
        | Some n => kdenot_node G n envG
        | None => 0
        end.
  Proof.
    intros.
    unfold kdenot_global_.
    setoid_rewrite Dprodi_DISTR_simpl.
    cases.
  Qed.

  Definition kdenot_global {PSyn Prefs} (G: @global PSyn Prefs) : FEnv :=
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
