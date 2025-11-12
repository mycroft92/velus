Require Import Cpo.

(** * Environment types of the Kahn semantics *)

Section KENV.

  (** identifier of variables *)
  Context {ident : Type}.

  Inductive key :=
  | Var : ident -> key
  | Last : ident -> key.

  Definition env (A : Type) : cpo := DS_prod (fun _:key => A).

  (** apply a function to every stream of the environment *)
  Definition ext_env {A B : Type} : (DS A -C-> DS B) -C-> (env A -C-> env B).
    apply curry, Dprodi_DISTR; intro i.
    refine ((AP _ _ @2_ FST _ _) (PROJ _ i @_ SND _ _)).
  Defined.

  Lemma ext_env_simpl : forall A B f env i,
      @ext_env A B f env i = f (env i).
  Proof.
    trivial.
  Qed.

  (** state/branch identifier *)
  Context {id_st : Type}.

  Context {id_st_dec : forall i j : id_st, { i = j } + { ~ i = j }}.

  Definition id_st_eqb (i j : id_st) : bool :=
    match id_st_dec i j with left _ => true | _ => false end.

End KENV.
