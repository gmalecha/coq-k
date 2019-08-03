Require Import Coq.Lists.List.
Require Import ExtLib.Data.HList.

Section K.

  Record Signature : Type :=
  { sig_sort : Type
  ; sig_symbol : Type
  ; sig_signature : sig_symbol -> list sig_sort * sig_sort
  }.

  Context {s : Signature}.

  Record Model : Type :=
  { mod_denote_sort : s.(sig_sort) -> Type
  ; mod_denote_symbol : forall sym,
      hlist mod_denote_sort (fst (s.(sig_signature) sym)) ->
      mod_denote_sort (snd (s.(sig_signature) sym)) -> Prop
  ; mod_non_empty : forall s, mod_denote_sort s
  }.

  Inductive Pattern : Type :=
  | Var  (_ : nat)
  | Conj (_ _ : Pattern)
  | Neg  (_ : Pattern)
  | Ex   (_ : s.(sig_sort))   (_ : Pattern)
  | Sym  (_ : s.(sig_symbol)) (_ : list Pattern)

  | Definedness (_ _ : s.(sig_sort)) (_ : Pattern).

  Definition Disj (l r : Pattern) : Pattern :=
    Neg (Conj (Neg l) (Neg r)).
  Definition Impl (l r : Pattern) : Pattern :=
    Disj (Neg l) r.
  Definition Iff (l r : Pattern) : Pattern :=
    Conj (Impl l r) (Impl r l).
  Definition All (t : s.(sig_sort)) (p : Pattern) : Pattern :=
    Neg (Ex t (Neg p)).
  Definition Top (s : s.(sig_sort)) : Pattern :=
    Ex s (Var 0).
  Definition Bot (s : s.(sig_sort)) : Pattern :=
    Neg (Top s).

  Inductive hlist2 {A B : Type} {R : A -> B -> Type} : list A -> list B -> Type :=
    Hnil2 : hlist2 nil nil
  | Hcons2 : forall {x : A} {y : B} {l : list A} {l' : list B},
                   R x y -> hlist2 l l' -> hlist2 (x :: l) (y :: l').
  Arguments hlist2 {_ _} _ _ _.

  Section hlist2_map.
    Context {A B : Type} {R : A -> B -> Type} (F : A -> Type).
    Variable (f : forall a b, R a b -> F a).

    Fixpoint hlist2_map {xs ys} (hs : hlist2 R xs ys) : hlist F xs :=
      match hs with
      | Hnil2 => Hnil
      | Hcons2 v rst => Hcons (f _ _ v) (hlist2_map rst)
      end.
  End hlist2_map.

  Inductive Wf_Pattern (ts : list s.(sig_sort)) (t : s.(sig_sort)) : Pattern -> Type :=
  | WfVar {n} (_ : Some t = nth_error ts n) : Wf_Pattern ts t (Var n)
  | WfConj {p1 p2} (_ : Wf_Pattern ts t p1) (_ : Wf_Pattern ts t p2)
    : Wf_Pattern ts t (Conj p1 p2)
  | WfNeg {p} (_ : Wf_Pattern ts t p)
    : Wf_Pattern ts t (Neg p)
  | WfEx {s p} (_ : Wf_Pattern (s :: ts) t p) : Wf_Pattern ts t (Ex s p)
  | WfSym {f xs} (_ : hlist2 (Wf_Pattern ts) (fst (s.(sig_signature) f)) xs) (_ : t = snd (s.(sig_signature) f))
    : Wf_Pattern ts t (Sym f xs)
  | WfDefinedness {s p} (_ : Wf_Pattern ts s p)
    : Wf_Pattern ts t (Definedness s t p).

  Section denotation.
    Context {m : Model}.

    Definition D (t : s.(sig_sort)) : Type :=
      m.(mod_denote_sort) t -> Prop.

    (* "pointwise extension" *)
    Fixpoint join_hlist {ts} (hs : hlist D ts) : (hlist m.(mod_denote_sort) ts) -> Prop :=
      match hs with
      | Hnil => fun _ => True
      | Hcons P Q => fun x => P (hlist_hd x) /\ join_hlist Q (hlist_tl x)
      end.

    Definition empty {T : Type} (P : T -> Prop) : Prop := forall x, ~P x.

    Proposition prop31 : forall {ts} (hs : hlist D ts),
        (exists t, exists i : Member.member t ts, empty (hlist_get i hs)) ->
        empty (join_hlist hs).
    Proof.
      induction hs; simpl; intros.
      { destruct H. destruct H.
        clear - x0. specialize (Member.member_case x0); simpl. contradiction. }
      { destruct H. destruct H.
        destruct (Member.member_case x0).
        { destruct H0. subst. intro.
          intro. destruct H0. eapply H. eapply H0. }
        { intro. intro. destruct H1.
          eapply IHhs in H2; auto.
          destruct H0. subst. simpl in *.
          do 2 eexists. eapply H. } }
    Qed.

    Proposition prop32 : True.
    Proof. Abort.

    Proposition prop33 : True.
    Proof. Abort.


    Definition Dpure {t} (v : m.(mod_denote_sort) t) : D t :=
      fun x => x = v.
    Definition Dand {t} (P Q : D t) : D t :=
      fun x => P x /\ Q x.
    Definition Dnot {t} (P : D t) : D t :=
      fun x => ~P x.
    Definition Dex {t u} (P : m.(mod_denote_sort) u -> D t) : D t :=
      fun x => exists y, P y x.

    (* "M-valuation" *)
    Definition mvaluation := hlist m.(mod_denote_sort).

    (* (Definition 4) called an "M-valuation extension" *)
    Fixpoint denote_pattern {p : Pattern} {ts t} (wf : Wf_Pattern ts t p)
    : mvaluation ts -> D t.
    destruct wf.
    { refine (fun genv => match e in _ = X return match X with
                                               | Some t => m.(mod_denote_sort) t
                                               | None => unit
                                               end -> D t with
                       | eq_refl => fun x => Dpure x
                       end (hlist_nth genv n)). }
    { refine (fun genv => Dand (denote_pattern _ _ _ wf1 genv) (denote_pattern _ _ _ wf2 genv)). }
    { refine (fun genv => Dnot (denote_pattern _ _ _ wf genv)). }
    { refine (fun genv => Dex (fun y => denote_pattern _ _ _ wf (Hcons y genv))). }
    { refine (fun genv val =>
                exists x, _ (m.(mod_denote_symbol) f x) val /\ _).
      subst.
      refine (fun x=> x).
      eapply join_hlist. 2: eapply x.
      eapply hlist2_map. 2: eapply h.
      intros. eapply denote_pattern. eassumption. eapply genv. }
    { refine (fun genv _ => exists x, denote_pattern _ _ _ wf genv x). }
    Defined.

    Definition Wf ts t : Type := {p : Pattern & Wf_Pattern ts t p }.

    (* (Definition 6) validity *)
    Definition valid {ts t} (p : Wf ts t) : Prop :=
      forall genv : hlist _ ts, forall x, denote_pattern (projT2 p) genv x.

    (* (Definition 6) validity on lists *)
    Definition valids {ts t} (ls : list (Wf ts t)) : Prop :=
      Forall valid ls.

    (* (Definition 6) validity entailment *)
    Definition entails {ts t} (P : list (Wf ts t)) (Q : Wf ts t) : Prop :=
      valids P -> valid Q.

  End denotation.

  (* (Definition 7) "totality" *)
  Definition Totality s s' (p : Pattern) : Pattern :=
    Neg (Definedness s s' (Neg p)).
  Definition Equality s s' (p q : Pattern) : Pattern :=
    (Totality s s' (Iff p q)).
  Definition Containment s s' (p q : Pattern) : Pattern :=
    (Totality s s' (Impl p q)).
  Definition Membership s s' (x p : Pattern) : Pattern :=
    (Definedness s s' (Conj x p)).


  Definition KFunction : Pattern.
  Abort.
  Definition KPFunction : Pattern.
  Abort.
  Definition KConstructor (ls : list s.(sig_symbol)) : Pattern.
  Abort.

  (* why is it not capture avoiding substitution? *)
