From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Codata.Simulation
     Core.ITreeDefinition.

From ITree Require Export
     Eq.Shallow.

Import ITreeNotations.
Local Open Scope itree.

Global Instance Symmetric_bot2 (A : Type) : @Symmetric A bot2.
Proof. auto. Qed.

Global Instance Transitive_bot2 (A : Type) : @Transitive A bot2.
Proof. auto. Qed.

Coercion is_true : bool >-> Sortclass.

Definition void_elim {A : Type} : void -> A := Empty_set_rect (const A).

Section eqit.
  
  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  
  Inductive eqitR' (b1 b2: bool) : itree' E R1 -> itree' E R2 -> forall P : Type, (P -> itree E R1) -> (P -> itree E R2) -> Prop :=
  | EqRet r1 r2
          (REL : RR r1 r2) :
      eqitR' b1 b2 (RetF r1) (RetF r2) void void_elim void_elim
  | EqTau t1 t2:
      eqitR' b1 b2 (TauF t1) (TauF t2) unit (const t1) (const t2)
  | EqVis {X} (e : E X) k1 k2 :
      eqitR' b1 b2 (VisF e k1) (VisF e k2) X k1 k2
  | EqTauL t1 ot2 P k1 k2
           (CHECK : b1)
           (REL : eqitR' b1 b2 (observe t1) ot2 P k1 k2) :
      eqitR' b1 b2 (TauF t1) ot2 P k1 k2
  | EqTauR ot1 t2 P k1 k2
           (CHECK : b2)
           (REL : eqitR' b1 b2 ot1 (observe t2) P k1 k2) :
      eqitR' b1 b2 ot1 (TauF t2) P k1 k2
  .
  Hint Constructors eqitR' : core.

  Definition eqitR b1 b2 t1 t2 := (eqitR' b1 b2 (observe t1) (observe t2)).
  Hint Unfold eqitR : core.
  
  Definition eqit b1 b2 := simulation (eqitR b1 b2) id.
  
  Definition eq_itree := eqit false false.
  Definition eutt := eqit true true.
  Definition euttge := eqit true false.

End eqit.

Hint Constructors eqitR': core.
Hint Unfold eqitR: core.
Hint Unfold eqit: core.
Hint Unfold eq_itree: core.
Hint Unfold eutt: core.
Hint Unfold euttge: core.
Hint Unfold id: core.

Section Homogeneous.
  Context {E : Type -> Type} {R: Type} (RR : R -> R -> Prop).
  
  Lemma Reflexive_eqitR b1 b2 (REFL : Reflexive RR) :
    forall (t : itree E R), exists P k, eqitR RR b1 b2 t t P k k.
  Proof. unfold eqitR; intros t; destruct (observe t); eauto. Qed.

  Lemma Reflexive_eqit b1 b2 (REFL : Reflexive RR) :
    Reflexive (@eqit E R R RR b1 b2).
  Proof.
    eapply Reflexive_simulation.
    eapply eqit_idclo_mono.
    eapply Reflexive_eqitR; eauto.
    eauto.
  Qed.

  Import EqNotations.
  
  Lemma Symmetric_eqitR b1 b2 (SYM : Symmetric RR) : forall x y P x' y',
      @eqitR E R R RR b1 b2 x y P x' y' -> eqitR RR b2 b1 y x P y' x'.
  Proof. unfold eqitR. intros. induction H; eauto. Qed.

  Lemma destruct_trans_ff :
      forall sim x y z,
          simulationF (@eqitR E R R RR false false) id sim x y ->
          simulationF (eqitR RR false false) id sim y z ->
          exists P kx ky kz,
            eqitR RR false false x y P kx ky /\
            eqitR RR false false y z P ky kz /\
            (forall p, sim (kx p) (ky p)) /\
            (forall p, sim (ky p) (kz p)).
  Proof.
    unfold eqitR. intros sim x y z H1 H2.
    destruct H1 as [x y P1 kx ky1 REL1 RELS1];
    remember (observe y);
    destruct REL1;
    destruct H2 as [y z P2 ky2 kz REL2 RELS2];
    remember (observe y);
    destruct REL2.
    all: try congruence; inversion Heqi; subst; repeat esplit; eauto.
    all: destruct (inj_pair2 _ _ _ _ _ H2); try rewrite Heqi; eauto.
  Qed.

  Lemma eqitR_trans (TRANS : Transitive RR) :
    forall x y z P x' y' z',
      @eqitR E R R RR false false x y P x' y' ->
      eqitR RR false false y z P y' z' ->
      eqitR RR false false x z P x' z'.
  Proof.
    unfold eqitR.
    intros x y z P kx ky kz H1 H2.
    remember (observe y) in H1.
    remember (observe y) in H2.
    destruct H1; destruct H2.
    all: try congruence; destruct Heqi; inversion Heqi0; subst.
    - econstructor; eapply TRANS; eauto.
    - eauto.
    - destruct (inj_pair2 _ _ _ _ _ H0); eauto.
  Qed.

  Lemma Transitive_simulation (TRANS : Transitive RR) :
    Transitive (@eq_itree E R R RR).
  Proof.
    eapply Transitive_simulation;
    [eapply destruct_trans_ff | eapply eqitR_trans, TRANS ].
  Qed.

  Lemma eqitR_inv_RetF b1 b2 r ot P kx ky:
    @eqitR' E R R RR b1 b2 (RetF r) ot P kx ky -> eqitR' RR b1 b2 (RetF r) ot void void_elim void_elim.
  Proof. intros H. remember (RetF r). induction H; try congruence; eauto. Qed.
  
  Lemma destruct_trans b1 b2 :
      forall sim x y z,
          simulationF (@eqitR E R R RR b1 b2) id sim x y ->
          simulationF (eqitR RR b1 b2) id sim y z ->
          exists P kx ky kz,
            eqitR RR b1 b2 x y P kx ky /\
            eqitR RR b1 b2 y z P ky kz /\
            (forall p, sim (kx p) (ky p)) /\
            (forall p, sim (ky p) (kz p)).
  Proof.
    unfold eqitR. intros sim x y z H1 H2.
    destruct H1 as [x y P1 kx ky1 REL1 RELS1];
    remember (observe y) as oy1;
    destruct (REL1);
    destruct H2 as [y z P2 ky2 kz REL2 RELS2];
    remember (observe y) as oy2;
    destruct (REL2);
    try congruence.
    - repeat esplit; eauto.
      assert (H : r2 = r0) by congruence; rewrite H.
      eauto.
    - repeat esplit; eauto.
      econstructor; eauto.
      rewrite <- Heqoy1 in e.
      eapply eqitR_inv_RetF, e.
    - repeat esplit; eauto.
      assert (H : t2 = t0) by congruence; rewrite H.
      eauto.
    - repeat esplit; eauto.
      + econstructor; eauto.
        assert (H : t2 = t0) by congruence; rewrite H.
        
      
  Admitted.
  
 End Homogeneous.
