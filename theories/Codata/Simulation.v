
From Paco Require Import paco.

Definition ObRel (X Y : Type) := X -> Y -> forall P : Type, (P -> X) -> (P -> Y) -> Prop.

Variant simulationF {X Y} (R : ObRel X Y) (vclo : (X -> Y -> Prop) -> (X -> Y -> Prop)) (sim : X -> Y -> Prop) : X -> Y -> Prop :=
| Step t1 t2 P k1 k2
       (REL : R t1 t2 P k1 k2)
       (RELS : forall p : P, vclo sim (k1 p) (k2 p))
  : simulationF R vclo sim t1 t2
.

Definition simulation {X Y} (R : ObRel X Y) vclo := paco2 (simulationF R vclo) bot2.

Lemma simulationF_mono {X Y} (R : ObRel X Y) vclo (MON : monotone2 vclo)
  : monotone2 (simulationF R vclo).
Proof.
  unfold monotone2; intros.
  destruct IN. econstructor; eauto.
Qed.
Hint Resolve simulationF_mono : paco.

Definition flip_obrel {X Y} (R : ObRel X Y) : ObRel Y X :=
  fun tx ty P kx ky => R ty tx P ky kx.

Definition flip_clo {A B C} clo r := @flip A B C (clo (@flip B A C r)).

Lemma flip_clo_mono {X Y} (vclo : (X -> Y -> Prop) -> X -> Y -> Prop)
  : monotone2 vclo -> monotone2 (flip_clo vclo).
Proof. compute; firstorder. Qed.
Hint Resolve flip_clo_mono : paco.

Lemma eqit_idclo_mono {X Y} : monotone2 (@id (X -> Y -> Prop)).
Proof. unfold id. eauto. Qed.
Hint Resolve eqit_idclo_mono : paco.

Lemma simulation_flip {X Y} (R : ObRel X Y) vclo (MON : monotone2 vclo) :
  forall (t1 : X) (t2 : Y),
    simulation (flip_obrel R) (flip_clo vclo) t2 t1 -> simulation R vclo t1 t2.
Proof.
  pcofix CIH; pstep. intros t1 t2 H.
  punfold H; destruct H.
  econstructor; [ eapply REL | ].
  intros; specialize (RELS p).
  eapply MON; [ eapply RELS | ].
  intros t1' t2' H'; pclearbot.
  eauto.
Qed.

Lemma simulation_mono {X Y} (R R' : ObRel X Y) vclo
      (MON : monotone2 vclo)
      (LE : R <5= R') :
  simulation R vclo <2= simulation R' vclo.
Proof.
  pcofix CIH; pstep. intros x y PR; punfold PR; destruct PR.
  econstructor; [eauto|].
  intros; eapply MON; [eapply RELS |].
  intros; pclearbot; eauto.
Qed.

From Coq Require Import
     RelationClasses.

Lemma Reflexive_simulationF {X} (R : ObRel X X) vclo sim
      (REFL_R : forall x, exists P k, R x x P k k)
      (REFL_hom : forall R, Reflexive R -> Reflexive (vclo R))
      (REFL_sim : Reflexive sim) :
  Reflexive (simulationF R vclo sim).
Proof.
  unfold Reflexive; intros; specialize (REFL_R x).
  destruct REFL_R as [ P [ k REFL ] ].
  econstructor; [ eapply REFL | ].
  intros; eapply REFL_hom; eauto.
Qed.

Lemma Reflexive_simulation {X} (R : ObRel X X) vclo
      (MON : monotone2 vclo)
      (REFL_R : forall x, exists P k, R x x P k k)
      (REFL_hom : forall R, Reflexive R -> Reflexive (vclo R)) :
  Reflexive (simulation R vclo).
Proof.
  unfold Reflexive; pcofix CIH; pstep.
  intros x; destruct (REFL_R x) as [P [k REFL]].
  econstructor; [eapply REFL|].
  intros; eapply MON; [eapply REFL_hom; eauto |].
  intros; eauto.
Qed.

Lemma Symmetric_simulationF {X} (R : ObRel X X) vclo sim
      (SYM_R : forall x y P x' y', R x y P x' y' -> R y x P y' x')
      (SYM_hom : forall R, Symmetric R -> Symmetric (vclo R))
      (SYM_sim : Symmetric sim) :
  Symmetric (simulationF R vclo sim).
Proof.
  unfold Symmetric. intros.
  destruct H.
  econstructor.
  eapply SYM_R. eapply REL.
  intros. eapply SYM_hom; eauto.
Qed.

Lemma Symmetric_simulation {X} (R : ObRel X X)
      (SYM_R : forall x y P x' y', R x y P x' y' -> R y x P y' x') :
  Symmetric (simulation R id).
Proof.
  pcofix CIH. pstep.
  intros x y H. punfold H. destruct H. pclearbot.
  econstructor; [eapply SYM_R; eapply REL|].
  intros. right. eapply CIH. eapply RELS.
Qed.

Lemma Transitive_simulation {X} (R : ObRel X X)
      (DES : forall sim x y z,
          simulationF R id sim x y ->
          simulationF R id sim y z ->
          exists P x' y' z',
            R x y P x' y' /\
            R y z P y' z' /\
            (forall p, sim (x' p) (y' p)) /\
            (forall p, sim (y' p) (z' p)))
      (TRANS : forall x y z P x' y' z',
          R x y P x' y' ->
          R y z P y' z' ->
          R x z P x' z') :
  Transitive (simulation R id).
Proof.
  pcofix CIH; pstep.
  intros x y z H1 H2; punfold H1; punfold H2.
  destruct (DES _ _ _ _ H1 H2) as [P [x' [y' [z' [REL1 [REL2 [RELS1 RELS2]]]]]]].
  econstructor; [eapply TRANS; eauto|].
  intros p; specialize (RELS1 p); specialize (RELS2 p); pclearbot.
  right; eapply CIH; eauto.
Qed.
