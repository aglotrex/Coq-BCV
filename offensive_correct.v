

Require Import OrderedType OrderedTypeEx OrderedTypeAlt DecidableType DecidableTypeEx.
Require Import RelationClasses.
From bcv Require Import vmtype dvm ovm.
Require bcv.heritage.

Module Offensive_correcte (H:heritage.Herit).

  Module D:= D(H).
  Module O:= O(H).

  (** Calcul de la valeur offensive d'une valeur défensive: on enlève
  le tag de type,et on met zéro là où il n'y a pas de valeur, de toute
  façon si le bcv est correct et accepte une applet, ces valeurs
  n'apparaitront jamais. *)
  Definition d2o (v:DefVal.Val): OffVal.Val :=
    match v with
      | DefVal.Vint i => i
      | DefVal.Vref (_,i) => i
      | DefVal.Vrefnull => 0
      | DefVal.Error => 0
      | DefVal.NonInit => 0
    end.

  (** * Les fonctions d'offensivisation: on applique d2o partout. *)

  Definition offensive_regs rgs: O.Registers := Dico.map d2o rgs.

  Definition offensive_stack st: O.Stack := List.map d2o st.

  Definition offensive_heap hp: O.Heap :=
    Dico.map (fun obj =>
                {| O.objclass:= obj.(D.objclass) ; O.objfields := Dico.map d2o (obj.(D.objfields)) |}) hp.

  Definition offensive_state (s:D.State) : O.State :=
    let fr :=
        {| O.mdef := s.(D.frame).(D.mdef);
           O.regs := offensive_regs (s.(D.frame).(D.regs));
           O.stack := offensive_stack (s.(D.frame).(D.stack));
           O.pc:=s.(D.frame).(D.pc) |} in
    {| O.frame := fr;
       O.framestack := nil;
       O.heap := offensive_heap s.(D.heap) |}.


  Definition offensive_opt_state (s:option D.State) : option O.State :=
    match s with
      | None => None
      | Some x => Some (offensive_state x)
    end.


  Lemma pc_ok: forall s,  (s.(D.frame)).(D.pc) = (O.frame (offensive_state s)).(O.pc).
    destruct s;simpl;reflexivity.
  Qed.

  Lemma mdef_ok: forall s, D.mdef(s.(D.frame)) = O.mdef(O.frame(offensive_state s)).
  Proof.
    destruct s;simpl;reflexivity.
  Qed.

  Definition d2o_opt := option_map d2o.


  Add Morphism offensive_regs with signature Dico.Equal ==> Dico.Equal as off_regs_m.
  Proof.
    intros rgs1 rgs2 H.
    unfold offensive_regs.
    apply Dicomore.map_m with (x:= d2o) (y:= d2o) in H.
    - assumption.
    - reflexivity.
  Qed.


  Lemma find_offensive_ok : forall rgs ridx, 
                              Dico.find ridx (offensive_regs rgs) 
                              = d2o_opt (Dico.find ridx rgs).
  Proof.
    intros rgs.
    induction rgs using  Dicomore.map_induction_bis;simpl;intros.
    - rewrite <- H.
      apply IHrgs1.
    - vm_compute.
      reflexivity. 
    - unfold offensive_regs.
      rewrite Dicomore.map_o.    
      reflexivity.
  Qed.
  Import D.

  (** Diagramme de commutation entre D et O. *)
  Lemma offensive_ok : 
    forall (s s':D.State) (os os' os'':O.State),
      offensive_state s = os ->
      offensive_state s' = os' ->
      D.exec_step s = Some s' ->
      O.exec_step os = Some os'' -> 
      O.state_eq os' os''.
  Proof.
    intros.
    unfold exec_step in H1.
    unfold O.exec_step in H2.
    subst.
    rewrite <- pc_ok in H2.
    rewrite <- mdef_ok in H2.
    destruct (FIND (pc (frame s)) (instrs (mdef (frame s)))) eqn:heq_instrpc; try now inversion H1.
    - destruct i eqn:heq_instr; try now inversion H1.
      + inversion H1.
        inversion H2.
        unfold offensive_state. simpl. reflexivity.


      + destruct (stack (frame s)) eqn:heq_add;try now inversion H1.
      destruct d eqn:heq_1;try now inversion H1.
      destruct l eqn:heq_2;try now inversion H1.
      destruct d0 eqn:heq_3;try now inversion H1.
      unfold offensive_state in H2. simpl in H2. rewrite heq_add in H2. simpl in H2. subst.
      inversion H1.
      inversion H2. clear H1 H2.
      unfold offensive_state .
      simpl.
      reflexivity.

  
     + destruct_with_eqn (FIND ridx (regs (frame s))) ; try now inversion H1.
       destruct_with_eqn d ; try now inversion H1.
       unfold offensive_state in H2.
       simpl in H2.
      unfold offensive_regs in H2.
        Search Dico.map.
      rewrite Dicomore.map_o in H2. simpl.
      setoid_rewrite  Heqo in H2.
      simpl in H2.
      inversion H1.
      inversion H2. clear H1 H2.
      subst.
      reflexivity.
    + destruct_with_eqn (FIND ridx (regs (frame s))) ; try now inversion H1.
      destruct_with_eqn d ; try now inversion H1.
      destruct clrf.
      destruct (H.sub c cl) ; try now inversion H1.
      unfold offensive_state in H2.
      simpl in H2.
      unfold offensive_regs in H2.
      Search Dico.map.
      rewrite Dicomore.map_o in H2. simpl.
      setoid_rewrite  Heqo in H2.
      inversion H1.
      inversion H2.  clear H1 H2.
      subst.
      reflexivity.
   + destruct_with_eqn (stack (frame s)); try now inversion H1.
     destruct_with_eqn d; try now inversion H1.
     unfold offensive_state in H2.
      simpl in H2.
      setoid_rewrite  Heql in H2.
    inversion H1.
      inversion H2.  clear H1 H2. simpl.
    unfold offensive_regs. simpl.
  
    apply O.state_eq_C;try reflexivity.
    * simpl.
      apply O.frame_eq_C;try reflexivity.
      -- simpl. Search Dico.map.
          apply Dicomore.add_map.
    
  + admit.
  + admit.
  + admit.
  + admit.
Admitted.
  

End Offensive_correcte.
