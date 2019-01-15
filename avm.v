From bcv Require Import heritage vmtype vmdefinition  LibHypsNaming.
Require Import List.
Import ListNotations.

(** * Valeurs de la machine abstraite

   On abstrait les défintions ci-dessus: on enlève les valeurs et les adresses
   mémoire et on les remplace par les types. *)

Module AbsVal <: VMVal.
  Definition Val := VMType.
  
  (** Calcul du type d'une valeur défensive. *)
  Definition v2t (v:Val): VMType := v.

End AbsVal.


Module A (Import H:Herit).
  Module Abs := VMDefinition(AbsVal)(H).
  Include Abs.

  Ltac rename_avm h th := fail.

  (* Hypothesis renaming stuff from other files + current file.
     DO NOT REDEFINE IN THIS FILE. Redefine rename_avm instead. *)
  Ltac rename_hyp h th ::=
    match th with
    | _ => (rename_avm h th)
    | _ => (Abs.rename_vmdef h th)
    | _ => (LibHypsNaming.rename_hyp_neg h th)
    end.


(** * Exécution de la machine défensive.
   Pas de vérif de overflow. pas de nb négatifs. *)
  Function exec_step (s:State): list (option State) :=
    Definition exec_step (s:State): option State :=
    let frm:Frame := s.(frame) in
    let pc: pc_idx := frm.(pc) in
    let instr_opt := Dico.find pc (frm.(mdef).(instrs)) in
    match instr_opt with
    | None => [None]
    | Some instr =>
      match instr with
        | ret => [Some s]
        | Iconst i =>
             [Some {| framestack := s.(framestack); heap := s.(heap);
                frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                            pc:= pc + 1;
                            stack:= DefVal.Tint i :: s.(frame).(stack)
                         |}
             |}} ]
          
       |Iadd =>
          match s.(frame).(stack) with
              | nil => [None]
              | Tint i1 :: nil => None
              | Tint i1 :: Tint i2 :: stack' => 
                [Some {| framestack := s.(framestack); heap := s.(heap);
                        frame := {| mdef:=s.(frame).(mdef); regs:= s.(frame).(regs);
                                    pc:= pc + 1;
                                    stack:= Tint (i1+i2) :: stack'
                                 |}
                     |}]
              | _  => [None]
              end
      | Iload ridx =>
        match Dico.find ridx (s.(frame).(regs)) with
        | Some (Tint i) =>
          [Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef); regs:= s.(frame).(regs);
                              pc:= pc + 1;
                              stack:= (Tint i) :: s.(frame).(stack)
                           |}
               |}]
        | _ => [None] (** Bad register number *)
        end

      | Rload cl_exp ridx =>
          match Dico.find ridx (s.(frame).(regs)) with
        | Some (Vref (cl_act,addr)) =>
          if (H.sub cl_act  cl_exp ) then
          Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                              pc:= pc + 1;
                              stack:= (Vref (cl_act,addr)) :: s.(frame).(stack)
                           |}
               |}
          else
            None
        | _ => None (** Bad register number *)
        end

      | Istore ridx =>
        match s.(frame).(stack) with
        | (Tint i) :: stack' =>
            [Some {| framestack := s.(framestack); heap := s.(heap);
                    frame := {| mdef:=s.(frame).(mdef) ;
                                regs:= Dico.add ridx (Vint i) (s.(frame).(regs));
                                pc:= pc + 1;
                                stack:= stack'
                             |}
                 |}]
        | _ => [None] (** Stack underflow *)
        end
        

      | Rstore cl_exp ridx =>
        match s.(frame).(stack) with
        | (Vref (cl_act,addr)) :: stack' =>
          if (H.sub cl_act cl_exp) then
            [Some {| framestack := s.(framestack); heap := s.(heap);
                    frame := {| mdef:=s.(frame).(mdef) ;
                                regs:= Dico.add ridx (Vref (cl_act,addr))  (s.(frame).(regs));
                                pc:= pc + 1;
                                stack:= stack'
                             |}
                 |}]
          else 
          [None]
            
        | _ =>  [None] (** Stack underflow *)
        end
       

      | Iifle jmp => (** ifeqe *)
      

 
      match s.(frame).(stack) with
        | (Tint 0) :: stack' => (** = 0  --> jump *)
          [Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                              pc:= jmp;
                              stack:= stack'
                           |}
               |}]
        | (Tint _ ):: stack' => (** <> 0  --> pc+1 *)
          [Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                              pc:= pc+1;
                              stack:= stack'
                           |}
               |}]
        | _ => [None] (** Stack underflow *)
        end
    

      | Goto jmp =>
        [Some {| framestack := s.(framestack); heap := s.(heap);
                frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                            stack:= s.(frame).(stack);
                            pc:= jmp
                         |}
             |}]

      | Getfield cl namefld typ =>
        match s.(frame).(stack) with
        | Tref (classid,hpidx) :: stack' =>
          if (H.sub classid cl) then
          match Dico.find hpidx s.(heap) with
          | None => [None] (** adresse inconnue *)
          | Some {|objclass:= objcl; objfields:= flds |} => (* TODO: vérifier le type retourné? *)
            if (H.sub objcl cl) then
            match Dico.find namefld flds with
            | None => [None] (** Champ de classe inconnu ou pas initialisé *)
            | Some v =>
              [Some {| framestack := s.(framestack); heap := s.(heap);
                      frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                                  pc:= pc+1;
                                  stack:= v :: stack'
                               |}
                   |}]
            end
            else [None]
          end
          else [None]
        | _  => [None] (** Stack underflow *)
        end

      | Putfield cl namefld typ =>
        match s.(frame).(stack) with
        | Tref (classid,hpidx) :: v :: stack' =>
          if (H.sub classid cl) then
          match FIND cl H.allcl with
          | None => [None]
          | Some (cldef) =>
            match FIND namefld cldef with
            | None => [None]
            | Some (typfld) =>
              let typv := D.v2t v in
              if compat typv typfld then
              match Dico.find hpidx s.(heap) with
              | None => [None] (** adresse inconnue, objet non alloué *)
              | Some {| objclass:= objcl; objfields:= flds |}=>
                let newflds := {| objclass:= objcl;
                                  objfields:=Dico.add namefld v flds |} in
                let newheap := Dico.add hpidx newflds s.(heap) in
                [Some {| framestack := s.(framestack);
                        heap := newheap;
                        frame := {| mdef:=s.(frame).(mdef) ;
                                    regs:= s.(frame).(regs);
                                    pc:= pc+1;
                                    stack:= stack'
                                 |}
                     |}]
              end
              else [None]
            end
          end
          else [None]
        | _ => [None] (** Stack underflow *) 
        end

      | New clid =>
        match new clid s.(heap) with
        | None => [None] (** Classe inconnue *)
        | Some (newobj,newhp) =>
           [Some {| framestack := s.(framestack); heap := newhp;
                  frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                              stack:= (Vref newobj) :: s.(frame).(stack);
                              pc:= pc+1
                           |}
               |}]

        end
      end
    end.


(** * Tests *)

  Notation "k --> i , d" := (Dico.add k i d) (at level 55, right associativity).

  Definition prog:MethodDef := 
    {| instrs := (0 --> Iload 1 ,
                  1 --> Istore 2 ,
                  2 --> ret ,
                  Dico.empty ) ;
       argstype := Tint :: Tint:: nil;
       restype := Tint |}.

  Definition startstate:State := 
    {| 
      framestack := nil;
      heap:= Dico.empty ;
      frame := {|
        mdef:= prog ; 
        regs:= (0 --> Tint , 1 --> Tint, Dico.empty);
        pc:= 0;
        stack:= nil
        |}
      |}.

  Fixpoint exec_n (s : State) (n:nat) {struct n}: list (option State) :=
    match n with
      | 0 => [ Some s ]
      | S n' =>
        let ls' := exec_step s in
          (fix exec_l_n (ls:list (option State)) {struct ls}: list (option State) :=
          match ls with
            | nil => nil
            | None :: ls' => None :: exec_l_n ls'
            | Some s' :: ls' => List.app (exec_n s' n') (exec_l_n ls')
          end) ls'
    end.

  Eval simpl in exec_n startstate 1.
  Eval simpl in exec_n startstate 2.
  Eval simpl in exec_n startstate 5.

  Lemma essai : forall s x,
    exec_step s = [ Some x ] -> 
    x.(framestack) = s.(framestack).
  Proof.
    intros s.
    functional induction exec_step s;intros ;simpl;
      try solve [discriminate | inversion H; subst;simpl;reflexivity] .
  Qed.

  Lemma essai2 : forall s x y,
    exec_step s = [ Some x ; Some y] -> 
    x.(framestack) = s.(framestack).
  Proof.
    intros s.
    functional induction exec_step s;intros ;simpl;
      try solve [discriminate | inversion H; subst;simpl;reflexivity] .
  Qed.
  
End A.

