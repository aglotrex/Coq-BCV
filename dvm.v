(**
   Version très simplifiée des idée de: "Java bytecode verification: algorithms
   and formalizations", Xavier Leroy (Journal of Automated Reasoning,
   30(3-4):235-269, 2003).

   Dont voici l'abstract:

   "Bytecode verification is a crucial security component for Java applets, on
   the Web and on embedded devices such as smart cards. This paper reviews the
   various bytecode verification algorithms that have been proposed, recasts
   them in a common framework of dataflow analysis, and surveys the use of proof
   assistants to specify bytecode verification and prove its correctness."

 *)

(* Coq écrira de préférence la syntaxe [foo.(bar)] plutôt que [(bar
   foo)], pour les champs (bar) de records (foo). *)
Set Printing Projections.


Require Omega.
Require Import OrderedType OrderedTypeEx OrderedTypeAlt DecidableType DecidableTypeEx.
From bcv Require Import LibHypsNaming heritage vmtype vmdefinition.

(** * Valeurs manipulée par la machine défensive,

   Ce module servira à instancier VMDefinition plus bas.
   La définition des types, classes et instruction est fixée dans [vmtype]. *)

Module DefVal <: VMVal.

  Inductive DVal:Set :=
  | Vint (i:nat)
  | Vref (clrf:class_id * heap_idx) (** nom de classe * adresse dans le tas *)
  | Vrefnull
  | Error
  | NonInit.

  Definition Val := DVal.

  (** Calcul du type d'une valeur défensive. *)
  Definition v2t (v:Val): VMType :=
    match v with
      | Vint i => Tint
      | Vref (clid,_) => Tref clid
      | Vrefnull => Trefnull
      | Error => Top
      | NonInit => Top
    end.

  Lemma val_eq_dec : forall v1 v2:Val, {v1=v2}+{v1<>v2}.
  Proof.
    intros v1 v2.
    decide equality.
    decide equality.
    decide equality.
    decide equality.
    decide equality.
  Qed.

End DefVal.

 


Module D (H:Herit).


(** États défensifs. *)
  Module Def := VMDefinition(DefVal)(H).
  Import DefVal.
  Include Def.
  Ltac rename_dvm h th := fail.

  (* Hypothesis renaming stuff from other files + current file.
     DO NOT REDEFINE IN THIS FILE. Redefine rename_dvm instead. *)
  Ltac rename_hyp h th ::=
    match th with
    | _ => (rename_dvm h th) (* redefine this tactic at will to enrich renaming*)
    | _ => (Def.rename_vmdef h th) (* renaming from Def *)
    | _ => (LibHypsNaming.rename_hyp_neg h th) (* basic generic renaming *)
    end.

  (** test *)
  (*
    Definition obj1:Obj := {| objclass:=1; objfields:=Dico.empty _|}.
    Definition heap1:Heap := Dico.empty _ .
    Definition heap2:Heap := Dico.add 1 obj1 heap1.
    Definition heap3:Heap := Dico.add 2 obj1 heap2.
    Eval vm_compute in (maxkey heap3).
    Eval vm_compute in (maxkey heap2). *)
  (* fin test *)

 Definition build_flds: ClasseDef -> (Dico.t Val) :=
    Dico.map 
      (fun t:VMType =>
         match t with
         | Tint => Vint 0
         | Tref id => Vrefnull (** null = 0 *)
         | Object => Vrefnull (** null = 0 *)
         | Top => Vrefnull (** Should never happen *)
         | Trefnull => Vrefnull (** Should never happen *)
         end).

(** [new cldefs clid heap] vérifie que clid existe bien, puis retourne une
    reference [r] un nouveau [Heap] [h] et telle que [heap(r) = None] et [h(r) =
    Some(o)] où [o] est un objet "frais" et toutes les adresses de [heap] sont
    identiques dans [h]. *)
  Function new (clid:class_id) (heap:Heap) :=
    match Dico.find clid allcl with
    | None => None (** Classe inconnue *)
    | Some cldef =>
      let flds:Obj := {| objclass := clid; objfields := build_flds cldef |} in
      let newhpidx: nat := maxkey heap in
      Some((clid,S newhpidx), Dico.add (S newhpidx) flds heap)
    end.

(**
  Lemma new_one_change : forall clid hp hpidx newhp,
      new clid hp = Some (hpidx, newhp) ->
      forall idx,
        FIND idx newhp = FIND idx hp \/ idx=hpidx.
  Proof.
    intros clid hp.
    !functional induction new clid hp;intros;simpl;try solve [discriminate].
    inversion heq_Some;clear heq_Some;subst.
    destruct (Dico.E.eq_dec idx (S (maxkey hp)));simpl.
    - right;auto.
    - rewrite Dicomore.add_neq_o;auto.
  Qed.

  Add Parametric Morphism: build_flds with signature (Dico.Equal ==> Dico.Equal) as build_flds_morphism.
    intros x y H.
    unfold build_flds. 
    setoid_rewrite H.
    apply  Dicomore.F.Equal_refl.
  Qed.*)
  (** * Fonction d'exécution défensive d'*un* bytecode.


     Pas de vérif d'overflow sur la pile d'opérandes. pas de nb
     négatifs, on ne vérifie que le typage et les underflow. *)
  Definition exec_step (s:State): option State :=
    let frm:Frame := s.(frame) in
    let pc: pc_idx := frm.(pc) in
    let instr_opt := Dico.find pc (frm.(mdef).(instrs)) in
    match instr_opt with
    | None => None
    | Some instr =>
      match instr with
        | ret => Some s
        | Iconst i =>
             Some {| framestack := s.(framestack); heap := s.(heap);
                frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                            pc:= pc + 1;
                            stack:= DefVal.Vint i :: s.(frame).(stack)
                         |}
             |}
          
       |Iadd =>
          match s.(frame).(stack) with
              | nil => None
              | Vint i1 :: nil => None
              | Vint i1 :: Vint i2 :: stack' => 
                Some {| framestack := s.(framestack); heap := s.(heap);
                        frame := {| mdef:=s.(frame).(mdef); regs:= s.(frame).(regs);
                                    pc:= pc + 1;
                                    stack:= Vint (i1+i2) :: stack'
                                 |}
                     |}
              | _  => None
              end
      | Iload ridx =>
        match Dico.find ridx (s.(frame).(regs)) with
        | Some (Vint i) =>
          Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef); regs:= s.(frame).(regs);
                              pc:= pc + 1;
                              stack:= (Vint i) :: s.(frame).(stack)
                           |}
               |}
        | _ => None (** Bad register number *)
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
        | (Vint i) :: stack' =>
            Some {| framestack := s.(framestack); heap := s.(heap);
                    frame := {| mdef:=s.(frame).(mdef) ;
                                regs:= Dico.add ridx (Vint i) (s.(frame).(regs));
                                pc:= pc + 1;
                                stack:= stack'
                             |}
                 |}
        | _ => None (** Stack underflow *)
        end
        

      | Rstore cl_exp ridx =>
        match s.(frame).(stack) with
        | (Vref (cl_act,addr)) :: stack' =>
          if (H.sub cl_act cl_exp) then
            Some {| framestack := s.(framestack); heap := s.(heap);
                    frame := {| mdef:=s.(frame).(mdef) ;
                                regs:= Dico.add ridx (Vref (cl_act,addr))  (s.(frame).(regs));
                                pc:= pc + 1;
                                stack:= stack'
                             |}
                 |}
          else 
          None
            
        | _ => None (** Stack underflow *)
        end
       

      | Iifle jmp => (** ifeqe *)
      

 
      match s.(frame).(stack) with
        | (Vint 0) :: stack' => (** = 0  --> jump *)
          Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                              pc:= jmp;
                              stack:= stack'
                           |}
               |}
        | (Vint _ ):: stack' => (** <> 0  --> pc+1 *)
          Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                              pc:= pc+1;
                              stack:= stack'
                           |}
               |}
        | _ => None (** Stack underflow *)
        end
    

      | Goto jmp =>
        Some {| framestack := s.(framestack); heap := s.(heap);
                frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                            stack:= s.(frame).(stack);
                            pc:= jmp
                         |}
             |}

      | Getfield cl namefld typ =>
        match s.(frame).(stack) with
        | Vref (classid,hpidx) :: stack' =>
          if (H.sub classid cl) then
          match Dico.find hpidx s.(heap) with
          | None => None (** adresse inconnue *)
          | Some {|objclass:= objcl; objfields:= flds |} => (* TODO: vérifier le type retourné? *)
            if (H.sub objcl cl) then
            match Dico.find namefld flds with
            | None => None (** Champ de classe inconnu ou pas initialisé *)
            | Some v =>
              Some {| framestack := s.(framestack); heap := s.(heap);
                      frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                                  pc:= pc+1;
                                  stack:= v :: stack'
                               |}
                   |}
            end
            else None
          end
          else None
        | _  => None (** Stack underflow *)
        end

      | Putfield cl namefld typ =>
        match s.(frame).(stack) with
        | Vref (classid,hpidx) :: v :: stack' =>
          if (H.sub classid cl) then
          match FIND cl H.allcl with
          | None => None
          | Some (cldef) =>
            match FIND namefld cldef with
            | None => None
            | Some (typfld) =>
              let typv := D.v2t v in
              if compat typv typfld then
              match Dico.find hpidx s.(heap) with
              | None => None (** adresse inconnue, objet non alloué *)
              | Some {| objclass:= objcl; objfields:= flds |}=>
                let newflds := {| objclass:= objcl;
                                  objfields:=Dico.add namefld v flds |} in
                let newheap := Dico.add hpidx newflds s.(heap) in
                Some {| framestack := s.(framestack);
                        heap := newheap;
                        frame := {| mdef:=s.(frame).(mdef) ;
                                    regs:= s.(frame).(regs);
                                    pc:= pc+1;
                                    stack:= stack'
                                 |}
                     |}
              end
              else None
            end
          end
          else None
        | _ => None (** Stack underflow *) 
        end

      | New clid =>
        match new clid s.(heap) with
        | None => None (** Classe inconnue *)
        | Some (newobj,newhp) =>
          Some {| framestack := s.(framestack); heap := newhp;
                  frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                              stack:= (Vref newobj) :: s.(frame).(stack);
                              pc:= pc+1
                           |}
               |}

        end
      end
    end.



  Functional Scheme exec_step_ind := Induction for exec_step Sort Prop.

  (** * Tests *)

  Notation "k --> i , d" := (Dico.add k i d) (at level 55, right associativity).

  Definition prog:MethodDef :=
    {| instrs := (0 --> Iload 1 ,
                  1 --> Istore 2 ,
                  2 --> ret ,
                  Dico.empty ) ;
       argstype :=( Tint :: Tint:: nil);
       restype := Tint |}.

  Definition startstate:State :=
    {|
      framestack := nil;
      heap := Dico.empty;
      frame := {|
                mdef:= prog ;
                regs:= (0 --> Vint 32 , 1-->Vint 11, Dico.empty );
                pc:= 0;
                stack:= nil
              |}
    |}.

  Fixpoint exec_n (s : State) (n:nat) {struct n}: option State :=
    match n with
    | 0 => Some s
    | S n' =>
      match exec_step s with
      | None => None
      | Some s' => exec_n s' n'
      end
    end.
  (*
    Eval simpl in exec_n startstate 1.
    Eval simpl in exec_n startstate 2.
    Eval simpl in exec_n startstate 5.
   *)
  (* Eval simpl in exec_n (fun x y => false) (Dico.empty _) startstate 2. *)


  (** Exemple de preuve très simple sur la fonction d'exécution: la
  pile (hormis la méthode en cours d'exécution) ne change pas au cours
  de exec_step. *)

  Lemma essai : forall s x,
      exec_step s = Some x ->
      x.(framestack) = s.(framestack).
  Proof.
    intros s.
    functional induction exec_step s;intros ;simpl;
      try solve [discriminate | inversion H; subst;simpl;reflexivity] .
  Qed.


End D.

