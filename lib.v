Require Import FMapList.
Require Import Omega.
Require FMapFacts.
Require Import Relations.
Require Import OrderedType OrderedTypeEx OrderedTypeAlt.
Require Import DecidableType DecidableTypeEx.

(** Un module pour regrouper les propriétés sur les maps. On met tout
    ce qu'il y a dans WProperties et WFacts + qq propriétés
    supplémentaires prouvées ci-dessous. Voir à la fin du fichier pour
    le module Dico qui servira partout dans ce développement. *)
Module MoreMaps (Dico:FMapInterface.S).

  (** Toutes celles de la lib standard... *)
  Include FMapFacts.WProperties(Dico).
  Include FMapFacts.WFacts(Dico).
  
  Import Dico.
  Arguments empty {elt}.

  (** Plus quelques autres. *)
  Lemma Empty_eq: forall (elt : Type) (x y : t elt),
      Empty x -> Empty (elt:=elt) y -> Equal x y.
  Proof.
    intros elt x y H H0.
    red.
    intros y0.
    red in H.
    red in H0.
    destruct_with_eqn (find y0 x).
    - rewrite <- find_mapsto_iff in Heqo.
      destruct (H _ _ Heqo).
    - destruct_with_eqn (find y0 y).
      rewrite <- find_mapsto_iff in Heqo0.
      + destruct (H0 _ _ Heqo0).
      + reflexivity.
  Qed.

  Lemma Empty_eq_empty:
    forall (elt : Type) (x : t elt),
      Empty x
      ->   Equal x empty .
  Proof.
    intros elt x H.
    apply Empty_eq.
    - assumption.
    - apply empty_1.
  Qed.

  Lemma add_map : forall A B k (x:A) l (f:A -> B),
    Equal
    (map f (add k x l))
    (add k (f x) (map f l)).
  Proof.
    unfold Equal.
    intros A B k x l f y.
    setoid_rewrite map_o.
    setoid_rewrite add_o.
    rewrite map_o.
    destruct (E.eq_dec k y);subst;auto.
  Qed.


  Lemma add_map2 : forall A B k (x:A) l (f:A -> B) P,
    (forall m m' : t B, Equal m m' -> P m -> P m') -> 
    P(map f (add k x l)) -> 
    P(add k (f x) (map f l)).
    intros A B k x l f P h h'.
    apply h with (m:=(map f (add k x l))).
    - apply add_map.
    - assumption.
  Qed.


  Lemma empty_map : forall A B (f:A -> B),
      Equal (map f empty) empty.
  Proof.
    intros A B f.
    unfold Equal.
    intros y.
    rewrite empty_o, map_o, empty_o;auto.
  Qed.

  Lemma Equiv_refl_Equal : forall elt (Req:elt -> elt -> Prop) (Req_refl:reflexive _ Req) (m m' : t elt),
      Equal m m' -> Equiv Req m m'.
  Proof.
    intros elt Req Req_refl m m' H.
    red.
    split.
    - intros k.
      red in H.
      specialize (H k).
      red;split;red;intros; red in H0; destruct H0.
      + exists x.
        rewrite  find_mapsto_iff in H0.
        rewrite H0 in H.
        apply find_2.
        auto.
      + exists x.
        rewrite  find_mapsto_iff in H0.
        rewrite H0 in H.
        apply find_2.
        auto.
    - intros k e e' H0 H1.
      red in H.
      specialize (H k).
      rewrite  find_mapsto_iff in H0.
      rewrite  find_mapsto_iff in H1.
      rewrite H0 in H.
      rewrite H1 in H.
      inversion H.
      apply Req_refl.
  Qed.


  Lemma Equiv_refl:
    forall (elt : Type) (Req : elt -> elt -> Prop),
      reflexive elt Req -> reflexive (t elt) (Equiv Req).
  Proof.
    unfold Equiv.
    intros elt Req H.
    red.
    intros x. 
    split;intros;auto.
    - reflexivity.
    - erewrite (@F.MapsTo_fun _ _ k e e');eauto.
  Qed.

  Lemma Equiv_sym:
    forall (elt : Type) (Req : elt -> elt -> Prop),
      symmetric elt Req -> symmetric (t elt) (Equiv Req).
  Proof.
    unfold Equiv.
    intros elt Req h_sym.
    red.
    intros x y [h1 h2]. 
    split;intros;auto.
    - symmetry.
      apply h1.
    - apply h_sym.
      eapply h2;eauto.
  Qed.

  Lemma Equiv_trans:
    forall (elt : Type) (Req : elt -> elt -> Prop),
      transitive elt Req -> transitive (t elt) (Equiv Req).
  Proof.
    unfold Equiv.
    intros elt Req h_trans.
    red.
    intros x y z [h1 h2] [h3 h4].
    split;intros. 
    - transitivity (In k y).
      + apply h1.
      + apply h3.
    - red in h_trans.
      assert (In k x) as hInx by (red;eauto).
      rewrite h1 in hInx.
      red in hInx.
      destruct hInx as [? h_mapstoy].
      eapply h_trans.
      + eapply h2;eauto.
      + eapply h4;eauto.
  Qed.
  
  Add Parametric Relation (elt : Type) {R:relation elt} {H:Equivalence R}:    (t elt) (Equiv R)
      reflexivity proved by (@Equiv_refl elt R (@Equivalence_Reflexive elt R H))
      symmetry proved by (@Equiv_sym elt R (@Equivalence_Symmetric elt R H))
      transitivity proved by (@Equiv_trans elt R (@Equivalence_Transitive elt R H))
        as EquivSetoid.

  (* Instance equiv_equiv: forall elt :Type, forall  R:elt -> elt -> Prop, *)
        (* Equivalence R -> Equivalence (Equiv R). *)
  (* Proof. *)
    
  (* Admitted. *)

  Add Parametric Morphism (elt elt': Type) {RA:relation elt} {RB: relation elt'}
      {Ha:Equivalence RA}{Hb:Equivalence RB}: (@map elt elt')
      with signature ((RA ==> RB) ==> (@Dico.Equiv elt RA) ==> @Dico.Equiv elt' RB)
        as map_morph.
  Proof.
    intros x y hcompat x0 y0 hEquiv.
    red in hcompat,hEquiv|-*.
    destruct hEquiv as [hinin hmapsto].
    split;intros.
    - setoid_rewrite F.map_in_iff.
      apply hinin.
    - apply F.map_mapsto_iff in H;destruct H as [a [heqe hmapstok]].
      apply F.map_mapsto_iff in H0;destruct H0 as [b [heqe' hmapstok']].
      subst.
      specialize hmapsto with (1:=hmapstok)(2:=hmapstok').
      apply hcompat.
      assumption.
  Qed.

  Add Parametric Morphism (elt: Type) {RA:relation elt}
      {Ha:Equivalence RA}: (@add elt)
      with signature (E.eq ==> RA ==> (@Dico.Equiv elt RA) ==> @Dico.Equiv elt RA)
        as add_morph.
  Proof.
    intros x y H x0 y0 hRA_x0_y0 x1 y1 hequiv_x1_x2.
    red in hequiv_x1_x2|-*.
    destruct hequiv_x1_x2 as [hInx0_y1 hmapsto].
    split.
    - intros.
      setoid_rewrite F.add_in_iff.
      split;intros [heq | hIn];auto.
      + left.
        transitivity x;auto.
      + right.
        apply hInx0_y1.
        assumption.
      + left.
        transitivity y;auto.
      + right.
        apply hInx0_y1.
        assumption.
    - intros ? ? ? hmapstok_e hmapstok_e'.
      apply F.add_mapsto_iff in hmapstok_e.
      apply F.add_mapsto_iff in hmapstok_e'.
      decompose [or and] hmapstok_e;subst; decompose [or and] hmapstok_e';subst;try discriminate.
      + assumption.
      + rewrite <- H in H2.
        contradiction.
      + rewrite H in H1.
        contradiction.
      + eapply hmapsto;eauto.
  Qed.

  (* Instance proper_map_equiv: forall  elt elt': Type, forall {RA} {RB}, *)
      (* Proper ((RA ==> RB) ==> (@Dico.Equiv elt RA) ==> @Dico.Equiv elt' RB) (map (elt':=elt')). *)
  (* Proof. *)
  (* Admitted. *)

(*  Lemma map_equiv: forall (A B : Type) (ReqA:A -> A -> Prop) (ReqB:B -> B -> Prop) 
                          (f : A -> B) (l l': Dico.t A),
      (forall x y, ReqA x y -> ReqB (f x) (f y)) -> 
      Dico.Equiv ReqA l l' ->
      Dico.Equiv ReqB (Dico.map f l) (Dico.map f l').
    Proof.
      intros A B ReqA ReqB f l.
      induction l using  map_induction_bis;simpl;intros.
      - admit.
      - admit. (* TODO lemma *)
      - 
      
      unfold Equiv in *.
      split.
      simpl.
*)
  Lemma add_map_equiv: forall (A B : Type) {ReqA:relation A} {ReqB:B -> B -> Prop}
                              {HA:Equivalence ReqA}{HB:Equivalence ReqB}
                              (k : Dico.key) (x : A) (l: Dico.t A) (f : A -> B),
      (Proper (ReqA ==> ReqB) f)%signature ->
      (* (forall x y, ReqA x y -> ReqB (f x) (f y)) ->  *)
      Dico.Equiv ReqB (Dico.map f (Dico.add k x l)) (Dico.add k (f x) (Dico.map f l)).
    Proof.
      intros A B ReqA ReqB HA HB k x l f Hcompat.
      red.
      (* Normalement il faudrait un rewrite ici. *)
      setoid_rewrite <- add_map.
      split;intros.
      - reflexivity.
      - erewrite (@F.MapsTo_fun _ _ k0 e e');eauto.
        reflexivity.
    Qed.


(*  Add Parametric Morphism (elt: Type) {R:relation elt}
      {Ha:Equivalence R} : (@Equiv elt R)
      with signature (@Dico.Equal elt ==>@Dico.Equal elt ==> iff)
        as equal_equiv_morph.
  Proof.
    intros x y hEq x0 y0 hEq0. 
    eapply Equiv_refl_Equal with (Req:=R) in hEq.
    - eapply Equiv_refl_Equal with (Req:=R) in hEq0.
      + rewrite hEq.
        rewrite hEq0.
        reflexivity.
      + apply Ha.
    - apply Ha.
  Qed.*)

End MoreMaps.




(** * [Dico]et [Dicomore] formalisent les maps (dictionnaires) ayant pour clés des [nat] et polymorphes sur les valeurs.

Il serviront pour représenter la mémoire, les programmes etc. *)

(* Les définitions et propriétés de base sont dans [Dico]. *)
Module Dico:=Make(Nat_as_OT).

(** Tout le reste (définition supplémentaire et très nombreuses
propriétés) est dans [Dicomore]. *)
Module Dicomore:=MoreMaps(Dico).

(** Une notation plus compacte pour find. *)
Notation FIND := (@Dico.find _).

(** Ce qui suit est spécifique à Dico car utilise le fait que les clés
    sont des entiers. *)

(** * Génération de clés <<fraîches>>. *)

(** Fonction auxiliaire: retourne le plus grand index utilisé dans [hp]. Permet
    de retourner un index "frais" dans la suite. *)
Definition maxkey {A} (hp:(Dico.t A)) :=
  Dico.fold
    (fun k e acc => if (Compare_dec.lt_dec acc k) then k else acc) hp 0.

(** Propriété basique de maxkey: l'index retourné est bien "frais". *)
Lemma maxkey_correct : forall A (h:Dico.t A) k, k>(maxkey h) -> 
  ~Dico.mem k h = true.
Proof.
  intros A h k.
  unfold maxkey.
  pattern h ,
    (Dico.fold
      (fun (k0 : Dico.key) (_ : A) (acc : nat) =>
        if Compare_dec.lt_dec acc k0 then k0 else acc) h 0).
  apply Dicomore.fold_rec;intros;intro.
  - assert (ass:Dico.Equal m Dico.empty).
    + apply Dicomore.Empty_eq_empty.
      assumption.
    + setoid_rewrite ass in H1.
      setoid_rewrite Dicomore.empty_a in H1.
      discriminate.
  - red in H1.
    setoid_rewrite (Dicomore.mem_find_b) in H4.
    setoid_rewrite H1 in H4.
    setoid_rewrite <- (Dicomore.mem_find_b) in H4.
    setoid_rewrite (@Dicomore.F.add_neq_b _ m' k0 k e) in H4.
    + apply H2;try assumption.
      destruct (Compare_dec.lt_dec a k0);omega.
    + destruct (Compare_dec.lt_dec a k0);omega.
Qed.


(* Nommage eutomatique d'hypothèses: *)
Ltac rename_lib h th :=
  match th with
  | List.In ?x ?l => fresh "inL_" x "_" l
  | List.In ?x ?l => fresh "inL_" x
  | List.In ?x ?l => fresh "inL"
  end.
