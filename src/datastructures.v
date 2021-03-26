Require Import List.
Import ListNotations.
Require Import Psatz.

(**
 This is a file containing the basic datastructures used in our project 

*)

(**
*)
Class InOpClass (A B:Type):= inOp: A->B->Prop.
Notation "a ∊ b" := (inOp a b) (at level 70).
Class InOpDecClass (A B:Type) (C:InOpClass A B):=
 inOpDec: forall (a:A) (b:B), {a ∊ b}+{~ a ∊ b}.
Notation "a ∊? b" := (inOpDec a b) (at level 70).
Class StrictSubsetOpClass (A B:Type):=
 strictSubsetOp: A->B->Prop.
Notation "a ⊂ b" := (strictSubsetOp a b) (at level 70).
Class SubsetOpClass (A B:Type):=
 subsetOp: A->B->Prop.
Notation "a ⊆ b" := (subsetOp a b) (at level 70).
Class EqDecOpClass (A:Type):=
 eqDecOp: forall (a b:A), {a = b}+{~ a = b}.
Notation "a =?= b" := (eqDecOp a b) (at level 70).
Class PushEndOpClass (A B C:Type):=
  pusEndOp: A->B->C.
Notation "a :<: b" := (pusEndOp a b) (at level 70).
(*:>:  :<: ::<  >::*)

Instance listInOpClass A: InOpClass A (list A):=
  fun a l => In a l.

Instance sumEqDecOpClass A B `(EqDecOpClass A, EqDecOpClass B):
EqDecOpClass (A+B).
  intros [a|a] [b|b].
-  destruct (a=?=b).
-- left. congruence.
-- right. congruence.
- right. congruence.
- right. congruence.
-  destruct (a=?=b).
-- left. congruence.
-- right. congruence.
Defined.

Instance listEqDecOpClass A `(EqDecOpClass A): EqDecOpClass (list A).
unfold EqDecOpClass.
induction a;
destruct b.
left. congruence.
right. congruence.
right. congruence.
destruct (a=?=a1).
destruct (IHa b).
left. congruence.
right. congruence.
right. congruence.
Defined.

(** 

The Maybe datatype contains a value of type 0 (Nothing) or 1 (Just) 'A'. Since it is mandatory to give a return value in the coq, if there is nothing to return, we can return Nothing. For example, if the parser can return Maybe parsetree, and if it could not recognize the text, it returns Nothing. 

*)

Inductive Maybe A:=
  | Just (a:A)
  | Nothing.
Arguments Just {A} _.
Arguments Nothing {A}.


(**
Class for an overloaded isEmpty operator.
*)
Class isEmptyable A := isEmpty : A -> bool.



(**
Abstract interface for a stack (first in last out)
The available functions:
- emptystack : creates a new empty stack
- pop : pops the top element, if nonempty
- push : pushes an element on top of the stack
- isStackEmpty : checks if the stack is empty
- pop_in : pops the top element, gives proof of
the properties of the operation
*)
Class Stack :=
{
  stack: Type->Type;
  emptystack {A}: stack A;
   pop {A} (s:stack A): Maybe (A * stack A); 
  push {A} (v:A) (s:stack A) : stack A;
  isStackEmpty {A} :> isEmptyable (stack A);
  stackInOpClass A:> InOpClass A (stack A);
  pop_in {A} (s:stack A):
    {'(a,s1):A*stack A|a∊s/\forall b, a<>b -> b∊s -> b∊s1}+{isStackEmpty s=true};
  inPush A x (s:stack A): x ∊ (push x s);
  inPush1 A x x0 (s:stack A): x ∊ s -> x ∊ (push x0 s);
  inEmpty A x (s:stack A): isStackEmpty s=true -> ~ x ∊ s;
}.

Instance listIsEmptiable A : isEmptyable (list A) :=
{
  isEmpty := fun l => match l with
                        | nil => true
                        | cons hd tl => false
                       end;

}.

(**
Actual implementation of a stack using a list

*)
#[refine]
Instance stackIns : Stack :=
{

  stack A := list A;
  emptystack {A} := nil;
  pop A (s:list A):=
  match s with
    | nil => Nothing 
    | cons hd tl => Just ( hd , tl)
  end;
  push A v s := @cons A v s;
  isStackEmpty := listIsEmptiable;
  pop_in A (s:list A):=
  match s with
    | nil => inright eq_refl
    | cons hd tl => inleft ( exist _ (hd,tl) (conj _ _))
  end;
}.
left. reflexivity.
intros b Hneq Hin.
destruct Hin.
contradiction.
assumption.
left.
reflexivity.
intros.
right.
apply H.
destruct s.
cbv.
auto.
cbv.
discriminate.
Defined.

(**
A stack that cannot contain the same elemet
multiple times simultaneously.
*)
Class UniqueStack :=
{
  ustack: Type->Type;
  uemptystack {A}: ustack A;
  isUStackEmpty {A} :> isEmptyable (ustack A);
  ustackInOpClass A:> InOpClass A (ustack A);
  upop_in {A} (s:ustack A):
    {'(a,s1):A*ustack A|
       a∊s/\~a∊s1/\forall b, a<>b -> (b∊s<-> b∊s1)}+
    {isUStackEmpty s=true};
  upush_in {A} (a:A) (s:ustack A) (pI:~ a ∊ s):
    {s1:ustack A|a∊s1/\forall b, a<>b -> (b∊s <-> b∊s1)};
  (*In the unique left fold operation the relation R
    on the result type means, some input has been processed.
    The folding function can take advantage of the fact,
    that the next element is not yet processed, on the
    other hand must provide proof, that on output, no
    additional processing has been taken place.
    The initial state must not have any of the elements
    of the stack been processed.*)
  ufoldl A B (R:A->B->Prop)
    (f:forall (b:B) (a:A), ~(R a b) ->
    {b1:B| forall a1:A, a1<>a -> R a1 b1 -> R a1 b})
    (b0:B) (us:ustack A) `(forall a:A, a∊us -> ~(R a b0)): B;
  uinEmpty A x (s:ustack A): isUStackEmpty s=true -> ~ x ∊ s;
  uEmptyEmpty A: isUStackEmpty (@uemptystack A)=true;

}.

(**
Data structure for the implementation.*)
Inductive notInList A: list A -> Prop:=
  | ninNil: notInList A nil
  | ninCons a l (ll:notInList A l): ~a∊l -> notInList A (a::l).
  
#[refine]
Instance ustackIns : UniqueStack :=
{
  ustack A := {l | notInList A l};
  uemptystack {A} := exist _ nil (ninNil A);
  isUStackEmpty A x:=
    let (l, _) := x in
    match l  with
    | nil => true
    | _ :: _ => false
    end;
  ustackInOpClass A a s:= let (l, _) := s in a ∊ l;
  upop_in A s:= match s return _ with exist _ l ll =>
    match l as l0 return l=l0 -> _ with
      | nil    => fun Heq => inright ?[pE]
      | hd::tl => fun Heq =>
          inleft (exist _ (hd,(exist _ tl ?[pNI1])) 
                 (conj ?[pop1] (conj ?[pop2] ?[pop3])))
    end eq_refl end;
  upush_in {A} (a:A) s (pI:~ a ∊ s):=
    match s as s0 return s=s0 -> _ with exist _ l ll => fun Heqs =>
      exist _ (exist _ (a::l) (ninCons A a l ll ?[pNI2])) ?[push1]
    end eq_refl;
  ufoldl A B R f b0 '(exist _ l nl):=?[ufold];
}.
[ufold]:{
refine (
  (fix ufold b0 l nl pNI:=
    match l as l0 return l=l0 -> _ with
      | [] => fun Hleq => b0
      | hd::tl => fun Hleq =>
      match f b0 hd ?[pNR] with
        | exist _ b1 pF => ufold b1 tl ?[tl] ?[pNI]
      end
  end eq_refl) b0 l nl 
).
[pNR]:{
  apply pNI.
  cbn.
  rewrite Hleq.
  left.
  reflexivity.
}
[tl]:{
destruct nl;
congruence.
}
[pNI]:{
cbn in *.
intros a H.
intros H1.
apply (pNI a).
rewrite Hleq.
right.
tauto.
apply pF.
destruct nl;
congruence.
tauto.
}
}
[pE]:{ rewrite Heq. reflexivity. }
[pNI1]:{
 destruct ll. discriminate.
injection Heq.
intros H1 H2.
rewrite <- H1.
exact ll.
}
[pop1]:{
cbn.
rewrite Heq.
left.
reflexivity.
}
[pop2]:{
cbn.
destruct ll.
discriminate.
congruence.
}
[pop3]:{
 cbn.
 intros.
 rewrite Heq.
 cbn.
 firstorder.
}
[pNI2]:{
rewrite Heqs in pI.
exact pI.
}
[push1]:{
  cbn.
  rewrite Heqs in pI.
  firstorder.
}
intros.
destruct s.
cbn.
destruct n.
auto.
congruence.
auto.
Defined.

(**
Abstract interface for a queue (first in first out)
The available functions:
- emptyqueue : creates a new empty queue
- push_front : pushes an element at the front of the queue
- pop_end : pops the end element, if nonempty
- isQueueEmpty : checks if the queue is empty

*)
Class Queue := {  
    queue: Type -> Type;
    emptyqueue {A} : queue A;
    push_front {A} (v: A) (q:queue A) : queue A;
    pop_end {A} (q:queue A): Maybe (A * queue A);
    isQueueEmpty {A} :> isEmptyable (queue A); 
}.



Instance isQEmptyable A : isEmptyable ((list A) * (list A)) :=
{

  isEmpty := fun lr => match lr with 
                         | pair l r => match l , r with
                                    | nil , nil => true
                                    | _ , _ => false
                                   end
                        end;

}.

(**

fast_queue is the instance of the Queue, 
The queue itself is a type cartesian product of two lists, emptyqueue is
initialised to a tuple, which is nil at first.
Elements are inseted into the first list, popped
from the second. If the second list is empty,
the first list is reversed and moved to the second
list before pop.

*)

Instance fast_queue : Queue :=
{

  queue A:= ((list A) * (list A))%type;
  emptyqueue A := (nil,nil);
  push_front A := fun v q =>
    match q with pair l r => (v::l,r) end;
  pop_end A := fun q: (list A) * (list A) => 
    match q with pair l r =>
      match r with
        | nil =>
        match l with
          | nil => Nothing 
          | cons hd tl => let tmp := rev l in
          match tmp with
            | nil => Nothing (* impossible case *)
            | cons hd1 tl1 => Just (hd1, (nil, tl1))
          end
        end
        | cons hd tl => Just (hd, (l, tl))
      end     
    end;
  isQueueEmpty := isQEmptyable;
}.

(** Several types of dictionaries are used. All of them
associate keys of type K to values.

In this version the same key can have several values.
All the previously inserted values are returned as a list.

 *)
Class MultiDictionary (K:Type) := 
{
  mdictionary : Type -> Type;
  memptyDictionary {V} : mdictionary V;
  minsert {V} (k:K) (v:V) (dic: mdictionary V) : mdictionary V;
  mlookup {V} (k:K) (dic : mdictionary V) : list V; 
}.

(** The traditional version: new value overwrites the old one
if the same key inserted twice
 *)
Class OverwriteDictionary (K:Type) := 
{
  odictionary : Type -> Type;
  oemptyDictionary {V} : odictionary V;
  oinsert {V} (k:K) (v:V) (dic: odictionary V) : odictionary V;
  olookup {V} (k:K) (dic : odictionary V) : Maybe V; 
  
}.

(**

Like above, new values overwrite the old ones if the same key inserted twice, however every key has a default value,
therefore the Maybe datatype can be omitted.

 *)
Class DefaultDictionary (K:Type) := 
{
  ddictionary : Type -> Type;
  demptyDictionary {V} (d:V): ddictionary V;
  dinsert {V} (k:K) (v:V) (dic: ddictionary V) : ddictionary V;
  dlookup {V} (k:K) (dic : ddictionary V) : V; 
}.

(** Here, new value overwrites the old one if the same key inserted twice,
every key has a default value, the type of the value may depend on the key. This dependence is defined by the function V:K->Type

 *)
Class DependentDefaultDictionary (K:Type) := 
{
  dddictionary : (K->Type) -> Type;
  ddemptyDictionary {V:K->Type} (df:forall k, V k): dddictionary V;
  ddinsert {V} (k:K) (v:V k) (dic: dddictionary V) : dddictionary V;
  ddlookup {V} (k:K) (dic : dddictionary V) : V k;
  ddInsertSame {V} (k:K) (v:V k) (dic : dddictionary V):
    ddlookup k (ddinsert k v dic) = v;
  ddInsertOther {V} (k k1:K) (v1:V k1) (dic : dddictionary V):
    k<>k1 -> ddlookup k dic = ddlookup k (ddinsert k1 v1 dic);
  ddEmptyLookup {V:K->Type} (df:forall k, V k) k:
    ddlookup k (ddemptyDictionary df) = df k;
}.

Arguments mdictionary K {MultiDictionary} _.
Arguments odictionary K {OverwriteDictionary} _.
Arguments ddictionary K {DefaultDictionary} _.
Arguments dddictionary K {DependentDefaultDictionary} _.

(**
We try to delegate as much list operation
as possible to typeclasses.*)
Class Foldable (T:Type->Type):=
{
  foldl [A B] (f:A->B->A) (z:A) (l:T B):A;
  foldForall [A]:(A->Prop)->T A->Prop;
  foldExists [A]:(A->Prop)->T A->Prop;
  foldForallDec [A] [P:A->Prop] (P_dec:forall a,{P a}+{~P a})
    (l:T A): {foldForall P l}+{foldExists (fun a=>~P a) l};
}.

#[refine]
Instance foldableList: Foldable list:=
{
  foldl _ _ f z l:=fold_left f l z;
  foldForall:=Forall;
  foldExists:=Exists;
foldForallDec [A] [P:A->Prop] (P_dec:forall a,{P a}+{~P a})
    (l:list A):= _(*fold_left (fun x a => _) _ (left (Forall_nil _)*);
}.
induction l.
left.
constructor.
destruct IHl.
destruct (P_dec a).
left.
constructor; assumption.
right.
apply Exists_cons_hd. assumption.
right.
apply Exists_cons_tl. assumption.
Defined.

(*Compute foldableList.*)

Class Functor (T:Type->Type):=
{
  fmap [A B]:(A->B)->T A->T B;
}.
Instance functorList: Functor list:=
{
  fmap:=map;
}.



Fixpoint listToMembershipProofList [A] (l:list A) : list {x:A | x ∊ l}:=
   match l with
    | nil => nil
    | hd :: tl => cons (exist _ hd (or_introl eq_refl))
      (fmap (fun '(exist _ x p) => exist _ x (or_intror p))
            (listToMembershipProofList tl))
   end.

(*  Compute listToMembershipProofList [1;2;3;66].*)

Lemma lastCons: forall A (l:list A) a b, last (a::l) b = last l a.
Proof.
  induction l as [ | a0 l0 IHl0].
-  reflexivity.
-  intros a b.
   cbn in IHl0.
   destruct l0. reflexivity.
   cbn in *.
   apply IHl0.
Qed.

Section sublist.
Context {A:Type}.
Context [eqAdec: forall (a b:A), {a=b}+{a<>b}].

Inductive Sublist: list A -> list A -> Prop:=
  | slNil: Sublist nil nil
  | slCons a l1 l2: Sublist l1 l2 -> Sublist (a::l1) (a::l2)
  | slSkip  a l1 l2: Sublist l1 l2 -> Sublist l1 (a::l2)
.
Inductive strictSublist: list A -> list A -> Prop:=
  | sslCons a l1 l2: strictSublist l1 l2 ->
        strictSublist (a::l1) (a::l2)
  | sslSkip  a l1 l2: Sublist l1 l2 -> strictSublist l1 (a::l2)
.
Instance sublistStrictSubsetOpClass:
  SubsetOpClass (list A) (list A):= Sublist.
Instance strictSublistStrictSubsetOpClass:
  StrictSubsetOpClass (list A) (list A):= strictSublist.



Fixpoint listDelete a l:list A:=
  match l with
    | nil => nil
    | hd::tl =>
    match eqAdec a hd with
      | left  _ => listDelete a tl
      | right _ => hd::listDelete a tl
    end
  end.

Lemma deleteLength1: forall a l, length (listDelete a l) <= length l.
Proof.
  induction l.
- cbn. lia.
- cbn.
  destruct (eqAdec a a0); cbn; lia.
Qed.

Lemma deleteLength: forall a l, a ∊ l ->
    length (listDelete a l) < length l.
Proof.
  induction l.
- cbn. tauto.
- intros [Hihd|Hitl].
  cbn.
  destruct (eqAdec a a0).
  pose proof (deleteLength1 a l).
  lia.
  congruence.
  cbn.
  destruct (eqAdec a a0);
  pose proof (IHl Hitl);
  cbn;
  lia.
Qed.

Lemma deleteSublist1: forall a l, listDelete a l ⊆ l.
Proof.
  induction l.
  simpl.
  constructor.
  simpl.
  destruct (eqAdec a a0);
  constructor;
  assumption.
Qed.

Lemma deleteSublist: forall a l, a ∊ l -> listDelete a l ⊂ l.
Proof.
  induction l.
  intros H.
  inversion H.
  intros H.
  simpl.
  destruct (eqAdec a a0).
  apply sslSkip.
  apply deleteSublist1.
  constructor.
  apply IHl.
  inversion H.
  symmetry in H0.
  contradiction.
  assumption.
Qed.

Lemma deleteIn: forall a b l, a<>b -> (a ∊ l <-> a ∊ listDelete b l).
Proof.
  induction l.
- intros Hneq.
  split;
  intros H;
  inversion H.
- intros Hneq.
  split.
-- intros Hin.
  simpl.
  destruct (eqAdec b a0).
---  destruct Hin.
---- congruence.
---- firstorder.
---  destruct Hin.
---- left. auto.
---- right.
    apply IHl;auto.
-- simpl.
   destruct (eqAdec b a0).
--- intros H.
  pose proof (IHl Hneq) as H1.
  right.
  apply H1.
  auto.
---  intros H.
  cbn in H.
  destruct H.
  rewrite H.
  left.
  reflexivity.
  right.
  pose proof (IHl Hneq) as H1.
  tauto.
Qed.
 
Lemma deleteNotIn: forall a l, ~ a ∊ listDelete a l.
Proof.
  induction l.
- intros H.
  inversion H.
- simpl.
  destruct (eqAdec a a0).
-- auto.
-- intros Hin. destruct Hin; auto.
Qed.

End sublist.

